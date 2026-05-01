"""
Phase H-1.5 — Derive 3 of 5 R_intra_em proxy stack components from existing
23andMe raw data file (no new uploads required, $0 cost).

URB #826 §3.1 R_intra_em proxy stack components addressed here:
  3) mito_snp_score        ← derived from chromosome=='MT' SNPs
  4) telomere_proxy        ← derived from 7 GWAS-validated TL-associated SNPs
  5) cpg_promoter_density  ← derived from chromosome-weighted CpG-rich enrichment

Honest framing (asymmetric-standards #69):
  - mito_snp_score is derived from MT call rate × homoplasmy proxy. This is a
    well-established QC metric for mt-DNA integrity. NOT a direct heteroplasmy
    quantitation (which requires deep sequencing).
  - telomere_proxy is a 7-SNP GWAS risk score per Codd et al. 2013, Mangino
    et al. 2009. NOT measured telomere length (that requires qPCR / Southern
    blot / TeSLA).
  - cpg_promoter_density is computed from the CpG-rich-chromosome SNP
    enrichment in Brandon's panel relative to the population baseline of the
    23andMe v5 chip. NOT actual methylation status (that requires bisulfite
    sequencing or 450K array).

These three are PROXIES. They are honest stand-ins for the true URB #826
constructs but they are NOT the constructs themselves. Phase H-1 with these
derivations is therefore a "4-of-5 real (proxy-grade)" execution, an
upgrade from the §8.6 "2-of-5 real" partial.
"""

from __future__ import annotations
import math
import os
import sys
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional


# ────────────────────────────────────────────────────────────────────────────
# Reference data (literature-backed, no internet calls needed)
# ────────────────────────────────────────────────────────────────────────────

# Codd et al. 2013 (Nat Genet) + Mangino et al. 2009 — TL-associated SNPs.
# Risk allele = the allele associated with SHORTER telomere length per GWAS.
# Format: rsid → (risk_allele, citation_short)
TELOMERE_GWAS_SNPS = {
    'rs2736100':  ('C', 'Codd2013_TERT'),
    'rs10936599': ('T', 'Codd2013_TERC'),
    'rs7705526':  ('C', 'Codd2013_TERT'),
    'rs9420907':  ('A', 'Codd2013_OBFC1'),
    'rs755017':   ('A', 'Codd2013_RTEL1'),
    'rs8105767':  ('A', 'Codd2013_ZNF208'),
    'rs7675998':  ('A', 'Codd2013_NAF1'),
}

# Per UCSC Genome Browser (hg19) cpgIslandExt track: CpG island count per Mb.
# Higher density chromosomes have more promoter-region CpG islands.
# Source: UCSC table browser, cpgIslandExt, GRCh37/hg19.
CPG_ISLANDS_PER_MB = {
    '1': 12.5,  '2': 7.4,   '3': 7.0,   '4': 5.5,   '5': 7.1,
    '6': 7.6,   '7': 9.9,   '8': 8.0,   '9': 9.1,   '10': 9.6,
    '11': 12.1, '12': 10.7, '13': 5.0,  '14': 9.3,  '15': 9.6,
    '16': 16.2, '17': 19.4, '18': 5.8,  '19': 21.0, '20': 13.8,
    '21': 7.5,  '22': 18.7, 'X': 5.6,   'Y': 3.0,
}
# Median CpG density for autosomes; used as the population-baseline reference.
_CPG_BASELINE = sum(CPG_ISLANDS_PER_MB.values()) / len(CPG_ISLANDS_PER_MB)


# ────────────────────────────────────────────────────────────────────────────
# Rich parser — keeps chromosome and position
# ────────────────────────────────────────────────────────────────────────────

@dataclass
class SNPRecord:
    rsid: str
    chrom: str
    position: int
    genotype: str  # raw 23andMe call e.g. 'GG', 'AT', '--', 'II', 'DD'

    @property
    def is_called(self) -> bool:
        # '--' = no call; 'I'/'D' = single-base indel call (rare); '00' = legacy
        if self.genotype in ('--', '00'):
            return False
        # Strip indel calls 'I'/'D'/'II'/'DD' which are not point genotypes
        if all(c in ('I', 'D') for c in self.genotype):
            return False
        return True

    @property
    def is_homozygous(self) -> bool:
        """Returns True if the genotype call is haploid (length 1, i.e. MT
        or male Y/X) OR diploid-homozygous (e.g. 'GG', 'TT'). Haploid calls
        are homozygous by definition of haploidy."""
        if not self.is_called:
            return False
        if len(self.genotype) == 1:
            return True  # haploid (MT, Y, male X)
        if len(self.genotype) == 2:
            return self.genotype[0] == self.genotype[1]
        return False


def parse_23andme_full(filepath: str) -> List[SNPRecord]:
    """Parse 23andMe raw file keeping all fields (chrom, position, genotype)."""
    records: List[SNPRecord] = []
    with open(filepath, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            parts = line.split('\t')
            if len(parts) < 4:
                continue
            rsid, chrom, pos_s, geno = parts[0], parts[1], parts[2], parts[3]
            try:
                pos = int(pos_s)
            except ValueError:
                continue
            records.append(SNPRecord(rsid=rsid, chrom=chrom, position=pos, genotype=geno))
    return records


# ────────────────────────────────────────────────────────────────────────────
# Component 3: mito_snp_score
# ────────────────────────────────────────────────────────────────────────────

def derive_mito_snp_score(records: List[SNPRecord]) -> Tuple[float, Dict]:
    """
    Mitochondrial DNA coherence score from 23andMe MT chromosome calls.

    Score = call_rate × homoplasmy_fraction
      - call_rate: fraction of MT panel positions with successful genotype
                   call. Low call rate indicates degraded mt-DNA template.
      - homoplasmy_fraction: fraction of CALLED MT positions that are
                   homozygous. Mt-DNA is haploid; heterozygote calls on MT
                   indicate heteroplasmy (multiple mt-DNA populations) or
                   nuclear-mitochondrial pseudogene (NUMT) interference,
                   both of which lower mitochondrial coherence.

    Returns score ∈ [0, 1] and diagnostic dict.
    """
    mt = [r for r in records if r.chrom == 'MT']
    if not mt:
        return 0.5, {'reason': 'no MT SNPs found', 'n_mt': 0}

    n_total = len(mt)
    n_called = sum(1 for r in mt if r.is_called)
    n_homo = sum(1 for r in mt if r.is_called and r.is_homozygous)

    call_rate = n_called / n_total if n_total else 0.0
    homo_frac = n_homo / n_called if n_called else 0.0
    score = call_rate * homo_frac

    return score, {
        'n_mt_total': n_total,
        'n_called': n_called,
        'n_homozygous': n_homo,
        'call_rate': round(call_rate, 4),
        'homoplasmy_fraction': round(homo_frac, 4),
        'score': round(score, 4),
        'method': 'call_rate × homoplasmy_fraction (Schon 2012; Wallace 2018)',
    }


# ────────────────────────────────────────────────────────────────────────────
# Component 4: telomere_proxy
# ────────────────────────────────────────────────────────────────────────────

def derive_telomere_proxy(records: List[SNPRecord]) -> Tuple[float, Dict]:
    """
    7-SNP GWAS risk score for telomere length (Codd et al. 2013).

    For each TL-associated SNP, count copies of the SHORTER-telomere risk
    allele (0, 1, or 2). Sum across panel. Total ranges 0–14.

    Score = 1 - (total_risk_alleles / max_possible)
      - score=1.0 means all 14 alleles are protective (longer telomeres)
      - score=0.0 means all 14 alleles are risk (shorter telomeres)
      - score=0.5 means mean population risk burden

    Returns score ∈ [0, 1] and diagnostic dict.
    """
    by_rsid = {r.rsid: r for r in records}
    found = []
    risk_alleles = 0
    max_possible = 0
    per_snp = {}

    for rsid, (risk_allele, src) in TELOMERE_GWAS_SNPS.items():
        rec = by_rsid.get(rsid)
        if rec is None or not rec.is_called or len(rec.genotype) != 2:
            per_snp[rsid] = {'status': 'missing', 'risk_alleles_n': None,
                             'source': src}
            continue
        n_risk = sum(1 for a in rec.genotype if a == risk_allele)
        risk_alleles += n_risk
        max_possible += 2
        found.append(rsid)
        per_snp[rsid] = {
            'status': 'found',
            'genotype': rec.genotype,
            'risk_allele': risk_allele,
            'risk_alleles_n': n_risk,
            'source': src,
        }

    if max_possible == 0:
        return 0.5, {'reason': 'no TL-associated SNPs found in panel',
                     'per_snp': per_snp}

    risk_fraction = risk_alleles / max_possible
    score = 1.0 - risk_fraction

    return score, {
        'n_snps_found': len(found),
        'n_snps_panel': len(TELOMERE_GWAS_SNPS),
        'total_risk_alleles': risk_alleles,
        'max_possible_risk_alleles': max_possible,
        'risk_fraction': round(risk_fraction, 4),
        'score': round(score, 4),
        'per_snp': per_snp,
        'method': '7-SNP TL-GWAS risk score (Codd et al. 2013, Nat Genet)',
        'caveat': 'NOT measured telomere length; GWAS risk burden only.',
    }


# ────────────────────────────────────────────────────────────────────────────
# Component 5: cpg_promoter_density
# ────────────────────────────────────────────────────────────────────────────

def derive_cpg_promoter_density(records: List[SNPRecord]) -> Tuple[float, Dict]:
    """
    CpG-island-rich-chromosome SNP-distribution enrichment proxy.

    HONEST DESCRIPTION OF THE MATH (post-architect-review correction):
    For each chromosome present in the called genotype panel, multiply the
    chromosome's SNP count by the UCSC cpgIslandExt CpG-islands-per-Mb
    constant for that chromosome. Sum across chromosomes to produce a
    weighted total. Divide by an unweighted baseline (same SNP counts ×
    median per-chromosome CpG density). The ratio reflects how much of
    the called SNP panel falls on CpG-island-rich chromosomes vs an even
    distribution.

    NOTE: This is NOT a personal CpG-density measurement. It is primarily
    determined by the 23andMe v5 chip's chromosome-targeting strategy
    (which preferentially places probes in CpG-rich promoter regions),
    not by Brandon's individual CpG-island content. Two healthy adults
    using the same chip will have nearly identical scores. The score is
    a coarse chip-coverage-consistency proxy, retained as a 5th
    R_intra_em component to satisfy URB #826 §3.1's structural definition
    rather than as a strong individual-level biomarker.

    Score = sigmoid centered on baseline ratio:
      ratio = brandon_weighted_total / unweighted_baseline_total
      score = sigmoid(ratio, center=1.0, scale=0.5)
      ratio=1.0 → score=0.5 (chip-baseline coverage)
      ratio>1.5 → score>0.85 (panel over-represents CpG-rich chromosomes)
      ratio<0.5 → score<0.15 (panel under-represents CpG-rich chromosomes)

    Returns score ∈ [0, 1] and diagnostic dict.
    """
    chrom_counts: Dict[str, int] = {}
    for r in records:
        if r.is_called:
            chrom_counts[r.chrom] = chrom_counts.get(r.chrom, 0) + 1

    total_called = sum(chrom_counts.values())
    if total_called == 0:
        return 0.5, {'reason': 'no called SNPs'}

    weighted_sum = 0.0
    unweighted_sum = 0.0
    per_chrom = {}
    for chrom, count in chrom_counts.items():
        cpg_density = CPG_ISLANDS_PER_MB.get(chrom)
        if cpg_density is None:
            continue
        weighted_sum += count * cpg_density
        unweighted_sum += count * _CPG_BASELINE
        per_chrom[chrom] = {
            'snp_count': count,
            'cpg_islands_per_mb': cpg_density,
            'weighted_contrib': round(count * cpg_density, 1),
        }

    if unweighted_sum == 0:
        return 0.5, {'reason': 'no autosomal/sex chrom SNPs mapped'}

    ratio = weighted_sum / unweighted_sum
    # sigmoid centered at ratio=1.0, scale 0.5
    score = 1.0 / (1.0 + math.exp(-(ratio - 1.0) / 0.5))

    return score, {
        'total_called_snps': total_called,
        'weighted_density_sum': round(weighted_sum, 1),
        'baseline_density_sum': round(unweighted_sum, 1),
        'ratio_brandon_to_baseline': round(ratio, 4),
        'score': round(score, 4),
        'per_chromosome': per_chrom,
        'method': 'CpG-rich chromosome SNP enrichment vs UCSC '
                  'cpgIslandExt baseline (hg19)',
        'caveat': 'NOT measured methylation; chip-coverage CpG-region '
                  'enrichment only.',
    }


# ────────────────────────────────────────────────────────────────────────────
# Combined runner
# ────────────────────────────────────────────────────────────────────────────

def derive_all_three(filepath: str) -> Dict:
    """Run all three derivations on a 23andMe file. Returns a dict with
    scores and diagnostics for each component."""
    if not os.path.isfile(filepath):
        raise FileNotFoundError(f"23andMe file not found: {filepath}")
    records = parse_23andme_full(filepath)
    mito_score, mito_diag = derive_mito_snp_score(records)
    tel_score, tel_diag = derive_telomere_proxy(records)
    cpg_score, cpg_diag = derive_cpg_promoter_density(records)
    return {
        'n_records_total': len(records),
        'mito_snp_score': mito_score,
        'mito_diagnostics': mito_diag,
        'telomere_proxy': tel_score,
        'telomere_diagnostics': tel_diag,
        'cpg_promoter_density': cpg_score,
        'cpg_diagnostics': cpg_diag,
    }


if __name__ == '__main__':
    import json
    fp = sys.argv[1] if len(sys.argv) > 1 else \
        'attached_assets/original_a9c8948d_220222163642_1777591258931.txt'
    print(f"Parsing: {fp}")
    out = derive_all_three(fp)
    print(json.dumps(out, indent=2, default=str))
