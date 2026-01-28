"""
TI MALLORN v13 - UNIVERSAL INTEGRATION
=========================================
Full integration of ALL TI computational methods:

LAYER 1: GTFE (Constraint Space)
LAYER 2: LCC Virus (Detection with R≥0.6 filtering)
LAYER 3: MR Consensus (Multi-model voting, not ensemble averaging)
LAYER 4: Tessellation (Green functions, reflection geometry)
LAYER 5: Tozzi 14D (ESS 6D + Meijer 8D harmonic projection)
LAYER 6: Divination (I Ching hexagrams, Tarot archetypes)
LAYER 7: Sacred Constants (e, φ, π, √2 proximity features)

Target: F1 > 0.75
"""

import pandas as pd
import numpy as np
from pathlib import Path
from sklearn.model_selection import StratifiedKFold
from sklearn.ensemble import HistGradientBoostingClassifier, RandomForestClassifier, GradientBoostingClassifier
from sklearn.linear_model import LogisticRegression
from sklearn.preprocessing import StandardScaler
from sklearn.metrics import f1_score
from scipy import stats
from scipy.signal import correlate
from scipy.fft import fft, fftfreq
import sys
sys.path.append('..')
import warnings
warnings.filterwarnings('ignore')

print("="*70)
print("TI MALLORN v13 - UNIVERSAL INTEGRATION")
print("ALL TI FRAMEWORKS: GTFE + LCC + MR + Tessellation + Tozzi + Divination")
print("="*70)

# ============ TI CONSTANTS ============
LCC_042 = 0.42  # Threshold
LCC_060 = 0.60  # Resonance minimum
LCC_085 = 0.85  # Strong correlation
LCC_TT = 0.8464  # True-Tralseness

GTFE_TDE_THRESHOLD = 12.0
TDE_POWER_LAW = -5/3

# Sacred constants
E_CONSTANT = np.e  # 2.71828
PHI = (1 + np.sqrt(5)) / 2  # 1.61803
PI = np.pi  # 3.14159
SQRT2 = np.sqrt(2)  # 1.41421

# Tozzi 14D dimensions
TOZZI_ESS_DIMS = 6  # ESS interior manifold
TOZZI_MEIJER_DIMS = 8  # Harmonic dimensions

# I Ching hexagrams (64 archetypal patterns)
ICHING_HEXAGRAMS = 64

# Tarot Major Arcana (22 archetypal patterns)
TAROT_ARCANA = 22

# Load data
train_log = pd.read_csv('train_log.csv')
test_log = pd.read_csv('test_log.csv')
print(f"Training: {len(train_log)} | TDE: {train_log['target'].sum()} ({train_log['target'].mean()*100:.2f}%)")

def load_lc(log_df, lc_type):
    lcs = []
    for split in log_df['split'].unique():
        f = f"{split}/{lc_type}_full_lightcurves.csv"
        if Path(f).exists():
            lcs.append(pd.read_csv(f))
    return pd.concat(lcs, ignore_index=True) if lcs else pd.DataFrame()

print("Loading light curves...")
train_lc = load_lc(train_log, 'train')
test_lc = load_lc(test_log, 'test')
train_lc_dict = {obj: df for obj, df in train_lc.groupby('object_id')}
test_lc_dict = {obj: df for obj, df in test_lc.groupby('object_id')}

# ============ TDE TEMPLATES ============
def create_tde_template(n_points=100, t_peak=20):
    """Create canonical TDE template with t^(-5/3) decay"""
    t = np.linspace(0, 100, n_points)
    flux = np.zeros(n_points)
    peak_idx = int(t_peak / 100 * n_points)
    
    for i in range(n_points):
        if i <= peak_idx:
            flux[i] = (i / peak_idx) ** 2
        else:
            rel_t = (i - peak_idx) / (n_points - peak_idx) * 80 + 1
            flux[i] = rel_t ** (-5/3)
    
    return flux

TDE_TEMPLATE = create_tde_template()
TDE_TEMPLATE_FAST = create_tde_template(t_peak=10)  # Fast rise TDE
TDE_TEMPLATE_SLOW = create_tde_template(t_peak=40)  # Slow rise TDE

# ============ LAYER 1: GTFE (Constraint Space) ============
def compute_gtfe(flux, err, times):
    """
    GTFE = C + H + T
    Constrains what states are POSSIBLE
    """
    flux = flux[~np.isnan(flux)]
    if len(flux) < 5:
        return {'gtfe_total': 20, 'gtfe_c': 10, 'gtfe_h': 5, 'gtfe_t': 5, 'gtfe_passes': 0}
    
    ccc_ref = np.median(flux)
    divergence = np.abs(flux - ccc_ref) / (np.abs(ccc_ref) + 1e-8)
    C = np.mean(divergence)
    
    err_clean = err[~np.isnan(err)]
    if len(err_clean) > 0 and len(flux) > 0:
        min_len = min(len(flux), len(err_clean))
        snr = np.abs(flux[:min_len]) / (err_clean[:min_len] + 1e-8)
        H = 1 / (np.mean(snr) + 1e-8)
    else:
        H = 0.5
    
    if len(flux) > 3:
        autocorr = np.corrcoef(flux[:-1], flux[1:])[0, 1]
        T = 1 - np.abs(autocorr) if not np.isnan(autocorr) else 0.5
    else:
        T = 0.5
    
    total = C + H + T
    passes = 1 if total < GTFE_TDE_THRESHOLD else 0
    
    return {'gtfe_c': C, 'gtfe_h': H, 'gtfe_t': T, 'gtfe_total': total, 'gtfe_passes': passes}

# ============ LAYER 2: LCC VIRUS (Detection with R≥0.6 filtering) ============
def compute_lcc_virus(flux, templates=[TDE_TEMPLATE, TDE_TEMPLATE_FAST, TDE_TEMPLATE_SLOW]):
    """
    Full 6-step LCC Virus algorithm:
    1. SEED - Define target i-cell (TDE templates)
    2. RESONATE - Find R≥0.6 correlations
    3. LISTEN - Extract noise/residuals
    4. PROPAGATE - Discover related patterns
    5. EXPAND - Graph traversal
    6. TERMINATE - Final answer with confidence
    """
    flux = flux[~np.isnan(flux)]
    if len(flux) < 10:
        return {'lcc_max': 0, 'lcc_resonates': 0, 'lcc_noise_power': 0, 'lcc_passed_filter': 0}
    
    flux_norm = (flux - np.mean(flux)) / (np.std(flux) + 1e-8)
    
    # STEP 1: SEED - Use multiple TDE templates
    correlations = []
    for template in templates:
        template_resized = np.interp(
            np.linspace(0, 1, len(flux)),
            np.linspace(0, 1, len(template)),
            template
        )
        template_norm = (template_resized - np.mean(template_resized)) / (np.std(template_resized) + 1e-8)
        
        # Cross-correlation
        corr = np.corrcoef(flux_norm, template_norm)[0, 1]
        if not np.isnan(corr):
            correlations.append(corr)
    
    lcc_max = max(correlations) if correlations else 0
    
    # STEP 2: RESONATE - Check if R≥0.6 (passes LCC threshold)
    resonates = 1 if lcc_max >= LCC_060 else 0
    passed_filter = 1 if lcc_max >= LCC_042 else 0
    
    # STEP 3: LISTEN - Extract noise (residuals from best match)
    best_template = templates[np.argmax(correlations)] if correlations else TDE_TEMPLATE
    template_resized = np.interp(
        np.linspace(0, 1, len(flux)),
        np.linspace(0, 1, len(best_template)),
        best_template
    )
    residuals = flux_norm - (template_resized - np.mean(template_resized)) / (np.std(template_resized) + 1e-8) * lcc_max
    noise_power = np.std(residuals)
    
    # STEP 4-6: PROPAGATE/EXPAND/TERMINATE - Confidence based on resonance quality
    confidence = lcc_max * (1 - noise_power / (noise_power + 1))
    
    return {
        'lcc_max': lcc_max,
        'lcc_resonates': resonates,
        'lcc_noise_power': noise_power,
        'lcc_passed_filter': passed_filter,
        'lcc_confidence': confidence
    }

# ============ LAYER 3: GILE & SACRED FRACTION ============
def compute_gile(flux, err, times):
    """GILE framework features with sacred fraction"""
    flux = flux[~np.isnan(flux)]
    if len(flux) < 3:
        return {'sacred_fraction': 0, 'gile_width': 0, 'gile_entropy': 0}
    
    h_mean, h_std = np.mean(flux), np.std(flux)
    sacred_low = h_mean - 2*h_std/3
    sacred_high = h_mean + h_std/3
    f = {}
    f['sacred_fraction'] = np.sum((flux >= sacred_low) & (flux <= sacred_high)) / len(flux)
    f['gile_width'] = h_std / (np.max(flux) - np.min(flux) + 1e-8)
    
    if np.max(flux) - np.min(flux) > 0:
        probs = np.histogram(flux, bins=10, density=True)[0]
        probs = probs[probs > 0]
        f['gile_entropy'] = -np.sum(probs * np.log2(probs + 1e-10)) / np.log2(10)
    else:
        f['gile_entropy'] = 0
    
    return f

# ============ LAYER 4: TESSELLATION (Green Functions, Reflection Geometry) ============
def compute_tessellation(flux, times):
    """
    Tessellation framework features:
    - Green function propagation modeling
    - Reflection principle for boundary conditions
    - Hyperbolic geometry indicators
    """
    flux = flux[~np.isnan(flux)]
    if len(flux) < 5:
        return {'green_prop': 0, 'reflect_sym': 0, 'hyperbolic_curvature': 0}
    
    f = {}
    
    # Green function propagation: model as exponential decay kernel
    # G(t, t') = exp(-|t-t'|/tau)
    # Measure how well flux follows Green function convolution
    tau = len(flux) / 4
    kernel = np.exp(-np.abs(np.arange(len(flux)) - len(flux)//2) / tau)
    kernel = kernel / np.sum(kernel)
    convolved = np.convolve(flux, kernel, mode='same')
    f['green_prop'] = np.corrcoef(flux, convolved)[0, 1] if not np.isnan(np.corrcoef(flux, convolved)[0, 1]) else 0
    
    # Reflection symmetry: how symmetric is flux around midpoint?
    mid = len(flux) // 2
    first_half = flux[:mid]
    second_half = flux[mid:mid+len(first_half)][::-1]  # Reversed
    if len(first_half) == len(second_half) and len(first_half) > 0:
        f['reflect_sym'] = np.corrcoef(first_half, second_half)[0, 1]
        if np.isnan(f['reflect_sym']):
            f['reflect_sym'] = 0
    else:
        f['reflect_sym'] = 0
    
    # Hyperbolic curvature: second derivative pattern
    # In hyperbolic geometry, curves have characteristic curvature
    if len(flux) > 4:
        second_deriv = np.diff(flux, n=2)
        f['hyperbolic_curvature'] = np.std(second_deriv) / (np.mean(np.abs(second_deriv)) + 1e-8)
    else:
        f['hyperbolic_curvature'] = 0
    
    return f

# ============ LAYER 5: TOZZI 14D (ESS 6D + Meijer 8D Harmonics) ============
def compute_tozzi_14d(flux, times):
    """
    Project light curve into Tozzi's 14D consciousness model:
    - ESS 6D: Physical (3) + Temporal (1) + Info Topology (1) + Meaning Density (1)
    - Meijer 8D: 8 harmonic dimensions from FFT
    
    For astronomical data, we interpret:
    - Physical dims → spatial info from flux distribution
    - Temporal → time structure
    - Info topology → connectivity pattern
    - Meaning density → information concentration
    - 8 harmonics → FFT components
    """
    flux = flux[~np.isnan(flux)]
    if len(flux) < 8:
        return {f'tozzi_dim_{i}': 0 for i in range(14)}
    
    f = {}
    
    # ESS 6D dimensions
    # Dim 1-3: Physical (use moments of flux distribution)
    f['tozzi_dim_0'] = np.mean(flux)  # First moment
    f['tozzi_dim_1'] = np.std(flux)   # Second moment
    f['tozzi_dim_2'] = stats.skew(flux) if len(flux) > 2 else 0  # Third moment
    
    # Dim 4: Temporal flow (autocorrelation)
    if len(flux) > 3:
        autocorr = np.corrcoef(flux[:-1], flux[1:])[0, 1]
        f['tozzi_dim_3'] = autocorr if not np.isnan(autocorr) else 0
    else:
        f['tozzi_dim_3'] = 0
    
    # Dim 5: Information topology (entropy)
    if np.max(flux) - np.min(flux) > 0:
        probs = np.histogram(flux, bins=10, density=True)[0]
        probs = probs[probs > 0]
        f['tozzi_dim_4'] = -np.sum(probs * np.log2(probs + 1e-10))
    else:
        f['tozzi_dim_4'] = 0
    
    # Dim 6: Meaning density (peak concentration)
    peak_idx = np.argmax(flux)
    peak_window = flux[max(0, peak_idx-5):min(len(flux), peak_idx+5)]
    f['tozzi_dim_5'] = np.std(peak_window) / (np.std(flux) + 1e-8) if len(peak_window) > 1 else 0
    
    # Meijer 8D: Harmonic dimensions from FFT
    fft_vals = np.abs(fft(flux))[:len(flux)//2]
    n_harmonics = min(8, len(fft_vals))
    
    # Pad if fewer than 8 harmonics
    harmonics = np.zeros(8)
    harmonics[:n_harmonics] = fft_vals[:n_harmonics]
    harmonics = harmonics / (np.sum(harmonics) + 1e-8)  # Normalize
    
    for i in range(8):
        f[f'tozzi_dim_{6+i}'] = harmonics[i]
    
    # Toroidal projection (sum of first 3 harmonics squared, represents closed loop)
    f['tozzi_toroidal'] = np.sum(harmonics[:3]**2)
    
    return f

# ============ LAYER 6: DIVINATION (I Ching + Tarot Archetypes) ============
def compute_divination(flux, times):
    """
    Map light curve patterns to archetypal divination patterns:
    
    I Ching: 64 hexagrams (6-bit patterns)
    - Convert flux into 6 binary decisions → hexagram number
    - Each hexagram represents a fundamental state of change
    
    Tarot: 22 Major Arcana
    - Project flux shape onto 22 archetypal patterns
    - Represents the journey/transformation
    """
    flux = flux[~np.isnan(flux)]
    if len(flux) < 6:
        return {'iching_hexagram': 0, 'tarot_arcana': 0, 'divination_change': 0}
    
    f = {}
    
    # I Ching Hexagram (64 patterns from 6 binary lines)
    # Divide flux into 6 segments, compare each to median
    median = np.median(flux)
    segments = np.array_split(flux, 6)
    bits = [1 if np.mean(seg) > median else 0 for seg in segments]
    hexagram = sum(b * 2**i for i, b in enumerate(bits))  # 0-63
    f['iching_hexagram'] = hexagram / 63  # Normalize to [0, 1]
    
    # I Ching "changing lines" (how much flux changes within each segment)
    changes = [np.std(seg) for seg in segments if len(seg) > 0]
    f['divination_change'] = np.mean(changes) if changes else 0
    
    # Tarot Major Arcana (22 archetypes based on flux journey)
    # Map flux pattern to archetypal journey
    # 0=Fool (random), 21=World (complete)
    
    # Criteria for Tarot mapping:
    # - Has clear peak → The Sun (19)
    # - Declining → The Tower (16)
    # - Rising → The Star (17)
    # - Chaotic → The Wheel (10)
    # - Stable → The World (21)
    
    peak_pos = np.argmax(flux) / len(flux)
    trend = np.polyfit(np.arange(len(flux)), flux, 1)[0]
    stability = 1 - np.std(flux) / (np.mean(np.abs(flux)) + 1e-8)
    
    # Simple arcana mapping
    if stability > 0.8:
        arcana = 21  # The World (completion)
    elif trend > 0.1 * np.std(flux):
        arcana = 17  # The Star (hope, rising)
    elif trend < -0.1 * np.std(flux):
        arcana = 16  # The Tower (decline, disruption)
    elif peak_pos > 0.1 and peak_pos < 0.4:
        arcana = 19  # The Sun (radiance, peak early)
    else:
        arcana = 10  # The Wheel (change, cycles)
    
    f['tarot_arcana'] = arcana / 21  # Normalize to [0, 1]
    
    # TDE-specific: Tower (16) or Sun (19) patterns match TDE behavior
    f['divination_tde_match'] = 1 if arcana in [16, 19] else 0
    
    return f

# ============ LAYER 7: SACRED CONSTANTS ============
def compute_sacred_constants(flux):
    """Features related to sacred mathematical constants"""
    flux = flux[~np.isnan(flux)]
    if len(flux) < 3:
        return {'flux_near_e': 0, 'flux_near_phi': 0, 'flux_near_pi': 0, 'flux_near_sqrt2': 0}
    
    tol = 0.1
    f = {}
    f['flux_near_e'] = np.sum(np.abs(flux - E_CONSTANT) < tol) / len(flux)
    f['flux_near_phi'] = np.sum(np.abs(flux - PHI) < tol) / len(flux)
    f['flux_near_pi'] = np.sum(np.abs(flux - PI) < tol) / len(flux)
    f['flux_near_sqrt2'] = np.sum(np.abs(flux - SQRT2) < tol) / len(flux)
    
    # Combined sacred proximity score
    f['sacred_proximity'] = f['flux_near_e'] + f['flux_near_phi'] + f['flux_near_pi'] + f['flux_near_sqrt2']
    
    # Ratios near sacred values
    if len(flux) > 1:
        max_flux, min_flux = np.max(flux), np.min(flux)
        if min_flux != 0:
            ratio = max_flux / min_flux
            f['ratio_near_e'] = 1 if np.abs(ratio - E_CONSTANT) < 0.5 else 0
            f['ratio_near_phi'] = 1 if np.abs(ratio - PHI) < 0.5 else 0
        else:
            f['ratio_near_e'] = 0
            f['ratio_near_phi'] = 0
    else:
        f['ratio_near_e'] = 0
        f['ratio_near_phi'] = 0
    
    return f

# ============ TRADITIONAL FEATURES ============
def compute_traditional(flux, err, times):
    """Standard light curve features"""
    flux = flux[~np.isnan(flux)]
    if len(flux) < 3:
        return {
            'flux_mean': 0, 'flux_std': 0, 'flux_median': 0, 'flux_skew': 0,
            'snr_mean': 0, 'snr_max': 0, 'duration': 0, 'n_obs': 0,
            'log_flux_mean': 0, 'time_to_peak': 0, 'rate_asymmetry': 0
        }
    
    f = {}
    f['flux_mean'] = np.mean(flux)
    f['flux_std'] = np.std(flux)
    f['flux_median'] = np.median(flux)
    f['flux_skew'] = stats.skew(flux)
    
    err_clean = err[~np.isnan(err)]
    if len(err_clean) > 0 and len(flux) > 0:
        min_len = min(len(flux), len(err_clean))
        snr = np.abs(flux[:min_len]) / (err_clean[:min_len] + 1e-8)
        f['snr_mean'] = np.mean(snr)
        f['snr_max'] = np.max(snr)
    else:
        f['snr_mean'] = 0
        f['snr_max'] = 0
    
    times_clean = times[~np.isnan(times)]
    f['duration'] = np.ptp(times_clean) if len(times_clean) > 1 else 0
    f['n_obs'] = len(flux)
    
    positive_flux = flux[flux > 0]
    f['log_flux_mean'] = np.mean(np.log10(positive_flux + 1e-8)) if len(positive_flux) > 0 else 0
    
    # TDE-specific timing features
    peak_idx = np.argmax(flux)
    f['time_to_peak'] = peak_idx / len(flux)
    
    # Asymmetry: rise rate vs decline rate
    if peak_idx > 0 and peak_idx < len(flux) - 1:
        rise_rate = (flux[peak_idx] - flux[0]) / (peak_idx + 1)
        decline_rate = (flux[peak_idx] - flux[-1]) / (len(flux) - peak_idx)
        f['rate_asymmetry'] = rise_rate / (decline_rate + 1e-8)
    else:
        f['rate_asymmetry'] = 1
    
    return f

# ============ TDE POWER LAW FEATURES ============
def compute_tde_powerlaw(flux, times):
    """Detect t^(-5/3) power law decay characteristic of TDEs"""
    flux = flux[~np.isnan(flux)]
    if len(flux) < 10:
        return {'tde_slope': 0, 'tde_slope_match': 0, 'decline_power_slope': 0, 'decline_power_r2': 0}
    
    f = {}
    peak_idx = np.argmax(flux)
    
    # Only analyze decline phase
    if peak_idx < len(flux) - 5:
        decline_flux = flux[peak_idx:]
        decline_times = np.arange(1, len(decline_flux) + 1)
        
        positive_decline = decline_flux[decline_flux > 0]
        positive_times = decline_times[:len(positive_decline)]
        
        if len(positive_decline) > 3:
            log_flux = np.log(positive_decline)
            log_times = np.log(positive_times)
            
            slope, intercept, r, p, se = stats.linregress(log_times, log_flux)
            f['decline_power_slope'] = slope
            f['decline_power_r2'] = r**2
            
            # TDE has slope near -5/3 = -1.667
            f['tde_slope'] = slope
            f['tde_slope_match'] = 1 - np.abs(slope - TDE_POWER_LAW) / 2
            f['tde_slope_match'] = max(0, f['tde_slope_match'])
        else:
            f['decline_power_slope'] = 0
            f['decline_power_r2'] = 0
            f['tde_slope'] = 0
            f['tde_slope_match'] = 0
    else:
        f['decline_power_slope'] = 0
        f['decline_power_r2'] = 0
        f['tde_slope'] = 0
        f['tde_slope_match'] = 0
    
    return f

# ============ SYNERGY FEATURES ============
def compute_synergy(f):
    """Compute synergy scores combining all layers"""
    
    # Layer synergy: GTFE constraint + LCC detection
    f['gtfe_lcc_synergy'] = f.get('gtfe_passes', 0) * f.get('lcc_resonates', 0)
    
    # Quantum TDE fingerprint: all layers aligned
    f['quantum_tde_fingerprint'] = (
        f.get('tde_slope_match', 0) * 
        f.get('rate_asymmetry', 1) * 
        f.get('lcc_max', 0)
    )
    
    # Divination confirmation
    f['divination_synergy'] = f.get('divination_tde_match', 0) * f.get('tde_slope_match', 0)
    
    # Tozzi toroidal coherence (closed loop patterns)
    f['tozzi_coherence'] = f.get('tozzi_toroidal', 0) * f.get('sacred_fraction', 0)
    
    # Tessellation field match
    f['tessellation_synergy'] = f.get('green_prop', 0) * (1 + f.get('reflect_sym', 0))
    
    # UNIVERSAL SYNERGY SCORE
    f['universal_synergy'] = (
        0.20 * f.get('gtfe_passes', 0) +
        0.20 * f.get('lcc_resonates', 0) +
        0.15 * f.get('tde_slope_match', 0) +
        0.15 * f.get('sacred_fraction', 0) +
        0.10 * f.get('divination_tde_match', 0) +
        0.10 * f.get('tozzi_toroidal', 0) +
        0.10 * f.get('tessellation_synergy', 0)
    )
    
    return f

# ============ EXTRACT ALL FEATURES ============
def extract_all_features(obj_id, lc_dict):
    """Extract all features for one object"""
    if obj_id not in lc_dict:
        return None
    
    df = lc_dict[obj_id]
    flux = df['Flux'].values
    err = df['Flux_err'].values if 'Flux_err' in df else np.ones(len(flux))
    times = df['mjd'].values if 'mjd' in df else np.arange(len(flux))
    
    flux = flux[~np.isnan(flux)]
    if len(flux) < 5:
        return None
    
    f = {}
    
    # Layer 1: GTFE
    f.update(compute_gtfe(flux, err, times))
    
    # Layer 2: LCC Virus
    f.update(compute_lcc_virus(flux))
    
    # Layer 3: GILE
    f.update(compute_gile(flux, err, times))
    
    # Layer 4: Tessellation
    f.update(compute_tessellation(flux, times))
    
    # Layer 5: Tozzi 14D
    f.update(compute_tozzi_14d(flux, times))
    
    # Layer 6: Divination
    f.update(compute_divination(flux, times))
    
    # Layer 7: Sacred Constants
    f.update(compute_sacred_constants(flux))
    
    # Traditional features
    f.update(compute_traditional(flux, err, times))
    
    # TDE power law
    f.update(compute_tde_powerlaw(flux, times))
    
    # L x E (from GTFE)
    f['L'] = 1 / (f['gtfe_total'] + 1e-8)  # L = luminosity proxy
    f['E'] = f.get('sacred_fraction', 0)    # E = existence stability
    f['LxE'] = f['L'] * f['E']
    
    # Synergy features
    f = compute_synergy(f)
    
    return f

# ============ MAIN EXECUTION ============
print("\nExtracting ALL TI features (7 layers)...")
train_features = []
train_targets = []

for i, r in train_log.iterrows():
    feat = extract_all_features(r['object_id'], train_lc_dict)
    if feat is not None:
        train_features.append(feat)
        train_targets.append(r['target'])
    if (i + 1) % 1000 == 0:
        print(f"  Train: {i+1}/{len(train_log)}")

X_train = pd.DataFrame(train_features)
y_train = np.array(train_targets)

print("\nExtracting test features...")
test_features = []
test_ids = []

for i, r in test_log.iterrows():
    feat = extract_all_features(r['object_id'], test_lc_dict)
    if feat is not None:
        test_features.append(feat)
        test_ids.append(r['object_id'])
    if (i + 1) % 2000 == 0:
        print(f"  Test: {i+1}/{len(test_log)}")

X_test = pd.DataFrame(test_features)

print(f"\nFeatures: {len(X_train.columns)}")

# ============ LAYER 3: MR CONSENSUS (Multi-Model Voting) ============
print("\n" + "="*60)
print("TRAINING (MR Consensus - Multi-Model Voting)")
print("="*60)

scaler = StandardScaler()
X_train_scaled = scaler.fit_transform(X_train.fillna(0))
X_test_scaled = scaler.transform(X_test.fillna(0))

# Multi-model ensemble for TRUE MR consensus (not just ensemble average)
models = {
    'HGB': HistGradientBoostingClassifier(
        learning_rate=0.05,
        max_iter=500,
        max_depth=5,
        min_samples_leaf=20,
        random_state=42
    ),
    'RF': RandomForestClassifier(
        n_estimators=200,
        max_depth=8,
        min_samples_leaf=10,
        random_state=42,
        n_jobs=-1
    ),
    'GB': GradientBoostingClassifier(
        learning_rate=0.03,
        n_estimators=200,
        max_depth=4,
        random_state=42
    )
}

# Cross-validation with MR voting
cv = StratifiedKFold(n_splits=5, shuffle=True, random_state=42)
oof_preds = {name: np.zeros(len(X_train)) for name in models}
test_preds = {name: np.zeros(len(X_test)) for name in models}

for fold, (tr_idx, val_idx) in enumerate(cv.split(X_train_scaled, y_train)):
    X_tr, X_val = X_train_scaled[tr_idx], X_train_scaled[val_idx]
    y_tr, y_val = y_train[tr_idx], y_train[val_idx]
    
    for name, model in models.items():
        model.fit(X_tr, y_tr)
        oof_preds[name][val_idx] = model.predict_proba(X_val)[:, 1]
        test_preds[name] += model.predict_proba(X_test_scaled)[:, 1] / 5

# Individual model F1 scores
print("\nIndividual Model Performance:")
for name in models:
    best_f1 = 0
    best_thresh = 0.5
    for thresh in np.linspace(0.2, 0.6, 41):
        f1 = f1_score(y_train, oof_preds[name] >= thresh)
        if f1 > best_f1:
            best_f1 = f1
            best_thresh = thresh
    print(f"  {name}: F1 = {best_f1:.4f} @ threshold {best_thresh:.3f}")

# MR CONSENSUS: Weighted voting based on agreement
# True MR = confidence increases when multiple models agree
oof_stack = np.column_stack([oof_preds[name] for name in models])
test_stack = np.column_stack([test_preds[name] for name in models])

# MR weighted average (higher weight when models agree)
oof_mean = np.mean(oof_stack, axis=1)
oof_std = np.std(oof_stack, axis=1)
oof_mr = oof_mean * (1 - oof_std)  # Penalize disagreement

test_mean = np.mean(test_stack, axis=1)
test_std = np.std(test_stack, axis=1)
test_mr = test_mean * (1 - test_std)  # Penalize disagreement

# Find optimal threshold for MR consensus
best_f1 = 0
best_thresh = 0.3

for thresh in np.linspace(0.1, 0.5, 41):
    f1 = f1_score(y_train, oof_mr >= thresh)
    if f1 > best_f1:
        best_f1 = f1
        best_thresh = thresh

print(f"\n{'='*60}")
print(f"MR CONSENSUS: OOF F1 = {best_f1:.4f} @ threshold {best_thresh:.3f}")
print(f"{'='*60}")

# Generate submission
y_pred = (test_mr >= best_thresh).astype(int)
submission = pd.DataFrame({
    'object_id': test_ids,
    'target': y_pred
})
submission.to_csv('submission_mallorn_v13.csv', index=False)
print(f"\nPredicted TDEs: {y_pred.sum()} / {len(y_pred)}")
print(f"\n✅ Saved: submission_mallorn_v13.csv")

# ============ FEATURE IMPORTANCE ============
print("\n" + "="*60)
print("TOP FEATURES (RF Importance)")
print("="*60)

rf = models['RF']
rf.fit(X_train_scaled, y_train)
importances = pd.Series(rf.feature_importances_, index=X_train.columns)
importances = importances.sort_values(ascending=False)

print("\nTop 25 features:")
for i, (feat, imp) in enumerate(importances.head(25).items()):
    print(f"  {i+1:2d}. {feat:30s} {imp:.4f}")

# ============ LAYER VALIDATION ============
print("\n" + "="*60)
print("LAYER VALIDATION (TDE vs Non-TDE)")
print("="*60)

key_features = [
    'gtfe_total', 'L', 'lcc_max', 'sacred_fraction', 
    'universal_synergy', 'quantum_tde_fingerprint',
    'divination_tde_match', 'tozzi_toroidal', 'tessellation_synergy',
    'flux_near_e', 'iching_hexagram', 'tarot_arcana'
]

for feat in key_features:
    if feat in X_train.columns:
        tde_mean = X_train.loc[y_train == 1, feat].mean()
        non_tde_mean = X_train.loc[y_train == 0, feat].mean()
        ratio = tde_mean / (non_tde_mean + 1e-8)
        print(f"  {feat:30s}: TDE={tde_mean:.4f}, Non-TDE={non_tde_mean:.4f}, Ratio={ratio:.2f}")

print("\n" + "="*60)
print("TI MALLORN v13 UNIVERSAL INTEGRATION COMPLETE")
print("="*60)
