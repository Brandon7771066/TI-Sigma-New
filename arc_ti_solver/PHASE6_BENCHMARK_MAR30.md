# ARC-AGI Phase 6 Benchmark — March 30, 2026

## Final Score: 25/400 = 6.25%

### Phase History
| Phase | Tasks Solved | Solve Rate | Key Addition |
|-------|-------------|------------|--------------|
| Phase 4 (Myrion only) | 15 | 3.75% | Klein V₄, GILE alignment, MR Moot |
| Phase 5 (Domain Routing) | 25 | 6.25% | color_permutation, scale, object_neighbor solvers |
| Phase 6 (Gravity + CC) | 25 | 6.25% | gravity solver, component_recolor, fixed routing |

Net Phase 6 gain: +0 tasks over Phase 5 (gravity wins replaced myrion wins — same total, cleaner architecture).

### Domain Breakdown (Phase 6)
| Domain | Description | Solved | Total | Rate |
|--------|-------------|--------|-------|------|
| 1 | Symmetry / Transforms | 11 | 43 | **25.6%** |
| 2 | Color Permutation | 3 | 72 | 4.2% |
| 3 | Per-Object Neighborhood | 5 | 147 | 3.4% |
| 4 | Resize / Scale | 6 | 138 | 4.3% |

### Method Breakdown
| Method | Wins | Notes |
|--------|------|-------|
| myrion | 14 | Myrion resolution + Klein V₄ + GILE scoring |
| scale_solver | 6 | Integer scale factor detection |
| color_permutation | 3 | Bijective color mapping from training |
| gravity | 2 | Domain 1 (gravity preserves color count → misclassified) |
| **Total** | **25** | |

### Key Architectural Fixes (Phase 6)
1. **Gravity routing fixed**: gravity tasks classified as Domain 1 (color count preserved by falling),
   now checked BEFORE Myrion via `solve_connected_components()` with pattern filter
2. **False positive guard**: `component_recolor_by_size` had 4/5 false positives — isolated from
   Domain 2 routing; only gravity/border patterns trusted in specialist routing
3. **Domain isolation**: specialists only run in their target domain (no cross-domain bleed)

### Near-Miss Analysis (Domain 3, LCC 0.85–0.90)
10 tasks within 10–15% of correct — need LLM program synthesis to cross the threshold:
```
9edfc990  LCC=0.90  10 colors  13×13  3 examples
29c11459  LCC=0.89   5 colors   5×11  2 examples
3ac3eb23  LCC=0.89   4 colors   6×10  2 examples
d06dbe63  LCC=0.88   2 colors  13×13  2 examples
a2fd1cf0  LCC=0.86   3 colors  15×15  3 examples
```

### What's Blocking Further Gains
**LLM Program Synthesis (Phase 7)**
- `llm_program_solver.py` is built and integrated
- Both Claude and GPT-4 via Replit modelfarm return `ApiKeyNotApproved`
- Perplexity API key in secrets returns `Invalid API key`
- **Fix needed**: User must add `ANTHROPIC_API_KEY` or `OPENAI_API_KEY` as a Replit secret
  (direct API keys bypass the modelfarm)

### Solved Tasks (All 25)
```
00d62c1b  [myrion]            08ed6ac7  [myrion]
0d3d703e  [color_permutation] 1cf80156  [scale_solver]
1e0a9b12  [gravity]           3906de3d  [gravity]
3c9b0459  [myrion]            4347f46a  [myrion]
496994bd  [myrion]            5bd6f4ac  [scale_solver]
6150a2bd  [myrion]            67a3c6ac  [myrion]
68b16354  [myrion]            74dd1130  [myrion]
9172f3a0  [scale_solver]      9dfd6313  [myrion]
a416b8f3  [scale_solver]      a5313dff  [myrion]
b1948b0a  [color_permutation] c59eb873  [scale_solver]
c8f0f002  [color_permutation] d10ecb37  [scale_solver]
d511f180  [myrion]            ed36ccf7  [myrion]
f25ffba3  [myrion]
```

### Phase 7 Roadmap
1. **Fix LLM API** → add `ANTHROPIC_API_KEY` secret → Claude for program synthesis
2. **Target**: 10 near-miss Domain 3 tasks via LLM → +10 tasks → 35/400 = 8.75%
3. **Stretch**: Domain 4 LLM assistance → +15 tasks → 50/400 = 12.5%
4. **LLM-validated**: Run full 400-task benchmark with `use_llm=True`
