# THEOREM MAP

Every proved statement, indexed. Line numbers from the v0.1.0-gcc-razor tag.
"Toolkit concept" points into `meta-calculus-toolkit` (Desktop) where the
same mathematics runs numerically; published anchors are in that repo's
`references/` tree and `CITATION_INDEX.md`.

## 1. GCC_CanonicalCore.lean (zero imports, Lean >= 4.7.0)

### Transport (Czachor 2016 Eq. 18; Burgin-Czachor 2020 Ch. 2)

| Name | Line | Meaning | Toolkit concept |
|---|---|---|---|
| `Gen` | 51 | generator = bijection carrier -> base | `core/generators.py` alpha/beta generators |
| `CRing` | 61 | minimal commutative-ring class for the base | base arithmetic |
| `gadd/gmul/gneg/gsub/gzero/gone` | 99-104 | generated arithmetic `g.inv (g.to x (op) g.to y)` | generated arithmetic, `core/derivatives.py:120-145` |
| `gadd_comm` | 107 | transported commutativity | - |
| `gadd_assoc` | 112 | transported associativity | - |
| `gzero_add` | 117 | transported additive identity | coordinate-relative zero |
| `gadd_neg` | 122 | transported inverses | - |
| `gmul_comm` | 127 | transported mul commutativity | - |
| `gmul_assoc` | 132 | transported mul associativity | - |
| `gone_mul` | 137 | transported multiplicative identity | - |
| `gmul_gadd` | 142 | transported distributivity | - |

### The razor

| Name | Line | Meaning |
|---|---|---|
| `razor_add` | 155 | `g.to` maps generated + to base + (one step: conjugation is contentless) |
| `razor_mul` | 159 | same for * |
| `razor_zero` | 163 | same for 0 |
| `razor_one` | 167 | same for 1 |

### Discrete g-calculus (Grossman 1981; Burgin-Czachor 2020 Ch. 4)

| Name | Line | Meaning | Toolkit concept |
|---|---|---|---|
| `gdiff` | 180 | discrete g-derivative | meta-difference |
| `gsum` | 184 | generated running sum | meta-integral (discrete) |
| `gsum_zero/gsum_succ` | 188/191 | unfolding lemmas | - |
| `gFTC` | 199 | g-sum of g-differences telescopes, all generators at once | Fundamental Theorem II, `tests/test_fundamental_theorem_ii.py` |
| `aprog` | 212 | arithmetic progression in the base | - |
| `const_gdiff` | 227 | constant g-derivative -> aprog in coordinates | exponentials are geometric straight lines |
| `aprog_const_gdiff` | 246 | converse | - |
| `const_gdiff_iff` | 255 | the iff | - |

### Mean invariance (phi-demotion) and operation-wise certificates

| Name | Line | Meaning | Toolkit concept |
|---|---|---|---|
| `BMean/gmean` | 275/281 | base mean; quasi-arithmetic (generated) mean | Kolmogorov-Nagumo averages, `scheme_robust_observables.py` |
| `gmean_idem/gmean_comm` | 284/288 | mean laws transport | - |
| `MeanAuto/recoord` | 294/302 | mean-compatible re-coordinatization | scheme change |
| `gmean_recoord` | 318 | re-coordinatization leaves generated mean unchanged: log base is unobservable | phi in Gamma, not phi = source code |
| `RingAuto/recoordRing` | 341/354 | ring-automorphism re-coordinatization | - |
| `gadd/gmul/gneg/gsub/gzero/gone_recoordRing` | 367-402 | operation-wise invariance certificates (which ops survive which chart changes) | scheme-robust vs scheme-fragile observables |

### Pareto discipline

| Name | Line | Meaning | Toolkit concept |
|---|---|---|---|
| `Dominates/scalarize` | 421/425 | dominance; positive-weight scalarization | `multiscale_moo.py` |
| `scalarized_min_is_pareto` | 447 | scalarized minimizers are Pareto-optimal (soundness) | MOO selection validity |
| `Triad/bad_f1/bad_f2` | 481-494 | three-point nonconvex frontier | - |
| `middle_pareto` | 501 | the middle is Pareto-optimal | - |
| `middle_not_scalar_min` | 510 | no positive weights select it (incompleteness witness) | why MOO returns frontiers, not argmins |

(Names with subscript digits appear in source as Unicode subscripts.)

## 2. GccLeanLab/Capstone.lean (Mathlib v4.28.0)

### Charts and flows

| Name | Line | Meaning | Toolkit concept |
|---|---|---|---|
| `Chart` | 33 | chart = `Equiv` state space <-> coordinates | generator bijection |
| `nativeLine` / `apply_nativeLine` | 38/43 | straight motion in chart coordinates | linearizing coordinates |
| `chartEuler` / `apply_chartEuler` | 49/54 | Euler step taken in the chart | log-space integrator step |

### Transported arithmetic (Mathlib idiom; weakest-typeclass discipline)

`gadd..gone` (61-76), laws `gadd_comm` (104) .. `gmul_gadd` (146), simp-facing
`apply_*` razor lemmas (79-101): same content as core section 1, over Mathlib
classes.

### Discrete g-calculus

`gdiff/gsum` (154/158), `gFTC` (170), `aprog` (183),
`const_gdiff/aprog_const_gdiff/const_gdiff_iff` (193/213/221): same as core,
Mathlib classes.

### Means and re-coordinatization

`BMean/gmean` (232/238), `gmean_idem/gmean_comm` (243/248),
`MeanAuto/recoord/gmean_recoord` (252/257/262),
`midpointMean` (269), `scaleMeanAuto` (276),
`gmean_scale_recoord` (292) - the tombstone instance: nonzero rescaling
(e.g. by `1/log phi`) cannot change a generated midpoint mean.
`recoordRing` over `RingEquiv` + six `*_recoordRing` certificates (305-345).

### Pareto

`Dominates/ParetoOptimal/scalarize` (347-355),
`scalarized_min_is_pareto` (359), `Triad` witnesses (378-414).

### The analytic laboratory

| Name | Line | Meaning | Toolkit concept |
|---|---|---|---|
| `PosReal/logChart` | 416/419 | positive reals; log chart as honest `Equiv` | Exponential/Log generators |
| `geometricLine` / `geometricLine_logCoord` | 431/435 | exponential flow; additive in log coordinates | log-space transform (7.7x Lane-Emden speedup) |
| `multiplicativeEuler` / `multiplicativeEuler_pos` | 441/445 | geometric Euler step; positivity by type | positivity-preserving integration |
| `expFlow` / `logRate` / `logRate_expFlow` | 457/461/465 | exponential flow has constant log-rate | geometric derivative constancy |
| `geometricLine_eq_expFlow` / `logRate_geometricLine` | 481/489 | fork-collapse bridge; rate theorem on the canonical object | - |
| `OpenUnit/sigmoid/logit` | 497-504 | bounded states and their chart pieces | logit generator |
| `sigmoid_mem_openUnit/logit_sigmoid/sigmoid_logit/sigmoidToOpenUnit_logit` | 508-573 | the discharged round-trip obligations | - |
| `logitChart` | 579 | (0,1) ~= R as an honest `Equiv` | bounded-state coordinates |
| `logisticLine` / `logisticLine_logitCoord` | 586/591 | logistic straight lines | - |
| `logisticEuler` / `logisticEuler_mem` | 597/602 | bounded Euler step; cannot leave (0,1), by type | constraint preservation |

## 3. GccLeanLab/Tests.lean (~45 witness examples)

Sections: transported arithmetic under `shift5` (generated zero = -5 by
`decide`), discrete FTC concrete + at `logChart` (multiplicative FTC),
straight-line iff on an affine sequence, midpoint-mean values, the
phi-demotion rescaling tombstone, recoordRing certificates, Pareto Triad
numerics + soundness instantiation, log-chart values and flows, closed-form
multiplicative Euler, sigmoid/logit round trips, logitChart equivalence,
boundedness safety. Each is a concrete instantiation that fails to
elaborate if the parent theorem's typeclass assumptions are wrong.

## 4. GccLeanLab/MetaCalculus.lean (the toolkit operator layer)

### Gradient transform safe window (spec for the Python k-guardrail)

| Name | Meaning | Toolkit/agent-maker concept |
|---|---|---|
| `bgTransform` | `g * \|g\| ^ (2k-1)` (rpow) | `BigeometricTransform.transform` |
| `bgTransform_zero` | transform fixes 0 | - |
| `abs_bgTransform` | magnitude law `\|out\| = \|g\| ^ (2k)` | - |
| `bgTransform_pos_of_pos` / `bgTransform_neg_of_neg` | sign preservation | `test_bigeometric_merge_preserves_common_negative_sign` |
| `bgTransform_fixed` | unit magnitudes are fixed points | - |
| `bgTransform_contracts` | 0 < k < 1/2 contracts large gradients - the anti-explosion theorem | `BigeometricConfig.k_max = 0.5` |
| `bgTransform_amplifies_of_k_le_zero` | k <= 0 lifts the noise floor | `BigeometricConfig.k_min > 0` |
| `bgTransform_expands_of_half_lt_k` | k > 1/2 re-amplifies | guardrail upper bound |

### k(L) structural facts (shape only; fitted values stay empirical)

| Name | Meaning |
|---|---|
| `kOf` | `slope * logb 10 L + intercept` |
| `kOf_strictAntiOn` | negative slope -> strictly decreasing on L > 0 |
| `kOf_mem_Icc` | on [1, 10^12] the value stays in [intercept + 12 slope, intercept]; at production constants the lower end is NEGATIVE (witnessed in Tests.lean) - why the optimizer path clamps |

### Bigeometric derivative and Grossman-Katz constancy

| Name | Meaning | Toolkit concept |
|---|---|---|
| `powFlow` | `x ^ n` on PosReal | power-law test family |
| `bgDeriv` / `bgDerivMul` | log-log derivative; `exp` of it | `BigeometricDerivative` |
| `bgDeriv_powFlow` | `bgDeriv (powFlow n) = n` | log-log straight lines |
| `bgDerivMul_powFlow` | `D_BG[x^n] = exp n`, x-independent | `verify_power_law`, `constancy_analysis_v2.json` |

### F007 unified derivative (Grossman 1981)

| Name | Meaning | Toolkit concept |
|---|---|---|
| `f007Deriv` | `(v(a)/u(a)) * beta'(f a) * f'(a) / alpha'(a)`; weights read at the argument (corrected 2026-11-21 from the historical `v(f a)`, matching registry F007) | `UnifiedDerivative.__call__` (core/derivatives.py) |
| `f007_meta` | identity charts, any weights -> `(v a / u a) * f'(a)`; false under the historical reading, witness in Tests | registry F007 correction |
| `f007_classical` | identity charts, unit weights -> `deriv f` | classical specialization |
| `f007_geometric` | log codomain -> `f'/f` (elasticity, NOT exp-wrapped) | the F007-vs-NNC distinction in the module header |
| `f007_geometric_eq_deriv_log` | agrees with `deriv (log . f)` under hypotheses | chain-rule honesty |
| `f007_bigeometric` | log both axes -> `a f'/f` | L_BG elasticity |

### Registry sync (2026-11-21; meta-calculus-portfolio docs/FORMULA_CLAIMS.json)

| Name | Meaning | Registry entry |
|---|---|---|
| `metaDeriv` / `f007_eq_metaDeriv` | `D_{u,v}[f](a) = (v a / u a) * f'(a)`; equals F007 with identity charts | META_DERIVATIVE |
| `metaDeriv_add` / `metaDeriv_const_mul` | additivity and homogeneity for fixed weights, f and g differentiable at a | META_DERIVATIVE_LINEARITY |
| `geomDeriv` | `D_G[f](a) = exp (f'(a) / f(a))`, outer exponential included | GEOMETRIC_DERIVATIVE |
| `geomDeriv_eq_exp_f007` / `geomDeriv_eq_exp_deriv_log` | exp of F007 with log codomain; exp of `deriv (log . f)` under hypotheses | GEOMETRIC_DERIVATIVE |
| `geomDeriv_mul` / `geomDeriv_const` | multiplicative product rule; constants map to 1 | GEOMETRIC_DERIVATIVE |
| `scaledPowFlow` / `bgDeriv_scaledPowFlow` / `bgDerivMul_scaledPowFlow` | `D_BG[c x^m] = e^m` for every c > 0 | BG_SLOPE_POWER_LAW |

### The audit tombstone (AUDIT-2026-06-12, A1)

| Name | Meaning | Toolkit concept |
|---|---|---|
| `signSqrt` / `signSqrtInv` | odd square root and its genuine inverse | `SignedSqrt` (corrected generator) |
| `signSqrtChart` | the corrected odd sqrt IS a chart: both round trips proved - the proofs Python's old `Sqrt` silently failed | `test_generator_round_trip` |

## 5. GccLeanLab/LaneC.lean (Lane C3 registry entries, 2026-11-22)

Registry: meta-calculus-portfolio docs/FORMULA_CLAIMS.json (Kramers-Wannier:
docs/HONEST-STATUS.md section 8). Scope column = how the Lean statement
differs from the registry wording.

| Registry id | Declarations | Scope difference from the registry wording |
|---|---|---|
| F008 (refuted) | `Sym2`, `eigDisc`, `eigHi`, `eigLo`, `eigDisc_sq`, `det_sub_eigHi`, `det_sub_eigLo`, `gap2`, `F008Claim`, `F008HistoricalClaim`, `f008P1`, `f008P2`, `f008_mix`, `gap2_f008P1`, `gap2_f008P2`, `gap2_f008_mix`, `f008_sym`, `f008_refuted`, `f008_historical_refuted` | Claim stated for two symmetric 2x2 real factors whose product is also symmetric (the guarded normal scope); n-factor and n x n versions are not stated, but a two-factor counterexample already refutes the general claim. `gap2` is `spectral_gap` from simulations/spectral_gap_verification.py (second minus first of the sorted absolute eigenvalues) on 2x2 input, with eigenvalues in closed form; `det_sub_eigHi/Lo` check they are characteristic roots. Counterexample diag(1,2), diag(2,1): component gaps 1 and 1, composed gap 0. Not a Markov or Laplacian matrix pair; the grid's nine counterexamples are separate numerical evidence. |
| META_FTC_I | `metaIntegral`, `meta_ftc_I` | Meta-integral taken as `int_r^s u f` (limit of `f(a_i) * meta_measure_u`), meta-derivative `metaDeriv` from MetaCalculus.lean. Hypotheses: u continuous and positive everywhere (META_WEIGHT_DOMAIN; v needs none), f continuous on [r, s]; conclusion at every x in the open interval (r, s), matching "on the interior". |
| META_FTC_II | `metaChange`, `meta_ftc_II`, `metaChange_one` | Meta-change taken in the registry's integral form `int_r^s v h'` (META_CHANGE_ARGUMENT), so the theorem is a pointwise identity needing only u > 0; it holds for every h because both sides use the same `deriv h`. Grossman's partition-sum definition of meta-change is not formalized. `metaChange_one` adds the analytic content for v = 1: meta-change = h s - h r for h differentiable on [r, s] with integrable derivative. |
| LANE_EMDEN_N5_REGULAR | `laneEmdenN5`, `laneEmdenN5_pos`, `laneEmdenN5_hasDerivAt`, `laneEmdenN5_deriv_apply`, `laneEmdenN5_deriv`, `laneEmdenN5_sq_mul`, `laneEmdenN5_ode`, `laneEmdenN5_initial` | theta written as `(sqrt(1 + xi^2/3))^-1`. ODE `theta'' + 2 theta'/xi + theta^5 = 0` proved for every real xi /= 0 (registry: xi >= 0); at xi = 0 the 2 theta'/xi term is singular and is not formalized as a limit. Initial conditions theta(0) = 1, theta'(0) = 0 proved; uniqueness of the regular solution is not. |
| F005 | `NonzeroReal`, `recipChart`, `recipChart_apply`, `recipChart_symm`, `recipChart_involutive`, `recip_injOn`, `recip_hasDerivAt`, `logChart_recip` | Registry states only `alpha(x) = 1/x`; Lean adds what meta_calculus/core/generators.py `Reciprocal` implements: a chart (Equiv) on the nonzero reals that is its own inverse, injectivity on x /= 0, derivative `-(1/x)*(1/x)`, and negation in the log chart on positive reals. Python returns NaN at 0; Lean's `0^-1 = 0` is excluded by the domain. |
| Kramers-Wannier dual map (HONEST-STATUS 8; no registry id) | `kwDual`, `kwDual_spec`, `kwDual_pos`, `kwDual_unique`, `kwDual_kwDual`, `kwDual_eq_self_iff`, `kwCritical`, `kwCritical_pos`, `sinh_two_kwCritical`, `kwDual_kwCritical`, `kwDual_eq_self_iff_critical` | `K* = arsinh(1/sinh 2K)/2` for K > 0: satisfies sinh 2K sinh 2K* = 1, is the unique such coupling, is positive, is an involution; self-dual iff sinh 2K = 1 iff K = log(1 + sqrt 2)/2. The Onsager free-energy duality is not formalized (research-level; stays a numerical check). |

Non-vacuity: each target had a deliberately false variant (wrong composed
gap, D g = f without v, u in place of v in the meta-change, theta^4 in place
of theta^5, derivative sign flipped, sqrt 3 in place of sqrt 2) compiled with
the same proof script; all six failed, then were removed.
