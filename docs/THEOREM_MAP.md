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
| F008 (refuted) | `Sym2`, `eigDisc`, `eigHi`, `eigLo`, `eigDisc_sq`, `det_sub_eigHi`, `det_sub_eigLo`, `gap2`, `F008Claim`, `F008HistoricalClaim`, `f008P1`, `f008P2`, `f008_mix`, `gap2_f008P1`, `gap2_f008P2`, `gap2_f008_mix`, `f008_sym`, `f008_refuted`, `f008_historical_refuted` | Claim stated for two symmetric 2x2 real factors whose product is also symmetric (the guarded normal scope); n-factor and n x n versions are not stated, but a two-factor counterexample already refutes the general claim. `gap2` is `spectral_gap` from simulations/spectral_gap_verification.py (second minus first of the sorted absolute eigenvalues) on 2x2 input, with eigenvalues in closed form; `det_sub_eigHi/Lo` check they are characteristic roots. Counterexample diag(1,2), diag(2,1): component gaps 1 and 1, composed gap 0. Not a Markov or Laplacian matrix pair; the grid's nine counterexamples are separate numerical evidence. Metric note (Keel review): `gap2` is the spacing between sorted absolute eigenvalues; it is not the subdominant-modulus (Markov) gap used by the triangle implementation, so this does not refute a claim restricted to Markov operators. Fair against the unrestricted registry formula, including the historical stronger bound. |
| META_FTC_I | `metaIntegral`, `meta_ftc_I` | Meta-integral taken as `int_r^s u f` (limit of `f(a_i) * meta_measure_u`), meta-derivative `metaDeriv` from MetaCalculus.lean. Hypotheses: u continuous and positive everywhere (META_WEIGHT_DOMAIN; v needs none), f continuous on [r, s]; conclusion at every x in the open interval (r, s), matching "on the interior". Representation note (Keel review): `metaIntegral` is an ordinary weighted interval integral and `metaDeriv` the weighted ordinary derivative; equivalence with the partition-limit definition is not proved. The output weight v is arbitrary, which is weaker than the published domain requiring both weights continuous and positive (the theorem is therefore stronger there). |
| META_FTC_II | `metaChange`, `meta_ftc_II`, `metaChange_one` | Meta-change taken in the registry's integral form `int_r^s v h'` (META_CHANGE_ARGUMENT), so the theorem is a pointwise identity needing only u > 0; it holds for every h because both sides use the same `deriv h`. Grossman's partition-sum definition of meta-change is not formalized. `metaChange_one` adds the analytic content for v = 1: meta-change = h s - h r for h differentiable on [r, s] with integrable derivative. Conventions note (Keel review): `meta_ftc_II` assumes no differentiability or integrability; it holds by Mathlib's conventions that `deriv` is 0 at non-differentiable points and the integral of a non-integrable function is 0, so it carries little analytic content by itself. It needs u > 0 everywhere (no continuity), and the endpoints may be in either order. |
| LANE_EMDEN_N5_REGULAR | `laneEmdenN5`, `laneEmdenN5_pos`, `laneEmdenN5_hasDerivAt`, `laneEmdenN5_deriv_apply`, `laneEmdenN5_deriv`, `laneEmdenN5_sq_mul`, `laneEmdenN5_ode`, `laneEmdenN5_initial` | theta written as `(sqrt(1 + xi^2/3))^-1`. ODE `theta'' + 2 theta'/xi + theta^5 = 0` proved for every real xi /= 0 (registry: xi >= 0); at xi = 0 the 2 theta'/xi term is singular and is not formalized as a limit. Initial conditions theta(0) = 1, theta'(0) = 0 proved; uniqueness of the regular solution is not. |
| F005 | `NonzeroReal`, `recipChart`, `recipChart_apply`, `recipChart_symm`, `recipChart_involutive`, `recip_injOn`, `recip_hasDerivAt`, `logChart_recip` | Registry states only `alpha(x) = 1/x`; Lean adds what meta_calculus/core/generators.py `Reciprocal` implements: a chart (Equiv) on the nonzero reals that is its own inverse, injectivity on x /= 0, derivative `-(1/x)*(1/x)`, and negation in the log chart on positive reals. Python returns NaN at 0; Lean's `0^-1 = 0` is excluded by the domain. |
| Kramers-Wannier dual map (HONEST-STATUS 8; no registry id) | `kwDual`, `kwDual_spec`, `kwDual_pos`, `kwDual_unique`, `kwDual_kwDual`, `kwDual_eq_self_iff`, `kwCritical`, `kwCritical_pos`, `sinh_two_kwCritical`, `kwDual_kwCritical`, `kwDual_eq_self_iff_critical` | `K* = arsinh(1/sinh 2K)/2` for K > 0: satisfies sinh 2K sinh 2K* = 1, is the unique such coupling, is positive, is an involution; self-dual iff sinh 2K = 1 iff K = log(1 + sqrt 2)/2. The Onsager free-energy duality is not formalized (research-level; stays a numerical check). |

Non-vacuity: each target had a deliberately false variant (wrong composed
gap, D g = f without v, u in place of v in the meta-change, theta^4 in place
of theta^5, derivative sign flipped, sqrt 3 in place of sqrt 2) compiled with
the same proof script; all six failed, then were removed.

## 6. GccLeanLab/LaneC4.lean (Lane C4 registry entries, 2026-11-22)

Registry: meta-calculus-portfolio docs/FORMULA_CLAIMS.json, the agreed
PROVABLE_NOW queue of laneC/TRIAGE.md. Scope column = how the Lean statement
differs from the registry wording, including the Mathlib conventions a proof
relies on. File is ASCII only, so focusing bullets are written `next =>`.

| Registry id | Declarations | Scope difference from the registry wording |
|---|---|---|
| F002 | `idGen`, `idGen_apply`, `idGen_symm_apply`, `idGen_hasDerivAt`, `gadd_idGen`, `gmul_idGen` | `alpha(x) = x` as the chart `Equiv.refl` on R with what generators.py `Identity` implements: inverse is itself, derivative 1, and identity-generated arithmetic is ordinary arithmetic. The chart, inverse and arithmetic identities are definitional; the derivative statement is an analytic theorem supplied by Mathlib (Keel review). |
| F003 | `expGen`, `expGen_apply`, `expGen_symm_apply`, `expGen_hasDerivAt`, `range_expGen`, `logChart_apply`, `gadd_logChart`, `gmul_logChart`, `gzero_logChart` | `alpha(x) = exp(x)` as a chart from R onto the positive reals (`logChart.symm`), inverse log, derivative exp, range exactly (0, inf) (Python returns NaN off it). Adds the generated arithmetic: exp-addition is multiplication, exp-multiplication is `x ^ log y`, exp-zero is 1. |
| F004 | `logGen`, `logGen_apply`, `logGen_symm_apply`, `logGen_hasDerivAt`, `expGen_eq_logGen_symm`, `gadd_logGen_symm`, `gmul_logGen_symm` | `alpha(x) = ln(x)` as a chart on its domain (0, inf), inverse exp, derivative 1/x for x > 0. Its domain is not all of R, so it is a generator only in the chart sense, not in the NNC_GENERATOR sense (its inverse exp is). ln-addition is log-sum-exp; ln-multiplication is ordinary addition. Uses the inherited ordinary addition and multiplication on the positive reals for `+` and `*` there (positive reals with ordinary addition are not a field; Keel review). |
| NNC_GENERATOR | `nncGen`, `nncGen_apply`, `nncGen_add`, `nncGen_mul`, `id_isGenerator`, `exp_isGenerator`, `sqrtAbs_not_isGenerator` | A one-to-one `alpha : R -> R` gives `Equiv.ofInjective : R ~ range alpha`, so A = range alpha and alpha carries + and * to alpha-addition and alpha-multiplication (the other arithmetic laws transport by Capstone.lean section 2). The source's examples I and exp are one-to-one; the audit's old `sqrt |x|` is not. Order on A is not formalized here. |
| NNC_STAR_ISOMORPHISM | `gdiv`, `apply_gdiv`, `iota`, `iota_apply`, `b_iota`, `iota_nncGen`, `iota_bijective`, `iota_gadd`, `iota_gsub`, `iota_gmul`, `iota_gdiv`, `iota_gzero`, `iota_gone`, `iota_lt_iff` | Stated for arbitrary charts `a = alpha^-1 : X ~ R`, `b = beta^-1 : Y ~ R`, with `iota = a.trans b.symm`; `iota_nncGen` recovers `iota(alpha t) = beta t`, i.e. `iota(x) = beta(alpha^-1 x)`. One-to-one and onto B, preserves add, sub, mul, div, zero, one. Order preservation is for the chart-induced orders (`x <_alpha y` iff `a x < a y`), which makes it immediate; that these coincide with the real order on A and B for increasing generators is not proved. |
| NNC_STAR_DERIVATIVE | `starQuot`, `b_starQuot`, `coordRep`, `StarTendsto`, `starDeriv`, `starTendsto_quot_iff`, `starTendsto_starDeriv`, `starTendsto_unique`, `starDeriv_gadd`, `starDeriv_gmul_const`, `starDeriv_classical`, `starDeriv_geometric`, `starDeriv_bigeometric` | The *-limit is defined through the charts: the argument tends to x0 in the topology transported by a (punctured) and values converge in the topology transported by b. Main theorem: the beta-quotient has *-limit L iff `beta^-1 o f o alpha` has classical derivative `b L` at `a x0`. The value lies in B by its type. beta-additivity and beta-homogeneity need differentiability of the coordinate representatives. f is total on X (source: defined on an alpha-interval around a). "Only *-uniform functions have constant derivative" is not formalized. Specializations: identity charts give `deriv`, (id, log) gives `geomDeriv`, (log, log) gives `bgDerivMul`. Totality note (Keel review): `starDeriv` is a total definition; at a non-differentiable coordinate representative Mathlib's derivative defaults to 0, so `starDeriv` then returns the codomain chart's inverse at 0. The substantive content is the limit characterization and the existence theorem under differentiability, not the definition's value everywhere. |
| BG_DERIVATIVE | `starQuot_logChart`, `bgDeriv_eq_elasticity`, `bgDerivMul_eq_exp_elasticity` | For `f : PosReal -> PosReal` agreeing with a real F that is differentiable at x: `D_BG[f](x) = exp(x F'(x) / F(x))`. The limit definition is covered by `starDeriv_bigeometric` plus `starTendsto_quot_iff` at (logChart, logChart), and `starQuot_logChart` identifies the quotient with Grossman-Katz's `(f(x)/f(a))^(1/(ln x - ln a))`. Hypothesis is differentiability of F at x, not existence and positivity of the limit; positivity of f is carried by the type. |
| META_WEIGHT_DOMAIN | `IsWeight`, `isWeight_one`, `isWeight_exp`, `IsWeight.mul`, `IsWeight.div`, `not_isWeight_id`, `metaDeriv_pos_iff`, `metaDeriv_eq_zero_iff`, `meta_ftc_I_of_weight` | `IsWeight w` = continuous and positive on all of R. Defining consequences: 1 and exp are weights, weights are closed under product and quotient (so v/u is a weight), the identity is not one, under a weight pair the meta-derivative has the sign and zeros of the classical derivative, and META_FTC_I applies to every weight u. |
| META_MEASURE_ARGUMENT | `metaMeasure`, `metaMeasure_eq_metaIntegral_one`, `metaMeasure_one`, `metaMeasure_pos`, `metaMeasure_add`, `metaMeasure_exp` | Meta-measure taken in the registry's integral form `int_r^s u` (interval integral, endpoints in either order). Proved: it is the meta-integral of 1, unit weight gives s - r, a weight gives positive measure for r < s, additivity over adjacent intervals, the value for u = exp. Grossman's limit over n-fold arithmetic partitions (Riemann sums of `u(a_i)`) is not formalized. Totalized integral (Keel review): a non-integrable integrand gives 0; genuine weights are integrable on finite intervals, so the stated results do not rely on that default. |
| META_CHANGE_ARGUMENT | `metaChange_def`, `metaChange_eq_metaIntegral`, `metaChangeAtValue`, `metaChange_ne_atValue` (with `metaChange`, `meta_ftc_II`, `metaChange_one` from LaneC.lean) | Meta-change in the registry's integral form `int_r^s v f'`, i.e. the v-meta-integral of f'. The point of the entry (v read at arguments, not at values) is proved by a witness: v = exp, f(x) = x + 1 on [0, 1] gives `e - 1` against `e^2 - e` for the value reading. Uses Mathlib's `deriv`, which is 0 where f is not differentiable (the registry assumes f smooth), and the totalized integral, which is 0 for a non-integrable integrand; the unrestricted meta-change identities do not establish integrability (Keel review). The argument-versus-value witness is substantive. Partition-sum definition not formalized. |
| CZACHOR_TRANSPORTED_ARITHMETIC | `czachorField`, `czachor_add`, `czachor_mul`, `czachor_map_add`, `czachor_map_mul` (with `gadd`, `gmul` and their laws in Capstone.lean) | For a bijection `f : X ~ R`, Mathlib's `Equiv.field` transports the whole field structure, and its + and * are definitionally Czachor's `f^-1(f x + f y)` and `f^-1(f x * f y)`; f is additive and multiplicative for it. Covers only encodings onto all of R, where closure of the range is automatic; for a proper range (e.g. exp onto (0, inf)) only `gadd`/`gmul` and the Capstone laws apply, and the registry's closure condition is not formalized. |
| BH_ENTROPY_CHART | `bhSRef`, `bhSRef_pos`, `le_bhSRef`, `bhEntropyChart`, `bhEntropyStar`, `bhEntropyStar_apply`, `bhEntropyChart_strictMono`, `bhEntropyChart_add`, `bhEntropyChart_hasDerivAt` | `S -> exp(S / S_ref)` is a chart R ~ (0, inf) with inverse `S_ref log`, for any S_ref > 0; `S_ref = max(k_B, S_BH(M0)) >= k_B > 0`. "Not new dynamics": strictly monotone, additive entropies become products, and along any differentiable history `dS*/dt = S* S'/S_ref` has the sign of S'. S_BH(M0) is a free real parameter here; units are not modeled. |
| SCHWARZSCHILD_RADIUS | `schwarzschildRadius`, `schwarzschildRadius_pos`, `schwarzschildRadius_mul`, `schwarzschildRadius_add`, `mass_of_schwarzschildRadius`, `schwarzschild_factor_eq_zero_iff` | Definition `2 G M / c^2` with: positive for G, M, c > 0, proportional (and additive) in M, M recovered from r_s, and the metric factor `1 - r_s/r` vanishes exactly at r = r_s (r /= 0). The metric itself and its derivation from the Einstein equations are not formalized. |
| SHANNON_NORMALIZED_ENTROPY | `shannonH`, `shannonNorm`, `IsProb`, `shannonH_eq`, `zero_mul_log_zero`, `IsProb.le_one`, `shannonH_nonneg`, `shannonH_single`, `shannonH_uniform`, `shannonH_le_log`, `shannonNorm_mem`, `shannonNorm_uniform`, `shannonNorm_card_one` | Over any finite index type, N = its cardinality, natural log. `0 log 0 = 0` comes from Mathlib's `log 0 = 0` (via `Real.negMulLog`). Proved: H >= 0, H = 0 for a certain outcome, H = log N at the uniform distribution, H <= log N (Jensen on `negMulLog`), normalized entropy in [0, 1] for N > 1 and 1 at uniform. N = 1 gives 0 because Mathlib has `log 1 = 0` and `x / 0 = 0`, matching the project convention by accident of convention. Not proved: uniqueness of the maximizer, or that H = 0 only for certain outcomes. |
| STM_FERMI_DERIVATIVE | `fermi`, `stmKernel`, `fermi_hasDerivAt`, `stmKernel_pos`, `stmKernel_neg`, `stmKernel_zero` | `K(E) = sech(E/(2kT))^2/(4kT)` with sech written `(cosh)^-1` and kT = k_B T > 0 one parameter. Proved: K = -df/dE for the Fermi function `1/(1 + exp(E/kT))`, K > 0, K even, `K(0) = 1/(4kT)`. Not proved: normalization `int K dE = 1`. The voltage-to-energy conversion is outside the statement. |
| AMPLITUDE_FOUR_POINT_ASSOCIAHEDRON | `fourPoint_pullback`, `fourPoint_canonical`, `fourPoint_pos`, `fourPoint_symm`, `fourPoint_residue` | One-forms are not formalized; the pullback of `ds/s - dt/t` to `t = C - s` is stated as the derivative of `log s - log(C - s)` on 0 < s < C, which is `1/s + 1/t`. Adds: canonical form `C/(s t)`, positivity on the interior, s <-> t symmetry, and the positive endpoint coefficient limit 1 at s = 0 (the theorem concerns a scalar coefficient; for the differential form, changing from s to t reverses orientation, so the upper-boundary residue has the opposite sign; Keel review). |
| BH_RADIATION_ENTROPY | `bhEntropy`, `hawkingTemp`, `bhEntropy_eq`, `bhEntropy_hasDerivAt`, `radEntropy`, `closureEntropy`, `radEntropy_add_closure`, `bhEntropy_mono`, `radEntropy_nonneg`, `radEntropy_hasDerivAt` | S_BH (r_s form) and T_H enter as the registry definitions, not derived. Proved: `S_BH = 4 pi k_B G M^2/(hbar c)`, first law `dS_BH/dM = c^2/T_H`, S_rad + S_closure = S_BH(M0) - S_BH(M), and for 0 <= M <= M0 S_rad >= 0 and S_closure <= 0. `radEntropy_hasDerivAt` proves `dS_rad/dM = (4/3)(-c^2)/T_H`, which is the photon-gas relation `dS = (4/3) dE/T` at T = T_H; the relation `s = 4u/(3T)` itself is the idealization, not proved. The radiation and closure entropies are definitions; differentiating the stipulated radiation entropy verifies consistency with the photon-gas relation, it does not derive the 4/3 factor from an independently formalized radiation model (Keel review). "No unitarity" is a physics remark with no formal content. |
| BH_BLACKBODY_EVAPORATION | `stefanBoltzmann`, `bhPower`, `evapK`, `evapK_div`, `bhPower_div`, `evapMass`, `evapTime`, `evapMass_hasDerivAt`, `evapMass_zero`, `evapMass_evapTime`, `evapMass_solves` | sigma and `P = 4 pi r_s^2 sigma T_H^4` are definitions with the registry's formulas. Proved: `P/c^2 = hbar c^4/(15360 pi G^2 M^2)`; the explicit history `M(t) = (M0^3 - 3Kt)^(1/3)` (real rpow) solves `dM/dt = -P/c^2` while `M0^3 - 3Kt > 0`, starts at M0 (M0 >= 0) and is 0 at `t_evap = 5120 pi G^2 M0^3/(hbar c^4)`. Not proved: uniqueness of the ODE solution. `information_recovery_time` (the plotting midpoint) is not covered. |
| COSMOLOGY_REGULATED_VACUUM | `vacuum_prefactor`, `regulated_vacuum` | Bochner integral over (0, inf) for E_c > 0, evaluated with Mathlib's Gamma integral (`Gamma 4 = 3! = 6`); the phase-space prefactor `(1/2) 4 pi/(2 pi)^3 = 1/(4 pi^2)` is a separate identity. Mathlib's integral is 0 for a non-integrable function, so the nonzero value also certifies integrability. SI conversion and the naturalness caveats are outside the statement. |
| QUANTUM_PROJECTIVE_ANGLE | `projAngle`, `projAngle_smul`, `projAngle_comm`, `projAngle_self`, `projAngle_nonneg`, `projAngle_le_pi_div_two`, `projAngle_of_inner_eq_zero` | Any complex inner product space (registry: finite vectors). Proved: invariance under nonzero complex rescaling of either vector (the phase quotient), symmetry, angle 0 for a ray with itself, range [0, pi/2] (from nonnegativity and Mathlib's totalized arccosine, which returns 0 above 1; it does not establish that the normalized overlap is at most 1; Keel review), pi/2 for orthogonal vectors. For a zero vector Mathlib's `x/0 = 0` gives pi/2; the registry excludes zero vectors. Not proved: the triangle inequality (metric on projective space) or the stacked-real-coordinate equivalence. |
| QUANTUM_STATIONARY_STATE | `stationaryPhase`, `stationaryPhase_eq`, `stationaryState`, `stationaryState_zero`, `stationaryPhase_hasDerivAt`, `stationaryState_schrodinger`, `norm_stationaryState` | Complex normed space, Ham a continuous linear operator, eigen-equation `Ham psi0 = E_n psi0` with E_n real. Proved: `psi(t) = exp(-i E_n t/hbar) psi0` (phase written with a real angle; `stationaryPhase_eq` gives the registry form) has `psi(0) = psi0`, satisfies `i hbar psi' = Ham psi` (hypothesis hbar /= 0), and keeps its norm. Not proved: uniqueness of the Schroedinger solution with that initial value. |
| QUANTUM_SPECTRAL_FUNCTION | `specFun`, `inner_basis_sum`, `specFun_basis`, `specFun_one`, `specFun_mul` | f(H) is a spectral-sum construction `sum_n f(E_n) <n|v> |n>` from an arbitrary orthonormal basis and real labels (finite index set); no independently supplied Hamiltonian is connected to those data, and the basis identity verifies the construction (Keel review). Proved: `f(H)|n> = f(E_n)|n>`, the constant 1 gives the identity, and `(fg)(H) = f(H) g(H)` (so polynomial f agree with operator powers). Not related here to Mathlib's continuous functional calculus. |
| BH_STATE_ENTROPY | `vonNeumann`, `matLog`, `neg_trace_mul_matLog`, `density_isProb`, `vonNeumann_bounds` | rho a complex Hermitian matrix; S_vN defined from Mathlib's eigenvalues; `log rho` defined on the eigenbasis as `U diag(log p) U*`, with Mathlib's `log 0 = 0` giving `0 log 0 = 0` on the kernel. Proved: `-Tr(rho log rho) = -sum p log p`; for positive semidefinite trace-one rho the eigenvalues form a probability vector and `0 <= S_vN <= log N`. Uses `open scoped ComplexOrder` for positive semidefiniteness. The entanglement-entropy interpretation is not formalized. |
| MULTIMETRIC_DIFFUSION_COORDINATES | `diffusion_stationary`, `diffusion_power_eq`, `diffusion_distance` | Finite chain. Assumes a complete pi-orthonormal right eigenbasis: `P Psi = Psi diag(lam)` and `Psi^T diag(pi) Psi = 1` (columns of Psi are the psi_j), pi > 0. From these: `P^t = Psi diag(lam^t) Psi^T diag(pi)` and the pi-weighted row distance equals the Euclidean distance of all N coordinates `lam_j^t psi_j(i)` (signed powers allowed, nonnegative integer t). Reversibility and connectedness are not used, and the existence of such a basis (spectral theorem for a reversible chain) is not derived. `diffusion_stationary` separately proves `pi_u = d_u / sum d` is stationary for `P_uv = W_uv / d_u` with W symmetric and d > 0. These are conditional matrix identities: stationarity does not need nonnegative weights, and the distance theorem's weights are not automatically connected to that construction (Keel review). Truncation to fewer modes is not covered. |
| QUANTUM_REAL_MATRIX_EMBEDDING | `realEmbed`, `realJ`, `realEmbed_re_im`, `map_re_mul`, `map_im_mul`, `realEmbed_mul`, `realEmbed_add`, `realEmbed_one`, `realEmbed_I`, `realJ_mul_self`, `realEmbed_conjTranspose`, `realEmbed_mul_realJ`, `realEmbed_injective` | Square matrices over any finite index type, block form via `Matrix.fromBlocks` on `n + n`. Proved: the registry form `Gamma(A + iB) = [[A, -B], [B, A]]`; Gamma is additive, multiplicative, unital and injective; `Gamma(i 1) = J`, `J^2 = -1`, adjoint goes to transpose, Gamma commutes with J. Multipartite composition is not covered (as the registry says). |
| AMPLITUDE_BCFW_CROSSING | `spinorMomentum`, `spinorMomentum_det`, `bcfw_crossing`, `spinorMomentum_littleGroup`, `bcfw_crossing_alt` | Momenta as 2x2 bispinors `p = lambda lambdatilde^T` (outer product), which are null (det 0). Proved: `(i lambda, i lambdatilde)` is a spinor decomposition of -P. Also proved: the little-group rescaling `(s lambda, s^-1 lambdatilde)` leaves P fixed and `(-lambda, lambdatilde)` also gives -P, so the registry rule is a valid convention, not a forced one. Helicity and sewing-sign conventions are not formalized. |

Non-vacuity: each of the 26 entries had one deliberately false variant compiled
with the same proof script (identity-addition read as multiplication, exp-addition
as addition, ln-multiplication as multiplication, alpha carrying + to *, iota
carrying + to *, the *-limit read as minus the derivative, elasticity without the
factor x, the weight sign reversed, unit meta-measure r - s, meta-change different
from e - 1, Czachor + read as *, entropy chart additive, horizon at 2 r_s,
H <= log N / 2, kernel = +df/dE, coefficient 1/s - 1/t, radiation entropy rising
with M, evaporation rate doubled, Gamma(4) dropped, a ray orthogonal to itself,
Schroedinger without i, f(H)|n> = (f(E_n) + 1)|n>, trace sign dropped, square
dropped on the diffusion side, Gamma reversing products, crossing giving +P); all
26 failed, then were removed. `#print axioms` on 92 main declarations: only
propext, Classical.choice, Quot.sound.
