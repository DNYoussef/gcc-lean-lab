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

## Planned (Phase 3 of META_CALCULUS_VALIDATION_PLAN)

`GccLeanLab/MetaCalculus.lean`: `geomDeriv`, `bgDeriv`, `bgDerivMul` +
power-law constancy (`bgDerivMul_powFlow = exp n`); F007 unified derivative
with classical/geometric/bigeometric specialization lemmas; `bgTransform`
contraction/amplification theorems (the k-guardrail spec); `kOf` structural
monotonicity/bounds (never the fitted coefficients).
