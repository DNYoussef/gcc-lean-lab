/-
# Meta-calculus operator layer

Formalizes the operator core of the meta-calculus toolkit
(Desktop/meta-calculus-toolkit, `meta_calculus/core/derivatives.py`):

* the gradient transform `g * |g| ^ (2k-1)` and its safe window (0, 1/2] -
  the formal spec for the Python k-guardrail
  (`BigeometricConfig.k_min/k_max` in the-agent-maker);
* the affine k(L) form's structural facts (monotonicity, range bounds) -
  never the fitted coefficients, which are empirical;
* the bigeometric derivative through log charts and the Grossman-Katz
  power-law constancy `D_BG[x^n] = e^n` (the toolkit's `verify_power_law`,
  checked numerically there, proved here);
* the F007 unified derivative `(v(f a)/u a) * beta'(f a) * f'(a) / alpha'(a)`
  (Grossman 1981 meta-calculus weights) with specialization lemmas showing
  it subsumes the classical, geometric, and bigeometric derivatives.

Published anchors (in the toolkit's references/ tree): Grossman & Katz 1972,
Grossman 1981 *Meta-Calculus*, Grossman 1983 *Bigeometric Calculus*,
Bashirov et al. 2008. Design note: F007 is stated over plain functions, not
`Equiv`s - the derivative formula needs differentiability, not bijectivity,
and the toolkit's `UnifiedDerivative` likewise just evaluates the formula.
-/

import GccLeanLab.Capstone

noncomputable section

namespace GCC

/-! ## 1. The bigeometric gradient transform and its safe window

`bgTransform k g = g * |g| ^ (2k-1)`, so `|bgTransform k g| = |g| ^ (2k)`.
The Python optimizer path (`BigeometricTransform.transform`) clamps k to
[0.05, 0.5]; these theorems are why. -/

/-- The k-weighted gradient transform `g * |g| ^ (2*k - 1)` (real rpow). -/
def bgTransform (k g : ℝ) : ℝ :=
  g * |g| ^ (2 * k - 1)

@[simp]
theorem bgTransform_zero (k : ℝ) : bgTransform k 0 = 0 := by
  simp [bgTransform]

/-- Magnitude law: the transform raises the magnitude to the power 2k. -/
theorem abs_bgTransform (k : ℝ) {g : ℝ} (hg : g ≠ 0) :
    |bgTransform k g| = |g| ^ (2 * k) := by
  have habs : (0 : ℝ) < |g| := abs_pos.mpr hg
  rw [bgTransform, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (abs_nonneg g) _)]
  calc |g| * |g| ^ (2 * k - 1)
      = |g| ^ (1 : ℝ) * |g| ^ (2 * k - 1) := by rw [Real.rpow_one]
    _ = |g| ^ (1 + (2 * k - 1)) := (Real.rpow_add habs 1 (2 * k - 1)).symm
    _ = |g| ^ (2 * k) := by rw [show (1 : ℝ) + (2 * k - 1) = 2 * k by ring]

/-- Sign preservation, positive case. -/
theorem bgTransform_pos_of_pos (k : ℝ) {g : ℝ} (hg : 0 < g) :
    0 < bgTransform k g :=
  mul_pos hg (Real.rpow_pos_of_pos (abs_pos.mpr (ne_of_gt hg)) _)

/-- Sign preservation, negative case. -/
theorem bgTransform_neg_of_neg (k : ℝ) {g : ℝ} (hg : g < 0) :
    bgTransform k g < 0 :=
  mul_neg_of_neg_of_pos hg (Real.rpow_pos_of_pos (abs_pos.mpr (ne_of_lt hg)) _)

/-- Unit-magnitude gradients are fixed points for every k. -/
theorem bgTransform_fixed (k : ℝ) {g : ℝ} (h : |g| = 1) :
    bgTransform k g = g := by
  rw [bgTransform, h, Real.one_rpow, mul_one]

/-- THE anti-explosion theorem: inside the safe window 0 < k < 1/2, the
transform strictly contracts every large gradient. -/
theorem bgTransform_contracts {k g : ℝ} (hk0 : 0 < k) (hk : k < 1 / 2)
    (hg : 1 < |g|) : |bgTransform k g| < |g| := by
  have hgne : g ≠ 0 := by
    intro h
    rw [h, abs_zero] at hg
    linarith
  rw [abs_bgTransform k hgne]
  calc |g| ^ (2 * k) < |g| ^ (1 : ℝ) := by
        rw [Real.rpow_lt_rpow_left_iff hg]
        linarith
    _ = |g| := Real.rpow_one _

/-- Below the window (k <= 0), every gradient with 0 < |g| < 1 is strictly
amplified (pointwise; the divergence of `|g| ^ (2k)` as g -> 0 for k < 0 is
the limit-level reading, not proved here). This is why the Python guardrail
has `k_min > 0`. -/
theorem bgTransform_amplifies_of_k_le_zero {k g : ℝ} (hk : k ≤ 0)
    (hg0 : 0 < |g|) (hg1 : |g| < 1) : |g| < |bgTransform k g| := by
  have hgne : g ≠ 0 := abs_pos.mp hg0
  rw [abs_bgTransform k hgne]
  calc |g| = |g| ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ < |g| ^ (2 * k) :=
        Real.rpow_lt_rpow_of_exponent_gt hg0 hg1 (by linarith)

/-- Above the window (k > 1/2) large gradients are strictly amplified:
explosion returns. This is why the Python guardrail has `k_max = 1/2`. -/
theorem bgTransform_expands_of_half_lt_k {k g : ℝ} (hk : 1 / 2 < k)
    (hg : 1 < |g|) : |g| < |bgTransform k g| := by
  have hgne : g ≠ 0 := by
    intro h
    rw [h, abs_zero] at hg
    linarith
  rw [abs_bgTransform k hgne]
  calc |g| = |g| ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ < |g| ^ (2 * k) := by
        rw [Real.rpow_lt_rpow_left_iff hg]
        linarith

/-! ## 2. Structural facts about the affine k(L) form

Only the SHAPE is mathematics; the fitted coefficients (-0.0137, 0.1593,
R^2 = 0.71 on 8 points) are empirical and live in the toolkit's
identifiability tests, not here. -/

/-- The affine-in-log10 k formula: `k(L) = slope * log10 L + intercept`. -/
def kOf (slope intercept L : ℝ) : ℝ :=
  slope * Real.logb 10 L + intercept

/-- Negative slope makes k strictly decreasing on positive scales. -/
theorem kOf_strictAntiOn {slope intercept : ℝ} (h : slope < 0) :
    StrictAntiOn (kOf slope intercept) (Set.Ioi 0) := by
  intro a ha b hb hab
  have hlog : Real.logb 10 a < Real.logb 10 b :=
    Real.logb_lt_logb (by norm_num) ha hab
  have := mul_lt_mul_of_neg_left hlog h
  simp only [kOf]
  linarith

/-- Range bound: across scales L in [1, 10^12] the affine form stays inside
[intercept + 12*slope, intercept]. Instantiated at the production constants
this interval EXITS the transform's safe window, which is exactly why the
optimizer-facing Python path clamps k. -/
theorem kOf_mem_Icc {slope intercept L : ℝ} (h : slope < 0)
    (hL1 : 1 ≤ L) (hL2 : L ≤ (10 : ℝ) ^ (12 : ℝ)) :
    kOf slope intercept L ∈ Set.Icc (intercept + 12 * slope) intercept := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
  have hlog0 : 0 ≤ Real.logb 10 L :=
    Real.logb_nonneg (by norm_num) hL1
  have hlog12 : Real.logb 10 L ≤ 12 := by
    have h2 : Real.logb 10 L ≤ Real.logb 10 ((10 : ℝ) ^ (12 : ℝ)) := by
      first
        | exact Real.logb_le_logb (by norm_num) hL2
        | exact Real.logb_le_logb_of_le (by norm_num) hL0 hL2
        | exact Real.logb_le_logb_right (by norm_num) hL2
        | (gcongr <;> first | assumption | norm_num)
    have h12 : Real.logb 10 ((10 : ℝ) ^ (12 : ℝ)) = (12 : ℝ) := by
      rw [Real.logb_rpow] <;> norm_num
    linarith
  constructor
  · simp only [kOf]
    nlinarith
  · simp only [kOf]
    nlinarith

/-! ## 3. The bigeometric derivative and Grossman-Katz power-law constancy

The bigeometric derivative reads a positive-to-positive map through log
charts on BOTH axes; its multiplicative form is `D_BG[f](x) = exp(bg f x)`.
The toolkit checks `D_BG[x^n] = e^n` numerically (`verify_power_law`,
`constancy_analysis_v2.json`, CV = 0.0000); here it is a theorem. -/

/-- Power flow `x ^ n` on positive reals, positivity carried by the type. -/
def powFlow (n : ℝ) (x : PosReal) : PosReal :=
  ⟨x.1 ^ n, Real.rpow_pos_of_pos x.property n⟩

/-- Log-log (additive) form of the bigeometric derivative. -/
def bgDeriv (f : PosReal → PosReal) (x : PosReal) : ℝ :=
  deriv (fun u : ℝ => Real.log (f (logChart.symm u)).1) (Real.log x.1)

/-- Multiplicative form: `D_BG[f](x) = exp (bgDeriv f x)`. -/
def bgDerivMul (f : PosReal → PosReal) (x : PosReal) : ℝ :=
  Real.exp (bgDeriv f x)

/-- Power functions have constant bigeometric log-derivative `n`: in log-log
coordinates `x ^ n` is the straight line of slope n. -/
theorem bgDeriv_powFlow (n : ℝ) (x : PosReal) :
    bgDeriv (powFlow n) x = n := by
  unfold bgDeriv
  have hfun : (fun u : ℝ => Real.log ((powFlow n) (logChart.symm u)).1)
      = fun u : ℝ => n * u := by
    funext u
    change Real.log ((Real.exp u) ^ n) = n * u
    rw [Real.log_rpow (Real.exp_pos u), Real.log_exp]
  rw [hfun]
  have h : HasDerivAt (fun u : ℝ => n * u) n (Real.log x.1) := by
    simpa using (hasDerivAt_id (Real.log x.1)).const_mul n
  exact h.deriv

/-- Grossman-Katz constancy: `D_BG[x ^ n] = e ^ n`, independent of x. -/
theorem bgDerivMul_powFlow (n : ℝ) (x : PosReal) :
    bgDerivMul (powFlow n) x = Real.exp n := by
  unfold bgDerivMul
  rw [bgDeriv_powFlow]

/-! ## 4. The F007 unified derivative

`D*_w f(a) = (v(f a) / u a) * beta'(f a) * f'(a) / alpha'(a)`
(toolkit `core/derivatives.py:26-40`; Grossman 1981). The specialization
lemmas prove the formula subsumes the classical, geometric, and bigeometric
derivatives - the keystone the Python `UnifiedDerivative` implements. -/

/-- The F007 weighted unified derivative.

Stated over bare `deriv`: where a function is not differentiable, Mathlib's
`deriv` is 0 and the formula degrades accordingly (0-division yields 0 in
real-field convention). Generators alpha/beta are assumed smooth and
invertible by USERS of the formula; the specialization lemmas below are
unconditional identities about the formula itself - the honest analytic
statement under hypotheses is `f007_geometric_eq_deriv_log`. -/
def f007Deriv (u v alpha beta : ℝ → ℝ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  (v (f a) / u a) * deriv beta (f a) * deriv f a / deriv alpha a

/-- Classical specialization: unit weights, identity generators. -/
theorem f007_classical (f : ℝ → ℝ) (a : ℝ) :
    f007Deriv (fun _ => 1) (fun _ => 1) id id f a = deriv f a := by
  simp [f007Deriv]

/-- Geometric specialization: log codomain generator yields `f' / f`, the
log-derivative whose exponential is the Grossman geometric derivative.
An unconditional FORMULA identity (`deriv f a` appears on both sides, junk
values included); see `f007_geometric_eq_deriv_log` for the version with
differentiability hypotheses. -/
theorem f007_geometric (f : ℝ → ℝ) (a : ℝ) :
    f007Deriv (fun _ => 1) (fun _ => 1) id Real.log f a
      = deriv f a / f a := by
  simp [f007Deriv, Real.deriv_log]
  ring

/-- The geometric specialization agrees with the honest chain-rule object
`deriv (log ∘ f)` wherever f is differentiable and nonvanishing. -/
theorem f007_geometric_eq_deriv_log {f : ℝ → ℝ} {a : ℝ}
    (hf : DifferentiableAt ℝ f a) (hfa : f a ≠ 0) :
    f007Deriv (fun _ => 1) (fun _ => 1) id Real.log f a
      = deriv (fun s => Real.log (f s)) a := by
  rw [f007_geometric, deriv.log hf hfa]

/-- Bigeometric specialization: log generators on BOTH axes yield
`a * f'(a) / f(a)`, the log of `D_BG[f](a) = exp(a f'/f)`. Unconditional
formula identity, same caveat as `f007_geometric`. -/
theorem f007_bigeometric (f : ℝ → ℝ) (a : ℝ) :
    f007Deriv (fun _ => 1) (fun _ => 1) Real.log Real.log f a
      = a * deriv f a / f a := by
  simp [f007Deriv, Real.deriv_log, div_eq_mul_inv, inv_inv]
  ring

/-! ## 5. The audit's tombstone: signSqrtChart

The toolkit's original `Sqrt` generator mapped x to sqrt|x| while inverting
as y^2 - silently wrong for x < 0 (AUDIT-2026-06-12, finding A1). That
object is unconstructible here: a `Chart` is an `Equiv`, and Lean demands
the two round-trip proofs below. The corrected Python class `SignedSqrt`
cites this chart as its formal counterpart. -/

/-- Odd square root `sign(x) * sqrt |x|`, written piecewise. -/
def signSqrt (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.sqrt x else -Real.sqrt (-x)

/-- Its genuine inverse `sign(y) * y ^ 2`, written piecewise. -/
def signSqrtInv (y : ℝ) : ℝ :=
  if 0 ≤ y then y ^ 2 else -(y ^ 2)

/-- The corrected odd square root IS a chart: both round trips prove. -/
def signSqrtChart : Chart ℝ ℝ where
  toFun := signSqrt
  invFun := signSqrtInv
  left_inv := by
    intro x
    unfold signSqrt signSqrtInv
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, if_pos (Real.sqrt_nonneg x), Real.sq_sqrt hx]
    · have hxlt : x < 0 := not_le.mp hx
      have hs : 0 < Real.sqrt (-x) := Real.sqrt_pos.mpr (by linarith)
      rw [if_neg hx,
        if_neg (by linarith : ¬ (0 : ℝ) ≤ -Real.sqrt (-x)),
        neg_sq, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ -x), neg_neg]
  right_inv := by
    intro y
    unfold signSqrt signSqrtInv
    by_cases hy : 0 ≤ y
    · rw [if_pos hy, if_pos (sq_nonneg y), Real.sqrt_sq hy]
    · have hylt : y < 0 := not_le.mp hy
      have hy2 : 0 < y ^ 2 := by nlinarith
      rw [if_neg hy,
        if_neg (by linarith : ¬ (0 : ℝ) ≤ -(y ^ 2)),
        neg_neg, Real.sqrt_sq_eq_abs, abs_of_neg hylt, neg_neg]

end GCC
