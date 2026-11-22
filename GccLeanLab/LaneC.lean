/-
# Lane C3: registry entries proved or refuted

Lean counterparts of five entries in meta-calculus-portfolio
docs/FORMULA_CLAIMS.json (and the Kramers-Wannier entry of
docs/HONEST-STATUS.md section 8):

* F008: the proposed spectral-gap bound `gap(P_mix) >= min(gap_i)` is FALSE.
  Stated for two symmetric 2x2 factors with a symmetric product (inside the
  guarded normal scope) and refuted by one explicit diagonal pair.
* META_FTC_I and META_FTC_II: Grossman's fundamental theorems of
  meta-calculus over `intervalIntegral`, with the meta-integral `int u f` and
  the meta-change `int v f'` (registry META_CHANGE_ARGUMENT).
* LANE_EMDEN_N5_REGULAR: `theta(xi) = 1/sqrt(1 + xi^2/3)` solves the n = 5
  Lane-Emden equation for xi /= 0 with theta(0) = 1, theta'(0) = 0.
* F005: the reciprocal generator `1/x` as a chart on the nonzero reals (an
  involution), its derivative `-(1/x)^2`, and its log-chart reading.
* Kramers-Wannier: `sinh(2K) sinh(2K*) = 1` defines K* for K > 0; the map is
  an involution and its unique fixed point is `K = log(1 + sqrt 2)/2`.

Scope differences from the registry wording are stated in each docstring and
in docs/THEOREM_MAP.md.
-/

import GccLeanLab.MetaCalculus

noncomputable section

open MeasureTheory Set

namespace GCC

/-! ## 1. F008: the composed spectral-gap bound is refuted

`spectral_gap` in simulations/spectral_gap_verification.py sorts the absolute
eigenvalues of a self-adjoint matrix ascending and returns second minus
first. For a symmetric 2x2 matrix the eigenvalues have the closed form
`(a + d +- sqrt((a - d)^2 + 4 b^2)) / 2`; `det_sub_eigHi` and
`det_sub_eigLo` check that both are roots of the characteristic polynomial,
so `gap2` is that function on 2x2 inputs. -/

/-- Symmetric 2x2 real matrix. -/
def Sym2 (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop := A 0 1 = A 1 0

/-- Discriminant root of a symmetric 2x2 matrix. -/
def eigDisc (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  Real.sqrt ((A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 ^ 2)

/-- Larger eigenvalue (closed form). -/
def eigHi (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (A 0 0 + A 1 1 + eigDisc A) / 2

/-- Smaller eigenvalue (closed form). -/
def eigLo (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := (A 0 0 + A 1 1 - eigDisc A) / 2

theorem eigDisc_sq (A : Matrix (Fin 2) (Fin 2) ℝ) :
    eigDisc A ^ 2 = (A 0 0 - A 1 1) ^ 2 + 4 * A 0 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem det_sub_eigHi (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : Sym2 A) :
    (A - eigHi A • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 := by
  rw [Matrix.det_fin_two]
  have hA' : A 0 1 = A 1 0 := hA
  simp [eigHi]
  linear_combination (1 / 4 : ℝ) * eigDisc_sq A + A 0 1 * hA'

theorem det_sub_eigLo (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : Sym2 A) :
    (A - eigLo A • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 := by
  rw [Matrix.det_fin_two]
  have hA' : A 0 1 = A 1 0 := hA
  simp [eigLo]
  linear_combination (1 / 4 : ℝ) * eigDisc_sq A + A 0 1 * hA'

/-- `spectral_gap` on a symmetric 2x2 matrix: the spacing of the absolute
eigenvalues. -/
def gap2 (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := |(|eigHi A| - |eigLo A|)|

/-- The registry's proposed F008 bound, two-factor instance, restricted to the
guarded normal scope: both factors and the product are symmetric. -/
def F008Claim : Prop :=
  ∀ P₁ P₂ : Matrix (Fin 2) (Fin 2) ℝ, Sym2 P₁ → Sym2 P₂ → Sym2 (P₂ * P₁) →
    min (gap2 P₁) (gap2 P₂) ≤ gap2 (P₂ * P₁)

/-- The historical F008 claim: the mixed gap exceeds the largest component. -/
def F008HistoricalClaim : Prop :=
  ∀ P₁ P₂ : Matrix (Fin 2) (Fin 2) ℝ, Sym2 P₁ → Sym2 P₂ → Sym2 (P₂ * P₁) →
    max (gap2 P₁) (gap2 P₂) < gap2 (P₂ * P₁)

def f008P1 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]
def f008P2 : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 1]

theorem f008_mix : f008P2 * f008P1 = !![2, 0; 0, 2] := by
  simp [f008P1, f008P2]

theorem gap2_f008P1 : gap2 f008P1 = 1 := by
  simp [gap2, eigHi, eigLo, eigDisc, f008P1]
  norm_num

theorem gap2_f008P2 : gap2 f008P2 = 1 := by
  simp [gap2, eigHi, eigLo, eigDisc, f008P2]
  norm_num

theorem gap2_f008_mix : gap2 (f008P2 * f008P1) = 0 := by
  rw [f008_mix]
  simp [gap2, eigHi, eigLo, eigDisc]

theorem f008_sym : Sym2 f008P1 ∧ Sym2 f008P2 ∧ Sym2 (f008P2 * f008P1) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Sym2, f008P1]
  · simp [Sym2, f008P2]
  · rw [f008_mix]; simp [Sym2]

/-- F008 is false: component gaps 1 and 1, composed gap 0. -/
theorem f008_refuted : ¬ F008Claim := by
  intro h
  have := h f008P1 f008P2 f008_sym.1 f008_sym.2.1 f008_sym.2.2
  rw [gap2_f008P1, gap2_f008P2, gap2_f008_mix] at this
  norm_num at this

/-- The historical claim falls with it. -/
theorem f008_historical_refuted : ¬ F008HistoricalClaim := by
  intro h
  have := h f008P1 f008P2 f008_sym.1 f008_sym.2.1 f008_sym.2.2
  rw [gap2_f008P1, gap2_f008P2, gap2_f008_mix] at this
  norm_num at this

/-! ## 2. META_FTC_I and META_FTC_II (Grossman 1981, section 2.13)

The meta-integral is the limit of sums `f(a_i) * meta_measure_u`, i.e.
`int_r^s u f`; the meta-change is `int_r^s v f'` (META_CHANGE_ARGUMENT). -/

/-- Grossman's meta-integral of f over [r, s] with input weight u. -/
def metaIntegral (u f : ℝ → ℝ) (r s : ℝ) : ℝ := ∫ x in r..s, u x * f x

/-- Grossman's meta-change of f over [r, s] with output weight v. -/
def metaChange (v f : ℝ → ℝ) (r s : ℝ) : ℝ := ∫ x in r..s, v x * deriv f x

/-- META_FTC_I: meta-differentiating the meta-integral returns `v * f`, not f,
at every interior point. Hypotheses: u continuous and positive (the weight
domain; v needs nothing), f continuous on [r, s]. -/
theorem meta_ftc_I {u v f : ℝ → ℝ} {r s x : ℝ} (hu : Continuous u)
    (hupos : ∀ y, 0 < u y) (hf : ContinuousOn f (Icc r s)) (hx : x ∈ Ioo r s) :
    metaDeriv u v (fun t => metaIntegral u f r t) x = v x * f x := by
  have hc : ContinuousOn (fun t => u t * f t) (Icc r s) := hu.continuousOn.mul hf
  have hint : IntervalIntegrable (fun t => u t * f t) volume r x := by
    apply ContinuousOn.intervalIntegrable
    apply hc.mono
    rw [uIcc_of_le hx.1.le]
    exact Icc_subset_Icc_right hx.2.le
  have hcat : ContinuousAt (fun t => u t * f t) x :=
    hc.continuousAt (Icc_mem_nhds hx.1 hx.2)
  have hmeas : StronglyMeasurableAtFilter (fun t => u t * f t) (nhds x) volume :=
    (hc.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo x hx
  have hd := intervalIntegral.integral_hasDerivAt_right hint hmeas hcat
  have hu0 : u x ≠ 0 := (hupos x).ne'
  unfold metaDeriv metaIntegral
  rw [hd.deriv]
  field_simp

/-- META_FTC_II: the meta-integral of the meta-derivative is the meta-change.
With the registry's integral form of the meta-change this is a pointwise
identity; it needs only u /= 0 (no smoothness: both sides use the same
`deriv h`). See `metaChange_one` for the analytic content. -/
theorem meta_ftc_II {u v h : ℝ → ℝ} (r s : ℝ) (hupos : ∀ y, 0 < u y) :
    metaIntegral u (metaDeriv u v h) r s = metaChange v h r s := by
  unfold metaIntegral metaChange metaDeriv
  congr 1
  funext x
  have hu0 : u x ≠ 0 := (hupos x).ne'
  field_simp

/-- With unit output weight the meta-change is the ordinary change `h s - h r`
(classical FTC), for h differentiable on [r, s] with integrable derivative. -/
theorem metaChange_one {h : ℝ → ℝ} {r s : ℝ}
    (hd : ∀ x ∈ uIcc r s, DifferentiableAt ℝ h x)
    (hint : IntervalIntegrable (deriv h) volume r s) :
    metaChange (fun _ => 1) h r s = h s - h r := by
  unfold metaChange
  simp only [one_mul]
  exact intervalIntegral.integral_deriv_eq_sub hd hint

/-! ## 3. LANE_EMDEN_N5_REGULAR

`theta'' + 2 theta' / xi + theta^5 = 0` with `theta(xi) = (1 + xi^2/3)^(-1/2)`.
Key step: `theta' = -(xi/3) theta^3`, and `theta^2 (1 + xi^2/3) = 1`. -/

/-- The regular n = 5 solution `1/sqrt(1 + xi^2/3)`, written with `⁻¹`. -/
def laneEmdenN5 (ξ : ℝ) : ℝ := (Real.sqrt (1 + ξ ^ 2 / 3))⁻¹

theorem laneEmdenN5_pos (ξ : ℝ) : 0 < laneEmdenN5 ξ :=
  inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem laneEmdenN5_hasDerivAt (ξ : ℝ) :
    HasDerivAt laneEmdenN5 (-(ξ / 3) * laneEmdenN5 ξ ^ 3) ξ := by
  have hw : (0 : ℝ) < 1 + ξ ^ 2 / 3 := by positivity
  have hs : 0 < Real.sqrt (1 + ξ ^ 2 / 3) := Real.sqrt_pos.mpr hw
  have hinner : HasDerivAt (fun t : ℝ => 1 + t ^ 2 / 3) (2 * ξ / 3) ξ := by
    have := ((hasDerivAt_pow 2 ξ).div_const 3).const_add 1
    convert this using 1
    norm_num
  have hinv := (hinner.sqrt hw.ne').inv hs.ne'
  convert hinv using 1
  simp only [laneEmdenN5]
  field_simp

theorem laneEmdenN5_deriv_apply (ξ : ℝ) :
    deriv laneEmdenN5 ξ = -(ξ / 3) * laneEmdenN5 ξ ^ 3 :=
  (laneEmdenN5_hasDerivAt ξ).deriv

theorem laneEmdenN5_deriv :
    deriv laneEmdenN5 = fun ξ => -(ξ / 3) * laneEmdenN5 ξ ^ 3 :=
  funext laneEmdenN5_deriv_apply

/-- The constraint behind the n = 5 identity: `theta^2 (1 + xi^2/3) = 1`. -/
theorem laneEmdenN5_sq_mul (ξ : ℝ) : laneEmdenN5 ξ ^ 2 * (1 + ξ ^ 2 / 3) = 1 := by
  have hw : (0 : ℝ) < 1 + ξ ^ 2 / 3 := by positivity
  simp only [laneEmdenN5, inv_pow, Real.sq_sqrt hw.le]
  exact inv_mul_cancel₀ hw.ne'

/-- LANE_EMDEN_N5_REGULAR, the ODE: for every xi /= 0,
`theta'' + 2 theta'/xi + theta^5 = 0`. -/
theorem laneEmdenN5_ode {ξ : ℝ} (hξ : ξ ≠ 0) :
    deriv (deriv laneEmdenN5) ξ + 2 * deriv laneEmdenN5 ξ / ξ
      + laneEmdenN5 ξ ^ 5 = 0 := by
  have hd2 : HasDerivAt (deriv laneEmdenN5)
      (-(1 / 3) * laneEmdenN5 ξ ^ 3
        + -(ξ / 3) * (3 * laneEmdenN5 ξ ^ 2 * (-(ξ / 3) * laneEmdenN5 ξ ^ 3))) ξ := by
    rw [laneEmdenN5_deriv]
    have h1 : HasDerivAt (fun t : ℝ => -(t / 3)) (-(1 / 3)) ξ := by
      simpa using ((hasDerivAt_id ξ).div_const 3).neg
    convert h1.mul ((laneEmdenN5_hasDerivAt ξ).pow 3) using 1
  rw [hd2.deriv, laneEmdenN5_deriv_apply]
  have hdiv : 2 * (-(ξ / 3) * laneEmdenN5 ξ ^ 3) / ξ = -(2 / 3) * laneEmdenN5 ξ ^ 3 := by
    field_simp
  rw [hdiv]
  linear_combination laneEmdenN5 ξ ^ 3 * laneEmdenN5_sq_mul ξ

/-- Regular initial conditions: theta(0) = 1 and theta'(0) = 0. -/
theorem laneEmdenN5_initial : laneEmdenN5 0 = 1 ∧ deriv laneEmdenN5 0 = 0 := by
  refine ⟨by simp [laneEmdenN5], ?_⟩
  rw [laneEmdenN5_deriv_apply]
  simp

/-! ## 4. F005: the reciprocal generator alpha(x) = 1/x

The Python `Reciprocal` returns NaN at 0, derivative `-(1/x)^2`, and is its
own inverse. In Lean `0⁻¹ = 0`, so the honest object is the chart on the
nonzero reals. -/

/-- Nonzero reals. -/
abbrev NonzeroReal : Type := {x : ℝ // x ≠ 0}

/-- F005: `x ↦ 1/x` as a chart on the nonzero reals; it is its own inverse. -/
def recipChart : Chart NonzeroReal NonzeroReal where
  toFun x := ⟨x.1⁻¹, inv_ne_zero x.2⟩
  invFun x := ⟨x.1⁻¹, inv_ne_zero x.2⟩
  left_inv x := Subtype.ext (inv_inv x.1)
  right_inv x := Subtype.ext (inv_inv x.1)

theorem recipChart_apply (x : NonzeroReal) : (recipChart x).1 = 1 / x.1 := by
  simp [recipChart]

theorem recipChart_symm : recipChart.symm = recipChart := rfl

theorem recipChart_involutive (x : NonzeroReal) : recipChart (recipChart x) = x :=
  recipChart.symm_apply_apply x

/-- Injective on the generator's domain (the nonzero reals). -/
theorem recip_injOn : InjOn (fun x : ℝ => 1 / x) {x | x ≠ 0} := by
  intro a _ b _ h
  simpa using h

/-- The Python `Reciprocal.derivative`: `-(1/x) * (1/x)` for x /= 0. -/
theorem recip_hasDerivAt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 / t) (-(1 / x) * (1 / x)) x := by
  have h := hasDerivAt_inv hx
  simp only [one_div]
  convert h using 1
  field_simp

/-- On positive reals the reciprocal is negation in the log chart. -/
theorem logChart_recip (x : PosReal) :
    logChart ⟨x.1⁻¹, inv_pos.mpr x.2⟩ = -logChart x := by
  change Real.log x.1⁻¹ = -Real.log x.1
  exact Real.log_inv x.1

/-! ## 5. Kramers-Wannier dual coupling

`sinh(2K) sinh(2K*) = 1`. K* is the unique positive solution, the map is an
involution, and its only fixed point is `K_c = log(1 + sqrt 2)/2`. The
Onsager free-energy duality itself stays a numerical check (HONEST-STATUS
section 8). -/

/-- The dual coupling `K* = arsinh(1/sinh(2K))/2`. -/
def kwDual (K : ℝ) : ℝ := Real.arsinh (1 / Real.sinh (2 * K)) / 2

theorem kwDual_spec {K : ℝ} (hK : 0 < K) :
    Real.sinh (2 * K) * Real.sinh (2 * kwDual K) = 1 := by
  have hs : 0 < Real.sinh (2 * K) := Real.sinh_pos_iff.mpr (by linarith)
  have h2 : 2 * kwDual K = Real.arsinh (1 / Real.sinh (2 * K)) := by
    unfold kwDual; ring
  rw [h2, Real.sinh_arsinh]
  field_simp

theorem kwDual_pos {K : ℝ} (hK : 0 < K) : 0 < kwDual K := by
  have hs : 0 < Real.sinh (2 * K) := Real.sinh_pos_iff.mpr (by linarith)
  unfold kwDual
  have : 0 < Real.arsinh (1 / Real.sinh (2 * K)) :=
    Real.arsinh_pos_iff.mpr (by positivity)
  linarith

/-- K* is the only coupling satisfying the duality relation. -/
theorem kwDual_unique {K L : ℝ} (hK : 0 < K)
    (h : Real.sinh (2 * K) * Real.sinh (2 * L) = 1) : L = kwDual K := by
  have hs : Real.sinh (2 * K) ≠ 0 := (Real.sinh_pos_iff.mpr (by linarith)).ne'
  have hspec := kwDual_spec hK
  have heq : Real.sinh (2 * L) = Real.sinh (2 * kwDual K) := by
    apply mul_left_cancel₀ hs
    rw [h, hspec]
  have := Real.sinh_injective heq
  linarith

/-- The dual map is an involution on K > 0. -/
theorem kwDual_kwDual {K : ℝ} (hK : 0 < K) : kwDual (kwDual K) = K :=
  (kwDual_unique (kwDual_pos hK) (by rw [mul_comm]; exact kwDual_spec hK)).symm

/-- Self-duality is exactly `sinh(2K) = 1`. -/
theorem kwDual_eq_self_iff {K : ℝ} (hK : 0 < K) :
    kwDual K = K ↔ Real.sinh (2 * K) = 1 := by
  have hs : 0 < Real.sinh (2 * K) := Real.sinh_pos_iff.mpr (by linarith)
  constructor
  · intro hd
    have h := kwDual_spec hK
    rw [hd] at h
    nlinarith
  · intro h1
    exact (kwDual_unique hK (by rw [h1]; norm_num)).symm

/-- The self-dual (critical) coupling `log(1 + sqrt 2)/2`. -/
def kwCritical : ℝ := Real.log (1 + Real.sqrt 2) / 2

theorem kwCritical_pos : 0 < kwCritical := by
  unfold kwCritical
  have : 0 < Real.log (1 + Real.sqrt 2) :=
    Real.log_pos (by have := Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num); linarith)
  linarith

theorem sinh_two_kwCritical : Real.sinh (2 * kwCritical) = 1 := by
  have h : 2 * kwCritical = Real.arsinh 1 := by
    unfold kwCritical
    rw [Real.arsinh]
    norm_num
    ring
  rw [h, Real.sinh_arsinh]

theorem kwDual_kwCritical : kwDual kwCritical = kwCritical :=
  (kwDual_eq_self_iff kwCritical_pos).mpr sinh_two_kwCritical

/-- K_c is the only positive self-dual coupling. -/
theorem kwDual_eq_self_iff_critical {K : ℝ} (hK : 0 < K) :
    kwDual K = K ↔ K = kwCritical := by
  rw [kwDual_eq_self_iff hK]
  constructor
  · intro h
    have := Real.sinh_injective (h.trans sinh_two_kwCritical.symm)
    linarith
  · rintro rfl
    exact sinh_two_kwCritical

end GCC
