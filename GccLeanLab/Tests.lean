/-
# Lean tests for the GCC Mathlib lab capstone

Concrete, kernel-checked instantiations of every section of
`GccLeanLab/Capstone.lean` (= `GCC_Mathlib_Lab_Capstone.lean` from the
2026-06-11 multi-model relay, with the predicted `MulCommMagma -> CommMagma`
fix applied).

Test philosophy, matching the relay's own doctrine:
* every abstract theorem gets at least one concrete instantiation
  (if the typeclass assumptions are wrong, these `example`s fail to elaborate);
* every computable claim gets a kernel-evaluated witness (`by decide`),
  so the numbers are checked, not asserted;
* safety theorems (positivity, boundedness) are exercised through their
  `.property` route to confirm illegal states really are unrepresentable.
-/

import GccLeanLab.Capstone
import GccLeanLab.MetaCalculus

namespace GCC.Tests

open GCC

/-! ## Test charts -/

/-- Shift-by-5 chart on the integers. Hand-rolled (not `Equiv.addRight`) so the
kernel can reduce it without instance gymnastics. -/
def shift5 : Chart ℤ ℤ where
  toFun x := x + 5
  invFun x := x - 5
  left_inv x := by change x + 5 - 5 = x; omega
  right_inv x := by change x - 5 + 5 = x; omega

/-- Identity chart on the integers. -/
def idZ : Chart ℤ ℤ := Equiv.refl ℤ

/-! ## 1. Transported arithmetic (capstone section 2)

The generated identities are chart-relative: under `shift5` the generated zero
is `-5` and the generated one is `-4` — the relay's "coordinate relativity of
identity elements" demo, now kernel-checked. -/

example : gzero shift5 = -5 := by decide
example : gone shift5 = -4 := by decide
example : gadd shift5 1 2 = 8 := by decide        -- x (+) y = x + y + 5
example : gneg shift5 0 = -10 := by decide
example : gsub shift5 8 1 = 2 := by decide
example : gmul shift5 1 2 = 37 := by decide       -- (1+5) * (2+5) - 5

-- transported laws, instantiated at the concrete chart
example : gadd shift5 3 4 = gadd shift5 4 3 := gadd_comm shift5 3 4
example : gadd shift5 (gzero shift5) 7 = 7 := gzero_add shift5 7
example : gadd shift5 7 (gneg shift5 7) = gzero shift5 := gadd_neg shift5 7
example : gmul shift5 (gone shift5) 9 = 9 := gone_mul shift5 9
example : gmul shift5 2 (gadd shift5 3 4) =
    gadd shift5 (gmul shift5 2 3) (gmul shift5 2 4) := gmul_gadd shift5 2 3 4

-- and the same law cross-checked numerically by the kernel
example : gadd shift5 7 (gneg shift5 7) = -5 := by decide

/-! ## 2. Discrete generated calculus (capstone section 3) -/

/-- Squares, as integers. -/
def sq : ℕ → ℤ := fun n => (n : ℤ) * (n : ℤ)

example : gdiff idZ sq 3 = 7 := by decide
example : gsum idZ (gdiff idZ sq) 5 = 25 := by decide

-- the discrete FTC at the identity chart, both as theorem and as kernel check
example : gsum idZ (gdiff idZ sq) 5 = gsub idZ (sq 5) (sq 0) := gFTC idZ sq 5

-- the same FTC at a nontrivial chart: holds for every f and n
example (f : ℕ → ℤ) (n : ℕ) :
    gsum shift5 (gdiff shift5 f) n = gsub shift5 (f n) (f 0) := gFTC shift5 f n

-- generated running sum of the constant-1 sequence under shift5:
-- -5, 1, 7, 13 (each step adds 1 + 5)
example : gsum shift5 (fun _ => (1 : ℤ)) 3 = 13 := by decide

/-! ### Straight lines: constant g-derivative iff arithmetic progression -/

/-- An affine sequence: 3n + 2. -/
def aff : ℕ → ℤ := fun n => 3 * (n : ℤ) + 2

theorem aff_const_gdiff : ∀ n, gdiff idZ aff n = idZ.symm 3 := by
  intro n
  simp [gdiff, gsub, idZ, aff]
  ring

example : ∀ n, idZ (aff n) = aprog (aff 0) 3 n :=
  (const_gdiff_iff idZ aff 3).mp aff_const_gdiff

example : aprog (2 : ℤ) 3 4 = 14 := by decide

/-! ## 3. Generated means and the tombstone (capstone section 4) -/

example : midpointMean.m 2 4 = 3 := by norm_num [midpointMean]

example (x : ℝ) : gmean (Equiv.refl ℝ) midpointMean x x = x :=
  gmean_idem (Equiv.refl ℝ) midpointMean x

example (x y : ℝ) : gmean (Equiv.refl ℝ) midpointMean x y =
    gmean (Equiv.refl ℝ) midpointMean y x :=
  gmean_comm (Equiv.refl ℝ) midpointMean x y

example : gmean (Equiv.refl ℝ) midpointMean 2 4 = 3 := by
  norm_num [gmean, midpointMean]

/-- The phi-demotion tombstone, concretely: rescaling coordinates (here by 2,
but `gmean_scale_recoord` holds for any nonzero `c`, e.g. `1 / Real.log phi`)
changes nothing about the generated midpoint mean. Log base is unobservable. -/
example (x y : ℝ) :
    gmean (recoord (Equiv.refl ℝ) (scaleMeanAuto 2 (by norm_num))) midpointMean x y
      = gmean (Equiv.refl ℝ) midpointMean x y :=
  gmean_scale_recoord (Equiv.refl ℝ) 2 (by norm_num) x y

-- ring-automorphism re-coordinatization certificates (capstone section 4b)
example (x y : ℤ) :
    gmul (recoordRing (Equiv.refl ℤ) (RingEquiv.refl ℤ)) x y
      = gmul (Equiv.refl ℤ) x y :=
  gmul_recoordRing (Equiv.refl ℤ) (RingEquiv.refl ℤ) x y

example (x y : ℤ) :
    gadd (recoordRing shift5 (RingEquiv.refl ℤ)) x y = gadd shift5 x y :=
  gadd_recoordRing shift5 (RingEquiv.refl ℤ) x y

/-! ## 4. Pareto frontier discipline (capstone section 5) -/

example : scalarize 1 1 bad_f₁ bad_f₂ Triad.middle = 120 := by decide
example : scalarize 1 1 bad_f₁ bad_f₂ Triad.left = 100 := by decide

-- the nonconvexity, witnessed: equal weights strictly prefer an endpoint
example : scalarize 1 1 bad_f₁ bad_f₂ Triad.left
    < scalarize 1 1 bad_f₁ bad_f₂ Triad.middle := by decide

-- neither endpoint dominates the middle (kernel re-check of middle_pareto's content)
example : ¬ Dominates bad_f₁ bad_f₂ Triad.left Triad.middle := by
  simp [Dominates, bad_f₁, bad_f₂]
example : ¬ Dominates bad_f₁ bad_f₂ Triad.right Triad.middle := by
  simp [Dominates, bad_f₁, bad_f₂]

example : ParetoOptimal bad_f₁ bad_f₂ Triad.middle := middle_pareto

example : ¬ (∀ y, scalarize 2 3 bad_f₁ bad_f₂ Triad.middle
    ≤ scalarize 2 3 bad_f₁ bad_f₂ y) :=
  middle_not_scalar_min (by decide) (by decide)

/-- Soundness, concretely: `left` minimizes the equal-weight scalarization,
so the theorem certifies it Pareto-optimal. -/
example : ParetoOptimal bad_f₁ bad_f₂ Triad.left :=
  scalarized_min_is_pareto (w₁ := 1) (w₂ := 1) (by decide) (by decide)
    (by intro y; cases y <;> decide)

/-! ## 5. The log chart: positive multiplicative systems (capstone sections 6-7) -/

example : logChart ⟨1, one_pos⟩ = 0 := by simp [logChart]
example : (logChart.symm 0).1 = 1 := by simp [logChart]

-- straightness in log coordinates, instantiated
example (x : PosReal) (r t : ℝ) :
    logChart (geometricLine x r t) = logChart x + t * r :=
  geometricLine_logCoord x r t

-- the fork-collapsing bridge, exercised at t = 0
example (x : PosReal) (r : ℝ) : (geometricLine x r 0).1 = x.1 := by
  rw [geometricLine_eq_expFlow]
  simp [expFlow]

-- constant log-rate on the canonical object, abstract and concrete
example (x : PosReal) (r t : ℝ) : logRate (geometricLine x r) t = r :=
  logRate_geometricLine x r t

example : logRate (geometricLine ⟨2, by norm_num⟩ 7) 1 = 7 :=
  logRate_geometricLine ⟨2, by norm_num⟩ 7 1

-- positivity safety: the multiplicative Euler step cannot leave PosReal
example (g : PosReal → ℝ) (h : ℝ) (x : PosReal) :
    0 < (multiplicativeEuler g h x).1 :=
  multiplicativeEuler_pos g h x

/-- Closed form of the multiplicative Euler step: it multiplies the state by
`exp (h * r)` — geometric stepping, as intended. -/
example (r h : ℝ) (x : PosReal) :
    (multiplicativeEuler (fun _ => r) h x).1 = x.1 * Real.exp (h * r) := by
  simp [multiplicativeEuler, chartEuler, logChart, smul_eq_mul, Real.exp_add,
    Real.exp_log x.property]

-- the multiplicative discrete FTC: gFTC instantiated at the log chart
example (f : ℕ → PosReal) (n : ℕ) :
    gsum logChart (gdiff logChart f) n = gsub logChart (f n) (f 0) :=
  gFTC logChart f n

-- classical recovery: at the identity chart, chartEuler is the textbook
-- Euler step and nativeLine is the ordinary straight line
example (V : ℝ → ℝ) (h x : ℝ) :
    chartEuler (Equiv.refl ℝ) V h x = x + h * V x := by
  simp [chartEuler, smul_eq_mul]

example (x v t : ℝ) : nativeLine (Equiv.refl ℝ) x v t = x + t * v := by
  simp [nativeLine, smul_eq_mul]

/-! ## 6. The logit chart: bounded logistic systems (capstone section 7) -/

example : sigmoid 0 = 1 / 2 := by
  unfold sigmoid
  rw [neg_zero, Real.exp_zero]
  norm_num

example (z : ℝ) : 0 < sigmoid z ∧ sigmoid z < 1 := sigmoid_mem_openUnit z

example : logit ⟨1 / 2, by norm_num⟩ = 0 := by
  unfold logit
  norm_num

-- the discharged round-trip obligations, exercised
example (z : ℝ) : logit (sigmoidToOpenUnit z) = z := logit_sigmoid z
example (x : OpenUnit) : sigmoid (logit x) = x.1 := sigmoid_logit x

-- the assembled chart is a genuine equivalence (the capstone's whole point)
example (z : ℝ) : logitChart (logitChart.symm z) = z :=
  logitChart.apply_symm_apply z
example (x : OpenUnit) : logitChart.symm (logitChart x) = x :=
  logitChart.symm_apply_apply x

-- straightness in logit coordinates: the bounded sibling of the geometric case
example (x : OpenUnit) (v t : ℝ) :
    logitChart (logisticLine x v t) = logitChart x + t * v :=
  logisticLine_logitCoord x v t

-- boundedness safety: logistic Euler steps cannot leave (0, 1)
example (g : OpenUnit → ℝ) (h : ℝ) (x : OpenUnit) :
    0 < (logisticEuler g h x).1 ∧ (logisticEuler g h x).1 < 1 :=
  logisticEuler_mem g h x

/-! ## 7. Meta-calculus operator layer (MetaCalculus.lean witnesses) -/

-- the k-guardrail spec, at concrete values
example : bgTransform 0.3 (0 : ℝ) = 0 := bgTransform_zero 0.3
example : bgTransform 0.3 (-4 : ℝ) < 0 := bgTransform_neg_of_neg 0.3 (by norm_num)
example : bgTransform 0.3 (1 : ℝ) = 1 := bgTransform_fixed 0.3 (by norm_num)
example : |bgTransform 0.16 (3 : ℝ)| < |(3 : ℝ)| :=
  bgTransform_contracts (by norm_num) (by norm_num) (by norm_num)
example : |(0.5 : ℝ)| < |bgTransform (-0.1) (0.5 : ℝ)| :=
  bgTransform_amplifies_of_k_le_zero (by norm_num) (by norm_num) (by norm_num)
example : |(3 : ℝ)| < |bgTransform 0.8 (3 : ℝ)| :=
  bgTransform_expands_of_half_lt_k (by norm_num) (by norm_num)

-- k(L) structural facts at the production constants: the affine form is
-- antitone, and over [1, 10^12] its range EXITS the safe window (the lower
-- end is negative) - which is why the Python optimizer path clamps k
example : kOf (-0.0137) 0.1593 1 = 0.1593 := by
  norm_num [kOf]
example (L : ℝ) (h1 : 1 ≤ L) (h2 : L ≤ (10 : ℝ) ^ (12 : ℝ)) :
    kOf (-0.0137) 0.1593 L ∈ Set.Icc (0.1593 + 12 * (-0.0137)) 0.1593 :=
  kOf_mem_Icc (by norm_num) h1 h2
example : (0.1593 : ℝ) + 12 * (-0.0137) < 0 := by norm_num

-- Grossman-Katz power-law constancy, concrete instance
example : bgDeriv (powFlow 3) ⟨2, by norm_num⟩ = 3 :=
  bgDeriv_powFlow 3 ⟨2, by norm_num⟩
example : bgDerivMul (powFlow 3) ⟨2, by norm_num⟩ = Real.exp 3 :=
  bgDerivMul_powFlow 3 ⟨2, by norm_num⟩

-- F007 subsumes the classical derivative (abstract instantiation)
example (f : ℝ → ℝ) (a : ℝ) :
    f007Deriv (fun _ => 1) (fun _ => 1) id id f a = deriv f a :=
  f007_classical f a
example (f : ℝ → ℝ) (a : ℝ) :
    f007Deriv (fun _ => 1) (fun _ => 1) Real.log Real.log f a
      = a * deriv f a / f a :=
  f007_bigeometric f a

-- the audit tombstone: the corrected odd square root is a genuine chart;
-- both round trips hold by construction (the Python original failed them)
example (x : ℝ) : signSqrtChart.symm (signSqrtChart x) = x :=
  signSqrtChart.symm_apply_apply x
example (y : ℝ) : signSqrtChart (signSqrtChart.symm y) = y :=
  signSqrtChart.apply_symm_apply y

end GCC.Tests
