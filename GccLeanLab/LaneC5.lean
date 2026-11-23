/-
# Lane C5: the eight owner-resolved registry entries (2026-11-22)

Lean counterparts of the eight entries of meta-calculus-portfolio
docs/FORMULA_CLAIMS.json that the owner resolution of the Lane C triage
(metacalculus-audit-runs/20261121-proof-techniques/laneC/TRIAGE.md,
section "Resolution") moved to PROVABLE_NOW under the rule "classify by the
narrowest precise statement the entry makes". Only those narrow statements
are proved here; the broader claim of each entry is recorded as not covered
in the docstrings and in docs/THEOREM_MAP.md section 7. ASCII only
(repository rule).
-/

import GccLeanLab.LaneC4

noncomputable section

open MeasureTheory Set Filter Topology

namespace GCC

/-! ## 1. BEKENSTEIN_HAWKING_ENTROPY: the area algebra

Registry: `S_BH = k_B c^3 A / (4 G hbar) = k_B c^3 pi r_s^2 / (G hbar)`.
Narrow statement: with `A = 4 pi r_s^2` the two forms agree, and in Planck
units the entropy is `A / 4`. The entropy-area law itself is not formalized. -/

/-- Horizon area `A = 4 pi r_s^2`. -/
def horizonArea (G M c : Real) : Real := 4 * Real.pi * schwarzschildRadius G M c ^ 2

/-- Area form `S = k_B c^3 A / (4 G hbar)`. -/
def bhEntropyArea (kB c G hbar A : Real) : Real := kB * c ^ 3 * A / (4 * G * hbar)

/-- Planck area `l_P^2 = G hbar / c^3`. -/
def planckArea (G hbar c : Real) : Real := G * hbar / c ^ 3

/-- The area form at `A = 4 pi r_s^2` is the r_s form `bhEntropy` of LaneC4. -/
theorem bhEntropyArea_horizon (kB c G hbar M : Real) :
    bhEntropyArea kB c G hbar (horizonArea G M c) = bhEntropy kB c G hbar M := by
  unfold bhEntropyArea horizonArea bhEntropy
  ring

/-- `S = k_B A / (4 l_P^2)`. -/
theorem bhEntropyArea_planck (kB c G hbar A : Real) :
    bhEntropyArea kB c G hbar A = kB * (A / (4 * planckArea G hbar c)) := by
  unfold bhEntropyArea planckArea
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- In units `k_B = c = G = hbar = 1`, `S = A / 4`. -/
theorem bhEntropyArea_natural (A : Real) : bhEntropyArea 1 1 1 1 A = A / 4 := by
  unfold bhEntropyArea
  ring

/-! ## 2. F006: the scale-dependent chart (monotone, C1, odd)

meta_calculus/core/generators.py `ScaleDependent`, scale l > 0:
`alpha(x; l) = x exp(-x^2/l^2) + sign(x) l exp(|x|/l) (1 - exp(-x^2/l^2))`.
Narrow statement: this is an odd, continuously differentiable, strictly
increasing bijection of R (a chart). Its physical reading as a
quantum-classical interpolation is not formalized. -/

/-- The registry formula, with Mathlib's `Real.sign` (`sign 0 = 0`). -/
def f006 (l x : Real) : Real :=
  x * Real.exp (-x ^ 2 / l ^ 2)
    + Real.sign x * l * Real.exp (|x| / l) * (1 - Real.exp (-x ^ 2 / l ^ 2))

/-- The branch for x >= 0 (smooth on all of R). -/
def f006Pos (l x : Real) : Real :=
  x * Real.exp (-x ^ 2 / l ^ 2) + l * Real.exp (x / l) * (1 - Real.exp (-x ^ 2 / l ^ 2))

/-- Slope of the positive branch; generators.py `derivative` at x >= 0. -/
def f006Slope (l x : Real) : Real :=
  Real.exp (-x ^ 2 / l ^ 2) * (1 - 2 * (x / l) ^ 2)
    + Real.exp (x / l) * (1 - Real.exp (-x ^ 2 / l ^ 2))
    + 2 * (x / l) * Real.exp (x / l) * Real.exp (-x ^ 2 / l ^ 2)

theorem f006Pos_hasDerivAt {l : Real} (hl : Ne l 0) (x : Real) :
    HasDerivAt (f006Pos l) (f006Slope l x) x := by
  have h1 : HasDerivAt (fun x : Real => -x ^ 2 / l ^ 2) (-(2 * x) / l ^ 2) x := by
    have := ((hasDerivAt_pow 2 x).neg).div_const (l ^ 2)
    convert this using 1
    push_cast
    ring
  have hg := h1.exp
  have he : HasDerivAt (fun x => Real.exp (x / l)) (Real.exp (x / l) * (1 / l)) x :=
    ((hasDerivAt_id' x).div_const l).exp
  have h := ((hasDerivAt_id' x).mul hg).add
    ((he.const_mul l).mul ((hasDerivAt_const x (1 : Real)).sub hg))
  convert h using 1
  unfold f006Slope
  simp only [Pi.sub_apply]
  generalize Real.exp (-x ^ 2 / l ^ 2) = g
  generalize Real.exp (x / l) = E
  field_simp
  ring

theorem f006_of_nonneg (l : Real) {x : Real} (hx : 0 <= x) : f006 l x = f006Pos l x := by
  rcases hx.lt_or_eq with h | h
  next =>
    unfold f006 f006Pos
    rw [Real.sign_of_pos h, abs_of_pos h]
    ring
  next =>
    subst h
    simp [f006, f006Pos]

theorem f006_of_nonpos (l : Real) {x : Real} (hx : x <= 0) :
    f006 l x = -f006Pos l (-x) := by
  rcases hx.lt_or_eq with h | h
  next =>
    unfold f006 f006Pos
    rw [Real.sign_of_neg h, abs_of_neg h, neg_sq]
    ring
  next =>
    subst h
    simp [f006, f006Pos]

/-- Oddness. -/
theorem f006_neg (l x : Real) : f006 l (-x) = -f006 l x := by
  unfold f006
  rw [Real.sign_neg, abs_neg, neg_sq]
  ring

theorem f006_zero (l : Real) : f006 l 0 = 0 := by simp [f006]

/-- The slope is positive for x >= 0 (generators.py's argument, with
`exp(t) >= 1 + t`). -/
theorem f006Slope_pos {l x : Real} (hl : 0 < l) (hx : 0 <= x) : 0 < f006Slope l x := by
  have ht : 0 <= x / l := div_nonneg hx hl.le
  have hg : 0 < Real.exp (-x ^ 2 / l ^ 2) := Real.exp_pos _
  have hg1 : Real.exp (-x ^ 2 / l ^ 2) <= 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 <= x ^ 2 / l ^ 2 := by positivity
    linarith [neg_div (l ^ 2) (x ^ 2)]
  have hE : x / l + 1 <= Real.exp (x / l) := Real.add_one_le_exp _
  have hE0 : 0 < Real.exp (x / l) := Real.exp_pos _
  have h1 : 0 <= 2 * (x / l) * Real.exp (-x ^ 2 / l ^ 2) * (Real.exp (x / l) - (x / l + 1)) :=
    mul_nonneg (mul_nonneg (by linarith) hg.le) (by linarith)
  have h2 : 0 <= Real.exp (x / l) * (1 - Real.exp (-x ^ 2 / l ^ 2)) :=
    mul_nonneg hE0.le (by linarith)
  have h3 : 0 <= 2 * (x / l) * Real.exp (-x ^ 2 / l ^ 2) := mul_nonneg (by linarith) hg.le
  unfold f006Slope
  nlinarith

theorem f006Slope_continuous (l : Real) : Continuous (f006Slope l) := by
  unfold f006Slope
  fun_prop

/-- The negative branch `x -> -p(-x)` has slope `p'(-x)`. -/
theorem f006Neg_hasDerivAt {l : Real} (hl : Ne l 0) (x : Real) :
    HasDerivAt (fun y => -f006Pos l (-y)) (f006Slope l (-x)) x := by
  have h := ((f006Pos_hasDerivAt hl (-x)).comp x (hasDerivAt_neg x)).neg
  convert h using 1
  ring

/-- `alpha'(x) = p'(|x|)` at every x, including the junction x = 0. -/
theorem f006_hasDerivAt {l : Real} (hl : Ne l 0) (x : Real) :
    HasDerivAt (f006 l) (f006Slope l |x|) x := by
  rcases lt_trichotomy x 0 with h | h | h
  next =>
    rw [abs_of_neg h]
    refine (f006Neg_hasDerivAt hl x).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Iio_mem_nhds h) (fun y hy => f006_of_nonpos l (le_of_lt hy))
  next =>
    subst h
    rw [abs_zero]
    have hR : HasDerivWithinAt (f006 l) (f006Slope l 0) (Ici 0) 0 :=
      (f006Pos_hasDerivAt hl 0).hasDerivWithinAt.congr_of_mem
        (fun y hy => f006_of_nonneg l hy) self_mem_Ici
    have hL : HasDerivWithinAt (f006 l) (f006Slope l 0) (Iic 0) 0 := by
      have h0 := (f006Neg_hasDerivAt hl 0).hasDerivWithinAt (s := Iic 0)
      rw [neg_zero] at h0
      exact h0.congr_of_mem (fun y hy => f006_of_nonpos l hy) self_mem_Iic
    have hU := hL.union hR
    rw [Iic_union_Ici] at hU
    exact hasDerivWithinAt_univ.mp hU
  next =>
    rw [abs_of_pos h]
    refine (f006Pos_hasDerivAt hl x).congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Ioi_mem_nhds h) (fun y hy => f006_of_nonneg l (le_of_lt hy))

theorem f006_deriv {l : Real} (hl : Ne l 0) : deriv (f006 l) = fun x => f006Slope l |x| :=
  funext (fun x => (f006_hasDerivAt hl x).deriv)

/-- alpha(.; l) is C1 (its slope `p'(|x|)` is continuous). -/
theorem f006_contDiff_one {l : Real} (hl : Ne l 0) : ContDiff Real 1 (f006 l) := by
  rw [contDiff_one_iff_deriv, f006_deriv hl]
  exact And.intro (fun x => (f006_hasDerivAt hl x).differentiableAt)
    ((f006Slope_continuous l).comp continuous_abs)

theorem f006_strictMono {l : Real} (hl : 0 < l) : StrictMono (f006 l) :=
  strictMono_of_hasDerivAt_pos (fun x => f006_hasDerivAt hl.ne' x)
    (fun x => f006Slope_pos hl (abs_nonneg x))

/-- `alpha(x) >= x` for x >= 0 (the bracket used by generators.py `inverse`). -/
theorem f006_ge_self {l x : Real} (hl : 0 < l) (hx : 0 <= x) : x <= f006 l x := by
  rw [f006_of_nonneg l hx]
  have hg1 : Real.exp (-x ^ 2 / l ^ 2) <= 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 <= x ^ 2 / l ^ 2 := by positivity
    linarith [neg_div (l ^ 2) (x ^ 2)]
  have hE : x / l + 1 <= Real.exp (x / l) := Real.add_one_le_exp _
  have hlE : x + l <= l * Real.exp (x / l) := by
    have h := mul_le_mul_of_nonneg_left hE hl.le
    have hid : l * (x / l + 1) = x + l := by field_simp
    rwa [hid] at h
  have h1 : 0 <= (l * Real.exp (x / l) - (x + l)) * (1 - Real.exp (-x ^ 2 / l ^ 2)) :=
    mul_nonneg (by linarith) (by linarith)
  unfold f006Pos
  nlinarith

theorem f006_surjective {l : Real} (hl : 0 < l) : Function.Surjective (f006 l) := by
  have hc : Continuous (f006 l) := (f006_contDiff_one hl.ne').continuous
  refine hc.surjective ?_ ?_
  next =>
    exact Filter.tendsto_atTop_mono' atTop
      ((eventually_ge_atTop 0).mono (fun x hx => f006_ge_self hl hx)) tendsto_id
  next =>
    refine Filter.tendsto_atBot_mono' atBot
      ((eventually_le_atBot 0).mono (fun x hx => ?_)) tendsto_id
    have h := f006_ge_self hl (neg_nonneg.mpr hx)
    rw [f006_neg] at h
    show f006 l x <= x
    linarith

/-- F006 as a chart R ~ R. -/
def f006Chart (l : Real) (hl : 0 < l) : Chart Real Real :=
  Equiv.ofBijective (f006 l) (And.intro (f006_strictMono hl).injective (f006_surjective hl))

theorem f006Chart_apply (l : Real) (hl : 0 < l) (x : Real) : f006Chart l hl x = f006 l x := rfl

/-! ## 3. NR_1PLUSLOG_SLICING: the scalar gauge and its log-volume relation

Registry: `(d_t - L_beta) alpha = -2 K alpha`. Narrow statement: along one
flow line of `d_t - L_beta`, parametrized by t, the lapse obeys
`alpha' = -2 K alpha`; with the ADM volume evolution
`(log sqrt gamma)' = -alpha K` taken as a hypothesis, `alpha - log gamma`
is constant, so `alpha = 1 + log gamma` for `alpha = gamma = 1` at t = 0
(the name "1+log"). The Lie derivative, the 3+1 split and the derivation of
the volume equation are not formalized. -/

/-- Right-hand side of the 1+log condition. -/
def onePlusLogRHS (alpha K : Real) : Real := -2 * K * alpha

theorem onePlusLog_invariant {alpha K gam : Real -> Real}
    (hgam : forall t, 0 < gam t)
    (halpha : forall t, HasDerivAt alpha (onePlusLogRHS (alpha t) (K t)) t)
    (hvol : forall t, HasDerivAt (fun s => Real.log (Real.sqrt (gam s))) (-(alpha t * K t)) t)
    (t : Real) :
    alpha t - Real.log (gam t) = alpha 0 - Real.log (gam 0) := by
  have hlog : forall t, HasDerivAt (fun s => Real.log (gam s)) (-2 * K t * alpha t) t := by
    intro t
    have h := (hvol t).const_mul 2
    have hfun : (fun s => 2 * Real.log (Real.sqrt (gam s))) = fun s => Real.log (gam s) := by
      funext s
      rw [Real.log_sqrt (hgam s).le]
      ring
    rw [hfun] at h
    convert h using 1
    ring
  have hd : forall t, HasDerivAt (fun s => alpha s - Real.log (gam s)) 0 t := by
    intro t
    have h := (halpha t).sub (hlog t)
    unfold onePlusLogRHS at h
    convert h using 1
    ring
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0

/-- 1+log: `alpha = 1 + log gamma` from `alpha(0) = gamma(0) = 1`. -/
theorem onePlusLog_alpha {alpha K gam : Real -> Real}
    (hgam : forall t, 0 < gam t)
    (halpha : forall t, HasDerivAt alpha (onePlusLogRHS (alpha t) (K t)) t)
    (hvol : forall t, HasDerivAt (fun s => Real.log (Real.sqrt (gam s))) (-(alpha t * K t)) t)
    (ha0 : alpha 0 = 1) (hg0 : gam 0 = 1) (t : Real) :
    alpha t = 1 + Real.log (gam t) := by
  have h := onePlusLog_invariant hgam halpha hvol t
  rw [ha0, hg0, Real.log_one] at h
  linarith

/-! ## 4. COSMOLOGY_FLAT_FRW: algebra given the Friedmann equations

Registry: `H^2 = 8 pi G rho/(3 c^2)`, `Lambda = 8 pi G rho_vac / c^4`,
`q = (rho_m/2 + rho_r - rho_vac)/(rho_m + rho_r + rho_vac)` for flat FRW with
matter (w = 0), radiation (w = 1/3) and vacuum (w = -1), energy densities.
Narrow statement: these algebraic consequences, with both Friedmann
equations taken as hypotheses at one instant. Deriving the Friedmann
equations from the Einstein equations is not formalized. -/

/-- Deceleration parameter `q = -a a'' / a'^2`. -/
def decelParam (a a1 a2 : Real) : Real := -(a * a2) / a1 ^ 2

/-- `Lambda = 8 pi G rho_vac / c^4`. -/
def cosmoLambda (G c rv : Real) : Real := 8 * Real.pi * G * rv / c ^ 4

/-- The vacuum term of the energy density is the Lambda term of the
Friedmann equation. -/
theorem friedmann_lambda {G c : Real} (hc : Ne c 0) (rm rr rv : Real) :
    8 * Real.pi * G * (rm + rr) / (3 * c ^ 2) + cosmoLambda G c rv * c ^ 2 / 3
      = 8 * Real.pi * G * (rm + rr + rv) / (3 * c ^ 2) := by
  unfold cosmoLambda
  field_simp

theorem vacuum_of_cosmoLambda {G c : Real} (hG : Ne G 0) (hc : Ne c 0) (rv : Real) :
    rv = cosmoLambda G c rv * c ^ 4 / (8 * Real.pi * G) := by
  unfold cosmoLambda
  have hpi : Ne Real.pi 0 := Real.pi_ne_zero
  field_simp

/-- The deceleration parameter from the two Friedmann equations with
`p = rho_r/3 - rho_vac`. -/
theorem frw_decel {G c a a1 a2 rm rr rv : Real} (hG : Ne G 0) (hc : Ne c 0) (ha : Ne a 0)
    (hrho : Ne (rm + rr + rv) 0)
    (hF : (a1 / a) ^ 2 = 8 * Real.pi * G * (rm + rr + rv) / (3 * c ^ 2))
    (hA : a2 / a
      = -(4 * Real.pi * G / (3 * c ^ 2)) * ((rm + rr + rv) + 3 * (rr / 3 - rv))) :
    decelParam a a1 a2 = (rm / 2 + rr - rv) / (rm + rr + rv) := by
  have hpi : Ne Real.pi 0 := Real.pi_ne_zero
  have hH : Ne ((a1 / a) ^ 2) 0 := by
    rw [hF]
    have : Ne (3 * c ^ 2) 0 := mul_ne_zero three_ne_zero (pow_ne_zero 2 hc)
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hpi) hG) hrho) this
  have ha1 : Ne a1 0 := by
    intro h
    apply hH
    rw [h]
    simp
  have hq : decelParam a a1 a2 = -(a2 / a) / (a1 / a) ^ 2 := by
    unfold decelParam
    field_simp
  rw [hq, hF, hA]
  field_simp
  ring

/-- Single components: matter q = 1/2, radiation q = 1, vacuum q = -1. -/
theorem frw_decel_single (r : Real) (hr : Ne r 0) :
    (r / 2 + 0 - 0) / (r + 0 + 0) = 1 / 2 /\ (0 / 2 + r - 0) / (0 + r + 0) = 1
      /\ (0 / 2 + 0 - r) / (0 + 0 + r) = -1 := by
  simp only [add_zero, zero_add, sub_zero, zero_div, zero_sub]
  refine And.intro ?_ (And.intro ?_ ?_)
  next =>
    rw [div_div, div_eq_iff (mul_ne_zero two_ne_zero hr)]
    ring
  next => exact div_self hr
  next => rw [neg_div, div_self hr]

/-! ## 5. DIFFUSION_RG_HEURISTICS: finite Markov and eigenmode formulas

Registry: `P >= 0; sum_j P_ij = 1; X_n = P^n X; gap = 1 - |lambda_2(P)|;
decay_exponent = -log|lambda| / log 2`, with complex eigenpairs retained and
fixed modes requiring lambda near +1, not unit modulus alone. Narrow
statement: these finite-matrix facts. The renormalization-group reading is
not formalized. -/

section Markov

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Row-stochastic: nonnegative entries, rows summing to 1. -/
def IsStochastic (P : Matrix n n Real) : Prop :=
  (forall i j, 0 <= P i j) /\ forall i, Finset.sum Finset.univ (fun j => P i j) = 1

omit [DecidableEq n] in
/-- The constant vector is a right eigenvector with eigenvalue 1
(automatic from row normalization, as the registry says). -/
theorem IsStochastic.mulVec_one {P : Matrix n n Real} (hP : IsStochastic P) :
    P.mulVec (fun _ => 1) = fun _ => 1 := by
  funext i
  simp [Matrix.mulVec, dotProduct, hP.2 i]

theorem isStochastic_one : IsStochastic (1 : Matrix n n Real) := by
  refine And.intro (fun i j => ?_) (fun i => ?_)
  next =>
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  next =>
    simp [Matrix.one_apply]

omit [DecidableEq n] in
theorem IsStochastic.mul {P Q : Matrix n n Real} (hP : IsStochastic P) (hQ : IsStochastic Q) :
    IsStochastic (P * Q) := by
  refine And.intro (fun i j => ?_) (fun i => ?_)
  next =>
    rw [Matrix.mul_apply]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hP.1 i k) (hQ.1 k j))
  next =>
    simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [<- Finset.mul_sum, hQ.2, mul_one]
    exact hP.2 i

theorem IsStochastic.pow {P : Matrix n n Real} (hP : IsStochastic P) (k : Nat) :
    IsStochastic (P ^ k) := by
  induction k with
  | zero => simpa using (isStochastic_one (n := n))
  | succ k ih =>
    rw [pow_succ]
    exact ih.mul hP

/-- `X_k = P^k X`. -/
def markovIter (P : Matrix n n Real) (X : n -> Real) (k : Nat) : n -> Real :=
  (P ^ k).mulVec X

theorem markovIter_succ (P : Matrix n n Real) (X : n -> Real) (k : Nat) :
    markovIter P X (k + 1) = P.mulVec (markovIter P X k) := by
  unfold markovIter
  rw [pow_succ', Matrix.mulVec_mulVec]

/-- Complexified matrix, so complex eigenpairs are retained. -/
def cplx (P : Matrix n n Real) : Matrix n n Complex := P.map (fun x => (x : Complex))

/-- An eigenvector of M is one of `M^k` with eigenvalue `lam^k`. -/
theorem pow_mulVec_eigen {M : Matrix n n Complex} {lam : Complex} {v : n -> Complex}
    (h : M.mulVec v = fun i => lam * v i) (k : Nat) :
    (M ^ k).mulVec v = fun i => lam ^ k * v i := by
  induction k with
  | zero => funext i; simp
  | succ k ih =>
    rw [pow_succ', <- Matrix.mulVec_mulVec, ih]
    have hlin : M.mulVec (fun i => lam ^ k * v i) = fun i => lam ^ k * M.mulVec v i := by
      funext i
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hlin, h]
    funext i
    ring

omit [DecidableEq n] in
/-- Every (complex) eigenvalue of a row-stochastic matrix has modulus <= 1. -/
theorem IsStochastic.norm_eig_le_one {P : Matrix n n Real} (hP : IsStochastic P)
    {lam : Complex} {v : n -> Complex} (hv : Ne v 0)
    (h : (cplx P).mulVec v = fun i => lam * v i) : norm lam <= 1 := by
  have hex : exists i, Ne (v i) 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv (funext hcon)
  cases hex with
  | intro i0 hi0 =>
  have hne : Finset.univ.Nonempty := Finset.univ_nonempty_iff.mpr (Nonempty.intro i0)
  cases Finset.exists_max_image Finset.univ (fun j => norm (v j)) hne with
  | intro i hi =>
  have hmax : forall j, norm (v j) <= norm (v i) := fun j => hi.2 j (Finset.mem_univ j)
  have hvi : 0 < norm (v i) := lt_of_lt_of_le (norm_pos_iff.mpr hi0) (hmax i0)
  have hrow := congrFun h i
  simp only [cplx, Matrix.mulVec, dotProduct, Matrix.map_apply] at hrow
  have key : norm lam * norm (v i) <= norm (v i) := by
    rw [<- norm_mul, <- hrow]
    calc norm (Finset.sum Finset.univ (fun j => (P i j : Complex) * v j))
        <= Finset.sum Finset.univ (fun j => norm ((P i j : Complex) * v j)) :=
          norm_sum_le _ _
      _ = Finset.sum Finset.univ (fun j => P i j * norm (v j)) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hP.1 i j)]
      _ <= Finset.sum Finset.univ (fun j => P i j * norm (v i)) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hmax j) (hP.1 i j))
      _ = norm (v i) := by rw [<- Finset.sum_mul, hP.2 i, one_mul]
  nlinarith

/-- `gap = 1 - |lambda|`. -/
def specGap (lam : Complex) : Real := 1 - norm lam

omit [DecidableEq n] in
/-- For any eigenvalue of a stochastic matrix the gap lies in [0, 1]. -/
theorem IsStochastic.specGap_mem {P : Matrix n n Real} (hP : IsStochastic P)
    {lam : Complex} {v : n -> Complex} (hv : Ne v 0)
    (h : (cplx P).mulVec v = fun i => lam * v i) :
    0 <= specGap lam /\ specGap lam <= 1 := by
  have := hP.norm_eig_le_one hv h
  unfold specGap
  exact And.intro (by linarith) (by linarith [norm_nonneg lam])

/-- `decay_exponent = -log|lambda| / log 2`. -/
def decayExp (lam : Complex) : Real := -Real.log (norm lam) / Real.log 2

theorem decayExp_nonneg {lam : Complex} (h : norm lam <= 1) : 0 <= decayExp lam :=
  div_nonneg (neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) h))
    (Real.log_pos one_lt_two).le

/-- The exponent is a power law in the scale `2^k`: `|lam|^k = (2^k)^(-d)`. -/
theorem norm_pow_eq_decay {lam : Complex} (hlam : Ne lam 0) (k : Nat) :
    norm lam ^ k = ((2 : Real) ^ k) ^ (-decayExp lam) := by
  have h2 : (0 : Real) < 2 ^ k := by positivity
  have hl : 0 < norm lam := norm_pos_iff.mpr hlam
  have hlog2 : Ne (Real.log 2) 0 := (Real.log_pos one_lt_two).ne'
  rw [Real.rpow_def_of_pos h2, Real.log_pow, decayExp]
  rw [show (k : Real) * Real.log 2 * -(-Real.log (norm lam) / Real.log 2)
      = Real.log (norm lam ^ k) by rw [Real.log_pow]; field_simp]
  rw [Real.exp_log (pow_pos hl k)]

/-- Eigenmode amplitude after k steps: `|(P^k v)_i| = (2^k)^(-d) |v_i|`. -/
theorem eigenmode_decay {P : Matrix n n Real} {lam : Complex} {v : n -> Complex}
    (hlam : Ne lam 0) (h : (cplx P).mulVec v = fun i => lam * v i) (k : Nat) (i : n) :
    norm (((cplx P) ^ k).mulVec v i) = ((2 : Real) ^ k) ^ (-decayExp lam) * norm (v i) := by
  rw [pow_mulVec_eigen h k, norm_mul, norm_pow, norm_pow_eq_decay hlam k]

end Markov

/-- The flip chain `[[0, 1], [1, 0]]`. -/
def flipP : Matrix (Fin 2) (Fin 2) Real := !![0, 1; 1, 0]

theorem flipP_isStochastic : IsStochastic flipP := by
  refine And.intro (fun i j => ?_) (fun i => ?_)
  next => fin_cases i <;> fin_cases j <;> simp [flipP]
  next => fin_cases i <;> simp [flipP, Fin.sum_univ_two]

/-- Unit modulus alone is not a fixed mode: the flip chain has eigenvalue -1
(eigenvector (1, -1)), modulus 1, yet the mode changes sign each step. -/
theorem flip_unit_modulus_not_fixed :
    (cplx flipP).mulVec ![1, -1] = (fun i => (-1 : Complex) * ![1, -1] i)
      /\ norm (-1 : Complex) = 1 /\ Ne (-1 : Complex) 1
      /\ Ne ((cplx flipP).mulVec ![1, -1]) ![1, -1] := by
  have hmv : (cplx flipP).mulVec ![(1 : Complex), -1] = fun i => (-1 : Complex) * ![1, -1] i := by
    funext i
    fin_cases i <;> simp [cplx, flipP, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine And.intro hmv (And.intro (by simp) (And.intro (by norm_num) ?_))
  rw [hmv]
  intro h
  have h0 := congrFun h 0
  norm_num at h0

/-! ## 6. TRIANGLE_CANONICAL_NORMALIZATION: affine substitution and determinant

Registry: `Omega = 18 dx^dy / (L1 L2 L3)`, `L1 = y - 2x + 2`, `L2 = y + x + 2`,
`L3 = -2y + x + 2`. Narrow statement: `L1 + L2 + L3 = 6`, so `b_i = L_i / 6`
are barycentric coordinates of the triangle with vertices (-2, 0), (2, 2),
(0, -2); the substitution `(x, y) -> (b1, b2)` is affine with Jacobian
determinant -1/12 (inverse Jacobian -12, an independent barycentric check),
and `|det| / (b1 b2 b3) = 18 / (L1 L2 L3)`: the standard simplex density
`1/(b1 b2 b3)` pulled back to (x, y) has coefficient 18. Differential forms,
orientation and the canonical-form theorem are not formalized. -/

def triL1 (x y : Real) : Real := y - 2 * x + 2
def triL2 (x y : Real) : Real := y + x + 2
def triL3 (x y : Real) : Real := -2 * y + x + 2

theorem tri_sum (x y : Real) : triL1 x y + triL2 x y + triL3 x y = 6 := by
  unfold triL1 triL2 triL3
  ring

/-- Each `L_i` vanishes on the two other vertices and is 6 at its own. -/
theorem tri_vertices :
    (triL1 (-2) 0 = 6 /\ triL2 (-2) 0 = 0 /\ triL3 (-2) 0 = 0)
    /\ (triL1 2 2 = 0 /\ triL2 2 2 = 6 /\ triL3 2 2 = 0)
    /\ (triL1 0 (-2) = 0 /\ triL2 0 (-2) = 0 /\ triL3 0 (-2) = 6) := by
  unfold triL1 triL2 triL3
  norm_num

/-- Barycentric reconstruction `(x, y) = b1 V1 + b2 V2 + b3 V3`. -/
theorem tri_reconstruct (x y : Real) :
    triL1 x y / 6 * (-2) + triL2 x y / 6 * 2 + triL3 x y / 6 * 0 = x
    /\ triL1 x y / 6 * 0 + triL2 x y / 6 * 2 + triL3 x y / 6 * (-2) = y := by
  unfold triL1 triL2 triL3
  constructor <;> ring

/-- Linear part of `(x, y) -> (L1/6, L2/6)`. -/
def triJac : Matrix (Fin 2) (Fin 2) Real := !![-2 / 6, 1 / 6; 1 / 6, 1 / 6]

/-- Linear part of the inverse `(b1, b2) -> (x, y)` with `b3 = 1 - b1 - b2`. -/
def triJacInv : Matrix (Fin 2) (Fin 2) Real := !![-2, 2; 2, 4]

theorem tri_affine (x y : Real) :
    ![triL1 x y / 6, triL2 x y / 6] = triJac.mulVec ![x, y] + ![1 / 3, 1 / 3] := by
  funext i
  fin_cases i <;> simp [triJac, triL1, triL2] <;> ring

theorem tri_affine_inv (x y : Real) :
    ![x, y] = triJacInv.mulVec ![triL1 x y / 6, triL2 x y / 6] + ![0, -2] := by
  funext i
  fin_cases i <;> simp [triJacInv, triL1, triL2] <;> ring

theorem triJac_det : triJac.det = -1 / 12 := by
  rw [triJac, Matrix.det_fin_two_of]
  norm_num

theorem triJacInv_det : triJacInv.det = -12 := by
  rw [triJacInv, Matrix.det_fin_two_of]
  norm_num

theorem triJacInv_mul : triJacInv * triJac = 1 := by
  rw [triJacInv, triJac]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The normalization coefficient 18. -/
theorem tri_density (x y : Real) :
    |triJac.det| / (triL1 x y / 6 * (triL2 x y / 6) * (triL3 x y / 6))
      = 18 / (triL1 x y * triL2 x y * triL3 x y) := by
  rw [triJac_det]
  norm_num
  ring

/-! ## 7. LANE_EMDEN_EQUATION: reduction to the scalar ODE

Registry: `theta'' + 2 theta'/xi + theta^n = 0`. Narrow statement: radial
Newtonian hydrostatic equilibrium `P' = -G m rho / r^2`, `m' = 4 pi r^2 rho`
with the polytrope `rho = rho_c theta^n`, `P = K_c theta^(n+1)`
(`K_c = K rho_c^(1+1/n)`) on an interval `0 < r < R` where theta > 0 reduces,
under `r = a xi` with `a^2 = (n+1) K_c / (4 pi G rho_c^2)`, to the stated ODE.
n is a natural number. Existence of equilibria and the solver-behavior
claims are not formalized. -/

/-- Equilibrium gives the ODE in r. -/
theorem laneEmden_radial {G Kc rhoc R : Real} {n : Nat}
    {theta theta1 theta2 m P rho : Real -> Real}
    (hG : 0 < G) (hK : 0 < Kc) (hrc : 0 < rhoc)
    (htheta : forall r, 0 < r -> r < R -> HasDerivAt theta (theta1 r) r)
    (htheta1 : forall r, 0 < r -> r < R -> HasDerivAt theta1 (theta2 r) r)
    (hpos : forall r, 0 < r -> r < R -> 0 < theta r)
    (hrho : forall r, 0 < r -> r < R -> rho r = rhoc * theta r ^ n)
    (hpoly : forall r, 0 < r -> r < R -> P r = Kc * theta r ^ (n + 1))
    (hmass : forall r, 0 < r -> r < R -> HasDerivAt m (4 * Real.pi * r ^ 2 * rho r) r)
    (hhyd : forall r, 0 < r -> r < R -> HasDerivAt P (-(G * m r * rho r) / r ^ 2) r)
    {r : Real} (hr : 0 < r) (hrR : r < R) :
    theta2 r + 2 * theta1 r / r
      + 4 * Real.pi * G * rhoc ^ 2 / ((n + 1) * Kc) * theta r ^ n = 0 := by
  have hn1 : (0 : Real) < n + 1 := by positivity
  -- mass from the two expressions for P'
  have hm : forall s, 0 < s -> s < R ->
      m s = -(Kc * (n + 1)) / (G * rhoc) * (s ^ 2 * theta1 s) := by
    intro s hs hsR
    have hPpoly : HasDerivAt P (Kc * ((n + 1 : Nat) * theta s ^ n * theta1 s)) s := by
      have h := ((htheta s hs hsR).pow (n + 1)).const_mul Kc
      rw [Nat.add_sub_cancel] at h
      refine h.congr_of_eventuallyEq ?_
      exact Filter.eventually_of_mem (Ioo_mem_nhds hs hsR)
        (fun y hy => hpoly y hy.1 hy.2)
    have heq := hPpoly.unique (hhyd s hs hsR)
    rw [hrho s hs hsR] at heq
    have htn : 0 < theta s ^ n := pow_pos (hpos s hs hsR) n
    push_cast at heq
    field_simp at heq
    field_simp
    nlinarith [htn, heq]
  have hmd : HasDerivAt m
      (-(Kc * (n + 1)) / (G * rhoc) * (2 * r * theta1 r + r ^ 2 * theta2 r)) r := by
    have h' : HasDerivAt (fun s => -(Kc * (n + 1)) / (G * rhoc) * (s ^ 2 * theta1 s))
        (-(Kc * (n + 1)) / (G * rhoc) * (2 * r * theta1 r + r ^ 2 * theta2 r)) r := by
      have h2 := ((hasDerivAt_pow 2 r).mul (htheta1 r hr hrR)).const_mul
        (-(Kc * (n + 1)) / (G * rhoc))
      convert h2 using 1
      push_cast
      ring
    refine h'.congr_of_eventuallyEq ?_
    exact Filter.eventually_of_mem (Ioo_mem_nhds hr hrR) (fun y hy => hm y hy.1 hy.2)
  have heq := hmd.unique (hmass r hr hrR)
  rw [hrho r hr hrR] at heq
  field_simp at heq
  field_simp
  nlinarith [heq]

/-- LANE_EMDEN_EQUATION: in `xi = r / a`, `Theta(xi) = theta(a xi)` satisfies
`Theta'' + 2 Theta'/xi + Theta^n = 0` with `Theta' = a theta'(a xi)`,
`Theta'' = a^2 theta''(a xi)`. -/
theorem laneEmden_equation {G Kc rhoc R a : Real} {n : Nat}
    {theta theta1 theta2 m P rho : Real -> Real}
    (hG : 0 < G) (hK : 0 < Kc) (hrc : 0 < rhoc) (ha : 0 < a)
    (hscale : a ^ 2 = (n + 1) * Kc / (4 * Real.pi * G * rhoc ^ 2))
    (htheta : forall r, 0 < r -> r < R -> HasDerivAt theta (theta1 r) r)
    (htheta1 : forall r, 0 < r -> r < R -> HasDerivAt theta1 (theta2 r) r)
    (hpos : forall r, 0 < r -> r < R -> 0 < theta r)
    (hrho : forall r, 0 < r -> r < R -> rho r = rhoc * theta r ^ n)
    (hpoly : forall r, 0 < r -> r < R -> P r = Kc * theta r ^ (n + 1))
    (hmass : forall r, 0 < r -> r < R -> HasDerivAt m (4 * Real.pi * r ^ 2 * rho r) r)
    (hhyd : forall r, 0 < r -> r < R -> HasDerivAt P (-(G * m r * rho r) / r ^ 2) r)
    {xi : Real} (hxi : 0 < xi) (hxiR : a * xi < R) :
    HasDerivAt (fun x => theta (a * x)) (a * theta1 (a * xi)) xi
    /\ HasDerivAt (fun x => a * theta1 (a * x)) (a ^ 2 * theta2 (a * xi)) xi
    /\ a ^ 2 * theta2 (a * xi) + 2 * (a * theta1 (a * xi)) / xi + theta (a * xi) ^ n = 0 := by
  have hr : 0 < a * xi := mul_pos ha hxi
  refine And.intro ?_ (And.intro ?_ ?_)
  next =>
    have h := (htheta (a * xi) hr hxiR).comp xi ((hasDerivAt_id' xi).const_mul a)
    convert h using 1
    ring
  next =>
    have h := ((htheta1 (a * xi) hr hxiR).comp xi ((hasDerivAt_id' xi).const_mul a)).const_mul a
    convert h using 1
    ring
  next =>
    have hode := laneEmden_radial hG hK hrc htheta htheta1 hpos hrho hpoly hmass hhyd hr hxiR
    have hpi : 0 < Real.pi := Real.pi_pos
    have hn1 : (0 : Real) < n + 1 := by positivity
    have hc : a ^ 2 * (4 * Real.pi * G * rhoc ^ 2 / ((n + 1) * Kc)) = 1 := by
      rw [hscale]
      field_simp
    have hxa : Ne (a * xi) 0 := hr.ne'
    calc a ^ 2 * theta2 (a * xi) + 2 * (a * theta1 (a * xi)) / xi + theta (a * xi) ^ n
        = a ^ 2 * (theta2 (a * xi) + 2 * theta1 (a * xi) / (a * xi)
            + 4 * Real.pi * G * rhoc ^ 2 / ((n + 1) * Kc) * theta (a * xi) ^ n)
          + (1 - a ^ 2 * (4 * Real.pi * G * rhoc ^ 2 / ((n + 1) * Kc)))
            * theta (a * xi) ^ n := by
          field_simp
          ring
      _ = 0 := by rw [hode, hc]; ring

/-! ## 8. CZACHOR_OSCILLATOR_SPECTRUM: the transported algebra

Registry: `E_{n,f} = f^-1(f(alpha) f(beta) (2n + 1))`. Narrow statement: for
a bijection `f : X ~ R` this is `(alpha (*) beta) (*) ((2_f (*) n_f) (+) 1_f)`
in Czachor's operations (`m_f = f^-1(m)`), equivalently
`alpha * beta * (2 * n + 1)` in the transported field `czachorField`
(LaneC4 section 9); consecutive levels differ by `2_f (*) alpha (*) beta`;
and the project's positive power chart gives `alpha beta (2n+1)^(1-k)`. That
the ordinary oscillator has spectrum `(2n + 1)` (the unbounded eigenproblem)
is not formalized. -/

section Czachor

variable {X : Type*}

/-- `E_{n,f} = f^-1(f(alpha) f(beta) (2n + 1))`. -/
def czachorEnergy (f : Chart X Real) (alpha beta : X) (k : Nat) : X :=
  f.symm (f alpha * f beta * (2 * k + 1))

theorem czachorEnergy_apply (f : Chart X Real) (alpha beta : X) (k : Nat) :
    f (czachorEnergy f alpha beta k) = f alpha * f beta * (2 * k + 1) :=
  Equiv.apply_symm_apply f _

/-- The level in Czachor's operations. -/
theorem czachorEnergy_gform (f : Chart X Real) (alpha beta : X) (k : Nat) :
    czachorEnergy f alpha beta k
      = gmul f (gmul f alpha beta) (gadd f (gmul f (f.symm 2) (f.symm k)) (f.symm 1)) := by
  apply f.injective
  simp [czachorEnergy, gmul, gadd]

/-- The same level in the transported field, whose numerals and casts are
`f^-1` of the real ones. -/
theorem czachorEnergy_transported (f : Chart X Real) (alpha beta : X) (k : Nat) :
    letI := czachorField f
    czachorEnergy f alpha beta k = alpha * beta * (2 * (k : X) + 1) := by
  letI := czachorField f
  exact czachorEnergy_gform f alpha beta k

/-- Equal transported spacing: `E_(n+1) = E_n (+) (2_f (*) (alpha (*) beta))`. -/
theorem czachorEnergy_succ (f : Chart X Real) (alpha beta : X) (k : Nat) :
    czachorEnergy f alpha beta (k + 1)
      = gadd f (czachorEnergy f alpha beta k) (gmul f (f.symm 2) (gmul f alpha beta)) := by
  apply f.injective
  simp [czachorEnergy, gmul, gadd]
  ring

/-- In chart coordinates consecutive levels differ by `2 f(alpha) f(beta)`. -/
theorem czachorEnergy_spacing (f : Chart X Real) (alpha beta : X) (k : Nat) :
    f (czachorEnergy f alpha beta (k + 1)) - f (czachorEnergy f alpha beta k)
      = 2 * (f alpha * f beta) := by
  rw [czachorEnergy_apply, czachorEnergy_apply]
  push_cast
  ring

end Czachor

/-- Positive power chart `f(x) = x^p` on (0, inf): the level is
`alpha beta (2n+1)^(1/p)`. -/
theorem czachor_power_level {alpha beta p : Real} (ha : 0 < alpha) (hb : 0 < beta)
    (hp : Ne p 0) (k : Nat) :
    (alpha ^ p * beta ^ p * (2 * k + 1)) ^ (1 / p) = alpha * beta * (2 * k + 1) ^ (1 / p) := by
  have hk : (0 : Real) <= 2 * k + 1 := by positivity
  rw [Real.mul_rpow (by positivity) hk, Real.mul_rpow (by positivity) (by positivity),
    one_div, Real.rpow_rpow_inv ha.le hp, Real.rpow_rpow_inv hb.le hp]

/-- The registry's specialization with `1/p = 1 - kap`, `kap < 1`. -/
theorem czachor_power_spectrum {alpha beta kap : Real} (ha : 0 < alpha) (hb : 0 < beta)
    (hk : kap < 1) (k : Nat) :
    (alpha ^ (1 / (1 - kap)) * beta ^ (1 / (1 - kap)) * (2 * k + 1)) ^ (1 - kap)
      = alpha * beta * (2 * k + 1) ^ (1 - kap) := by
  have hp : Ne (1 / (1 - kap)) 0 := one_div_ne_zero (sub_pos.mpr hk).ne'
  have h := czachor_power_level ha hb hp k
  rwa [one_div_one_div] at h

end GCC
