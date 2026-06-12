/-
# Generator Coordinate Calculus (GCC) — Mathlib laboratory

This is the merged Lean direction after comparing the two drafts:

* use Mathlib and `Equiv`/ordinary algebra instead of a hand-rolled ring shim;
* keep the chart/flow abstraction for real dynamics;
* port the proof-bearing algebraic/discrete content: transport, razor,
  discrete FTC, straight-line iff, generated means, and Pareto soundness;
* remove decorative enum-style claims entirely.

There are no intentional proof placeholders in this file. The former analytic
obligations are discharged in §7 and assembled into chart instruments below.

Static status: this file has not been compiled in this runtime; no Lean/Lake
toolchain is installed here.

Typeclass hygiene rule used here: each theorem asks for the weakest single
class layer it needs; inherited ancestors are not stacked as separate binders.
-/

import Mathlib

noncomputable section

open scoped BigOperators

namespace GCC

/-! ## 1. Charts / generators -/

/-- A chart/generator is an equivalence between raw states and coordinates. -/
abbrev Chart (State Coord : Type*) := State ≃ Coord

variable {State Coord α β σ : Type*}

/-- Native straight-line flow induced by a chart. -/
def nativeLine [Add Coord] [SMul ℝ Coord]
    (ψ : Chart State Coord) (x₀ : State) (v : Coord) (t : ℝ) : State :=
  ψ.symm (ψ x₀ + t • v)

@[simp]
theorem apply_nativeLine [Add Coord] [SMul ℝ Coord]
    (ψ : Chart State Coord) (x₀ : State) (v : Coord) (t : ℝ) :
    ψ (nativeLine ψ x₀ v t) = ψ x₀ + t • v := by
  simp [nativeLine]

/-- One explicit Euler step in the selected chart, not raw coordinates. -/
def chartEuler [Add Coord] [SMul ℝ Coord]
    (ψ : Chart State Coord) (V : State → Coord) (h : ℝ) (x : State) : State :=
  ψ.symm (ψ x + h • V x)

@[simp]
theorem apply_chartEuler [Add Coord] [SMul ℝ Coord]
    (ψ : Chart State Coord) (V : State → Coord) (h : ℝ) (x : State) :
    ψ (chartEuler ψ V h x) = ψ x + h • V x := by
  simp [chartEuler]

/-! ## 2. Transported arithmetic: non-Newtonian arithmetic as conjugation -/

def gadd [Add β] (g : Chart α β) (x y : α) : α :=
  g.symm (g x + g y)

def gmul [Mul β] (g : Chart α β) (x y : α) : α :=
  g.symm (g x * g y)

def gneg [Neg β] (g : Chart α β) (x : α) : α :=
  g.symm (-(g x))

def gsub [Sub β] (g : Chart α β) (x y : α) : α :=
  g.symm (g x - g y)

def gzero [Zero β] (g : Chart α β) : α :=
  g.symm 0

def gone [One β] (g : Chart α β) : α :=
  g.symm 1

@[simp] theorem apply_gadd [Add β] (g : Chart α β) (x y : α) :
    g (gadd g x y) = g x + g y := by
  simp [gadd]

@[simp] theorem apply_gmul [Mul β] (g : Chart α β) (x y : α) :
    g (gmul g x y) = g x * g y := by
  simp [gmul]

@[simp] theorem apply_gneg [Neg β] (g : Chart α β) (x : α) :
    g (gneg g x) = -(g x) := by
  simp [gneg]

@[simp] theorem apply_gsub [Sub β] (g : Chart α β) (x y : α) :
    g (gsub g x y) = g x - g y := by
  simp [gsub]

@[simp] theorem apply_gzero [Zero β] (g : Chart α β) :
    g (gzero g) = 0 := by
  simp [gzero]

@[simp] theorem apply_gone [One β] (g : Chart α β) :
    g (gone g) = 1 := by
  simp [gone]

/-- Transported addition is commutative when base addition is. -/
theorem gadd_comm [AddCommMagma β] (g : Chart α β) (x y : α) :
    gadd g x y = gadd g y x := by
  apply g.injective
  simp [add_comm]

/-- Transported addition is associative when base addition is. -/
theorem gadd_assoc [AddSemigroup β] (g : Chart α β) (x y z : α) :
    gadd g (gadd g x y) z = gadd g x (gadd g y z) := by
  apply g.injective
  simp [gadd, add_assoc]

/-- Transported zero is the identity when base zero is. -/
theorem gzero_add [AddZeroClass β] (g : Chart α β) (x : α) :
    gadd g (gzero g) x = x := by
  apply g.injective
  simp [gadd, gzero]

/-- Transported additive inverse is an inverse when the base has additive inverses. -/
theorem gadd_neg [AddGroup β] (g : Chart α β) (x : α) :
    gadd g x (gneg g x) = gzero g := by
  apply g.injective
  simp [gadd, gneg, gzero]

/-- Transported multiplication is commutative when base multiplication is. -/
theorem gmul_comm [CommMagma β] (g : Chart α β) (x y : α) :
    gmul g x y = gmul g y x := by
  apply g.injective
  simp [mul_comm]

/-- Transported multiplication is associative when base multiplication is. -/
theorem gmul_assoc [Semigroup β] (g : Chart α β) (x y z : α) :
    gmul g (gmul g x y) z = gmul g x (gmul g y z) := by
  apply g.injective
  simp [gmul, mul_assoc]

/-- Transported one is the multiplicative identity when base one is. -/
theorem gone_mul [MulOneClass β] (g : Chart α β) (x : α) :
    gmul g (gone g) x = x := by
  apply g.injective
  simp [gmul, gone]

/-- The whole ring law transports. -/
theorem gmul_gadd [NonUnitalNonAssocSemiring β] (g : Chart α β) (x y z : α) :
    gmul g x (gadd g y z) = gadd g (gmul g x y) (gmul g x z) := by
  apply g.injective
  simp [gmul, gadd, left_distrib]

/-! ## 3. Discrete generated calculus -/

/-- Discrete g-derivative: `Δ_g f n = f(n+1) ⊖_g f(n)`. -/
def gdiff [Sub β] (g : Chart α β) (f : ℕ → α) (n : ℕ) : α :=
  gsub g (f (n + 1)) (f n)

/-- Discrete g-integral: generated running sum. -/
def gsum [Zero β] [Add β] (g : Chart α β) (f : ℕ → α) : ℕ → α
  | 0     => gzero g
  | n + 1 => gadd g (gsum g f n) (f n)

@[simp] theorem gsum_zero [Zero β] [Add β] (g : Chart α β) (f : ℕ → α) :
    gsum g f 0 = gzero g := rfl

@[simp] theorem gsum_succ [Zero β] [Add β] (g : Chart α β) (f : ℕ → α) (n : ℕ) :
    gsum g f (n + 1) = gadd g (gsum g f n) (f n) := rfl

/-- Fundamental theorem of discrete g-calculus: generated sums of generated
successive differences telescope. -/
theorem gFTC [AddCommGroup β] (g : Chart α β) (f : ℕ → α) (n : ℕ) :
    gsum g (gdiff g f) n = gsub g (f n) (f 0) := by
  induction n with
  | zero =>
      apply g.injective
      simp [gsub]
  | succ n ih =>
      apply g.injective
      have ihc : g (gsum g (gdiff g f) n) = g (f n) - g (f 0) := by
        simpa [gsub] using congrArg g ih
      simp [gdiff, gsub, gadd, ihc]

/-- Arithmetic progression in the base. -/
def aprog [Add β] (b c : β) : ℕ → β
  | 0     => b
  | n + 1 => aprog b c n + c

@[simp] theorem aprog_zero [Add β] (b c : β) : aprog b c 0 = b := rfl

@[simp] theorem aprog_succ [Add β] (b c : β) (n : ℕ) :
    aprog b c (n + 1) = aprog b c n + c := rfl

/-- Constant generated derivative implies arithmetic progression in coordinates. -/
theorem const_gdiff [AddCommGroup β] (g : Chart α β) (f : ℕ → α) (c : β)
    (h : ∀ n, gdiff g f n = g.symm c) :
    ∀ n, g (f n) = aprog (g (f 0)) c n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have key : g (f (n + 1)) - g (f n) = c := by
        simpa [gdiff, gsub] using congrArg g (h n)
      have step : g (f (n + 1)) = g (f n) + c := by
        calc
          g (f (n + 1)) = (g (f (n + 1)) - g (f n)) + g (f n) := by abel
          _ = c + g (f n) := by rw [key]
          _ = g (f n) + c := by abel
      calc
        g (f (n + 1)) = g (f n) + c := step
        _ = aprog (g (f 0)) c n + c := by rw [ih]
        _ = aprog (g (f 0)) c (n + 1) := rfl

/-- Arithmetic progression in coordinates implies constant generated derivative. -/
theorem aprog_const_gdiff [AddCommGroup β] (g : Chart α β) (f : ℕ → α) (c : β)
    (h : ∀ n, g (f n) = aprog (g (f 0)) c n) :
    ∀ n, gdiff g f n = g.symm c := by
  intro n
  apply g.injective
  simp [gdiff, gsub, h (n + 1), h n, aprog_succ]

/-- Straight-line theorem, exact iff form. -/
theorem const_gdiff_iff [AddCommGroup β] (g : Chart α β) (f : ℕ → α) (c : β) :
    (∀ n, gdiff g f n = g.symm c)
      ↔
    (∀ n, g (f n) = aprog (g (f 0)) c n) := by
  constructor
  · exact const_gdiff g f c
  · exact aprog_const_gdiff g f c

/-! ## 4. Generated means and re-coordinatization invariance -/

/-- A base mean; no order/topology assumptions yet. -/
structure BMean (β : Type*) where
  m    : β → β → β
  idem : ∀ a, m a a = a
  comm : ∀ a b, m a b = m b a

/-- Quasi-arithmetic/generated mean. -/
def gmean (g : Chart α β) (M : BMean β) (x y : α) : α :=
  g.symm (M.m (g x) (g y))

@[simp] theorem gmean_idem (g : Chart α β) (M : BMean β) (x : α) :
    gmean g M x x = x := by
  apply g.injective
  simp [gmean, M.idem]

 theorem gmean_comm (g : Chart α β) (M : BMean β) (x y : α) :
    gmean g M x y = gmean g M y x := by
  apply g.injective
  simp [gmean, M.comm]

/-- An automorphism of the coordinate base compatible with the selected mean. -/
structure MeanAuto (β : Type*) (M : BMean β) where
  equiv  : β ≃ β
  compat : ∀ a b, M.m (equiv a) (equiv b) = equiv (M.m a b)

/-- Post-compose a chart with a coordinate automorphism. -/
def recoord {M : BMean β} (g : Chart α β) (e : MeanAuto β M) : Chart α β :=
  g.trans e.equiv

/-- Mean-compatible re-coordinatization leaves the generated mean unchanged.
This is the mathematical φ-demotion pattern: only invariants survive chart change. -/
theorem gmean_recoord {M : BMean β} (g : Chart α β) (e : MeanAuto β M)
    (x y : α) : gmean (recoord g e) M x y = gmean g M x y := by
  simp only [gmean, recoord, Equiv.trans_apply, Equiv.symm_trans_apply]
  rw [e.compat]
  simp

/-- The midpoint base mean on reals. -/
def midpointMean : BMean ℝ where
  m a b := (a + b) / 2
  idem := by intro a; ring
  comm := by intro a b; ring

/-- Nonzero rescaling of coordinates preserves the midpoint mean. This is the
formal version of “log base is not observable” for generated midpoint means. -/
def scaleMeanAuto (c : ℝ) (hc : c ≠ 0) : MeanAuto ℝ midpointMean where
  equiv :=
    { toFun := fun x => c * x
      invFun := fun y => y / c
      left_inv := by
        intro x
        field_simp [hc]
      right_inv := by
        intro y
        field_simp [hc] }
  compat := by
    intro a b
    dsimp [midpointMean]
    field_simp [hc]

/-- Generated midpoint means are invariant under nonzero coordinate rescaling. -/
theorem gmean_scale_recoord (g : Chart α ℝ) (c : ℝ) (hc : c ≠ 0) (x y : α) :
    gmean (recoord g (scaleMeanAuto c hc)) midpointMean x y =
      gmean g midpointMean x y := by
  exact gmean_recoord g (scaleMeanAuto c hc) x y

/-! ### 4b. Operation-compatible re-coordinatization

Mean compatibility is not ring compatibility.  The Mathlib layer expresses the
stronger operation-wise certificate with `RingEquiv` rather than a bespoke
`RingAuto` shim.
-/

/-- Post-compose a chart with a ring automorphism of the coordinate base. -/
def recoordRing [Semiring β] (g : Chart α β) (e : β ≃+* β) : Chart α β :=
  g.trans e.toEquiv

@[simp]
theorem gadd_recoordRing [Semiring β] (g : Chart α β) (e : β ≃+* β) (x y : α) :
    gadd (recoordRing g e) x y = gadd g x y := by
  apply (recoordRing g e).injective
  simp [recoordRing, gadd]

@[simp]
theorem gmul_recoordRing [Semiring β] (g : Chart α β) (e : β ≃+* β) (x y : α) :
    gmul (recoordRing g e) x y = gmul g x y := by
  apply (recoordRing g e).injective
  simp [recoordRing, gmul]

@[simp]
theorem gzero_recoordRing [Semiring β] (g : Chart α β) (e : β ≃+* β) :
    gzero (recoordRing g e) = gzero g := by
  apply (recoordRing g e).injective
  simp [recoordRing, gzero]

@[simp]
theorem gone_recoordRing [Semiring β] (g : Chart α β) (e : β ≃+* β) :
    gone (recoordRing g e) = gone g := by
  apply (recoordRing g e).injective
  simp [recoordRing, gone]

@[simp]
theorem gneg_recoordRing [Ring β] (g : Chart α β) (e : β ≃+* β) (x : α) :
    gneg (recoordRing g e) x = gneg g x := by
  apply (recoordRing g e).injective
  simp [recoordRing, gneg]

@[simp]
theorem gsub_recoordRing [Ring β] (g : Chart α β) (e : β ≃+* β) (x y : α) :
    gsub (recoordRing g e) x y = gsub g x y := by
  apply (recoordRing g e).injective
  simp [recoordRing, gsub]

/-! ## 5. Pareto frontier discipline -/

/-- `y` dominates `x`: lower-or-equal on both objectives and strictly lower on one. -/
def Dominates (f₁ f₂ : σ → ℕ) (y x : σ) : Prop :=
  f₁ y ≤ f₁ x ∧ f₂ y ≤ f₂ x ∧ (f₁ y < f₁ x ∨ f₂ y < f₂ x)

/-- Pareto optimality for two discrete objectives. -/
def ParetoOptimal (f₁ f₂ : σ → ℕ) (x : σ) : Prop :=
  ¬ ∃ y, Dominates f₁ f₂ y x

/-- Weighted scalarization of two objectives. -/
def scalarize (w₁ w₂ : ℕ) (f₁ f₂ : σ → ℕ) (x : σ) : ℕ :=
  w₁ * f₁ x + w₂ * f₂ x

/-- Soundness of scalarization: a positive-weight scalarized minimizer is Pareto-optimal. -/
theorem scalarized_min_is_pareto {f₁ f₂ : σ → ℕ} {w₁ w₂ : ℕ}
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {x : σ}
    (hmin : ∀ y, scalarize w₁ w₂ f₁ f₂ x ≤ scalarize w₁ w₂ f₁ f₂ y) :
    ParetoOptimal f₁ f₂ x := by
  intro hex
  rcases hex with ⟨y, hle₁, hle₂, hstrict⟩
  have hy := hmin y
  unfold scalarize at hy
  cases hstrict with
  | inl hlt₁ =>
      have s₁ : w₁ * f₁ y < w₁ * f₁ x := Nat.mul_lt_mul_of_pos_left hlt₁ hw₁
      have s₂ : w₂ * f₂ y ≤ w₂ * f₂ x := Nat.mul_le_mul_left w₂ hle₂
      omega
  | inr hlt₂ =>
      have s₁ : w₁ * f₁ y ≤ w₁ * f₁ x := Nat.mul_le_mul_left w₁ hle₁
      have s₂ : w₂ * f₂ y < w₂ * f₂ x := Nat.mul_lt_mul_of_pos_left hlt₂ hw₂
      omega

/-- Three-point nonconvex frontier counterexample. -/
inductive Triad where
  | left
  | middle
  | right
  deriving DecidableEq, Repr

open Triad

def bad_f₁ : Triad → ℕ
  | left   => 0
  | middle => 60
  | right  => 100

def bad_f₂ : Triad → ℕ
  | left   => 100
  | middle => 60
  | right  => 0

/-- The middle point is Pareto-optimal. -/
theorem middle_pareto : ParetoOptimal bad_f₁ bad_f₂ middle := by
  intro h
  rcases h with ⟨y, hdom⟩
  cases y <;> simp [Dominates, bad_f₁, bad_f₂] at hdom

/-- But no positive linear scalarization selects the middle point. -/
theorem middle_not_scalar_min {w₁ w₂ : ℕ}
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    ¬ (∀ y, scalarize w₁ w₂ bad_f₁ bad_f₂ middle
          ≤ scalarize w₁ w₂ bad_f₁ bad_f₂ y) := by
  intro hmin
  have hL := hmin left
  have hR := hmin right
  simp only [scalarize, bad_f₁, bad_f₂] at hL hR
  omega

/-! ## 6. Positive real log chart: the analytic laboratory begins here -/

/-- Positive real state space. -/
abbrev PosReal : Type := {x : ℝ // 0 < x}

/-- The logarithmic chart on positive reals. -/
def logChart : Chart PosReal ℝ where
  toFun x := Real.log x.1
  invFun z := ⟨Real.exp z, Real.exp_pos z⟩
  left_inv := by
    intro x
    ext
    exact Real.exp_log x.property
  right_inv := by
    intro z
    exact Real.log_exp z

/-- A native line in log coordinates; in ordinary coordinates this is exponential. -/
def geometricLine (x₀ : PosReal) (r t : ℝ) : PosReal :=
  nativeLine logChart x₀ r t

/-- Log coordinates make geometric lines additive. -/
theorem geometricLine_logCoord (x₀ : PosReal) (r t : ℝ) :
    logChart (geometricLine x₀ r t) = logChart x₀ + t * r := by
  simpa [geometricLine, smul_eq_mul] using
    apply_nativeLine (ψ := logChart) (x₀ := x₀) (v := r) (t := t)

/-- Multiplicative/geometric Euler step: positivity is carried by the chart. -/
def multiplicativeEuler (g : PosReal → ℝ) (h : ℝ) (x : PosReal) : PosReal :=
  chartEuler logChart g h x

/-- The multiplicative Euler step cannot leave positive reals. -/
theorem multiplicativeEuler_pos (g : PosReal → ℝ) (h : ℝ) (x : PosReal) :
    0 < (multiplicativeEuler g h x).1 := by
  exact (multiplicativeEuler g h x).property


/-! ## 7. Discharged analytic obligations

These are the former named obligations from `GCC_Analysis_Obligations.lean`,
now placed in the Mathlib laboratory where the required real-analysis API lives.
-/

/-- Exponential/geometric line through a positive real state. -/
def expFlow (x₀ : PosReal) (r : ℝ) (t : ℝ) : PosReal :=
  ⟨x₀.1 * Real.exp (r * t), mul_pos x₀.property (Real.exp_pos _)⟩

/-- Log-coordinate rate of change. -/
def logRate (f : ℝ → PosReal) (t : ℝ) : ℝ :=
  deriv (fun s => Real.log (f s).1) t

/-- Exponentials have constant log-rate. -/
theorem logRate_expFlow (x₀ : PosReal) (r t : ℝ) :
    logRate (expFlow x₀ r) t = r := by
  unfold logRate
  have hfun : (fun s : ℝ => Real.log ((expFlow x₀ r s).1))
      = fun s : ℝ => Real.log x₀.1 + r * s := by
    funext s
    change Real.log (x₀.1 * Real.exp (r * s)) = Real.log x₀.1 + r * s
    rw [Real.log_mul (ne_of_gt x₀.property) (Real.exp_ne_zero _), Real.log_exp]
  rw [hfun]
  have hlin : HasDerivAt (fun s : ℝ => r * s) r t := by
    simpa using (HasDerivAt.const_mul r (hasDerivAt_id t))
  have h : HasDerivAt (fun s : ℝ => Real.log x₀.1 + r * s) r t :=
    hlin.const_add (Real.log x₀.1)
  exact h.deriv

/-- The native log-chart line is the exponential flow. -/
theorem geometricLine_eq_expFlow (x₀ : PosReal) (r t : ℝ) :
    geometricLine x₀ r t = expFlow x₀ r t := by
  apply Subtype.ext
  simp [geometricLine, nativeLine, logChart, expFlow, smul_eq_mul,
    Real.exp_add, Real.exp_log x₀.property, mul_comm, mul_left_comm, mul_assoc]

/-- Exponentials, stated on the lab's canonical `geometricLine`, have constant
log-rate `r`. -/
theorem logRate_geometricLine (x₀ : PosReal) (r t : ℝ) :
    logRate (geometricLine x₀ r) t = r := by
  have h : geometricLine x₀ r = expFlow x₀ r :=
    funext (geometricLine_eq_expFlow x₀ r)
  rw [h]
  exact logRate_expFlow x₀ r t

/-- The open unit interval. -/
abbrev OpenUnit : Type := {x : ℝ // 0 < x ∧ x < 1}

/-- Logistic sigmoid. -/
def sigmoid (z : ℝ) : ℝ :=
  (1 + Real.exp (-z))⁻¹

/-- Logit coordinate on the open unit interval. -/
def logit (x : OpenUnit) : ℝ :=
  Real.log (x.1 / (1 - x.1))

/-- Sigmoid maps real coordinates into `(0,1)`. -/
theorem sigmoid_mem_openUnit (z : ℝ) :
    0 < sigmoid z ∧ sigmoid z < 1 := by
  unfold sigmoid
  have hu_pos : (0 : ℝ) < Real.exp (-z) := Real.exp_pos _
  have hden_pos : (0 : ℝ) < 1 + Real.exp (-z) := by positivity
  have hden_ne : 1 + Real.exp (-z) ≠ 0 := ne_of_gt hden_pos
  have hsub_eq :
      1 - (1 + Real.exp (-z))⁻¹ = Real.exp (-z) / (1 + Real.exp (-z)) := by
    field_simp [hden_ne]
    ring
  have hsub_pos : (0 : ℝ) < 1 - (1 + Real.exp (-z))⁻¹ := by
    rw [hsub_eq]
    exact div_pos hu_pos hden_pos
  constructor
  · exact inv_pos.mpr hden_pos
  · linarith [hsub_pos]

/-- Sigmoid as a map into the open unit interval. -/
def sigmoidToOpenUnit (z : ℝ) : OpenUnit :=
  ⟨sigmoid z, sigmoid_mem_openUnit z⟩

/-- Logit after sigmoid is the identity. -/
theorem logit_sigmoid (z : ℝ) :
    logit (sigmoidToOpenUnit z) = z := by
  unfold logit sigmoidToOpenUnit sigmoid
  dsimp
  have hu_pos : (0 : ℝ) < Real.exp (-z) := Real.exp_pos _
  have hu_ne : Real.exp (-z) ≠ 0 := Real.exp_ne_zero _
  have hden_pos : (0 : ℝ) < 1 + Real.exp (-z) := by positivity
  have hden_ne : 1 + Real.exp (-z) ≠ 0 := ne_of_gt hden_pos
  have hsub_eq :
      1 - (1 + Real.exp (-z))⁻¹ = Real.exp (-z) / (1 + Real.exp (-z)) := by
    field_simp [hden_ne]
    ring
  have hsub_pos : (0 : ℝ) < 1 - (1 + Real.exp (-z))⁻¹ := by
    rw [hsub_eq]
    exact div_pos hu_pos hden_pos
  have hsub_ne : 1 - (1 + Real.exp (-z))⁻¹ ≠ 0 := ne_of_gt hsub_pos
  have key :
      ((1 + Real.exp (-z))⁻¹) / (1 - (1 + Real.exp (-z))⁻¹)
        = (Real.exp (-z))⁻¹ := by
    field_simp [hden_ne, hsub_ne, hu_ne]
    ring
  rw [key, Real.log_inv, Real.log_exp]
  ring

/-- Sigmoid after logit is the identity on the open unit interval. -/
theorem sigmoid_logit (x : OpenUnit) :
    sigmoid (logit x) = x.1 := by
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨h0, h1⟩
  unfold sigmoid logit
  dsimp
  have hden_pos : (0 : ℝ) < 1 - x := sub_pos.mpr h1
  have hq : (0 : ℝ) < x / (1 - x) := div_pos h0 hden_pos
  rw [Real.exp_neg, Real.exp_log hq, inv_div]
  have hx_ne : x ≠ 0 := ne_of_gt h0
  have hfrac_pos : (0 : ℝ) < (1 - x) / x := div_pos hden_pos h0
  have hbig_pos : (0 : ℝ) < 1 + (1 - x) / x := by
    linarith [hfrac_pos]
  have hbig_ne : 1 + (1 - x) / x ≠ 0 := ne_of_gt hbig_pos
  field_simp [hx_ne, hbig_ne]
  ring

/-- Chart-level inverse: sigmoid after logit is the identity on `OpenUnit`. -/
theorem sigmoidToOpenUnit_logit (x : OpenUnit) :
    sigmoidToOpenUnit (logit x) = x := by
  exact Subtype.ext (sigmoid_logit x)

/-- The logit chart `(0,1) ≃ ℝ`. Bounded states now have an honest coordinate
instrument, parallel to `logChart` for positive states. -/
def logitChart : Chart OpenUnit ℝ where
  toFun := logit
  invFun := sigmoidToOpenUnit
  left_inv := sigmoidToOpenUnit_logit
  right_inv := logit_sigmoid

/-- A native line in logit coordinates: logistic-coordinate straight motion. -/
def logisticLine (x₀ : OpenUnit) (v t : ℝ) : OpenUnit :=
  nativeLine logitChart x₀ v t

/-- Logit coordinates make logistic lines additive: the bounded sibling of
`geometricLine_logCoord`. -/
theorem logisticLine_logitCoord (x₀ : OpenUnit) (v t : ℝ) :
    logitChart (logisticLine x₀ v t) = logitChart x₀ + t * v := by
  simpa [logisticLine, smul_eq_mul] using
    apply_nativeLine (ψ := logitChart) (x₀ := x₀) (v := v) (t := t)

/-- Logistic Euler step: boundedness is carried by the chart. -/
def logisticEuler (g : OpenUnit → ℝ) (h : ℝ) (x : OpenUnit) : OpenUnit :=
  chartEuler logitChart g h x

/-- The logistic Euler step cannot leave `(0,1)`. Illegal bounded states are
unrepresentable by construction. -/
theorem logisticEuler_mem (g : OpenUnit → ℝ) (h : ℝ) (x : OpenUnit) :
    0 < (logisticEuler g h x).1 ∧ (logisticEuler g h x).1 < 1 := by
  exact (logisticEuler g h x).property

end GCC
