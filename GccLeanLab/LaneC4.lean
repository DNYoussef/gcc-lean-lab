/-
# Lane C4: registry entries proved (2026-11-22)

Lean counterparts of entries in meta-calculus-portfolio docs/FORMULA_CLAIMS.json,
taken from the agreed PROVABLE_NOW queue of the Lane C triage
(metacalculus-audit-runs/20261121-proof-techniques/laneC/TRIAGE.md).
Where an entry is only a definition, the theorems state the defining
properties the registry or its authority record asserts. Scope differences
from the registry wording are stated in the docstrings and in
docs/THEOREM_MAP.md section 6. ASCII only (repository rule).
-/

import GccLeanLab.LaneC

noncomputable section

open MeasureTheory Set Filter Topology

namespace GCC

/-! ## 1. F002, F003, F004: identity, exponential and logarithmic generators

meta_calculus/core/generators.py classes `Identity`, `Exponential`, `Log`:
each implements a forward map, a derivative and an inverse. -/

/-- F002: the identity generator `alpha(x) = x`, a chart on R. -/
def idGen : Chart Real Real := Equiv.refl Real

theorem idGen_apply (x : Real) : idGen x = x := rfl

theorem idGen_symm_apply (y : Real) : idGen.symm y = y := rfl

/-- Python `Identity.derivative` returns 1. -/
theorem idGen_hasDerivAt (x : Real) : HasDerivAt (fun t => idGen t) 1 x :=
  hasDerivAt_id' x

/-- Identity-generated arithmetic is ordinary arithmetic. -/
theorem gadd_idGen (x y : Real) : gadd idGen x y = x + y := rfl

theorem gmul_idGen (x y : Real) : gmul idGen x y = x * y := rfl

/-- `logChart` read as a function. -/
theorem logChart_apply (x : PosReal) : logChart x = Real.log x.1 := rfl

/-- F003: the exponential generator `alpha(x) = exp(x)`, a chart from R onto
the positive reals; its inverse is `log`. -/
def expGen : Chart Real PosReal := logChart.symm

theorem expGen_apply (x : Real) : (expGen x).1 = Real.exp x := rfl

theorem expGen_symm_apply (y : PosReal) : expGen.symm y = Real.log y.1 := rfl

/-- Python `Exponential.derivative` returns `exp(x)`. -/
theorem expGen_hasDerivAt (x : Real) :
    HasDerivAt (fun t => (expGen t).1) (Real.exp x) x :=
  Real.hasDerivAt_exp x

/-- The range is exactly (0, inf); Python's inverse returns NaN off it. -/
theorem range_expGen : Set.range (fun x => (expGen x).1) = Set.Ioi 0 :=
  Real.range_exp

/-- exp-generated addition on (0, inf) is ordinary multiplication. -/
theorem gadd_logChart (x y : PosReal) : (gadd logChart x y).1 = x.1 * y.1 := by
  change Real.exp (Real.log x.1 + Real.log y.1) = x.1 * y.1
  rw [Real.exp_add, Real.exp_log x.2, Real.exp_log y.2]

/-- exp-generated multiplication is `x ^ log y`. -/
theorem gmul_logChart (x y : PosReal) :
    (gmul logChart x y).1 = x.1 ^ Real.log y.1 := by
  change Real.exp (Real.log x.1 * Real.log y.1) = x.1 ^ Real.log y.1
  rw [Real.rpow_def_of_pos x.2]

theorem gzero_logChart : (gzero logChart).1 = 1 := Real.exp_zero

/-- F004: the logarithmic generator `alpha(x) = ln(x)` on its domain (0, inf);
its inverse is `exp`. -/
def logGen : Chart PosReal Real := logChart

theorem logGen_apply (x : PosReal) : logGen x = Real.log x.1 := rfl

theorem logGen_symm_apply (y : Real) : (logGen.symm y).1 = Real.exp y := rfl

/-- Python `Log.derivative` returns `1/x` for x > 0. -/
theorem logGen_hasDerivAt {x : Real} (hx : 0 < x) :
    HasDerivAt Real.log (1 / x) x := by
  rw [one_div]
  exact Real.hasDerivAt_log hx.ne'

theorem expGen_eq_logGen_symm : expGen = logGen.symm := rfl

/-- ln-generated addition on R is log-sum-exp. -/
theorem gadd_logGen_symm (x y : Real) :
    gadd logGen.symm x y = Real.log (Real.exp x + Real.exp y) := rfl

/-- ln-generated multiplication on R is ordinary addition. -/
theorem gmul_logGen_symm (x y : Real) : gmul logGen.symm x y = x + y := by
  change Real.log (Real.exp x * Real.exp y) = x + y
  rw [<- Real.exp_add, Real.log_exp]

/-! ## 2. NNC_GENERATOR (Grossman-Katz 1972, section 5.3) -/

/-- NNC_GENERATOR: a one-to-one `alpha : R -> R` is an equivalence of R onto its
range A, the realm of alpha-arithmetic. -/
def nncGen (alpha : Real -> Real) (h : Function.Injective alpha) :
    Equiv Real (Set.range alpha) :=
  Equiv.ofInjective alpha h

theorem nncGen_apply (alpha : Real -> Real) (h : Function.Injective alpha)
    (x : Real) : (nncGen alpha h x).1 = alpha x := rfl

/-- alpha carries ordinary addition to alpha-addition on A. -/
theorem nncGen_add (alpha : Real -> Real) (h : Function.Injective alpha)
    (x y : Real) :
    gadd (nncGen alpha h).symm (nncGen alpha h x) (nncGen alpha h y)
      = nncGen alpha h (x + y) := by
  simp [gadd]

/-- alpha carries ordinary multiplication to alpha-multiplication on A. -/
theorem nncGen_mul (alpha : Real -> Real) (h : Function.Injective alpha)
    (x y : Real) :
    gmul (nncGen alpha h).symm (nncGen alpha h x) (nncGen alpha h y)
      = nncGen alpha h (x * y) := by
  simp [gmul]

/-- The source's examples I and exp are generators. -/
theorem id_isGenerator : Function.Injective (fun x : Real => x) :=
  fun _ _ h => h

theorem exp_isGenerator : Function.Injective Real.exp := Real.exp_injective

/-- The audit's old `Sqrt` map `sqrt |x|` is not a generator. -/
theorem sqrtAbs_not_isGenerator :
    Not (Function.Injective (fun x : Real => Real.sqrt |x|)) := by
  intro h
  have h1 := @h 1 (-1) (by simp)
  norm_num at h1

/-! ## 3. NNC_STAR_ISOMORPHISM (Grossman-Katz 1972, section 6.1)

Charts are the inverses of generators: `a = alpha^-1 : A -> R`,
`b = beta^-1 : B -> R`. -/

variable {X Y : Type*}

/-- Generated division `g^-1 (g x / g y)`. -/
def gdiv {A B : Type*} [Div B] (g : Chart A B) (x y : A) : A :=
  g.symm (g x / g y)

@[simp] theorem apply_gdiv {A B : Type*} [Div B] (g : Chart A B) (x y : A) :
    g (gdiv g x y) = g x / g y := by
  simp [gdiv]

/-- NNC_STAR_ISOMORPHISM: `iota = beta o alpha^-1 : A -> B`. -/
def iota (a : Chart X Real) (b : Chart Y Real) : Equiv X Y := a.trans b.symm

theorem iota_apply (a : Chart X Real) (b : Chart Y Real) (x : X) :
    iota a b x = b.symm (a x) := rfl

@[simp] theorem b_iota (a : Chart X Real) (b : Chart Y Real) (x : X) :
    b (iota a b x) = a x := by
  simp [iota]

/-- Generator form: `iota(alpha t) = beta t`, i.e. `iota(x) = beta(alpha^-1 x)`. -/
theorem iota_nncGen (alpha beta : Real -> Real) (ha : Function.Injective alpha)
    (hb : Function.Injective beta) (t : Real) :
    (iota (nncGen alpha ha).symm (nncGen beta hb).symm (nncGen alpha ha t)).1
      = beta t := by
  simp [iota, nncGen_apply]

/-- One-to-one and onto B. -/
theorem iota_bijective (a : Chart X Real) (b : Chart Y Real) :
    Function.Bijective (iota a b) :=
  (iota a b).bijective

theorem iota_gadd (a : Chart X Real) (b : Chart Y Real) (x y : X) :
    iota a b (gadd a x y) = gadd b (iota a b x) (iota a b y) := by
  apply b.injective
  simp

theorem iota_gsub (a : Chart X Real) (b : Chart Y Real) (x y : X) :
    iota a b (gsub a x y) = gsub b (iota a b x) (iota a b y) := by
  apply b.injective
  simp

theorem iota_gmul (a : Chart X Real) (b : Chart Y Real) (x y : X) :
    iota a b (gmul a x y) = gmul b (iota a b x) (iota a b y) := by
  apply b.injective
  simp

theorem iota_gdiv (a : Chart X Real) (b : Chart Y Real) (x y : X) :
    iota a b (gdiv a x y) = gdiv b (iota a b x) (iota a b y) := by
  apply b.injective
  simp

theorem iota_gzero (a : Chart X Real) (b : Chart Y Real) :
    iota a b (gzero a) = gzero b := by
  apply b.injective
  simp

theorem iota_gone (a : Chart X Real) (b : Chart Y Real) :
    iota a b (gone a) = gone b := by
  apply b.injective
  simp

/-- Order: under the chart-induced orders (`x <_alpha y` iff `a x < a y`),
iota preserves and reflects order. -/
theorem iota_lt_iff (a : Chart X Real) (b : Chart Y Real) (x y : X) :
    b (iota a b x) < b (iota a b y) <-> a x < a y := by
  simp

/-! ## 4. NNC_STAR_DERIVATIVE (Grossman-Katz 1972, section 6.3) -/

/-- The beta-quotient of beta-changes
`[f(x) -_beta f(x0)] /_beta [iota(x) -_beta iota(x0)]`. -/
def starQuot (a : Chart X Real) (b : Chart Y Real) (f : X -> Y) (x0 x : X) : Y :=
  gdiv b (gsub b (f x) (f x0)) (gsub b (iota a b x) (iota a b x0))

theorem b_starQuot (a : Chart X Real) (b : Chart Y Real) (f : X -> Y)
    (x0 x : X) :
    b (starQuot a b f x0 x) = (b (f x) - b (f x0)) / (a x - a x0) := by
  simp [starQuot]

/-- The coordinate representative `beta^-1 o f o alpha` on R. -/
def coordRep (a : Chart X Real) (b : Chart Y Real) (f : X -> Y) : Real -> Real :=
  fun t => b (f (a.symm t))

/-- The *-limit, read through the charts: x tends to x0 in the alpha-topology
(punctured) and values converge in the beta-topology. -/
def StarTendsto (a : Chart X Real) (b : Chart Y Real) (F : X -> Y) (x0 : X)
    (L : Y) : Prop :=
  Tendsto (fun t => b (F (a.symm t))) (nhdsWithin (a x0) (compl {a x0}))
    (nhds (b L))

/-- The *-derivative value `beta((beta^-1 o f o alpha)'(alpha^-1 x0))`. -/
def starDeriv (a : Chart X Real) (b : Chart Y Real) (f : X -> Y) (x0 : X) : Y :=
  b.symm (deriv (coordRep a b f) (a x0))

/-- NNC_STAR_DERIVATIVE: the *-limit of the beta-quotient is L exactly when the
coordinate representative has classical derivative `b L`. -/
theorem starTendsto_quot_iff (a : Chart X Real) (b : Chart Y Real) (f : X -> Y)
    (x0 : X) (L : Y) :
    StarTendsto a b (starQuot a b f x0) x0 L
      <-> HasDerivAt (coordRep a b f) (b L) (a x0) := by
  rw [hasDerivAt_iff_tendsto_slope]
  refine tendsto_congr (fun t => ?_)
  rw [b_starQuot, slope_def_field]
  simp [coordRep]

/-- Where the representative is differentiable the *-limit exists and is
`starDeriv`; the value lies in B by its type. -/
theorem starTendsto_starDeriv {a : Chart X Real} {b : Chart Y Real} {f : X -> Y}
    {x0 : X} (hf : DifferentiableAt Real (coordRep a b f) (a x0)) :
    StarTendsto a b (starQuot a b f x0) x0 (starDeriv a b f x0) := by
  rw [starTendsto_quot_iff]
  simp only [starDeriv, Equiv.apply_symm_apply]
  exact hf.hasDerivAt

/-- *-limits are unique. -/
theorem starTendsto_unique {a : Chart X Real} {b : Chart Y Real} {f : X -> Y}
    {x0 : X} {L : Y} (h : StarTendsto a b (starQuot a b f x0) x0 L) :
    L = starDeriv a b f x0 := by
  rw [starTendsto_quot_iff] at h
  apply b.injective
  simp only [starDeriv, Equiv.apply_symm_apply]
  exact h.deriv.symm

/-- beta-additivity. -/
theorem starDeriv_gadd {a : Chart X Real} {b : Chart Y Real} {f g : X -> Y}
    {x0 : X} (hf : DifferentiableAt Real (coordRep a b f) (a x0))
    (hg : DifferentiableAt Real (coordRep a b g) (a x0)) :
    starDeriv a b (fun x => gadd b (f x) (g x)) x0
      = gadd b (starDeriv a b f x0) (starDeriv a b g x0) := by
  have hrep : coordRep a b (fun x => gadd b (f x) (g x))
      = fun t => coordRep a b f t + coordRep a b g t := by
    funext t
    simp [coordRep]
  apply b.injective
  simp only [starDeriv, Equiv.apply_symm_apply, apply_gadd]
  rw [hrep]
  exact (hf.hasDerivAt.add hg.hasDerivAt).deriv

/-- beta-homogeneity, for a constant c in B. -/
theorem starDeriv_gmul_const {a : Chart X Real} {b : Chart Y Real} {f : X -> Y}
    {x0 : X} (c : Y) (hf : DifferentiableAt Real (coordRep a b f) (a x0)) :
    starDeriv a b (fun x => gmul b c (f x)) x0 = gmul b c (starDeriv a b f x0) := by
  have hrep : coordRep a b (fun x => gmul b c (f x))
      = fun t => b c * coordRep a b f t := by
    funext t
    simp [coordRep]
  apply b.injective
  simp only [starDeriv, Equiv.apply_symm_apply, apply_gmul]
  rw [hrep, deriv_const_mul _ hf]

/-- Identity charts give the classical derivative. -/
theorem starDeriv_classical (f : Real -> Real) (x : Real) :
    starDeriv (Equiv.refl Real) (Equiv.refl Real) f x = deriv f x := rfl

/-- Identity on the arguments, log on the values: the geometric derivative. -/
theorem starDeriv_geometric (f : Real -> PosReal) (x : Real)
    (hf : DifferentiableAt Real (fun t => (f t).1) x) :
    (starDeriv (Equiv.refl Real) logChart f x).1
      = geomDeriv (fun t => (f t).1) x := by
  rw [geomDeriv_eq_exp_deriv_log hf (f x).2.ne']
  rfl

/-- Log on both axes: the bigeometric derivative of MetaCalculus.lean. -/
theorem starDeriv_bigeometric (f : PosReal -> PosReal) (x : PosReal) :
    (starDeriv logChart logChart f x).1 = bgDerivMul f x := rfl

/-! ## 5. BG_DERIVATIVE (Grossman-Katz 1972, section 4.3) -/

/-- The bigeometric quotient is Grossman-Katz's `(f(x)/f(x0))^(1/(ln x - ln x0))`. -/
theorem starQuot_logChart (f : PosReal -> PosReal) (x0 x : PosReal) :
    (starQuot logChart logChart f x0 x).1
      = ((f x).1 / (f x0).1) ^ (1 / (Real.log x.1 - Real.log x0.1)) := by
  have hq : (starQuot logChart logChart f x0 x).1
      = Real.exp (logChart (starQuot logChart logChart f x0 x)) :=
    (Real.exp_log (starQuot logChart logChart f x0 x).2).symm
  rw [hq, b_starQuot, Real.rpow_def_of_pos (div_pos (f x).2 (f x0).2),
    Real.log_div (f x).2.ne' (f x0).2.ne']
  simp only [logChart_apply]
  congr 1
  ring

/-- BG_DERIVATIVE, log form: for f extending a real function F differentiable
at x, the bigeometric log-derivative is the elasticity `x F'(x) / F(x)`. -/
theorem bgDeriv_eq_elasticity (f : PosReal -> PosReal) (F : Real -> Real)
    (hF : forall x : PosReal, (f x).1 = F x.1) (x : PosReal)
    (hd : DifferentiableAt Real F x.1) :
    bgDeriv f x = x.1 * deriv F x.1 / F x.1 := by
  unfold bgDeriv
  have hfun : (fun u : Real => Real.log (f (logChart.symm u)).1)
      = fun u => Real.log (F (Real.exp u)) := by
    funext u
    rw [hF]
    rfl
  rw [hfun]
  have hexp : Real.exp (Real.log x.1) = x.1 := Real.exp_log x.2
  have hFx : Ne (F x.1) 0 := by
    rw [<- hF x]
    exact (f x).2.ne'
  have hF' : HasDerivAt F (deriv F x.1) (Real.exp (Real.log x.1)) := by
    rw [hexp]
    exact hd.hasDerivAt
  have h2 := (hF'.comp (Real.log x.1) (Real.hasDerivAt_exp (Real.log x.1))).log
    (by simp only [Function.comp_apply, hexp]; exact hFx)
  have h3 : deriv (fun u => Real.log (F (Real.exp u))) (Real.log x.1)
      = deriv F x.1 * Real.exp (Real.log x.1)
        / Function.comp F Real.exp (Real.log x.1) := h2.deriv
  rw [h3]
  simp only [Function.comp_apply, hexp]
  ring

/-- BG_DERIVATIVE: `D_BG[f](x) = exp(x F'(x) / F(x))`. -/
theorem bgDerivMul_eq_exp_elasticity (f : PosReal -> PosReal) (F : Real -> Real)
    (hF : forall x : PosReal, (f x).1 = F x.1) (x : PosReal)
    (hd : DifferentiableAt Real F x.1) :
    bgDerivMul f x = Real.exp (x.1 * deriv F x.1 / F x.1) := by
  rw [bgDerivMul, bgDeriv_eq_elasticity f F hF x hd]

/-! ## 6. META_WEIGHT_DOMAIN (Grossman 1981, section 2.2) -/

/-- META_WEIGHT_DOMAIN: a weight function is continuous and positive on R. -/
def IsWeight (w : Real -> Real) : Prop := Continuous w /\ forall x, 0 < w x

theorem isWeight_one : IsWeight (fun _ => 1) :=
  And.intro continuous_const (fun _ => one_pos)

theorem isWeight_exp : IsWeight Real.exp :=
  And.intro Real.continuous_exp Real.exp_pos

theorem IsWeight.mul {u v : Real -> Real} (hu : IsWeight u) (hv : IsWeight v) :
    IsWeight (fun x => u x * v x) :=
  And.intro (hu.1.mul hv.1) (fun x => mul_pos (hu.2 x) (hv.2 x))

/-- The ratio `v/u` that scales the meta-derivative is itself a weight. -/
theorem IsWeight.div {u v : Real -> Real} (hu : IsWeight u) (hv : IsWeight v) :
    IsWeight (fun x => v x / u x) :=
  And.intro (hv.1.div hu.1 (fun x => (hu.2 x).ne')) (fun x => div_pos (hv.2 x) (hu.2 x))

/-- Not every function is a weight. -/
theorem not_isWeight_id : Not (IsWeight (fun x : Real => x)) := by
  intro h
  have := h.2 0
  norm_num at this

/-- Under a weight pair the meta-derivative has the sign of the classical one. -/
theorem metaDeriv_pos_iff {u v : Real -> Real} (hu : IsWeight u) (hv : IsWeight v)
    (f : Real -> Real) (a : Real) :
    0 < metaDeriv u v f a <-> 0 < deriv f a := by
  have hc : 0 < v a / u a := div_pos (hv.2 a) (hu.2 a)
  unfold metaDeriv
  exact Iff.intro (fun h => (pos_iff_pos_of_mul_pos h).mp hc) (fun h => mul_pos hc h)

theorem metaDeriv_eq_zero_iff {u v : Real -> Real} (hu : IsWeight u)
    (hv : IsWeight v) (f : Real -> Real) (a : Real) :
    metaDeriv u v f a = 0 <-> deriv f a = 0 := by
  unfold metaDeriv
  simp [(hv.2 a).ne', (hu.2 a).ne']

/-- META_FTC_I holds for every weight pair. -/
theorem meta_ftc_I_of_weight {u v f : Real -> Real} {r s x : Real}
    (hu : IsWeight u) (hf : ContinuousOn f (Icc r s)) (hx : r < x /\ x < s) :
    metaDeriv u v (fun t => metaIntegral u f r t) x = v x * f x :=
  meta_ftc_I hu.1 hu.2 hf hx

/-! ## 7. META_MEASURE_ARGUMENT (Grossman 1981, section 2.3) -/

/-- META_MEASURE_ARGUMENT: the meta-measure of [r, s] is `int_r^s u`. -/
def metaMeasure (u : Real -> Real) (r s : Real) : Real :=
  intervalIntegral (fun x => u x) r s volume

/-- It is the meta-integral of the constant 1. -/
theorem metaMeasure_eq_metaIntegral_one (u : Real -> Real) (r s : Real) :
    metaMeasure u r s = metaIntegral u (fun _ => 1) r s := by
  simp [metaMeasure, metaIntegral]

/-- Unit weight gives classical length. -/
theorem metaMeasure_one (r s : Real) : metaMeasure (fun _ => 1) r s = s - r := by
  simp [metaMeasure]

/-- A weight gives every nondegenerate interval positive meta-measure. -/
theorem metaMeasure_pos {u : Real -> Real} (hu : IsWeight u) {r s : Real}
    (hrs : r < s) : 0 < metaMeasure u r s :=
  intervalIntegral.intervalIntegral_pos_of_pos_on (hu.1.intervalIntegrable r s)
    (fun x _ => hu.2 x) hrs

/-- Additive over adjacent intervals. -/
theorem metaMeasure_add {u : Real -> Real} (hu : IsWeight u) (r s t : Real) :
    metaMeasure u r s + metaMeasure u s t = metaMeasure u r t :=
  intervalIntegral.integral_add_adjacent_intervals (hu.1.intervalIntegrable r s)
    (hu.1.intervalIntegrable s t)

theorem metaMeasure_exp (r s : Real) :
    metaMeasure Real.exp r s = Real.exp s - Real.exp r :=
  integral_exp

/-! ## 8. META_CHANGE_ARGUMENT (Grossman 1981, section 2.4)

`metaChange v f r s = int_r^s v(x) f'(x) dx` is defined in LaneC.lean. -/

theorem metaChange_def (v f : Real -> Real) (r s : Real) :
    metaChange v f r s = intervalIntegral (fun x => v x * deriv f x) r s volume :=
  rfl

/-- The meta-change is the v-meta-integral of f'. -/
theorem metaChange_eq_metaIntegral (v f : Real -> Real) (r s : Real) :
    metaChange v f r s = metaIntegral v (deriv f) r s := rfl

/-- The rejected reading with v evaluated at function values. -/
def metaChangeAtValue (v f : Real -> Real) (r s : Real) : Real :=
  intervalIntegral (fun x => v (f x) * deriv f x) r s volume

/-- The argument reading is a different number from the value reading:
v = exp, f(x) = x + 1 on [0, 1] gives `e - 1` against `e^2 - e`. -/
theorem metaChange_ne_atValue :
    Ne (metaChange Real.exp (fun x => x + 1) 0 1)
      (metaChangeAtValue Real.exp (fun x => x + 1) 0 1) := by
  have hd : deriv (fun x : Real => x + 1) = fun _ => 1 := by
    funext x
    simp
  simp only [metaChange, metaChangeAtValue, hd, mul_one]
  rw [integral_exp, intervalIntegral.integral_comp_add_right (fun x => Real.exp x)]
  rw [integral_exp]
  intro h
  have he : (2 : Real) < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : Ne (1 : Real) 0)
    linarith
  have h2 : Real.exp (1 + 1) = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
  rw [zero_add, Real.exp_zero, h2] at h
  nlinarith

/-! ## 9. CZACHOR_TRANSPORTED_ARITHMETIC (Czachor 2016, section II)

`gadd f x y = f^-1 (f x + f y)` and `gmul f x y = f^-1 (f x * f y)` are
defined in Capstone.lean, which also transports commutativity,
associativity, identities, inverses and distributivity. Here the whole field
structure is transported at once. -/

/-- A bijection `f : X -> R` makes X a field (Mathlib `Equiv.field`). -/
abbrev czachorField (f : Chart X Real) : Field X := f.field

/-- Its addition is Czachor's `x (+) y = f^-1 (f x + f y)`. -/
theorem czachor_add (f : Chart X Real) (x y : X) :
    letI := czachorField f
    x + y = gadd f x y := rfl

/-- Its multiplication is Czachor's `x (*) y = f^-1 (f x * f y)`. -/
theorem czachor_mul (f : Chart X Real) (x y : X) :
    letI := czachorField f
    x * y = gmul f x y := rfl

/-- f is additive for the transported structure. -/
theorem czachor_map_add (f : Chart X Real) (x y : X) :
    letI := czachorField f
    f (x + y) = f x + f y :=
  Equiv.apply_symm_apply f _

/-- f is multiplicative for the transported structure. -/
theorem czachor_map_mul (f : Chart X Real) (x y : X) :
    letI := czachorField f
    f (x * y) = f x * f y :=
  Equiv.apply_symm_apply f _

/-! ## 10. BH_ENTROPY_CHART -/

/-- `S_ref = max(k_B, S_BH(M0))`. -/
def bhSRef (kB SBH0 : Real) : Real := max kB SBH0

theorem bhSRef_pos {kB : Real} (SBH0 : Real) (hk : 0 < kB) : 0 < bhSRef kB SBH0 :=
  lt_max_of_lt_left hk

theorem le_bhSRef (kB SBH0 : Real) : kB <= bhSRef kB SBH0 /\ SBH0 <= bhSRef kB SBH0 :=
  And.intro (le_max_left _ _) (le_max_right _ _)

/-- `S -> exp(S / S_ref)` is a chart from R onto (0, inf), inverse
`S_ref * log`. -/
def bhEntropyChart (Sref : Real) (h : 0 < Sref) : Chart Real PosReal where
  toFun S := Subtype.mk (Real.exp (S / Sref)) (Real.exp_pos _)
  invFun y := Sref * Real.log y.1
  left_inv S := by
    simp only [Real.log_exp]
    field_simp
  right_inv y := by
    apply Subtype.ext
    change Real.exp (Sref * Real.log y.1 / Sref) = y.1
    rw [show Sref * Real.log y.1 / Sref = Real.log y.1 by field_simp, Real.exp_log y.2]

/-- BH_ENTROPY_CHART: `S_star = exp(S / S_ref)` with `S_ref = max(k_B, S_BH(M0))`. -/
def bhEntropyStar (kB SBH0 : Real) (hk : 0 < kB) : Chart Real PosReal :=
  bhEntropyChart (bhSRef kB SBH0) (bhSRef_pos SBH0 hk)

theorem bhEntropyStar_apply (kB SBH0 : Real) (hk : 0 < kB) (S : Real) :
    (bhEntropyStar kB SBH0 hk S).1 = Real.exp (S / max kB SBH0) := rfl

/-- Entropy order is preserved: the chart adds no dynamics. -/
theorem bhEntropyChart_strictMono (Sref : Real) (h : 0 < Sref) :
    StrictMono (fun S => (bhEntropyChart Sref h S).1) := by
  intro S T hST
  change Real.exp (S / Sref) < Real.exp (T / Sref)
  rw [Real.exp_lt_exp]
  exact div_lt_div_of_pos_right hST h

/-- Additive entropies become multiplicative chart values. -/
theorem bhEntropyChart_add (Sref : Real) (h : 0 < Sref) (S T : Real) :
    (bhEntropyChart Sref h (S + T)).1
      = (bhEntropyChart Sref h S).1 * (bhEntropyChart Sref h T).1 := by
  change Real.exp ((S + T) / Sref) = Real.exp (S / Sref) * Real.exp (T / Sref)
  rw [add_div, Real.exp_add]

/-- Along any differentiable entropy history the chart value moves with the
same sign as S: `d S_star / dt = S_star * S' / S_ref`. -/
theorem bhEntropyChart_hasDerivAt (Sref : Real) (h : 0 < Sref) {S : Real -> Real}
    {S' t : Real} (hS : HasDerivAt S S' t) :
    HasDerivAt (fun t => (bhEntropyChart Sref h (S t)).1)
      ((bhEntropyChart Sref h (S t)).1 * (S' / Sref)) t :=
  (hS.div_const Sref).exp

/-! ## 11. SCHWARZSCHILD_RADIUS -/

/-- `r_s = 2 G M / c^2`. -/
def schwarzschildRadius (G M c : Real) : Real := 2 * G * M / c ^ 2

theorem schwarzschildRadius_pos {G M c : Real} (hG : 0 < G) (hM : 0 < M)
    (hc : 0 < c) : 0 < schwarzschildRadius G M c :=
  div_pos (mul_pos (mul_pos two_pos hG) hM) (pow_pos hc 2)

/-- Proportional to mass. -/
theorem schwarzschildRadius_mul (G M c k : Real) :
    schwarzschildRadius G (k * M) c = k * schwarzschildRadius G M c := by
  unfold schwarzschildRadius
  ring

theorem schwarzschildRadius_add (G M N c : Real) :
    schwarzschildRadius G (M + N) c
      = schwarzschildRadius G M c + schwarzschildRadius G N c := by
  unfold schwarzschildRadius
  ring

/-- The mass is recovered from the radius. -/
theorem mass_of_schwarzschildRadius {G M c : Real} (hG : Ne G 0) (hc : Ne c 0) :
    schwarzschildRadius G M c * c ^ 2 / (2 * G) = M := by
  unfold schwarzschildRadius
  field_simp

/-- The metric factor `1 - r_s / r` vanishes exactly at `r = r_s`. -/
theorem schwarzschild_factor_eq_zero_iff (G M c : Real) {r : Real} (hr : Ne r 0) :
    1 - schwarzschildRadius G M c / r = 0 <-> r = schwarzschildRadius G M c := by
  rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hr, eq_comm]

/-! ## 12. SHANNON_NORMALIZED_ENTROPY (Shannon 1948, Theorem 2)

Mathlib's `Real.negMulLog x = -x * log x` with `log 0 = 0` carries the
convention `0 * log 0 = 0`. -/

variable {I : Type*} [Fintype I]

/-- `H = -sum p_i log p_i`, in nats. -/
def shannonH (p : I -> Real) : Real := Finset.sum Finset.univ (fun i => Real.negMulLog (p i))

/-- `H / log N`; Mathlib's `log 1 = 0` and `x / 0 = 0` give 0 when N = 1, the
project convention. -/
def shannonNorm (p : I -> Real) : Real := shannonH p / Real.log (Fintype.card I)

/-- Probability vector. -/
def IsProb (p : I -> Real) : Prop :=
  (forall i, 0 <= p i) /\ Finset.sum Finset.univ p = 1

theorem shannonH_eq (p : I -> Real) :
    shannonH p = -Finset.sum Finset.univ (fun i => p i * Real.log (p i)) := by
  simp [shannonH, Real.negMulLog, Finset.sum_neg_distrib]

theorem zero_mul_log_zero : (0 : Real) * Real.log 0 = 0 := by simp

theorem IsProb.le_one {p : I -> Real} (hp : IsProb p) (i : I) : p i <= 1 := by
  rw [<- hp.2]
  exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)

theorem shannonH_nonneg {p : I -> Real} (hp : IsProb p) : 0 <= shannonH p :=
  Finset.sum_nonneg (fun i _ => Real.negMulLog_nonneg (hp.1 i) (hp.le_one i))

/-- A certain outcome has entropy zero. -/
theorem shannonH_single [DecidableEq I] (j : I) :
    shannonH (Pi.single j (1 : Real)) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases h : i = j
  next =>
    subst h
    simp
  next =>
    simp [h]

/-- The uniform distribution has entropy `log N`. -/
theorem shannonH_uniform (hN : 0 < Fintype.card I) :
    shannonH (fun _ : I => 1 / (Fintype.card I : Real)) = Real.log (Fintype.card I) := by
  have hN' : Ne (Fintype.card I : Real) 0 := by exact_mod_cast hN.ne'
  simp [shannonH, Real.negMulLog, Real.log_inv, Finset.sum_const, Finset.card_univ]
  field_simp

/-- Entropy is maximal at the uniform distribution: `H <= log N`. -/
theorem shannonH_le_log {p : I -> Real} (hp : IsProb p) :
    shannonH p <= Real.log (Fintype.card I) := by
  have hN : (0 : Real) < Fintype.card I := by
    rcases Nat.eq_zero_or_pos (Fintype.card I) with h | h
    next =>
      exfalso
      have hE : IsEmpty I := Fintype.card_eq_zero_iff.mp h
      have h2 := hp.2
      simp at h2
    next =>
      exact_mod_cast h
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
    (w := fun _ => Inv.inv (Fintype.card I : Real)) (p := p)
    (fun i _ => inv_nonneg.mpr hN.le)
    (by simp [Finset.sum_const, Finset.card_univ, hN.ne'])
    (fun i _ => hp.1 i)
  simp only [smul_eq_mul] at hJ
  rw [<- Finset.mul_sum, <- Finset.mul_sum, hp.2, mul_one] at hJ
  have hn : Real.negMulLog (Inv.inv (Fintype.card I : Real))
      = Inv.inv (Fintype.card I : Real) * Real.log (Fintype.card I) := by
    simp [Real.negMulLog, Real.log_inv]
  rw [hn] at hJ
  exact le_of_mul_le_mul_left hJ (inv_pos.mpr hN)

/-- For N > 1 the normalized entropy lies in [0, 1]. -/
theorem shannonNorm_mem {p : I -> Real} (hp : IsProb p) (hN : 1 < Fintype.card I) :
    0 <= shannonNorm p /\ shannonNorm p <= 1 := by
  have hlog : 0 < Real.log (Fintype.card I) :=
    Real.log_pos (by exact_mod_cast hN)
  constructor
  next =>
    exact div_nonneg (shannonH_nonneg hp) hlog.le
  next =>
    rw [shannonNorm, div_le_one hlog]
    exact shannonH_le_log hp

theorem shannonNorm_uniform (hN : 1 < Fintype.card I) :
    shannonNorm (fun _ : I => 1 / (Fintype.card I : Real)) = 1 := by
  have hlog : 0 < Real.log (Fintype.card I) :=
    Real.log_pos (by exact_mod_cast hN)
  rw [shannonNorm, shannonH_uniform (by omega), div_self hlog.ne']

/-- Project convention: a one-element signal has normalized entropy 0. -/
theorem shannonNorm_card_one (hN : Fintype.card I = 1) (p : I -> Real) :
    shannonNorm p = 0 := by
  simp [shannonNorm, hN]

/-! ## 13. STM_FERMI_DERIVATIVE (Zandvliet 2022, eq. B2) -/

/-- Fermi-Dirac occupation `1 / (1 + exp(E / kT))`, E measured from the Fermi
level, `kT = k_B T`. -/
def fermi (kT E : Real) : Real := Inv.inv (1 + Real.exp (E / kT))

/-- `K(E) = sech(E / (2 kT))^2 / (4 kT)`. -/
def stmKernel (kT E : Real) : Real := (Inv.inv (Real.cosh (E / (2 * kT)))) ^ 2 / (4 * kT)

/-- STM_FERMI_DERIVATIVE: the thermal kernel is `-df/dE`. -/
theorem fermi_hasDerivAt {kT : Real} (hT : 0 < kT) (E : Real) :
    HasDerivAt (fermi kT) (-stmKernel kT E) E := by
  have hx : HasDerivAt (fun E => 1 + Real.exp (E / kT)) (Real.exp (E / kT) * (1 / kT)) E :=
    (((hasDerivAt_id' E).div_const kT).exp).const_add 1
  have hpos : 0 < 1 + Real.exp (E / kT) := by positivity
  have h := hx.inv hpos.ne'
  convert h using 1
  unfold stmKernel
  have hsplit : E / kT = E / (2 * kT) + E / (2 * kT) := by
    field_simp
    ring
  have he : 0 < Real.exp (E / (2 * kT)) := Real.exp_pos _
  rw [Real.cosh_eq, hsplit, Real.exp_add, Real.exp_neg]
  field_simp
  ring

theorem stmKernel_pos {kT : Real} (hT : 0 < kT) (E : Real) : 0 < stmKernel kT E := by
  unfold stmKernel
  have := Real.cosh_pos (E / (2 * kT))
  positivity

/-- Even in E. -/
theorem stmKernel_neg (kT E : Real) : stmKernel kT (-E) = stmKernel kT E := by
  unfold stmKernel
  rw [neg_div, Real.cosh_neg]

/-- Peak value `1 / (4 kT)` at the Fermi level. -/
theorem stmKernel_zero (kT : Real) : stmKernel kT 0 = 1 / (4 * kT) := by
  simp [stmKernel]

/-! ## 14. AMPLITUDE_FOUR_POINT_ASSOCIAHEDRON (Arkani-Hamed, Bai, He, Yan 2017)

On the line `s + t = C`, `ds/s - dt/t = d(log s - log(C - s))`. -/

/-- The pullback coefficient with respect to ds is `1/s + 1/t`, t = C - s. -/
theorem fourPoint_pullback {C s : Real} (hs : 0 < s) (hsC : s < C) :
    HasDerivAt (fun x => Real.log x - Real.log (C - x)) (1 / s + 1 / (C - s)) s := by
  have h1 := Real.hasDerivAt_log hs.ne'
  have h2 := ((hasDerivAt_id' s).const_sub C).log (by linarith : Ne (C - s) 0)
  convert h1.sub h2 using 1
  ring

/-- Canonical form `C / (s t)`. -/
theorem fourPoint_canonical {C s : Real} (hs : Ne s 0) (hsC : Ne (C - s) 0) :
    1 / s + 1 / (C - s) = C / (s * (C - s)) := by
  field_simp
  ring

/-- Positive on the interior 0 < s < C. -/
theorem fourPoint_pos {C s : Real} (hs : 0 < s) (hsC : s < C) :
    0 < 1 / s + 1 / (C - s) := by
  have : 0 < C - s := by linarith
  positivity

/-- Symmetric under exchanging the two boundaries s and t. -/
theorem fourPoint_symm (C s : Real) :
    1 / (C - s) + 1 / (C - (C - s)) = 1 / s + 1 / (C - s) := by
  rw [sub_sub_cancel]
  ring

/-- The s = 0 boundary contributes residue 1 (and by `fourPoint_symm`, so does
t = 0). -/
theorem fourPoint_residue {C : Real} (hC : 0 < C) :
    Tendsto (fun s => s * (1 / s + 1 / (C - s))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hcont : ContinuousAt (fun s : Real => 1 + s / (C - s)) 0 := by
    apply ContinuousAt.add continuousAt_const
    exact continuousAt_id.div (continuousAt_const.sub continuousAt_id) (by simp [hC.ne'])
  have h1 : Tendsto (fun s : Real => 1 + s / (C - s)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h := hcont.tendsto
    simp only [zero_div, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : Ne s 0 := ne_of_gt hs
  rw [mul_add, mul_one_div_cancel hs0, mul_one_div]

/-! ## 15. BH_RADIATION_ENTROPY

The Bekenstein-Hawking entropy (registry BEKENSTEIN_HAWKING_ENTROPY, r_s form)
and the Hawking temperature (HAWKING_TEMPERATURE) enter as definitions; the
physics behind them is not formalized. -/

/-- `S_BH = k_B c^3 pi r_s^2 / (G hbar)`. -/
def bhEntropy (kB c G hbar M : Real) : Real :=
  kB * c ^ 3 * Real.pi * schwarzschildRadius G M c ^ 2 / (G * hbar)

/-- `T_H = hbar c^3 / (8 pi G M k_B)`. -/
def hawkingTemp (hbar c G M kB : Real) : Real :=
  hbar * c ^ 3 / (8 * Real.pi * G * M * kB)

theorem bhEntropy_eq {kB c G hbar : Real} (hc : Ne c 0) (hG : Ne G 0)
    (hh : Ne hbar 0) (M : Real) :
    bhEntropy kB c G hbar M = 4 * Real.pi * kB * G * M ^ 2 / (hbar * c) := by
  unfold bhEntropy schwarzschildRadius
  field_simp
  ring

/-- First law `dS_BH/dM = c^2 / T_H` (energy `E = M c^2`). -/
theorem bhEntropy_hasDerivAt {kB c G hbar M : Real} (hk : Ne kB 0) (hc : Ne c 0)
    (hG : Ne G 0) (hh : Ne hbar 0) (hM : Ne M 0) :
    HasDerivAt (bhEntropy kB c G hbar) (c ^ 2 / hawkingTemp hbar c G M kB) M := by
  have hfun : bhEntropy kB c G hbar
      = fun M => 4 * Real.pi * kB * G / (hbar * c) * (M * M) := by
    funext M
    rw [bhEntropy_eq hc hG hh]
    ring
  rw [hfun]
  have h := ((hasDerivAt_id' M).mul (hasDerivAt_id' M)).const_mul
    (4 * Real.pi * kB * G / (hbar * c))
  convert h using 1
  unfold hawkingTemp
  have hpi : Ne Real.pi 0 := Real.pi_ne_zero
  field_simp
  ring

/-- `S_rad = (4/3) (S_BH(M0) - S_BH(M))`. -/
def radEntropy (S0 S : Real) : Real := 4 / 3 * (S0 - S)

/-- `S_closure = -(1/3) (S_BH(M0) - S_BH(M))`. -/
def closureEntropy (S0 S : Real) : Real := -(1 / 3) * (S0 - S)

/-- Bookkeeping: radiation plus closure equals the entropy the hole lost. -/
theorem radEntropy_add_closure (S0 S : Real) :
    radEntropy S0 S + closureEntropy S0 S = S0 - S := by
  unfold radEntropy closureEntropy
  ring

theorem bhEntropy_mono {kB c G hbar M M0 : Real} (hk : 0 <= kB) (hc : 0 < c)
    (hG : 0 < G) (hh : 0 < hbar) (hM : 0 <= M) (hMM : M <= M0) :
    bhEntropy kB c G hbar M <= bhEntropy kB c G hbar M0 := by
  rw [bhEntropy_eq hc.ne' hG.ne' hh.ne', bhEntropy_eq hc.ne' hG.ne' hh.ne']
  have h2 : M ^ 2 <= M0 ^ 2 := by nlinarith
  have hK : 0 <= 4 * Real.pi * kB * G := by
    have := Real.pi_pos
    positivity
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hK) (by positivity)

/-- While the hole shrinks (0 <= M <= M0) the radiation entropy is
nonnegative and the closure term nonpositive. -/
theorem radEntropy_nonneg {kB c G hbar M M0 : Real} (hk : 0 <= kB) (hc : 0 < c)
    (hG : 0 < G) (hh : 0 < hbar) (hM : 0 <= M) (hMM : M <= M0) :
    0 <= radEntropy (bhEntropy kB c G hbar M0) (bhEntropy kB c G hbar M) /\
      closureEntropy (bhEntropy kB c G hbar M0) (bhEntropy kB c G hbar M) <= 0 := by
  have := bhEntropy_mono hk hc hG hh hM hMM
  unfold radEntropy closureEntropy
  constructor <;> linarith

/-- Photon gas: `dS_rad = (4/3) dE_rad / T` with `dE_rad = -c^2 dM` at
`T = T_H`; by the first law this is `dS_rad = -(4/3) dS_BH`. -/
theorem radEntropy_hasDerivAt {kB c G hbar M M0 : Real} (hk : Ne kB 0) (hc : Ne c 0)
    (hG : Ne G 0) (hh : Ne hbar 0) (hM : Ne M 0) :
    HasDerivAt (fun M => radEntropy (bhEntropy kB c G hbar M0) (bhEntropy kB c G hbar M))
      (4 / 3 * (-(c ^ 2) / hawkingTemp hbar c G M kB)) M := by
  have h := ((bhEntropy_hasDerivAt hk hc hG hh hM).const_sub
    (bhEntropy kB c G hbar M0)).const_mul (4 / 3 : Real)
  convert h using 1
  ring

/-! ## 16. BH_BLACKBODY_EVAPORATION -/

/-- `sigma = pi^2 k_B^4 / (60 hbar^3 c^2)`. -/
def stefanBoltzmann (kB hbar c : Real) : Real :=
  Real.pi ^ 2 * kB ^ 4 / (60 * hbar ^ 3 * c ^ 2)

/-- Blackbody power `P = (4 pi r_s^2) sigma T_H^4`. -/
def bhPower (kB hbar c G M : Real) : Real :=
  4 * Real.pi * schwarzschildRadius G M c ^ 2 * stefanBoltzmann kB hbar c
    * hawkingTemp hbar c G M kB ^ 4

/-- `K = hbar c^4 / (15360 pi G^2)`. -/
def evapK (hbar c G : Real) : Real := hbar * c ^ 4 / (15360 * Real.pi * G ^ 2)

/-- The registry's rate `hbar c^4 / (15360 pi G^2 M^2)` is `K / M^2`. -/
theorem evapK_div (hbar c G M : Real) :
    evapK hbar c G / M ^ 2 = hbar * c ^ 4 / (15360 * Real.pi * G ^ 2 * M ^ 2) := by
  unfold evapK
  rw [div_div]

/-- `P / c^2 = K / M^2`. -/
theorem bhPower_div {kB hbar c G M : Real} (hk : Ne kB 0) (hh : Ne hbar 0)
    (hc : Ne c 0) (hG : Ne G 0) (hM : Ne M 0) :
    bhPower kB hbar c G M / c ^ 2 = evapK hbar c G / M ^ 2 := by
  unfold bhPower stefanBoltzmann hawkingTemp schwarzschildRadius evapK
  have hpi : Ne Real.pi 0 := Real.pi_ne_zero
  field_simp
  ring

/-- Mass history `M(t) = (M0^3 - 3 K t)^(1/3)`. -/
def evapMass (K M0 t : Real) : Real := (M0 ^ 3 - 3 * K * t) ^ ((1 : Real) / 3)

/-- `t_evap = 5120 pi G^2 M0^3 / (hbar c^4)`. -/
def evapTime (hbar c G M0 : Real) : Real :=
  5120 * Real.pi * G ^ 2 * M0 ^ 3 / (hbar * c ^ 4)

theorem evapMass_hasDerivAt {K M0 t : Real} (hw : 0 < M0 ^ 3 - 3 * K * t) :
    HasDerivAt (evapMass K M0) (-K / evapMass K M0 t ^ 2) t := by
  have hlin : HasDerivAt (fun t => M0 ^ 3 - 3 * K * t) (-(3 * K)) t := by
    have := ((hasDerivAt_id' t).const_mul (3 * K)).const_sub (M0 ^ 3)
    convert this using 1
    ring
  have h := hlin.rpow_const (p := (1 : Real) / 3) (Or.inl hw.ne')
  convert h using 1
  have key : ((M0 ^ 3 - 3 * K * t) ^ ((1 : Real) / 3)) ^ 2
      * (M0 ^ 3 - 3 * K * t) ^ ((1 : Real) / 3 - 1) = 1 := by
    rw [sq, <- Real.rpow_add hw, <- Real.rpow_add hw]
    norm_num
  have hne : Ne (((M0 ^ 3 - 3 * K * t) ^ ((1 : Real) / 3)) ^ 2) 0 := by positivity
  unfold evapMass
  rw [div_eq_iff hne]
  linear_combination K * key

theorem evapMass_zero {K M0 : Real} (hM0 : 0 <= M0) : evapMass K M0 0 = M0 := by
  unfold evapMass
  rw [mul_zero, sub_zero, show (1 : Real) / 3 = Inv.inv ((3 : Nat) : Real) by norm_num]
  exact Real.pow_rpow_inv_natCast hM0 (by norm_num)

/-- The mass reaches zero exactly at t_evap. -/
theorem evapMass_evapTime {hbar c G M0 : Real} (hh : Ne hbar 0) (hc : Ne c 0)
    (hG : Ne G 0) : evapMass (evapK hbar c G) M0 (evapTime hbar c G M0) = 0 := by
  unfold evapMass
  have h0 : M0 ^ 3 - 3 * evapK hbar c G * evapTime hbar c G M0 = 0 := by
    unfold evapK evapTime
    have hpi : Ne Real.pi 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [h0, Real.zero_rpow (by norm_num)]

/-- BH_BLACKBODY_EVAPORATION: before t_evap the mass history solves
`dM/dt = -P/c^2 = -hbar c^4 / (15360 pi G^2 M^2)`. -/
theorem evapMass_solves {kB hbar c G M0 t : Real} (hk : Ne kB 0) (hh : Ne hbar 0)
    (hc : Ne c 0) (hG : Ne G 0) (hw : 0 < M0 ^ 3 - 3 * evapK hbar c G * t) :
    HasDerivAt (evapMass (evapK hbar c G) M0)
      (-(bhPower kB hbar c G (evapMass (evapK hbar c G) M0 t) / c ^ 2)) t := by
  have hM : Ne (evapMass (evapK hbar c G) M0 t) 0 := (Real.rpow_pos_of_pos hw _).ne'
  rw [bhPower_div hk hh hc hG hM, <- neg_div]
  exact evapMass_hasDerivAt hw

/-! ## 17. COSMOLOGY_REGULATED_VACUUM -/

/-- Phase-space prefactor `(1/2) 4 pi / (2 pi)^3 = 1 / (4 pi^2)`. -/
theorem vacuum_prefactor :
    (1 / 2 : Real) * (4 * Real.pi) / (2 * Real.pi) ^ 3 = 1 / (4 * Real.pi ^ 2) := by
  have hpi : Ne Real.pi 0 := Real.pi_ne_zero
  field_simp
  ring

/-- COSMOLOGY_REGULATED_VACUUM:
`int_0^inf E^3 exp(-E/E_c) / (4 pi^2) dE = 3 E_c^4 / (2 pi^2)`. -/
theorem regulated_vacuum {Ec : Real} (hE : 0 < Ec) :
    integral (volume.restrict (Ioi 0))
        (fun E : Real => E ^ 3 * Real.exp (-E / Ec) / (4 * Real.pi ^ 2))
      = 3 * Ec ^ 4 / (2 * Real.pi ^ 2) := by
  have hG := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 4) (r := 1 / Ec)
    (by norm_num) (by positivity)
  have hcongr : integral (volume.restrict (Ioi 0))
        (fun E : Real => E ^ 3 * Real.exp (-E / Ec))
      = integral (volume.restrict (Ioi 0))
        (fun t : Real => t ^ ((4 : Real) - 1) * Real.exp (-(1 / Ec * t))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [show (4 : Real) - 1 = ((3 : Nat) : Real) by norm_num, Real.rpow_natCast]
    congr 2
    ring
  have hGamma : Real.Gamma 4 = 6 := by
    rw [show (4 : Real) = ((3 : Nat) : Real) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  have hp : (1 / (1 / Ec)) ^ (4 : Real) = Ec ^ 4 := by
    rw [one_div_one_div, show (4 : Real) = ((4 : Nat) : Real) by norm_num, Real.rpow_natCast]
  rw [integral_div, hcongr, hG, hp, hGamma]
  have hpi : Ne Real.pi 0 := Real.pi_ne_zero
  field_simp
  ring

/-! ## 18. QUANTUM_PROJECTIVE_ANGLE (Braunstein-Caves 1994) -/

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Complex E]

/-- `d(psi, phi) = arccos(|<psi|phi>| / (|psi| |phi|))`. -/
def projAngle (psi phi : E) : Real :=
  Real.arccos (norm (inner Complex psi phi) / (norm psi * norm phi))

/-- Ray invariance: nonzero complex rescaling of either vector (in particular a
global phase) leaves the angle unchanged. -/
theorem projAngle_smul {c d : Complex} (hc : Ne c 0) (hd : Ne d 0) (psi phi : E) :
    projAngle (HSMul.hSMul c psi) (HSMul.hSMul d phi) = projAngle psi phi := by
  unfold projAngle
  have hcd : Ne (norm c * norm d) 0 :=
    mul_ne_zero (norm_ne_zero_iff.mpr hc) (norm_ne_zero_iff.mpr hd)
  have key : norm (inner Complex (HSMul.hSMul c psi) (HSMul.hSMul d phi))
      = (norm c * norm d) * norm (inner Complex psi phi) := by
    rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, RCLike.norm_conj]
    ring
  have key2 : norm (HSMul.hSMul c psi) * norm (HSMul.hSMul d phi)
      = (norm c * norm d) * (norm psi * norm phi) := by
    rw [norm_smul, norm_smul]
    ring
  rw [key, key2, mul_div_mul_left _ _ hcd]

theorem projAngle_comm (psi phi : E) : projAngle psi phi = projAngle phi psi := by
  unfold projAngle
  rw [norm_inner_symm, mul_comm (norm psi)]

theorem projAngle_self {psi : E} (h : Ne psi 0) : projAngle psi psi = 0 := by
  unfold projAngle
  have hn : Ne (norm psi) 0 := norm_ne_zero_iff.mpr h
  have hi : norm (inner Complex psi psi) = norm psi * norm psi := by
    rw [inner_self_eq_norm_sq_to_K]
    simp [sq]
  rw [hi, div_self (mul_ne_zero hn hn), Real.arccos_one]

theorem projAngle_nonneg (psi phi : E) : 0 <= projAngle psi phi :=
  Real.arccos_nonneg _

/-- By Cauchy-Schwarz the angle never exceeds pi/2. -/
theorem projAngle_le_pi_div_two (psi phi : E) : projAngle psi phi <= Real.pi / 2 :=
  Real.arccos_le_pi_div_two.mpr
    (div_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

theorem projAngle_of_inner_eq_zero {psi phi : E} (h : inner Complex psi phi = 0) :
    projAngle psi phi = Real.pi / 2 := by
  simp [projAngle, h, Real.arccos_zero]

/-! ## 20. QUANTUM_SPECTRAL_FUNCTION (Tokmakoff 2007, after eq. 1.15) -/

variable {J : Type*} [Fintype J]

/-- `f(H) v = sum_n f(E_n) <n|v> |n>` for an orthonormal eigenbasis b with
real energies e. -/
def specFun (b : OrthonormalBasis J Complex E) (e : J -> Real) (f : Real -> Complex)
    (v : E) : E :=
  Finset.sum Finset.univ (fun i => HSMul.hSMul (f (e i) * inner Complex (b i) v) (b i))

theorem inner_basis_sum (b : OrthonormalBasis J Complex E) (c : J -> Complex) (i : J) :
    inner Complex (b i) (Finset.sum Finset.univ (fun k => HSMul.hSMul (c k) (b k)))
      = c i := by
  classical
  simp [orthonormal_iff_ite.mp b.orthonormal]

/-- QUANTUM_SPECTRAL_FUNCTION: `f(H)|n> = f(E_n)|n>`. With `f = id` this is
`H|n> = E_n|n>`. -/
theorem specFun_basis (b : OrthonormalBasis J Complex E) (e : J -> Real)
    (f : Real -> Complex) (j : J) :
    specFun b e f (b j) = HSMul.hSMul (f (e j)) (b j) := by
  classical
  unfold specFun
  simp [orthonormal_iff_ite.mp b.orthonormal]

/-- The constant function 1 gives the identity operator. -/
theorem specFun_one (b : OrthonormalBasis J Complex E) (e : J -> Real) (v : E) :
    specFun b e (fun _ => 1) v = v := by
  simp [specFun, b.sum_repr']

/-- `(f g)(H) = f(H) g(H)`, so polynomials in H agree with `specFun`. -/
theorem specFun_mul (b : OrthonormalBasis J Complex E) (e : J -> Real)
    (f g : Real -> Complex) (v : E) :
    specFun b e f (specFun b e g v) = specFun b e (fun x => f x * g x) v := by
  unfold specFun
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [inner_basis_sum, mul_assoc]

end Hilbert

/-! ## 19. QUANTUM_STATIONARY_STATE (Tokmakoff 2007, eqs. 1.8-1.9) -/

section Stationary

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace Complex H]

/-- The phase `exp(-i E_n t / hbar)`, written with a real angle. -/
def stationaryPhase (En hbar t : Real) : Complex :=
  Complex.exp (((-(En * t / hbar) : Real) : Complex) * Complex.I)

theorem stationaryPhase_eq (En hbar t : Real) :
    stationaryPhase En hbar t = Complex.exp (-(Complex.I * En * t / hbar)) := by
  unfold stationaryPhase
  congr 1
  push_cast
  ring

/-- `psi_n(t) = exp(-i E_n t / hbar) psi_n(0)`. -/
def stationaryState (psi0 : H) (En hbar t : Real) : H :=
  HSMul.hSMul (stationaryPhase En hbar t) psi0

theorem stationaryState_zero (psi0 : H) (En hbar : Real) :
    stationaryState psi0 En hbar 0 = psi0 := by
  simp [stationaryState, stationaryPhase]

theorem stationaryPhase_hasDerivAt (En hbar t : Real) :
    HasDerivAt (stationaryPhase En hbar)
      (stationaryPhase En hbar t * (((-(En / hbar)) : Real) * Complex.I)) t := by
  have hg : HasDerivAt (fun t : Real => -(En * t / hbar)) (-(En / hbar)) t := by
    have := (((hasDerivAt_id' t).const_mul En).div_const hbar).neg
    convert this using 1
    ring
  exact (hg.ofReal_comp.mul_const Complex.I).cexp

/-- QUANTUM_STATIONARY_STATE: if `Ham psi0 = E_n psi0`, then psi solves the
Schroedinger equation `i hbar psi' = Ham psi`. -/
theorem stationaryState_schrodinger (Ham : ContinuousLinearMap (RingHom.id Complex) H H)
    {psi0 : H} {En hbar : Real} (hh : Ne hbar 0)
    (heig : Ham psi0 = HSMul.hSMul (En : Complex) psi0) (t : Real) :
    exists psi' : H, HasDerivAt (fun t => stationaryState psi0 En hbar t) psi' t /\
      HSMul.hSMul (Complex.I * hbar) psi' = Ham (stationaryState psi0 En hbar t) := by
  refine Exists.intro _
    (And.intro ((stationaryPhase_hasDerivAt En hbar t).smul_const psi0) ?_)
  rw [stationaryState, map_smul, heig, smul_smul, smul_smul]
  congr 1
  have hh' : Ne (hbar : Complex) 0 := by exact_mod_cast hh
  have hc : (hbar : Complex) * (-((En : Complex) / hbar)) = -En := by
    field_simp
  push_cast
  linear_combination (stationaryPhase En hbar t * Complex.I ^ 2) * hc
    - (stationaryPhase En hbar t * En) * Complex.I_sq

/-- The population is retained: `|psi_n(t)| = |psi_n(0)|`. -/
theorem norm_stationaryState (psi0 : H) (En hbar t : Real) :
    norm (stationaryState psi0 En hbar t) = norm psi0 := by
  rw [stationaryState, norm_smul, stationaryPhase, Complex.norm_exp_ofReal_mul_I, one_mul]

end Stationary

/-! ## 21. BH_STATE_ENTROPY (Almheiri et al. 2021, eq. 4.1) -/

section Matrices

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Von Neumann entropy from the eigenvalues, `-sum p log p` with `0 log 0 = 0`. -/
def vonNeumann {rho : Matrix n n Complex} (h : rho.IsHermitian) : Real :=
  shannonH h.eigenvalues

/-- Matrix logarithm on the eigenbasis, `U diag(log p) U*` (Mathlib `log 0 = 0`
on the kernel). -/
def matLog {rho : Matrix n n Complex} (h : rho.IsHermitian) : Matrix n n Complex :=
  (h.eigenvectorUnitary : Matrix n n Complex)
    * Matrix.diagonal (fun i => ((Real.log (h.eigenvalues i) : Real) : Complex))
    * star (h.eigenvectorUnitary : Matrix n n Complex)

/-- BH_STATE_ENTROPY: `-Tr(rho log rho) = -sum p log p`. -/
theorem neg_trace_mul_matLog {rho : Matrix n n Complex} (h : rho.IsHermitian) :
    -(rho * matLog h).trace = ((vonNeumann h : Real) : Complex) := by
  set U : Matrix n n Complex := (h.eigenvectorUnitary : Matrix n n Complex) with hUdef
  have hU : star U * U = 1 := Unitary.coe_star_mul_self h.eigenvectorUnitary
  have hrho : rho = U * Matrix.diagonal (fun i => ((h.eigenvalues i : Real) : Complex))
      * star U := by
    conv_lhs => rw [h.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hUdef, Function.comp_def]
  have e1 : rho * matLog h
      = U * Matrix.diagonal (fun i => ((h.eigenvalues i : Real) : Complex)) * star U
        * (U * Matrix.diagonal (fun i => ((Real.log (h.eigenvalues i) : Real) : Complex))
          * star U) :=
    congrArg (fun M => M * matLog h) hrho
  have e2 : U * Matrix.diagonal (fun i => ((h.eigenvalues i : Real) : Complex)) * star U
        * (U * Matrix.diagonal (fun i => ((Real.log (h.eigenvalues i) : Real) : Complex))
          * star U)
      = U * Matrix.diagonal
          (fun i => ((h.eigenvalues i * Real.log (h.eigenvalues i) : Real) : Complex))
        * star U := by
    calc _ = U * (Matrix.diagonal (fun i => ((h.eigenvalues i : Real) : Complex))
            * (star U * U)
            * Matrix.diagonal (fun i => ((Real.log (h.eigenvalues i) : Real) : Complex)))
            * star U := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
          rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
          congr 3
          funext i
          push_cast
          ring
  rw [e1, e2, Matrix.trace_mul_comm, <- Matrix.mul_assoc, hU, Matrix.one_mul,
    Matrix.trace_diagonal]
  simp [vonNeumann, shannonH, Real.negMulLog, Finset.sum_neg_distrib]

/-- A density matrix (positive semidefinite, trace one) has a probability vector
of eigenvalues. -/
theorem density_isProb {rho : Matrix n n Complex} (hpsd : rho.PosSemidef)
    (htr : rho.trace = 1) : IsProb hpsd.isHermitian.eigenvalues := by
  refine And.intro (fun i => hpsd.eigenvalues_nonneg i) ?_
  have h := hpsd.isHermitian.trace_eq_sum_eigenvalues
  rw [htr] at h
  have h2 : ((Finset.sum Finset.univ hpsd.isHermitian.eigenvalues : Real) : Complex) = 1 := by
    push_cast
    exact h.symm
  exact_mod_cast h2

/-- `0 <= S_vN <= log N` for density matrices. -/
theorem vonNeumann_bounds {rho : Matrix n n Complex} (hpsd : rho.PosSemidef)
    (htr : rho.trace = 1) :
    0 <= vonNeumann hpsd.isHermitian /\
      vonNeumann hpsd.isHermitian <= Real.log (Fintype.card n) :=
  And.intro (shannonH_nonneg (density_isProb hpsd htr))
    (shannonH_le_log (density_isProb hpsd htr))

/-! ## 22. MULTIMETRIC_DIFFUSION_COORDINATES (Coifman-Lafon 2006, Prop. 1) -/

omit [DecidableEq n] in
/-- Stationarity of `pi_u = d_u / sum d` for the walk `P = D^-1 W` with W
symmetric and positive degrees. -/
theorem diffusion_stationary (W : Matrix n n Real) (hW : W.transpose = W) (d : n -> Real)
    (hd : forall u, d u = Finset.sum Finset.univ (fun v => W u v))
    (hpos : forall u, 0 < d u) (v : n) :
    Finset.sum Finset.univ
        (fun u => d u / Finset.sum Finset.univ d * (W u v / d u))
      = d v / Finset.sum Finset.univ d := by
  have h1 : forall u, d u / Finset.sum Finset.univ d * (W u v / d u)
      = W v u / Finset.sum Finset.univ d := by
    intro u
    have hu := (hpos u).ne'
    have hS : 0 < Finset.sum Finset.univ d :=
      lt_of_lt_of_le (hpos u)
        (Finset.single_le_sum (fun i _ => (hpos i).le) (Finset.mem_univ u))
    have hsym : W u v = W v u := congrFun (congrFun hW v) u
    rw [hsym]
    field_simp
  simp only [h1, <- Finset.sum_div, <- hd]

/-- `P^t = Psi diag(lam^t) Psi^T diag(pi)` for a pi-orthonormal right
eigenbasis (columns of Psi). -/
theorem diffusion_power_eq (P Psi : Matrix n n Real) (lam piw : n -> Real)
    (heig : P * Psi = Psi * Matrix.diagonal lam)
    (horth : Psi.transpose * Matrix.diagonal piw * Psi = 1) (t : Nat) :
    P ^ t = Psi * Matrix.diagonal (fun j => lam j ^ t) * Psi.transpose
      * Matrix.diagonal piw := by
  have hright : Psi * (Psi.transpose * Matrix.diagonal piw) = 1 :=
    mul_eq_one_comm.mp horth
  have hpow : P ^ t * Psi = Psi * Matrix.diagonal (fun j => lam j ^ t) := by
    induction t with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.mul_assoc, heig, <- Matrix.mul_assoc, ih, Matrix.mul_assoc,
        Matrix.diagonal_mul_diagonal]
      congr 2
  calc P ^ t = P ^ t * (Psi * (Psi.transpose * Matrix.diagonal piw)) := by
        rw [hright, Matrix.mul_one]
    _ = _ := by
        rw [<- Matrix.mul_assoc (P ^ t) Psi, hpow, <- Matrix.mul_assoc]

/-- MULTIMETRIC_DIFFUSION_COORDINATES: the pi-weighted transition distance
`D_t(i,k)^2 = sum_u (P^t_iu - P^t_ku)^2 / pi_u` equals the squared Euclidean
distance of the diffusion coordinates `Phi_t(i)_j = lam_j^t psi_j(i)` over all
N modes. -/
theorem diffusion_distance (P Psi : Matrix n n Real) (lam piw : n -> Real)
    (heig : P * Psi = Psi * Matrix.diagonal lam)
    (horth : Psi.transpose * Matrix.diagonal piw * Psi = 1)
    (hpi : forall u, 0 < piw u) (t : Nat) (i k : n) :
    Finset.sum Finset.univ (fun u => ((P ^ t) i u - (P ^ t) k u) ^ 2 / piw u)
      = Finset.sum Finset.univ
          (fun j => (lam j ^ t * Psi i j - lam j ^ t * Psi k j) ^ 2) := by
  rw [diffusion_power_eq P Psi lam piw heig horth t]
  set a : n -> Real := fun j => lam j ^ t * Psi i j - lam j ^ t * Psi k j with ha
  set w : n -> Real := Matrix.mulVec Psi a with hw
  have hentry : forall x u,
      (Psi * Matrix.diagonal (fun j => lam j ^ t) * Psi.transpose * Matrix.diagonal piw) x u
        = Finset.sum Finset.univ (fun j => Psi x j * lam j ^ t * Psi u j) * piw u := by
    intro x u
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  have hdiff : forall u,
      (Psi * Matrix.diagonal (fun j => lam j ^ t) * Psi.transpose * Matrix.diagonal piw) i u
        - (Psi * Matrix.diagonal (fun j => lam j ^ t) * Psi.transpose * Matrix.diagonal piw) k u
        = piw u * w u := by
    intro u
    rw [hentry, hentry, <- sub_mul, <- Finset.sum_sub_distrib, mul_comm _ (piw u)]
    congr 1
    simp only [hw, ha, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  simp only [hdiff]
  have hsq : forall u, (piw u * w u) ^ 2 / piw u = w u * (piw u * w u) := by
    intro u
    have := (hpi u).ne'
    field_simp
  simp only [hsq]
  have hq : dotProduct w (Matrix.mulVec (Matrix.diagonal piw) w) = dotProduct a a := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, <- Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul, <- Matrix.mul_assoc, horth, Matrix.vecMul_one]
  have hl : Finset.sum Finset.univ (fun u => w u * (piw u * w u))
      = dotProduct w (Matrix.mulVec (Matrix.diagonal piw) w) := by
    simp [dotProduct, Matrix.mulVec_diagonal]
  rw [hl, hq]
  simp only [dotProduct, sq, ha]

/-! ## 23. QUANTUM_REAL_MATRIX_EMBEDDING (Hoffreumon-Woods 2025, eqs. 4-5) -/

/-- `Gamma(X) = [[Re X, -Im X], [Im X, Re X]]`. -/
def realEmbed (X : Matrix n n Complex) : Matrix (Sum n n) (Sum n n) Real :=
  Matrix.fromBlocks (X.map Complex.re) (-(X.map Complex.im)) (X.map Complex.im)
    (X.map Complex.re)

/-- `J_n = [[0, -I_n], [I_n, 0]]`. -/
def realJ : Matrix (Sum n n) (Sum n n) Real := Matrix.fromBlocks 0 (-1) 1 0

omit [Fintype n] [DecidableEq n] in
/-- The registry form `Gamma(A + i B) = [[A, -B], [B, A]]` for real A, B. -/
theorem realEmbed_re_im (A B : Matrix n n Real) :
    realEmbed (A.map (fun x => (x : Complex))
        + HSMul.hSMul Complex.I (B.map (fun x => (x : Complex))))
      = Matrix.fromBlocks A (-B) B A := by
  unfold realEmbed
  congr 1 <;> ext i j <;> simp

omit [DecidableEq n] in
theorem map_re_mul (X Y : Matrix n n Complex) :
    (X * Y).map Complex.re
      = X.map Complex.re * Y.map Complex.re - X.map Complex.im * Y.map Complex.im := by
  ext i j
  simp [Matrix.mul_apply, Complex.re_sum, Finset.sum_sub_distrib]

omit [DecidableEq n] in
theorem map_im_mul (X Y : Matrix n n Complex) :
    (X * Y).map Complex.im
      = X.map Complex.re * Y.map Complex.im + X.map Complex.im * Y.map Complex.re := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Finset.sum_add_distrib]

omit [DecidableEq n] in
theorem realEmbed_mul (X Y : Matrix n n Complex) :
    realEmbed (X * Y) = realEmbed X * realEmbed Y := by
  simp only [realEmbed, Matrix.fromBlocks_multiply, map_re_mul, map_im_mul]
  congr 1 <;> first | noncomm_ring | abel

omit [Fintype n] [DecidableEq n] in
theorem realEmbed_add (X Y : Matrix n n Complex) :
    realEmbed (X + Y) = realEmbed X + realEmbed Y := by
  simp only [realEmbed, Matrix.fromBlocks_add]
  congr 1
  ext i j
  simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.map_apply, Complex.add_im]
  ring

omit [Fintype n] in
theorem realEmbed_one : realEmbed (1 : Matrix n n Complex) = 1 := by
  rw [<- Matrix.fromBlocks_one]
  unfold realEmbed
  congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [Matrix.one_apply, h]

omit [Fintype n] in
/-- The imaginary unit maps to J. -/
theorem realEmbed_I :
    realEmbed (HSMul.hSMul Complex.I (1 : Matrix n n Complex)) = realJ := by
  unfold realEmbed realJ
  congr 1 <;> ext i j <;> by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem realJ_mul_self : (realJ : Matrix (Sum n n) (Sum n n) Real) * realJ = -1 := by
  rw [realJ, Matrix.fromBlocks_multiply, <- Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

omit [Fintype n] [DecidableEq n] in
/-- Adjoint maps to transpose. -/
theorem realEmbed_conjTranspose (X : Matrix n n Complex) :
    realEmbed X.conjTranspose = (realEmbed X).transpose := by
  simp only [realEmbed, Matrix.fromBlocks_transpose]
  congr 1
  ext i j
  simp [Matrix.conjTranspose_apply]

/-- Gamma commutes with J (complex-linearity in real form). -/
theorem realEmbed_mul_realJ (X : Matrix n n Complex) :
    realEmbed X * realJ = realJ * realEmbed X := by
  simp [realEmbed, realJ, Matrix.fromBlocks_multiply]

omit [Fintype n] [DecidableEq n] in
theorem realEmbed_injective : Function.Injective (realEmbed (n := n)) := by
  intro X Y h
  simp only [realEmbed, Matrix.fromBlocks_inj] at h
  ext i j
  apply Complex.ext
  next =>
    exact congrFun (congrFun h.1 i) j
  next =>
    exact congrFun (congrFun h.2.2.1 i) j

end Matrices

/-! ## 24. AMPLITUDE_BCFW_CROSSING (Dixon 2013, eq. 5.13) -/

/-- A momentum bispinor `p_{a adot} = lambda_a tilde_lambda_adot`. -/
def spinorMomentum (lam lamt : Fin 2 -> Complex) : Matrix (Fin 2) (Fin 2) Complex :=
  Matrix.vecMulVec lam lamt

/-- Such a momentum is null: det p = 0. -/
theorem spinorMomentum_det (lam lamt : Fin 2 -> Complex) :
    (spinorMomentum lam lamt).det = 0 := by
  simp [spinorMomentum, Matrix.det_fin_two, Matrix.vecMulVec_apply]
  ring

/-- AMPLITUDE_BCFW_CROSSING: `lambda(-P) = i lambda(P)`,
`tilde_lambda(-P) = i tilde_lambda(P)` is a spinor decomposition of -P. -/
theorem bcfw_crossing (lam lamt : Fin 2 -> Complex) :
    spinorMomentum (HSMul.hSMul Complex.I lam) (HSMul.hSMul Complex.I lamt)
      = -spinorMomentum lam lamt := by
  ext a b
  simp only [spinorMomentum, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.neg_apply]
  linear_combination (lam a * lamt b) * Complex.I_sq

/-- The rule is a convention: rescaling `(s lambda, s^-1 tilde_lambda)` gives
the same momentum, so `(-lambda, tilde_lambda)` is an equally valid choice. -/
theorem spinorMomentum_littleGroup (lam lamt : Fin 2 -> Complex) {s : Complex}
    (hs : Ne s 0) :
    spinorMomentum (HSMul.hSMul s lam) (HSMul.hSMul (Inv.inv s) lamt)
      = spinorMomentum lam lamt := by
  ext a b
  simp only [spinorMomentum, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem bcfw_crossing_alt (lam lamt : Fin 2 -> Complex) :
    spinorMomentum (-lam) lamt = -spinorMomentum lam lamt := by
  ext a b
  simp [spinorMomentum, Matrix.vecMulVec_apply]

end GCC
