/-
# Generator Coordinate Calculus (GCC) — formal core
# Lean 4, Std only (core only — no Mathlib required)

This file formalizes the salvageable kernel of the φ-framework / non-Newtonian
calculus project, per the April 2026 verdict: "a calculus of coordinate
choices," not φ-worship.

What is PROVED here (no proof placeholders anywhere):

  1. TRANSPORT      — Every generator (bijection onto a commutative ring)
                      induces a full ring structure on its domain. The
                      "generated arithmetic" of Grossman–Katz exists for
                      *every* generator. (§2)
  2. THE RAZOR      — The generator is a ring isomorphism between the
                      generated structure and the base. Conjugation cannot
                      create content: every generated identity is the image
                      of a classical one. (§3)
  3. DISCRETE FTC   — The fundamental theorem of discrete g-calculus:
                      the g-sum of g-differences telescopes. Proved once,
                      for all generators simultaneously. (§4)
  4. STRAIGHT LINES — A sequence has constant g-derivative iff its image
                      under g is an arithmetic progression. Instantiated at
                      g = log this is "geometric sequences are the straight
                      lines of geometric calculus." (§4)
  5. φ-DEMOTION     — Kolmogorov–Nagumo direction: re-coordinatizing a
                      generator by any mean-compatible automorphism leaves
                      the quasi-arithmetic mean unchanged. Operation-wise
                      invariance is separately certified by `RingAuto`, so
                      log-base changes cannot smuggle in multiplication claims.
                      φ ∈ Γ, not φ = source code. (§5, §5b)
  6. PARETO         — Any minimizer of a positive-weight scalarization is
                      Pareto-optimal — and the converse fails in general,
                      which is why MetaSearch must return the frontier, not
                      an argmin. (§6)

What is deliberately NOT claimed: anything analytic (limits, ℝ, measure)
— that needs Mathlib (`Equiv`, `CommRing`, `deriv`); porting notes at the end.
-/

namespace GCC

/-! ## §1  Generators

A generator is a bijection `g : α ≃ β` between a carrier `α` (raw
observations) and a base `β` (the coordinate system where structure lives).
This is Grossman–Katz's "generator," Jane Grossman's α/β maps, and the
`g ∈ Γ` of the GCC search loop — one object. -/

/-- A coordinate generator: a bijection from carrier `α` onto base `β`. -/
structure Gen (α β : Type) where
  to   : α → β
  inv  : β → α
  linv : ∀ a, inv (to a) = a
  rinv : ∀ b, to (inv b) = b

variable {α β : Type}

/-- Minimal commutative-ring axioms. Core Lean has no algebra hierarchy,
so we state exactly what we use. (In Mathlib this is `CommRing`.) -/
class CRing (β : Type) extends Add β, Mul β, Neg β where
  zero : β
  one  : β
  add_assoc    : ∀ a b c : β, a + b + c = a + (b + c)
  add_comm     : ∀ a b : β, a + b = b + a
  zero_add     : ∀ a : β, zero + a = a
  add_neg      : ∀ a : β, a + -a = zero
  mul_assoc    : ∀ a b c : β, a * b * c = a * (b * c)
  mul_comm     : ∀ a b : β, a * b = b * a
  one_mul      : ∀ a : β, one * a = a
  left_distrib : ∀ a b c : β, a * (b + c) = a * b + a * c

section RingLemmas
variable [CRing β]

theorem neg_add_cancel (a : β) : -a + a = CRing.zero := by
  rw [CRing.add_comm]; exact CRing.add_neg a

theorem add_zero' (a : β) : a + CRing.zero = a := by
  rw [CRing.add_comm]; exact CRing.zero_add a

/-- Right cancellation by the additive inverse: `(a+b)-a=b`. -/
theorem add_right_neg_cancel (a b : β) : (a + b) + -a = b := by
  rw [CRing.add_comm a b, CRing.add_assoc, CRing.add_neg, add_zero']

/-- Telescoping shuffle: `(b - a) + (c - b) = c - a`, spelled with `+ -`. -/
theorem shuffle (a b c : β) : (b + -a) + (c + -b) = c + -a := by
  rw [CRing.add_comm b (-a), CRing.add_assoc,
      CRing.add_comm c (-b), ← CRing.add_assoc b (-b) c,
      CRing.add_neg, CRing.zero_add, CRing.add_comm (-a) c]

end RingLemmas

/-! ## §2  Generated arithmetic (transport of structure)

Pull the base operations back through the generator. This is the entire
mechanical content of "non-Newtonian arithmetic": `x ⊕ y = g⁻¹(g x + g y)`. -/

def gadd  (g : Gen α β) [CRing β] (x y : α) : α := g.inv (g.to x + g.to y)
def gmul  (g : Gen α β) [CRing β] (x y : α) : α := g.inv (g.to x * g.to y)
def gneg  (g : Gen α β) [CRing β] (x : α)   : α := g.inv (-(g.to x))
def gsub  (g : Gen α β) [CRing β] (x y : α) : α := g.inv (g.to x + -(g.to y))
def gzero (g : Gen α β) [CRing β] : α := g.inv CRing.zero
def gone  (g : Gen α β) [CRing β] : α := g.inv CRing.one

/-- TRANSPORT: generated addition is commutative … -/
theorem gadd_comm (g : Gen α β) [CRing β] (x y : α) :
    gadd g x y = gadd g y x := by
  unfold gadd; rw [CRing.add_comm]

/-- … and associative … -/
theorem gadd_assoc (g : Gen α β) [CRing β] (x y z : α) :
    gadd g (gadd g x y) z = gadd g x (gadd g y z) := by
  unfold gadd; rw [g.rinv, g.rinv, CRing.add_assoc]

/-- … with identity `gzero` … -/
theorem gzero_add (g : Gen α β) [CRing β] (x : α) :
    gadd g (gzero g) x = x := by
  unfold gadd gzero; rw [g.rinv, CRing.zero_add, g.linv]

/-- … and inverses. -/
theorem gadd_neg (g : Gen α β) [CRing β] (x : α) :
    gadd g x (gneg g x) = gzero g := by
  unfold gadd gneg gzero; rw [g.rinv, CRing.add_neg]

/-- Generated multiplication is commutative … -/
theorem gmul_comm (g : Gen α β) [CRing β] (x y : α) :
    gmul g x y = gmul g y x := by
  unfold gmul; rw [CRing.mul_comm]

/-- … associative … -/
theorem gmul_assoc (g : Gen α β) [CRing β] (x y z : α) :
    gmul g (gmul g x y) z = gmul g x (gmul g y z) := by
  unfold gmul; rw [g.rinv, g.rinv, CRing.mul_assoc]

/-- … unital … -/
theorem gone_mul (g : Gen α β) [CRing β] (x : α) :
    gmul g (gone g) x = x := by
  unfold gmul gone; rw [g.rinv, CRing.one_mul, g.linv]

/-- … and distributes over generated addition. The whole ring transports. -/
theorem gmul_gadd (g : Gen α β) [CRing β] (x y z : α) :
    gmul g x (gadd g y z) = gadd g (gmul g x y) (gmul g x z) := by
  unfold gmul gadd; rw [g.rinv, g.rinv, g.rinv, CRing.left_distrib]

/-! ## §3  The Razor

`g.to` is a ring isomorphism from the generated structure to the base.
Consequence: a statement provable in g-coordinates is provable in base
coordinates and vice versa. Generator-dependent claims are convention;
only conjugation-invariants are content. This is the theorem the
March-2025 φ-papers were missing: it is *why* "predictions" obtained by
rewriting RG flow in base-φ logarithms were empty. -/

theorem razor_add (g : Gen α β) [CRing β] (x y : α) :
    g.to (gadd g x y) = g.to x + g.to y := by
  unfold gadd; exact g.rinv _

theorem razor_mul (g : Gen α β) [CRing β] (x y : α) :
    g.to (gmul g x y) = g.to x * g.to y := by
  unfold gmul; exact g.rinv _

theorem razor_zero (g : Gen α β) [CRing β] :
    g.to (gzero g) = CRing.zero := by
  unfold gzero; exact g.rinv _

theorem razor_one (g : Gen α β) [CRing β] :
    g.to (gone g) = CRing.one := by
  unfold gone; exact g.rinv _

/-! ## §4  Discrete non-Newtonian calculus

Sequences `f : Nat → α`. The g-derivative is the generated difference of
successive terms; the g-integral is the generated running sum. Both are
conjugations of the classical operators, so the Fundamental Theorem is
proved once for *all* generators — including every member of Γ that the
GCC search loop will ever try. -/

/-- Discrete g-derivative: `Δ_g f n = f(n+1) ⊖_g f(n)`. -/
def gdiff (g : Gen α β) [CRing β] (f : Nat → α) (n : Nat) : α :=
  gsub g (f (n + 1)) (f n)

/-- Discrete g-integral: generated running sum. -/
def gsum (g : Gen α β) [CRing β] (f : Nat → α) : Nat → α
  | 0     => g.inv CRing.zero
  | n + 1 => gadd g (gsum g f n) (f n)

theorem gsum_zero (g : Gen α β) [CRing β] (f : Nat → α) :
    gsum g f 0 = g.inv CRing.zero := rfl

theorem gsum_succ (g : Gen α β) [CRing β] (f : Nat → α) (n : Nat) :
    gsum g f (n + 1) = gadd g (gsum g f n) (f n) := rfl

/-- FUNDAMENTAL THEOREM of discrete g-calculus:
the g-sum of the g-derivative telescopes to a g-difference of endpoints.
At `g = id` this is the classical discrete FTC; at `g = log` it is the
fundamental theorem of geometric (multiplicative) calculus: the product
of ratios telescopes. One proof, every calculus. -/
theorem gFTC (g : Gen α β) [CRing β] (f : Nat → α) (n : Nat) :
    gsum g (gdiff g f) n = gsub g (f n) (f 0) := by
  induction n with
  | zero =>
    show g.inv CRing.zero = gsub g (f 0) (f 0)
    unfold gsub
    rw [CRing.add_neg]
  | succ n ih =>
    rw [gsum_succ, ih]
    unfold gadd gdiff gsub
    rw [g.rinv, g.rinv, shuffle]

/-- Arithmetic progression in the base: `aprog b c n = b + n·c`. -/
def aprog [CRing β] (b c : β) : Nat → β
  | 0     => b
  | n + 1 => aprog b c n + c

theorem aprog_succ [CRing β] (b c : β) (n : Nat) :
    aprog b c (n + 1) = aprog b c n + c := rfl

/-- STRAIGHT LINES: if a sequence has constant g-derivative `c`, then its
image under `g` is an arithmetic progression with common difference `c`.

Instantiations (comments, since they need ℝ):
  · g = id  : constant difference  ⇒ arithmetic sequence (classical lines)
  · g = log : constant *ratio*     ⇒ geometric sequence — "exponentials are
              the straight lines of geometric calculus," the engine behind
              log-coordinate law recovery in the GCC harness. -/
theorem const_gdiff (g : Gen α β) [CRing β] (f : Nat → α) (c : β)
    (h : ∀ n, gdiff g f n = g.inv c) :
    ∀ n, g.to (f n) = aprog (g.to (f 0)) c n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have key : g.to (f (n + 1)) + -(g.to (f n)) = c := by
      have h2 := congrArg g.to (h n)
      unfold gdiff gsub at h2
      rw [g.rinv, g.rinv] at h2
      exact h2
    have h3 : (g.to (f (n + 1)) + -(g.to (f n))) + g.to (f n)
            = c + g.to (f n) := by rw [key]
    rw [CRing.add_assoc, neg_add_cancel, add_zero'] at h3
    rw [aprog_succ, ← ih, h3, CRing.add_comm]

/-- Converse straight-line theorem: if the image under `g` is an arithmetic
progression with difference `c`, then the discrete g-derivative is constant. -/
theorem aprog_const_gdiff (g : Gen α β) [CRing β] (f : Nat → α) (c : β)
    (h : ∀ n, g.to (f n) = aprog (g.to (f 0)) c n) :
    ∀ n, gdiff g f n = g.inv c := by
  intro n
  unfold gdiff gsub
  rw [h (n + 1), h n, aprog_succ, add_right_neg_cancel]

/-- STRAIGHT LINES, exact iff form: constant g-derivative is equivalent to
being an arithmetic progression after applying the generator. -/
theorem const_gdiff_iff (g : Gen α β) [CRing β] (f : Nat → α) (c : β) :
    (∀ n, gdiff g f n = g.inv c)
      ↔
    (∀ n, g.to (f n) = aprog (g.to (f 0)) c n) := by
  constructor
  · exact const_gdiff g f c
  · exact aprog_const_gdiff g f c

/-! ## §5  Quasi-arithmetic means and the φ-demotion theorem

A generated mean is `M_g(x,y) = g⁻¹(m(g x, g y))` for a base mean `m`.
The Kolmogorov–Nagumo question: when do two generators give the same mean?
Answer (one direction, proved): whenever they differ by an automorphism of
the base that commutes with `m`. For the midpoint mean, those automorphisms
are exactly the affine maps `t ↦ p·t + q` — so an exponential generator's
base is unobservable: `log_φ` and `log_e` differ by the linear map
`t ↦ t / ln φ`, hence induce the *same* geometric mean and the same
generated calculus up to isomorphism. φ demoted, formally. -/

/-- A base mean: idempotent and symmetric. -/
structure BMean (β : Type) where
  m    : β → β → β
  idem : ∀ a, m a a = a
  comm : ∀ a b, m a b = m b a

/-- Quasi-arithmetic (generated) mean. -/
def gmean (g : Gen α β) (M : BMean β) (x y : α) : α :=
  g.inv (M.m (g.to x) (g.to y))

theorem gmean_idem (g : Gen α β) (M : BMean β) (x : α) :
    gmean g M x x = x := by
  unfold gmean; rw [M.idem, g.linv]

theorem gmean_comm (g : Gen α β) (M : BMean β) (x y : α) :
    gmean g M x y = gmean g M y x := by
  unfold gmean; rw [M.comm]

/-- An automorphism of the base compatible with the mean `M`.
For `M = midpoint` over ℝ these are exactly the affine maps. -/
structure MeanAuto (β : Type) (M : BMean β) where
  φ      : β → β
  ψ      : β → β
  linv   : ∀ b, ψ (φ b) = b
  rinv   : ∀ b, φ (ψ b) = b
  compat : ∀ a b, M.m (φ a) (φ b) = φ (M.m a b)

/-- Re-coordinatize a generator by post-composing with an automorphism. -/
def recoord {M : BMean β} (g : Gen α β) (e : MeanAuto β M) : Gen α β where
  to   := fun a => e.φ (g.to a)
  inv  := fun b => g.inv (e.ψ b)
  linv := by
    intro a
    show g.inv (e.ψ (e.φ (g.to a))) = a
    rw [e.linv, g.linv]
  rinv := by
    intro b
    show e.φ (g.to (g.inv (e.ψ b))) = b
    rw [g.rinv, e.rinv]

/-- φ-DEMOTION (Kolmogorov–Nagumo direction): mean-compatible
re-coordinatization of the generator does not change the generated mean.
The "choice of φ" in any generator family related to another by such an
automorphism is convention, not content. -/
theorem gmean_recoord {M : BMean β} (g : Gen α β) (e : MeanAuto β M)
    (x y : α) : gmean (recoord g e) M x y = gmean g M x y := by
  show g.inv (e.ψ (M.m (e.φ (g.to x)) (e.φ (g.to y))))
     = g.inv (M.m (g.to x) (g.to y))
  rw [e.compat, e.linv]

/-! ### §5b  Operation-compatible re-coordinatization

Mean invariance is not ring invariance.  A post-coordinate change may preserve
one selected mean while failing to preserve multiplication, zero, one, or
negation.  This section makes the precision layer explicit: operation-wise
invariance is certified only when the re-coordinatization is compatible with
that operation.

This is the formal version of the log-base caveat: changing log base by a
nonzero scalar preserves additive-coordinate calculus and midpoint generated
means, but it is not automatically invisible for every transported ring
operation unless the coordinate change is a ring automorphism of the base.
-/

/-- An automorphism of the base compatible with the ring operations used by
`CRing`.  This is stronger than `MeanAuto`: it certifies operation-wise
invariance of generated arithmetic under re-coordinatization. -/
structure RingAuto (β : Type) [CRing β] where
  φ        : β → β
  ψ        : β → β
  linv     : ∀ b, ψ (φ b) = b
  rinv     : ∀ b, φ (ψ b) = b
  map_add  : ∀ a b, φ (a + b) = φ a + φ b
  map_mul  : ∀ a b, φ (a * b) = φ a * φ b
  map_neg  : ∀ a, φ (-a) = -(φ a)
  map_zero : φ CRing.zero = CRing.zero
  map_one  : φ CRing.one = CRing.one

/-- Re-coordinate a generator by post-composing with a ring automorphism of the
base. -/
def recoordRing (g : Gen α β) [CRing β] (r : RingAuto β) : Gen α β where
  to   := fun a => r.φ (g.to a)
  inv  := fun b => g.inv (r.ψ b)
  linv := by
    intro a
    show g.inv (r.ψ (r.φ (g.to a))) = a
    rw [r.linv, g.linv]
  rinv := by
    intro b
    show r.φ (g.to (g.inv (r.ψ b))) = b
    rw [g.rinv, r.rinv]

/-- Operation-wise invariance certificate for generated addition. -/
theorem gadd_recoordRing (g : Gen α β) [CRing β] (r : RingAuto β) (x y : α) :
    gadd (recoordRing g r) x y = gadd g x y := by
  unfold gadd recoordRing
  change g.inv (r.ψ (r.φ (g.to x) + r.φ (g.to y))) = g.inv (g.to x + g.to y)
  rw [← r.map_add, r.linv]

/-- Operation-wise invariance certificate for generated multiplication. -/
theorem gmul_recoordRing (g : Gen α β) [CRing β] (r : RingAuto β) (x y : α) :
    gmul (recoordRing g r) x y = gmul g x y := by
  unfold gmul recoordRing
  change g.inv (r.ψ (r.φ (g.to x) * r.φ (g.to y))) = g.inv (g.to x * g.to y)
  rw [← r.map_mul, r.linv]

/-- Operation-wise invariance certificate for generated negation. -/
theorem gneg_recoordRing (g : Gen α β) [CRing β] (r : RingAuto β) (x : α) :
    gneg (recoordRing g r) x = gneg g x := by
  unfold gneg recoordRing
  change g.inv (r.ψ (-(r.φ (g.to x)))) = g.inv (-(g.to x))
  rw [← r.map_neg, r.linv]

/-- Operation-wise invariance certificate for generated subtraction. -/
theorem gsub_recoordRing (g : Gen α β) [CRing β] (r : RingAuto β) (x y : α) :
    gsub (recoordRing g r) x y = gsub g x y := by
  unfold gsub recoordRing
  change g.inv (r.ψ (r.φ (g.to x) + -(r.φ (g.to y)))) = g.inv (g.to x + -(g.to y))
  rw [← r.map_neg, ← r.map_add, r.linv]

/-- Operation-wise invariance certificate for generated zero. -/
theorem gzero_recoordRing (g : Gen α β) [CRing β] (r : RingAuto β) :
    gzero (recoordRing g r) = gzero g := by
  unfold gzero recoordRing
  change g.inv (r.ψ CRing.zero) = g.inv CRing.zero
  rw [← r.map_zero, r.linv, r.map_zero]

/-- Operation-wise invariance certificate for generated one. -/
theorem gone_recoordRing (g : Gen α β) [CRing β] (r : RingAuto β) :
    gone (recoordRing g r) = gone g := by
  unfold gone recoordRing
  change g.inv (r.ψ CRing.one) = g.inv CRing.one
  rw [← r.map_one, r.linv, r.map_one]

/-! ## §6  Scalarization vs the Pareto frontier

The MetaSearch critique, formalized. Scores in ℕ (think: discretized
error / complexity / instability). A positive-weight scalar minimum is
always Pareto-optimal — so scalarization is *sound*. It is not *complete*:
Pareto points in non-convex regions of the frontier are unreachable by any
weights. The small three-point counterexample below formalizes
the incompleteness side. Hence: return the frontier, log the regime choice. -/

variable {σ : Type}

/-- `y` dominates `x`: at least as good on both objectives, strictly
better on one. -/
def Dominates (f₁ f₂ : σ → Nat) (y x : σ) : Prop :=
  f₁ y ≤ f₁ x ∧ f₂ y ≤ f₂ x ∧ (f₁ y < f₁ x ∨ f₂ y < f₂ x)

/-- Weighted scalarization of two objectives. -/
def scalarize (w₁ w₂ : Nat) (f₁ f₂ : σ → Nat) (x : σ) : Nat :=
  w₁ * f₁ x + w₂ * f₂ x

theorem mul_le_mul_left' (k : Nat) {a b : Nat} (h : a ≤ b) :
    k * a ≤ k * b :=
  Nat.mul_le_mul (Nat.le_refl k) h

theorem mul_lt_mul_left' {k a b : Nat} (hk : 0 < k) (h : a < b) :
    k * a < k * b := by
  -- a < b is definitionally a + 1 ≤ b over Nat
  have h1 : k * (a + 1) ≤ k * b := Nat.mul_le_mul (Nat.le_refl k) h
  have h2 : k * a + k ≤ k * b := by
    have e : k * (a + 1) = k * a + k := Nat.mul_succ k a
    rw [← e]; exact h1
  have h3 : k * a < k * a + k := by
    have x := Nat.add_lt_add_left hk (k * a)
    rw [Nat.add_zero] at x
    exact x
  exact Nat.lt_of_lt_of_le h3 h2

/-- SOUNDNESS OF SCALARIZATION: a minimizer of any positive-weight
scalarization is Pareto-optimal (no point dominates it). -/
theorem scalarized_min_is_pareto {f₁ f₂ : σ → Nat} {w₁ w₂ : Nat}
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) {x : σ}
    (hmin : ∀ y, scalarize w₁ w₂ f₁ f₂ x ≤ scalarize w₁ w₂ f₁ f₂ y) :
    ¬ ∃ y, Dominates f₁ f₂ y x := by
  intro hex
  cases hex with
  | intro y hdom =>
    have hle₁ := hdom.1
    have hle₂ := hdom.2.1
    have hstrict := hdom.2.2
    have hy := hmin y
    unfold scalarize at hy
    have c₁ : w₁ * f₁ y ≤ w₁ * f₁ x := mul_le_mul_left' w₁ hle₁
    have c₂ : w₂ * f₂ y ≤ w₂ * f₂ x := mul_le_mul_left' w₂ hle₂
    cases hstrict with
    | inl h =>
      have s : w₁ * f₁ y < w₁ * f₁ x := mul_lt_mul_left' hw₁ h
      have t1 : w₁ * f₁ y + w₂ * f₂ y < w₁ * f₁ x + w₂ * f₂ y :=
        Nat.add_lt_add_right s (w₂ * f₂ y)
      have t2 : w₁ * f₁ x + w₂ * f₂ y ≤ w₁ * f₁ x + w₂ * f₂ x :=
        Nat.add_le_add_left c₂ (w₁ * f₁ x)
      exact Nat.lt_irrefl _
        (Nat.lt_of_le_of_lt hy (Nat.lt_of_lt_of_le t1 t2))
    | inr h =>
      have s : w₂ * f₂ y < w₂ * f₂ x := mul_lt_mul_left' hw₂ h
      have t1 : w₁ * f₁ y + w₂ * f₂ y ≤ w₁ * f₁ x + w₂ * f₂ y :=
        Nat.add_le_add_right c₁ (w₂ * f₂ y)
      have t2 : w₁ * f₁ x + w₂ * f₂ y < w₁ * f₁ x + w₂ * f₂ x :=
        Nat.add_lt_add_left s (w₁ * f₁ x)
      exact Nat.lt_irrefl _
        (Nat.lt_of_le_of_lt hy (Nat.lt_of_le_of_lt t1 t2))

/-! ### A finite counterexample: Pareto-optimal does not imply scalarized-minimal. -/

inductive Triad where
  | left
  | middle
  | right
  deriving DecidableEq, Repr

open Triad

def bad_f₁ : Triad → Nat
  | left   => 0
  | middle => 60
  | right  => 100

def bad_f₂ : Triad → Nat
  | left   => 100
  | middle => 60
  | right  => 0

/-- The middle point `(60,60)` is Pareto-optimal among
`(0,100), (60,60), (100,0)`. -/
theorem middle_pareto : ¬ ∃ y, Dominates bad_f₁ bad_f₂ y middle := by
  intro h
  cases h with
  | intro y hdom =>
    cases y <;> simp [Dominates, bad_f₁, bad_f₂] at hdom

/-- But no positive-weight linear scalarization can select that middle point.
This is the formal reason MetaSearch must expose a frontier rather than a
single weighted argmin. -/
theorem middle_not_scalar_min {w₁ w₂ : Nat}
    (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    ¬ (∀ y, scalarize w₁ w₂ bad_f₁ bad_f₂ middle
          ≤ scalarize w₁ w₂ bad_f₁ bad_f₂ y) := by
  intro hmin
  have hL := hmin left
  have hR := hmin right
  simp only [scalarize, bad_f₁, bad_f₂] at hL hR
  omega

/-! ## §7  Executable demos (sanity, not proof) -/

/-- A shift generator over ℤ: coordinates offset by `c`
(Celsius/Fahrenheit-style recoordinatization). -/
def shift (c : Int) : Gen Int Int where
  to   := fun a => a + c
  inv  := fun b => b - c
  linv := by intro a; show a + c - c = a; omega
  rinv := by intro b; show b - c + c = b; omega

instance : CRing Int where
  toAdd := inferInstance
  toMul := inferInstance
  toNeg := inferInstance
  zero  := 0
  one   := 1
  add_assoc    := by intro a b c; omega
  add_comm     := by intro a b; omega
  zero_add     := by intro a; omega
  add_neg      := by intro a; omega
  mul_assoc    := Int.mul_assoc
  mul_comm     := Int.mul_comm
  one_mul      := Int.one_mul
  left_distrib := Int.mul_add

-- Shift-generated addition: g⁻¹(g 10 + g 20) with g = (·+5) gives 35.
#eval gadd (shift 5) 10 20        -- expected: 35
#eval gzero (shift 5)             -- expected: -5  (the generated zero!)
#eval gadd (shift 5) 10 (gzero (shift 5))  -- expected: 10 (identity law, live)

/-- Geometric sequence 3·1.5ⁿ for the Float demo. -/
def geom : Nat → Float
  | 0     => 3.0
  | n + 1 => geom n * 1.5

-- Numerically: the log-generated discrete derivative of a geometric
-- sequence is constant (≈ 1.5 after exponentiating back) — the Float
-- shadow of `const_gdiff` at g = log.
#eval (List.range 5).map fun n =>
  Float.exp (Float.log (geom (n + 1)) - Float.log (geom n))

/-! ## §8  Porting notes (Mathlib) and non-claims

To upgrade this skeleton in a Mathlib project:
  · `Gen α β`            ↦ `Equiv α β` (`α ≃ β`)
  · `CRing`              ↦ `CommRing` / `Field`
  · §2–§3                ↦ `Equiv.commRing` (transport of structure is
                           one line in Mathlib; the razor is `RingEquiv`)
  · §4 analytic version  ↦ `deriv` + chain rule: the g-derivative of
                           Grossman–Katz is `g⁻¹' ∘ deriv (g ∘ f)`; the
                           continuous FTC transports along `g` exactly as
                           `gFTC` does discretely.
  · §5 full KN theorem   ↦ needs continuity/monotonicity on ℝ intervals:
                           midpoint-compatible automorphisms = affine maps
                           requires Jensen-equation machinery.
  · §5b ring layer       ↦ `RingEquiv` should replace `RingAuto`; operation-wise
                           invariance becomes transport through a ring equivalence.
  · §6 converse failure  ↦ already represented by the three-point frontier
                           counterexample above.

NON-CLAIMS, recorded so the file cannot be quoted beyond its content:
no theorem here mentions φ; no theorem asserts any generator is optimal
for physics; optimality of a generator is an *empirical* property of a
(system, score) pair — MDL-scored search, outside the prover's remit.
-/

end GCC