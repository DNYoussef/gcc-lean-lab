# Upstream corrections relevant to this formalization (2026-06-12)

The meta-calculus-toolkit ran its full simulation fleet and shipped
corrections (toolkit `docs/HONEST-STATUS.md`, commits `88269ec`..`3678210`).
Two are worth recording here because they bear directly on what this repo
proves.

## 1. The convergence retraction is the razor, observed numerically

Toolkit EXP-2 retracted "Bigeometric-RK4 achieves 2nd order convergence":
the scheme was central difference in disguise. Converting the bigeometric
derivative back to an additive derivative reproduces u' exactly, so the
"new" scheme was the SAME update rule written in a different chart, and
its measured order (1.99) was Central-RK4's order wearing a costume.

That is precisely the content of the razor layer in this repo
(`razor_add`/`razor_mul` in GCC_CanonicalCore.lean, the `apply_*` lemmas
in Capstone.lean): conjugation by a chart is contentless, so a
chart-transported operation can never have different invariant content
than the operation it transports. The numerical claim died for exactly
the reason the theorems say it had to. Conversely, the claims that
SURVIVED the toolkit's sweep are the ones about genuinely different
update rules, not relabelings:

- NNC shock limiter (a different flux limiter, not a chart image of an
  existing one): 9.7% L2 over superbee on Shu-Osher after the upstream
  integrator fix (its benchmark had been silently NaN), tie on Sod.
- Meta-k advection schemes (genuinely different stencils): measured order
  0.84-0.95, i.e. ~1st order - the cost side of the stability trade-off,
  now on record.

Rule of thumb this episode validates: before claiming a scheme is new,
exhibit the invariant that distinguishes it from a chart image of a known
one. `Chart := Equiv` makes the relabeling case unconstructible as a
novelty claim in Lean; the toolkit now enforces the same by making
`_deriv_bigeometric` raise instead of posing as a distinct scheme.

## 2. Operator-layer fix upstream; spec layer here unaffected

`BigeometricDerivative.__call__` (toolkit) crashed on non-vectorized
(scalar-returning) callables via boolean indexing; it now normalizes
shapes. The Lean spec layer (`bgDeriv`/`bgDerivMul` in MetaCalculus.lean)
is shape-free mathematics and needed no change; golden vectors are
unaffected (no numeric outputs changed, only the operator's input
tolerance).

Nothing in this repo's theorem statements, golden vectors, or
EXPECTED_SHA256 pins changes as a result of the upstream sweep.
