# gcc-lean-lab — Generator Coordinate Calculus, kernel-checked

This repository does not prove that phi governs physics. It proves that
generated calculi are transported coordinate structures, and gives checked
instruments for choosing coordinates where systems simplify.

The doctrine, machine-checked: pick a chart; transport the structure; prove
what is invariant; search empirically for the chart that compresses the
phenomenon. Anything that depends on the specific generator is convention;
only conjugation-invariants are content.

## Contents

| File | What it is | How to check |
|---|---|---|
| `GCC_CanonicalCore.lean` | Zero-imports core: transport, razor, discrete FTC, straight-line iff, mean invariance, Pareto soundness + incompleteness witness. | `lean GCC_CanonicalCore.lean` (Lean >= 4.7.0; checked on 4.28.0) |
| `GccLeanLab/Capstone.lean` | Mathlib laboratory: charts as `Equiv`, log/logit chart instruments, flows, analytic log-rate theorems. | `lake build` |
| `GccLeanLab/Tests.lean` | ~45 witness examples: kernel-checked concrete instantiations of every section. | `lake build` |
| `docs/THEOREM_MAP.md` | Every theorem -> file -> meaning -> toolkit concept. | grep-verified |
| `docs/` | Verbatim transcripts of the three-model relay that produced this, responses to the first build log, retired artifacts. | - |

## Pinned versions

- Lean `4.28.0` (`lean-toolchain`)
- Mathlib `v4.28.0` (`lakefile.lean`)

## Build

```bash
# Mathlib lab + tests (first build downloads the Mathlib cache)
lake exe cache get
lake build

# Zero-imports core, instant verdict
lean GCC_CanonicalCore.lean
```

## Relationship to the meta-calculus toolkit

This repo is the formal spec layer for
`meta-calculus-toolkit` (Grossman-Katz / Czachor generated calculi in
production Python). The transported arithmetic here is Czachor's generated
arithmetic (Eq. 18, *Relativity of Arithmetic*, 2016); `gFTC` is the
discrete meta-calculus FTC (Grossman 1981). See `docs/THEOREM_MAP.md` for
the full concept map, and the toolkit's `CITATION_INDEX.md` for the
code-side equation index.

## Release

`v0.1.0-gcc-razor` — first kernel-checked release: transport, razor,
discrete FTC, quasi-mean invariance, Pareto soundness, log/logit chart lab,
and witness suite.
