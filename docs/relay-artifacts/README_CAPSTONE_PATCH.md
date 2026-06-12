# GCC Mathlib Lab Capstone Patch

Static status: not compiled in this runtime. `lean`, `lake`, and `elan` are not installed here.

This patch applies three fixes to `GCC_Mathlib_Lab_WithAnalysis.lean`:

1. Replaces the brittle `gmean_recoord` proof that used `change` across an abstract `Equiv` inverse with a `simp`/`rw` proof that crosses the propositional inverse boundary properly.
2. Assembles the discharged sigmoid/logit obligations into `logitChart : Chart OpenUnit ℝ`, then adds `logisticLine`, `logisticLine_logitCoord`, `logisticEuler`, and `logisticEuler_mem`.
3. Connects `geometricLine` and `expFlow` with `geometricLine_eq_expFlow`, then states `logRate_geometricLine` on the canonical lab object.

Files:

- `GCC_Mathlib_Lab_Capstone.lean`: full patched lab file.
- `GCC_Lab_Capstone.patch`: unified diff against `GCC_Mathlib_Lab_WithAnalysis.lean`.

Expected external check:

```bash
lake new gcc math
cd gcc
lake exe cache get
mkdir -p Gcc
cp /path/to/GCC_Mathlib_Lab_Capstone.lean Gcc/GCC_Mathlib_Lab.lean
lake build
```

After a green build, retire/delete:

- `GCC_Mathlib_Lab_WithAnalysis.lean`
- `GCC_Analysis_Discharged.lean`
- `GCC_Analysis_Obligations.lean`

Keep one lab and one canonical core.
