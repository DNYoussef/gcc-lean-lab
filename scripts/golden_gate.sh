#!/usr/bin/env bash
# golden_gate.sh - hermetic golden-vector drift gate.
# GREEN (exit 0) iff freshly generated vectors are byte-identical to the
# committed golden_vectors.json AND all canaries appear in both files.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
COMMITTED="$REPO_ROOT/golden_vectors.json"

# Locate the built generator (Linux CI vs Windows dev box).
BIN="$REPO_ROOT/.lake/build/bin/gccvectors"
[ -x "$BIN" ] || BIN="$REPO_ROOT/.lake/build/bin/gccvectors.exe"
if [ ! -x "$BIN" ]; then
  echo "GATE ERROR: gccvectors not built; run 'lake build gccvectors' first" >&2
  exit 2
fi

# Hermetic: generate in a fresh temp dir; never touch the committed file.
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
( cd "$TMP" && "$BIN" >/dev/null )
FRESH="$TMP/golden_vectors.json"
[ -f "$FRESH" ] || { echo "GATE ERROR: generator wrote no file" >&2; exit 2; }

# Canaries: exact unique values that must appear in BOTH files.
CANARIES=(
  '{"k": 0.050000, "g": -4.000000, "expected": -1.148698}'
  '{"n": 3.000000, "expected_D_BG": 20.085537}'
  '{"x": 10000.000000, "expected": 100.000000, "round_trip": 10000.000000}'
)
for c in "${CANARIES[@]}"; do
  grep -qF -- "$c" "$COMMITTED" || { echo "GATE RED: canary missing from committed file: $c" >&2; exit 1; }
  grep -qF -- "$c" "$FRESH"     || { echo "GATE RED: canary missing from fresh output: $c" >&2; exit 1; }
done

# Byte-for-byte drift check (.gitattributes pins the committed file -text).
if ! cmp -s "$COMMITTED" "$FRESH"; then
  echo "GATE RED: golden_vectors.json drifted from generator output" >&2
  diff -u "$COMMITTED" "$FRESH" | head -40 >&2 || true
  exit 1
fi

echo "GATE GREEN: golden_vectors.json matches generator output (3 canaries verified)"
