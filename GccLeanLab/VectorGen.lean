/-
# Golden-vector generator (plan P5)

Writes `golden_vectors.json`: Float shadows of the Lean-proved operator
semantics, for consumption by the two Python repos (meta-calculus-toolkit
and the-agent-maker). The floats are NOT the proofs - the theorems named in
the provenance field are; these vectors pin the implementations to the
proved formulas within float tolerance.

Deterministic by construction: no clock, no randomness. The executable
writes the file itself (no shell redirection, so no CRLF/UTF-16 surprises
on Windows).
-/

namespace GCC.VectorGen

/-- Float shadow of `GCC.bgTransform`: `g * |g| ^ (2k-1)`. The base is
abs-guarded like the Real version; the one Float-only edge is g = 0 with a
negative exponent (0 * inf = NaN), which the vector grids exclude - the
Real theorem `bgTransform_zero` covers g = 0 exactly. -/
def bgTransformF (k g : Float) : Float :=
  g * (Float.abs g) ^ (2.0 * k - 1.0)

/-- Float shadow of `GCC.kOf`. `Float.log10` is the IEEE 754 approximation
of `Real.logb 10` - functional form identical, values differ by rounding,
which is why consumers assert rtol tolerance, never equality. -/
def kOfF (slope intercept L : Float) : Float :=
  slope * Float.log10 L + intercept

/-- Float shadow of `GCC.signSqrt` (theorem: `signSqrtChart` round trips). -/
def signSqrtF (x : Float) : Float :=
  if 0 ≤ x then Float.sqrt x else -(Float.sqrt (-x))

def jnum (x : Float) : String := toString x

def jpair (a b : Float) : String :=
  "[" ++ jnum a ++ ", " ++ jnum b ++ "]"

def KS : List Float := [0.05, 0.1593, 0.3, 0.49]
def GS : List Float := [-4.0, -1.0, -0.001, 0.001, 1.0, 9.0]
def NS : List Float := [-2.0, -1.0, 0.5, 1.0, 3.0]
def LS : List Float := [1.0, 10.0, 100.0, 10000.0, 1000000.0]
def XS : List Float := [-10000.0, -7.0, -1.0, -0.25, 0.0, 0.25, 1.0, 7.0, 10000.0]

def bgTransformEntries : List String :=
  KS.flatMap fun k =>
    GS.map fun g =>
      "    {\"k\": " ++ jnum k ++ ", \"g\": " ++ jnum g ++
      ", \"expected\": " ++ jnum (bgTransformF k g) ++ "}"

def powerLawEntries : List String :=
  NS.map fun n =>
    "    {\"n\": " ++ jnum n ++ ", \"expected_D_BG\": " ++ jnum (Float.exp n) ++ "}"

def kOfEntries : List String :=
  LS.map fun L =>
    "    {\"L\": " ++ jnum L ++ ", \"expected_k\": " ++
    jnum (kOfF (-0.0137) 0.1593 L) ++ "}"

def signSqrtEntries : List String :=
  XS.map fun x =>
    "    {\"x\": " ++ jnum x ++ ", \"expected\": " ++ jnum (signSqrtF x) ++
    ", \"round_trip\": " ++ jnum x ++ "}"

/-- F007 specialization triples: (family, point, expected value), per the
theorems f007_classical (f = t^2 -> 2a), f007_geometric (f = exp(2t) -> 2),
f007_bigeometric (f = t^3 on t>0 -> 3). -/
def f007Entries : List String :=
  let pts : List Float := [0.5, 1.0, 2.0, 3.0]
  (pts.map fun a =>
    "    {\"family\": \"classical_t_squared\", \"a\": " ++ jnum a ++
    ", \"expected\": " ++ jnum (2.0 * a) ++ "}") ++
  (pts.map fun a =>
    "    {\"family\": \"geometric_exp2t\", \"a\": " ++ jnum a ++
    ", \"expected\": " ++ jnum 2.0 ++ "}") ++
  (pts.map fun a =>
    "    {\"family\": \"bigeometric_t_cubed\", \"a\": " ++ jnum a ++
    ", \"expected\": " ++ jnum 3.0 ++ "}")

def jarr (entries : List String) : String :=
  "[\n" ++ String.intercalate ",\n" entries ++ "\n  ]"

def jsonDoc : String :=
  "{\n" ++
  "  \"provenance\": \"Float shadow of Lean theorems bgTransform_contracts/abs_bgTransform/bgTransform_fixed, kOf_strictAntiOn/kOf_mem_Icc, bgDerivMul_powFlow, f007_classical/f007_geometric/f007_bigeometric, signSqrtChart (gcc-lean-lab v0.1.0+); floats are not the proofs\",\n" ++
  "  \"generator\": \"lake exe gccvectors (GccLeanLab/VectorGen.lean)\",\n" ++
  "  \"bg_transform\": " ++ jarr bgTransformEntries ++ ",\n" ++
  "  \"power_law_D_BG\": " ++ jarr powerLawEntries ++ ",\n" ++
  "  \"k_of_L\": " ++ jarr kOfEntries ++ ",\n" ++
  "  \"sign_sqrt\": " ++ jarr signSqrtEntries ++ ",\n" ++
  "  \"f007\": " ++ jarr f007Entries ++ "\n" ++
  "}\n"

end GCC.VectorGen

def main : IO Unit := do
  IO.FS.writeFile "golden_vectors.json" GCC.VectorGen.jsonDoc
  IO.println "wrote golden_vectors.json"
