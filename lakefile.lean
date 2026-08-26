import Lake

open Lake DSL

package gromovFilling

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.0"

require JordanCurveTheorem from git
  "https://github.com/epfl-lara/jordan-curve-theorem.git" @
    "e442525a662e9e3beb8205b9fa1fc99509076ded" / "HOLLight-Lean"

@[default_target]
lean_lib GromovFilling
