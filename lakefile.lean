import Lake

open Lake DSL

package gromovFilling

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

@[default_target]
lean_lib GromovFilling
