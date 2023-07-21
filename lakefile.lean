import Lake
open Lake DSL

def moreLeanArgs := #[
  "-Dpp.unicode.fun=true" -- pretty-prints `fun a ↦ b`
]

package «lean-math-workshop» {
  -- add any package configuration options here
  -- moreLeanArgs := moreLeanArgs
  moreServerArgs := moreLeanArgs
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @"08fc07cd8ba56396909a84a7b2361cfda8223840"

@[default_target]
lean_lib «Tutorial» {
  -- add any library configuration options here
  -- moreLeanArgs := moreLeanArgs
}