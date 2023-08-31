import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DrelaxedAutoImplicit=false"
]

package «lean-math-workshop» {
  -- add any package configuration options here
  -- moreLeanArgs := moreLeanArgs
  moreServerArgs := moreServerArgs
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @"23550c1e3b21f7f3312acb901cef261f51219f72"

@[default_target]
lean_lib «Tutorial» {
  -- add any library configuration options here
  -- moreLeanArgs := moreLeanArgs
}