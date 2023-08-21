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
    @"c6e395dd3bb117a6db28f2b094bc822994f7cee9"

@[default_target]
lean_lib «Tutorial» {
  -- add any library configuration options here
  -- moreLeanArgs := moreLeanArgs
}