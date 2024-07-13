import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-DrelaxedAutoImplicit=false"
]

package «lean-math-workshop» where
  -- add any package configuration options here
  moreGlobalServerArgs := moreServerArgs

require «mk-exercise» from git
  "https://github.com/Seasawher/mk-exercise.git" @ "lean/v4.10.0-rc1"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.10.0-rc2"

@[default_target]
lean_lib «Solution» where
  -- add any library configuration options here
  -- moreLeanArgs := moreLeanArgs
