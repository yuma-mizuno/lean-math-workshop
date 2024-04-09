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
  "https://github.com/Seasawher/mk-exercise.git" @ "70102f2963f5bc19aac0339d9464b72a1de2e1cb"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.7.0"

@[default_target]
lean_lib «Solution» where
  -- add any library configuration options here
  -- moreLeanArgs := moreLeanArgs
