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
  "https://github.com/leanprover-community/mathlib4.git" @ "7ca43cbd6aa34058a1afad8e47190af3ec1f9bdb"

@[default_target]
lean_lib «Solution» where
  -- add any library configuration options here
  -- moreLeanArgs := moreLeanArgs
