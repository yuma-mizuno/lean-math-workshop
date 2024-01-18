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
  "https://github.com/Seasawher/mk-exercise" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "afe6b29fd5ae8baf11db1d2c2921b9730d9f7ad0"

@[default_target]
lean_lib «Solution» where
  -- add any library configuration options here
  -- moreLeanArgs := moreLeanArgs
