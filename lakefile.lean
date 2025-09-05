import Lake
open Lake DSL

def moreServerArgs : Array LeanOption := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩
]

package «lean-math-workshop» where
  -- add any package configuration options here
  leanOptions := moreServerArgs

require «mk-exercise» from git
  "https://github.com/Seasawher/mk-exercise.git" @ "2.1.1"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.12.0"

@[default_target]
lean_lib «Solution» where
  -- add any library configuration options here
  -- moreLeanArgs := moreLeanArgs
