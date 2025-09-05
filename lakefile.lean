import Lake
open Lake DSL

def moreServerArgs : Array LeanOption := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩
]

package «lean-math-workshop» where
  -- add any package configuration options here
  leanOptions := moreServerArgs

require "Seasawher" / "mk-exercise" @ git "main"

require "leanprover-community" / "mathlib" @ git "master"

@[default_target]
lean_lib «Solution» where
  -- add any library configuration options here
  -- moreLeanArgs := moreLeanArgs
