import Lake
open Lake DSL

package «CoveringSpacesProject» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib «CoveringSpacesProject»

--
-- DO NOT REPLACE WITH '@ "master"': the pace of development of mathlib is too
-- fast for us to keep up. If you need to bump the version of mathlib, change
-- the commit to a more recent one.
--
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.20.0"

meta if get_config? env = some "dev" then require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "v4.20.0"
