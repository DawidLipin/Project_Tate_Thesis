import Lake
open Lake DSL

package «TateThesis» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩
  ]
  -- add any additional package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require AdeleRingLocallyCompact from git
  "https://github.com/smmercuri/adele-ring_locally-compact.git" @ "main"

@[default_target]
lean_lib «TateThesis» where
  -- add any library configuration options here
