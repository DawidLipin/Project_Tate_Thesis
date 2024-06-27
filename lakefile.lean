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
  "https://github.com/leanprover-community/mathlib4.git" @ "eaede86aa7777630a3826cd8f3fbf0cbaafa53e6"

require «adele-ring_locally-compact» from git
  "https://github.com/smmercuri/adele-ring_locally-compact.git" @ "be597202277bd89a9d16295e9c99bd8fec72de51"

@[default_target]
lean_lib «TateThesis» where
  -- add any library configuration options here
