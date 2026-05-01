import Lake
open Lake DSL

package RedPallasFormal where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib RedPallas where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

require pasta_formal from git
  "https://github.com/oxarbitrage/pasta-formal"
