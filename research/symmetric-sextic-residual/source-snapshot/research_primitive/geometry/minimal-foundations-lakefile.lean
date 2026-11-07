/- Proposed ISOLATED build configuration. Do not replace the target lakefile.
   Static imports of the extracted closure use only OAI, preserved
   HodgeConjecture helpers, Lean, and mathlib. Not yet build-validated. -/
import Lake
open Lake DSL

package GFExternalFoundations where
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib OAI
lean_lib HodgeConjecture where
  srcDir := "ComparatorChallenges/HodgeConjectureCMAbelianVarieties"
  globs := #[.submodules `HodgeConjecture]
