import Proposal.GeometricCanonicalResidueDiagram

/-!
# Complex linearity of the actual canonical residue connecting map

Status: source-only proof draft. Compilation and independent kernel replay
are deferred at the user's request. No new axioms or admissions are used.

The scalar action is the existing action obtained by applying cohomology
to multiplication in the original module sheaves. The original scalar
endomorphism of a short complex and extension-class naturality prove the
open-set connecting identity. The final linear map has the actual
canonical residue connecting homomorphism as its underlying map.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricIntrinsicCartierCohomology

open CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar

variable {X : TopCat.{0}}

local instance :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The open-set version of the existing scalar naturality theorem for
the unchanged module short complex. -/
theorem moduleOpenConnecting_scalar
    (R : X.Sheaf CommRingCat.{0}) (c : ℂ →+* R.obj.obj (op ⊤))
    (S : ShortComplex (SheafOfModules.{0} (ringSheaf R)))
    (hS : (moduleAdditiveComplex R S).ShortExact)
    (n : ℕ) (U : Opens X) (z : ℂ)
    (x : (additiveSheaf R S.X₃).H' n U) :
    openConnecting hS n U (cohomologyScalar R c S.X₃ n U z x) =
      cohomologyScalar R c S.X₁ (n + 1) U z (openConnecting hS n U x) :=
  openConnecting_naturality hS hS (moduleScalarComplexEnd R c S z) n U x

end CycleQ2GeometricIntrinsicCartierCohomology

namespace CycleQ2CanonicalResidueScalar

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar
  CycleQ2SurfaceCechTwoScalar CycleQ2GeometricIntrinsicCartierCohomology
  CycleQ2CanonicalResidueSheaf CycleQ2CanonicalResidueDiagram

local instance :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual complex multiplication on the surface canonical sheaf,
followed by the existing cohomology functor. -/
instance canonicalCohomologyModule (n : ℕ) (U : Surface.Opens) :
    Module ℂ (canonicalResidueAdditiveComplex.X₁.H' n U) :=
  cohomologyModule Surface.sheaf (surfaceGlobalCoefficient 57 1) CanonicalForms n U

/-- The residue target retains the structure-module action of the actual
closed-immersion pushforward. -/
instance residueCohomologyModule (n : ℕ) (U : Surface.Opens) :
    Module ℂ (canonicalResidueAdditiveComplex.X₃.H' n U) :=
  cohomologyModule Surface.sheaf (surfaceGlobalCoefficient 57 1) ResidueTarget n U

theorem canonicalOpenConnecting_smul (U : Surface.Opens) (z : ℂ)
    (x : canonicalResidueAdditiveComplex.X₃.H' 1 U) :
    canonicalOpenConnecting U (z • x) = z • canonicalOpenConnecting U x :=
  moduleOpenConnecting_scalar Surface.sheaf (surfaceGlobalCoefficient 57 1)
    canonicalResidueComplex canonicalResidueAdditiveComplex_shortExact 1 U z x

/-- The fixed canonical residue connecting homomorphism, bundled with
its proved intrinsic complex linearity. -/
def canonicalOpenConnectingLinear (U : Surface.Opens) :
    canonicalResidueAdditiveComplex.X₃.H' 1 U →ₗ[ℂ]
      canonicalResidueAdditiveComplex.X₁.H' 2 U :=
  { canonicalOpenConnecting U with
    map_smul' := canonicalOpenConnecting_smul U }

@[simp] theorem canonicalOpenConnectingLinear_apply (U : Surface.Opens)
    (x : canonicalResidueAdditiveComplex.X₃.H' 1 U) :
    canonicalOpenConnectingLinear U x = canonicalOpenConnecting U x := rfl

/-- Multiplication by an actual global form is linear for the same
intrinsic scalar actions; this is the original cohomology map. -/
def formMultiplicationH2Linear (σ : GlobalForm) (U : Surface.Opens) :
    (CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf Surface).H' 2 U →ₗ[ℂ]
      canonicalResidueAdditiveComplex.X₁.H' 2 U :=
  cohomologyMapLinear Surface.sheaf (surfaceGlobalCoefficient 57 1)
    StructureModule (formMultiplication σ) 2 U

@[simp] theorem formMultiplicationH2Linear_apply (σ : GlobalForm) (U : Surface.Opens)
    (x : (CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf Surface).H' 2 U) :
    formMultiplicationH2Linear σ U x = formMultiplicationH2 σ U x := rfl

#print axioms canonicalOpenConnecting_smul
#print axioms canonicalOpenConnectingLinear
#print axioms formMultiplicationH2Linear

end CycleQ2CanonicalResidueScalar

end
