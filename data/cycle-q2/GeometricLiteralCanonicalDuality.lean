import Proposal.GeometricLiteralGlobalFunctions
import Proposal.GeometricLiteralCotangentTrace
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# The top canonical residue pairing for the literal surface

The fixed Čech residue identifies the top canonical cohomology with the
linear dual of the original global regular functions. The pairing sends
a class and a regular function to the residue of the cohomology class
after multiplication by that function on the canonical sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralCanonicalDuality

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricSurfaceCoefficients CycleQ2CanonicalCoordinateH2
  CycleQ2LiteralGlobalFunctions CycleQ2LiteralCotangentTrace

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

private def coefficientsLinear {A : Type} [CommRing A] (f : ℂ ≃+* A) :
    letI := f.toRingHom.toAlgebra
    ℂ ≃ₗ[ℂ] A :=
  letI := f.toRingHom.toAlgebra
  { f.toAddEquiv with map_smul' := fun c z => f.map_mul c z }

scoped instance globalFunctionAlgebra : Algebra ℂ Γ(Surface, ⊤) :=
  globalFunctionsEquiv.toRingHom.toAlgebra

def scalarFunctions : ℂ ≃ₗ[ℂ] Γ(Surface, ⊤) :=
  coefficientsLinear globalFunctionsEquiv

private def pairingEquiv {V : Type 1} {W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] ℂ) (f : W ≃ₗ[ℂ] ℂ) :
    V ≃ₗ[ℂ] Module.Dual ℂ W :=
  e ≪≫ₗ (LinearMap.ringLmapEquivSelf ℂ ℂ ℂ).symm ≪≫ₗ f.dualMap

private theorem pairingEquiv_apply {V : Type 1} {W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : V ≃ₗ[ℂ] ℂ) (f : W ≃ₗ[ℂ] ℂ) (x : V) (s : W) :
    pairingEquiv e f x s = f s • e x := rfl

/-- Duality between top canonical cohomology and global regular functions. -/
def canonicalDuality : CanonicalSheaf.H' 2 ⊤ ≃ₗ[ℂ] Module.Dual ℂ Γ(Surface, ⊤) :=
  pairingEquiv algebraicTraceEquiv scalarFunctions.symm

theorem canonicalDuality_apply (x : CanonicalSheaf.H' 2 ⊤) (s : Γ(Surface, ⊤)) :
    canonicalDuality x s = algebraicTrace (canonicalFunctionH2 s x) := by
  rw [canonicalDuality, pairingEquiv_apply]
  change constantCoefficient s • algebraicTrace x = _
  rw [canonicalFunctionH2_apply, map_smul]

end CycleQ2LiteralCanonicalDuality
end

#print axioms CycleQ2LiteralCanonicalDuality.canonicalDuality_apply
