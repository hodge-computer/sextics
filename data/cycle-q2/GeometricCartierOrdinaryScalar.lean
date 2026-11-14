import Proposal.GeometricCartierCohomologyScalar

section

/-!
# The same intrinsic scalars in ordinary derived cohomology

Ordinary cohomology acts on a genuine scalar sheaf endomorphism using
`Sheaf.H.map`. Naturality of the existing terminal-source isomorphism
identifies this action with the intrinsic action on H-prime at the top open.
The actual surface comparison therefore has exactly the same canonical
underlying map in ordinary H-two.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CechTwoOrdinaryScalar
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  Opposite TopologicalSpace CycleQ2InjectiveCech CycleQ2CechTwoComparison
  CycleQ2CechTwoScalar CycleQ2SurfaceCechTwoScalar
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar
  CycleQ2GeometricSheafCohomologyRestriction

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- The existing terminal cohomology equivalence is natural for every genuine
additive-sheaf morphism, in every degree. -/
theorem terminalCohomologyEquiv_naturality {F G : AbSheaf X} (f : F ⟶ G)
    (n : ℕ) (x : F.H' n ⊤) :
    terminalCohomologyEquiv (Opens.grothendieckTopology X) G ⊤ isTerminalTop n
      (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map f).app
        (op ⊤) x) =
      Sheaf.H.map f n
        (terminalCohomologyEquiv (Opens.grothendieckTopology X) F ⊤ isTerminalTop n x) := by
  let e := (extFunctor n).mapIso
    (terminalFreeSheafIso (Opens.grothendieckTopology X) ⊤ isTerminalTop).op
  exact congrArg (fun k : AddCommGrpCat.of (F.H' n ⊤) ⟶ AddCommGrpCat.of (G.H n) => k x)
    (e.inv.naturality f)

section ModuleSheaf
variable (R : X.Sheaf CommRingCat.{0}) (c : ℂ →+* R.obj.obj (op ⊤))
  (M : SheafOfModules.{0} (ringSheaf R))

/-- Ordinary derived cohomology applies its actual functor to the genuine
scalar multiplication morphism of the original sheaf. -/
def ordinaryScalar (n : ℕ) (z : ℂ) :
    (additiveSheaf R M).H n →+ (additiveSheaf R M).H n :=
  Sheaf.H.map (scalarEnd R c M z) n

theorem ordinaryScalar_one (n : ℕ) (x : (additiveSheaf R M).H n) :
    ordinaryScalar R c M n 1 x=x := by
  change Sheaf.H.map (scalarEnd R c M 1) n x=x
  rw [scalarEnd_one, Sheaf.H.map_id_apply]

theorem ordinaryScalar_mul (n : ℕ) (a b : ℂ) (x : (additiveSheaf R M).H n) :
    ordinaryScalar R c M n (a*b) x =
      ordinaryScalar R c M n a (ordinaryScalar R c M n b x) := by
  change Sheaf.H.map (scalarEnd R c M (a*b)) n x =
    Sheaf.H.map (scalarEnd R c M a) n (Sheaf.H.map (scalarEnd R c M b) n x)
  rw [scalarEnd_mul, Sheaf.H.map_comp_apply]

theorem ordinaryScalar_add (n : ℕ) (a b : ℂ) (x : (additiveSheaf R M).H n) :
    ordinaryScalar R c M n (a+b) x =
      ordinaryScalar R c M n a x + ordinaryScalar R c M n b x := by
  change Sheaf.H.map (scalarEnd R c M (a+b)) n x =
    Sheaf.H.map (scalarEnd R c M a) n x + Sheaf.H.map (scalarEnd R c M b) n x
  rw [scalarEnd_add, Sheaf.H.map_add_apply]

theorem ordinaryScalar_zero (n : ℕ) (x : (additiveSheaf R M).H n) :
    ordinaryScalar R c M n 0 x=0 := by
  change Sheaf.H.map (scalarEnd R c M 0) n x=0
  rw [scalarEnd_zero, Sheaf.H.map_apply, Ext.mk₀_zero, Ext.comp_zero]

/-- The intrinsic complex action on ordinary derived cohomology. -/
@[instance_reducible] def ordinaryModule (n : ℕ) : Module ℂ ((additiveSheaf R M).H n) := by
  letI : SMul ℂ ((additiveSheaf R M).H n) := ⟨fun z x => ordinaryScalar R c M n z x⟩
  exact
    { smul_add := fun z x y => (ordinaryScalar R c M n z).map_add x y
      smul_zero := fun z => (ordinaryScalar R c M n z).map_zero
      add_smul := ordinaryScalar_add R c M n
      zero_smul := ordinaryScalar_zero R c M n
      mul_smul := ordinaryScalar_mul R c M n
      one_smul := ordinaryScalar_one R c M n }

theorem ordinaryModule_smul (n : ℕ) (z : ℂ) (x : (additiveSheaf R M).H n) :
    letI := ordinaryModule R c M n
    z • x = Sheaf.H.map (scalarEnd R c M z) n x := rfl

/-- Scalar compatibility of the existing terminal-source equivalence, proved
from naturality for the genuine scalar endomorphism before constructing a
linear-equivalence record. -/
theorem terminalCohomologyEquiv_smul (n : ℕ) (z : ℂ)
    (x : (additiveSheaf R M).H' n ⊤) :
    letI := cohomologyModule R c M n ⊤
    letI := ordinaryModule R c M n
    terminalCohomologyEquiv (Opens.grothendieckTopology X)
      (additiveSheaf R M) ⊤ isTerminalTop n (z • x) =
    z • terminalCohomologyEquiv (Opens.grothendieckTopology X)
      (additiveSheaf R M) ⊤ isTerminalTop n x :=
  terminalCohomologyEquiv_naturality (scalarEnd R c M z) n x

/-- The existing terminal-source equivalence is linear for the two intrinsic
cohomology actions. Neither action is defined by transporting through it. -/
def terminalLinearEquiv (n : ℕ) :
    letI := cohomologyModule R c M n ⊤
    letI := ordinaryModule R c M n
    (additiveSheaf R M).H' n ⊤ ≃ₗ[ℂ] (additiveSheaf R M).H n := by
  letI := cohomologyModule R c M n ⊤
  letI := ordinaryModule R c M n
  exact (terminalCohomologyEquiv (Opens.grothendieckTopology X)
    (additiveSheaf R M) ⊤ isTerminalTop n).toLinearEquiv
      (terminalCohomologyEquiv_smul R c M n)

@[simp] theorem terminalLinearEquiv_apply (n : ℕ) (x : (additiveSheaf R M).H' n ⊤) :
    terminalLinearEquiv R c M n x =
      terminalCohomologyEquiv (Opens.grothendieckTopology X)
        (additiveSheaf R M) ⊤ isTerminalTop n x := rfl

end ModuleSheaf

section Surface
open CycleQ2CartierProjectiveCover CycleQ2GeometricProjectiveHOne

/-- The actual structure sheaf has the intrinsic ordinary cohomology action. -/
instance surfaceOrdinaryModule (r θ : ℂ) (n : ℕ) :
    Module ℂ ((structureAdditiveSheaf (projectiveSurface r θ)).H n) :=
  ordinaryModule (projectiveSurface r θ).sheaf (surfaceGlobalCoefficient r θ)
    (structureModule (projectiveSurface r θ)) n

/-- The existing terminal comparison on the actual surface, with both
intrinsic actions. -/
def surfaceTerminalLinearEquiv (r θ : ℂ) (n : ℕ) :
    (structureAdditiveSheaf (projectiveSurface r θ)).H' n ⊤ ≃ₗ[ℂ]
      (structureAdditiveSheaf (projectiveSurface r θ)).H n :=
  terminalLinearEquiv (projectiveSurface r θ).sheaf (surfaceGlobalCoefficient r θ)
    (structureModule (projectiveSurface r θ)) n

/-- The same canonical four-open comparison, now in ordinary H-two. -/
def surfaceOrdinaryComparisonLinear (r θ : ℂ) (hr : r ≠ 0) :
    CechTwo (F := structureAdditiveSheaf (projectiveSurface r θ)) (coverFamily r θ) →ₗ[ℂ]
      (structureAdditiveSheaf (projectiveSurface r θ)).H 2 :=
  (surfaceTerminalLinearEquiv r θ 2).toLinearMap.comp (surfaceComparisonLinear r θ hr)

/-- Exact agreement with the previously defined terminal-source equivalence
applied to the original additive comparison. -/
@[simp] theorem surfaceOrdinaryComparisonLinear_apply (r θ : ℂ) (hr : r ≠ 0)
    (x : CechTwo (F := structureAdditiveSheaf (projectiveSurface r θ)) (coverFamily r θ)) :
    surfaceOrdinaryComparisonLinear r θ hr x =
      terminalCohomologyEquiv (Opens.grothendieckTopology (projectiveSurface r θ))
        (structureAdditiveSheaf (projectiveSurface r θ)) ⊤ isTerminalTop 2
        (comparison (coverFamily r θ) (projective_four_cover r θ hr) x) := rfl

theorem surfaceOrdinaryComparisonLinear_injective (r θ : ℂ) (hr : r ≠ 0) :
    Function.Injective (surfaceOrdinaryComparisonLinear r θ hr) :=
  (surfaceTerminalLinearEquiv r θ 2).injective.comp (surfaceComparisonLinear_injective r θ hr)

end Surface

#print axioms terminalCohomologyEquiv_naturality
#print axioms ordinaryModule
#print axioms ordinaryModule_smul
#print axioms terminalCohomologyEquiv_smul
#print axioms terminalLinearEquiv
#print axioms terminalLinearEquiv_apply
#print axioms surfaceOrdinaryModule
#print axioms surfaceTerminalLinearEquiv
#print axioms surfaceOrdinaryComparisonLinear_apply
#print axioms surfaceOrdinaryComparisonLinear_injective

end CycleQ2CechTwoOrdinaryScalar
end

end
