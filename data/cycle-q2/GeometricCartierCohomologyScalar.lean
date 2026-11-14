import Proposal.GeometricCartierDerivedClass
import Proposal.GeometricSheafCohomologyScalar
import Proposal.GeometricCartierCechNonboundary

section

/-!
# Intrinsic complex scalars on the actual four-open comparison

Scalar multiplication on the Cech quotient is induced by genuine
multiplication endomorphisms of the module sheaf. The derived action is
its existing intrinsic cohomology action. Naturality gives a complex-linear
comparison with the same underlying additive map.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CechTwoScalar
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2CechTwoToDerived
  CycleQ2CechTwoComparison CycleQ2CechTwoNaturality
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G H : AbSheaf X} (U : Fin 4 → Opens X)

theorem mapTwo_id (a : Two F U) : mapTwo U (𝟙 F) a=a := by
  rcases a with ⟨a,b,c,d⟩
  rfl

theorem mapTwo_morphism_add (f g : F ⟶ G) (a : Two F U) :
    mapTwo U (f+g) a = mapTwo U f a + mapTwo U g a := by
  rcases a with ⟨a,b,c,d⟩
  rfl

theorem quotientMap_id : quotientMap U (𝟙 F) = AddMonoidHom.id (CechTwo (F := F) U) := by
  apply AddMonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro c
  have h : cyclesMap U (𝟙 F) c=c := Subtype.ext (mapTwo_id U c.val)
  exact congrArg (QuotientAddGroup.mk' (twoBoundaries (F := F) U)) h

theorem quotientMap_comp (f : F ⟶ G) (g : G ⟶ H) :
    quotientMap U (f ≫ g) = (quotientMap U g).comp (quotientMap U f) := by
  apply AddMonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro c
  rfl

theorem quotientMap_add (f g : F ⟶ G) :
    quotientMap U (f+g) = quotientMap U f + quotientMap U g := by
  apply AddMonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro c
  have h : cyclesMap U (f+g) c = cyclesMap U f c + cyclesMap U g c :=
    Subtype.ext (mapTwo_morphism_add U f g c.val)
  exact (congrArg (QuotientAddGroup.mk' (twoBoundaries (F := G) U)) h).trans
    ((QuotientAddGroup.mk' (twoBoundaries (F := G) U)).map_add _ _)

theorem quotientMap_zero : quotientMap U (0 : F ⟶ G) = 0 := by
  apply AddMonoidHom.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro c
  have h : cyclesMap U (0 : F ⟶ G) c=0 := Subtype.ext (mapTwo_zeroHom U c.val)
  exact (congrArg (QuotientAddGroup.mk' (twoBoundaries (F := G) U)) h).trans
    (QuotientAddGroup.mk' (twoBoundaries (F := G) U)).map_zero

section ModuleSheaf
variable (R : X.Sheaf CommRingCat.{0}) (c : ℂ →+* R.obj.obj (op ⊤))
  (M : SheafOfModules.{0} (ringSheaf R))

local instance (O : (Opens X)ᵒᵖ) :
    Module (R.obj.obj O) ((additiveSheaf R M).obj.obj O) :=
  (M.val.obj O).isModule

/-- The literal component of a genuine scalar sheaf endomorphism. -/
theorem scalarEnd_section (z : ℂ) (O : Opens X)
    (x : Sections (additiveSheaf R M) O) :
    app (scalarEnd R c M z) O x = coefficientOn R c O z • x := rfl

/-- All four face components use actual coefficient multiplication on sections. -/
theorem mapTwo_scalarEnd (z : ℂ) (a : Two (additiveSheaf R M) U) :
    mapTwo U (scalarEnd R c M z) a =
      ⟨coefficientOn R c ((U 0 ⊓ U 1) ⊓ U 2) z • a.1,
       coefficientOn R c ((U 0 ⊓ U 1) ⊓ U 3) z • a.2.1,
       coefficientOn R c ((U 0 ⊓ U 2) ⊓ U 3) z • a.2.2.1,
       coefficientOn R c ((U 1 ⊓ U 2) ⊓ U 3) z • a.2.2.2⟩ := rfl

/-- Scalar action induced directly by the actual sectionwise sheaf morphism. -/
def cechScalar (z : ℂ) :
    CechTwo (F := additiveSheaf R M) U →+ CechTwo (F := additiveSheaf R M) U :=
  quotientMap U (scalarEnd R c M z)

theorem cechScalar_one (x : CechTwo (F := additiveSheaf R M) U) :
    cechScalar U R c M 1 x=x := by
  rw [cechScalar, scalarEnd_one, quotientMap_id]
  rfl

theorem cechScalar_mul (a b : ℂ) (x : CechTwo (F := additiveSheaf R M) U) :
    cechScalar U R c M (a*b) x = cechScalar U R c M a (cechScalar U R c M b x) := by
  rw [cechScalar, scalarEnd_mul, quotientMap_comp]
  rfl

theorem cechScalar_add (a b : ℂ) (x : CechTwo (F := additiveSheaf R M) U) :
    cechScalar U R c M (a+b) x = cechScalar U R c M a x + cechScalar U R c M b x := by
  rw [cechScalar, scalarEnd_add, quotientMap_add]
  rfl

theorem cechScalar_zero (x : CechTwo (F := additiveSheaf R M) U) :
    cechScalar U R c M 0 x=0 := by
  rw [cechScalar, scalarEnd_zero, quotientMap_zero]
  rfl

/-- The complex module structure on the genuine cycle/boundary quotient,
induced by multiplication on the original module sheaf. -/
@[instance_reducible] def cechModule : Module ℂ (CechTwo (F := additiveSheaf R M) U) := by
  letI : SMul ℂ (CechTwo (F := additiveSheaf R M) U) :=
    ⟨fun z x => cechScalar U R c M z x⟩
  exact
    { smul_add := fun z x y => (cechScalar U R c M z).map_add x y
      smul_zero := fun z => (cechScalar U R c M z).map_zero
      add_smul := cechScalar_add U R c M
      zero_smul := cechScalar_zero U R c M
      mul_smul := cechScalar_mul U R c M
      one_smul := cechScalar_one U R c M }

/-- The scalar quotient class is represented by the actual componentwise product. -/
theorem cechScalar_mk (z : ℂ) (a : twoCycles (F := additiveSheaf R M) U) :
    cechScalar U R c M z (QuotientAddGroup.mk a) =
      QuotientAddGroup.mk (cyclesMap U (scalarEnd R c M z) a) := rfl

/-- The existing additive comparison is linear for the intrinsic actions on
both sides, as a consequence of genuine sheaf-morphism naturality. -/
def comparisonLinear (hcover : (⨆ i, U i) = ⊤) :
    letI := cechModule U R c M
    letI := cohomologyModule R c M 2 ⊤
    CechTwo (F := additiveSheaf R M) U →ₗ[ℂ] (additiveSheaf R M).H' 2 ⊤ := by
  letI := cechModule U R c M
  letI := cohomologyModule R c M 2 ⊤
  exact
    { comparison U hcover with
      map_smul' := by
        intro z x
        change comparison U hcover (quotientMap U (scalarEnd R c M z) x) =
          derivedMap (scalarEnd R c M z) (comparison U hcover x)
        exact DFunLike.congr_fun (comparison_naturality U hcover (scalarEnd R c M z)) x }

@[simp] theorem comparisonLinear_apply (hcover : (⨆ i, U i) = ⊤)
    (x : CechTwo (F := additiveSheaf R M) U) :
    comparisonLinear U R c M hcover x = comparison U hcover x := rfl

theorem comparisonLinear_injective (hcover : (⨆ i, U i) = ⊤)
    (hlocal : ∀ i, Subsingleton ((additiveSheaf R M).H' 1 (U i))) :
    Function.Injective (comparisonLinear U R c M hcover) :=
  comparison_injective U hcover hlocal

end ModuleSheaf

#print axioms mapTwo_scalarEnd
#print axioms cechModule
#print axioms cechScalar_mk
#print axioms comparisonLinear
#print axioms comparisonLinear_apply
#print axioms comparisonLinear_injective

end CycleQ2CechTwoScalar
end

end


section

/-!
# The intrinsic complex-linear comparison on the actual projective surface

The coefficient map comes from the actual weighted Proj structure morphism.
Both scalar actions are induced by multiplication on its structure-module
sheaf, and the underlying comparison is the previously proved additive map.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2SurfaceCechTwoScalar
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  Opposite TopologicalSpace CycleQ2InjectiveCech CycleQ2CechTwoComparison
  CycleQ2CechTwoScalar CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSheafCohomologyScalar

local instance schemeSheavesHasExt (Y : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) :=
  HasExt.standard _

section Surface
open AlgebraicGeometry CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
  CycleQ2GeometricProjectiveHOne

/-- The genuine rank-one structure-module sheaf. -/
def structureModule (Y : Scheme.{0}) : SheafOfModules.{0} (ringSheaf Y.sheaf) :=
  SheafOfModules.unit (ringSheaf Y.sheaf)

@[simp] theorem structureModule_additive (Y : Scheme.{0}) :
    additiveSheaf Y.sheaf (structureModule Y) = structureAdditiveSheaf Y := rfl

/-- The actual complex structure morphism of the weighted projective surface. -/
def surfaceToComplex (r θ : ℂ) : projectiveSurface r θ ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero (surfaceGrade r θ) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (surfaceGrade r θ 0)))

/-- Global complex coefficients pulled back along the actual structure morphism. -/
def surfaceGlobalCoefficient (r θ : ℂ) : ℂ →+* Γ(projectiveSurface r θ, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (surfaceToComplex r θ).appTop).hom

/-- The actual componentwise complex action on the surface's four-open quotient. -/
instance surfaceCechModule (r θ : ℂ) :
    Module ℂ (CechTwo (F := structureAdditiveSheaf (projectiveSurface r θ))
      (coverFamily r θ)) :=
  cechModule (coverFamily r θ) (projectiveSurface r θ).sheaf
    (surfaceGlobalCoefficient r θ) (structureModule (projectiveSurface r θ))

/-- The intrinsic complex action on every actual derived group of the structure
sheaf, obtained by applying cohomology to genuine scalar multiplication. -/
instance surfaceCohomologyModule (r θ : ℂ) (n : ℕ)
    (O : (projectiveSurface r θ).Opens) :
    Module ℂ ((structureAdditiveSheaf (projectiveSurface r θ)).H' n O) :=
  cohomologyModule (projectiveSurface r θ).sheaf (surfaceGlobalCoefficient r θ)
    (structureModule (projectiveSurface r θ)) n O

/-- The actual four-open comparison for the actual surface is complex-linear. -/
def surfaceComparisonLinear (r θ : ℂ) (hr : r ≠ 0) :
    CechTwo (F := structureAdditiveSheaf (projectiveSurface r θ)) (coverFamily r θ) →ₗ[ℂ]
      (structureAdditiveSheaf (projectiveSurface r θ)).H' 2 ⊤ :=
  comparisonLinear (coverFamily r θ) (projectiveSurface r θ).sheaf
    (surfaceGlobalCoefficient r θ) (structureModule (projectiveSurface r θ))
    (projective_four_cover r θ hr)

@[simp] theorem surfaceComparisonLinear_apply (r θ : ℂ) (hr : r ≠ 0)
    (x : CechTwo (F := structureAdditiveSheaf (projectiveSurface r θ)) (coverFamily r θ)) :
    surfaceComparisonLinear r θ hr x =
      comparison (coverFamily r θ) (projective_four_cover r θ hr) x := rfl

theorem surfaceComparisonLinear_injective (r θ : ℂ) (hr : r ≠ 0) :
    Function.Injective (surfaceComparisonLinear r θ hr) := by
  apply comparisonLinear_injective
  intro i
  have h := coverPatch_H_one_subsingleton r θ {i} (by simp)
  simpa only [structureModule_additive, coverPatch_singleton] using h

end Surface

#print axioms surfaceToComplex
#print axioms surfaceGlobalCoefficient
#print axioms surfaceCechModule
#print axioms surfaceCohomologyModule
#print axioms surfaceComparisonLinear_apply
#print axioms surfaceComparisonLinear_injective

end CycleQ2SurfaceCechTwoScalar
end

end
