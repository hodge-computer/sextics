import Proposal.GeometricCartierCohomologyScalar
import Proposal.GeometricSurfaceResidueFunctoriality
import Proposal.GeometricNormalSheafComparison

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


section

/-! The same original normal classes and cubic maps in ordinary derived
surface cohomology. The comparison is the canonical terminal-source
isomorphism and is natural for the actual pushed-forward cubic morphism. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2SurfaceNormalOrdinary

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
  CycleQ2SurfaceNormalCohomology CycleQ2CartierProjectiveCover
  CycleQ2ProjectiveCurveSurface CycleQ2GeometricProjectiveNormalClass
  CycleQ2GeometricSheafCohomologyRestriction CycleQ2CechTwoOrdinaryScalar
  CycleQ2GeometricLiteralDirection CycleQ2SeedTrace

local instance surfaceHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveSurface r θ)) AddCommGrpCat.{0}) :=
  HasExt.standard _

abbrev NormalOrdinaryH1 (r θ : ℂ) := (pushedNormalSheaf r θ).H 1

def normalTerminalEquiv (r θ : ℂ) :
    NormalH1OnSurface r θ ≃+ NormalOrdinaryH1 r θ :=
  terminalCohomologyEquiv (Opens.grothendieckTopology (projectiveSurface r θ))
    (pushedNormalSheaf r θ) ⊤ isTerminalTop 1

def degreeOneTerminalEquiv (r θ : ℂ) :
    (pushedDegreeOneSheaf r θ).H' 1 ⊤ ≃+ (pushedDegreeOneSheaf r θ).H 1 :=
  terminalCohomologyEquiv (Opens.grothendieckTopology (projectiveSurface r θ))
    (pushedDegreeOneSheaf r θ) ⊤ isTerminalTop 1

def normalOrdinaryClass (r θ : ℂ) (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 6) : NormalOrdinaryH1 r θ :=
  normalTerminalEquiv r θ (normalClassOnSurface r θ hr p hp)

theorem normalOrdinaryClass_zero_iff (r θ : ℂ) (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 6) :
    normalOrdinaryClass r θ hr p hp = 0 ↔ normalClass r θ hr p hp = 0 := by
  change normalTerminalEquiv r θ (normalClassOnSurface r θ hr p hp) = 0 ↔ _
  rw [map_eq_zero_iff _ (normalTerminalEquiv r θ).injective]
  exact normalClassOnSurface_zero_iff r θ hr p hp

def cubicOrdinaryMap (r θ : ℂ) (hr : r ≠ 0) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    NormalOrdinaryH1 r θ →+ (pushedDegreeOneSheaf r θ).H 1 :=
  Sheaf.H.map
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (curveToSurface r θ).base).map
      (cubicAdditiveMorphism r θ hr σ hσ)) 1

theorem cubicOrdinaryMap_terminal (r θ : ℂ) (hr : r ≠ 0)
    (σ : Poly) (hσ : σ.IsHomogeneous 3) (x : NormalH1OnSurface r θ) :
    cubicOrdinaryMap r θ hr σ hσ (normalTerminalEquiv r θ x) =
      degreeOneTerminalEquiv r θ (cubicH1OnSurface r θ hr σ hσ x) :=
  (terminalCohomologyEquiv_naturality
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (curveToSurface r θ).base).map
      (cubicAdditiveMorphism r θ hr σ hσ)) 1 x).symm

theorem cubicOrdinaryMap_normalClass_zero_iff (r θ : ℂ) (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 6) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    cubicOrdinaryMap r θ hr σ hσ (normalOrdinaryClass r θ hr p hp) = 0 ↔
      cubicH1Map r θ hr σ hσ (normalClass r θ hr p hp) = 0 := by
  change cubicOrdinaryMap r θ hr σ hσ
    (normalTerminalEquiv r θ (normalClassOnSurface r θ hr p hp)) = 0 ↔ _
  rw [cubicOrdinaryMap_terminal, map_eq_zero_iff _ (degreeOneTerminalEquiv r θ).injective]
  exact cubicH1OnSurface_normalClass_zero_iff r θ hr p hp σ hσ

def literalOrdinaryNormalClass : NormalOrdinaryH1 57 1 :=
  normalTerminalEquiv 57 1 literalNormalClassOnSurface

theorem literalOrdinaryNormalClass_ne_zero : literalOrdinaryNormalClass ≠ 0 := by
  intro hz
  apply literalNormalClassOnSurface_ne_zero
  exact (normalTerminalEquiv 57 1).injective (hz.trans (map_zero _).symm)

theorem literal_ordinary_selected_cubic_image_ne_zero :
    cubicOrdinaryMap 57 1 (by norm_num) selectedCubic selectedCubic_homogeneous
      literalOrdinaryNormalClass ≠ 0 := by
  intro hz
  apply literal_selected_cubic_image_ne_zero
  change cubicOrdinaryMap 57 1 (by norm_num) selectedCubic selectedCubic_homogeneous
    (normalTerminalEquiv 57 1 literalNormalClassOnSurface) = 0 at hz
  rw [cubicOrdinaryMap_terminal] at hz
  exact (degreeOneTerminalEquiv 57 1).injective (hz.trans (map_zero _).symm)

def selectedOrdinaryIncidenceNormalClass : NormalOrdinaryH1 57 1 :=
  normalTerminalEquiv 57 1 selectedIncidenceNormalClassOnSurface

theorem selectedOrdinaryIncidenceNormalClass_in_seven_kernels (j : Fin 7) :
    cubicOrdinaryMap 57 1 (by norm_num) (testCubic j) (testCubic_homogeneous j)
      selectedOrdinaryIncidenceNormalClass = 0 := by
  change cubicOrdinaryMap 57 1 (by norm_num) (testCubic j) (testCubic_homogeneous j)
    (normalTerminalEquiv 57 1 selectedIncidenceNormalClassOnSurface) = 0
  rw [cubicOrdinaryMap_terminal, selectedIncidenceNormalClassOnSurface_in_seven_kernels, map_zero]

end CycleQ2SurfaceNormalOrdinary
end

end


section

/-! The original selected normal class and incidence class in cohomology
of the genuine intrinsic normal direct image of the original closed
immersion. The concrete sheaf identification is proved at the literal
seed, so no model-identification or smoothness premise remains here. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2IntrinsicSurfaceNormalCohomology

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2SurfaceNormalCohomology CycleQ2SurfaceNormalTransport
  CycleQ2IntrinsicNormalModel CycleQ2GeometricProjectiveNormalClass
  CycleQ2GeometricLiteralDirection CycleQ2SeedTrace CycleQ2CartierProjectiveCover

local instance surfaceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveSurface 57 1)) AddCommGrpCat.{0}) :=
  HasExt.standard _

def literalIntrinsicNormalClass : IntrinsicNormalH1 57 1 :=
  intrinsicNormalClass 57 1 intrinsicNormalIso (by norm_num)
    ambientNormalNumerator ambientNormalNumerator_homogeneous

theorem literalIntrinsicNormalClass_ne_zero : literalIntrinsicNormalClass ≠ 0 := by
  intro hz
  apply literalNormalClass_ne_zero
  exact (intrinsicNormalClass_zero_iff 57 1 intrinsicNormalIso (by norm_num)
    ambientNormalNumerator ambientNormalNumerator_homogeneous).mp hz

/-- This is an actual morphism out of the intrinsic surface-side normal
sheaf; its coefficient is the original cubic under the proved normal frame. -/
def literalIntrinsicCubicMorphism (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    intrinsicSurfaceNormalSheaf 57 1 ⟶ pushedDegreeOneSheaf 57 1 :=
  intrinsicCubicMorphism 57 1 intrinsicNormalIso (by norm_num) σ hσ

def literalIntrinsicCubicH1Map (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    IntrinsicNormalH1 57 1 →+ (pushedDegreeOneSheaf 57 1).H' 1 ⊤ :=
  intrinsicCubicH1Map 57 1 intrinsicNormalIso (by norm_num) σ hσ

theorem literalIntrinsicCubicH1Map_class (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    literalIntrinsicCubicH1Map σ hσ literalIntrinsicNormalClass =
      cubicH1OnSurface 57 1 (by norm_num) σ hσ literalNormalClassOnSurface :=
  intrinsicCubicH1Map_class 57 1 intrinsicNormalIso (by norm_num)
    ambientNormalNumerator ambientNormalNumerator_homogeneous σ hσ

theorem literal_intrinsic_selected_cubic_image_ne_zero :
    literalIntrinsicCubicH1Map selectedCubic selectedCubic_homogeneous
      literalIntrinsicNormalClass ≠ 0 := by
  rw [literalIntrinsicCubicH1Map_class]
  exact literal_selected_cubic_image_ne_zero

def literalIntrinsicIncidenceClass : IntrinsicNormalH1 57 1 :=
  intrinsicNormalClass 57 1 intrinsicNormalIso (by norm_num)
    incidenceNormalNumerator incidenceNormalNumerator_homogeneous

theorem literalIntrinsicIncidenceClass_in_seven_kernels (j : Fin 7) :
    literalIntrinsicCubicH1Map (testCubic j) (testCubic_homogeneous j)
      literalIntrinsicIncidenceClass = 0 :=
  (intrinsicCubicH1Map_class 57 1 intrinsicNormalIso (by norm_num)
    incidenceNormalNumerator incidenceNormalNumerator_homogeneous
      (testCubic j) (testCubic_homogeneous j)).trans
    (selectedIncidenceNormalClassOnSurface_in_seven_kernels j)

end CycleQ2IntrinsicSurfaceNormalCohomology
end

end
