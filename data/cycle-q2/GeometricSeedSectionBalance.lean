import Proposal.GeometricSeedSectionInverse
import Proposal.GeometricSeedImageSheafEmbedding
import Proposal.GeometricSeedProjectiveImageCocycle

/-!
# The original section functional satisfies its linkage equation

The balance identity is proved on the original left generators and then
extended to the whole original ideal. It uses the original section
functional and the original right generators; no auxiliary functional is
chosen. Functoriality transports the equation to every section module of
the actual associated sheaves. Regularity of the linkage element also
survives on those section modules.

-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

namespace CycleQ2SeedSectionBalance

open CategoryTheory AlgebraicGeometry Matrix
open CycleQ2SegreFactorSequence CycleQ2SegreLinkageDuality
  CycleQ2SeedProjectiveImageTwist CycleQ2SeedSectionInverse
  CycleQ2SeedImageSheafEmbedding

variable {R : Type u} [CommRing R]

local instance (priority := 10) nativeSectionAlgebra (U : (Spec (CommRingCat.of R)).Opens) :
    Algebra R Γ(Spec (CommRingCat.of R), U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (Opposite.op U)))

local instance (priority := 10) nativeSectionsModule (M : (Spec (CommRingCat.of R)).Modules)
    (U : (Spec (CommRingCat.of R)).Opens) : Module R Γ(M, U) :=
  inferInstanceAs (Module R ((modulesSpecToSheaf.obj M).presheaf.obj (Opposite.op U)))

theorem sectionFunctional_balance_linear (F : FactorData R) (t : Fin 3 → R) :
    F.linkage • sectionFunctional F t =
      (∑ b, t b * F.right b) • F.leftIdeal.subtype := by
  apply Regrading.dual_ext F
  intro a
  change F.linkage * sectionFunctional F t (leftElement F a) =
    (∑ b, t b * F.right b) * F.left a
  rw [sectionFunctional_left]
  change F.linkage * (∑ b, F.matrix a b * t b) =
    (∑ b, t b * F.right b) * F.left a
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  calc
    F.linkage * (F.matrix a b * t b) = t b * (F.linkage * F.matrix a b) := by ring
    _ = t b * (F.left a * F.right b) := by rw [← F.product a b]
    _ = (t b * F.right b) * F.left a := by ring

/-- The literal linkage equation holds for every element of the original
left ideal, not only the three distinguished generators. -/
theorem sectionFunctional_balance (F : FactorData R) (t : Fin 3 → R)
    (x : F.leftIdeal) :
    F.linkage * sectionFunctional F t x = (x : R) * ∑ b, t b * F.right b := by
  calc
    F.linkage * sectionFunctional F t x = (∑ b, t b * F.right b) * (x : R) :=
      LinearMap.congr_fun (sectionFunctional_balance_linear F t) x
    _ = (x : R) * ∑ b, t b * F.right b := mul_comm _ _

/-- The linkage equation determines the original functional value
uniquely because the linkage element is regular. -/
theorem eq_sectionFunctional_of_balance (F : FactorData R) (t : Fin 3 → R)
    (x : F.leftIdeal) (y : R)
    (hy : F.linkage * y = (x : R) * ∑ b, t b * F.right b) :
    y = sectionFunctional F t x :=
  F.regular (hy.trans (sectionFunctional_balance F t x).symm)

/-- Multiplication as an actual morphism of the original affine module. -/
def scalarMap (a : R) : ModuleCat.of R R ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom (a • (LinearMap.id : R →ₗ[R] R))

def functionalMap (F : FactorData R) (t : Fin 3 → R) :
    ModuleCat.of R F.leftIdeal ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom (sectionFunctional F t)

def idealInclusion (F : FactorData R) :
    ModuleCat.of R F.leftIdeal ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom F.leftIdeal.subtype

theorem functionalMap_balance (F : FactorData R) (t : Fin 3 → R) :
    functionalMap F t ≫ scalarMap F.linkage =
      idealInclusion F ≫ scalarMap (R := R) (∑ b, t b * F.right b) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (sectionFunctional_balance_linear F t) x

/-- Balance in the category of actual sheaves on Spec R. -/
theorem tilde_balance (F : FactorData R) (t : Fin 3 → R) :
    tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R F.leftIdeal) (N := ModuleCat.of R R) (functionalMap F t) ≫ tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R R) (N := ModuleCat.of R R) (scalarMap F.linkage) =
      tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R F.leftIdeal) (N := ModuleCat.of R R) (idealInclusion F) ≫ tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R R) (N := ModuleCat.of R R) (scalarMap (R := R) (∑ b, t b * F.right b)) := by
  rw [← tilde.map_comp, ← tilde.map_comp, functionalMap_balance]

/-- The same identity on every actual open, including nonprincipal opens. -/
theorem tilde_balance_app (F : FactorData R) (t : Fin 3 → R)
    (U : (Spec (CommRingCat.of R)).Opens)
    (s : Γ(tilde (R := CommRingCat.of R) (ModuleCat.of R F.leftIdeal), U)) :
    (tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R R) (N := ModuleCat.of R R) (scalarMap F.linkage)).app U
        ((tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R F.leftIdeal) (N := ModuleCat.of R R) (functionalMap F t)).app U s) =
      (tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R R) (N := ModuleCat.of R R) (scalarMap (R := R) (∑ b, t b * F.right b))).app U
        ((tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R F.leftIdeal) (N := ModuleCat.of R R) (idealInclusion F)).app U s) := by
  exact congrArg (fun f : tilde (R := CommRingCat.of R) (ModuleCat.of R F.leftIdeal) ⟶
    tilde (R := CommRingCat.of R) (ModuleCat.of R R) => f.app U s) (tilde_balance F t)

/-- Multiplication by the original regular linkage element stays
injective on every actual associated-sheaf section module. -/
theorem tilde_linkage_app_injective (F : FactorData R)
    (U : (Spec (CommRingCat.of R)).Opens) :
    Function.Injective ((tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R R) (N := ModuleCat.of R R) (scalarMap F.linkage)).app U) :=
  tilde_map_app_injective (R := CommRingCat.of R)
    (M := ModuleCat.of R R) (N := ModuleCat.of R R) (scalarMap F.linkage) F.regular U

/-- The associated-sheaf map of multiplication is the canonical scalar
action on sections. The comparison iso is needed because the two native
R-module presentations of these sections are not definitionally equal. -/
theorem tilde_scalarMap_app (a : R)
    (U : (Spec (CommRingCat.of R)).Opens)
    (s : Γ(tilde (R := CommRingCat.of R) (ModuleCat.of R R), U)) :
    (tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R R) (N := ModuleCat.of R R) (scalarMap a)).app U s = a • s := by
  let e := ((tilde.modulesSpecToSheafIso (R := CommRingCat.of R) (ModuleCat.of R R)).app
    (Opposite.op U)).toLinearEquiv
  apply e.injective
  rw [e.map_smul]
  apply Subtype.ext
  funext x
  change IsLocalizedModule.map x.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl R)
      (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl R)
      (a • (LinearMap.id : R →ₗ[R] R)) (s.1 x) = a • s.1 x
  rw [map_smul, IsLocalizedModule.map_id]
  rfl

/-- The linkage element is regular for the canonical R-action on every
actual associated-sheaf section module. -/
theorem tilde_linkage_isSMulRegular (F : FactorData R)
    (U : (Spec (CommRingCat.of R)).Opens) :
    IsSMulRegular Γ(tilde (R := CommRingCat.of R) (ModuleCat.of R R), U) F.linkage := by
  intro s t h
  apply tilde_linkage_app_injective F U
  simpa only [tilde_scalarMap_app] using h

/-- Balance expressed using the canonical scalar action, ready for the
structure-sheaf multiplication comparison `Scheme.Modules.smul_Spec_def`. -/
theorem tilde_balance_smul (F : FactorData R) (t : Fin 3 → R)
    (U : (Spec (CommRingCat.of R)).Opens)
    (s : Γ(tilde (R := CommRingCat.of R) (ModuleCat.of R F.leftIdeal), U)) :
    F.linkage • ((tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R F.leftIdeal) (N := ModuleCat.of R R) (functionalMap F t)).app U s) =
      (∑ b, t b * F.right b) • ((tilde.map (R := CommRingCat.of R)
      (M := ModuleCat.of R F.leftIdeal) (N := ModuleCat.of R R) (idealInclusion F)).app U s) := by
  simpa only [tilde_scalarMap_app] using tilde_balance_app F t U s

/-! ## The same linkage equation in actual projective sections -/

open MvPolynomial CycleQ2SeedTrace CycleQ2CartierSurfaceGrading
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2SeedProjectiveImageChart
  CycleQ2SeedProjectiveImageCocycle

def sectionLinkage (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    Γ(Surface, V) := chartSectionMap i V hi (chartFactorData i).linkage

theorem sectionLinkage_entry (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    sectionLinkage i V hi =
      polynomialSection i V hi (CycleQ2SeedFactorHomogeneous.polynomialLinkage (57 : ℂ)) := by
  change chartSectionMap i V hi (coneToChart i (conePolynomial i
      (CycleQ2SeedFactorHomogeneous.polynomialLinkage (57 : ℂ)))) =
    chartSectionMap i V hi (affinePolynomial i
      (CycleQ2SeedFactorHomogeneous.polynomialLinkage (57 : ℂ)))
  exact congrArg (chartSectionMap i V hi) (coneToChart_polynomial i _)

theorem sectionLinkage_change (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) :
    sectionLinkage j V hj =
      (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 4 * sectionLinkage i V hi := by
  rw [sectionLinkage_entry, sectionLinkage_entry]
  exact polynomialSection_change i j V hi hj 4 _ linkage_weighted_homogeneous

def sectionRight (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    Fin 3 → Γ(Surface, V) :=
  fun b => chartSectionMap i V hi ((chartFactorData i).right b)

theorem sectionRight_entry (i b : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    sectionRight i V hi b =
      polynomialSection i V hi (CycleQ2SeedFactorHomogeneous.polynomialRight (57 : ℂ) b) := by
  change chartSectionMap i V hi (coneToChart i (conePolynomial i
      (CycleQ2SeedFactorHomogeneous.polynomialRight (57 : ℂ) b))) =
    chartSectionMap i V hi (affinePolynomial i
      (CycleQ2SeedFactorHomogeneous.polynomialRight (57 : ℂ) b))
  exact congrArg (chartSectionMap i V hi) (coneToChart_polynomial i _)

theorem sectionRight_change (i j b : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) :
    sectionRight j V hj b =
      (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 8 * sectionRight i V hi b := by
  rw [sectionRight_entry, sectionRight_entry]
  exact polynomialSection_change i j V hi hj 8 _
    (CycleQ2GeometricIncidenceProj.homogeneous_of_character
      (CycleQ2SeedFactorHomogeneous.polynomialRight_homogeneous (57 : ℂ) b))

theorem affinePolynomial_constant (i : Fin 3) (c : ℂ) :
    affinePolynomial i (C c) = algebraMap ℂ (AffineRing i) c := by
  change dehomogenizedMap 57 1 i.succ (dehomogenize i.succ (C c)) = _
  rw [show dehomogenize i.succ (C c) = C c from by
    simpa only [MvPolynomial.algebraMap_eq] using (dehomogenize i.succ).commutes c]
  rfl

def sectionConstant (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) (c : ℂ) :
    Γ(Surface, V) := chartSectionMap i V hi (algebraMap ℂ (AffineRing i) c)

theorem sectionConstant_entry (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (c : ℂ) : sectionConstant i V hi c = polynomialSection i V hi (C c) := by
  exact congrArg (chartSectionMap i V hi) (affinePolynomial_constant i c).symm

theorem sectionConstant_change (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (c : ℂ) :
    sectionConstant j V hj c = sectionConstant i V hi c := by
  rw [sectionConstant_entry, sectionConstant_entry]
  simpa only [pow_zero, one_mul] using
    polynomialSection_change i j V hi hj 0 (C c) (isWeightedHomogeneous_C weight c)

def sectionRightCombination (t : Fin 3 → ℂ) (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) : Γ(Surface, V) :=
  chartSectionMap i V hi
    (∑ b, algebraMap ℂ (AffineRing i) (t b) * (chartFactorData i).right b)

theorem sectionRightCombination_eq_sum (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) :
    sectionRightCombination t i V hi =
      ∑ b, sectionConstant i V hi (t b) * sectionRight i V hi b := by
  simp only [sectionRightCombination, map_sum, map_mul, sectionConstant, sectionRight]

/-- The same complex vector has degree-eight right-combination transition
on every actual common open. Its coefficient sections agree across charts. -/
theorem sectionRightCombination_change (t : Fin 3 → ℂ) (i j : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (hj : V ≤ Patch j) :
    sectionRightCombination t j V hj =
      (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 8 *
        sectionRightCombination t i V hi := by
  rw [sectionRightCombination_eq_sum, sectionRightCombination_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [sectionConstant_change i j V hi hj (t b), sectionRight_change i j b V hi hj]
  ring

end CycleQ2SeedSectionBalance

end

#print axioms CycleQ2SeedSectionBalance.sectionFunctional_balance
#print axioms CycleQ2SeedSectionBalance.tilde_balance_app
#print axioms CycleQ2SeedSectionBalance.tilde_linkage_app_injective
#print axioms CycleQ2SeedSectionBalance.tilde_scalarMap_app
#print axioms CycleQ2SeedSectionBalance.tilde_linkage_isSMulRegular
#print axioms CycleQ2SeedSectionBalance.sectionLinkage_change
#print axioms CycleQ2SeedSectionBalance.sectionRightCombination_change
