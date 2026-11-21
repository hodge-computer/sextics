import Proposal.GeometricCanonicalCoordinateH2
import Proposal.GeometricCanonicalResidueScalar
import Proposal.GeometricSurfaceSectionCoefficients
import Proposal.GeometricSurfaceProjectiveCoefficients

/-!
# Global regular functions on the literal surface

A global section is determined on the triple coordinate open. Its restriction
to every singleton chart has the same Laurent coordinates. The finite
rank-nine basis over the three polynomial coordinates and the projective
degree-zero condition then identify the surviving coefficient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralGlobalFunctions

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricLaurentTop
  CycleQ2ProjectiveCoordinateCohomology CycleQ2CartierSurfaceGrading
  CycleQ2GeometricSurfaceCoefficients CycleQ2SurfaceSectionCoefficients
  CycleQ2CanonicalCoordinateH2 CycleQ2GeometricHomogeneousWeight
  CycleQ2CoordinateCechTrace CycleQ2ProjectiveCoordinateH2 CycleQ2SeedCechThreeOpen
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
  CycleQ2SeedCechLocalizedBasis

/-- The Laurent coefficient on the indicated intersection of the coordinate charts. -/
def globalOn (s : Γ(Surface, ⊤)) (I : Finset (Fin 3)) (hI : I.Nonempty) :
    CoordinateLocal 57 1 I :=
  sectionCoefficient 57 1 I hI
    (Surface.presheaf.map (homOfLE (le_top : coordinateIntersection 57 1 I ≤ ⊤)).op s)

/-- Restriction of global functions commutes with the localized-section identification. -/
theorem globalOn_restrict (s : Γ(Surface, ⊤)) {I J : Finset (Fin 3)}
    (hI : I.Nonempty) (hJ : J.Nonempty) (h : I ⊆ J) :
    globalOn s J hJ = coordinateRestriction 57 1 h (globalOn s I hI) := by
  unfold globalOn
  rw [← sectionCoefficient_restrict 57 1 hI hJ h]
  apply congrArg (sectionCoefficient 57 1 J hJ)
  exact congrArg (fun f : Surface.presheaf.obj (op ⊤) ⟶
    Surface.presheaf.obj (op (coordinateIntersection 57 1 J)) => f s)
    (Surface.presheaf.map_comp (homOfLE (le_top : coordinateIntersection 57 1 I ≤ ⊤)).op
      (homOfLE (coordinateIntersection_mono 57 1 h)).op)

/-- A global function gives a weight-zero Laurent expansion on the triple chart. -/
theorem globalOn_weight (s : Γ(Surface, ⊤)) :
    globalOn s Finset.univ (by simp) ∈ coordinateLocalWeight 57 0 Finset.univ := by
  apply (mem_coordinateLocalWeight_iff 57 0 Finset.univ _).mpr
  exact homogeneous_coordinate_weight 57
    ((coordinateSections 57 1 Finset.univ (by simp)).symm
      (Surface.presheaf.map (homOfLE le_top).op s))

/-- A Laurent monomial occurring in a global function has no negative exponents. -/
theorem globalOn_nonnegative (s : Γ(Surface, ⊤)) (ab : ShiftIndex) (e : LaurentExponent)
    (h : (coordinateLaurent 57 Finset.univ (globalOn s Finset.univ (by simp)) ab).coeff e ≠ 0)
    (i : Fin 3) : 0 ≤ e i := by
  let j : Fin 3 := if i = 0 then 1 else 0
  have hij : i ∉ ({j} : Finset (Fin 3)) := by fin_cases i <;> decide
  rw [globalOn_restrict s (Finset.singleton_nonempty j) (by simp) (Finset.subset_univ {j}),
    coordinateLaurent_restriction] at h
  exact le_of_not_gt (fun he => h (coordinateLaurent_hasPoles 57 {j}
    (globalOn s {j} (by simp)) ab e i hij he))


private theorem weight_zero_unique (ab : ShiftIndex) (e : LaurentExponent)
    (he : ∀ i, 0 ≤ e i) (hw : (shiftedGrade ab e).1 = 0) :
    ab = (0,0) ∧ e = 0 := by
  rcases ab with ⟨a,b⟩
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  simp only [shiftedGrade, Fin.sum_univ_three] at hw
  have ha : a.val = 0 := by omega
  have hb : b.val = 0 := by omega
  refine ⟨Prod.ext (Fin.ext ha) (Fin.ext hb), ?_⟩
  funext i
  fin_cases i
  · change e 0 = 0
    omega
  · change e 1 = 0
    omega
  · change e 2 = 0
    omega

private theorem laurent_one (I : Finset (Fin 3)) (ab : ShiftIndex) :
    coordinateLaurent 57 I 1 ab = if ab = (0,0) then 1 else 0 := by
  classical
  change localizedCoordinates ℂ 57 Complex.I I (seedCoordinateEquiv 57 I 1) ab = _
  rw [map_one, ← map_one (algebraMap (SeedRing 57 Complex.I) (SeedLocal ℂ 57 Complex.I I)),
    localizedCoordinates_algebraMap]
  have hb : seedBasis ℂ 57 Complex.I (0,0) = 1 := by simp [seedBasis_apply]
  rw [← hb, Module.Basis.repr_self]
  by_cases h : ab = (0,0) <;> simp [h]

/-- In the original Laurent coordinates the scalar has a single coefficient. -/
theorem scalar_coefficient (I : Finset (Fin 3)) (c : ℂ) (ab : ShiftIndex)
    (e : LaurentExponent) :
    (coordinateLaurent 57 I (algebraMap ℂ (CoordinateLocal 57 1 I) c) ab).coeff e =
      if ab = (0,0) ∧ e = 0 then c else 0 := by
  classical
  have hc : algebraMap ℂ (CoordinateLocal 57 1 I) c = c • (1 : CoordinateLocal 57 1 I) := by
    rw [Algebra.smul_def, mul_one]
  rw [hc, coordinateLaurent_complex_smul, Pi.smul_apply, laurent_one]
  by_cases hab : ab = (0,0) <;> by_cases he : e = 0 <;>
    simp [hab, he, AddMonoidAlgebra.one_def]

/-- If all exponents in a regular weight-zero fraction are nonnegative, the
fraction is its constant coefficient embedded through the original algebra map. -/
theorem eq_scalar_of_nonnegative (p : CoordinateLocal 57 1 Finset.univ)
    (hw : p ∈ coordinateLocalWeight 57 0 Finset.univ)
    (hn : ∀ ab e, (coordinateLaurent 57 Finset.univ p ab).coeff e ≠ 0 → ∀ i, 0 ≤ e i) :
    p = algebraMap ℂ _ ((coordinateLaurent 57 Finset.univ p (0,0)).coeff 0) := by
  classical
  apply coordinateLaurent_injective 57 Finset.univ
  ext ab e
  rw [scalar_coefficient]
  by_cases h : ab = (0,0) ∧ e = 0
  · obtain ⟨rfl,rfl⟩ := h
    simp
  · rw [if_neg h]
    by_contra hc
    exact h (weight_zero_unique ab e (hn ab e hc)
      ((mem_coordinateLocalWeight_iff 57 0 Finset.univ p).mp hw ab e hc))

/-- The triple coefficient determines a global section, by faithful Laurent
restriction on each member of the three-open cover. -/
theorem globalOn_injective :
    Function.Injective (fun s => globalOn s Finset.univ (by simp)) := by
  intro s t h
  change globalOn s Finset.univ (by simp) = globalOn t Finset.univ (by simp) at h
  apply Surface.sheaf.eq_of_locally_eq' (fun i : Fin 3 => coordinateIntersection 57 1 {i}) ⊤
    (fun _ => homOfLE le_top) (by simpa only [coordinateIntersection_singleton] using
      (coordinate_cover 57 1 one_ne_zero).ge) s t
  intro i
  let I : Finset (Fin 3) := {i}
  have hI : I.Nonempty := by simp [I]
  let e := coordinateSections 57 1 I hI
  apply e.symm.injective
  apply HomogeneousLocalization.val_injective
  change globalOn s I hI = globalOn t I hI
  apply coordinateLaurent_injective 57 I
  let hIU := Finset.subset_univ I
  have hs := (globalOn_restrict s hI (by simp) hIU).symm
  have ht := (globalOn_restrict t hI (by simp) hIU).symm
  rw [← coordinateLaurent_restriction 57 hIU, hs, h, ← ht, coordinateLaurent_restriction]

theorem globalOn_scalar (I : Finset (Fin 3)) (hI : I.Nonempty) (c : ℂ) :
    globalOn (projectiveGlobalCoefficient 57 1 c) I hI =
      algebraMap ℂ (CoordinateLocal 57 1 I) c := by
  have h := coefficientOn_basicOpen 57 1 (coordinateProduct 57 1 I)
    (coordinateProduct_mem_grade 57 1 I) (Finset.card_pos.mpr hI) c
  have hh := congrArg (fun z : HomogeneousCoordinateLocal 57 1 I => z.val) h
  refine hh.trans ?_
  change Localization.mk (algebraMap ℂ (SurfaceRing 57 1) c) 1 = _
  rw [Localization.mk_one_eq_algebraMap, ← IsScalarTower.algebraMap_apply]


/-- The coefficient from the only possible degree-zero Laurent monomial. -/
def constantCoefficient (s : Γ(Surface, ⊤)) : ℂ :=
  (coordinateLaurent 57 Finset.univ (globalOn s Finset.univ (by simp)) (0,0)).coeff 0

theorem constantCoefficient_scalar (c : ℂ) :
    constantCoefficient (projectiveGlobalCoefficient 57 1 c) = c := by
  simp [constantCoefficient, globalOn_scalar, scalar_coefficient]

/-- Each global function equals the scalar obtained from its Laurent expansion. -/
theorem scalar_constantCoefficient (s : Γ(Surface, ⊤)) :
    projectiveGlobalCoefficient 57 1 (constantCoefficient s) = s := by
  apply globalOn_injective
  change globalOn _ Finset.univ (by simp) = _
  rw [globalOn_scalar]
  exact (eq_scalar_of_nonnegative _ (globalOn_weight s) (globalOn_nonnegative s)).symm

/-- The original structure morphism identifies global regular functions with ℂ. -/
def globalFunctionsEquiv : ℂ ≃+* Γ(Surface, ⊤) where
  __ := projectiveGlobalCoefficient 57 1
  invFun := constantCoefficient
  left_inv := constantCoefficient_scalar
  right_inv := scalar_constantCoefficient


open TopologicalSpace CycleQ2GeometricSheafCohomologyScalar CycleQ2SurfaceCechTwoScalar

private abbrev Forms := CycleQ2CanonicalResidueSheaf.CanonicalForms
local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The endomorphism of the canonical sheaf induced by a global function. -/
def canonicalFunctionEnd (s : Γ(Surface, ⊤)) : CanonicalSheaf ⟶ CanonicalSheaf :=
  scalarEnd Surface.sheaf (surfaceGlobalCoefficient 57 1) Forms (constantCoefficient s)

local instance (U : Surface.Opens) : Module Γ(Surface, U) (CanonicalSheaf.obj.obj (op U)) :=
  (Forms.val.obj (op U)).isModule

/-- On every open this endomorphism multiplies by the actual restricted function. -/
theorem canonicalFunctionEnd_apply (s : Γ(Surface, ⊤)) (U : Surface.Opens)
    (x : CanonicalSheaf.obj.obj (op U)) :
    (canonicalFunctionEnd s).hom.app (op U) x =
      Surface.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s • x := by
  change Surface.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (projectiveGlobalCoefficient 57 1 (constantCoefficient s)) • x = _
  rw [scalar_constantCoefficient]

/-- Cohomology of multiplication by a regular function on this surface. -/
def canonicalFunctionH2 (s : Γ(Surface, ⊤)) :
    CanonicalSheaf.H' 2 ⊤ →+ CanonicalSheaf.H' 2 ⊤ :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Surface) 2).map
    (canonicalFunctionEnd s)).app (op ⊤)).hom

theorem canonicalFunctionH2_apply (s : Γ(Surface, ⊤)) (x : CanonicalSheaf.H' 2 ⊤) :
    canonicalFunctionH2 s x = (constantCoefficient s) • x := rfl

end CycleQ2LiteralGlobalFunctions
end

#print axioms CycleQ2LiteralGlobalFunctions.globalFunctionsEquiv
#print axioms CycleQ2LiteralGlobalFunctions.canonicalFunctionEnd_apply
#print axioms CycleQ2LiteralGlobalFunctions.canonicalFunctionH2_apply
