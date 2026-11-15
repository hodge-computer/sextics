import Proposal.GeometricSeedSectionSheafTwist
import Proposal.GeometricSeedSectionBalance

/-!
# The original linkage balance after actual chart transport

The associated-sheaf multiplication maps are identified with multiplication
in the actual structure sheaf.  The square is transported through the
original affine chart isomorphism, retaining its actual coefficient map.
This gives the linkage balance for the evaluation morphisms of the fixed
global twisted source, before using it to glue their outputs.

Source-only draft: no elaboration or kernel replay was run.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafEvaluation

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageCocycle
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricAffineChartSections
  CycleQ2SeedSectionSheaf CycleQ2SeedSectionSheafSections CycleQ2SeedSectionBalance

section ScalarTransport

variable {R : Type} [CommRing R]

theorem iso_app_hom_inv {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (s : Γ(M, U)) : e.inv.app U (e.hom.app U s) = s :=
  congrArg (fun f : M ⟶ M => f.app U s) e.hom_inv_id

theorem iso_app_inv_hom {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) (s : Γ(N, U)) : e.hom.app U (e.inv.app U s) = s :=
  congrArg (fun f : N ⟶ N => f.app U s) e.inv_hom_id

theorem iso_app_injective {X : Scheme.{0}} {M N : X.Modules} (e : M ≅ N)
    (U : X.Opens) : Function.Injective (e.hom.app U) := by
  intro s t hst
  have h := congrArg (e.inv.app U) hst
  simpa only [iso_app_hom_inv] using h

/-- Associated-sheaf multiplication has the actual affine coefficient
given by ΓSpecIso, including on nonprincipal opens. -/
theorem tilde_scalarMap_structure (a : R) :
    tilde.map (scalarMap a) =
      structureScalar (Spec (CommRingCat.of R))
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  rw [tilde_scalarMap_app, structureScalar_app, Scheme.Modules.smul_Spec_def] <;> rfl

/-- The actual open-immersion structure-module isomorphism intertwines
multiplication with the ordinary pullback of the global coefficient. -/
theorem restrict_structureScalar {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsOpenImmersion f] (a : Γ(Y, ⊤)) :
    (Scheme.Modules.restrictFunctor f).map (structureScalar Y a) ≫
        (Scheme.Modules.restrictUnitIso f).hom =
      (Scheme.Modules.restrictUnitIso f).hom ≫ structureScalar X (f.appTop a) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  change (f.appIso U).hom
      (Y.presheaf.map (homOfLE (show f ''ᵁ U ≤ ⊤ from le_top)).op a * s) =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (f.appTop a) *
      (f.appIso U).hom s
  rw [map_mul]
  congr 1
  have h : Y.presheaf.map (homOfLE (show f ''ᵁ U ≤ ⊤ from le_top)).op ≫
      (f.appIso U).hom =
    f.appTop ≫ X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE] <;> rfl
  exact ConcreteCategory.congr_hom h a

end ScalarTransport

def chartCoefficient (i : Fin 3) (a : AffineRing i) : Γ((Patch i).toScheme, ⊤) :=
  (coordinateAffineChart 57 1 i.succ).hom.appTop
    ((Scheme.ΓSpecIso (CommRingCat.of (AffineRing i))).inv a)

/-- The native chart coefficient is the original chartSectionMap under
the canonical global-section isomorphism of the open subscheme. -/
theorem chartCoefficient_top (i : Fin 3) (a : AffineRing i) :
    (Patch i).topIso.inv (chartSectionMap i (Patch i) le_rfl a) = chartCoefficient i a := by
  have h := ConcreteCategory.congr_hom
    (chartSection_top (coordinateAffineChart 57 1 i.succ)) a
  change chartSectionMap i (Patch i) le_rfl a =
    (Patch i).topIso.hom (chartCoefficient i a) at h
  rw [h]
  exact Iso.hom_inv_id_apply (Patch i).topIso _

theorem chartSectionMap_restrict (i : Fin 3) (V W : Surface.Opens)
    (hWV : W ≤ V) (hi : V ≤ Patch i) (a : AffineRing i) :
    Surface.presheaf.map (homOfLE hWV).op (chartSectionMap i V hi a) =
      chartSectionMap i W (hWV.trans hi) a := by
  exact chartSection_naturality (coordinateAffineChart 57 1 i.succ)
    (Over.homMk (homOfLE hWV)) a

def chartScalar (i : Fin 3) (a : AffineRing i) :
    structureModule (Patch i).toScheme ⟶ structureModule (Patch i).toScheme :=
  structureScalar (Patch i).toScheme (chartCoefficient i a)

theorem chartScalar_square (i : Fin 3) (a : AffineRing i) :
    (Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).map
        (tilde.map (scalarMap a)) ≫
        (Scheme.Modules.restrictUnitIso (coordinateAffineChart 57 1 i.succ).hom).hom =
      (Scheme.Modules.restrictUnitIso (coordinateAffineChart 57 1 i.succ).hom).hom ≫
        chartScalar i a := by
  rw [tilde_scalarMap_structure]
  exact restrict_structureScalar (coordinateAffineChart 57 1 i.succ).hom _

def patchScalar (i : Fin 3) (a : AffineRing i) :
    patchStructure (Patch i) ⟶ patchStructure (Patch i) :=
  (Scheme.Modules.pushforward (Patch i).ι).map (chartScalar i a)

/-- The balance remains an equality of genuine chart sheaf morphisms. -/
theorem chartEvaluation_balance (t : Fin 3 → ℂ) (i : Fin 3) :
    chartEvaluation t i ≫ chartScalar i (chartFactorData i).linkage =
      chartInclusion i ≫ chartScalar i
        (∑ b, algebraMap ℂ (AffineRing i) (t b) * (chartFactorData i).right b) := by
  let T := Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom
  let u := (Scheme.Modules.restrictUnitIso (coordinateAffineChart 57 1 i.succ).hom).hom
  change (T.map (tilde.map (functionalMap (chartFactorData i)
      (fun b => algebraMap ℂ (AffineRing i) (t b)))) ≫ u) ≫
      chartScalar i (chartFactorData i).linkage =
    (T.map (tilde.map (idealInclusion (chartFactorData i))) ≫ u) ≫
      chartScalar i (∑ b, algebraMap ℂ (AffineRing i) (t b) * (chartFactorData i).right b)
  rw [Category.assoc, ← chartScalar_square, ← Category.assoc,
    ← Functor.map_comp, tilde_balance, Functor.map_comp, Category.assoc,
    chartScalar_square, ← Category.assoc]

theorem patchEvaluation_balance (t : Fin 3 → ℂ) (i : Fin 3) :
    patchEvaluation t i ≫ patchScalar i (chartFactorData i).linkage =
      idealPatchInclusion i ≫ patchScalar i
        (∑ b, algebraMap ℂ (AffineRing i) (t b) * (chartFactorData i).right b) := by
  rw [patchEvaluation, idealPatchInclusion, patchScalar, patchScalar,
    ← Functor.map_comp, ← Functor.map_comp, chartEvaluation_balance]

/-- Regularity of the actual linkage multiplication survives transport
to every open of the original projective coordinate chart. -/
theorem chartScalar_linkage_app_injective (i : Fin 3) (U : (Patch i).toScheme.Opens) :
    Function.Injective ((chartScalar i (chartFactorData i).linkage).app U) := by
  let e := (Scheme.Modules.restrictUnitIso (coordinateAffineChart 57 1 i.succ).hom)
  intro s t hst
  apply iso_app_injective e.symm U
  have hs := congrArg (fun k => k.app U (e.inv.app U s))
    (chartScalar_square i (chartFactorData i).linkage)
  have ht := congrArg (fun k => k.app U (e.inv.app U t))
    (chartScalar_square i (chartFactorData i).linkage)
  change e.hom.app U
      (((Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).map
        (tilde.map (scalarMap (chartFactorData i).linkage))).app U (e.inv.app U s)) =
    (chartScalar i (chartFactorData i).linkage).app U (e.hom.app U (e.inv.app U s)) at hs
  change e.hom.app U
      (((Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).map
        (tilde.map (scalarMap (chartFactorData i).linkage))).app U (e.inv.app U t)) =
    (chartScalar i (chartFactorData i).linkage).app U (e.hom.app U (e.inv.app U t)) at ht
  rw [iso_app_inv_hom] at hs ht
  have hc :
      ((Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).map
          (tilde.map (scalarMap (chartFactorData i).linkage))).app U (e.inv.app U s) =
      ((Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).map
          (tilde.map (scalarMap (chartFactorData i).linkage))).app U (e.inv.app U t) := by
    apply iso_app_injective e U
    exact hs.trans (hst.trans ht.symm)
  exact tilde_linkage_app_injective (chartFactorData i)
    ((coordinateAffineChart 57 1 i.succ).hom ''ᵁ U) hc

theorem patchScalar_linkage_app_injective (i : Fin 3) (V : Surface.Opens) :
    Function.Injective ((patchScalar i (chartFactorData i).linkage).app V) :=
  chartScalar_linkage_app_injective i ((Patch i).ι ⁻¹ᵁ V)

/-- The chart scalar is normalized by the same original coefficient
map used by the original linkage and matrix equations. -/
theorem patchScalar_eq (i : Fin 3) (a : AffineRing i) :
    patchScalar i a = CycleQ2SeedSectionSheafTwist.patchScalar (Patch i)
      (chartSectionMap i (Patch i) le_rfl a) := by
  unfold patchScalar chartScalar CycleQ2SeedSectionSheafTwist.patchScalar
  rw [chartCoefficient_top]

theorem patchScalar_coordinate (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (a : AffineRing i) (y : Γ(patchStructure (Patch i), V)) :
    patchSectionsEquiv (Patch i) V hi ((patchScalar i a).app V y) =
      chartSectionMap i V hi a * patchSectionsEquiv (Patch i) V hi y := by
  rw [patchScalar_eq, CycleQ2SeedSectionSheafTwist.patchSectionsEquiv_scalar,
    chartSectionMap_restrict]

/-- The original linkage element is regular in the actual section ring
of every projective subopen of its chart. No localization hypothesis on
the subopen is supplied by a caller. -/
theorem sectionLinkage_isSMulRegular (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) : IsSMulRegular Γ(Surface, V) (sectionLinkage i V hi) := by
  intro a b hab
  let e := patchSectionsEquiv (Patch i) V hi
  have h : (patchScalar i (chartFactorData i).linkage).app V (e.symm a) =
      (patchScalar i (chartFactorData i).linkage).app V (e.symm b) := by
    apply e.injective
    rw [patchScalar_coordinate, patchScalar_coordinate]
    simpa only [e, RingEquiv.apply_symm_apply, sectionLinkage, smul_eq_mul] using hab
  exact e.symm.injective (patchScalar_linkage_app_injective i V h)

/-- Balance for the actual global source section in the actual original
projective section ring, retaining the same original t. -/
theorem evaluatedCoordinate_balance (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (s : Γ(twistedIdeal, V)) :
    sectionLinkage i V hi * evaluatedCoordinate t i V hi s =
      sourceCoordinate i V hi s * sectionRightCombination t i V hi := by
  have h := congrArg
    (fun f : idealPatch i ⟶ patchStructure (Patch i) =>
      f.app V ((chartProjection i).app V s)) (patchEvaluation_balance t i)
  have h' := congrArg (patchSectionsEquiv (Patch i) V hi) h
  change patchSectionsEquiv (Patch i) V hi
      ((patchScalar i (chartFactorData i).linkage).app V
        ((patchEvaluation t i).app V ((chartProjection i).app V s))) =
    patchSectionsEquiv (Patch i) V hi
      ((patchScalar i (∑ b, algebraMap ℂ (AffineRing i) (t b) *
        (chartFactorData i).right b)).app V
        ((idealPatchInclusion i).app V ((chartProjection i).app V s))) at h'
  rw [patchScalar_coordinate, patchScalar_coordinate] at h'
  exact h'.trans (mul_comm _ _)

/-- The outputs of the original local functionals agree on every common
subopen. The proof cancels the actual regular linkage section after using
the prescribed source twist and the degree-eight right-generator change. -/
theorem evaluatedCoordinate_compatible (t : Fin 3 → ℂ) (i j : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (hj : V ≤ Patch j)
    (s : Γ(twistedIdeal, V)) :
    evaluatedCoordinate t i V hi s = evaluatedCoordinate t j V hj s := by
  apply sectionLinkage_isSMulRegular j V hj
  change sectionLinkage j V hj * evaluatedCoordinate t i V hi s =
    sectionLinkage j V hj * evaluatedCoordinate t j V hj s
  calc
    _ = (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 4 *
        (sectionLinkage i V hi * evaluatedCoordinate t i V hi s) := by
      rw [sectionLinkage_change i j V hi hj]
      ring
    _ = (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 4 *
        (sourceCoordinate i V hi s * sectionRightCombination t i V hi) := by
      rw [evaluatedCoordinate_balance]
    _ = sourceCoordinate j V hj s *
        ((transitionUnit i j V hi hj : Γ(Surface, V)) ^ 8 *
          sectionRightCombination t i V hi) := by
      rw [CycleQ2SeedSectionSheafTwist.sourceCoordinate_transition i j V hi hj s]
      ring
    _ = sourceCoordinate j V hj s * sectionRightCombination t j V hj := by
      rw [sectionRightCombination_change t i j V hi hj]
    _ = _ := (evaluatedCoordinate_balance t j V hj s).symm

end CycleQ2SeedSectionSheafEvaluation

end

#print axioms CycleQ2SeedSectionSheafEvaluation.chartEvaluation_balance
#print axioms CycleQ2SeedSectionSheafEvaluation.patchEvaluation_balance
#print axioms CycleQ2SeedSectionSheafEvaluation.patchScalar_linkage_app_injective
#print axioms CycleQ2SeedSectionSheafEvaluation.evaluatedCoordinate_balance
#print axioms CycleQ2SeedSectionSheafEvaluation.evaluatedCoordinate_compatible
