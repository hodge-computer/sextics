import Proposal.GeometricDerivationTransport
import Proposal.GeometricAffineChartSections
import Proposal.GeometricDifferentialRestriction
import Proposal.GeometricSheafKaehlerMap

/-!
# An actual differential frame transported through an affine scheme chart

The coefficient derivation is transported through the actual section-ring
isomorphisms on all subopens. Its universal lift is inverse to the section
obtained from the ordinary affine Kähler frame. The inverse generator is
identified explicitly, including its restrictions to every subopen.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricDifferentialChartTransport

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricDifferentialRestriction
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricAffineChartSections
  CycleQ2GeometricSheafKaehlerMap

abbrev chartSourceRingSheaf (X : Scheme.{0}) (U : X.Opens) :
    Sheaf ((Opens.grothendieckTopology X).over U) CommRingCat.{0} := X.sheaf.over U

def chartTop {X : Scheme.{0}} (U : X.Opens) : Over U := Over.mk (𝟙 U)

def toChartTop {X : Scheme.{0}} {U : X.Opens} (V : Over U) : V ⟶ chartTop U :=
  Over.homMk V.hom (by simp [chartTop])

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

abbrev ChartModule := OverModule X.sheaf U
abbrev ChartDerivation (M : ChartModule (X := X) (U := U)) :=
  OverDerivation X.sheaf (schemeCoefficient f) U M
abbrev ChartStructureModule : ChartModule (X := X) (U := U) :=
  SheafOfModules.unit ((ringSheaf X.sheaf).over U)
abbrev ChartDifferentialModule : ChartModule (X := X) (U := U) :=
  (differentialSheaf X.sheaf (schemeCoefficient f)).over U

omit [Algebra ℂ A] in
private theorem inverseRingIso_chartSection (W : (Opens (Spec (CommRingCat.of A)))ᵒᵖ) (a : A) :
    (CycleQ2GeometricDerivationTransport.inverseRingIso
      (chartSourceRingSheaf X U) (Spec.structureSheaf A) (chartOpensEquiv e)
      (chartSectionsIso e)).hom.app W (algebraMap A (AffineSections A W.unop) a) =
      chartSection e ((chartOpensEquiv e).inverse.obj W.unop) a := by
  rw [CycleQ2GeometricDerivationTransport.inverseRingIso_apply]
  rfl

include h in
/-- Natural complex derivations on the actual chart are determined by
the actual affine ring, mapped to sections on the terminal chart open. -/
theorem chartDerivation_ext (M : ChartModule (X := X) (U := U))
    (d₁ d₂ : ChartDerivation f M)
    (hd : ∀ a : A, d₁.d (X := op (chartTop U)) (chartSection e (chartTop U) a) =
      d₂.d (X := op (chartTop U)) (chartSection e (chartTop U) a)) : d₁ = d₂ := by
  let : (chartOpensEquiv e).inverse.IsContinuous
      (Opens.grothendieckTopology (PrimeSpectrum.Top A))
      ((Opens.grothendieckTopology X).over U) := chartOpensInverse_continuous e
  apply CycleQ2GeometricDerivationTransport.inverseDerivation_injective
    (chartSourceRingSheaf X U) (Spec.structureSheaf A) (chartOpensEquiv e)
    (chartSectionsIso e) (overCoefficient X.sheaf (schemeCoefficient f) U)
    (coefficientMap (Spec.structureSheaf A) (affineCoefficient A))
    (fun V c => chartSectionsIso_coefficient e f h V.unop c) M
  apply affineDerivation_ext
  intro a
  change d₁.d ((CycleQ2GeometricDerivationTransport.inverseRingIso
      (chartSourceRingSheaf X U) (Spec.structureSheaf A) (chartOpensEquiv e)
      (chartSectionsIso e)).hom.app (op ⊤) (algebraMap A (AffineSections A ⊤) a)) =
    d₂.d ((CycleQ2GeometricDerivationTransport.inverseRingIso
      (chartSourceRingSheaf X U) (Spec.structureSheaf A) (chartOpensEquiv e)
      (chartSectionsIso e)).hom.app (op ⊤) (algebraMap A (AffineSections A ⊤) a))
  rw [inverseRingIso_chartSection]
  let V := (chartOpensEquiv e).inverse.obj ⊤
  have hn := chartSection_naturality e (toChartTop V) a
  have h₁ := (congrArg (d₁.d (X := op V)) hn).symm.trans
    (d₁.d_map (toChartTop V).op (chartSection e (chartTop U) a))
  have h₂ := (congrArg (d₂.d (X := op V)) hn).symm.trans
    (d₂.d_map (toChartTop V).op (chartSection e (chartTop U) a))
  exact h₁.trans ((congrArg (M.val.map (toChartTop V).op) (hd a)).trans h₂.symm)

variable (frame : KaehlerDifferential ℂ A ≃ₗ[A] A)

/-- The genuine derivation of actual chart sections associated with the
affine Kähler frame. -/
def chartCoefficientDerivation :
    ChartDerivation f (ChartStructureModule (X := X) (U := U)) :=
  CycleQ2GeometricDerivationTransport.structureDerivation
    (chartSourceRingSheaf X U) (Spec.structureSheaf A) (chartOpensEquiv e)
    (chartSectionsIso e) (overCoefficient X.sheaf (schemeCoefficient f) U)
    (coefficientMap (Spec.structureSheaf A) (affineCoefficient A))
    (fun V c => chartSectionsIso_coefficient e f h V.unop c)
    (regularSectionDerivation frame)

theorem chartCoefficientDerivation_section (V : Over U) (a : A) :
    (chartCoefficientDerivation e f h frame).d (X := op V) (chartSection e V a) =
      chartSection e V (frame (KaehlerDifferential.D ℂ A a)) := by
  change (chartSectionIso e V).inv
    (sectionDerivative frame ((chartOpensEquiv e).functor.obj V)
      ((chartSectionIso e V).hom ((chartSectionIso e V).inv
        (algebraMap A (AffineSections A ((chartOpensEquiv e).functor.obj V)) a)))) = _
  rw [Iso.inv_hom_id_apply, sectionDerivative_algebraMap]
  rfl

def chartCoefficientMap : ChartDifferentialModule f ⟶ ChartStructureModule (X := X) (U := U) :=
  restrictedLift X.sheaf (schemeCoefficient f) U (ChartStructureModule (X := X) (U := U))
    (chartCoefficientDerivation e f h frame)

theorem chartCoefficientMap_D (V : Over U) (s : Γ(X, V.left)) :
    (chartCoefficientMap e f h frame).val.app (op V)
        ((universalDifferential X.sheaf (schemeCoefficient f)).d (X := op V.left) s) =
      (chartCoefficientDerivation e f h frame).d (X := op V) s :=
  PresheafOfModules.Derivation.congr_d
    (restrictedLift_fac X.sheaf (schemeCoefficient f) U
      (ChartStructureModule (X := X) (U := U)) (chartCoefficientDerivation e f h frame)) s

/-- The inverse generator is the ordinary universal image of the original
affine Kähler frame; it is not a newly chosen local basis. -/
def chartFrameSection : (differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op U) :=
  sectionLift X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) U
    (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U)) (frame.symm 1)

def sectionsFromChart (M : ChartModule (X := X) (U := U)) (m : M.val.obj (op (chartTop U))) :
    M.sections :=
  M.val.sectionsMk (fun V => M.val.map (toChartTop V.unop).op m)
    (fun V W g => by rw [← M.val.map_comp_apply]; congr 2)

def unitMapFromChart (M : ChartModule (X := X) (U := U)) (m : M.val.obj (op (chartTop U))) :
    ChartStructureModule (X := X) (U := U) ⟶ M :=
  M.unitHomEquiv.symm (sectionsFromChart M m)

theorem unitMapFromChart_apply (M : ChartModule (X := X) (U := U))
    (m : M.val.obj (op (chartTop U))) (V : (Over U)ᵒᵖ) (a : Γ(X, V.unop.left)) :
    (unitMapFromChart M m).val.app V a = a • M.val.map (toChartTop V.unop).op m := rfl

theorem unitMapFromChart_top (M : ChartModule (X := X) (U := U))
    (m : M.val.obj (op (chartTop U))) (a : Γ(X, U)) :
    (unitMapFromChart M m).val.app (op (chartTop U)) a = a • m := by
  rw [unitMapFromChart_apply]
  have hm : M.val.map (toChartTop (chartTop U)).op m = m := by
    change M.val.presheaf.map (𝟙 (op (chartTop U))) m = m
    exact congrArg (fun k : M.val.presheaf.obj (op (chartTop U)) ⟶
      M.val.presheaf.obj (op (chartTop U)) => k m) (M.val.presheaf.map_id _)
  exact congrArg (fun z : M.val.obj (op (chartTop U)) => a • z) hm

def chartFrameMap : ChartStructureModule (X := X) (U := U) ⟶ ChartDifferentialModule f :=
  unitMapFromChart (ChartDifferentialModule f) (chartFrameSection e f h frame)

theorem chartCoefficientMap_sectionLift (ω : KaehlerDifferential ℂ A) :
    (chartCoefficientMap e f h frame).val.app (op (chartTop U))
        (sectionLift X.sheaf (schemeCoefficient f)
          (differentialSheaf X.sheaf (schemeCoefficient f))
          (universalDifferential X.sheaf (schemeCoefficient f)) U
          (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U)) ω) =
      chartSection e (chartTop U) (frame ω) := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [sectionLift_D]
      exact (chartCoefficientMap_D e f h frame (chartTop U)
        (chartSection e (chartTop U) a)).trans
          (chartCoefficientDerivation_section e f h frame (chartTop U) a)
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [sectionLift_smul, ((chartCoefficientMap e f h frame).val.app (op (chartTop U))).hom.map_smul,
        hx]
      change chartSection e (chartTop U) a * chartSection e (chartTop U) (frame x) =
        chartSection e (chartTop U) (frame (a • x))
      rw [frame.map_smul]
      exact (map_mul (chartSection e (chartTop U)) a (frame x)).symm

theorem chartCoefficientMap_frameSection :
    (chartCoefficientMap e f h frame).val.app (op (chartTop U))
      (chartFrameSection e f h frame) = (1 : Γ(X, U)) := by
  have hc := chartCoefficientMap_sectionLift e f h frame (frame.symm 1)
  simpa only [chartFrameSection, LinearEquiv.apply_symm_apply, map_one] using hc

theorem chartFrameMap_coefficientMap :
    chartFrameMap e f h frame ≫ chartCoefficientMap e f h frame =
      𝟙 (ChartStructureModule (X := X) (U := U)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (chartCoefficientMap e f h frame).val.app V
    ((unitMapFromChart (ChartDifferentialModule f) (chartFrameSection e f h frame)).val.app V a) = a
  rw [unitMapFromChart_apply, map_smul, PresheafOfModules.naturality_apply,
    chartCoefficientMap_frameSection]
  change (show Γ(X, V.unop.left) from a) * X.presheaf.map V.unop.hom.op (1 : Γ(X, U)) = a
  rw [map_one, mul_one]

theorem chartCoefficientMap_frameMap :
    chartCoefficientMap e f h frame ≫ chartFrameMap e f h frame =
      𝟙 (ChartDifferentialModule f) := by
  apply restrictedLift_unique X.sheaf (schemeCoefficient f) U
  apply chartDerivation_ext e f h
  intro a
  change (unitMapFromChart (ChartDifferentialModule f) (chartFrameSection e f h frame)).val.app
      (op (chartTop U)) ((chartCoefficientMap e f h frame).val.app (op (chartTop U))
        ((universalDifferential X.sheaf (schemeCoefficient f)).d
          (chartSection e (chartTop U) a))) =
    (universalDifferential X.sheaf (schemeCoefficient f)).d (chartSection e (chartTop U) a)
  have hc := (chartCoefficientMap_D e f h frame (chartTop U)
    (chartSection e (chartTop U) a)).trans
      (chartCoefficientDerivation_section e f h frame (chartTop U) a)
  refine (congrArg (fun z : Γ(X, U) =>
    (unitMapFromChart (ChartDifferentialModule f) (chartFrameSection e f h frame)).val.app
      (op (chartTop U)) z) hc).trans ?_
  rw [unitMapFromChart_top]
  change chartSection e (chartTop U) (frame (KaehlerDifferential.D ℂ A a)) •
      sectionLift X.sheaf (schemeCoefficient f)
        (differentialSheaf X.sheaf (schemeCoefficient f))
        (universalDifferential X.sheaf (schemeCoefficient f)) U
        (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U)) (frame.symm 1) = _
  have he : frame (KaehlerDifferential.D ℂ A a) • frame.symm 1 = KaehlerDifferential.D ℂ A a := by
    apply frame.injective
    rw [frame.map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  exact (sectionLift_smul X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) U
    (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U))
    (frame (KaehlerDifferential.D ℂ A a)) (frame.symm 1)).symm.trans
      ((congrArg (sectionLift X.sheaf (schemeCoefficient f)
        (differentialSheaf X.sheaf (schemeCoefficient f))
        (universalDifferential X.sheaf (schemeCoefficient f)) U
        (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U))) he).trans
          (sectionLift_D X.sheaf (schemeCoefficient f)
            (differentialSheaf X.sheaf (schemeCoefficient f))
            (universalDifferential X.sheaf (schemeCoefficient f)) U
            (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U)) a))

/-- An actual affine scheme chart and a frame of its actual Kähler module
give a frame of the actual differential sheaf on the restricted over-site. -/
def chartFrameIso : ChartDifferentialModule f ≅ ChartStructureModule (X := X) (U := U) where
  hom := chartCoefficientMap e f h frame
  inv := chartFrameMap e f h frame
  hom_inv_id := chartCoefficientMap_frameMap e f h frame
  inv_hom_id := chartFrameMap_coefficientMap e f h frame

theorem chartFrameIso_inv_one :
    (chartFrameIso e f h frame).inv.val.app (op (chartTop U)) (1 : Γ(X, U)) =
      chartFrameSection e f h frame := by
  change (unitMapFromChart (ChartDifferentialModule f)
    (chartFrameSection e f h frame)).val.app (op (chartTop U)) (1 : Γ(X, U)) = _
  rw [unitMapFromChart_top, one_smul]

theorem chartFrameIso_inv_one_subopen (V : Over U) :
    (chartFrameIso e f h frame).inv.val.app (op V) (1 : Γ(X, V.left)) =
      sectionLift X.sheaf (schemeCoefficient f)
        (differentialSheaf X.sheaf (schemeCoefficient f))
        (universalDifferential X.sheaf (schemeCoefficient f)) V.left
        (chartSection e V) (chartSection_complex e f h V) (frame.symm 1) := by
  change (unitMapFromChart (ChartDifferentialModule f)
    (chartFrameSection e f h frame)).val.app (op V) (1 : Γ(X, V.left)) = _
  rw [unitMapFromChart_apply, one_smul]
  exact sectionLift_restriction X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) U
    (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U))
    V.left V.hom.le (chartSection e V) (chartSection_complex e f h V)
    (chartSection_naturality e (toChartTop V)) (frame.symm 1)

end CycleQ2GeometricDifferentialChartTransport
end
