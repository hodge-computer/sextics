import Proposal.GeometricLiteralAbelJacobiTimeCharts
import Proposal.GeometricLiteralCylinderEvaluation
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The closed curve inside the cylinder and its infinitesimal germ

The original specialized projective curve sits in the actual time family.
Its inclusion factors through the closed fibre of the retained tangent germ.
On each of the four affine charts this factorization is the original quotient
by epsilon, with square-zero kernel.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationFiber

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2LiteralAbelJacobiTimeCharts CycleQ2LiteralAbelJacobiTimeProjection
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralIncidenceTimeCurve
  CycleQ2FirstOrderCurve CycleQ2FirstOrderCurveSeedFiber CycleQ2FirstOrderCurveCharts
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceFirstOrder CycleQ2IncidenceChartFiberScheme
  CycleQ2IncidenceSeedFiberCover CycleQ2IncidenceTraceFamily
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2RelativeConstantCurve
  CycleQ2RelativeCurveChart CycleQ2RelativeCurveSeedProj CycleQ2RelativeCurveSeedFiberIso
  CycleQ2RelativeCurveSeedChart CycleQ2RelativeCurveChartScheme CycleQ2RelativeCurveChartFiber
  CycleQ2SpecializedCurveCoordinateChart CycleQ2SpecializedProjectiveCurve
  CycleQ2FirstOrderChartFlatness CycleQ2FirstOrderChartReduction
  CycleQ2FirstOrderNeighborhood CycleQ2DualNumberRegularQuotient
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralCylinderEvaluation

open scoped DualNumber TensorProduct

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralAbelJacobiMovingNormal.thickCommRing
  CycleQ2LiteralAbelJacobiMovingNormal.closedCommRing

private abbrev seedPt := seedPoint (57 : ℂ) Complex.I

private instance : IsClosedImmersion firstOrderClosedPoint :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) (fun z => ⟨TrivSqZeroExt.inl z, rfl⟩)

private instance : Surjective firstOrderClosedPoint :=
  ⟨fun x => ⟨default, (firstOrderPoint_eq_closedPoint x).symm⟩⟩

/-- The full epsilon direction and every scalar are in the original parameter chart. -/
private theorem firstOrderMap_surjective : Function.Surjective firstOrderMap := by
  intro x
  refine ⟨algebraMap ℂ ParameterAlgebra x.fst + algebraMap ℂ ParameterAlgebra x.snd *
    algebraMap TraceRing ParameterAlgebra traceParameter, ?_⟩
  rw [map_add, map_mul, firstOrderMap.commutes, firstOrderMap.commutes, firstOrderMap_traceParameter]
  apply TrivSqZeroExt.ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

private instance : IsClosedImmersion firstOrderParameterPoint :=
  IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom firstOrderMap.toRingHom) firstOrderMap_surjective

variable (t : Fin 3 → ℂ)

instance : IsClosedImmersion (seedCurveToFirstOrderCurve t) := by
  rw [← firstOrderCurveSeedFiberIso_hom_snd]
  infer_instance

instance : Surjective (seedCurveToFirstOrderCurve t) := by
  have : Surjective (pullback.snd firstOrderClosedPoint (firstOrderCurveToBase t)) :=
    MorphismProperty.pullback_snd _ _ (show Surjective firstOrderClosedPoint by infer_instance)
  rw [← firstOrderCurveSeedFiberIso_hom_snd]
  infer_instance

/-- The seed inclusion induces a homeomorphism on underlying spaces. -/
theorem seed_germ_homeomorph : IsHomeomorph (seedCurveToFirstOrderCurve t) :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(seedCurveToFirstOrderCurve t).isClosedEmbedding.isEmbedding, (seedCurveToFirstOrderCurve t).surjective⟩

theorem germ_preimage_coordinate (i : Fin 4) :
    seedCurveToFirstOrderCurve t ⁻¹ᵁ firstOrderCurveCoordinateOpen t i = specializedCoordinatePatch seedPt t i := by
  rw [firstOrderCurveCoordinateOpen, firstOrderChartToCurve_opensRange,
    ← Scheme.Hom.comp_preimage, seedCurveToFirstOrderCurve_original, seedCurveToRelative_preimage_coordinatePatch]

theorem seed_coordinate_cover : (⨆ i : Fin 4, specializedCoordinatePatch seedPt t i) = ⊤ := by
  simp only [← germ_preimage_coordinate, ← Scheme.Hom.preimage_iSup, iSup_firstOrderCurveCoordinateOpen,
    Scheme.Hom.preimage_top]

/-- The actual affine model of the seed projective curve. -/
def seedChart (i : Fin 4) : Spec (CommRingCat.of (A t i)) ⟶ specializedCurve seedPt t :=
  (specializedCoordinateAffineChart seedPt t i).inv ≫ (specializedCoordinatePatch seedPt t i).ι

instance (i : Fin 4) : IsOpenImmersion (seedChart t i) := by
  unfold seedChart
  infer_instance

theorem seedChart_opensRange (i : Fin 4) : (seedChart t i).opensRange = specializedCoordinatePatch seedPt t i := by
  dsimp only [seedChart]
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact (specializedCoordinatePatch seedPt t i).opensRange_ι

theorem toClosed_surjective (i : Fin 4) : Function.Surjective (toClosed t i) :=
  (curveChartReductionEquiv t i).surjective.comp Ideal.Quotient.mk_surjective

theorem toClosed_ker (i : Fin 4) : RingHom.ker (toClosed t i) = epsilonIdeal (k := ℂ) (B t i) := by
  rw [toClosed, RingHom.ker_comp_of_injective _ (curveChartReductionEquiv t i).injective, Ideal.mk_ker]

theorem toClosed_ker_sq (i : Fin 4) : RingHom.ker (toClosed t i) ^ 2 = ⊥ := by
  rw [toClosed_ker, epsilonIdeal, Ideal.span_singleton_pow, ← map_pow, pow_two, DualNumber.eps_mul_eps,
    map_zero, Ideal.span_singleton_zero]

/-- Reducing the genuine infinitesimal affine chart gives the global seed immersion. -/
@[reassoc] theorem seedChart_to_germ (i : Fin 4) :
    seedChart t i ≫ seedCurveToFirstOrderCurve t =
      Spec.map (CommRingCat.ofHom (toClosed t i)) ≫ firstOrderChartToCurve t i := by
  have : Mono (firstOrderCurveToOriginalCurve t) := (firstOrderCurve_isPullback t).mono_fst_of_mono
  apply (cancel_mono (firstOrderCurveToOriginalCurve t)).mp
  rw [Category.assoc, seedCurveToFirstOrderCurve_original, seedChart, Category.assoc,
    seedCurveToRelative_on_coordinateChart, Category.assoc, firstOrderChartToCurve_original,
    tensorChartToOriginal, ← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom (curveChartSpecialization t i)) ≫ originalCurveChart t i =
    Spec.map (CommRingCat.ofHom ((toClosed t i).comp _)) ≫ originalCurveChart t i
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ originalCurveChart t i)
    (RingHom.ext (fun a => (curveChartReductionEquiv_includeRight t i a).symm))

/-- The affine square on the original seed and tangent schemes is Cartesian. -/
theorem affine_reduction_isPullback (i : Fin 4) :
    IsPullback (Spec.map (CommRingCat.ofHom (toClosed t i))) (seedChart t i)
      (firstOrderChartToCurve t i) (seedCurveToFirstOrderCurve t) := by
  apply IsOpenImmersion.isPullback _ _ _ _ (seedChart_to_germ t i)
  exact (germ_preimage_coordinate t i).trans (seedChart_opensRange t i).symm

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

def seedToTime : specializedCurve seedPt t ⟶ family V t :=
  (seedIso V t hV).hom ≫ pullback.snd _ _

def germToTime : firstOrderCurve t ⟶ family V t :=
  (firstOrderIso V t hV).hom ≫ pullback.snd _ _

private instance : IsClosedImmersion (seedLift V hV) :=
  isClosedImmersion_of_comp_eq_id ((timeOpen V).ι ≫ toComplex) (seedLift V hV) (by
    rw [seedLift_fac_assoc]
    exact pullback.lift_fst _ _ _)

instance : IsClosedImmersion (seedToTime t V hV) := by
  unfold seedToTime
  infer_instance

private theorem seedToTime_toOriginal :
    seedToTime t V hV ≫ familyToFull V t ≫ CycleQ2LiteralIncidenceTimeFamily.toOriginal t =
      seedCurveToRelative t := by
  simp only [seedToTime, seedIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc (pullback.snd (seedLift V hV) (projection V t)) (familyToFull V t),
    IsPullback.isoPullback_inv_snd_assoc, CycleQ2LiteralIncidenceTimeFamily.seedIso_toOriginal]

private theorem germToTime_toOriginal :
    germToTime t V hV ≫ familyToFull V t ≫ CycleQ2LiteralIncidenceTimeFamily.toOriginal t =
      firstOrderCurveToOriginalCurve t := by
  rw [germToTime, Category.assoc, familyToFull_toOriginal]
  exact firstOrderIso_toOriginal V t hV

private instance : IsClosedImmersion seedSextic := by
  apply isClosedImmersion_of_comp_eq_id (Spec.map (CommRingCat.ofHom
    (MvPolynomial.C : ℂ →+* CycleQ2IncidenceTimeCurve.SexticRing)))
  simp only [seedSextic, seedPointMorphism, CycleQ2IncidenceTimeCurve.parameterToSextics,
    ← Spec.map_comp, ← Spec.map_id]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact (congrArg seedMap (CycleQ2GenericTimeDerivation.sexticToParameter_C z)).trans
    (CycleQ2IncidenceSeedFiber.seedMap_complex z)

/-- The closed fibre of the tangent germ gives the actual seed inclusion into the time family. -/
@[reassoc] theorem seed_germ_to_time :
    seedCurveToFirstOrderCurve t ≫ germToTime t V hV = seedToTime t V hV := by
  have : Mono toIncidence := by unfold toIncidence; infer_instance
  have : Mono (CycleQ2LiteralIncidenceTimeFamily.toOriginal t) := by
    unfold CycleQ2LiteralIncidenceTimeFamily.toOriginal
    infer_instance
  apply (cancel_mono (familyToFull V t ≫ CycleQ2LiteralIncidenceTimeFamily.toOriginal t)).mp
  rw [Category.assoc, germToTime_toOriginal, seedToTime_toOriginal, seedCurveToFirstOrderCurve_original]

/-- Reduction before embedding a thick chart in the time family gives its original closed chart. -/
@[reassoc] theorem reduction_to_time (i : Fin 4) :
    Spec.map (CommRingCat.ofHom (toClosed t i)) ≫ thickChart V t hV i = closedChart V t hV i := by
  change _ ≫ firstOrderChartToCurve t i ≫ germToTime t V hV = (seedChart t i) ≫ seedToTime t V hV
  rw [← Category.assoc, ← seedChart_to_germ, Category.assoc, seed_germ_to_time]

end CycleQ2LiteralAbelJacobiEvaluationFiber
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationFiber.affine_reduction_isPullback
#print axioms CycleQ2LiteralAbelJacobiEvaluationFiber.toClosed_ker_sq
#print axioms CycleQ2LiteralAbelJacobiEvaluationFiber.reduction_to_time
