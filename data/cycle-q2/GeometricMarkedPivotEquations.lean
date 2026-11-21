import Proposal.GeometricMarkedDenseTestIdeal
import Proposal.GeometricLiteralAbelJacobiSeedLiftChart
import Proposal.GeometricLiteralAbelJacobiQChartSource
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Affine matrix-pivot equations on the actual original marked test surface.
The source chart maps openly into the marked test. Its raw universal homogeneous
coordinates agree with the displayed quotient by the cubic and the selected row.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2IncidenceDensePivot

open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceDehomogenizedChart
  CycleQ2LiteralAbelJacobiSeedLiftChart CycleQ2RelativeCurveChart
  CycleQ2GeometricIncidenceProj CycleQ2RelativeConstantSection
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceTimeCurve CycleQ2IncidenceTimeCurve
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
attribute [local instance] CycleQ2RelativeCurveChartScheme.affineCurveChartCommRing

variable (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart)

abbrev P := ParameterAlgebra
abbrev F := dehomogenizedEquations incidencePoint i 0
abbrev ambient := ChartPolynomial P ⧸ Ideal.span {F i}
abbrev mk := Ideal.Quotient.mk (Ideal.span {F i})
abbrev H := mk i (dehomogenizedEquations incidencePoint i 1)
abbrev G := mk i (dehomogenize i (relativeSectionPolynomial incidencePoint t p.1))
abbrev pivot := mk i (pivotPolynomial incidencePoint i p)

private abbrev rows := Ideal.span (Set.range (chartEquations incidencePoint t i p))

private theorem le_rows : Ideal.span {F i} ≤ rows t i p :=
  (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.subset_span ⟨0,rfl⟩)

private def rowMap : ambient i →ₐ[P] RowRing incidencePoint t i p :=
  Ideal.Quotient.factorₐ P (le_rows t i p)

private theorem rowMap_ker :
    RingHom.ker (rowMap t i p).toRingHom = Ideal.span {H i,G t i p} := by
  change RingHom.ker (Ideal.Quotient.factor (le_rows t i p)) = _
  rw [Ideal.Quotient.factor_ker,Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨_,⟨m,rfl⟩,rfl⟩
    fin_cases m
    · change mk i (F i) ∈ _
      rw [show mk i (F i) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
      exact Ideal.zero_mem _
    · exact Ideal.subset_span (Set.mem_insert _ _)
    · exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro _ (rfl | h)
    · exact Ideal.subset_span ⟨_,⟨1,rfl⟩,rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp h
      exact Ideal.subset_span ⟨_,⟨2,rfl⟩,rfl⟩

abbrev Ambient := Localization.Away (pivot i p)
abbrev Curve := Localization.Away (toCurve incidencePoint t i p (rowPivot incidencePoint t i p))

/-- Restriction on the matrix-pivot chart of the original parameter family,
with the source chart of its actual projective section curve. -/
def inclusionMap : Ambient i p →ₐ[P] Curve t i p :=
  (pivotEquiv t i p).toAlgHom.comp (Localization.awayMapₐ (rowMap t i p) (pivot i p))

theorem inclusion_surjective : Function.Surjective (inclusionMap t i p) :=
  (pivotEquiv t i p).surjective.comp (IsLocalization.Away.mapₐ_surjective_of_surjective
    (f := rowMap t i p) (Aₚ := Ambient i p)
    (Bₚ := Localization.Away ((rowMap t i p) (pivot i p))) (pivot i p)
    (Ideal.Quotient.factor_surjective (le_rows t i p)))

abbrev cubic := algebraMap (ambient i) (Ambient i p) (H i)
abbrev row := algebraMap (ambient i) (Ambient i p) (G t i p)

theorem inclusion_ker : RingHom.ker (inclusionMap t i p).toRingHom =
    Ideal.span {cubic i p, row t i p} := by
  let f := (rowMap t i p).toRingHom
  let u := pivot i p
  have h : RingHom.ker (inclusionMap t i p).toRingHom = RingHom.ker (Localization.awayMap f u) := by
    ext x
    change pivotEquiv t i p (Localization.awayMap f u x) = 0 ↔ Localization.awayMap f u x = 0
    exact (pivotEquiv t i p).map_eq_zero_iff
  rw [h,show RingHom.ker (Localization.awayMap f u) = (RingHom.ker f).map (algebraMap _ (Ambient i p)) from
    IsLocalization.ker_map (Localization.Away (f u)) f (Submonoid.map_powers f u),
    show RingHom.ker f = _ from rowMap_ker t i p,Ideal.map_span]
  simp only [Set.image_insert_eq,Set.image_singleton]

/-- Pulling an arbitrary polynomial class down to the projective curve agrees
with the original quotient map, including its shifted fourth coordinate. -/
theorem inclusion_mk (w : ChartPolynomial P) :
    inclusionMap t i p (algebraMap (ambient i) (Ambient i p) (mk i w)) =
      algebraMap (AffineCurveChart incidencePoint t i)
        (Localization.Away (toCurve incidencePoint t i p (rowPivot incidencePoint t i p)))
        (Ideal.Quotient.mk _ (dehomogenizedMap incidencePoint i w)) := by
  change pivotEquiv t i p
    (Localization.awayMap (rowMap t i p).toRingHom (pivot i p)
      (algebraMap (ambient i) (Ambient i p) (mk i w))) = _
  simp only [Localization.awayMap,IsLocalization.Away.map,IsLocalization.map_eq]
  exact pivotEquiv_algebraMap t i p ((rowMap t i p) (mk i w))

variable {V : parameterScheme.Opens} {D : Scheme} (a : D ⟶ Time toRaw V)
  {R : CommRingCat} (u : Spec R ⟶ D)

def actualParameters : P →+* R :=
  (Spec.preimage (u ≫ a ≫ pullback.snd toRaw (V.ι ≫ parameterToSextics) ≫ V.ι)).hom

set_option maxHeartbeats 950000 in
/-- The ideal on the base change of the original projective pivot chart to an affine
test on the marked curve is generated by the restricted cubic and its selected row. -/
theorem actual_test_kernel :
    letI : Algebra P R := (actualParameters a u).toAlgebra
    let f := Algebra.TensorProduct.map (AlgHom.id P R) (inclusionMap t i p)
    let r : Ambient i p →ₐ[P] R ⊗[P] Ambient i p := Algebra.TensorProduct.includeRight
    RingHom.ker f.toRingHom = Ideal.span {r (cubic i p),r (row t i p)} := by
  let : Algebra P R := (actualParameters a u).toAlgebra
  dsimp only
  let r : Ambient i p →ₐ[P] R ⊗[P] Ambient i p := Algebra.TensorProduct.includeRight
  have h : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id P R) (inclusionMap t i p)).toRingHom =
      (RingHom.ker (inclusionMap t i p).toRingHom).map r.toRingHom :=
    Algebra.TensorProduct.lTensor_ker (A := R) (inclusionMap t i p) (inclusion_surjective t i p)
  rw [h,inclusion_ker,Ideal.map_span]
  simp only [Set.image_insert_eq,Set.image_singleton]
  rfl

end CycleQ2IncidenceDensePivot

namespace CycleQ2MarkedPivotSource

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve CycleQ2GeometricIncidenceProj
  CycleQ2RelativeConstantCurve CycleQ2RelativeCurveChart CycleQ2LiteralIncidenceTimeCurve
  CycleQ2LiteralIncidenceNormalizedSlice CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceRelativeCylinder CycleQ2GenericSmoothCurveGraph
  CycleQ2FirstOrderCurveCharts CycleQ2IncidenceDensePivot
  CycleQ2MonicGenericAmbientChartBaseChange CycleQ2LiteralIncidenceCylinderMap
open scoped TensorProduct
attribute [local instance] CycleQ2RelativeCurveChartScheme.affineCurveChartCommRing
 CycleQ2RelativeCurveChartScheme.curveCoordinateCommRing CycleQ2RelativeCurveChart.pointSurfaceCommRing
 CycleQ2RelativeCurveChart.dehomogenizedCommRing CycleQ2IncidenceTimeCurve.timeParameterCommRing

variable (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart)

private abbrev original := relativeCurveToBase incidencePoint t
private abbrev chart := AffineCurveChart incidencePoint t i
private abbrev value : chart t i := CycleQ2LiteralAbelJacobiSeedLiftChart.toCurve incidencePoint t i p
  (CycleQ2LiteralAbelJacobiSeedLiftChart.rowPivot incidencePoint t i p)
private abbrev toPivot : chart t i →+* Curve t i p := algebraMap (chart t i) (Localization.Away (value t i p))

def originalPivot := Spec.map (CommRingCat.ofHom (toPivot t i p)) ≫ originalCurveChart t i

instance originalPivot_isOpenImmersion : IsOpenImmersion (originalPivot t i p) := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (toPivot t i p))) :=
    IsOpenImmersion.of_isLocalization (value t i p)
  unfold originalPivot
  infer_instance

private theorem originalPivot_over : originalPivot t i p ≫ original t =
    Spec.map (CommRingCat.ofHom (algebraMap P (Curve t i p))) := by
  rw [originalPivot,Category.assoc,originalCurveChart_overBase,← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq P (chart t i) (Curve t i p)).symm

variable {V : parameterScheme.Opens} {D : Scheme} (a : D ⟶ Time toRaw V)
  {R : CommRingCat.{0}} (u : Spec R ⟶ D)

abbrev testOriginal := pullback.snd a (curveMap toRaw V t) ≫ toOriginal toRaw V t
abbrev testParameters := a ≫ pullback.snd toRaw (V.ι ≫ parameterToSextics) ≫ V.ι

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem test_square' : IsPullback (pullback.fst a (curveMap toRaw V t))
    (testOriginal t a) (testParameters a) (original t) := by
  have h := (IsPullback.of_hasPullback a (curveMap toRaw V t)).paste_vert
    (IsPullback.of_hasPullback (pullback.snd toRaw (V.ι ≫ parameterToSextics)) ((original t) ∣_ V))
  simpa only [Category.assoc,testOriginal,toOriginal,testParameters] using
    h.paste_vert (isPullback_morphismRestrict (original t) V)

private abbrev Tensor := letI : Algebra P R := (actualParameters a u).toAlgebra; R ⊗[P] Curve t i p
private abbrev toTensor : Curve t i p →+* Tensor t i p a u :=
  letI : Algebra P R := (actualParameters a u).toAlgebra
  Algebra.TensorProduct.includeRight.toRingHom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem affine_square : IsPullback (pullback.fst u (pullback.fst a (curveMap toRaw V t)))
    (pullback.snd u (pullback.fst a (curveMap toRaw V t)) ≫ testOriginal t a)
    (Spec.map (CommRingCat.ofHom (actualParameters a u))) (original t) := by
  have h := (IsPullback.of_hasPullback u (pullback.fst a (curveMap toRaw V t))).paste_vert (test_square' t a)
  simpa only [actualParameters,CommRingCat.ofHom_hom,Spec.map_preimage] using h

/-- The tensor-product curve ring of the literal pivot equations is an affine open
of the original marked test surface over every affine parameter open. -/
def chartToTest : Spec (CommRingCat.of (Tensor t i p a u)) ⟶ TestSurface V t a :=
  letI : Algebra P R := (actualParameters a u).toAlgebra
  tensorInclusion (S := R) (original t) (originalPivot t i p) (originalPivot_over t i p) ≫
  (affine_square t a u).isoPullback.inv ≫ pullback.snd u (pullback.fst a (curveMap toRaw V t))

instance chartToTest_isOpenImmersion [IsOpenImmersion u] : IsOpenImmersion (chartToTest t i p a u) := by
  let : Algebra P R := (actualParameters a u).toAlgebra
  unfold chartToTest
  infer_instance

@[reassoc] theorem congr_snd {X Y Z : Scheme} {f f' : X ⟶ Z} {g g' : Y ⟶ Z}
    (ef : f = f') (eg : g = g') :
    (pullback.congrHom ef eg).hom ≫ pullback.snd f' g' = pullback.snd f g := by
  rw [pullback.congrHom_hom,pullback.lift_snd,Category.comp_id]

theorem tensor_second {A B S : Type} [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of A))
    (k : Spec (CommRingCat.of B) ⟶ X) (hk : k ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A B))) :
    tensorInclusion (S := S) f k hk ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := S) (B := B)).toRingHom) ≫ k := by
  simp only [tensorInclusion,Category.assoc,pullbackLeftPullbackSndIso_inv_fst_snd]
  rw [congr_snd_assoc,pullbackSpecIso_inv_snd_assoc]
  rfl

theorem chartToTest_original : chartToTest t i p a u ≫ testOriginal t a =
    Spec.map (CommRingCat.ofHom (toTensor t i p a u)) ≫
      originalPivot t i p := by
  let : Algebra P R := (actualParameters a u).toAlgebra
  let e := (affine_square t a u).isoPullback
  let F := tensorInclusion (S := R) (original t) (originalPivot t i p) (originalPivot_over t i p)
  let b := pullback.snd u (pullback.fst a (curveMap toRaw V t))
  have he : e.inv ≫ (b ≫ testOriginal t a) =
      pullback.snd (Spec.map (CommRingCat.ofHom (actualParameters a u))) (original t) :=
    (affine_square t a u).isoPullback_inv_snd
  exact (Category.assoc F _ _).trans
    ((congrArg (fun k => F ≫ k) ((Category.assoc e.inv b _).trans he)).trans
      (tensor_second (S := R) (original t) (originalPivot t i p) (originalPivot_over t i p)))

open CycleQ2LiteralAbelJacobiQChartSource CycleQ2LiteralAbelJacobiQCoordinates

/-- Actual raw universal coordinates of the projective point on this marked
pivot, before taking residues or passing to differential forms. -/
theorem chartToTest_raw : chartToTest t i p a u ≫ testOriginal t a ≫ originalToAmbient t =
    Spec.map (CommRingCat.ofHom (toTensor t i p a u)) ≫
      Spec.map (CommRingCat.ofHom (toPivot t i p)) ≫
      Spec.map (CommRingCat.ofHom ((curveCoordinateChartEquiv incidencePoint t i).toRingHom.comp
        (universalToOriginal t i))) ≫ sexticInclusion universalPoint i := by
  have h := congrArg (fun k => k ≫ originalToAmbient t) (chartToTest_original t i p a u)
  simpa only [originalPivot,Category.assoc,affine_chart_map] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 850000 in
/-- Each raw homogeneous fraction on the genuine test-pivot restriction is
the image of the same dehomogenized ambient polynomial in the displayed
two-equation quotient. -/
theorem raw_fraction (n : ℕ) (w : MvPolynomial (Fin 5) CycleQ2IncidenceTimeCurve.SexticRing)
    (hw : w.IsWeightedHomogeneous CycleQ2GeometricIncidenceProj.geometricWeight n) :
    toTensor t i p a u (toPivot t i p ((curveCoordinateChartEquiv incidencePoint t i)
      (universalToOriginal t i (sexticFraction universalPoint i n w hw)))) =
    toTensor t i p a u (inclusionMap t i p (algebraMap (ambient i) (Ambient i p)
      (mk i (CycleQ2IncidenceDehomogenizedChart.dehomogenize i
        (MvPolynomial.map sexticToParameter w))))) := by
  apply congrArg (toTensor t i p a u)
  rw [inclusion_mk]
  change toPivot t i p (curveCoordinateChartEquiv incidencePoint t i
    (coordinateCurveMap incidencePoint t i (surfaceChart incidencePoint i
      (coefficientChart sexticToParameter universalPoint incidencePoint universal_to_incidence i
        (sexticFraction universalPoint i n w hw))))) = _
  apply congrArg (toPivot t i p)
  simp only [coefficientChart_fraction,surfaceChart_fraction,curveCoordinateChartEquiv_map,
    CycleQ2IncidenceDehomogenizedChart.familyCoordinateChartEquiv_homogeneousFraction]

end CycleQ2MarkedPivotSource
end

#print axioms CycleQ2IncidenceDensePivot.actual_test_kernel
#print axioms CycleQ2MarkedPivotSource.chartToTest_raw
#print axioms CycleQ2MarkedPivotSource.raw_fraction
