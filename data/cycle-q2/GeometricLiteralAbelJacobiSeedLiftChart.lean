import Proposal.GeometricFirstOrderCurveChartFlat
import Proposal.GeometricSpecializedCurveCoordinateChart
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Three affine equations on a matrix-pivot chart of the incidence curve

After inverting the selected matrix entry, its row generates all section
equations on the surface. Thus the quotient by the two surface equations
and that row presents the actual localized section curve, over the same base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSeedLiftAway

variable {S Q A : Type*} [CommRing S] [CommRing Q] [CommRing A]
  [Algebra S Q] [Algebra S A]
  (f : Q →ₐ[S] A) (u : Q) (hf : Function.Surjective f)
  (g : A →+* Localization.Away u)
  (hg : ∀ x, g (f x) = algebraMap Q (Localization.Away u) x)

/-- The induced map of the two pivot localizations is an algebra equivalence. -/
def awayEquiv : Localization.Away u ≃ₐ[S] Localization.Away (f u) := by
  apply AlgEquiv.ofBijective (Localization.awayMapₐ f u)
  refine ⟨?_, IsLocalization.Away.mapₐ_surjective_of_surjective u hf⟩
  change Function.Injective (Localization.awayMap f.toRingHom u)
  apply Localization.awayMap_injective_iff.mpr
  intro a ha
  have hzero : algebraMap Q (Localization.Away u) a = 0 := by
    rw [← hg, show f a = 0 from ha, map_zero]
  obtain ⟨⟨_, n, rfl⟩, h⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers u) (Localization.Away u) a).mp hzero
  exact ⟨n, h⟩

@[simp] theorem awayEquiv_algebraMap (x : Q) :
    awayEquiv f u hf g hg (algebraMap Q (Localization.Away u) x) =
      algebraMap A (Localization.Away (f u)) (f x) := by
  change Localization.awayMap f.toRingHom u (algebraMap Q (Localization.Away u) x) = _
  simp only [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

end CycleQ2LiteralAbelJacobiSeedLiftAway

namespace CycleQ2LiteralAbelJacobiSeedLiftChart

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceImageLine CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTraceGeometry
  CycleQ2IncidencePolynomialRelations CycleQ2IncidenceCoefficientRelations
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
  CycleQ2RelativeConstantSection CycleQ2RelativeCurveChart CycleQ2FirstOrderCurveChartFlat
  CycleQ2SpecializedSectionIdeal CycleQ2UniversalCurveCartier

variable {S : Type} [CommRing S] [Algebra ℂ S]
variable (y : ParameterIndex → S) (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart)

def chartEquations : Fin 3 → ChartPolynomial S :=
  Fin.snoc (dehomogenizedEquations y i) (dehomogenize i (relativeSectionPolynomial y t p.1))

def pivotPolynomial : ChartPolynomial S :=
  dehomogenize i (pointMatrixPolynomial y p.1 p.2)

abbrev RowRing := ChartPolynomial S ⧸ Ideal.span (Set.range (chartEquations y t i p))

def rowPivot : RowRing y t i p :=
  Ideal.Quotient.mk _ (pivotPolynomial y i p)

private def polyToCurve : ChartPolynomial S →+* AffineCurveChart y t i :=
  (Ideal.Quotient.mk _).comp (dehomogenizedMap y i)

private theorem polyToCurve_rel (j : Fin 3) :
    polyToCurve y t i (chartEquations y t i p j) = 0 := by
  induction j using Fin.lastCases with
  | last =>
    simp only [chartEquations, Fin.snoc_last]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨p.1, rfl⟩)
  | cast j =>
    simp only [chartEquations, Fin.snoc_castSucc, polyToCurve, RingHom.comp_apply,
      dehomogenizedMap_equation, map_zero]

def toCurve : RowRing y t i p →ₐ[S] AffineCurveChart y t i where
  toRingHom := Ideal.Quotient.lift _ (polyToCurve y t i) (by
    change Ideal.span (Set.range (chartEquations y t i p)) ≤ RingHom.ker (polyToCurve y t i)
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact polyToCurve_rel y t i p j)
  commutes' _ := rfl

@[simp] theorem toCurve_mk (a : ChartPolynomial S) :
    toCurve y t i p (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk (affineSectionIdeal y t i) (dehomogenizedMap y i a) := rfl

theorem toCurve_surjective : Function.Surjective (toCurve y t i p) := by
  intro z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

theorem toCurve_rowPivot :
    toCurve y t i p (rowPivot y t i p) =
      Ideal.Quotient.mk (affineSectionIdeal y t i) (affineMatrixEntry y i p) := by
  rw [affineMatrixEntry_polynomial]
  rfl

private def surfaceToRow : DehomogenizedRing y i →+* RowRing y t i p :=
  Ideal.Quotient.lift _ (Ideal.Quotient.mk _) (by
    change chartIdeal (dehomogenizedEquations y i) ≤
      RingHom.ker (Ideal.Quotient.mk (Ideal.span (Set.range (chartEquations y t i p))))
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.subset_span
    exact ⟨j.castSucc, Fin.snoc_castSucc ..⟩)

private theorem selectedRow_zero :
    surfaceToRow y t i p (affineSectionEquation y t i p.1) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  exact ⟨Fin.last 2, Fin.snoc_last ..⟩

private abbrev RowAway := Localization.Away (rowPivot y t i p)

private def surfaceToRowAway : DehomogenizedRing y i →+* RowAway y t i p :=
  (algebraMap (RowRing y t i p) (RowAway y t i p)).comp (surfaceToRow y t i p)

variable [hS : Nontrivial S]
variable (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
variable (hu : IsUnit (aeval y (leadingProduct ℂ)))

include he hu hS

private theorem imageRows_zero :
    (affineSectionIdeal y t i).map (surfaceToRowAway y t i p) = ⊥ := by
  let f := (surfaceToRowAway y t i p).comp (surfaceToDehomogenized y i)
  have hp : IsUnit (f (basePivot y p)) := by
    change IsUnit (surfaceToRowAway y t i p (affineMatrixEntry y i p))
    rw [affineMatrixEntry_polynomial]
    exact IsLocalization.Away.algebraMap_isUnit (rowPivot y t i p)
  have hsingle := image_rows_principal y t he hu f p hp
  rw [affineSectionIdeal, Ideal.map_span, ← Set.range_comp]
  change Ideal.span (Set.range (fun j => f (relativeEquation y t j))) = ⊥
  rw [hsingle]
  have hz : f (relativeEquation y t p.1) = 0 := by
    change algebraMap (RowRing y t i p) (RowAway y t i p)
      (surfaceToRow y t i p (affineSectionEquation y t i p.1)) = 0
    rw [selectedRow_zero, map_zero]
  rw [hz, Ideal.span_singleton_zero]

private def curveToRowAway : AffineCurveChart y t i →+* RowAway y t i p :=
  Ideal.Quotient.lift _ (surfaceToRowAway y t i p) (by
    change affineSectionIdeal y t i ≤ RingHom.ker (surfaceToRowAway y t i p)
    apply (Ideal.map_eq_bot_iff_le_ker _).mp
    exact imageRows_zero y t i p he hu)

private theorem curveToRowAway_toCurve (x : RowRing y t i p) :
    curveToRowAway y t i p he hu (toCurve y t i p x) =
      algebraMap (RowRing y t i p) (RowAway y t i p) x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] toCurve rowPivot

/-- On a matrix-pivot chart the literal three-equation presentation gives
the whole original section curve. -/
def pivotEquivOfRelations :
    Localization.Away (rowPivot y t i p) ≃ₐ[S]
      Localization.Away (toCurve y t i p (rowPivot y t i p)) :=
  @CycleQ2LiteralAbelJacobiSeedLiftAway.awayEquiv S (RowRing y t i p) (AffineCurveChart y t i)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (toCurve y t i p) (rowPivot y t i p) (toCurve_surjective y t i p)
    (curveToRowAway y t i p he hu) (curveToRowAway_toCurve y t i p he hu)

private abbrev localizedClass {A : Type} [CommRing A] (v a : A) : Localization.Away v :=
  algebraMap A (Localization.Away v) a

theorem pivotEquivOfRelations_algebraMap (x : RowRing y t i p) :
    pivotEquivOfRelations y t i p he hu
        (localizedClass (A := RowRing y t i p) (rowPivot y t i p) x) =
      localizedClass (A := AffineCurveChart y t i)
        (toCurve y t i p (rowPivot y t i p)) (toCurve y t i p x) :=
  @CycleQ2LiteralAbelJacobiSeedLiftAway.awayEquiv_algebraMap S (RowRing y t i p)
    (AffineCurveChart y t i) inferInstance inferInstance inferInstance inferInstance inferInstance
    (toCurve y t i p) (rowPivot y t i p)
    (toCurve_surjective y t i p) (curveToRowAway y t i p he hu)
    (curveToRowAway_toCurve y t i p he hu) x

omit he hu hS

abbrev pivotEquiv :=
  pivotEquivOfRelations incidencePoint t i p
    (tracePoint_original_equations splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint)
    (tracePoint_leading_unit splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint)

theorem pivotEquiv_algebraMap (x : RowRing incidencePoint t i p) :
    pivotEquiv t i p
        (localizedClass (A := RowRing incidencePoint t i p) (rowPivot incidencePoint t i p) x) =
      localizedClass (A := AffineCurveChart incidencePoint t i)
        (toCurve incidencePoint t i p (rowPivot incidencePoint t i p)) (toCurve incidencePoint t i p x) :=
  pivotEquivOfRelations_algebraMap incidencePoint t i p
    (tracePoint_original_equations splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint)
    (tracePoint_leading_unit splitting.P splitting.B _ sliceCoordinate incidence_isTracePoint) x

private abbrev seed := seedPoint (57 : ℂ) Complex.I

abbrev seedPivotEquiv :=
  pivotEquivOfRelations seed t i p seed_original_equations seed_leading_unit

theorem seedPivotEquiv_algebraMap (x : RowRing seed t i p) :
    seedPivotEquiv t i p
        (localizedClass (A := RowRing seed t i p) (rowPivot seed t i p) x) =
      localizedClass (A := AffineCurveChart seed t i)
        (toCurve seed t i p (rowPivot seed t i p)) (toCurve seed t i p x) :=
  pivotEquivOfRelations_algebraMap seed t i p seed_original_equations seed_leading_unit x

open CategoryTheory AlgebraicGeometry
open CycleQ2SpecializedProjectiveCurve CycleQ2SpecializedCurveCoordinateChart

private theorem smooth_open_precomp {U X Y : Scheme} (j : U ⟶ X) [IsOpenImmersion j]
    (f : X ⟶ Y) (h : SmoothOfRelativeDimension 1 f) :
    SmoothOfRelativeDimension 1 (j ≫ f) :=
  smoothOfRelativeDimension_comp 0 1 j f

private abbrev specToComplex (A : Type) [CommRing A] [Algebra ℂ A] :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ A))

private theorem smoothOfRelativeDimension_pivot {Q A : Type} [CommRing Q] [CommRing A]
    [Algebra ℂ Q] [Algebra ℂ A] (u : Q) (v : A)
    (e : Localization.Away u ≃ₐ[ℂ] Localization.Away v)
    (h : SmoothOfRelativeDimension 1 (specToComplex A)) :
    SmoothOfRelativeDimension 1 (specToComplex (Localization.Away u)) := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away v)))
  have : IsOpenImmersion j := IsOpenImmersion.of_isLocalization v
  have hj : j ≫ specToComplex A = specToComplex (Localization.Away v) := by
    dsimp only [j, specToComplex]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext (IsScalarTower.algebraMap_eq ℂ A (Localization.Away v)).symm
  have hv := smooth_open_precomp j _ h
  rw [hj] at hv
  let k := (Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op).hom
  have hk : k ≫ specToComplex (Localization.Away v) = specToComplex (Localization.Away u) := by
    change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ _ = _
    dsimp only [specToComplex]
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    exact CommRingCat.hom_ext e.symm.toAlgHom.comp_algebraMap
  rw [← hk]
  exact smooth_open_precomp k _ hv

/-- A smooth seed section curve induces smooth maps of relative dimension one
on all of its literal three-polynomial pivot charts. -/
theorem seedRowPivot_smoothOfRelativeDimension
    (hc : SmoothOfRelativeDimension 1 (specializedCurveToBase seed t)) :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away (rowPivot seed t i p))))) := by
  apply smoothOfRelativeDimension_pivot (Q := RowRing seed t i p) (A := AffineCurveChart seed t i)
    (rowPivot seed t i p) (toCurve seed t i p (rowPivot seed t i p)) (seedPivotEquiv t i p)
  rw [specToComplex, ← specializedCoordinateAffineChart_overBase]
  apply smooth_open_precomp (specializedCoordinateAffineChart seed t i).inv
  exact smooth_open_precomp (specializedCoordinatePatch seed t i).ι _ hc

end CycleQ2LiteralAbelJacobiSeedLiftChart

end

#print axioms CycleQ2LiteralAbelJacobiSeedLiftChart.pivotEquiv
#print axioms CycleQ2LiteralAbelJacobiSeedLiftChart.seedPivotEquiv

#print axioms CycleQ2LiteralAbelJacobiSeedLiftChart.seedRowPivot_smoothOfRelativeDimension
