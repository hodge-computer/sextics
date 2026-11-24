import Proposal.GeometricProjectiveCurve
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Flat

/-!
# The actual universal incidence quotient and its surface pivot charts

The homogeneous ring of the existing `genericCurve` is identified with
the quotient by the existing three `sectionVector` equations over the
original surface ring. Both directions are actual polynomial quotient
maps, and they retain every geometric and section-parameter coordinate.

On a unit matrix pivot the three equations reduce to one linear equation
whose derivative in a section parameter is a unit. Its actual quotient
therefore has a submersive presentation of relative dimension two over
the surface ring. The proved basepoint open supplies such a pivot at
every relevant prime of the actual trace surface.

The relative base in this last statement is the surface, not the space of
section parameters. Smoothness of the projective curves over a nonempty
section-parameter open is a separate relative Bertini statement. In
particular, the zero section parameter has the entire surface as fiber.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2UniversalCurveSection

open CategoryTheory AlgebraicGeometry MvPolynomial Matrix
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidencePolynomialRelations CycleQ2IncidenceCoefficientRelations
  CycleQ2SegreGenericSection CycleQ2GenericLinearSection

variable {S : Type} [CommRing S] [Algebra ℂ S]

local instance pointSurfaceCommRing (y : ParameterIndex → S) : CommRing (PointSurface y) :=
  inferInstance
local instance genericCurveCommRing (y : ParameterIndex → S) : CommRing (GenericCurveRing y) :=
  inferInstance

abbrev SectionPolynomial (y : ParameterIndex → S) :=
  MvPolynomial (Fin 3) (PointSurface y)

abbrev SectionQuotient (y : ParameterIndex → S) :=
  SectionPolynomial y ⧸
    sectionIdeal (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y))

/-- Scalar extension of the two original equations, before quotienting. -/
theorem pointEquations_sectionPoint (y : ParameterIndex → S) :
    (pointEquations y).map (MvPolynomial.map (C : S →+* SectionBase S)) =
      pointEquations (sectionPoint y) := by
  simp only [pointEquations, equationsIdeal, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton,
    ← pointEquationH_sectionPoint, ← pointEquationF_sectionPoint]

/-- The original surface coefficient ring maps into the homogeneous
coordinate ring of the already defined universal curve. -/
def coefficientToCurve (y : ParameterIndex → S) :
    PointSurface y →+* GenericCurveRing y :=
  Ideal.Quotient.lift (pointEquations y)
    ((Ideal.Quotient.mk (genericCurveIdeal y)).comp
      (MvPolynomial.map (C : S →+* SectionBase S))) (by
        intro p hp
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        apply (pointEquations_le_genericCurveIdeal y)
        rw [← pointEquations_sectionPoint y]
        exact Ideal.mem_map_of_mem _ hp)

@[simp] theorem coefficientToCurve_mk (y : ParameterIndex → S)
    (p : MvPolynomial (Fin 5) S) :
    coefficientToCurve y (Ideal.Quotient.mk (pointEquations y) p) =
      Ideal.Quotient.mk (genericCurveIdeal y)
        (MvPolynomial.map (C : S →+* SectionBase S) p) := rfl

theorem coefficientToCurve_matrix (y : ParameterIndex → S) (i j : Fin 3) :
    coefficientToCurve y (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y) i j) =
      Ideal.Quotient.mk (genericCurveIdeal y)
        (pointMatrixPolynomial (sectionPoint y) i j) := by
  change Ideal.Quotient.mk (genericCurveIdeal y)
      (MvPolynomial.map (C : S →+* SectionBase S)
        (MvPolynomial.map (pointMap y)
          (CycleQ2IncidenceBasepointOpen.familyMatrix i j))) = _
  rw [← pointMatrixPolynomial_eq, ← pointMatrixPolynomial_sectionPoint]

def fromSectionPolynomial (y : ParameterIndex → S) :
    SectionPolynomial y →+* GenericCurveRing y :=
  MvPolynomial.eval₂Hom (coefficientToCurve y)
    (fun j => Ideal.Quotient.mk (genericCurveIdeal y) (C (X j : SectionBase S)))

@[simp] theorem fromSectionPolynomial_C (y : ParameterIndex → S) (a : PointSurface y) :
    fromSectionPolynomial y (C a) = coefficientToCurve y a := by
  simp [fromSectionPolynomial]

@[simp] theorem fromSectionPolynomial_X (y : ParameterIndex → S) (j : Fin 3) :
    fromSectionPolynomial y (X j) =
      Ideal.Quotient.mk (genericCurveIdeal y) (C (X j : SectionBase S)) := by
  simp [fromSectionPolynomial]

theorem fromSectionPolynomial_equation (y : ParameterIndex → S) (i : Fin 3) :
    fromSectionPolynomial y
      (sectionVector (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y)) i) = 0 := by
  have h := genericCurve_equation_zero y i
  simp only [genericSectionEquation, map_sum, map_mul] at h
  calc
    _ = ∑ j : Fin 3,
        Ideal.Quotient.mk (genericCurveIdeal y) (pointMatrixPolynomial (sectionPoint y) i j) *
          Ideal.Quotient.mk (genericCurveIdeal y) (C (X j : SectionBase S)) := by
      simp only [sectionVector, linearForm, map_sum, map_mul,
        fromSectionPolynomial_C, fromSectionPolynomial_X, coefficientToCurve_matrix]
    _ = ∑ j : Fin 3,
        Ideal.Quotient.mk (genericCurveIdeal y) (C (X j : SectionBase S)) *
          Ideal.Quotient.mk (genericCurveIdeal y) (pointMatrixPolynomial (sectionPoint y) i j) :=
      Finset.sum_congr rfl (fun j _ => mul_comm
        (Ideal.Quotient.mk (genericCurveIdeal y) (pointMatrixPolynomial (sectionPoint y) i j))
        (Ideal.Quotient.mk (genericCurveIdeal y) (C (X j : SectionBase S))))
    _ = 0 := h

/-- Reverse map out of the literal section-ideal quotient. -/
def modelToCurve (y : ParameterIndex → S) : SectionQuotient y →+* GenericCurveRing y :=
  Ideal.Quotient.lift _ (fromSectionPolynomial y) (by
    change Ideal.span (Set.range (sectionVector
      (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y)))) ≤
        RingHom.ker (fromSectionPolynomial y)
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact fromSectionPolynomial_equation y i)

/-- Forward map uses the previously defined actual variable swap and
coefficient quotient, rather than a new presentation of the equations. -/
def curveToModel (y : ParameterIndex → S) : GenericCurveRing y →+* SectionQuotient y :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (sectionIdeal
      (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y)))).comp
        (toSectionPolynomial y)) (by
          intro p hp
          apply Ideal.Quotient.eq_zero_iff_mem.mpr
          rw [← toSectionPolynomial_genericCurveIdeal y]
          exact Ideal.mem_map_of_mem _ hp)

@[simp] theorem curveToModel_mk (y : ParameterIndex → S)
    (p : MvPolynomial (Fin 5) (SectionBase S)) :
    curveToModel y (Ideal.Quotient.mk (genericCurveIdeal y) p) =
      Ideal.Quotient.mk _ (toSectionPolynomial y p) := rfl

@[simp] theorem modelToCurve_mk (y : ParameterIndex → S) (p : SectionPolynomial y) :
    modelToCurve y (Ideal.Quotient.mk _ p) = fromSectionPolynomial y p := rfl

private theorem from_to_parameter (y : ParameterIndex → S) (p : SectionBase S) :
    fromSectionPolynomial y (toSectionPolynomial y (C p)) =
      Ideal.Quotient.mk (genericCurveIdeal y) (C p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [show (C (C a) : MvPolynomial (Fin 5) (SectionBase S)) =
        MvPolynomial.map (C : S →+* SectionBase S) (C a) by simp]
      rw [toSectionPolynomial_map, fromSectionPolynomial_C]
      rfl
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp, toSectionPolynomial_parameter, fromSectionPolynomial_X]

theorem from_to_polynomial (y : ParameterIndex → S)
    (p : MvPolynomial (Fin 5) (SectionBase S)) :
    fromSectionPolynomial y (toSectionPolynomial y p) =
      Ideal.Quotient.mk (genericCurveIdeal y) p := by
  have h : (fromSectionPolynomial y).comp (toSectionPolynomial y) =
      Ideal.Quotient.mk (genericCurveIdeal y) := by
    apply MvPolynomial.ringHom_ext
    · exact from_to_parameter y
    · intro j
      change fromSectionPolynomial y (toSectionPolynomial y (X j)) = _
      rw [show (X j : MvPolynomial (Fin 5) (SectionBase S)) =
        MvPolynomial.map (C : S →+* SectionBase S) (X j) by simp]
      rw [toSectionPolynomial_map, fromSectionPolynomial_C]
      rfl
  exact RingHom.congr_fun h p

theorem to_from_polynomial (y : ParameterIndex → S) (p : SectionPolynomial y) :
    curveToModel y (fromSectionPolynomial y p) = Ideal.Quotient.mk _ p := by
  have h : (curveToModel y).comp (fromSectionPolynomial y) =
      Ideal.Quotient.mk (sectionIdeal
        (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y))) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective (I := pointEquations y) a
      change curveToModel y (fromSectionPolynomial y
        (C (Ideal.Quotient.mk (pointEquations y) q))) = _
      rw [fromSectionPolynomial_C, coefficientToCurve_mk, curveToModel_mk,
        toSectionPolynomial_map]
      rfl
    · intro j
      change curveToModel y (fromSectionPolynomial y (X j)) = _
      rw [fromSectionPolynomial_X, curveToModel_mk, toSectionPolynomial_parameter]
  exact RingHom.congr_fun h p

/-- The actual homogeneous universal-curve ring is exactly the original
generic-section quotient. This closes the previous one-way ideal-image
comparison without imposing any incidence or regularity hypothesis. -/
def genericCurveRingEquiv (y : ParameterIndex → S) :
    GenericCurveRing y ≃+* SectionQuotient y where
  toFun := curveToModel y
  invFun := modelToCurve y
  left_inv x := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact from_to_polynomial y p
  right_inv x := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact to_from_polynomial y p
  map_add' := map_add (curveToModel y)
  map_mul' := map_mul (curveToModel y)

@[simp] theorem genericCurveRingEquiv_mk (y : ParameterIndex → S)
    (p : MvPolynomial (Fin 5) (SectionBase S)) :
    genericCurveRingEquiv y (Ideal.Quotient.mk (genericCurveIdeal y) p) =
      Ideal.Quotient.mk _ (toSectionPolynomial y p) := rfl

@[simp] theorem genericCurveRingEquiv_parameter (y : ParameterIndex → S) (j : Fin 3) :
    genericCurveRingEquiv y
      (Ideal.Quotient.mk (genericCurveIdeal y) (C (X j : SectionBase S))) =
      Ideal.Quotient.mk _ (X j) := by
  rw [genericCurveRingEquiv_mk, toSectionPolynomial_parameter]

@[simp] theorem genericCurveRingEquiv_geometric (y : ParameterIndex → S)
    (p : MvPolynomial (Fin 5) S) :
    genericCurveRingEquiv y
      (Ideal.Quotient.mk (genericCurveIdeal y)
        (MvPolynomial.map (C : S →+* SectionBase S) p)) =
      Ideal.Quotient.mk _
        (C (CycleQ2IncidenceBasepointOpen.curveQuotient (pointMap y) p)) := by
  rw [genericCurveRingEquiv_mk, toSectionPolynomial_map]

theorem toSectionPolynomial_constants (y : ParameterIndex → S) (p : SectionBase S) :
    toSectionPolynomial y (C p) =
      MvPolynomial.map (algebraMap S (PointSurface y)) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have h := toSectionPolynomial_map y (C a)
      have hc : CycleQ2IncidenceBasepointOpen.curveQuotient (pointMap y) (C a) =
          algebraMap S (PointSurface y) a := rfl
      simpa only [MvPolynomial.map_C, hc] using h
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, hp, toSectionPolynomial_parameter, MvPolynomial.map_X]

/-- The ring equivalence also retains the entire original parameter-base
map, not only its three variable generators. -/
theorem genericCurveRingEquiv_coefficients (y : ParameterIndex → S) (p : SectionBase S) :
    genericCurveRingEquiv y
      (Ideal.Quotient.mk (genericCurveIdeal y) (C p)) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap S (PointSurface y)) p) := by
  rw [genericCurveRingEquiv_mk, toSectionPolynomial_constants]

section PivotPresentation

variable {R : Type} [CommRing R]

abbrev MatrixSectionQuotient (M : Matrix (Fin 3) (Fin 3) R) :=
  MvPolynomial (Fin 3) R ⧸ sectionIdeal M

local instance matrixSectionModule (M : Matrix (Fin 3) (Fin 3) R) :
    Module R (MatrixSectionQuotient M) := Algebra.toModule

private def pivotRelations (M : Matrix (Fin 3) (Fin 3) R)
    (p : CycleQ2SegreCech.Chart) : Fin 1 → MvPolynomial (Fin 3) R :=
  fun _ => localEquation M p

private abbrev PivotQuotient (M : Matrix (Fin 3) (Fin 3) R)
    (p : CycleQ2SegreCech.Chart) :=
  MvPolynomial (Fin 3) R ⧸ Ideal.span (Set.range (pivotRelations M p))

private def pivotPrePresentation (M : Matrix (Fin 3) (Fin 3) R)
    (p : CycleQ2SegreCech.Chart) :
    Algebra.PreSubmersivePresentation R (PivotQuotient M p) (Fin 3) (Fin 1) :=
  Algebra.PreSubmersivePresentation.naive (v := pivotRelations M p)
    (fun _ => p.2) (fun _ _ _ => Subsingleton.elim _ _)

theorem pderiv_linearForm (a : Fin 3 → R) (j : Fin 3) :
    pderiv j (linearForm a) = C (a j) := by
  classical
  simp [linearForm, pderiv_X, Pi.single_apply]

private theorem pivotPrePresentation_jacobian
    (M : Matrix (Fin 3) (Fin 3) R) (p : CycleQ2SegreCech.Chart) :
    (pivotPrePresentation M p).jacobian =
      algebraMap R (PivotQuotient M p) (M p.1 p.2) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_fin_one, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change algebraMap (MvPolynomial (Fin 3) R) (PivotQuotient M p)
      (pderiv p.2 (linearForm (M p.1))) = _
  rw [pderiv_linearForm]
  rfl

private def pivotPresentation (M : Matrix (Fin 3) (Fin 3) R)
    (p : CycleQ2SegreCech.Chart) (hu : IsUnit (M p.1 p.2)) :
    Algebra.SubmersivePresentation R (PivotQuotient M p) (Fin 3) (Fin 1) where
  toPreSubmersivePresentation := pivotPrePresentation M p
  jacobian_isUnit := by
    rw [pivotPrePresentation_jacobian]
    exact hu.map (algebraMap R (PivotQuotient M p))

private theorem pivotRelations_ideal (M : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p : CycleQ2SegreCech.Chart) (hu : IsUnit (M p.1 p.2)) :
    Ideal.span (Set.range (pivotRelations M p)) = sectionIdeal M := by
  obtain ⟨u, hu⟩ := hu
  rw [sectionIdeal_principal M hM p u hu]
  apply congrArg Ideal.span
  change Set.range (fun _ : Fin 1 => localEquation M p) = {localEquation M p}
  exact Set.range_const

/-- An actual submersive presentation of the original three-equation
quotient. Its only pivot hypothesis is discharged below on the actual
basepoint open of the trace surface. -/
def matrixSectionPresentation (M : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p : CycleQ2SegreCech.Chart) (hu : IsUnit (M p.1 p.2)) :
    Algebra.SubmersivePresentation R (MatrixSectionQuotient M) (Fin 3) (Fin 1) :=
  (pivotPresentation M p hu).ofAlgEquiv
    (Ideal.quotientEquivAlgOfEq R (pivotRelations_ideal M hM p hu))

theorem matrixSectionPresentation_dimension (M : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p : CycleQ2SegreCech.Chart) (hu : IsUnit (M p.1 p.2)) :
    (matrixSectionPresentation M hM p hu).dimension = 2 := by
  change Nat.card (Fin 3) - Nat.card (Fin 1) = 2
  norm_num [Nat.card_eq_fintype_card]

theorem matrixSection_standardSmooth (M : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p : CycleQ2SegreCech.Chart) (hu : IsUnit (M p.1 p.2)) :
    Algebra.IsStandardSmoothOfRelativeDimension 2 R (MatrixSectionQuotient M) :=
  (matrixSectionPresentation M hM p hu).isStandardSmoothOfRelativeDimension
    (matrixSectionPresentation_dimension M hM p hu)

end PivotPresentation

/-- On every relevant prime of an actual incidence surface in the
basepoint open, the universal section quotient is standard smooth over
that localized surface ring. All matrix equations and pivots come from
the original coefficient point. -/
theorem point_section_standardSmooth [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ)))
    (hb : IsUnit (aeval y CycleQ2IncidenceBasepointOpen.basepointPolynomial))
    (P : Ideal (PointSurface y)) [P.IsPrime]
    (hx : ∃ j, CycleQ2IncidenceBasepointOpen.curveCoordinate (pointMap y) j ∉ P) :
    Algebra.IsStandardSmoothOfRelativeDimension 2 (PointPrimeRing y P)
      (MatrixSectionQuotient (primeMatrix y P)) := by
  obtain ⟨i, j, hij⟩ := CycleQ2IncidenceBasepointOpen.specialized_prime_pivot_cover
    (pointMap y) hb P hx
  have hpivot : IsUnit (primeMatrix y P i j) :=
    IsLocalization.map_units (M := P.primeCompl) (PointPrimeRing y P)
      ⟨CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y) i j, hij⟩
  have hcof := @CycleQ2SegreCech.cofactors_map_zero
    (PointSurface y) (inferInstance : CommRing (PointSurface y))
    (PointPrimeRing y P) (inferInstance : CommRing (PointPrimeRing y P))
    (algebraMap (PointSurface y) (PointPrimeRing y P))
    (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y))
    (curveMatrix_cofactors y he hu)
  exact matrixSection_standardSmooth (primeMatrix y P) hcof (i, j) hpivot

theorem point_section_flat [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ)))
    (hb : IsUnit (aeval y CycleQ2IncidenceBasepointOpen.basepointPolynomial))
    (P : Ideal (PointSurface y)) [P.IsPrime]
    (hx : ∃ j, CycleQ2IncidenceBasepointOpen.curveCoordinate (pointMap y) j ∉ P) :
    Module.Flat (PointPrimeRing y P) (MatrixSectionQuotient (primeMatrix y P)) := by
  letI := point_section_standardSmooth y he hu hb P hx
  letI : Algebra.IsStandardSmooth (PointPrimeRing y P)
      (MatrixSectionQuotient (primeMatrix y P)) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 2
  exact Algebra.Smooth.flat (PointPrimeRing y P)
    (MatrixSectionQuotient (primeMatrix y P))

section TracePoint

open CycleQ2IncidenceTraceFamily CycleQ2IncidenceTraceGenericPoint
  CycleQ2IncidenceTraceGeometry CycleQ2SegreFullJacobianBounds
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

variable [Nontrivial S] [Algebra TraceRing S] [IsScalarTower ℂ TraceRing S]

/-- The already constructed trace points satisfy every geometric input
of the preceding result. No new smoothness premise is imposed. -/
theorem tracePoint_section_standardSmooth
    (Q : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → S)
    (hz : IsTracePoint Q B CycleQ2IncidenceBasepointOpen.basepointPolynomial z)
    (P : Ideal (PointSurface (tracePointValue B z))) [P.IsPrime]
    (hx : ∃ j, CycleQ2IncidenceBasepointOpen.curveCoordinate
      (pointMap (tracePointValue B z)) j ∉ P) :
    Algebra.IsStandardSmoothOfRelativeDimension 2 (PointPrimeRing (tracePointValue B z) P)
      (MatrixSectionQuotient (primeMatrix (tracePointValue B z) P)) :=
  point_section_standardSmooth (tracePointValue B z)
    (tracePoint_original_equations Q B _ z hz) (tracePoint_leading_unit Q B _ z hz)
    (tracePoint_extra_unit Q B _ z hz) P hx

end TracePoint

#print axioms genericCurveRingEquiv
#print axioms genericCurveRingEquiv_coefficients
#print axioms matrixSection_standardSmooth
#print axioms point_section_standardSmooth
#print axioms point_section_flat
#print axioms tracePoint_section_standardSmooth

end CycleQ2UniversalCurveSection

end
