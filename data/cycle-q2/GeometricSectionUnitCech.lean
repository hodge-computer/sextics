import Proposal.GeometricSpecializedCurveNonemptyCriterion

/-!
# Unit equations for the original fixed section give an explicit Cech boundary

The equations below are the existing fractions `(M*t)i / Mij`, with the
same constant complex vector `t`. Their maps into an overlap ring are
constructed from the actual homogeneous-localization rings. If these
fractions are units, their images give a multiplicative boundary for the
existing normalized transition, and their logarithmic differentials give
an explicit additive boundary in the actual Kahler module.
The final theorem obtains these units from emptiness of the original
specialized curve, using its actual affine chart quotient kernels.

Both normalizations are recorded. Matrix-pivot equations have transition
`up * uq^-1 * transition`; equations normalized by projective coordinates
have the degree-fourteen `twistedTransition`. The separate comparison in
`GeometricSeedProjectiveImageTwist` changes the degree-fourteen matrix image
against degree-ten orbit-ideal generators and retains the positive O(4)
twist. A class comparison must retain that contribution.

This is not a nonemptiness theorem. In particular, the scalar degree-two
class in `CycleQ2ActualCartierNonboundary` is the normal connecting class
of the original divisor, not an already identified degree-one dlog class
of this image line. To deduce nonemptiness by this route one must still
prove that the actual twisted image-line dlog class is nonzero, or build
a map taking its explicit boundaries below to boundaries of an existing
nonzero class, with the original orbit ideal and the O(4) term accounted
for. No such comparison is assumed here.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric strategy and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SectionUnitCech

open MvPolynomial Matrix
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidenceGenericPointSemantics CycleQ2GeometricIncidenceProj
  CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidencePolynomialRelations CycleQ2IncidenceCoefficientRelations
  CycleQ2SegreCech CycleQ2SegreGenericSection CycleQ2GenericLinearSection
  CycleQ2UniversalCurveCartier CycleQ2RegularSeedSection
  CycleQ2SpecializedSectionIdeal CycleQ2SpecializedProjectiveCurve
  CycleQ2SpecializedCurveNonemptyCriterion

variable (y : ParameterIndex → ℂ)
variable {R : Type} [CommRing R] [Algebra ℂ R]
variable (f : PointSurface y →ₐ[ℂ] R)

/-- The original surface matrix, mapped into a common overlap ring. -/
def mappedMatrix : Matrix (Fin 3) (Fin 3) R :=
  f.toRingHom.mapMatrix (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y))

theorem mappedMatrix_cofactors
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
    (hu : IsUnit (aeval y (leadingProduct ℂ))) :
    CycleQ2SegreLocal.cofactors (mappedMatrix y f) = 0 :=
  cofactors_map_zero f.toRingHom _ (curveMatrix_cofactors y he hu)

/-- Evaluation still uses the same original constant row of `M*t`. -/
theorem constantEquation_map (t : Fin 3 → ℂ) (i : Fin 3) :
    f (constantEquation y t i) =
      MvPolynomial.eval (fun j => algebraMap ℂ R (t j))
        (sectionVector (mappedMatrix y f) i) := by
  simp only [constantEquation, map_sum, map_smul, sectionVector, linearForm,
    map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The actual ordinary localization map induced by a unit pivot. -/
def pivotToOverlap (p : Chart) (up : Rˣ) (hp : (up : R) = f (basePivot y p)) :
    CoefficientPivot y p →+* R :=
  IsLocalization.Away.lift (S := CoefficientPivot y p) (g := f.toRingHom)
    (basePivot y p) (hp ▸ up.isUnit)

@[simp] theorem pivotToOverlap_algebraMap (p : Chart) (up : Rˣ)
    (hp : (up : R) = f (basePivot y p)) (a : PointSurface y) :
    pivotToOverlap y f p up hp
      (algebraMap (PointSurface y) (CoefficientPivot y p) a) = f a :=
  IsLocalization.Away.lift_eq _ _ a

/-- Restrict the genuine degree-zero projective chart into the overlap. -/
def projectiveToOverlap (p : Chart) (up : Rˣ)
    (hp : (up : R) = f (basePivot y p)) : ConstantProjectivePivot y p →+* R :=
  (pivotToOverlap y f p up hp).comp
    (algebraMap (ConstantProjectivePivot y p) (CoefficientPivot y p))

theorem projectiveToOverlap_equation (t : Fin 3 → ℂ) (p : Chart) (up : Rˣ)
    (hp : (up : R) = f (basePivot y p)) :
    projectiveToOverlap y f p up hp (constantProjectiveEquation y t p) =
      (↑(up⁻¹) : R) * f (constantEquation y t p.1) := by
  have h := congrArg (pivotToOverlap y f p up hp)
    (constantProjectiveEquation_val_mul y t p)
  simp only [map_mul, pivotToOverlap_algebraMap] at h
  change projectiveToOverlap y f p up hp (constantProjectiveEquation y t p) *
    f (basePivot y p) = f (constantEquation y t p.1) at h
  rw [← hp] at h
  calc
    _ = projectiveToOverlap y f p up hp (constantProjectiveEquation y t p) *
        ((up : R) * (↑(up⁻¹) : R)) := by rw [Units.mul_inv, mul_one]
    _ = (projectiveToOverlap y f p up hp (constantProjectiveEquation y t p) *
        (up : R)) * (↑(up⁻¹) : R) := by ring
    _ = f (constantEquation y t p.1) * (↑(up⁻¹) : R) := by rw [h]
    _ = _ := mul_comm _ _

theorem projectiveToOverlap_eq_eval (t : Fin 3 → ℂ) (p : Chart) (up : Rˣ)
    (hp : (up : R) = f (basePivot y p)) :
    projectiveToOverlap y f p up hp (constantProjectiveEquation y t p) =
      MvPolynomial.eval (fun j => algebraMap ℂ R (t j))
        (normalizedEquation (mappedMatrix y f) p up) := by
  rw [projectiveToOverlap_equation, constantEquation_map]
  simp only [normalizedEquation, localEquation, map_mul, MvPolynomial.eval_C]

variable (he : ∀ q, aeval y ((presentation ℂ 57).equation q) = 0)
variable (hu : IsUnit (aeval y (leadingProduct ℂ)))

/-- The transition is the existing one, including the pivot normalization. -/
def normalizedTransition (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = f (basePivot y p))
    (hq : (uq : R) = f (basePivot y q)) : Rˣ :=
  up * uq⁻¹ * transition (mappedMatrix y f) (mappedMatrix_cofactors y f he hu)
    p q up uq hp hq

theorem projectiveEquation_overlap (t : Fin 3 → ℂ) (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = f (basePivot y p))
    (hq : (uq : R) = f (basePivot y q)) :
    projectiveToOverlap y f q uq hq (constantProjectiveEquation y t q) =
      (normalizedTransition y f he hu p q up uq hp hq : R) *
        projectiveToOverlap y f p up hp (constantProjectiveEquation y t p) := by
  rw [projectiveToOverlap_eq_eval, projectiveToOverlap_eq_eval]
  have h := congrArg (MvPolynomial.eval (fun j => algebraMap ℂ R (t j)))
    (normalizedEquation_overlap (mappedMatrix y f) (mappedMatrix_cofactors y f he hu)
      p q up uq hp hq)
  simpa only [map_mul, MvPolynomial.eval_C, normalizedTransition] using h

private theorem unit_eq_of_multiply (u v w : Rˣ)
    (h : (v : R) = (u : R) * (w : R)) : u = v * w⁻¹ := by
  apply Units.ext
  change (u : R) = (v : R) * (↑(w⁻¹) : R)
  rw [h, mul_assoc, Units.mul_inv, mul_one]

/-- Units of the actual section equations trivialize its actual transition. -/
theorem normalizedTransition_of_equationUnits (t : Fin 3 → ℂ)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = f (basePivot y p))
    (hq : (uq : R) = f (basePivot y q))
    (vp : (ConstantProjectivePivot y p)ˣ) (vq : (ConstantProjectivePivot y q)ˣ)
    (hvp : (vp : ConstantProjectivePivot y p) = constantProjectiveEquation y t p)
    (hvq : (vq : ConstantProjectivePivot y q) = constantProjectiveEquation y t q) :
    normalizedTransition y f he hu p q up uq hp hq =
      Units.map (projectiveToOverlap y f q uq hq).toMonoidHom vq *
        (Units.map (projectiveToOverlap y f p up hp).toMonoidHom vp)⁻¹ := by
  apply unit_eq_of_multiply
  change projectiveToOverlap y f q uq hq (vq : ConstantProjectivePivot y q) =
    (normalizedTransition y f he hu p q up uq hp hq : R) *
      projectiveToOverlap y f p up hp (vp : ConstantProjectivePivot y p)
  rw [hvp, hvq]
  exact projectiveEquation_overlap y f he hu t p q up uq hp hq

/-- The explicit additive boundary consists of dlog of those same local units. -/
theorem normalizedTransition_dlog_of_equationUnits (t : Fin 3 → ℂ)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = f (basePivot y p))
    (hq : (uq : R) = f (basePivot y q))
    (vp : (ConstantProjectivePivot y p)ˣ) (vq : (ConstantProjectivePivot y q)ˣ)
    (hvp : (vp : ConstantProjectivePivot y p) = constantProjectiveEquation y t p)
    (hvq : (vq : ConstantProjectivePivot y q) = constantProjectiveEquation y t q) :
    unitDlog ℂ (normalizedTransition y f he hu p q up uq hp hq) =
      unitDlog ℂ (Units.map (projectiveToOverlap y f q uq hq).toMonoidHom vq) -
        unitDlog ℂ (Units.map (projectiveToOverlap y f p up hp).toMonoidHom vp) := by
  rw [normalizedTransition_of_equationUnits y f he hu t p q up uq hp hq vp vq hvp hvq,
    unitDlog_mul, unitDlog_inv, sub_eq_add_neg]

/-- On coordinate charts the same row has the full degree-fourteen twist. -/
theorem coordinateEquation_overlap (t : Fin 3 → ℂ) (p q : Chart) (up uq xp xq : Rˣ)
    (hp : (up : R) = f (basePivot y p))
    (hq : (uq : R) = f (basePivot y q)) :
    f (constantEquation y t q.1) * (↑(xq⁻¹) : R)^14 =
      (twistedTransition (mappedMatrix y f) (mappedMatrix_cofactors y f he hu)
        p q up uq hp hq xp xq 14 : R) *
          (f (constantEquation y t p.1) * (↑(xp⁻¹) : R)^14) := by
  have hrow := congrArg (MvPolynomial.eval (fun j => algebraMap ℂ R (t j)))
    (localEquation_overlap (mappedMatrix y f) (mappedMatrix_cofactors y f he hu)
      p q up uq hp hq)
  change MvPolynomial.eval (fun j => algebraMap ℂ R (t j))
      (sectionVector (mappedMatrix y f) q.1) = _ at hrow
  simp only [localEquation, map_mul, MvPolynomial.eval_C] at hrow
  rw [← constantEquation_map, ← constantEquation_map] at hrow
  have ha : (xp * xq⁻¹)^14 * (xp⁻¹)^14 = (xq⁻¹)^14 := by
    rw [← mul_pow]
    congr 1
    calc
      _ = (xp * xp⁻¹) * xq⁻¹ := by ac_rfl
      _ = xq⁻¹ := by rw [mul_inv_cancel, one_mul]
  have hb : (↑(xp * xq⁻¹) : R)^14 * (↑(xp⁻¹) : R)^14 = (↑(xq⁻¹) : R)^14 :=
    congrArg (fun u : Rˣ => (u : R)) ha
  rw [hrow, ← hb]
  change _ =
    ((↑(xp * xq⁻¹) : R)^14 *
      (transition (mappedMatrix y f) (mappedMatrix_cofactors y f he hu)
        p q up uq hp hq : R)) * _
  ring

theorem coordinateTransition_dlog (p q : Chart) (up uq xp xq : Rˣ)
    (hp : (up : R) = f (basePivot y p))
    (hq : (uq : R) = f (basePivot y q)) :
    unitDlog ℂ (twistedTransition (mappedMatrix y f) (mappedMatrix_cofactors y f he hu)
      p q up uq hp hq xp xq 14) =
        14 • (unitDlog ℂ xp - unitDlog ℂ xq) +
          unitDlog ℂ (transition (mappedMatrix y f) (mappedMatrix_cofactors y f he hu)
            p q up uq hp hq) :=
  twistedTransition_dlog ℂ _ _ p q up uq hp hq xp xq 14

/-- The literal seed supplies its cofactor hypotheses internally. If all
its actual equations are units, they provide this same boundary on every
common overlap; the vector `t` is unchanged. -/
theorem seed_equationUnits_dlog (t : Fin 3 → ℂ)
    (v : ∀ p : Chart, (ConstantProjectivePivot (seedPoint (57 : ℂ) Complex.I) p)ˣ)
    (hv : ∀ p, (v p : ConstantProjectivePivot (seedPoint (57 : ℂ) Complex.I) p) =
      constantProjectiveEquation (seedPoint (57 : ℂ) Complex.I) t p)
    (g : PointSurface (seedPoint (57 : ℂ) Complex.I) →ₐ[ℂ] R)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = g (basePivot (seedPoint (57 : ℂ) Complex.I) p))
    (hq : (uq : R) = g (basePivot (seedPoint (57 : ℂ) Complex.I) q)) :
    unitDlog ℂ (normalizedTransition (seedPoint (57 : ℂ) Complex.I) g
      seed_original_equations seed_leading_unit p q up uq hp hq) =
      unitDlog ℂ (Units.map (projectiveToOverlap (seedPoint (57 : ℂ) Complex.I)
        g q uq hq).toMonoidHom (v q)) -
      unitDlog ℂ (Units.map (projectiveToOverlap (seedPoint (57 : ℂ) Complex.I)
        g p up hp).toMonoidHom (v p)) :=
  normalizedTransition_dlog_of_equationUnits (seedPoint (57 : ℂ) Complex.I) g
    seed_original_equations seed_leading_unit t p q up uq hp hq (v p) (v q) (hv p) (hv q)

/-- Actual emptiness supplies the same explicit local primitive on every
overlap. A nonzero class comparison, still missing, would contradict this. -/
theorem seed_isEmpty_dlog (t : Fin 3 → ℂ)
    [IsEmpty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t)]
    (g : PointSurface (seedPoint (57 : ℂ) Complex.I) →ₐ[ℂ] R)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = g (basePivot (seedPoint (57 : ℂ) Complex.I) p))
    (hq : (uq : R) = g (basePivot (seedPoint (57 : ℂ) Complex.I) q)) :
    unitDlog ℂ (normalizedTransition (seedPoint (57 : ℂ) Complex.I) g
      seed_original_equations seed_leading_unit p q up uq hp hq) =
      unitDlog ℂ (Units.map (projectiveToOverlap (seedPoint (57 : ℂ) Complex.I)
        g q uq hq).toMonoidHom (emptyEquationUnit (seedPoint (57 : ℂ) Complex.I) t
          seed_original_equations seed_leading_unit q)) -
      unitDlog ℂ (Units.map (projectiveToOverlap (seedPoint (57 : ℂ) Complex.I)
        g p up hp).toMonoidHom (emptyEquationUnit (seedPoint (57 : ℂ) Complex.I) t
          seed_original_equations seed_leading_unit p)) :=
  seed_equationUnits_dlog t
    (emptyEquationUnit (seedPoint (57 : ℂ) Complex.I) t
      seed_original_equations seed_leading_unit)
    (emptyEquationUnit_val (seedPoint (57 : ℂ) Complex.I) t
      seed_original_equations seed_leading_unit) g p q up uq hp hq

#print axioms projectiveToOverlap_eq_eval
#print axioms normalizedTransition_dlog_of_equationUnits
#print axioms coordinateEquation_overlap
#print axioms seed_equationUnits_dlog
#print axioms seed_isEmpty_dlog

end CycleQ2SectionUnitCech
end
