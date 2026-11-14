import Proposal.GeometricSurfaceAdjunction
import Proposal.GeometricSurfaceCoordinates
import Proposal.GeometricNormalConnecting
import Proposal.GeometricDehomogenizedCharts
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The original seed surface, its actual projective charts, and normal bindings

The original parameter and PointSurface declarations are retained in their
original namespaces. The constructed quotient and projective chart maps
preserve the actual polynomial classes, weighted fractions and conormal
classes. The normal vector used in surface adjunction is identified with
the original surface-relative normal-kernel generator on the same patch.

This module does not assert global surface adjunction or a Serre trace.
-/

/- Checked component: DebugSeedPointSurface -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceMonomials

open MvPolynomial


abbrev RawIndex (d xBound wBound : ℕ) :=
  (Fin xBound × Fin wBound) × (Fin (d + 1) × Fin (d + 1))

def Allowed (d xBound wBound : ℕ) (q : RawIndex d xBound wBound) : Prop :=
  q.1.1.val + q.2.1.val + q.2.2.val + 2 * q.1.2.val ≤ d ∧
    (2 * q.1.1.val + 2 * q.2.1.val + q.2.2.val) % 3 = 0

instance (d xBound wBound : ℕ) (q : RawIndex d xBound wBound) :
    Decidable (Allowed d xBound wBound q) := inferInstanceAs (Decidable (_ ∧ _))

abbrev Index (d xBound wBound : ℕ) :=
  {q : RawIndex d xBound wBound // Allowed d xBound wBound q}
abbrev StandardIndex (d : ℕ) := Index d 3 3

end CycleQ2IncidenceMonomials

namespace CycleQ2IncidenceNormalForm

open MvPolynomial
variable {R : Type*} [CommRing R]

abbrev FullExponent := Fin 5 →₀ ℕ
def fullDegree (e : Fin 5 → ℕ) : ℕ := e 0 + e 1 + e 2 + e 3 + 2 * e 4
def fullCharacter (e : Fin 5 → ℕ) : ℕ := (2 * e 0 + 2 * e 1 + e 2) % 3

/-- All invariant monomials of the stated weighted degree; no search-selected
subset of the coefficients is used. -/
abbrev FullInvariantIndex (d : ℕ) :=
  {e : Fin 5 → Fin (d + 1) //
    fullDegree (fun i ↦ (e i).val) = d ∧ fullCharacter (fun i ↦ (e i).val) = 0}
def fullExponentOf {d : ℕ} (e : Fin 5 → Fin (d + 1)) : FullExponent :=
  ∑ i, Finsupp.single i (e i).val

@[simp] lemma fullExponentOf_apply {d : ℕ} (e : Fin 5 → Fin (d + 1)) (i : Fin 5) :
    fullExponentOf e i = (e i).val := by
  classical
  simp [fullExponentOf, Finsupp.single_apply]
def fullGrading : Fin 5 → ℕ × ZMod 3 :=
  ![(1, 2), (1, 2), (1, 1), (1, 0), (2, 0)]

theorem fullGrading_weight (e : FullExponent) :
    Finsupp.weight fullGrading e =
      (fullDegree e, ((2 * e 0 + 2 * e 1 + e 2 : ℕ) : ZMod 3)) := by
  rw [Finsupp.weight_eq_sum]
  apply Prod.ext <;>
    simp [fullGrading, fullDegree, Fin.sum_univ_succ, nsmul_eq_mul] <;> ring

theorem fullGrading_eq_iff (e : FullExponent) (d : ℕ) :
    Finsupp.weight fullGrading e = (d, 0) ↔ fullDegree e = d ∧ fullCharacter e = 0 := by
  rw [fullGrading_weight, Prod.mk.injEq]
  simp only [fullCharacter, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

def fullIndexOf {d : ℕ} (e : FullExponent)
    (he : Finsupp.weight fullGrading e = (d, 0)) : FullInvariantIndex d := by
  have hh := (fullGrading_eq_iff e d).mp he
  have hb : ∀ i, e i < d + 1 := by
    intro i
    have hd := hh.1
    simp only [fullDegree] at hd
    fin_cases i
    · change e 0 < d + 1
      omega
    · change e 1 < d + 1
      omega
    · change e 2 < d + 1
      omega
    · change e 3 < d + 1
      omega
    · change e 4 < d + 1
      omega
  exact ⟨fun i ↦ ⟨e i, hb i⟩, hh⟩

@[simp] lemma fullIndexOf_apply {d : ℕ} (e : FullExponent)
    (he : Finsupp.weight fullGrading e = (d, 0)) (i : Fin 5) :
    ((fullIndexOf e he).val i).val = e i := rfl

@[simp] lemma fullIndexOf_exponent {d : ℕ} (e : FullExponent)
    (he : Finsupp.weight fullGrading e = (d, 0)) :
    fullExponentOf (fullIndexOf e he).val = e := by
  ext i
  simp

theorem fullGrading_of_invariant {d : ℕ} (e : FullInvariantIndex d) :
    Finsupp.weight fullGrading (fullExponentOf e.val) = (d, 0) := by
  rw [fullGrading_weight]
  apply Prod.ext
  · simpa only [fullDegree, fullExponentOf_apply] using e.property.1
  · have hc := congrArg (fun n : ℕ ↦ (n : ZMod 3)) e.property.2
    simpa [fullCharacter] using hc
def fullInvariantPolynomial (d : ℕ) (c : FullInvariantIndex d → R) :
    MvPolynomial (Fin 5) R :=
  ∑ e, monomial (fullExponentOf e.val) (c e)

lemma fullExponentOf_injective {d : ℕ} :
    Function.Injective (fullExponentOf (d := d)) := by
  intro e f h
  funext i
  apply Fin.ext
  simpa only [fullExponentOf_apply] using congrArg (fun s : FullExponent ↦ s i) h

theorem fullInvariantPolynomial_coeff (d : ℕ) (c : FullInvariantIndex d → R)
    (e : FullInvariantIndex d) :
    (fullInvariantPolynomial d c).coeff (fullExponentOf e.val) = c e := by
  classical
  have heq (f : FullInvariantIndex d) :
      fullExponentOf f.val = fullExponentOf e.val ↔ f = e := by
    constructor
    · intro h
      exact Subtype.ext (fullExponentOf_injective h)
    · rintro rfl
      rfl
  simp [fullInvariantPolynomial, coeff_sum, coeff_monomial, heq]

/-- Every homogeneous invariant polynomial is exactly a member of the full
coefficient family, with its own monomial coefficients. -/
theorem fullInvariantPolynomial_of_homogeneous {d : ℕ} {p : MvPolynomial (Fin 5) R}
    (hp : p.IsWeightedHomogeneous fullGrading (d, 0)) :
    fullInvariantPolynomial d (fun e ↦ p.coeff (fullExponentOf e.val)) = p := by
  classical
  ext s
  by_cases hs : ∃ e : FullInvariantIndex d, fullExponentOf e.val = s
  · obtain ⟨e, rfl⟩ := hs
    exact fullInvariantPolynomial_coeff d _ e
  · have hp0 : p.coeff s = 0 := by
      by_contra hp0
      exact hs ⟨fullIndexOf s (hp hp0), fullIndexOf_exponent s (hp hp0)⟩
    rw [hp0]
    simp only [fullInvariantPolynomial, coeff_sum, coeff_monomial]
    apply Finset.sum_eq_zero
    intro e _
    have he : fullExponentOf e.val ≠ s := fun he ↦ hs ⟨e, he⟩
    simp [he]

theorem fullInvariantPolynomial_homogeneous (d : ℕ) (c : FullInvariantIndex d → R) :
    (fullInvariantPolynomial d c).IsWeightedHomogeneous fullGrading (d, 0) := by
  apply (weightedHomogeneousSubmodule R fullGrading (d, 0)).sum_mem
  intro e _
  exact isWeightedHomogeneous_monomial fullGrading _ _ (fullGrading_of_invariant e)

@[simp] theorem map_fullInvariantPolynomial {S : Type*} [CommRing S]
    (φ : R →+* S) (d : ℕ) (c : FullInvariantIndex d → R) :
    MvPolynomial.map φ (fullInvariantPolynomial d c) =
      fullInvariantPolynomial d (φ ∘ c) := by
  simp [fullInvariantPolynomial]

end CycleQ2IncidenceNormalForm

namespace CycleQ2IncidenceEquations

open MvPolynomial CycleQ2IncidenceNormalForm
variable {R : Type*} [CommRing R]

abbrev Grade := ℕ × ZMod 3
abbrev HG (p : Poly R) (d : Grade) := p.IsWeightedHomogeneous fullGrading d

private lemma regrade {p : Poly R} {a b : Grade} (hp : HG p a) (h : a = b) : HG p b := h ▸ hp
private lemma hx0 : HG (X 0 : Poly R) (1, 2) := isWeightedHomogeneous_X R fullGrading 0
private lemma hx1 : HG (X 1 : Poly R) (1, 2) := isWeightedHomogeneous_X R fullGrading 1
private lemma hx2 : HG (X 2 : Poly R) (1, 1) := isWeightedHomogeneous_X R fullGrading 2
private lemma hx3 : HG (X 3 : Poly R) (1, 0) := isWeightedHomogeneous_X R fullGrading 3
private lemma hw : HG (X 4 : Poly R) (2, 0) := isWeightedHomogeneous_X R fullGrading 4
theorem smoothB_homogeneous : HG (smoothB : Poly R) (3, 0) :=
  (((((regrade (hx3.pow 3) (by decide)).add
    (regrade (hx2.pow 3) (by decide))).add
    (regrade ((hx1.mul hx2).mul hx3) (by decide))).add
    (regrade ((hx0.mul hx2).mul hx3) (by decide))).add
    (regrade (hx0.mul (hx1.pow 2)) (by decide))).add
    (regrade (hx0.pow 3) (by decide))

theorem smoothA_homogeneous : HG (smoothA : Poly R) (3, 0) :=
  (regrade (hx1.pow 3) (by decide)).add (regrade (hx3.pow 3) (by decide))

theorem smoothH_homogeneous (ι : R) : HG (smoothH ι) (3, 0) :=
  smoothB_homogeneous.sub (smoothA_homogeneous.C_mul ι)

theorem smoothK_homogeneous (ι : R) : HG (smoothK ι) (3, 0) :=
  smoothB_homogeneous.add (smoothA_homogeneous.C_mul ι)

theorem seedG_homogeneous (r : R) : HG (seedG r) (6, 0) := by
  rw [seedG, CycleQ2SegreSeed.seedG_expanded]
  exact (((regrade (hx0.pow 6) (by decide)).sub
    (regrade ((((isWeightedHomogeneous_C fullGrading r).pow 3).mul
      (hx1.pow 3)).mul (hx3.pow 3)) (by decide))).add
    (regrade (hx2.pow 6) (by decide))).add (regrade (hw.pow 3) (by decide))

theorem smoothF_homogeneous (r ι : R) : HG (smoothF r ι) (6, 0) :=
  (seedG_homogeneous r).add
    (regrade ((smoothH_homogeneous ι).mul (smoothK_homogeneous ι)) (by decide))
def seedCubicCoefficients (ι : R) (e : FullInvariantIndex 3) : R :=
  (smoothH ι).coeff (fullExponentOf e.val)

def seedSexticCoefficients (r ι : R) (e : FullInvariantIndex 6) : R :=
  (smoothF r ι).coeff (fullExponentOf e.val)

theorem seedCubicCoefficients_polynomial (ι : R) :
    fullInvariantPolynomial 3 (seedCubicCoefficients ι) = smoothH ι :=
  fullInvariantPolynomial_of_homogeneous (smoothH_homogeneous ι)

theorem seedSexticCoefficients_polynomial (r ι : R) :
    fullInvariantPolynomial 6 (seedSexticCoefficients r ι) = smoothF r ι :=
  fullInvariantPolynomial_of_homogeneous (smoothF_homogeneous r ι)

end CycleQ2IncidenceEquations

namespace CycleQ2IncidenceUniversalChart

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials CycleQ2IncidenceEquations


abbrev MatrixParameter := (Fin 3 × Fin 3) × StandardIndex 14
abbrev ParameterIndex := FullInvariantIndex 3 ⊕ (FullInvariantIndex 6 ⊕ MatrixParameter)
abbrev ParameterPolynomial (R : Type*) [CommRing R] := MvPolynomial ParameterIndex R

section Specialization
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def coefficientPoint (hcoeff : FullInvariantIndex 3 → S)
    (Fcoeff : FullInvariantIndex 6 → S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) : ParameterIndex → S :=
  Sum.elim hcoeff (Sum.elim Fcoeff (fun q => δ q.1.1 q.1.2 q.2))

def polynomialSpecialization (hcoeff : FullInvariantIndex 3 → S)
    (Fcoeff : FullInvariantIndex 6 → S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) : ParameterPolynomial R →ₐ[R] S :=
  aeval (coefficientPoint hcoeff Fcoeff δ)

end Specialization

end CycleQ2IncidenceUniversalChart

namespace CycleQ2IncidencePolynomialJacobianBinding

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
variable {R : Type*} [CommRing R] [IsDomain R]

def seedPoint (r ι : R) : ParameterIndex → R :=
  coefficientPoint (seedCubicCoefficients ι) (seedSexticCoefficients r ι) (fun _ _ _ => 0)

end CycleQ2IncidencePolynomialJacobianBinding

namespace CycleQ2IncidenceBasepointOpen

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart


abbrev Coeff := ParameterPolynomial ℂ

def rawCubicCoefficient (e : FullInvariantIndex 3) : Coeff := X (Sum.inl e)
def rawSexticCoefficient (e : FullInvariantIndex 6) : Coeff := X (Sum.inr (Sum.inl e))
def familyH : Poly Coeff := fullInvariantPolynomial 3 rawCubicCoefficient
def familyF : Poly Coeff := fullInvariantPolynomial 6 rawSexticCoefficient

section SpecializedQuotient
variable {S : Type} [CommRing S] (g : Coeff →+* S)

abbrev CurveRing := Poly S ⧸ equationsIdeal (map g familyH) (map g familyF)

end SpecializedQuotient

end CycleQ2IncidenceBasepointOpen

namespace CycleQ2IncidenceGenericPointSemantics

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
variable {S : Type*} [CommRing S]

def pointCubic (y : ParameterIndex → S) : FullInvariantIndex 3 → S :=
  fun j => y (Sum.inl j)

def pointSextic (y : ParameterIndex → S) : FullInvariantIndex 6 → S :=
  fun j => y (Sum.inr (Sum.inl j))

end CycleQ2IncidenceGenericPointSemantics

namespace CycleQ2IncidenceImageLine

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart CycleQ2IncidenceBasepointOpen CycleQ2IncidenceGenericPointSemantics
variable {S : Type} [CommRing S] [Algebra ℂ S]

def pointMap (y : ParameterIndex → S) : Coeff →+* S := (aeval y).toRingHom

theorem pointMap_familyH (y : ParameterIndex → S) :
    map (pointMap y) familyH=fullInvariantPolynomial 3 (pointCubic y) := by
  rw [familyH,map_fullInvariantPolynomial]
  congr 1
  funext j
  simp only [Function.comp_apply,pointMap,rawCubicCoefficient,AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe,aeval_X,pointCubic]

theorem pointMap_familyF (y : ParameterIndex → S) :
    map (pointMap y) familyF=fullInvariantPolynomial 6 (pointSextic y) := by
  rw [familyF,map_fullInvariantPolynomial]
  congr 1
  funext j
  simp only [Function.comp_apply,pointMap,rawSexticCoefficient,AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe,aeval_X,pointSextic]
abbrev PointSurface (y : ParameterIndex → S) := CurveRing (pointMap y)

end CycleQ2IncidenceImageLine

namespace CycleQ2GeometricSurfaceAdjunction

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceBasepointOpen CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceImageLine
  CycleQ2GeometricSeedNormalIdeals CycleQ2ConormalJacobian CycleQ2SeedTrace

/-- Equality of the original literal incidence-point ideal and the same
surface ideal used by the conormal and Cartier constructions. -/
theorem literalPointSurface_ideal :
    equationsIdeal
      (map (pointMap (seedPoint (57 : ℂ) Complex.I)) familyH)
      (map (pointMap (seedPoint (57 : ℂ) Complex.I)) familyF) = surfaceIdeal 57 1 := by
  rw [pointMap_familyH, pointMap_familyF]
  change equationsIdeal
    (fullInvariantPolynomial 3 (seedCubicCoefficients Complex.I))
    (fullInvariantPolynomial 6 (seedSexticCoefficients (57 : ℂ) Complex.I)) = _
  rw [seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial]
  exact (CycleQ2GeometricSurfaceCoordinates.surfaceIdeal_eq_seedIdeal 57).symm

/-- The canonical quotient isomorphism identifies the ORIGINAL PointSurface
at the literal seed with the ORIGINAL surface-cone quotient. -/
def literalPointSurfaceEquiv :
    PointSurface (seedPoint (57 : ℂ) Complex.I) ≃ₐ[ℂ] SurfaceRing 57 1 :=
  Ideal.quotientEquivAlgOfEq ℂ literalPointSurface_ideal

@[simp] theorem literalPointSurfaceEquiv_polynomial (p : WeightedPoly) :
    literalPointSurfaceEquiv (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk (surfaceIdeal 57 1) p :=
  Ideal.quotientEquivAlgOfEq_mk ℂ literalPointSurface_ideal p

end CycleQ2GeometricSurfaceAdjunction

end

/- Checked component: DebugSeedProjectiveSurface -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIncidenceProj

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidenceImageLine
attribute [local instance] MvPolynomial.weightedGradedAlgebra

def geometricWeight : Fin 5 → ℕ := ![1, 1, 1, 1, 2]

theorem geometricWeight_weight (e : FullExponent) :
    Finsupp.weight geometricWeight e = fullDegree e := by
  rw [Finsupp.weight_eq_sum]
  simp [geometricWeight, fullDegree, Fin.sum_univ_succ, nsmul_eq_mul] <;> ring

theorem homogeneous_of_character {S : Type*} [CommRing S]
    {p : MvPolynomial (Fin 5) S} {d : ℕ} {χ : ZMod 3}
    (hp : p.IsWeightedHomogeneous fullGrading (d, χ)) :
    p.IsWeightedHomogeneous geometricWeight d := by
  intro e he
  rw [geometricWeight_weight]
  have hd := congrArg Prod.fst (hp he)
  simpa only [fullGrading_weight] using hd

abbrev PolynomialGrade (S : Type) [CommRing S] (d : ℕ) :
    Submodule S (MvPolynomial (Fin 5) S) :=
  weightedHomogeneousSubmodule S geometricWeight d

variable {S : Type} [CommRing S] [Algebra ℂ S]

def pointEquationH (y : ParameterIndex → S) : MvPolynomial (Fin 5) S :=
  map (pointMap y) CycleQ2IncidenceBasepointOpen.familyH

def pointEquationF (y : ParameterIndex → S) : MvPolynomial (Fin 5) S :=
  map (pointMap y) CycleQ2IncidenceBasepointOpen.familyF

def pointEquations (y : ParameterIndex → S) : Ideal (MvPolynomial (Fin 5) S) :=
  equationsIdeal (pointEquationH y) (pointEquationF y)

theorem pointEquationH_homogeneous (y : ParameterIndex → S) :
    pointEquationH y ∈ PolynomialGrade S 3 := by
  rw [pointEquationH, pointMap_familyH]
  exact homogeneous_of_character (fullInvariantPolynomial_homogeneous 3 (pointCubic y))

theorem pointEquationF_homogeneous (y : ParameterIndex → S) :
    pointEquationF y ∈ PolynomialGrade S 6 := by
  rw [pointEquationF, pointMap_familyF]
  exact homogeneous_of_character (fullInvariantPolynomial_homogeneous 6 (pointSextic y))

theorem pointEquations_homogeneous (y : ParameterIndex → S) :
    (pointEquations y).IsHomogeneous (PolynomialGrade S) := by
  apply Ideal.homogeneous_span
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨3, pointEquationH_homogeneous y⟩
  · exact ⟨6, pointEquationF_homogeneous y⟩

/-- This is a grading on the existing literal `PointSurface y` quotient. -/
abbrev surfaceGrade (y : ParameterIndex → S) (d : ℕ) :
    Submodule S (PointSurface y) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
    (PolynomialGrade S) (pointEquations y) d

instance surfaceGradedRing (y : ParameterIndex → S) : GradedRing (surfaceGrade y) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing
    (PolynomialGrade S) (pointEquations y) (pointEquations_homogeneous y)

/-- The projective scheme of the literal weighted cubic/sextic quotient. -/
def surface (y : ParameterIndex → S) : Scheme := Proj (surfaceGrade y)

def weightedAmbient (S : Type) [CommRing S] : Scheme := Proj (PolynomialGrade S)

end CycleQ2GeometricIncidenceProj

namespace CycleQ2GeometricSurfaceAdjunction
open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj

/-- The actual original projective incidence surface at the literal seed. -/
abbrev literalIncidenceSurface : Scheme := surface (seedPoint (57 : ℂ) Complex.I)

def literalSurfaceCoordinate (i : Fin 5) : PointSurface (seedPoint (57 : ℂ) Complex.I) :=
  Ideal.Quotient.mk (pointEquations (seedPoint (57 : ℂ) Complex.I)) (X i)

@[simp] theorem literalSurfaceCoordinate_binding (i : Fin 5) :
    literalPointSurfaceEquiv (literalSurfaceCoordinate i) =
      Ideal.Quotient.mk (CycleQ2ConormalJacobian.surfaceIdeal 57 1) (X i) :=
  literalPointSurfaceEquiv_polynomial (X i)

private theorem geometricWeight_castSucc (i : Fin 4) : geometricWeight i.castSucc = 1 := by
  fin_cases i <;> rfl

theorem literalSurfaceCoordinate_mem_grade (i : Fin 4) :
    literalSurfaceCoordinate i.castSucc ∈ surfaceGrade (seedPoint (57 : ℂ) Complex.I) 1 := by
  refine ⟨X i.castSucc, ?_, rfl⟩
  change (X i.castSucc : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous geometricWeight 1
  simpa only [geometricWeight_castSucc] using
    isWeightedHomogeneous_X ℂ geometricWeight i.castSucc

abbrev LiteralSurfaceCoordinateRing (i : Fin 4) :=
  HomogeneousLocalization.Away (surfaceGrade (seedPoint (57 : ℂ) Complex.I))
    (literalSurfaceCoordinate i.castSucc)

def literalSurfaceCoordinatePatch (i : Fin 4) : literalIncidenceSurface.Opens :=
  Proj.basicOpen (surfaceGrade (seedPoint (57 : ℂ) Complex.I))
    (literalSurfaceCoordinate i.castSucc)

/-- The coordinate ring is the ACTUAL degree-zero localization of the
original projective surface, with its canonical chart and section maps. -/
def literalSurfaceCoordinateChart (i : Fin 4) :
    (literalSurfaceCoordinatePatch i).toScheme ≅
      Spec (CommRingCat.of (LiteralSurfaceCoordinateRing i)) :=
  Proj.basicOpenIsoSpec (surfaceGrade (seedPoint (57 : ℂ) Complex.I))
    (literalSurfaceCoordinate i.castSucc) (literalSurfaceCoordinate_mem_grade i) (by decide)

def literalSurfaceCoordinateSections (i : Fin 4) :
    CommRingCat.of (LiteralSurfaceCoordinateRing i) ≅
      Γ(literalIncidenceSurface, literalSurfaceCoordinatePatch i) :=
  Proj.basicOpenIsoAway (surfaceGrade (seedPoint (57 : ℂ) Complex.I))
    (literalSurfaceCoordinate i.castSucc) (literalSurfaceCoordinate_mem_grade i) (by decide)

end CycleQ2GeometricSurfaceAdjunction
end

/- Checked component: DebugSurfaceConeMaps -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2GeometricSurfaceAdjunction
open MvPolynomial Module
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricAffineCurveCharts
open scoped TensorProduct

/-! ## Binding the affine surface charts to the original surface cone -/

open CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals

def firstSurfaceChartEquations (r θ : ℂ) : Fin 2 → SurfacePoly :=
  ![surfaceEquation (firstQuadric r) (firstCubic θ)
      (firstSurfaceDehomogenize (originalG1 r))
      (firstSurfaceDehomogenize originalG2) (firstSurfaceDehomogenize (thetaK θ)),
    includeCurve (firstCubic θ)]

def secondSurfaceChartEquations (r θ : ℂ) : Fin 2 → SurfacePoly :=
  ![surfaceEquation (secondQuadric r) (secondCubic θ)
      (secondSurfaceDehomogenize (originalG1 r))
      (secondSurfaceDehomogenize originalG2) (secondSurfaceDehomogenize (thetaK θ)),
    includeCurve (secondCubic θ)]

/-- The map starts at the same literal cone quotient used by the actual
relative normal and Cartier constructions. It is induced by x₁=1 and
z=y+x₂², with both original surface equations checked in the target. -/
def firstSurfaceRingMap (r θ : ℂ) :
    SurfaceRing r θ →ₐ[ℂ] SurfaceChartRing (firstSurfaceChartEquations r θ) :=
  Ideal.Quotient.liftₐ (surfaceIdeal r θ)
    ((Ideal.Quotient.mkₐ ℂ (surfaceChartIdeal (firstSurfaceChartEquations r θ))).comp
      firstSurfaceDehomogenize) (by
    change surfaceIdeal r θ ≤ RingHom.ker
      (((Ideal.Quotient.mkₐ ℂ (surfaceChartIdeal (firstSurfaceChartEquations r θ))).comp
        firstSurfaceDehomogenize).toRingHom)
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    fin_cases a
    · change Ideal.Quotient.mk (surfaceChartIdeal (firstSurfaceChartEquations r θ))
        (firstSurfaceDehomogenize (actualSeedEquation r θ)) = 0
      rw [firstSurfaceDehomogenize_equation]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0, rfl⟩)
    · change Ideal.Quotient.mk (surfaceChartIdeal (firstSurfaceChartEquations r θ))
        (firstSurfaceDehomogenize (thetaH θ)) = 0
      rw [firstSurfaceDehomogenize_h]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨1, rfl⟩))

/-- The analogous actual cone map on x₂=1, using z=y+1. -/
def secondSurfaceRingMap (r θ : ℂ) :
    SurfaceRing r θ →ₐ[ℂ] SurfaceChartRing (secondSurfaceChartEquations r θ) :=
  Ideal.Quotient.liftₐ (surfaceIdeal r θ)
    ((Ideal.Quotient.mkₐ ℂ (surfaceChartIdeal (secondSurfaceChartEquations r θ))).comp
      secondSurfaceDehomogenize) (by
    change surfaceIdeal r θ ≤ RingHom.ker
      (((Ideal.Quotient.mkₐ ℂ (surfaceChartIdeal (secondSurfaceChartEquations r θ))).comp
        secondSurfaceDehomogenize).toRingHom)
    apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    fin_cases a
    · change Ideal.Quotient.mk (surfaceChartIdeal (secondSurfaceChartEquations r θ))
        (secondSurfaceDehomogenize (actualSeedEquation r θ)) = 0
      rw [secondSurfaceDehomogenize_equation]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨0, rfl⟩)
    · change Ideal.Quotient.mk (surfaceChartIdeal (secondSurfaceChartEquations r θ))
        (secondSurfaceDehomogenize (thetaH θ)) = 0
      rw [secondSurfaceDehomogenize_h]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨1, rfl⟩))

@[simp] theorem firstSurfaceRingMap_polynomial (r θ : ℂ) (p : WeightedPoly) :
    firstSurfaceRingMap r θ (Ideal.Quotient.mk (surfaceIdeal r θ) p) =
      Ideal.Quotient.mk (surfaceChartIdeal (firstSurfaceChartEquations r θ))
        (firstSurfaceDehomogenize p) := rfl

@[simp] theorem secondSurfaceRingMap_polynomial (r θ : ℂ) (p : WeightedPoly) :
    secondSurfaceRingMap r θ (Ideal.Quotient.mk (surfaceIdeal r θ) p) =
      Ideal.Quotient.mk (surfaceChartIdeal (secondSurfaceChartEquations r θ))
        (secondSurfaceDehomogenize p) := rfl

theorem firstSurfaceDehomogenize_restrict (p : WeightedPoly) :
    setNormalZero (firstSurfaceDehomogenize p) = firstDehomogenize (substitute p) := by
  have he : setNormalZero.comp firstSurfaceDehomogenize =
      firstDehomogenize.comp substitute := by
    ext a
    fin_cases a <;> simp [firstSurfaceDehomogenize, setNormalZero,
      firstDehomogenize, substitute]
  exact congrArg (fun f : WeightedPoly →ₐ[ℂ] AffinePoly => f p) he

theorem secondSurfaceDehomogenize_restrict (p : WeightedPoly) :
    setNormalZero (secondSurfaceDehomogenize p) = secondDehomogenize (substitute p) := by
  have he : setNormalZero.comp secondSurfaceDehomogenize =
      secondDehomogenize.comp substitute := by
    ext a
    fin_cases a <;> simp [secondSurfaceDehomogenize, setNormalZero,
      secondDehomogenize, substitute]
  exact congrArg (fun f : WeightedPoly →ₐ[ℂ] AffinePoly => f p) he

/-- The constructed surface-to-curve map commutes with the original
substitution and the existing x₁ coordinate dehomogenization. -/
theorem firstSurfaceRingMap_curve_square (r θ : ℂ) (p : WeightedPoly) :
    surfaceToCurve (firstQuadric r) (firstCubic θ)
      (firstSurfaceDehomogenize (originalG1 r))
      (firstSurfaceDehomogenize originalG2) (firstSurfaceDehomogenize (thetaK θ))
      (firstSurfaceRingMap r θ (Ideal.Quotient.mk (surfaceIdeal r θ) p)) =
      Ideal.Quotient.mk (chartIdeal ![firstQuadric r, firstCubic θ])
        (firstDehomogenize (substitute p)) := by
  rw [firstSurfaceRingMap_polynomial]
  change Ideal.Quotient.mk (chartIdeal ![firstQuadric r, firstCubic θ])
    (setNormalZero (firstSurfaceDehomogenize p)) = _
  rw [firstSurfaceDehomogenize_restrict]

/-- The same commuting square holds on the existing x₂ chart. -/
theorem secondSurfaceRingMap_curve_square (r θ : ℂ) (p : WeightedPoly) :
    surfaceToCurve (secondQuadric r) (secondCubic θ)
      (secondSurfaceDehomogenize (originalG1 r))
      (secondSurfaceDehomogenize originalG2) (secondSurfaceDehomogenize (thetaK θ))
      (secondSurfaceRingMap r θ (Ideal.Quotient.mk (surfaceIdeal r θ) p)) =
      Ideal.Quotient.mk (chartIdeal ![secondQuadric r, secondCubic θ])
        (secondDehomogenize (substitute p)) := by
  rw [secondSurfaceRingMap_polynomial]
  change Ideal.Quotient.mk (chartIdeal ![secondQuadric r, secondCubic θ])
    (setNormalZero (secondSurfaceDehomogenize p)) = _
  rw [secondSurfaceDehomogenize_restrict]
/-! ## The actual functorial conormal map along a surface chart -/

section ConormalFunctor

variable {A S R : Type*} [CommRing A] [CommRing S] [CommRing R]
  [Algebra A S] [Algebra A R] [Algebra S R] [IsScalarTower A S R]

/-- An element of the original curve ideal maps into the kernel of the
actual surface-chart-to-curve map by the commuting scalar tower. -/
theorem conormalChart_mem (I : Ideal A)
    (hI : I ≤ RingHom.ker (algebraMap A R)) (x : I) :
    algebraMap A S (x : A) ∈ RingHom.ker (algebraMap S R) := by
  change algebraMap S R (algebraMap A S (x : A)) = 0
  rw [← IsScalarTower.algebraMap_apply A S R]
  exact hI x.property

/-- The functorial map on actual ideal conormals, followed by scalar
extension to the actual curve chart. No flatness or isomorphism is assumed. -/
def conormalChartMap (I : Ideal A)
    (hI : I ≤ RingHom.ker (algebraMap A R)) :
    R ⊗[A] I.Cotangent →ₗ[R]
      R ⊗[S] (RingHom.ker (algebraMap S R)).Cotangent :=
  ((((TensorProduct.mk S R (RingHom.ker (algebraMap S R)).Cotangent) (1 : R)).restrictScalars A).comp
    (Ideal.mapCotangent I (RingHom.ker (algebraMap S R)) (Algebra.ofId A S)
      (fun _ hx => conormalChart_mem I hI ⟨_, hx⟩))).liftBaseChange R

@[simp] theorem conormalChartMap_equation (I : Ideal A)
    (hI : I ≤ RingHom.ker (algebraMap A R)) (a : R) (x : I) :
    conormalChartMap (S := S) I hI (a ⊗ₜ[A] I.toCotangent x) =
      a ⊗ₜ[S] (RingHom.ker (algebraMap S R)).toCotangent
        ⟨algebraMap A S (x : A), conormalChart_mem I hI x⟩ := by
  simp only [conormalChartMap, LinearMap.liftBaseChange_tmul,
    LinearMap.comp_apply, Ideal.mapCotangent_toCotangent, LinearMap.restrictScalars_apply,
    TensorProduct.mk_apply, Algebra.ofId_apply,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end ConormalFunctor

end CycleQ2GeometricSurfaceAdjunction
end

/- Checked component: DebugSurfaceConeNormal -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2GeometricSurfaceAdjunction
open MvPolynomial Module
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricAffineCurveCharts
open scoped TensorProduct

/-! ## Restriction of the original cone normal to the constructed adjunction patches -/

open CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals

/-- `false` selects x₁=1 and `true` selects x₂=1. These are the two
literal dehomogenizations already constructed above. -/
def coneChartDehomogenize (ε : Bool) : WeightedPoly →ₐ[ℂ] SurfacePoly :=
  if ε then secondSurfaceDehomogenize else firstSurfaceDehomogenize

def coneChartQuadric (r : ℂ) (ε : Bool) : AffinePoly :=
  if ε then secondQuadric r else firstQuadric r

def coneChartCubic (θ : ℂ) (ε : Bool) : AffinePoly :=
  if ε then secondCubic θ else firstCubic θ

abbrev ConeChartSurfaceRing (r θ : ℂ) (ε : Bool) :=
  SurfaceChartRing ![surfaceEquation (coneChartQuadric r ε) (coneChartCubic θ ε)
      (coneChartDehomogenize ε (originalG1 r))
      (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)),
    includeCurve (coneChartCubic θ ε)]

def coneSurfaceRingMap (r θ : ℂ) (ε : Bool) :
    SurfaceRing r θ →ₐ[ℂ] ConeChartSurfaceRing r θ ε := by
  cases ε
  · exact firstSurfaceRingMap r θ
  · exact secondSurfaceRingMap r θ

@[simp] theorem coneSurfaceRingMap_polynomial (r θ : ℂ) (ε : Bool) (p : WeightedPoly) :
    coneSurfaceRingMap r θ ε (Ideal.Quotient.mk (surfaceIdeal r θ) p) =
      algebraMap SurfacePoly (ConeChartSurfaceRing r θ ε) (coneChartDehomogenize ε p) := by
  cases ε <;> rfl

@[simp] theorem coneChartDehomogenize_f1 (r : ℂ) (ε : Bool) :
    coneChartDehomogenize ε (originalF1 r) = includeCurve (coneChartQuadric r ε) := by
  cases ε
  · exact firstSurfaceDehomogenize_f1 r
  · exact secondSurfaceDehomogenize_f1 r

@[simp] theorem coneChartDehomogenize_f2 (ε : Bool) :
    coneChartDehomogenize ε originalF2 = X none := by
  cases ε
  · exact firstSurfaceDehomogenize_f2
  · exact secondSurfaceDehomogenize_f2

@[simp] theorem coneChartDehomogenize_h (θ : ℂ) (ε : Bool) :
    coneChartDehomogenize ε (thetaH θ) = includeCurve (coneChartCubic θ ε) := by
  cases ε
  · exact firstSurfaceDehomogenize_h θ
  · exact secondSurfaceDehomogenize_h θ

abbrev ConeNormalSurfacePatch (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :=
  NormalSurfacePatch (coneChartQuadric r ε) (coneChartCubic θ ε)
    (coneChartDehomogenize ε (originalG1 r))
    (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)) i j

abbrev ConeNormalCurvePatch (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :=
  NormalCurvePatch (coneChartQuadric r ε) (coneChartCubic θ ε)
    (coneChartDehomogenize ε (originalG1 r))
    (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)) i j

def coneToSurfacePatch (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    SurfaceRing r θ →ₐ[ℂ] ConeNormalSurfacePatch r θ ε i j :=
  (IsScalarTower.toAlgHom ℂ (ConeChartSurfaceRing r θ ε)
    (ConeNormalSurfacePatch r θ ε i j)).comp (coneSurfaceRingMap r θ ε)

def coneToCurvePatch (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    SurfaceRing r θ →ₐ[ℂ] ConeNormalCurvePatch r θ ε i j :=
  (normalChartMap (coneChartQuadric r ε) (coneChartCubic θ ε)
    (coneChartDehomogenize ε (originalG1 r))
    (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)) i j).comp
      (coneToSurfacePatch r θ ε i j)

instance coneNormalSurfaceAlgebra (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    Algebra (SurfaceRing r θ) (ConeNormalSurfacePatch r θ ε i j) :=
  (coneToSurfacePatch r θ ε i j).toRingHom.toAlgebra

instance coneNormalCurveAlgebra (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    Algebra (SurfaceRing r θ) (ConeNormalCurvePatch r θ ε i j) :=
  (coneToCurvePatch r θ ε i j).toRingHom.toAlgebra

instance coneNormalScalarTower (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    IsScalarTower (SurfaceRing r θ) (ConeNormalSurfacePatch r θ ε i j)
      (ConeNormalCurvePatch r θ ε i j) :=
  IsScalarTower.of_algebraMap_eq' rfl

instance coneNormalAmbientAlgebra (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    Algebra WeightedPoly (ConeNormalCurvePatch r θ ε i j) :=
  ((coneToCurvePatch r θ ε i j).toRingHom.comp (Ideal.Quotient.mk (surfaceIdeal r θ))).toAlgebra

/-- These are the scalar actions of the constructed algebras, cached to
avoid searching through several reducible quotient/localization aliases. -/
instance (priority := 2000) coneNormalAmbientSMul
    (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    SMul WeightedPoly (ConeNormalCurvePatch r θ ε i j) :=
  (coneNormalAmbientAlgebra r θ ε i j).toSMul

instance (priority := 2000) coneNormalCurveSMul
    (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    SMul (SurfaceRing r θ) (ConeNormalCurvePatch r θ ε i j) :=
  (coneNormalCurveAlgebra r θ ε i j).toSMul

instance coneNormalAmbientTower (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    IsScalarTower WeightedPoly (SurfaceRing r θ) (ConeNormalCurvePatch r θ ε i j) where
  smul_assoc p a z := by
    change coneToCurvePatch r θ ε i j
        (Ideal.Quotient.mk (surfaceIdeal r θ) p * a) * z =
      coneToCurvePatch r θ ε i j (Ideal.Quotient.mk (surfaceIdeal r θ) p) *
        (coneToCurvePatch r θ ε i j a * z)
    rw [map_mul, mul_assoc]

@[simp] theorem coneToSurfacePatch_polynomial (r θ : ℂ) (ε : Bool)
    (i : Fin 2) (j : Fin 3) (p : WeightedPoly) :
    algebraMap (SurfaceRing r θ) (ConeNormalSurfacePatch r θ ε i j)
      (Ideal.Quotient.mk (surfaceIdeal r θ) p) =
      algebraMap SurfacePoly (ConeNormalSurfacePatch r θ ε i j) (coneChartDehomogenize ε p) := by
  change algebraMap (ConeChartSurfaceRing r θ ε) (ConeNormalSurfacePatch r θ ε i j)
    (coneSurfaceRingMap r θ ε (Ideal.Quotient.mk (surfaceIdeal r θ) p)) = _
  rw [coneSurfaceRingMap_polynomial, ← IsScalarTower.algebraMap_apply]

@[simp] theorem coneToCurvePatch_polynomial (r θ : ℂ) (ε : Bool)
    (i : Fin 2) (j : Fin 3) (p : WeightedPoly) :
    algebraMap (SurfaceRing r θ) (ConeNormalCurvePatch r θ ε i j)
      (Ideal.Quotient.mk (surfaceIdeal r θ) p) =
      normalCoefficientMap (coneChartQuadric r ε) (coneChartCubic θ ε)
        (coneChartDehomogenize ε (originalG1 r))
        (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)) i j
          (coneChartDehomogenize ε p) := by
  rw [IsScalarTower.algebraMap_apply (SurfaceRing r θ) (ConeNormalSurfacePatch r θ ε i j)
      (ConeNormalCurvePatch r θ ε i j),
    coneToSurfacePatch_polynomial, normalAlgebraMap_polynomial]

/-- The original curve ideal really vanishes in this actual localized
curve ring. Only its three literal generators are used. -/
theorem coneCurveIdeal_annihilates (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    curveIdealOnSurface r θ ≤
      RingHom.ker (algebraMap (SurfaceRing r θ) (ConeNormalCurvePatch r θ ε i j)) := by
  change (ambientCurveIdeal r θ).map (Ideal.Quotient.mk (surfaceIdeal r θ)) ≤ _
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨a, rfl⟩
  change algebraMap (SurfaceRing r θ) (ConeNormalCurvePatch r θ ε i j)
    (Ideal.Quotient.mk (surfaceIdeal r θ) (curveEquations r θ a)) = 0
  rw [coneToCurvePatch_polynomial]
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl <;>
    simp only [curveEquations, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      coneChartDehomogenize_f1, coneChartDehomogenize_f2,
      coneChartDehomogenize_h, normalCoefficientMap, AlgHom.comp_apply,
      polynomialToCurve_quadric, polynomialToCurve_normal,
      polynomialToCurve_cubic, map_zero]

/-- This map is the functorial map from the conormal of the ORIGINAL
curve ideal on the surface cone to the conormal of the actual affine
surface-to-curve quotient used in adjunction. -/
def coneToLocalConormal (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    ConeNormalCurvePatch r θ ε i j ⊗[SurfaceRing r θ] (curveIdealOnSurface r θ).Cotangent →ₗ[
      ConeNormalCurvePatch r θ ε i j]
        NormalConormal (coneChartQuadric r ε) (coneChartCubic θ ε)
          (coneChartDehomogenize ε (originalG1 r))
          (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)) i j :=
  conormalChartMap (S := ConeNormalSurfacePatch r θ ε i j)
    (curveIdealOnSurface r θ) (coneCurveIdeal_annihilates r θ ε i j)

theorem coneToLocalConormal_equation (r θ : ℂ) (ε : Bool)
    (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    coneToLocalConormal r θ ε i j
      (relativeEquationClass r θ (ConeNormalCurvePatch r θ ε i j) a.castSucc) =
      normalEquationClass (coneChartQuadric r ε) (coneChartCubic θ ε)
        (coneChartDehomogenize ε (originalG1 r))
        (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)) i j a := by
  rw [coneToLocalConormal, relativeEquationClass, conormalChartMap_equation]
  unfold normalEquationClass tensorCotangentClass
  let J := NormalCurveIdeal (coneChartQuadric r ε) (coneChartCubic θ ε)
    (coneChartDehomogenize ε (originalG1 r))
    (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)) i j
  apply congrArg (fun x : J => (1 : ConeNormalCurvePatch r θ ε i j) ⊗ₜ[
    ConeNormalSurfacePatch r θ ε i j] J.toCotangent x)
  apply Subtype.ext
  have he : coneChartDehomogenize ε (curveEquations r θ a.castSucc) =
      normalPolynomial (coneChartQuadric r ε) a := by
    fin_cases a
    · exact coneChartDehomogenize_f1 r ε
    · exact coneChartDehomogenize_f2 ε
  change algebraMap (SurfaceRing r θ) (ConeNormalSurfacePatch r θ ε i j)
      (Ideal.Quotient.mk (surfaceIdeal r θ) (curveEquations r θ a.castSucc)) =
    algebraMap SurfacePoly (ConeNormalSurfacePatch r θ ε i j)
      (normalPolynomial (coneChartQuadric r ε) a)
  exact (coneToSurfacePatch_polynomial r θ ε i j _).trans
    (congrArg (algebraMap SurfacePoly (ConeNormalSurfacePatch r θ ε i j)) he)

theorem coneToLocalConormal_cubic (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    coneToLocalConormal r θ ε i j
      (relativeEquationClass r θ (ConeNormalCurvePatch r θ ε i j) 2) = 0 := by
  have hh : (⟨Ideal.Quotient.mk (surfaceIdeal r θ) (curveEquations r θ 2),
      Ideal.mem_map_of_mem _ (curveEquation_mem r θ 2)⟩ : curveIdealOnSurface r θ) = 0 := by
    apply Subtype.ext
    change Ideal.Quotient.mk (surfaceIdeal r θ) (thetaH θ) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨1, rfl⟩)
  simp only [relativeEquationClass, hh, map_zero, TensorProduct.tmul_zero]

/-- Restriction of the fixed actual normal vector to the ORIGINAL
cone-relative conormal. This is a constructed linear map, not a supplied
comparison or an arbitrary choice of a rank-one generator. -/
def coneNormalVector (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    RelativeNormal r θ (ConeNormalCurvePatch r θ ε i j) :=
  (normalVector (coneChartQuadric r ε) (coneChartCubic θ ε)
    (coneChartDehomogenize ε (originalG1 r))
    (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)) i j).comp
      (coneToLocalConormal r θ ε i j)

/-- Every original equation value is fixed: f₁ maps to G₂, f₂ to −G₁,
and h to zero. Thus the normalization is exactly the one used by the
original relative-normal connecting cochain and the Cartier lift. -/
theorem coneNormalVector_equation (r θ : ℂ) (ε : Bool)
    (i : Fin 2) (j : Fin 3) (a : Fin 3) :
    coneNormalVector r θ ε i j
      (relativeEquationClass r θ (ConeNormalCurvePatch r θ ε i j) a) =
      ![algebraMap WeightedPoly (ConeNormalCurvePatch r θ ε i j) originalG2,
        -algebraMap WeightedPoly (ConeNormalCurvePatch r θ ε i j) (originalG1 r), 0] a := by
  have hv (b : Fin 2) := normalVector_equation (coneChartQuadric r ε) (coneChartCubic θ ε)
    (coneChartDehomogenize ε (originalG1 r))
    (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)) i j b
  have hm (p : WeightedPoly) :
      algebraMap WeightedPoly (ConeNormalCurvePatch r θ ε i j) p =
        normalCoefficientMap (coneChartQuadric r ε) (coneChartCubic θ ε)
          (coneChartDehomogenize ε (originalG1 r))
          (coneChartDehomogenize ε originalG2) (coneChartDehomogenize ε (thetaK θ)) i j
            (coneChartDehomogenize ε p) :=
    coneToCurvePatch_polynomial r θ ε i j p
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
  · change normalVector _ _ _ _ _ i j
      (coneToLocalConormal r θ ε i j
        (relativeEquationClass r θ (ConeNormalCurvePatch r θ ε i j) (0 : Fin 2).castSucc)) = _
    rw [coneToLocalConormal_equation, hv 0]
    simp only [Matrix.cons_val_zero, hm]
  · change normalVector _ _ _ _ _ i j
      (coneToLocalConormal r θ ε i j
        (relativeEquationClass r θ (ConeNormalCurvePatch r θ ε i j) (1 : Fin 2).castSucc)) = _
    rw [coneToLocalConormal_equation, hv 1]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, hm]
  · change normalVector _ _ _ _ _ i j
      (coneToLocalConormal r θ ε i j
        (relativeEquationClass r θ (ConeNormalCurvePatch r θ ε i j) 2)) = _
    rw [coneToLocalConormal_cubic, map_zero]
    rfl

end CycleQ2GeometricSurfaceAdjunction
end

/- Checked component: DebugConeNormalKernel -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2GeometricSurfaceAdjunction
open MvPolynomial Module
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricAffineCurveCharts
open CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals
open scoped TensorProduct

/-! ## The original genuine normal-kernel generator -/

open CycleQ2GenuineNormalConnecting CycleQ2SeedGlobalConormal

instance coneNormalComplexAmbientTower (r θ : ℂ) (ε : Bool)
    (i : Fin 2) (j : Fin 3) :
    IsScalarTower ℂ WeightedPoly (ConeNormalCurvePatch r θ ε i j) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap ℂ (ConeNormalCurvePatch r θ ε i j) c =
    coneToCurvePatch r θ ε i j (algebraMap ℂ (SurfaceRing r θ) c)
  exact ((coneToCurvePatch r θ ε i j).commutes c).symm

theorem coneAmbient_annihilates (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    ∀ p ∈ ambientCurveIdeal r θ,
      algebraMap WeightedPoly (ConeNormalCurvePatch r θ ε i j) p = 0 := by
  intro p hp
  exact coneCurveIdeal_annihilates r θ ε i j (Ideal.mem_map_of_mem _ hp)

/-- The original ambient equation classes give their proved conormal basis
on this very curve patch; no basis is supplied as a comparison premise. -/
def coneAmbientConormalBasis (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    Module.Basis (Fin 3) (ConeNormalCurvePatch r θ ε i j)
      (CurveConormal (S := ConeNormalCurvePatch r θ ε i j) r θ) :=
  seedConormalBasis r θ (coneAmbient_annihilates r θ ε i j)

theorem coneAmbientConormalBasis_apply (r θ : ℂ) (ε : Bool)
    (i : Fin 2) (j : Fin 3) (a : Fin 3) :
    coneAmbientConormalBasis r θ ε i j a =
      curveClass (S := ConeNormalCurvePatch r θ ε i j) r θ a :=
  seedConormalBasis_apply r θ (coneAmbient_annihilates r θ ε i j) a

/-- The normal vector used in the actual adjunction map is exactly the
original genuine kernel generator after the canonical conormal comparison.
The equality is determined by the three original equation classes. -/
theorem coneNormalVector_toAmbient (r θ : ℂ) (ε : Bool) (i : Fin 2) (j : Fin 3) :
    ((normalModuleEquiv r θ (ConeNormalCurvePatch r θ ε i j))
      (coneNormalVector r θ ε i j)).val =
        genuineKernelGenerator r θ (coneAmbientConormalBasis r θ ε i j) := by
  apply curveNormal_ext r θ
  intro a
  have he := normalModuleEquiv_symm_equation r θ (ConeNormalCurvePatch r θ ε i j)
    ((normalModuleEquiv r θ (ConeNormalCurvePatch r θ ε i j))
      (coneNormalVector r θ ε i j)) a
  have hb := coneAmbientConormalBasis_apply r θ ε i j
  calc
    _ = coneNormalVector r θ ε i j
        (relativeEquationClass r θ (ConeNormalCurvePatch r θ ε i j) a) := by
          simpa only [LinearEquiv.symm_apply_apply, curveClass] using he.symm
    _ = kernelVector
        (algebraMap WeightedPoly (ConeNormalCurvePatch r θ ε i j) (originalG1 r))
        (algebraMap WeightedPoly (ConeNormalCurvePatch r θ ε i j) originalG2) a :=
      coneNormalVector_equation r θ ε i j a
    _ = _ := (fromCoordinates_class r θ (coneAmbientConormalBasis r θ ε i j)
      hb _ a).symm

end CycleQ2GeometricSurfaceAdjunction
end

/- Checked component: DebugWeightedSurfaceCharts -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceAdjunction

open MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricDehomogenizedCharts

/-- Weighted rescaling of every monomial, with its actual weighted degree. -/
theorem weighted_eval_scale {ι R S : Type*} [CommRing R] [CommRing S]
    (w : ι → ℕ) (f : R →+* S) (x : ι → S) (c : S)
    (p : MvPolynomial ι R) (n : ℕ) (hp : p.IsWeightedHomogeneous w n) :
    eval₂Hom f (fun j => c ^ w j * x j) p = c ^ n * eval₂Hom f x p := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial d a hd =>
      have hdegree : (∑ j ∈ d.support, w j * d j) = n := by
        simpa [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_comm] using hd
      simp only [eval₂Hom_monomial, Finsupp.prod, mul_pow, ← pow_mul,
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdegree]
      ring

abbrev LiteralPointRing := PointSurface (seedPoint (57 : ℂ) Complex.I)

def literalPointQuotient : WeightedPoly →+* LiteralPointRing :=
  Ideal.Quotient.mk (pointEquations (seedPoint (57 : ℂ) Complex.I))

theorem literalPointQuotient_binding (p : WeightedPoly) :
    literalPointSurfaceEquiv (literalPointQuotient p) =
      Ideal.Quotient.mk (CycleQ2ConormalJacobian.surfaceIdeal 57 1) p :=
  literalPointSurfaceEquiv_polynomial p

theorem literalPointQuotient_mem_grade (p : WeightedPoly) (n : ℕ)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    literalPointQuotient p ∈ surfaceGrade (seedPoint (57 : ℂ) Complex.I) n :=
  ⟨p, hp, rfl⟩

/-- The selected coordinate is one. The normal variable is z=f₂, so the
weight-two coordinate is z minus the square of the dehomogenized x₂. -/
def literalSurfaceDehomogenize (i : Fin 4) : WeightedPoly →ₐ[ℂ] SurfacePoly :=
  aeval (Fin.snoc
    (fun j : Fin 4 => includeCurve (dehomogenize i (X j)))
    (X none - includeCurve (dehomogenize i (X 2)) ^ 2))

@[simp] theorem literalSurfaceDehomogenize_castSucc (i j : Fin 4) :
    literalSurfaceDehomogenize i (X j.castSucc) =
      includeCurve (dehomogenize i (X j)) := by
  simp [literalSurfaceDehomogenize]

@[simp] theorem literalSurfaceDehomogenize_last (i : Fin 4) :
    literalSurfaceDehomogenize i (X (4 : Fin 5)) =
      X none - includeCurve (dehomogenize i (X 2)) ^ 2 := by
  simp only [literalSurfaceDehomogenize, aeval_X]
  change Fin.snoc (α := fun _ : Fin 5 => SurfacePoly)
    (fun j : Fin 4 => includeCurve (dehomogenize i (X j)))
    (X none - includeCurve (dehomogenize i (X 2)) ^ 2) (Fin.last 4) = _
  exact Fin.snoc_last _ _

@[simp] theorem literalSurfaceDehomogenize_self (i : Fin 4) :
    literalSurfaceDehomogenize i (X i.castSucc) = 1 := by simp

@[simp] theorem literalSurfaceDehomogenize_f2 (i : Fin 4) :
    literalSurfaceDehomogenize i originalF2 = X none := by
  simp only [originalF2, map_add, map_pow, literalSurfaceDehomogenize_last]
  have h₂ := literalSurfaceDehomogenize_castSucc i 2
  change literalSurfaceDehomogenize i (X (2 : Fin 5)) = _ at h₂
  rw [h₂, sub_add_cancel]

def literalDehomogenizedEquations (i : Fin 4) : Fin 2 → SurfacePoly :=
  ![literalSurfaceDehomogenize i (pointEquationF (seedPoint (57 : ℂ) Complex.I)),
    literalSurfaceDehomogenize i (pointEquationH (seedPoint (57 : ℂ) Complex.I))]

abbrev LiteralDehomogenizedRing (i : Fin 4) :=
  SurfaceChartRing (literalDehomogenizedEquations i)

def literalDehomogenizedMap (i : Fin 4) : SurfacePoly →+* LiteralDehomogenizedRing i :=
  Ideal.Quotient.mk (surfaceChartIdeal (literalDehomogenizedEquations i))

theorem literalDehomogenizedMap_equation (i : Fin 4) (j : Fin 2) :
    literalDehomogenizedMap i (literalDehomogenizedEquations i j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

theorem literalPointIdeal_le_dehomogenization_kernel (i : Fin 4) :
    pointEquations (seedPoint (57 : ℂ) Complex.I) ≤
      RingHom.ker ((literalDehomogenizedMap i).comp
        (literalSurfaceDehomogenize i).toRingHom) := by
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact literalDehomogenizedMap_equation i 1
  · exact literalDehomogenizedMap_equation i 0

def literalPointToDehomogenized (i : Fin 4) :
    LiteralPointRing →+* LiteralDehomogenizedRing i :=
  Ideal.Quotient.lift (pointEquations (seedPoint (57 : ℂ) Complex.I))
    ((literalDehomogenizedMap i).comp (literalSurfaceDehomogenize i).toRingHom)
    (fun _ hp => literalPointIdeal_le_dehomogenization_kernel i hp)

@[simp] theorem literalPointToDehomogenized_quotient (i : Fin 4) (p : WeightedPoly) :
    literalPointToDehomogenized i (literalPointQuotient p) =
      literalDehomogenizedMap i (literalSurfaceDehomogenize i p) := rfl

@[simp] theorem literalPointToDehomogenized_self (i : Fin 4) :
    literalPointToDehomogenized i (literalSurfaceCoordinate i.castSucc) = 1 := by
  change literalPointToDehomogenized i (literalPointQuotient (X i.castSucc)) = 1
  simp

abbrev LiteralCoordinateLocalization (i : Fin 4) :=
  Localization.Away (literalSurfaceCoordinate i.castSucc)

def literalLocalizationToDehomogenized (i : Fin 4) :
    LiteralCoordinateLocalization i →+* LiteralDehomogenizedRing i :=
  Localization.awayLift (literalPointToDehomogenized i)
    (literalSurfaceCoordinate i.castSucc) (isUnit_iff_exists_inv.mpr ⟨1, by simp⟩)

def literalToDehomogenized (i : Fin 4) :
    LiteralSurfaceCoordinateRing i →+* LiteralDehomogenizedRing i :=
  (literalLocalizationToDehomogenized i).comp
    (algebraMap (LiteralSurfaceCoordinateRing i) (LiteralCoordinateLocalization i))

def literalWeightedFraction (i : Fin 4) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : LiteralSurfaceCoordinateRing i :=
  HomogeneousLocalization.Away.mk (surfaceGrade (seedPoint (57 : ℂ) Complex.I))
    (literalSurfaceCoordinate_mem_grade i) n (literalPointQuotient p)
    (by simpa using literalPointQuotient_mem_grade p n hp)

theorem literalWeightedFraction_val (i : Fin 4) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (literalWeightedFraction i n p hp).val =
      algebraMap LiteralPointRing (LiteralCoordinateLocalization i) (literalPointQuotient p) *
        IsLocalization.Away.invSelf (literalSurfaceCoordinate i.castSucc) ^ n := by
  rw [literalWeightedFraction, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf (literalSurfaceCoordinate i.castSucc) ^ n),
    ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

@[simp] theorem literalToDehomogenized_fraction (i : Fin 4) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    literalToDehomogenized i (literalWeightedFraction i n p hp) =
      literalDehomogenizedMap i (literalSurfaceDehomogenize i p) := by
  change literalLocalizationToDehomogenized i
    (Localization.mk (literalPointQuotient p)
      ⟨literalSurfaceCoordinate i.castSucc ^ n, n, rfl⟩) = _
  simpa only [literalLocalizationToDehomogenized, one_pow, mul_one,
    literalPointToDehomogenized_quotient] using
      (Localization.awayLift_mk (literalPointToDehomogenized i)
        (literalSurfaceCoordinate i.castSucc) (literalPointQuotient p) 1 (by simp) n)

def literalCoordinateConstants (i : Fin 4) : ℂ →+* LiteralSurfaceCoordinateRing i where
  toFun c := literalWeightedFraction i 0 (C c) (isWeightedHomogeneous_C _ c)
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    simp only [literalWeightedFraction_val, map_zero, pow_zero, zero_mul,
      HomogeneousLocalization.val_zero]
  map_one' := by
    apply HomogeneousLocalization.val_injective
    simp only [literalWeightedFraction_val, map_one, pow_zero, one_mul,
      HomogeneousLocalization.val_one]
  map_add' c d := by
    apply HomogeneousLocalization.val_injective
    simp only [literalWeightedFraction_val, map_add, pow_zero, mul_one,
      HomogeneousLocalization.val_add]
  map_mul' c d := by
    apply HomogeneousLocalization.val_injective
    simp only [literalWeightedFraction_val, map_mul, pow_zero, mul_one,
      HomogeneousLocalization.val_mul]

@[simp] theorem literalCoordinateConstants_val (i : Fin 4) (c : ℂ) :
    (literalCoordinateConstants i c).val =
      algebraMap LiteralPointRing (LiteralCoordinateLocalization i)
        (literalPointQuotient (C c)) := by
  change (literalWeightedFraction i 0 (C c) (isWeightedHomogeneous_C _ c)).val = _
  simp only [literalWeightedFraction_val, pow_zero, mul_one]

def literalCoordinateRatio (i : Fin 4) (j : Fin 5) : LiteralSurfaceCoordinateRing i :=
  literalWeightedFraction i (geometricWeight j) (X j)
    (isWeightedHomogeneous_X ℂ geometricWeight j)

@[simp] theorem literalCoordinateRatio_val (i : Fin 4) (j : Fin 5) :
    (literalCoordinateRatio i j).val =
      algebraMap LiteralPointRing (LiteralCoordinateLocalization i) (literalPointQuotient (X j)) *
        IsLocalization.Away.invSelf (literalSurfaceCoordinate i.castSucc) ^ geometricWeight j :=
  literalWeightedFraction_val i (geometricWeight j) (X j) _

@[simp] theorem literalCoordinateRatio_self (i : Fin 4) :
    literalCoordinateRatio i i.castSucc = 1 := by
  have hw : geometricWeight i.castSucc = 1 := by fin_cases i <;> rfl
  apply HomogeneousLocalization.val_injective
  rw [literalCoordinateRatio_val, hw, pow_one]
  rw [HomogeneousLocalization.val_one]
  change algebraMap LiteralPointRing (LiteralCoordinateLocalization i)
    (literalSurfaceCoordinate i.castSucc) *
      IsLocalization.Away.invSelf (literalSurfaceCoordinate i.castSucc) = 1
  exact IsLocalization.Away.mul_invSelf (S := LiteralCoordinateLocalization i)
    (literalSurfaceCoordinate i.castSucc)

@[simp] theorem literalToDehomogenized_constants (i : Fin 4) (c : ℂ) :
    literalToDehomogenized i (literalCoordinateConstants i c) =
      literalDehomogenizedMap i (C c) := by
  change literalToDehomogenized i
    (literalWeightedFraction i 0 (C c) (isWeightedHomogeneous_C _ c)) = _
  rw [literalToDehomogenized_fraction]
  simp [literalSurfaceDehomogenize]

@[simp] theorem literalToDehomogenized_ratio (i : Fin 4) (j : Fin 5) :
    literalToDehomogenized i (literalCoordinateRatio i j) =
      literalDehomogenizedMap i (literalSurfaceDehomogenize i (X j)) :=
  literalToDehomogenized_fraction i (geometricWeight j) (X j) _

def literalOrdinaryEvaluate (i : Fin 4) :
    CycleQ2SeedTrace.Poly →+* LiteralSurfaceCoordinateRing i :=
  eval₂Hom (literalCoordinateConstants i) (fun j => literalCoordinateRatio i j.castSucc)

def literalAffineEvaluate (i : Fin 4) : AffinePoly →+* LiteralSurfaceCoordinateRing i :=
  eval₂Hom (literalCoordinateConstants i)
    (fun j => literalCoordinateRatio i (i.succAbove j).castSucc)

def literalSurfaceEvaluate (i : Fin 4) : SurfacePoly →+* LiteralSurfaceCoordinateRing i :=
  eval₂Hom (literalCoordinateConstants i)
    (fun j => match j with
      | none => literalCoordinateRatio i 4 + literalCoordinateRatio i 2 ^ 2
      | some j => literalCoordinateRatio i (i.succAbove j).castSucc)

def literalWeightedEvaluate (i : Fin 4) : WeightedPoly →+* LiteralSurfaceCoordinateRing i :=
  eval₂Hom (literalCoordinateConstants i) (literalCoordinateRatio i)

theorem literalSurfaceEvaluate_include (i : Fin 4) (p : AffinePoly) :
    literalSurfaceEvaluate i (includeCurve p) = literalAffineEvaluate i p := by
  have he : (literalSurfaceEvaluate i).comp includeCurve.toRingHom = literalAffineEvaluate i := by
    apply MvPolynomial.ringHom_ext <;> intro x
    · simp [literalSurfaceEvaluate, literalAffineEvaluate, includeCurve]
    · simp [literalSurfaceEvaluate, literalAffineEvaluate, includeCurve]
  exact RingHom.congr_fun he p

theorem literalAffineEvaluate_dehomogenize (i : Fin 4) (p : CycleQ2SeedTrace.Poly) :
    literalAffineEvaluate i (dehomogenize i p) = literalOrdinaryEvaluate i p := by
  have he : (literalAffineEvaluate i).comp (dehomogenize i).toRingHom =
      literalOrdinaryEvaluate i := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [literalAffineEvaluate, literalOrdinaryEvaluate, dehomogenize]
    · intro j
      rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
      · simp [literalAffineEvaluate, literalOrdinaryEvaluate]
      · simp [literalAffineEvaluate, literalOrdinaryEvaluate]
  exact RingHom.congr_fun he p

theorem literalSurfaceEvaluate_comp_dehomogenize (i : Fin 4) :
    (literalSurfaceEvaluate i).comp (literalSurfaceDehomogenize i).toRingHom =
      literalWeightedEvaluate i := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [literalSurfaceEvaluate, literalWeightedEvaluate, literalSurfaceDehomogenize]
  · intro j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · change literalSurfaceEvaluate i (literalSurfaceDehomogenize i (X (4 : Fin 5))) = _
      rw [literalSurfaceDehomogenize_last, map_sub, map_pow,
        literalSurfaceEvaluate_include, literalAffineEvaluate_dehomogenize]
      simp [literalSurfaceEvaluate, literalOrdinaryEvaluate, literalWeightedEvaluate]
    · change literalSurfaceEvaluate i (literalSurfaceDehomogenize i (X k.castSucc)) = _
      rw [literalSurfaceDehomogenize_castSucc, literalSurfaceEvaluate_include,
        literalAffineEvaluate_dehomogenize]
      simp [literalOrdinaryEvaluate, literalWeightedEvaluate]

theorem literalSurfaceEvaluate_dehomogenize (i : Fin 4) (p : WeightedPoly) :
    literalSurfaceEvaluate i (literalSurfaceDehomogenize i p) =
      literalWeightedEvaluate i p :=
  RingHom.congr_fun (literalSurfaceEvaluate_comp_dehomogenize i) p

/-- The inverse evaluation is the actual fraction p/Xi^n for every weighted
homogeneous numerator; the weight-two variable uses Xi². -/
theorem literalWeightedEvaluate_fraction (i : Fin 4) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    literalWeightedEvaluate i p = literalWeightedFraction i n p hp := by
  let F : WeightedPoly →+* LiteralCoordinateLocalization i :=
    (algebraMap LiteralPointRing (LiteralCoordinateLocalization i)).comp literalPointQuotient
  have heval : eval₂Hom (F.comp C) (fun j => F (X j)) = F := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp
  have hcomp :
      (algebraMap (LiteralSurfaceCoordinateRing i) (LiteralCoordinateLocalization i)).comp
          (literalWeightedEvaluate i) =
        eval₂Hom (F.comp C) (fun j =>
          IsLocalization.Away.invSelf (literalSurfaceCoordinate i.castSucc) ^ geometricWeight j *
            F (X j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, literalWeightedEvaluate, eval₂Hom_C,
        HomogeneousLocalization.algebraMap_apply, literalCoordinateConstants_val]
      rfl
    · intro j
      simp only [RingHom.comp_apply, literalWeightedEvaluate, eval₂Hom_X',
        HomogeneousLocalization.algebraMap_apply, literalCoordinateRatio_val]
      exact mul_comm _ _
  apply HomogeneousLocalization.val_injective
  change ((algebraMap (LiteralSurfaceCoordinateRing i) (LiteralCoordinateLocalization i)).comp
    (literalWeightedEvaluate i)) p = _
  rw [hcomp, weighted_eval_scale geometricWeight (F.comp C) (fun j => F (X j))
    (IsLocalization.Away.invSelf (literalSurfaceCoordinate i.castSucc)) p n hp,
    heval, literalWeightedFraction_val]
  exact mul_comm _ _

theorem literalWeightedEvaluate_zero (i : Fin 4) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous geometricWeight n) (hz : literalPointQuotient p = 0) :
    literalWeightedEvaluate i p = 0 := by
  rw [literalWeightedEvaluate_fraction i n p hp]
  apply HomogeneousLocalization.val_injective
  simp only [literalWeightedFraction_val, hz, map_zero, zero_mul,
    HomogeneousLocalization.val_zero]

theorem literalSurfaceEvaluate_equation (i : Fin 4) (j : Fin 2) :
    literalSurfaceEvaluate i (literalDehomogenizedEquations i j) = 0 := by
  fin_cases j
  · change literalSurfaceEvaluate i
      (literalSurfaceDehomogenize i (pointEquationF (seedPoint (57 : ℂ) Complex.I))) = 0
    rw [literalSurfaceEvaluate_dehomogenize]
    apply literalWeightedEvaluate_zero i 6 _ (pointEquationF_homogeneous _)
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp [pointEquations, equationsIdeal])
  · change literalSurfaceEvaluate i
      (literalSurfaceDehomogenize i (pointEquationH (seedPoint (57 : ℂ) Complex.I))) = 0
    rw [literalSurfaceEvaluate_dehomogenize]
    apply literalWeightedEvaluate_zero i 3 _ (pointEquationH_homogeneous _)
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp [pointEquations, equationsIdeal])

def literalFromDehomogenized (i : Fin 4) :
    LiteralDehomogenizedRing i →+* LiteralSurfaceCoordinateRing i :=
  Ideal.Quotient.lift (surfaceChartIdeal (literalDehomogenizedEquations i))
    (literalSurfaceEvaluate i) (by
      change surfaceChartIdeal (literalDehomogenizedEquations i) ≤
        RingHom.ker (literalSurfaceEvaluate i)
      apply Ideal.span_le.mpr
      rintro p ⟨j, rfl⟩
      exact literalSurfaceEvaluate_equation i j)

@[simp] theorem literalFromDehomogenized_mk (i : Fin 4) (p : SurfacePoly) :
    literalFromDehomogenized i (literalDehomogenizedMap i p) =
      literalSurfaceEvaluate i p := rfl

theorem literalToDehomogenized_surfaceEvaluate (i : Fin 4) :
    (literalToDehomogenized i).comp (literalSurfaceEvaluate i) = literalDehomogenizedMap i := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [literalSurfaceEvaluate]
  · intro j
    cases j with
    | none =>
      simp only [RingHom.comp_apply, literalSurfaceEvaluate, eval₂Hom_X', map_add, map_pow,
        literalToDehomogenized_ratio, literalSurfaceDehomogenize_last]
      have h₂ := literalSurfaceDehomogenize_castSucc i 2
      change literalSurfaceDehomogenize i (X (2 : Fin 5)) = _ at h₂
      rw [h₂, map_sub, map_pow, sub_add_cancel]
    | some j =>
      simp [literalSurfaceEvaluate, literalSurfaceDehomogenize_castSucc,
        dehomogenize_succAbove, includeCurve]

theorem literalToDehomogenized_fromDehomogenized (i : Fin 4)
    (z : LiteralDehomogenizedRing i) :
    literalToDehomogenized i (literalFromDehomogenized i z) = z := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact RingHom.congr_fun (literalToDehomogenized_surfaceEvaluate i) p

theorem literalFromDehomogenized_toDehomogenized (i : Fin 4)
    (z : LiteralSurfaceCoordinateRing i) :
    literalFromDehomogenized i (literalToDehomogenized i z) = z := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (surfaceGrade (seedPoint (57 : ℂ) Complex.I)) (literalSurfaceCoordinate_mem_grade i) z
  obtain ⟨p, hp, rfl⟩ := ha
  have hp' : p.IsWeightedHomogeneous geometricWeight n := by simpa using hp
  change literalFromDehomogenized i
      (literalToDehomogenized i (literalWeightedFraction i n p hp')) =
    literalWeightedFraction i n p hp'
  rw [literalToDehomogenized_fraction, literalFromDehomogenized_mk,
    literalSurfaceEvaluate_dehomogenize, literalWeightedEvaluate_fraction i n p hp']

/-- The actual degree-zero coordinate localization of the ORIGINAL literal
projective surface is its actual dehomogenized equation quotient. -/
def literalSurfaceCoordinateEquiv (i : Fin 4) :
    LiteralSurfaceCoordinateRing i ≃+* LiteralDehomogenizedRing i where
  toFun := literalToDehomogenized i
  invFun := literalFromDehomogenized i
  left_inv := literalFromDehomogenized_toDehomogenized i
  right_inv := literalToDehomogenized_fromDehomogenized i
  map_mul' := map_mul (literalToDehomogenized i)
  map_add' := map_add (literalToDehomogenized i)

@[simp] theorem literalSurfaceCoordinateEquiv_constants (i : Fin 4) (c : ℂ) :
    literalSurfaceCoordinateEquiv i (literalCoordinateConstants i c) =
      literalDehomogenizedMap i (C c) := literalToDehomogenized_constants i c

@[simp] theorem literalSurfaceCoordinateEquiv_ratio (i : Fin 4) (j : Fin 5) :
    literalSurfaceCoordinateEquiv i (literalCoordinateRatio i j) =
      literalDehomogenizedMap i (literalSurfaceDehomogenize i (X j)) :=
  literalToDehomogenized_ratio i j

def literalCoordinateComplexAlgebra (i : Fin 4) :
    Algebra ℂ (LiteralSurfaceCoordinateRing i) :=
  (literalCoordinateConstants i).toAlgebra

attribute [local instance] literalCoordinateComplexAlgebra

/-- This complex structure is the actual degree-zero constant map proved
above, and the chart equivalence preserves it. -/
def literalSurfaceCoordinateAlgEquiv (i : Fin 4) :
    LiteralSurfaceCoordinateRing i ≃ₐ[ℂ] LiteralDehomogenizedRing i :=
  { literalSurfaceCoordinateEquiv i with
    commutes' := literalSurfaceCoordinateEquiv_constants i }

theorem literalPointEquationH :
    pointEquationH (seedPoint (57 : ℂ) Complex.I) = thetaH 1 := by
  rw [pointEquationH, pointMap_familyH]
  change fullInvariantPolynomial 3
    (CycleQ2IncidenceEquations.seedCubicCoefficients Complex.I) = _
  rw [CycleQ2IncidenceEquations.seedCubicCoefficients_polynomial]
  exact smoothH_eq_thetaH

theorem literalPointEquationF :
    pointEquationF (seedPoint (57 : ℂ) Complex.I) = actualSeedEquation 57 1 := by
  rw [pointEquationF, pointMap_familyF]
  change fullInvariantPolynomial 6
    (CycleQ2IncidenceEquations.seedSexticCoefficients (57 : ℂ) Complex.I) = _
  rw [CycleQ2IncidenceEquations.seedSexticCoefficients_polynomial]
  exact (actualSeedEquation_eq_smoothF 57).symm

theorem literalSurfaceDehomogenize_one :
    literalSurfaceDehomogenize 1 = firstSurfaceDehomogenize := by
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change literalSurfaceDehomogenize 1 (X (4 : Fin 5)) = _
    rw [literalSurfaceDehomogenize_last]
    simp [firstSurfaceDehomogenize, dehomogenize_one, firstDehomogenize, includeCurve]
  · rw [literalSurfaceDehomogenize_castSucc]
    fin_cases k <;> simp [firstSurfaceDehomogenize,
      dehomogenize_one, firstDehomogenize, includeCurve]

theorem literalSurfaceDehomogenize_two :
    literalSurfaceDehomogenize 2 = secondSurfaceDehomogenize := by
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · change literalSurfaceDehomogenize 2 (X (4 : Fin 5)) = _
    rw [literalSurfaceDehomogenize_last]
    simp [secondSurfaceDehomogenize, dehomogenize_two, secondDehomogenize, includeCurve]
  · rw [literalSurfaceDehomogenize_castSucc]
    fin_cases k <;> simp [secondSurfaceDehomogenize,
      dehomogenize_two, secondDehomogenize, includeCurve]

theorem literalDehomogenizedEquations_one :
    literalDehomogenizedEquations 1 = firstSurfaceChartEquations 57 1 := by
  funext j
  fin_cases j <;>
    simp [literalDehomogenizedEquations, firstSurfaceChartEquations,
      literalPointEquationF, literalPointEquationH, literalSurfaceDehomogenize_one,
      firstSurfaceDehomogenize_equation, firstSurfaceDehomogenize_h]

theorem literalDehomogenizedEquations_two :
    literalDehomogenizedEquations 2 = secondSurfaceChartEquations 57 1 := by
  funext j
  fin_cases j <;>
    simp [literalDehomogenizedEquations, secondSurfaceChartEquations,
      literalPointEquationF, literalPointEquationH, literalSurfaceDehomogenize_two,
      secondSurfaceDehomogenize_equation, secondSurfaceDehomogenize_h]

/-- The actual projective x₁ chart is precisely the affine surface ring
on which the conormal differential and adjunction were constructed. -/
def literalFirstSurfaceCoordinateEquiv :
    LiteralSurfaceCoordinateRing 1 ≃ₐ[ℂ]
      SurfaceChartRing (firstSurfaceChartEquations 57 1) :=
  (literalSurfaceCoordinateAlgEquiv 1).trans
    (Ideal.quotientEquivAlgOfEq ℂ
      (congrArg surfaceChartIdeal literalDehomogenizedEquations_one))

/-- The same identification on x₂, with the original second affine surface
equations and the same original weighted projective surface. -/
def literalSecondSurfaceCoordinateEquiv :
    LiteralSurfaceCoordinateRing 2 ≃ₐ[ℂ]
      SurfaceChartRing (secondSurfaceChartEquations 57 1) :=
  (literalSurfaceCoordinateAlgEquiv 2).trans
    (Ideal.quotientEquivAlgOfEq ℂ
      (congrArg surfaceChartIdeal literalDehomogenizedEquations_two))

theorem literalFirstSurfaceCoordinateEquiv_fraction (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    literalFirstSurfaceCoordinateEquiv (literalWeightedFraction 1 n p hp) =
      firstSurfaceRingMap 57 1 (literalPointSurfaceEquiv (literalPointQuotient p)) := by
  rw [literalPointQuotient_binding, firstSurfaceRingMap_polynomial]
  change Ideal.quotientEquivAlgOfEq ℂ
      (congrArg surfaceChartIdeal literalDehomogenizedEquations_one)
      (literalToDehomogenized 1 (literalWeightedFraction 1 n p hp)) = _
  rw [literalToDehomogenized_fraction]
  simp only [literalDehomogenizedMap]
  rw [Ideal.quotientEquivAlgOfEq_mk ℂ
    (congrArg surfaceChartIdeal literalDehomogenizedEquations_one)]
  rw [literalSurfaceDehomogenize_one]

theorem literalSecondSurfaceCoordinateEquiv_fraction (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    literalSecondSurfaceCoordinateEquiv (literalWeightedFraction 2 n p hp) =
      secondSurfaceRingMap 57 1 (literalPointSurfaceEquiv (literalPointQuotient p)) := by
  rw [literalPointQuotient_binding, secondSurfaceRingMap_polynomial]
  change Ideal.quotientEquivAlgOfEq ℂ
      (congrArg surfaceChartIdeal literalDehomogenizedEquations_two)
      (literalToDehomogenized 2 (literalWeightedFraction 2 n p hp)) = _
  rw [literalToDehomogenized_fraction]
  simp only [literalDehomogenizedMap]
  rw [Ideal.quotientEquivAlgOfEq_mk ℂ
    (congrArg surfaceChartIdeal literalDehomogenizedEquations_two)]
  rw [literalSurfaceDehomogenize_two]

end CycleQ2GeometricSurfaceAdjunction
end
