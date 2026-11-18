import Proposal.GeometricIncidenceFamilyContainment
import Proposal.GeometricSeedFermatProj
import Proposal.SolutionSupport02Part02
import Mathlib.Algebra.MvPolynomial.Division

/-!
# The full invariant weighted projective hypersurface

Use the original invariant sextic after an arbitrary coefficient specialization.
When the coefficient of the pure cube in the weight-two variable is a unit,
the four original weight-one coordinate opens cover its projective spectrum.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricHodgeThreefold

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing universalF seedEvaluation)
open CycleQ2IncidenceNormalForm CycleQ2GeometricIncidenceProj

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

def equation : MvPolynomial (Fin 5) R := MvPolynomial.map φ universalF

theorem equation_homogeneous : (equation φ).IsWeightedHomogeneous geometricWeight 6 := by
  rw [equation, universalF, map_fullInvariantPolynomial]
  exact homogeneous_of_character (fullInvariantPolynomial_homogeneous 6 _)

abbrev cone := MvPolynomial (Fin 5) R ⧸ Ideal.span {equation φ}

def quotient : MvPolynomial (Fin 5) R →+* cone φ := Ideal.Quotient.mk _
def coord (j : Fin 5) : cone φ := quotient φ (X j)

theorem equation_zero : quotient φ (equation φ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

abbrev grade (n : ℕ) : Submodule R (cone φ) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
    (PolynomialGrade R) (Ideal.span {equation φ}) n

instance coneGradedRing : GradedRing (grade φ) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing _ _
    (Ideal.homogeneous_span _ _ (by
      rintro p (rfl : p = equation φ)
      exact ⟨6, equation_homogeneous φ⟩))

theorem quotient_mem_grade {n : ℕ} (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) : quotient φ p ∈ grade φ n :=
  ⟨p, hp, rfl⟩

theorem coord_mem_grade (j : Fin 5) : coord φ j ∈ grade φ (geometricWeight j) :=
  quotient_mem_grade φ (X j) (isWeightedHomogeneous_X _ _ _)

theorem weightOne_mem_grade (i : Fin 4) : coord φ i.castSucc ∈ grade φ 1 := by
  simpa only [CycleQ2SeedFermatProj.geometricWeight_castSucc] using coord_mem_grade φ i.castSucc

def threefold : Scheme := Proj (grade φ)

def coefficient : R →+* grade φ 0 := algebraMap R (grade φ 0)

def toBase : threefold φ ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (grade φ) ≫ Spec.map (CommRingCat.ofHom (coefficient φ))

def coordinateOpen (i : Fin 4) : (threefold φ).Opens :=
  Proj.basicOpen (grade φ) (coord φ i.castSucc)

abbrev ChartRing (i : Fin 4) := HomogeneousLocalization.Away (grade φ) (coord φ i.castSucc)

def chartCoefficient (i : Fin 4) : R →+* ChartRing φ i :=
  (HomogeneousLocalization.fromZeroRingHom (grade φ) (Submonoid.powers (coord φ i.castSucc))).comp
    (coefficient φ)

instance chartAlgebra (i : Fin 4) : Algebra R (ChartRing φ i) := (chartCoefficient φ i).toAlgebra

@[simp] theorem chartCoefficient_val (i : Fin 4) (c : R) :
    (chartCoefficient φ i c).val = algebraMap (cone φ) (Localization.Away (coord φ i.castSucc))
      (quotient φ (C c)) := by
  change Localization.mk (quotient φ (C c)) 1 = _
  rw [Localization.mk_one_eq_algebraMap]

def coordinateChart (i : Fin 4) : (coordinateOpen φ i).toScheme ≅
    Spec (CommRingCat.of (ChartRing φ i)) :=
  Proj.basicOpenIsoSpec (grade φ) (coord φ i.castSucc) (weightOne_mem_grade φ i) (by decide)

theorem coordinateChart_overBase (i : Fin 4) :
    (coordinateChart φ i).inv ≫ (coordinateOpen φ i).ι ≫ toBase φ =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing φ i))) := by
  change (Proj.basicOpenIsoSpec (grade φ) (coord φ i.castSucc)
    (weightOne_mem_grade φ i) (by decide)).inv ≫
    (Proj.basicOpen (grade φ) (coord φ i.castSucc)).ι ≫ toBase φ = _
  rw [Proj.basicOpenIsoSpec_inv_ι_assoc, toBase, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

theorem irrelevant_le_coordinateIdeal :
    (HomogeneousIdeal.irrelevant (grade φ)).toIdeal ≤ Ideal.span (Set.range (coord φ)) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn p hp
  obtain ⟨f,hf,rfl⟩ := hp
  have hi : Ideal.span (Set.range (X : Fin 5 → MvPolynomial (Fin 5) R)) ≤
      (Ideal.span (Set.range (coord φ))).comap (quotient φ) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Ideal.subset_span ⟨j,rfl⟩
  exact hi (CycleQ2IncidenceFamilyContainment.homogeneous_mem_variableIdeal hn hf)

def vertexCoefficient : CoeffRing := X fullSexticLeadingIndex

theorem equation_raw : equation φ =
    monomial (Finsupp.single 4 3) (φ vertexCoefficient) +
      ∑ e : FullSexticTailIndex, monomial (fullExponentOf e.val.val) (φ (X e.val)) := by
  rw [equation, universalF, map_fullInvariantPolynomial, fullInvariantPolynomial_sextic]
  rfl

private theorem tail_has_linear (e : FullSexticTailIndex) :
    ∃ j : Fin 4, fullExponentOf e.val.val j.castSucc ≠ 0 := by
  by_contra! h
  have hd := e.val.property.1
  have h4 := e.property
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [fullExponentOf_apply] at h0 h1 h2 h3
  change ((e.val.val 0).val = 0) at h0
  change ((e.val.val 1).val = 0) at h1
  change ((e.val.val 2).val = 0) at h2
  change ((e.val.val 3).val = 0) at h3
  simp only [fullDegree, h0, h1, h2, h3, zero_add] at hd
  omega

theorem exists_weightOne_not_mem (hu : IsUnit (φ vertexCoefficient)) (q : threefold φ) :
    ∃ i : Fin 4, coord φ i.castSucc ∉ q.asHomogeneousIdeal.toIdeal := by
  classical
  by_contra! h
  let P := q.asHomogeneousIdeal.toIdeal
  letI : P.IsPrime := q.isPrime
  let ρ := (Ideal.Quotient.mk P).comp (quotient φ)
  have hz (j : Fin 4) : ρ (X j.castSucc) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (h j)
  have ht (e : FullSexticTailIndex) :
      ρ (monomial (fullExponentOf e.val.val) (φ (X e.val))) = 0 := by
    obtain ⟨j,hj⟩ := tail_has_linear e
    obtain ⟨p,hp⟩ := (MvPolynomial.X_dvd_monomial (r := φ (X e.val))).mpr (Or.inr hj)
    rw [hp, map_mul, hz, zero_mul]
  have he : ρ (equation φ) = 0 := by
    change Ideal.Quotient.mk P (quotient φ (equation φ)) = 0
    rw [equation_zero, map_zero]
  have hraw := (congrArg ρ (equation_raw φ)).symm.trans he
  rw [map_add, map_sum, Finset.sum_eq_zero (fun e _ => ht e), add_zero] at hraw
  have hw : ρ (X (4 : Fin 5)) ^ 3 = 0 := by
    have he' : ρ (C (φ vertexCoefficient)) * ρ (X (4 : Fin 5)) ^ 3 = 0 := by
      rw [← map_pow, ← map_mul, X_pow_eq_monomial, C_mul_monomial, mul_one]
      exact hraw
    exact (hu.map (ρ.comp C)).mul_left_cancel (he'.trans (mul_zero _).symm)
  have h4 : coord φ 4 ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero hw)
  apply q.not_irrelevant_le
  refine (irrelevant_le_coordinateIdeal φ).trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨j,rfl⟩
  fin_cases j
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h4

theorem coordinateOpens_cover (hu : IsUnit (φ vertexCoefficient)) :
    (⨆ i : Fin 4, coordinateOpen φ i) = ⊤ := by
  apply top_le_iff.mp
  intro q _
  obtain ⟨i, hi⟩ := exists_weightOne_not_mem φ hu q
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

end CycleQ2GeometricHodgeThreefold
end

#print axioms CycleQ2GeometricHodgeThreefold.coordinateChart_overBase
#print axioms CycleQ2GeometricHodgeThreefold.coordinateOpens_cover
