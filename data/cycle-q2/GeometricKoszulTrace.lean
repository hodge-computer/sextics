import Proposal.GeometricDegreeOneCech
import Proposal.GeometricHomogeneousBoundary

/-!
# The homogeneous Koszul relation in the existing projective Cech quotient

This file uses the existing `FirstDegreeOne`, `SecondDegreeOne`, and
`degreeNineCechClass` objects, whose definitions now live in the independently
checked algebraic core imported by `GeometricProjectiveCurve`.

A homogeneous degree-nine relation among the actual curve equations and
the two quartic denominators gives quintic single-chart numerators. Their
actual degree-one sections are a coboundary for the original numerator
class. In particular, this comparison retains the homogeneous degree of
the chart witnesses; it does not merely prove vanishing after forgetting
the grading. No canonical-bundle or Serre-trace identification is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricKoszulTrace

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricProjectiveCurve
open CycleQ2SeedCech (curveA curveB)

/-- The first denominator's actual homogeneous polynomial representative. -/
def firstQuartic (r : ℂ) : Poly := C (3 * r ^ 2) * curveA ^ 2

/-- The second denominator's actual homogeneous polynomial representative. -/
def secondQuartic : Poly := C 3 * curveB ^ 4

theorem firstQuartic_homogeneous (r : ℂ) : (firstQuartic r).IsHomogeneous 4 :=
  ((isHomogeneous_X ℂ (1 : Fin 4)).mul
    (isHomogeneous_X ℂ (3 : Fin 4))).pow 2 |>.C_mul (3 * r ^ 2)

theorem secondQuartic_homogeneous : secondQuartic.IsHomogeneous 4 :=
  ((isHomogeneous_X ℂ (2 : Fin 4)).pow 4).C_mul 3

@[simp] theorem curveMap_firstQuartic (r θ : ℂ) :
    curveMap r θ (firstQuartic r) = curveG1 r θ :=
  (ambientCurveMap_g1 r θ).symm

@[simp] theorem curveMap_secondQuartic (r θ : ℂ) :
    curveMap r θ secondQuartic = curveG2 r θ :=
  (ambientCurveMap_g2 r θ).symm

def fourGeneratorIdeal (r θ : ℂ) : Ideal Poly :=
  Ideal.span {relation r 0, curveH θ, firstQuartic r, secondQuartic}

def firstQuinticSection (r θ : ℂ) (p : Poly) (hp : p.IsHomogeneous 5) :
    FirstDegreeOne r θ :=
  ⟨awayFraction r θ (curveG1 r θ) 1 (curveMap r θ p),
    awayFraction_mem_degreeOne r θ _ 4 (curveG1_mem_grade r θ) 1 _
      (curveMap_mem_grade r θ hp)⟩

def secondQuinticSection (r θ : ℂ) (p : Poly) (hp : p.IsHomogeneous 5) :
    SecondDegreeOne r θ :=
  ⟨awayFraction r θ (curveG2 r θ) 1 (curveMap r θ p),
    awayFraction_mem_degreeOne r θ _ 4 (curveG2_mem_grade r θ) 1 _
      (curveMap_mem_grade r θ hp)⟩

theorem awayFraction_one_eq_chartFraction (r θ : ℂ) (f a : CurveRing r θ) :
    awayFraction r θ f 1 a = CycleQ2GeometricHomogeneousBoundary.chartFraction f a := by
  change Localization.mk a (⟨f ^ 1, 1, rfl⟩ : Submonoid.powers f) =
    IsLocalization.mk' (Localization.Away f) a
      (CycleQ2GeometricHomogeneousBoundary.chartDenominator f)
  rw [Localization.mk_eq_mk']
  congr 1
  apply Subtype.ext
  exact pow_one f

theorem degreeNineRepresentative_coe (r θ : ℂ) (p : Poly) (hp : p.IsHomogeneous 9) :
    (degreeNineRepresentative r θ p hp : Overlap r θ) =
      CycleQ2GeometricKoszulKernel.representative (curveG1 r θ) (curveG2 r θ)
        (curveMap r θ p) := by
  change Localization.mk (curveMap r θ p)
      (⟨(curveG1 r θ * curveG2 r θ) ^ 1, 1, rfl⟩ :
        Submonoid.powers (curveG1 r θ * curveG2 r θ)) =
    IsLocalization.mk' (Overlap r θ) (curveMap r θ p)
      (CycleQ2GeometricKoszulKernel.denominator (curveG1 r θ) (curveG2 r θ))
  rw [Localization.mk_eq_mk']
  congr 1
  apply Subtype.ext
  exact pow_one _

/-- A relation with quintic chart numerators is a boundary in the existing
degree-one Cech quotient, with its original first-minus-second convention. -/
theorem degreeNineCechClass_zero_of_quintic_relation (r θ : ℂ) (p c d : Poly)
    (hp : p.IsHomogeneous 9) (hc : c.IsHomogeneous 5) (hd : d.IsHomogeneous 5)
    (hrelation : curveMap r θ p =
      curveMap r θ c * curveG1 r θ + curveMap r θ d * curveG2 r θ) :
    degreeNineCechClass r θ p hp = 0 := by
  have hrep : (degreeNineRepresentative r θ p hp : Overlap r θ) =
      firstRestriction r θ (firstQuinticSection r θ d hd) +
        secondRestriction r θ (secondQuinticSection r θ c hc) := by
    rw [degreeNineRepresentative_coe, hrelation]
    change CycleQ2GeometricKoszulKernel.representative (curveG1 r θ) (curveG2 r θ)
        (curveMap r θ c * curveG1 r θ + curveMap r θ d * curveG2 r θ) =
      firstRestriction r θ (awayFraction r θ (curveG1 r θ) 1 (curveMap r θ d)) +
        secondRestriction r θ (awayFraction r θ (curveG2 r θ) 1 (curveMap r θ c))
    rw [awayFraction_one_eq_chartFraction, awayFraction_one_eq_chartFraction]
    exact CycleQ2GeometricHomogeneousBoundary.representative_relation _ _ _ _
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨(firstQuinticSection r θ d hd, -(secondQuinticSection r θ c hc)), ?_⟩
  apply Subtype.ext
  change (firstDegreeOneRestriction r θ (firstQuinticSection r θ d hd) : Overlap r θ) -
      (secondDegreeOneRestriction r θ (-(secondQuinticSection r θ c hc)) : Overlap r θ) =
    (degreeNineRepresentative r θ p hp : Overlap r θ)
  simpa only [map_neg, Submodule.coe_neg, firstDegreeOneRestriction_coe,
    secondDegreeOneRestriction_coe, sub_neg_eq_add] using hrep.symm

/-- Homogeneous ideal membership now kills the actual existing projective
degree-one Cech class, using proved homogeneous chart witnesses. -/
theorem degreeNineCechClass_zero_of_mem (r θ : ℂ) (p : Poly)
    (hp : p.IsHomogeneous 9) (hmem : p ∈ fourGeneratorIdeal r θ) :
    degreeNineCechClass r θ p hp = 0 := by
  obtain ⟨a, b, c, d, _, _, hc, hd, heq⟩ :=
    CycleQ2GeometricGradedWitness.degreeNine_witness
      (relation r 0) (curveH θ) (firstQuartic r) secondQuartic p
      (relation_zero_homogeneous r) (sparse_curveH_homogeneous θ)
      (firstQuartic_homogeneous r) secondQuartic_homogeneous hp hmem
  apply degreeNineCechClass_zero_of_quintic_relation r θ p c d hp hc hd
  rw [← heq]
  simp only [map_add, map_mul, curveMap_f1, curveMap_h, mul_zero, zero_add,
    curveMap_firstQuartic, curveMap_secondQuartic]

/-- Forgetting the degree of an actual homogeneous coboundary gives an
actual unrestricted localization coboundary. -/
theorem boundary_zero_of_degreeNineCechClass_zero (r θ : ℂ) (p : Poly)
    (hp : p.IsHomogeneous 9) (hz : degreeNineCechClass r θ p hp = 0) :
    CycleQ2GeometricKoszulKernel.boundary (curveG1 r θ) (curveG2 r θ)
      (curveMap r θ p) = 0 := by
  have hmem : degreeNineRepresentative r θ p hp ∈ degreeOneBoundaries r θ :=
    (QuotientAddGroup.eq_zero_iff _).mp hz
  obtain ⟨⟨a, b⟩, hab⟩ := hmem
  have hval := congrArg (fun z : OverlapDegreeOne r θ => (z : Overlap r θ)) hab
  change (firstDegreeOneRestriction r θ a : Overlap r θ) -
      (secondDegreeOneRestriction r θ b : Overlap r θ) =
    (degreeNineRepresentative r θ p hp : Overlap r θ) at hval
  rw [firstDegreeOneRestriction_coe, secondDegreeOneRestriction_coe] at hval
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [← degreeNineRepresentative_coe r θ p hp, ← hval]
  exact Submodule.sub_mem _
    (Submodule.mem_sup_left ⟨(a : FirstOpen r θ), rfl⟩)
    (Submodule.mem_sup_right ⟨(b : SecondOpen r θ), rfl⟩)

/-- Under the actual regular-pair hypotheses, the original homogeneous
Cech class has exactly the four-generator ideal as its numerator kernel.
No injectivity of a map that forgets the grading is assumed. -/
theorem degreeNineCechClass_eq_zero_iff (r θ : ℂ)
    (hg₁ : IsSMulRegular (CurveRing r θ) (curveG1 r θ))
    (hg₂ : IsSMulRegular (CurveRing r θ ⧸ Ideal.span {curveG1 r θ}) (curveG2 r θ))
    (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineCechClass r θ p hp = 0 ↔ p ∈ fourGeneratorIdeal r θ := by
  constructor
  · intro hz
    have hg₁' : IsSMulRegular (CurveRing r θ) (curveMap r θ (firstQuartic r)) := by
      rwa [curveMap_firstQuartic]
    have hg₂' : IsSMulRegular
        (CurveRing r θ ⧸ Ideal.span {curveMap r θ (firstQuartic r)})
        (curveMap r θ secondQuartic) := by
      rwa [curveMap_firstQuartic, curveMap_secondQuartic]
    have hi := CycleQ2GeometricHomogeneousBoundary.quotient_boundary_eq_zero_iff
      (relation r 0) (curveH θ) (firstQuartic r) secondQuartic p hg₁' hg₂'
    change CycleQ2GeometricKoszulKernel.boundary
        (curveMap r θ (firstQuartic r)) (curveMap r θ secondQuartic)
        (curveMap r θ p) = 0 ↔ p ∈ fourGeneratorIdeal r θ at hi
    rw [curveMap_firstQuartic, curveMap_secondQuartic] at hi
    exact hi.mp (boundary_zero_of_degreeNineCechClass_zero r θ p hp hz)
  · exact degreeNineCechClass_zero_of_mem r θ p hp

/-- The actual reduced seed ideal uses unscaled quartics. The nonzero
constants `3*r²` and `3` identify it with the actual denominator ideal. -/
theorem fourGeneratorIdeal_zero_eq_reducedIdeal (r : ℂ) (hr : r ≠ 0) :
    fourGeneratorIdeal r 0 = reducedIdeal r := by
  have hrel (i : Fin 4) : relation r i ∈ reducedIdeal r :=
    Ideal.subset_span ⟨i, rfl⟩
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact hrel 0
    · simpa [curveH, relation] using hrel 3
    · have hm := (reducedIdeal r).mul_mem_left (C (3 * r ^ 2)) (hrel 1)
      simpa [firstQuartic, curveA, relation, mul_pow] using hm
    · have hm := (reducedIdeal r).mul_mem_left (C 3) (hrel 2)
      simpa [secondQuartic, curveB, relation] using hm
  · rw [reducedIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hf : relation r 0 ∈ fourGeneratorIdeal r 0 := Ideal.subset_span (by simp)
    have hh : curveH 0 ∈ fourGeneratorIdeal r 0 := Ideal.subset_span (by simp)
    have hq₁ : firstQuartic r ∈ fourGeneratorIdeal r 0 := Ideal.subset_span (by simp)
    have hq₂ : secondQuartic ∈ fourGeneratorIdeal r 0 := Ideal.subset_span (by simp)
    fin_cases i
    · exact hf
    · have hm := (fourGeneratorIdeal r 0).mul_mem_left (C ((3 * r ^ 2)⁻¹)) hq₁
      have heq : C ((3 * r ^ 2)⁻¹) * firstQuartic r = relation r 1 := by
        unfold firstQuartic
        rw [← mul_assoc, ← map_mul,
          inv_mul_cancel₀ (mul_ne_zero (by norm_num) (pow_ne_zero _ hr)), map_one, one_mul]
        simp [relation, curveA, mul_pow]
      rwa [heq] at hm
    · have hm := (fourGeneratorIdeal r 0).mul_mem_left (C ((3 : ℂ)⁻¹)) hq₂
      have heq : C ((3 : ℂ)⁻¹) * secondQuartic = relation r 2 := by
        unfold secondQuartic
        rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0),
          map_one, one_mul]
        rfl
      rwa [heq] at hm
    · simpa [curveH, relation] using hh

/-- A homogeneous relation in the existing reduced seed quotient is an
actual degree-one coboundary. This statement needs no regularity premise. -/
theorem degreeNineCechClass_zero_of_reducedIdeal (r : ℂ) (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 9) (hmem : p ∈ reducedIdeal r) :
    degreeNineCechClass r 0 p hp = 0 := by
  apply degreeNineCechClass_zero_of_mem r 0 p hp
  rwa [fourGeneratorIdeal_zero_eq_reducedIdeal r hr]

theorem degreeNineCechClass_eq_zero_iff_reducedIdeal (r : ℂ) (hr : r ≠ 0)
    (hg₁ : IsSMulRegular (CurveRing r 0) (curveG1 r 0))
    (hg₂ : IsSMulRegular (CurveRing r 0 ⧸ Ideal.span {curveG1 r 0}) (curveG2 r 0))
    (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineCechClass r 0 p hp = 0 ↔ p ∈ reducedIdeal r := by
  rw [degreeNineCechClass_eq_zero_iff r 0 hg₁ hg₂,
    fourGeneratorIdeal_zero_eq_reducedIdeal r hr]

theorem degreeNineRepresentative_sub (r θ : ℂ) (p q : Poly)
    (hp : p.IsHomogeneous 9) (hq : q.IsHomogeneous 9) :
    degreeNineRepresentative r θ (p - q) (hp.sub hq) =
      degreeNineRepresentative r θ p hp - degreeNineRepresentative r θ q hq := by
  apply Subtype.ext
  change (degreeNineRepresentative r θ (p - q) (hp.sub hq) : Overlap r θ) =
    (degreeNineRepresentative r θ p hp : Overlap r θ) -
      (degreeNineRepresentative r θ q hq : Overlap r θ)
  rw [degreeNineRepresentative_coe, degreeNineRepresentative_coe,
    degreeNineRepresentative_coe, map_sub, map_sub]

theorem degreeNineCechClass_sub (r θ : ℂ) (p q : Poly)
    (hp : p.IsHomogeneous 9) (hq : q.IsHomogeneous 9) :
    degreeNineCechClass r θ (p - q) (hp.sub hq) =
      degreeNineCechClass r θ p hp - degreeNineCechClass r θ q hq := by
  change (QuotientAddGroup.mk' (degreeOneBoundaries r θ))
      (degreeNineRepresentative r θ (p - q) (hp.sub hq)) =
    (QuotientAddGroup.mk' (degreeOneBoundaries r θ)) (degreeNineRepresentative r θ p hp) -
      (QuotientAddGroup.mk' (degreeOneBoundaries r θ)) (degreeNineRepresentative r θ q hq)
  rw [degreeNineRepresentative_sub, map_sub]

/-- The existing degree-nine class is independent of the homogeneous
representative in the actual reduced seed quotient. No regularity premise
or assumed equality of Cech classes enters this descent statement. -/
theorem degreeNineCechClass_eq_of_reducedQuotient_eq (r : ℂ) (hr : r ≠ 0)
    (p q : Poly) (hp : p.IsHomogeneous 9) (hq : q.IsHomogeneous 9)
    (heq : Ideal.Quotient.mk (reducedIdeal r) p = Ideal.Quotient.mk (reducedIdeal r) q) :
    degreeNineCechClass r 0 p hp = degreeNineCechClass r 0 q hq := by
  have hmem : p - q ∈ reducedIdeal r := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, heq, sub_self]
  have hz := degreeNineCechClass_zero_of_reducedIdeal r hr (p - q) (hp.sub hq) hmem
  rw [degreeNineCechClass_sub r 0 p q hp hq] at hz
  exact sub_eq_zero.mp hz

end CycleQ2GeometricKoszulTrace

end
