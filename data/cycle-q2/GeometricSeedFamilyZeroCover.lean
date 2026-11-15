import Proposal.GeometricSeedFamilyZeroCoefficients
import Proposal.GeometricSeedFamilyJacobian
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The whole actual zero fiber lies in the relative Jacobian open

Coefficient-prime transport places every projective point over zero in a
weight-one chart. In that chart, the literal normalization and the Fermat
equation exclude simultaneous vanishing of all remaining partials. These
are specializations of the original relative derivatives, so every actual
point over zero lies in the already constructed relative Jacobian open.
No global fiber isomorphism or fiberwise smoothness implication is assumed.

Source-only draft: no Lean elaboration, compilation, or kernel replay has
been run. Prepared for `fqlx` with OpenAI ChatGPT assistance, following
Ben Diamond's geometric route and the project's incidence-prime method.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFamilyZeroCover

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSeedSmooth CycleQ2GeometricIncidenceProj
  CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily
  CycleQ2SeedProjectiveSpecialization CycleQ2SeedFamilyZeroCoefficients
  CycleQ2SeedFamilyNormalized CycleQ2SeedFamilyChart CycleQ2SeedFamilyJacobian

theorem irrelevant_le_coordinateIdeal (r : ℂ) :
    (HomogeneousIdeal.irrelevant (familyGrade r)).toIdeal ≤
      Ideal.span (Set.range (familyCoordinate r)) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn a ha
  obtain ⟨p, hp, rfl⟩ := ha
  have hpI : p ∈ MvPolynomial.idealOfVars (Fin 5) ParameterRing := by
    have hpow : p ∈ MvPolynomial.idealOfVars (Fin 5) ParameterRing ^ 1 := by
      apply (MvPolynomial.mem_pow_idealOfVars_iff' 1 p).mpr
      intro e he
      have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
      subst e
      by_contra hc
      have hz : 0 = n := by simpa only [map_zero] using hp hc
      omega
    simpa only [pow_one] using hpow
  have hmap : MvPolynomial.idealOfVars (Fin 5) ParameterRing ≤
      (Ideal.span (Set.range (familyCoordinate r))).comap (familyQuotient r) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨j, rfl⟩
  exact hmap hpI

theorem exists_coordinate_not_mem (r : ℂ) (x : family r) :
    ∃ j : Fin 5, familyCoordinate r j ∉ x.asHomogeneousIdeal.toIdeal := by
  classical
  by_contra! h
  apply x.not_irrelevant_le
  apply (irrelevant_le_coordinateIdeal r).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  exact h j

/-- Every actual projective point over zero lies in a degree-one chart. -/
theorem exists_weightOne_of_over_zero (r : ℂ) (hr : r ^ 3 = 2)
    (s : Spec (CommRingCat.of ℂ)) (x : family r)
    (hx : familyToParameters r x = zeroParameterMorphism s) :
    ∃ i : Fin 4, x ∈ coordinateOpen r i := by
  classical
  change ∃ i : Fin 4, familyCoordinate r i.castSucc ∉ x.asHomogeneousIdeal.toIdeal
  letI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let P : Ideal FamilyPolynomial :=
    x.asHomogeneousIdeal.toIdeal.comap (familyQuotient r)
  letI : P.IsPrime := inferInstance
  have hcoeff : ∀ a : ParameterRing, zeroCoefficientMap a = 0 → C a ∈ P := by
    intro a ha
    exact zero_kernel_mem_of_over_zero r x s hx a ha
  have hF : familyEquation r ∈ P := by
    change familyQuotient r (familyEquation r) ∈ x.asHomogeneousIdeal.toIdeal
    rw [familyEquation_zero]
    exact Ideal.zero_mem _
  let J := specializedPrime P
  letI : J.IsPrime := inferInstance
  have hFseed : seedFamily r 0 ∈ J := by
    simpa only [zeroPolynomialSpecialization_equation] using
      specialization_mem P hcoeff (familyEquation r) hF
  by_contra! h
  have hz (i : Fin 4) : Ideal.Quotient.mk J (X i.castSucc) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (coordinate_mem_specializedPrime_iff P i.castSucc).mpr
    exact h i
  have hFzero := Ideal.Quotient.eq_zero_iff_mem.mpr hFseed
  rw [seedFamily_zero_of_cube_two r hr] at hFzero
  have hw3 : Ideal.Quotient.mk J (X (4 : Fin 5)) ^ 3 = 0 := by
    simpa only [map_add, map_pow, hz 0, hz 1, hz 2, hz 3,
      zero_pow (by decide : (6 : ℕ) ≠ 0), zero_add] using hFzero
  have hw : (X (4 : Fin 5) : FamilyPolynomial) ∈ P :=
    (coordinate_mem_specializedPrime_iff P 4).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero hw3))
  obtain ⟨j, hj⟩ := exists_coordinate_not_mem r x
  fin_cases j
  · exact hj (h 0)
  · exact hj (h 1)
  · exact hj (h 2)
  · exact hj (h 3)
  · exact hj hw

private theorem exists_seedDerivative_not_mem (r : ℂ) (hr : r ^ 3 = 2)
    (i : Fin 4) (J : Ideal SeedPolynomial) [J.IsPrime]
    (hF : seedFamily r 0 ∈ J) (hi : (X i.castSucc - 1 : SeedPolynomial) ∈ J) :
    ∃ j : OtherCoordinate i, pderiv j.1 (seedFamily r 0) ∉ J := by
  classical
  by_contra! h
  have hz (j : OtherCoordinate i) : Ideal.Quotient.mk J (X j.1) = 0 := by
    have hδ := Ideal.Quotient.eq_zero_iff_mem.mpr (h j)
    rw [CycleQ2SeedFermatCone.zeroCubic_pderiv r hr j.1] at hδ
    simp only [map_mul, map_pow] at hδ
    have hc : IsUnit (CycleQ2SeedFermatCone.coordinateDegree j.1 : ℂ) := by
      apply isUnit_iff_ne_zero.mpr
      rcases j with ⟨j, hj⟩
      fin_cases j <;> norm_num [CycleQ2SeedFermatCone.coordinateDegree]
    have hc' : IsUnit (Ideal.Quotient.mk J
        (C (CycleQ2SeedFermatCone.coordinateDegree j.1 : ℂ))) :=
      hc.map ((Ideal.Quotient.mk J).comp MvPolynomial.C)
    exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hδ).resolve_left hc'.ne_zero)
  have hi' : Ideal.Quotient.mk J (X i.castSucc) = 1 := by
    have h₁ := Ideal.Quotient.eq_zero_iff_mem.mpr hi
    rw [map_sub, map_one] at h₁
    exact sub_eq_zero.mp h₁
  have hcoord (j : Fin 5) :
      Ideal.Quotient.mk J (X j) = if j = i.castSucc then 1 else 0 := by
    by_cases hj : j = i.castSucc
    · subst j
      simpa only [if_pos rfl] using hi'
    · simpa only [if_neg hj] using hz ⟨j, hj⟩
  have hFzero := Ideal.Quotient.eq_zero_iff_mem.mpr hF
  rw [seedFamily_zero_of_cube_two r hr] at hFzero
  simp only [map_add, map_pow, hcoord] at hFzero
  fin_cases i <;> norm_num at hFzero

/-- At a normalized chart point over zero, one of the actual relative
derivatives is nonzero in its prime quotient. -/
theorem exists_derivative_not_mem_of_over_zero (r : ℂ) (hr : r ^ 3 = 2)
    (i : Fin 4) (s : Spec (CommRingCat.of ℂ)) (q : normalizedScheme r i)
    (hq : normalizedToParameters r i q = zeroParameterMorphism s) :
    ∃ j : OtherCoordinate i, normalizedDerivative r i j.1 ∉ q.asIdeal := by
  letI : q.asIdeal.IsPrime := q.isPrime
  let P : Ideal FamilyPolynomial := q.asIdeal.comap (normalizedQuotient r i)
  letI : P.IsPrime := inferInstance
  have hcoeff : ∀ a : ParameterRing, zeroCoefficientMap a = 0 → C a ∈ P := by
    intro a ha
    have hmem : a ∈ (normalizedToParameters r i q).asIdeal := by
      rw [hq]
      change zeroCoefficientMap a ∈ s.asIdeal
      rw [ha]
      exact Ideal.zero_mem _
    exact hmem
  have hF : familyEquation r ∈ P := by
    change normalizedQuotient r i (familyEquation r) ∈ q.asIdeal
    rw [normalizedEquation]
    exact Ideal.zero_mem _
  have hi : (X i.castSucc - 1 : FamilyPolynomial) ∈ P := by
    change normalizedQuotient r i (X i.castSucc - 1) ∈ q.asIdeal
    have hz := normalizedQuotient_relation r i 1
    change normalizedQuotient r i (X i.castSucc - 1) = 0 at hz
    rw [hz]
    exact Ideal.zero_mem _
  let J := specializedPrime P
  letI : J.IsPrime := inferInstance
  have hFseed : seedFamily r 0 ∈ J := by
    simpa only [zeroPolynomialSpecialization_equation] using
      specialization_mem P hcoeff (familyEquation r) hF
  have hiseed : (X i.castSucc - 1 : SeedPolynomial) ∈ J := by
    change coefficientLift (X i.castSucc - 1) ∈ P
    simpa only [coefficientLift, map_sub, map_one, MvPolynomial.map_X] using hi
  obtain ⟨j, hj⟩ := exists_seedDerivative_not_mem r hr i J hFseed hiseed
  refine ⟨j, fun hδ => hj ?_⟩
  have hδP : pderiv j.1 (familyEquation r) ∈ P := hδ
  simpa only [zeroSpecialization_pderiv_equation] using
    specialization_mem P hcoeff (pderiv j.1 (familyEquation r)) hδP

/-- The entire actual projective zero fiber lies in the constructed
relative-dimension-three open of the original parameter family. -/
theorem zeroFiber_mem_smoothOpen (r : ℂ) (hr : r ^ 3 = 2)
    (s : Spec (CommRingCat.of ℂ)) (x : family r)
    (hx : familyToParameters r x = zeroParameterMorphism s) :
    x ∈ smoothOpen r := by
  obtain ⟨i, hi⟩ := exists_weightOne_of_over_zero r hr s x hx
  obtain ⟨q, hq⟩ := exists_normalizedChart_preimage r i x hi
  have hbase : normalizedToParameters r i q = zeroParameterMorphism s := by
    change (Spec.map (CommRingCat.ofHom
      (algebraMap ParameterRing (NormalizedRing r i)))) q = _
    rw [← normalizedChartToFamily_overParameters]
    change familyToParameters r (normalizedChartToFamily r i q) = _
    rw [hq]
    exact hx
  obtain ⟨j, hj⟩ := exists_derivative_not_mem_of_over_zero r hr i s q hbase
  rw [← hq]
  exact mem_smoothOpen_of_derivative_not_mem r i j q hj

end CycleQ2SeedFamilyZeroCover

end

#print axioms CycleQ2SeedFamilyZeroCover.exists_weightOne_of_over_zero
#print axioms CycleQ2SeedFamilyZeroCover.exists_derivative_not_mem_of_over_zero
#print axioms CycleQ2SeedFamilyZeroCover.zeroFiber_mem_smoothOpen
