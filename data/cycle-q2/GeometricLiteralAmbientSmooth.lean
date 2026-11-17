import Proposal.GeometricLiteralAmbientElimination
import Proposal.GeometricSeedFamilySmoothNeighborhood
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The ambient cubic-family fiber at the incidence seed

The parameter point uses the coefficients of the cubic `smoothB`.
The specialized equation is `smoothF r Complex.I`. Its weighted vertex
is absent for every complex parameter `r`. On a weight-one chart, a
nonvanishing derivative in another coordinate puts the point in the
relative dimension-three smooth open of the original cubic family. The exact
branch-gradient certificate establishes this criterion at the trace seed `r = 57`.

Prepared for `fqlx` with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAmbientSmooth

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSeedSmooth CycleQ2IncidenceEquations
  CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily CycleQ2SeedProjectiveSpecialization
  CycleQ2SeedFamilyZeroCoefficients CycleQ2SeedFamilyZeroCover
  CycleQ2SeedFamilyNormalized CycleQ2SeedFamilyChart CycleQ2SeedFamilyJacobian

/-- The full coefficient vector of the cubic occurring in the incidence equation. -/
def incidenceParameter : Spec (CommRingCat.of ℂ) ⟶ parameterScheme :=
  Spec.map (CommRingCat.ofHom (coefficientEvaluation incidenceCoefficients))

/-- Specialization at any full cubic coefficient vector respects membership
in primes over that vector. -/
theorem specialization_mem_of_coefficients (c : CubicIndex → ℂ)
    (P : Ideal FamilyPolynomial)
    (hcoeff : ∀ a : ParameterRing, coefficientEvaluation c a = 0 → C a ∈ P)
    {p : FamilyPolynomial} (hp : p ∈ P) :
    MvPolynomial.map (coefficientEvaluation c) p ∈ specializedPrime P := by
  let φ : FamilyPolynomial →+* SeedPolynomial := MvPolynomial.map (coefficientEvaluation c)
  have heq : (Ideal.Quotient.mk P).comp (coefficientLift.comp φ) = Ideal.Quotient.mk P := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, φ, coefficientLift, MvPolynomial.map_C]
      apply Ideal.Quotient.eq.mpr
      have hz : coefficientEvaluation c
          (algebraMap ℂ ParameterRing (coefficientEvaluation c a) - a) = 0 := by
        rw [map_sub, coefficientEvaluation_algebraMap, sub_self]
      simpa only [map_sub] using hcoeff _ hz
    · intro j
      simp only [RingHom.comp_apply, φ, coefficientLift, MvPolynomial.map_X]
  change coefficientLift (φ p) ∈ P
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact (RingHom.congr_fun heq p).trans (Ideal.Quotient.eq_zero_iff_mem.mpr hp)

/-- On the specialized cone, vanishing of every weight-one coordinate
forces the weight-two coordinate to vanish as well. -/
theorem weightTwo_mem_of_weightOne_mem (r : ℂ) (J : Ideal SeedPolynomial) [J.IsPrime]
    (hF : smoothF r Complex.I ∈ J) (hX : ∀ i : Fin 4, X i.castSucc ∈ J) :
    (X (4 : Fin 5) : SeedPolynomial) ∈ J := by
  have hx (i : Fin 4) : Ideal.Quotient.mk J (X i.castSucc) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hX i)
  have hx0 : Ideal.Quotient.mk J (X (0 : Fin 5)) = 0 := hx 0
  have hx1 : Ideal.Quotient.mk J (X (1 : Fin 5)) = 0 := hx 1
  have hx2 : Ideal.Quotient.mk J (X (2 : Fin 5)) = 0 := hx 2
  have hx3 : Ideal.Quotient.mk J (X (3 : Fin 5)) = 0 := hx 3
  have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hF
  rw [← seedFamily_at_incidence_seed, seedFamily_expanded] at hzero
  have hw : Ideal.Quotient.mk J (X (4 : Fin 5)) ^ 3 = 0 := by
    simpa [smoothB, map_add, map_mul, map_pow, hx0, hx1, hx2, hx3] using hzero
  exact Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero hw)

/-- Every point of the incidence fiber belongs to a weight-one chart. -/
theorem exists_weightOne_of_over_incidence (r : ℂ) (s : Spec (CommRingCat.of ℂ))
    (x : family r) (hx : familyToParameters r x = incidenceParameter s) :
    ∃ i : Fin 4, x ∈ coordinateOpen r i := by
  classical
  change ∃ i : Fin 4, familyCoordinate r i.castSucc ∉ x.asHomogeneousIdeal.toIdeal
  let : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  let P := x.asHomogeneousIdeal.toIdeal.comap (familyQuotient r)
  let : P.IsPrime := inferInstance
  have hcoeff : ∀ a : ParameterRing, coefficientEvaluation incidenceCoefficients a = 0 →
      C a ∈ P := by
    intro a ha
    apply (coefficient_mem_iff r x a).mp
    rw [hx]
    change coefficientEvaluation incidenceCoefficients a ∈ s.asIdeal
    rw [ha]
    exact s.asIdeal.zero_mem
  have hF : familyEquation r ∈ P := by
    change familyQuotient r (familyEquation r) ∈ x.asHomogeneousIdeal.toIdeal
    rw [familyEquation_zero]
    exact Ideal.zero_mem _
  have hseed : smoothF r Complex.I ∈ specializedPrime P := by
    simpa only [specialize_incidence] using specialization_mem_of_coefficients _ P hcoeff hF
  by_contra! h
  have hweightOne (i : Fin 4) : X i.castSucc ∈ specializedPrime P :=
    (coordinate_mem_specializedPrime_iff P i.castSucc).mpr (h i)
  have hweightTwo : (X (4 : Fin 5) : FamilyPolynomial) ∈ P :=
    (coordinate_mem_specializedPrime_iff P 4).mp
      (weightTwo_mem_of_weightOne_mem r _ hseed hweightOne)
  obtain ⟨j, hj⟩ := exists_coordinate_not_mem r x
  fin_cases j
  · exact hj (h 0)
  · exact hj (h 1)
  · exact hj (h 2)
  · exact hj (h 3)
  · exact hj hweightTwo

open CycleQ2GeometricIncidenceProj CycleQ2SeedFermatProj CycleQ2IncidenceNormalForm in
/-- On a weight-one chart Euler's identity expresses the omitted derivative
in terms of the remaining derivatives modulo the hypersurface equation. -/
theorem literal_exists_other_derivative (r : ℂ) (i : Fin 4)
    (J : Ideal (MvPolynomial (Fin 5) ℂ))
    (hF : smoothF r Complex.I ∈ J) (hi : X i.castSucc - 1 ∈ J)
    (hδ : ∃ j : Fin 5, pderiv j (smoothF r Complex.I) ∉ J) :
    ∃ j : {j : Fin 5 // j ≠ i.castSucc}, pderiv j.1 (smoothF r Complex.I) ∉ J := by
  classical
  by_contra! h
  have hu : Ideal.Quotient.mk J (X i.castSucc) = 1 := by
    simpa only [map_sub, map_one, sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr hi
  have he : (smoothF r Complex.I).IsWeightedHomogeneous geometricWeight 6 :=
    homogeneous_of_character (smoothF_homogeneous r Complex.I)
  have hsum := congrArg (Ideal.Quotient.mk J) he.sum_weight_X_mul_pderiv
  simp only [map_sum, map_nsmul, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hF,
    nsmul_zero] at hsum
  rw [Finset.sum_eq_single i.castSucc] at hsum
  · rw [geometricWeight_castSucc, one_smul, hu, one_mul] at hsum
    obtain ⟨j, hj⟩ := hδ
    by_cases hji : j = i.castSucc
    · exact hj (hji ▸ Ideal.Quotient.eq_zero_iff_mem.mp hsum)
    · exact hj (h ⟨j, hji⟩)
  · intro j _ hji
    simp only [Ideal.Quotient.eq_zero_iff_mem.mpr (h ⟨j, hji⟩), mul_zero, nsmul_zero]
  · simp

/-- The prime-ideal form of the Jacobian condition on the four normalized charts. -/
def IncidenceJacobianCover (r : ℂ) : Prop :=
  ∀ (J : Ideal SeedPolynomial) [J.IsPrime] (i : Fin 4),
    X i.castSucc - 1 ∈ J → smoothF r Complex.I ∈ J →
    ∃ j : Fin 5, pderiv j (smoothF r Complex.I) ∉ J

/-- A derivative cover on the normalized seed equation gives a cover of
the entire incidence fiber by smooth patches of the full coefficient family. -/
theorem incidenceFiber_mem_smoothOpen (r : ℂ)
    (hcover : IncidenceJacobianCover r)
    (s : Spec (CommRingCat.of ℂ)) (x : family r)
    (hx : familyToParameters r x = incidenceParameter s) :
    x ∈ smoothOpen r := by
  obtain ⟨i, hi⟩ := exists_weightOne_of_over_incidence r s x hx
  obtain ⟨q, hq⟩ := exists_normalizedChart_preimage r i x hi
  have hbase : normalizedToParameters r i q = incidenceParameter s := by
    change (Spec.map (CommRingCat.ofHom
      (algebraMap ParameterRing (NormalizedRing r i)))) q = _
    rw [← normalizedChartToFamily_overParameters]
    change familyToParameters r (normalizedChartToFamily r i q) = _
    rw [hq]
    exact hx
  let : q.asIdeal.IsPrime := q.isPrime
  let P := q.asIdeal.comap (normalizedQuotient r i)
  let : P.IsPrime := inferInstance
  have hcoeff : ∀ a : ParameterRing, coefficientEvaluation incidenceCoefficients a = 0 →
      C a ∈ P := by
    intro a ha
    have hm : a ∈ (normalizedToParameters r i q).asIdeal := by
      rw [hbase]
      change coefficientEvaluation incidenceCoefficients a ∈ s.asIdeal
      rw [ha]
      exact s.asIdeal.zero_mem
    exact hm
  have hF : familyEquation r ∈ P := by
    change normalizedQuotient r i (familyEquation r) ∈ q.asIdeal
    rw [normalizedEquation]
    exact q.asIdeal.zero_mem
  have hFseed : smoothF r Complex.I ∈ specializedPrime P := by
    simpa only [specialize_incidence] using specialization_mem_of_coefficients _ P hcoeff hF
  have hiP : (X i.castSucc - 1 : FamilyPolynomial) ∈ P := by
    change normalizedQuotient r i (X i.castSucc - 1) ∈ q.asIdeal
    have hz := normalizedQuotient_relation r i 1
    change normalizedQuotient r i (X i.castSucc - 1) = 0 at hz
    rw [hz]
    exact q.asIdeal.zero_mem
  have hiJ : (X i.castSucc - 1 : SeedPolynomial) ∈ specializedPrime P := by
    change coefficientLift (X i.castSucc - 1) ∈ P
    simpa only [coefficientLift, map_sub, map_one, MvPolynomial.map_X] using hiP
  obtain ⟨j, hj⟩ := literal_exists_other_derivative r i _ hFseed hiJ
    (hcover (specializedPrime P) i hiJ hFseed)
  rw [← hq]
  apply mem_smoothOpen_of_derivative_not_mem r i j q
  intro hδ
  have hδP : pderiv j.1 (familyEquation r) ∈ P := hδ
  exact hj (by simpa only [← MvPolynomial.pderiv_map, specialize_incidence] using
    specialization_mem_of_coefficients _ P hcoeff hδP)

private theorem pullback_smoothOfRelativeDimension_of_range
    {X Y T : Scheme} (n : ℕ) (f : X ⟶ Y) (p : T ⟶ Y) (U : X.Opens)
    (hc : ∀ (s : T) (x : X), f x = p s → x ∈ U)
    (hs : SmoothOfRelativeDimension n (U.ι ≫ f)) :
    SmoothOfRelativeDimension n (pullback.fst p f) := by
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  let V := (pullback.snd p f) ⁻¹ᵁ U
  have hV : V = ⊤ := by
    apply top_unique
    intro z _
    apply hc (pullback.fst p f z) (pullback.snd p f z)
    exact (congrArg (fun g : pullback p f ⟶ Y => g z)
      (pullback.condition (f := p) (g := f))).symm
  have : IsIso V.ι := by rw [hV]; exact (pullback p f).topIso.isIso_hom
  let e : V.toScheme ≅ pullback p (U.ι ≫ f) :=
    (pullbackRestrictIsoRestrict (pullback.snd p f) U).symm ≪≫
      pullbackLeftPullbackSndIso p f U.ι
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension n) V.ι (pullback.fst p f)).mp
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := @SmoothOfRelativeDimension n) e.inv (V.ι ≫ pullback.fst p f)).mp
  have h : e.inv ≫ V.ι ≫ pullback.fst p f = pullback.fst p (U.ι ≫ f) := by
    dsimp only [e, V, Iso.trans_inv, Iso.symm_inv]
    simp only [Category.assoc, pullbackRestrictIsoRestrict_hom_ι_assoc,
      pullbackLeftPullbackSndIso_inv_fst]
  rw [h]
  exact MorphismProperty.pullback_fst _ _ hs


/-- The actual scheme fiber of the family defined by the full invariant cubic. -/
abbrev IncidenceFiber (r : ℂ) := pullback incidenceParameter (familyToParameters r)

/-- The structure map of the specialized projective threefold. -/
def incidenceFiberToComplex (r : ℂ) : IncidenceFiber r ⟶ Spec (CommRingCat.of ℂ) :=
  pullback.fst incidenceParameter (familyToParameters r)

/-- The original family is smooth of relative dimension three along the
incidence fiber whenever its specialized equation satisfies the Jacobian criterion. -/
theorem incidenceFiber_smoothOfRelativeDimension (r : ℂ) (hcover : IncidenceJacobianCover r) :
    SmoothOfRelativeDimension 3 (incidenceFiberToComplex r) :=
  pullback_smoothOfRelativeDimension_of_range 3 (familyToParameters r) incidenceParameter
    (smoothOpen r) (incidenceFiber_mem_smoothOpen r hcover)
    (smoothOpen_family_smoothOfRelativeDimension r)

/-- The given incidence parameter belongs to the open smooth base of the proper family. -/
theorem incidence_mem_seedSmoothBase (r : ℂ) (hcover : IncidenceJacobianCover r)
    (s : Spec (CommRingCat.of ℂ)) :
    incidenceParameter s ∈ CycleQ2SeedFamilySmoothNeighborhood.seedSmoothBase r := by
  let : IsProper (familyToParameters r) :=
    CycleQ2SeedProjectiveFamilyProper.familyToParameters_proper r
  apply (CycleQ2IncidenceProperNeighborhood.mem_properBaseNeighborhood_iff
    (familyToParameters r) (smoothOpen r) (incidenceParameter s)).mpr
  exact incidenceFiber_mem_smoothOpen r hcover s

/-- The coordinate chart Jacobian criterion holds at the literal trace seed. -/
theorem literal_jacobian_cover : IncidenceJacobianCover 57 :=
  CycleQ2LiteralAmbientEquation.ambient_prime_cover_of_gradient
    CycleQ2LiteralAmbientEquation.gradient_zero

/-- The actual incidence threefold carrying the trace surface is smooth of
relative dimension three over the complex numbers. -/
theorem literal_fiber_smooth : SmoothOfRelativeDimension 3 (incidenceFiberToComplex 57) :=
  incidenceFiber_smoothOfRelativeDimension 57 literal_jacobian_cover

/-- The specialized structure map is proper by base change from the coefficient family. -/
theorem incidenceFiber_proper (r : ℂ) : IsProper (incidenceFiberToComplex r) := by
  let := CycleQ2SeedProjectiveFamilyProper.familyToParameters_proper r
  dsimp only [incidenceFiberToComplex]
  infer_instance

/-- The incidence cubic used in the trace calculation belongs to the open
base over which the whole original projective family is smooth. -/
theorem literal_mem_seedSmoothBase (s : Spec (CommRingCat.of ℂ)) :
    incidenceParameter s ∈ CycleQ2SeedFamilySmoothNeighborhood.seedSmoothBase 57 :=
  incidence_mem_seedSmoothBase 57 literal_jacobian_cover s

end CycleQ2LiteralAmbientSmooth

end

#print axioms CycleQ2LiteralAmbientSmooth.incidenceFiber_smoothOfRelativeDimension
#print axioms CycleQ2LiteralAmbientSmooth.incidence_mem_seedSmoothBase

#print axioms CycleQ2LiteralAmbientSmooth.literal_fiber_smooth
#print axioms CycleQ2LiteralAmbientSmooth.incidenceFiber_proper
#print axioms CycleQ2LiteralAmbientSmooth.literal_mem_seedSmoothBase
