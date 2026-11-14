import Proposal.GeometricFormalInputs03Part01

/-! Continuation of GeometricFormalInputs03.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: continuation_2/AffineExactnessCriterion.lean -/
section
/-!
# Actual top-form exactness is equivalent to the protected residue PDE

Write g for the nonzero normal derivative and c for the actual second normal
source. The residue source is the genuine top exterior form (c/g) dx1∧⋯∧dx4.
The three-form with coefficients (-1)^i w_i/g has derivative
(residueDivergence w/g) dx1∧⋯∧dx4. Thus a solved PDE c+div_g(w)=0 makes its
negative a primitive of the positive source form. No exactness is assumed
without appearing explicitly as a hypothesis in the final implication.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineExactness

open MvPolynomial HodgeComputer CycleQ2AffineDifferentials CycleQ2AffineExterior
open CycleQ2AffineHypersurface CycleQ2AffineClearing CycleQ2AffineResidueClosure
open HoldoutConstruction
open scoped BigOperators

local instance intAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

def normalDensity : K := affineMap (pderiv 0 affineF)

theorem normalDensity_ne_zero : normalDensity ≠ 0 := normal_ne_zero

def coordinateSign (i : Fin 4) : K := (-1 : K) ^ i.val

theorem coordinateSign_mul_self (i : Fin 4) :
    coordinateSign i * coordinateSign i = 1 := by
  unfold coordinateSign
  rw [← pow_add, show i.val + i.val = 2 * i.val by omega, pow_mul]
  simp

@[simp] theorem tangent_coordinateSign (j i : Fin 4) :
    affineTangent j (coordinateSign i) = 0 := by
  simp only [coordinateSign, Derivation.leibniz_pow, map_neg,
    Derivation.map_one_eq_zero, neg_zero, smul_zero]

def signedCoefficients (η : Form 3) (i : Fin 4) : K :=
  coordinateSign i * thirdBasis.repr η i

def densityVector (η : Form 3) (i : Fin 4) : K :=
  normalDensity * signedCoefficients η i

theorem exteriorD3_as_divergence (η : Form 3) :
    exteriorD3 η = fieldDivergence affineTangent (signedCoefficients η) • volume := by
  rw [exteriorD3_apply]
  congr 1
  unfold fieldDivergence signedCoefficients
  apply Finset.sum_congr rfl
  intro i hi
  rw [Derivation.leibniz, tangent_coordinateSign]
  simp only [smul_eq_mul, mul_zero, add_zero, coordinateSign]

theorem densityVector_residueDivergence (η : Form 3) :
    residueDivergence affineTangent normalDensity (densityVector η) =
      normalDensity * fieldDivergence affineTangent (signedCoefficients η) :=
  residueDivergence_cancel_density affineTangent normalDensity normalDensity_ne_zero _

theorem volumeCoefficient_exteriorD3 (η : Form 3) :
    volumeCoefficient (exteriorD3 η) = fieldDivergence affineTangent (signedCoefficients η) := by
  rw [exteriorD3_as_divergence, map_smul, volumeCoefficient_volume, smul_eq_mul, mul_one]

/-- The actual source top-form, with the positive residue sign. -/
def residueSourceForm (A : AmbientPoly 4) : Form 4 :=
  (affineNormalSource A / normalDensity) • volume

@[simp] theorem volumeCoefficient_residueSourceForm (A : AmbientPoly 4) :
    volumeCoefficient (residueSourceForm A) = affineNormalSource A / normalDensity := by
  simp [residueSourceForm]

/-- The explicit three-form whose coordinate coefficients are (-1)^i w_i/g. -/
def residuePrimitiveForm (w : Fin 4 → K) : Form 3 :=
  thirdBasis.equivFun.symm (fun i => coordinateSign i * (w i / normalDensity))

@[simp] theorem residuePrimitiveForm_repr (w : Fin 4 → K) (i : Fin 4) :
    thirdBasis.repr (residuePrimitiveForm w) i =
      coordinateSign i * (w i / normalDensity) := by
  change thirdBasis.coord i (thirdBasis.equivFun.symm _) = _
  exact Module.Basis.coord_equivFun_symm thirdBasis i _

theorem densityVector_residuePrimitiveForm (w : Fin 4 → K) :
    densityVector (residuePrimitiveForm w) = w := by
  funext i
  simp only [densityVector, signedCoefficients, residuePrimitiveForm_repr]
  rw [← mul_assoc (coordinateSign i), coordinateSign_mul_self, one_mul]
  field_simp [normalDensity_ne_zero]

theorem residuePrimitiveForm_densityVector (η : Form 3) :
    residuePrimitiveForm (densityVector η) = η := by
  apply thirdBasis.repr.injective
  ext i
  rw [residuePrimitiveForm_repr]
  simp only [densityVector, signedCoefficients]
  rw [mul_div_cancel_left₀ _ normalDensity_ne_zero,
    ← mul_assoc, coordinateSign_mul_self, one_mul]

/-- Exact identity between the genuine exterior derivative and the existing
weighted residue divergence. -/
theorem exteriorD3_residuePrimitiveForm (w : Fin 4 → K) :
    exteriorD3 (residuePrimitiveForm w) =
      (residueDivergence affineTangent normalDensity w / normalDensity) • volume := by
  have hd := densityVector_residueDivergence (residuePrimitiveForm w)
  rw [densityVector_residuePrimitiveForm] at hd
  rw [exteriorD3_as_divergence]
  congr 1
  apply (eq_div_iff normalDensity_ne_zero).mpr
  simpa only [mul_comm] using hd.symm

theorem affineResidueExpression_densityVector (A : AmbientPoly 4) (η : Form 3) :
    affineResidueExpression A (densityVector η) =
      affineNormalSource A + normalDensity * volumeCoefficient (exteriorD3 η) := by
  change affineNormalSource A +
    residueDivergence affineTangent normalDensity (densityVector η) = _
  rw [densityVector_residueDivergence, volumeCoefficient_exteriorD3]

/-- The sign convention is explicit: a zero residue PDE gives the negative
of the positive source form as the derivative of `residuePrimitiveForm w`. -/
theorem exteriorD3_residuePrimitiveForm_add_source (A : AmbientPoly 4) (w : Fin 4 → K) :
    exteriorD3 (residuePrimitiveForm w) + residueSourceForm A =
      (affineResidueExpression A w / normalDensity) • volume := by
  rw [exteriorD3_residuePrimitiveForm, residueSourceForm, ← add_smul]
  change (residueDivergence affineTangent normalDensity w / normalDensity +
    affineNormalSource A / normalDensity) • volume =
      ((affineNormalSource A + residueDivergence affineTangent normalDensity w) /
        normalDensity) • volume
  congr 1
  ring

/-- Genuine exactness of the actual top exterior source is equivalent to
the already defined concrete residue PDE. Neither side is asserted here. -/
theorem exact_residueSourceForm_iff (A : AmbientPoly 4) :
    (∃ η : Form 3, exteriorD3 η = residueSourceForm A) ↔
      ∃ w : Fin 4 → K, affineResidueExpression A w = 0 := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨densityVector (-η), ?_⟩
    rw [affineResidueExpression_densityVector, map_neg, hη, map_neg,
      volumeCoefficient_residueSourceForm]
    field_simp [normalDensity_ne_zero]
    ring
  · rintro ⟨w, hw⟩
    have hh := exteriorD3_residuePrimitiveForm_add_source A w
    rw [hw, zero_div, zero_smul] at hh
    refine ⟨-residuePrimitiveForm w, ?_⟩
    rw [map_neg, eq_neg_of_add_eq_zero_left hh, neg_neg]

/-- Actual exterior-form exactness now implies the unchanged protected
certificate through the proved residue, chart, and denominator constructions. -/
theorem protected_certificate_of_exact_residueSourceForm
    (h : ∃ η : Form 3, exteriorD3 η = residueSourceForm affineA) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  protected_certificate_of_affine_residue_primitive ((exact_residueSourceForm_iff affineA).mp h)

end CycleQ2AffineExactness

#print axioms CycleQ2AffineExactness.exteriorD3_residuePrimitiveForm_add_source
#print axioms CycleQ2AffineExactness.exact_residueSourceForm_iff
#print axioms CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
end
end


/- Component: continuation_2/VeryGeneralPoint.lean -/
section
/-!
Actual very-general-point selection in affine coefficient spaces.

The countable-proper-image specialization argument requires a complex point
outside countably many proper algebraic conditions. This module proves that
selection statement for genuine polynomial equations. It does not assert
that any moving cycle, supported projector, or primitive exists.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2VeryGeneral

open MvPolynomial

variable {K : Type*} [Field K] [Uncountable K]

theorem exists_avoiding_univariate {ι : Type*} [Countable ι]
    (p : ι → Polynomial K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : K, ∀ i, (p i).eval x ≠ 0 := by
  classical
  let roots : ι → Set K := fun i => {x | (p i).eval x = 0}
  have hroots (i : ι) : (roots i).Finite := by
    simpa only [roots, Polynomial.IsRoot] using
      (Polynomial.finite_setOfPred_isRoot (hp i))
  have hcount : (⋃ i, roots i).Countable :=
    Set.countable_iUnion (fun i => (hroots i).countable)
  have hout : ∃ x : K, x ∉ ⋃ i, roots i := by
    by_contra h
    push Not at h
    have heq : (⋃ i, roots i) = Set.univ := Set.eq_univ_of_forall h
    exact Set.not_countable_univ (heq ▸ hcount)
  obtain ⟨x, hx⟩ := hout
  refine ⟨x, fun i hi => hx ?_⟩
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Countably many genuine nonzero multivariate polynomials have a common
nonvanishing point over an uncountable field. -/
theorem exists_avoiding_polynomials (n : ℕ) {ι : Type*} [Countable ι]
    (p : ι → MvPolynomial (Fin n) K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : Fin n → K, ∀ i, eval x (p i) ≠ 0 := by
  classical
  induction n with
  | zero =>
      refine ⟨Fin.elim0, ?_⟩
      intro i hi
      obtain ⟨c, hc⟩ := (isEmptyAlgEquiv K (Fin 0)).symm.surjective (p i)
      have hpi : p i = C c := by simpa using hc.symm
      rw [hpi, eval_C] at hi
      exact hp i (by simp [hpi, hi])
  | succ n ih =>
      let q : ι → Polynomial (MvPolynomial (Fin n) K) :=
        fun i => finSuccEquiv K n (p i)
      have hq (i : ι) : q i ≠ 0 := by
        intro hz
        apply hp i
        apply (finSuccEquiv K n).injective
        simpa only [q, map_zero] using hz
      have hlc (i : ι) : (q i).leadingCoeff ≠ 0 := by
        simpa only [ne_eq, Polynomial.leadingCoeff_eq_zero] using hq i
      obtain ⟨y, hy⟩ := ih (fun i => (q i).leadingCoeff) hlc
      let s : ι → Polynomial K := fun i => (q i).map (eval y)
      have hs (i : ι) : s i ≠ 0 := by
        intro hz
        have hc := congrArg (fun z : Polynomial K => z.coeff (q i).natDegree) hz
        simp only [s, Polynomial.coeff_map, Polynomial.coeff_zero] at hc
        exact hy i hc
      obtain ⟨x, hx⟩ := exists_avoiding_univariate s hs
      refine ⟨Fin.cons x y, ?_⟩
      intro i
      simpa only [eval_eq_eval_mv_eval', q, s] using hx i

/-- A very general complex coefficient point can also be required to lie in
any prescribed nonempty principal open, without a coefficient bound. -/
theorem complex_point_in_principal_open_avoiding (n : ℕ)
    {ι : Type*} [Countable ι] (g : MvPolynomial (Fin n) ℂ) (hg : g ≠ 0)
    (p : ι → MvPolynomial (Fin n) ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ x : Fin n → ℂ, eval x g ≠ 0 ∧ ∀ i, eval x (p i) ≠ 0 := by
  letI : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  let family : Option ι → MvPolynomial (Fin n) ℂ := fun i => Option.elim i g p
  have hn (i : Option ι) : family i ≠ 0 := by
    cases i with
    | none => exact hg
    | some i => exact hp i
  obtain ⟨x, hx⟩ := exists_avoiding_polynomials n family hn
  exact ⟨x, hx none, fun i => hx (some i)⟩

/-- A countable family of genuine affine algebraic zero loci covering a
nonempty principal open has a member equal to the whole affine space.
This is the countability step in proper-image specialization, without any
assumed existence of projectors or cycle families. -/
theorem complex_countable_algebraic_cover (n : ℕ)
    {ι : Type*} [Countable ι]
    (I : ι → Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin n) ℂ) (hg : g ≠ 0)
    (hcover : ∀ x : Fin n → ℂ, eval x g ≠ 0 →
      ∃ i, x ∈ zeroLocus ℂ (I i)) :
    ∃ i, zeroLocus ℂ (I i) = Set.univ := by
  classical
  by_contra h
  push Not at h
  have hn (i : ι) : I i ≠ ⊥ := by
    intro hi
    apply h i
    simp only [hi, zeroLocus_bot, Set.top_eq_univ]
  have hp (i : ι) : ∃ p : MvPolynomial (Fin n) ℂ, p ∈ I i ∧ p ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hn i
    apply le_antisymm
    · intro p hp
      exact (Ideal.mem_bot).mpr (hh p hp)
    · exact bot_le
  choose p hpI hpne using hp
  obtain ⟨x, hxg, hxp⟩ := complex_point_in_principal_open_avoiding n g hg p hpne
  obtain ⟨i, hxi⟩ := hcover x hxg
  apply hxp i
  exact hxi (p i) (hpI i)

end CycleQ2VeryGeneral

#print axioms CycleQ2VeryGeneral.exists_avoiding_polynomials
#print axioms CycleQ2VeryGeneral.complex_point_in_principal_open_avoiding
#print axioms CycleQ2VeryGeneral.complex_countable_algebraic_cover
end
end


/- Component: continuation_2/AffineFormalSpecialization.lean -/
section
/-!
An actual formal neighborhood of the protected affine hypersurface.

The normal derivative is already proved nonzero in its function field. Hensel's
lemma therefore solves the exact one-parameter deformation in that function
field's power series ring. This is a specialization tool: it does not turn a
formal primitive at the Fermat member into a rational primitive of the family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace CycleQ2FormalSpecialization

open scoped PowerSeries

/-- Hensel lifting written with the actual constant-coefficient specialization.
No algebraicity or rationality of the resulting power series is inferred. -/
theorem simple_root_lifts {k : Type*} [Field k]
    (p : Polynomial (PowerSeries k)) (hp : p.Monic) (a : k)
    (ha : p.eval₂ (PowerSeries.constantCoeff (R := k)) a = 0)
    (hderiv : p.derivative.eval₂ (PowerSeries.constantCoeff (R := k)) a ≠ 0) :
    ∃ z : PowerSeries k, p.eval z = 0 ∧ z.constantCoeff = a := by
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  have hmem : p.eval (PowerSeries.C a) ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simpa only [← Polynomial.eval₂_at_apply, PowerSeries.constantCoeff_C] using ha
  have hu : IsUnit (p.derivative.eval (PowerSeries.C a)) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    simpa only [← Polynomial.eval₂_at_apply, PowerSeries.constantCoeff_C] using hderiv
  obtain ⟨z, hz, hza⟩ := HenselianRing.is_henselian p hp (PowerSeries.C a)
    hmem (hu.map (Ideal.Quotient.mk I))
  refine ⟨z, hz, ?_⟩
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hza
  simpa only [map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] using hza

open MvPolynomial CycleQ2AffineClearing CycleQ2AffineGeometry
  CycleQ2AffineHypersurface

abbrev K := AffineFunctionField

def fieldCoordinate (i : Fin 5) : K := affineMap (MvPolynomial.X i)

/-- The family parameter is zero at the protected target and minus one at
the Fermat polynomial. The eliminated coordinate is the polynomial variable;
the other four coordinates are constants in the actual function field. -/
def targetFamily : Polynomial (PowerSeries K) :=
  Polynomial.X ^ 6 +
    Polynomial.C (PowerSeries.C (1 + fieldCoordinate 1 ^ 6 +
      fieldCoordinate 2 ^ 6 + fieldCoordinate 3 ^ 6 + fieldCoordinate 4 ^ 6)) +
    Polynomial.C (PowerSeries.C (1 / 2 : K) * (1 + PowerSeries.X)) *
      (Polynomial.X * Polynomial.C (PowerSeries.C (fieldCoordinate 2 * fieldCoordinate 3)) +
        Polynomial.X ^ 3 * Polynomial.C (PowerSeries.C
          (fieldCoordinate 1 * fieldCoordinate 3 * fieldCoordinate 4)) +
        Polynomial.C (PowerSeries.C
          (fieldCoordinate 1 ^ 3 * fieldCoordinate 4 * fieldCoordinate 2)))

theorem targetFamily_monic : targetFamily.Monic := by
  unfold targetFamily
  rw [add_assoc]
  apply Polynomial.monic_X_pow_add
  compute_degree!

theorem targetFamily_specializes :
    targetFamily.eval₂ (PowerSeries.constantCoeff (R := K)) (fieldCoordinate 0) = 0 := by
  have hc (c : ℂ) : affineMap (MvPolynomial.C c) = algebraMap ℂ K c := rfl
  have h := congrArg affineMap affineF_formula
  simp only [affineMap_F, map_add, map_mul, map_pow, map_one, hc] at h
  norm_num only [map_div₀, map_one, map_ofNat] at h
  convert h.symm using 1 <;> norm_num only [targetFamily, fieldCoordinate,
    Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one, map_add, map_mul,
    map_one, map_zero, map_pow, map_ofNat, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X] <;> ring

theorem targetFamily_simple :
    targetFamily.derivative.eval₂ (PowerSeries.constantCoeff (R := K))
      (fieldCoordinate 0) ≠ 0 := by
  have hc (c : ℂ) : affineMap (MvPolynomial.C c) = algebraMap ℂ K c := rfl
  have h := congrArg (fun P => affineMap (MvPolynomial.pderiv 0 P)) affineF_formula
  norm_num [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X, Pi.single_apply, Fin.ext_iff, hc] at h
  have hn := normal_ne_zero
  rw [h] at hn
  convert hn using 1 <;>
    norm_num [targetFamily, fieldCoordinate, Polynomial.derivative_add,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] <;> simp only [map_ofNat] <;> ring

/-- The protected hypersurface has a genuine formal solution along the
specified deformation, with its original coordinate as constant coefficient. -/
theorem exists_target_formal_coordinate :
    ∃ z : PowerSeries K, targetFamily.eval z = 0 ∧
      z.constantCoeff = fieldCoordinate 0 :=
  simple_root_lifts targetFamily targetFamily_monic (fieldCoordinate 0)
    targetFamily_specializes targetFamily_simple

end CycleQ2FormalSpecialization

#print axioms CycleQ2FormalSpecialization.simple_root_lifts
#print axioms CycleQ2FormalSpecialization.exists_target_formal_coordinate
end
end


/- Component: continuation_2/LaurentCoefficientDerivations.lean -/
section
/-!
Coefficientwise derivations and exactness under formal Laurent extension.

The exponent is a deformation parameter, not a coordinate to differentiate.
The actual Hahn-series multiplication is used in the Leibniz proof. Taking
any Laurent coefficient commutes with these derivations, including for
series with negative powers. Consequently a Laurent primitive specializes
coefficientwise; no converse from formal deformation to a rational primitive
of a generic algebraic family is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2LaurentDerivation

open scoped BigOperators

variable {C K : Type*} [CommRing C] [CommRing K] [Algebra C K]

abbrev Series := HahnSeries ℤ K

/-- Use the coefficient algebra explicitly. The power-series imports also
provide a compatible algebra through the power-series embedding; fixing
this instance keeps the scalar action definitionally coefficientwise. -/
local instance coefficientAlgebra : Algebra C (Series (K := K)) :=
  HahnSeries.instAlgebra

def coefficientwise (D : Derivation C K K) (s : Series (K := K)) : Series (K := K) where
  coeff n := D (s.coeff n)
  isPWO_support' := s.isPWO_support.mono (by
    intro n hn hzero
    exact hn (by simp only [hzero, map_zero]))

@[simp] theorem coefficientwise_coeff (D : Derivation C K K) (s : Series (K := K)) (n : ℤ) :
    (coefficientwise D s).coeff n = D (s.coeff n) := rfl

theorem support_coefficientwise_subset (D : Derivation C K K) (s : Series (K := K)) :
    (coefficientwise D s).support ⊆ s.support := by
  intro n hn hzero
  exact hn (by simp only [coefficientwise_coeff, hzero, map_zero])

theorem coefficientwise_mul (D : Derivation C K K) (s t : Series (K := K)) :
    coefficientwise D (s * t) = s * coefficientwise D t + t * coefficientwise D s := by
  ext n
  rw [coefficientwise_coeff, HahnSeries.coeff_mul, map_sum, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_right' t.isPWO_support (support_coefficientwise_subset D t),
    mul_comm t (coefficientwise D s),
    HahnSeries.coeff_mul_left' s.isPWO_support (support_coefficientwise_subset D s)]
  simp only [Derivation.leibniz, smul_eq_mul, coefficientwise_coeff, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  exact mul_comm _ _

/-- An actual derivation of the Laurent-series ring, obtained by applying the
coefficient derivation while keeping the formal parameter constant. -/
def extend (D : Derivation C K K) : Derivation C (Series (K := K)) (Series (K := K)) where
  toFun := coefficientwise D
  map_add' s t := by
    ext n
    simp
  map_smul' c s := by
    ext n
    simp only [coefficientwise_coeff, HahnSeries.coeff_smul,
      RingHom.id_apply, Derivation.map_smul]
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [HahnSeries.coeff_one, hn]
  leibniz' s t := by
    change coefficientwise D (s * t) = s * coefficientwise D t + t * coefficientwise D s
    exact coefficientwise_mul D s t

@[simp] theorem extend_coeff (D : Derivation C K K) (s : Series (K := K)) (n : ℤ) :
    (extend D s).coeff n = D (s.coeff n) := rfl

theorem extend_commute (D E : Derivation C K K) (h : Function.Commute D E) :
    Function.Commute (extend D) (extend E) := by
  intro s
  ext n
  exact h (s.coeff n)

@[simp] theorem extend_single (D : Derivation C K K) (n : ℤ) (a : K) :
    extend D (HahnSeries.single n a) = HahnSeries.single n (D a) := by
  ext j
  by_cases hj : j = n <;> simp [hj]

/-- Coefficient extraction is a left inverse on exactness, even when a
primitive has a pole in the deformation parameter. -/
theorem divergence_coefficient {ι : Type*} [Fintype ι]
    (D : ι → Derivation C K K) (v : ι → Series (K := K)) (b : Series (K := K))
    (h : (∑ i, extend (D i) (v i)) = b) (n : ℤ) :
    (∑ i, D i ((v i).coeff n)) = b.coeff n := by
  have hc := congrArg (fun s : Series (K := K) => s.coeff n) h
  simpa only [HahnSeries.coeff_sum, extend_coeff] using hc

/-- Extending the coefficient field to formal Laurent series cannot make a
constant source exact unless it was already exact over the original ring. -/
theorem exists_divergence_constant_iff {ι : Type*} [Fintype ι]
    (D : ι → Derivation C K K) (b : K) :
    (∃ v : ι → Series (K := K), ∑ i, extend (D i) (v i) = HahnSeries.single 0 b) ↔
      ∃ v : ι → K, ∑ i, D i (v i) = b := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun i => (v i).coeff 0, ?_⟩
    simpa using divergence_coefficient D v _ hv 0
  · rintro ⟨v, hv⟩
    refine ⟨fun i => HahnSeries.single 0 (v i), ?_⟩
    simp_rw [extend_single]
    change (∑ i, HahnSeries.single.addMonoidHom 0 (D i (v i))) =
      HahnSeries.single.addMonoidHom 0 b
    rw [← map_sum (HahnSeries.single.addMonoidHom 0), hv]

end CycleQ2LaurentDerivation

#print axioms CycleQ2LaurentDerivation.extend
#print axioms CycleQ2LaurentDerivation.divergence_coefficient
#print axioms CycleQ2LaurentDerivation.exists_divergence_constant_iff
end
end


/- Component: continuation_2/AffineNormalExpansion.lean -/
section
/-!
The actual normal formal coordinate at the generic point of f=0.

We solve f(x0(T),x1,...,x4)=T in K[[T]], prove that its constant-coefficient
map is the actual residue map on polynomials, and prove injectivity of the
resulting polynomial substitution. The formal derivative satisfies the
actual normal chain rule. These are local algebraic facts, independent of
any assertion that the target residue is exact.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2NormalExpansion

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineGeometry
  CycleQ2AffineHypersurface CycleQ2FormalSpecialization

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

def normalEquation : Polynomial S :=
  Polynomial.X ^ 6 +
    (Polynomial.C (PowerSeries.C (1 + fieldCoordinate 1 ^ 6 +
      fieldCoordinate 2 ^ 6 + fieldCoordinate 3 ^ 6 + fieldCoordinate 4 ^ 6)) +
      Polynomial.C (PowerSeries.C (1 / 2 : K)) *
        (Polynomial.X * Polynomial.C (PowerSeries.C (fieldCoordinate 2 * fieldCoordinate 3)) +
          Polynomial.X ^ 3 * Polynomial.C (PowerSeries.C
            (fieldCoordinate 1 * fieldCoordinate 3 * fieldCoordinate 4)) +
          Polynomial.C (PowerSeries.C
            (fieldCoordinate 1 ^ 3 * fieldCoordinate 4 * fieldCoordinate 2))) -
      Polynomial.C PowerSeries.X)

theorem normalEquation_monic : normalEquation.Monic := by
  unfold normalEquation
  apply Polynomial.monic_X_pow_add
  compute_degree!

theorem normalEquation_specializes :
    normalEquation.eval₂ (PowerSeries.constantCoeff (R := K)) (fieldCoordinate 0) = 0 := by
  convert targetFamily_specializes using 1 <;>
    simp [normalEquation, targetFamily] <;> ring

theorem normalEquation_simple :
    normalEquation.derivative.eval₂ (PowerSeries.constantCoeff (R := K))
      (fieldCoordinate 0) ≠ 0 := by
  convert targetFamily_simple using 1 <;>
    simp [normalEquation, targetFamily, Polynomial.derivative_pow]

theorem normal_root_exists :
    ∃ z : S, normalEquation.eval z = 0 ∧ z.constantCoeff = fieldCoordinate 0 :=
  simple_root_lifts normalEquation normalEquation_monic (fieldCoordinate 0)
    normalEquation_specializes normalEquation_simple

def normalRoot : S := Classical.choose normal_root_exists

theorem normalRoot_equation : normalEquation.eval normalRoot = 0 :=
  (Classical.choose_spec normal_root_exists).1

@[simp] theorem normalRoot_constantCoeff :
    normalRoot.constantCoeff = fieldCoordinate 0 :=
  (Classical.choose_spec normal_root_exists).2

def normalCoordinates : Fin 5 → S :=
  Fin.cases normalRoot (fun j => PowerSeries.C (fieldCoordinate j.succ))

def normalExpansion : AmbientPoly 4 →+* S :=
  MvPolynomial.eval₂Hom (PowerSeries.C.comp (affineMap.comp MvPolynomial.C)) normalCoordinates

@[simp] theorem normalExpansion_C (c : ℂ) :
    normalExpansion (MvPolynomial.C c) = PowerSeries.C (affineMap (MvPolynomial.C c)) := by
  simp [normalExpansion]

@[simp] theorem normalExpansion_X_zero :
    normalExpansion (MvPolynomial.X (0 : Fin 5)) = normalRoot := by
  simp [normalExpansion, normalCoordinates]

@[simp] theorem normalExpansion_X_succ (j : Fin 4) :
    normalExpansion (MvPolynomial.X j.succ) = PowerSeries.C (fieldCoordinate j.succ) := by
  simp [normalExpansion, normalCoordinates]

/-- The constant coefficient is exactly the previously constructed quotient
map into the protected hypersurface function field, on every polynomial. -/
theorem constantCoeff_normalExpansion (P : AmbientPoly 4) :
    (normalExpansion P).constantCoeff = affineMap P := by
  have h : (PowerSeries.constantCoeff (R := K)).comp normalExpansion = affineMap := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [fieldCoordinate]
      · simp [fieldCoordinate]
  exact RingHom.congr_fun h P

/-- The normal parameter is the actual protected equation f. -/
theorem normalExpansion_F : normalExpansion affineF = PowerSeries.X := by
  have hf := congrArg normalExpansion affineF_formula
  have hr := normalRoot_equation
  have hc : normalExpansion (MvPolynomial.C (1 / 2 : ℂ)) =
      PowerSeries.C (1 / 2 : K) := by
    rw [normalExpansion_C]
    congr 1
    change (affineMap.comp MvPolynomial.C) (1 / 2 : ℂ) = _
    rw [map_div₀, map_one, map_ofNat]
  norm_num [normalEquation, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
  simp only [map_add, map_mul, map_pow, map_one, hc] at hf
  have h1 : normalExpansion (MvPolynomial.X (1 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 1) := normalExpansion_X_succ 0
  have h2 : normalExpansion (MvPolynomial.X (2 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 2) := normalExpansion_X_succ 1
  have h3 : normalExpansion (MvPolynomial.X (3 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 3) := normalExpansion_X_succ 2
  have h4 : normalExpansion (MvPolynomial.X (4 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 4) := normalExpansion_X_succ 3
  rw [hf]
  simp only [normalExpansion_X_zero, h1, h2, h3, h4]
  change 1 + normalRoot ^ 6 + PowerSeries.C (fieldCoordinate 1) ^ 6 +
    PowerSeries.C (fieldCoordinate 2) ^ 6 + PowerSeries.C (fieldCoordinate 3) ^ 6 +
    PowerSeries.C (fieldCoordinate 4) ^ 6 +
      PowerSeries.C (1 / 2 : K) *
        (normalRoot * PowerSeries.C (fieldCoordinate 2) * PowerSeries.C (fieldCoordinate 3) +
          normalRoot ^ 3 * PowerSeries.C (fieldCoordinate 1) *
            PowerSeries.C (fieldCoordinate 3) * PowerSeries.C (fieldCoordinate 4) +
          PowerSeries.C (fieldCoordinate 1) ^ 3 * PowerSeries.C (fieldCoordinate 4) *
            PowerSeries.C (fieldCoordinate 2)) = _
  simp only [one_div]
  linear_combination hr

theorem normalExpansion_injective : Function.Injective normalExpansion := by
  have hnonzero (P : AmbientPoly 4) (hP : P ≠ 0) : normalExpansion P ≠ 0 := by
    obtain ⟨m, U, hFU, hfactor⟩ := WfDvdMonoid.max_power_factor hP affineF_irreducible
    have hU : normalExpansion U ≠ 0 := by
      intro h
      have hc := congrArg (PowerSeries.constantCoeff (R := K)) h
      rw [constantCoeff_normalExpansion, map_zero] at hc
      exact hFU ((affineMap_kernel U).mp hc)
    rw [hfactor, map_mul, map_pow, normalExpansion_F]
    exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) hU
  intro P Q h
  by_contra hn
  exact hnonzero (P - Q) (sub_ne_zero.mpr hn) (by rw [map_sub, h, sub_self])

abbrev Dt : Derivation K S S := PowerSeries.derivative K

def normalVelocity : S := Dt normalRoot

/-- Chain rule for every polynomial under the actual formal normal chart. -/
theorem normalExpansion_chain_rule (P : AmbientPoly 4) :
    Dt (normalExpansion P) = normalExpansion (pderiv 0 P) * normalVelocity := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [Dt]
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ, add_mul]
  | mul_X P i ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [map_mul, Derivation.leibniz, normalExpansion_X_zero, ih,
          normalVelocity, pderiv_mul, pderiv_X_self, mul_one, map_add,
          smul_eq_mul]
        ring
      · simp only [map_mul, Derivation.leibniz, normalExpansion_X_succ, ih,
          pderiv_mul, pderiv_X, Pi.single_apply, Fin.succ_ne_zero,
          if_false, mul_zero, add_zero, map_add, map_zero, smul_eq_mul,
          PowerSeries.derivative_C, mul_zero, zero_add]
        ring

theorem normal_velocity_identity :
    normalExpansion (pderiv 0 affineF) * normalVelocity = 1 := by
  have h := normalExpansion_chain_rule affineF
  rw [normalExpansion_F, PowerSeries.derivative_X] at h
  exact h.symm

end CycleQ2NormalExpansion

#print axioms CycleQ2NormalExpansion.normalExpansion_F
#print axioms CycleQ2NormalExpansion.normalExpansion_injective
#print axioms CycleQ2NormalExpansion.normalExpansion_chain_rule
#print axioms CycleQ2NormalExpansion.normal_velocity_identity
end
end


/- Component: continuation_2/AffineFormalResidue.lean -/
section
/-!
The actual pole-three residue coefficient in a genuine formal normal chart.

The normal chart sends f to T and holds the four other coordinates fixed.
Its Jacobian in the normal direction is dx0/dT. We prove that the T^(-1)
coefficient of A(x(T)) (dx0/dT) / T^3 is precisely the previously defined
normal source divided by g. This supplies the local residue calculation;
it does not assert geometric support or global de Rham vanishing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace CycleQ2FormalResidue

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineResidueClosure CycleQ2NormalExpansion HoldoutConstruction
open SplitHigherResidue

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

def normalG : K := affineMap (pderiv 0 affineF)
def normalG1 : K := affineMap (pderiv 0 (pderiv 0 affineF))
def normalG2 : K := affineMap (pderiv 0 (pderiv 0 (pderiv 0 affineF)))

theorem normalG_ne_zero : normalG ≠ 0 := normal_ne_zero

theorem velocity_first_identity :
    normalExpansion (pderiv 0 (pderiv 0 affineF)) * normalVelocity ^ 2 +
      normalExpansion (pderiv 0 affineF) * Dt normalVelocity = 0 := by
  have h := congrArg Dt normal_velocity_identity
  simp only [Derivation.leibniz, normalExpansion_chain_rule,
    smul_eq_mul, Derivation.map_one_eq_zero] at h
  linear_combination h

theorem velocity_second_identity :
    normalExpansion (pderiv 0 (pderiv 0 (pderiv 0 affineF))) * normalVelocity ^ 3 +
      3 * normalExpansion (pderiv 0 (pderiv 0 affineF)) * normalVelocity * Dt normalVelocity +
      normalExpansion (pderiv 0 affineF) * Dt (Dt normalVelocity) = 0 := by
  have h := congrArg Dt velocity_first_identity
  simp only [map_add, Derivation.leibniz, normalExpansion_chain_rule,
    Derivation.leibniz_pow, smul_eq_mul, map_zero] at h
  norm_num only [Nat.cast_ofNat, pow_one, Nat.reduceSub] at h
  linear_combination h

theorem velocity_constant : normalVelocity.constantCoeff = 1 / normalG := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) normal_velocity_identity
  simp only [map_mul, constantCoeff_normalExpansion, map_one] at h
  apply (eq_div_iff normalG_ne_zero).mpr
  simpa only [normalG, mul_comm] using h

theorem velocity_first_constant :
    (Dt normalVelocity).constantCoeff = -normalG1 / normalG ^ 3 := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) velocity_first_identity
  simp only [map_add, map_mul, map_pow, constantCoeff_normalExpansion, map_zero,
    velocity_constant] at h
  change normalG1 * (1 / normalG) ^ 2 +
    normalG * (Dt normalVelocity).constantCoeff = 0 at h
  apply (eq_div_iff (pow_ne_zero _ normalG_ne_zero)).mpr
  field_simp [normalG_ne_zero] at h
  linear_combination h

theorem velocity_second_constant :
    (Dt (Dt normalVelocity)).constantCoeff =
      (3 * normalG1 ^ 2 - normalG * normalG2) / normalG ^ 5 := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) velocity_second_identity
  simp only [map_add, map_mul, map_pow, map_ofNat, constantCoeff_normalExpansion,
    map_zero, velocity_constant, velocity_first_constant] at h
  change normalG2 * (1 / normalG) ^ 3 +
    3 * normalG1 * (1 / normalG) * (-normalG1 / normalG ^ 3) +
    normalG * (Dt (Dt normalVelocity)).constantCoeff = 0 at h
  apply (eq_div_iff (pow_ne_zero _ normalG_ne_zero)).mpr
  field_simp [normalG_ne_zero] at h
  linear_combination h

def densityStream (A : AmbientPoly 4) : S := normalExpansion A * normalVelocity

theorem densityStream_second_derivative (A : AmbientPoly 4) :
    Dt (Dt (densityStream A)) =
      normalExpansion (pderiv 0 (pderiv 0 A)) * normalVelocity ^ 3 +
        3 * normalExpansion (pderiv 0 A) * normalVelocity * Dt normalVelocity +
        normalExpansion A * Dt (Dt normalVelocity) := by
  simp only [densityStream, Derivation.leibniz, map_add, normalExpansion_chain_rule,
    smul_eq_mul]
  ring

/-- The normal Taylor coefficient is the actual residue density used in
the protected affine exactness criterion. -/
theorem densityStream_coefficient_two (A : AmbientPoly 4) :
    PowerSeries.coeff 2 (densityStream A) = affineNormalSource A / normalG := by
  have hcoef := PowerSeries.constantCoeff_iterate_derivative (densityStream A) 2
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, mul_one] at hcoef
  have hderiv := congrArg (PowerSeries.constantCoeff (R := K))
    (densityStream_second_derivative A)
  simp only [map_add, map_mul, map_pow, map_ofNat, constantCoeff_normalExpansion,
    velocity_constant, velocity_first_constant, velocity_second_constant] at hderiv
  have he : PowerSeries.coeff 2 (densityStream A) =
      (affineMap (pderiv 0 (pderiv 0 A)) * (1 / normalG) ^ 3 +
        3 * affineMap (pderiv 0 A) * (1 / normalG) * (-normalG1 / normalG ^ 3) +
        affineMap A * ((3 * normalG1 ^ 2 - normalG * normalG2) / normalG ^ 5)) / 2 := by
    rw [hcoef] at hderiv
    apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).mpr
    simpa only [mul_comm] using hderiv
  rw [he]
  unfold affineNormalSource normalSourceTwo normalG normalG1 normalG2
  field_simp [normal_ne_zero]
  ring

/-- The density of the actual pulled-back pole-three form in the genuine
normal chart. Its denominator is the image of f, not a formal replacement. -/
def poleThreeDensity (A : AmbientPoly 4) : HahnSeries ℤ K :=
  HahnSeries.ofPowerSeries ℤ K (normalExpansion A) /
      (HahnSeries.ofPowerSeries ℤ K (normalExpansion affineF)) ^ 3 *
    HahnSeries.ofPowerSeries ℤ K normalVelocity

theorem poleThreeDensity_expansion (A : AmbientPoly 4) :
    poleThreeDensity A = HahnSeries.ofPowerSeries ℤ K (densityStream A) *
      HahnSeries.single (-3) 1 := by
  simp only [poleThreeDensity, normalExpansion_F, HahnSeries.ofPowerSeries_X,
    div_eq_mul_inv, HahnSeries.single_pow, nsmul_eq_mul, one_pow,
    HahnSeries.inv_single, inv_one, densityStream, map_mul]
  norm_num
  ring

/-- The Laurent residue of the actual pole-three normal pullback is c/g. -/
theorem poleThreeDensity_residue (A : AmbientPoly 4) :
    (poleThreeDensity A).coeff (-1) = affineNormalSource A / normalG := by
  rw [poleThreeDensity_expansion, HahnSeries.coeff_mul_single]
  norm_num only [Int.reduceSub, mul_one]
  change (HahnSeries.ofPowerSeries ℤ K (densityStream A)).coeff ((2 : ℕ) : ℤ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff, densityStream_coefficient_two]

/-- Binding to the genuine exterior form used by the certificate theorem.
The coefficient is computed from the actual normal pullback, not postulated. -/
theorem residueSourceForm_eq_formalResidue (A : AmbientPoly 4) :
    CycleQ2AffineExactness.residueSourceForm A =
      (poleThreeDensity A).coeff (-1) • CycleQ2AffineExterior.volume := by
  rw [poleThreeDensity_residue]
  rfl

end CycleQ2FormalResidue

#print axioms CycleQ2FormalResidue.densityStream_coefficient_two
#print axioms CycleQ2FormalResidue.poleThreeDensity_residue
#print axioms CycleQ2FormalResidue.residueSourceForm_eq_formalResidue
end
end


/- Component: continuation_2/NormalChartDerivations.lean -/
section
/-!+# Actual coordinate derivations and Jacobian of the formal normal chart

The coefficient derivations are the actual complex tangent derivations of
the protected affine function field, extended coefficient by coefficient.
The formal parameter is held constant.  The normal derivative and the four
tangent derivations therefore give the implicit-coordinate Jacobian of the
faithful chart already constructed from `f ↦ T`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2PowerSeriesTangents

variable {C K : Type*} [CommRing C] [CommRing K] [Algebra C K]

def coefficientwise (D : Derivation C K K) (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => D (PowerSeries.coeff n f)

@[simp] theorem coefficientwise_coeff (D : Derivation C K K) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (coefficientwise D f) = D (PowerSeries.coeff n f) := by
  simp [coefficientwise]

theorem coefficientwise_mul (D : Derivation C K K) (f g : PowerSeries K) :
    coefficientwise D (f * g) = f * coefficientwise D g + g * coefficientwise D f := by
  rw [mul_comm g (coefficientwise D f)]
  ext n
  simp only [coefficientwise_coeff, PowerSeries.coeff_mul, map_sum, map_add,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  ring

/-- Coefficientwise extension as an actual complex-linear derivation. -/
def extend (D : Derivation C K K) : Derivation C (PowerSeries K) (PowerSeries K) where
  toFun := coefficientwise D
  map_add' f g := by
    ext n
    simp
  map_smul' c f := by
    ext n
    simp only [coefficientwise_coeff, PowerSeries.coeff_smul, Derivation.map_smul,
      RingHom.id_apply]
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  leibniz' f g := by
    change coefficientwise D (f * g) = f * coefficientwise D g + g * coefficientwise D f
    exact coefficientwise_mul D f g

@[simp] theorem extend_coeff (D : Derivation C K K) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (extend D f) = D (PowerSeries.coeff n f) :=
  coefficientwise_coeff D f n

@[simp] theorem extend_C (D : Derivation C K K) (a : K) :
    extend D (PowerSeries.C a) = PowerSeries.C (D a) := by
  ext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

@[simp] theorem extend_X (D : Derivation C K K) : extend D PowerSeries.X = 0 := by
  ext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

theorem extend_commute (D E : Derivation C K K) (h : Function.Commute D E) :
    Function.Commute (extend D) (extend E) := by
  intro f
  ext n
  simpa only [extend_coeff] using h (PowerSeries.coeff n f)

theorem derivative_extend_commute (D : Derivation C K K) :
    Function.Commute (PowerSeries.derivative K) (extend D) := by
  intro f
  ext n
  simp [PowerSeries.coeff_derivative, Derivation.leibniz, smul_eq_mul, mul_comm]

end CycleQ2PowerSeriesTangents

namespace CycleQ2PolynomialChainRule

open MvPolynomial

variable {R B M σ : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Fintype σ] [DecidableEq σ] [AddCommGroup M] [Module B M] [Module R M]

/-- The genuine derivation chain rule for any polynomial algebra map. -/
theorem apply (φ : MvPolynomial σ R →ₐ[R] B) (δ : Derivation R B M)
    (P : MvPolynomial σ R) :
    δ (φ P) = ∑ i : σ, φ (pderiv i P) • δ (φ (X i)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have hc : φ (MvPolynomial.C c) = algebraMap R B c := φ.commutes c
      rw [hc, Derivation.map_algebraMap]
      simp
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ, add_smul, Finset.sum_add_distrib]
  | mul_X P i ih =>
      have hs :
          (∑ j : σ, (φ (pderiv j P) * φ (X i)) • δ (φ (X j))) =
          φ (X i) • ∑ j : σ, φ (pderiv j P) • δ (φ (X j)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [smul_smul]
        congr 1
        ring
      have hd :
          (∑ j : σ, (φ P * φ (pderiv j (X i))) • δ (φ (X j))) =
          φ P • δ (φ (X i)) := by
        simp [pderiv_X, Pi.single_apply, apply_ite]
      rw [map_mul, Derivation.leibniz, ih]
      simp only [pderiv_mul, map_add, map_mul, add_smul, Finset.sum_add_distrib]
      rw [hs, hd]
      exact add_comm _ _

end CycleQ2PolynomialChainRule

namespace CycleQ2NormalChart

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineDifferentials CycleQ2FormalSpecialization CycleQ2NormalExpansion

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

def normalAlgHom : AmbientPoly 4 →ₐ[ℂ] S where
  toRingHom := normalExpansion
  commutes' c := by
    change normalExpansion (MvPolynomial.C c) = algebraMap ℂ S c
    rw [normalExpansion_C, PowerSeries.algebraMap_apply]
    rfl

def tangent (j : Fin 4) : Derivation ℂ S S :=
  CycleQ2PowerSeriesTangents.extend (complexTangent j)

def parameterDerivative : Derivation ℂ S S :=
  (PowerSeries.derivative K).restrictScalars ℂ

@[simp] theorem parameterDerivative_apply (f : S) : parameterDerivative f = Dt f := rfl

@[simp] theorem tangent_C (j : Fin 4) (a : K) :
    tangent j (PowerSeries.C a) = PowerSeries.C (affineTangent j a) := by
  exact CycleQ2PowerSeriesTangents.extend_C (complexTangent j) a

@[simp] theorem tangent_X (j : Fin 4) : tangent j PowerSeries.X = 0 :=
  CycleQ2PowerSeriesTangents.extend_X (complexTangent j)

@[simp] theorem tangent_coordinate (j i : Fin 4) :
    tangent j (PowerSeries.C (fieldCoordinate i.succ)) = if i = j then 1 else 0 := by
  rw [tangent_C]
  simp only [fieldCoordinate, affineTangent_coordinate]
  split_ifs <;> simp

theorem tangent_normalExpansion_chain (j : Fin 4) (P : AmbientPoly 4) :
    tangent j (normalExpansion P) =
      normalExpansion (pderiv 0 P) * tangent j normalRoot +
        normalExpansion (pderiv j.succ P) := by
  have h := CycleQ2PolynomialChainRule.apply normalAlgHom (tangent j) P
  change tangent j (normalExpansion P) =
    ∑ i : Fin 5, normalExpansion (pderiv i P) * tangent j (normalExpansion (X i)) at h
  rw [Fin.sum_univ_succ] at h
  simpa only [normalExpansion_X_zero, normalExpansion_X_succ, tangent_coordinate,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

theorem tangent_normalRoot (j : Fin 4) :
    tangent j normalRoot = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
  have h := tangent_normalExpansion_chain j affineF
  rw [normalExpansion_F, tangent_X] at h
  calc
    tangent j normalRoot =
        (normalExpansion (pderiv 0 affineF) * normalVelocity) * tangent j normalRoot := by
      rw [normal_velocity_identity, one_mul]
    _ = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
      linear_combination -normalVelocity * h

/-- The actual implicit-coordinate derivative with `f` held equal to the
formal parameter.  Its reciprocal normal derivative is the proved velocity. -/
theorem tangent_normalExpansion (j : Fin 4) (P : AmbientPoly 4) :
    tangent j (normalExpansion P) = normalExpansion (pderiv j.succ P) -
      normalVelocity * normalExpansion (pderiv j.succ affineF) *
        normalExpansion (pderiv 0 P) := by
  rw [tangent_normalExpansion_chain, tangent_normalRoot]
  ring

theorem tangents_commute (i j : Fin 4) : Function.Commute (tangent i) (tangent j) := by
  apply CycleQ2PowerSeriesTangents.extend_commute
  exact affineTangents_commute i j

theorem parameter_tangent_commute (j : Fin 4) :
    Function.Commute parameterDerivative (tangent j) :=
  CycleQ2PowerSeriesTangents.derivative_extend_commute (complexTangent j)

/-- The coordinate derivations are ordered `(∂T,E₁,E₂,E₃,E₄)`. -/
def coordinateDerivative : Fin 5 → Derivation ℂ S S :=
  Fin.cases parameterDerivative tangent

/-- Rows are coordinate derivations; columns are the five original affine
coordinate functions after the actual normal substitution. -/
def jacobian : Matrix (Fin 5) (Fin 5) S :=
  fun i j => coordinateDerivative i (normalExpansion (X j))

theorem jacobian_zero_row (i : Fin 5) :
    jacobian 0 i = if i = 0 then normalVelocity else 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [jacobian, coordinateDerivative, normalVelocity]
  · simp [jacobian, coordinateDerivative, Dt]

theorem jacobian_succ_zero (j : Fin 4) :
    jacobian j.succ 0 = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
  simpa [jacobian, coordinateDerivative] using tangent_normalRoot j

theorem jacobian_succ_succ (i j : Fin 4) :
    jacobian i.succ j.succ = if j = i then 1 else 0 := by
  change tangent i (normalExpansion (X j.succ)) = _
  rw [normalExpansion_X_succ, tangent_coordinate]

/-- The determinant is the actual normal velocity, with positive sign in
the stipulated parameter-first coordinate order. -/
theorem jacobian_det : Matrix.det jacobian = normalVelocity := by
  have hminor : jacobian.submatrix Fin.succ Fin.succ =
      (1 : Matrix (Fin 4) (Fin 4) S) := by
    ext i j
    simp [Matrix.submatrix, jacobian_succ_succ, Matrix.one_apply, eq_comm]
  rw [Matrix.det_succ_row_zero]
  simp [jacobian_zero_row, hminor]

/-! The algebraic Kähler module of a power-series ring need not be generated
by these five coordinate differentials.  The following argument instead
differentiates the actual polynomial relation inside that entire module. -/

abbrev Omega := Ω[S⁄ℂ]
abbrev universalD : Derivation ℂ S Omega := KaehlerDifferential.D ℂ S
abbrev TopForm := ⋀[S]^5 Omega

theorem normalExpansion_complex_constant (c : ℂ) :
    normalExpansion (MvPolynomial.C c) = algebraMap ℂ S c := by
  rw [normalExpansion_C, PowerSeries.algebraMap_apply]
  rfl

/-- The universal polynomial chain rule in the full algebraic Kähler module
of the power-series ring; no finite-rank or continuity assertion is used. -/
theorem universal_polynomial_differential (P : AmbientPoly 4) :
    universalD (normalExpansion P) =
      ∑ i : Fin 5, normalExpansion (pderiv i P) • universalD (normalExpansion (X i)) := by
  exact CycleQ2PolynomialChainRule.apply normalAlgHom universalD P

def tangentDifferential (j : Fin 4) : Omega :=
  universalD (PowerSeries.C (fieldCoordinate j.succ))

theorem universal_normal_differential :
    universalD normalRoot = normalVelocity • universalD PowerSeries.X -
      ∑ j : Fin 4, (normalVelocity * normalExpansion (pderiv j.succ affineF)) •
        tangentDifferential j := by
  have h := universal_polynomial_differential affineF
  rw [normalExpansion_F, Fin.sum_univ_succ] at h
  simp only [normalExpansion_X_zero, normalExpansion_X_succ] at h
  have hm := congrArg (fun η : Omega => normalVelocity • η) h
  have hv : normalVelocity * normalExpansion (pderiv 0 affineF) = 1 := by
    rw [mul_comm, normal_velocity_identity]
  simp only [smul_add, Finset.smul_sum, smul_smul, hv, one_smul] at hm
  exact (eq_sub_iff_add_eq).mpr hm.symm

private def wedgeWithTangents : Omega →ₗ[S] TopForm where
  toFun a := exteriorPower.ιMulti S 5 (Matrix.vecCons a tangentDifferential)
  map_add' a b := (exteriorPower.ιMulti S 5).map_vecCons_add tangentDifferential a b
  map_smul' c a := (exteriorPower.ιMulti S 5).map_vecCons_smul tangentDifferential c a

private theorem wedgeWithTangents_tangent (j : Fin 4) :
    wedgeWithTangents (tangentDifferential j) = 0 := by
  apply (exteriorPower.ιMulti S 5).map_eq_zero_of_eq
    (Matrix.vecCons (tangentDifferential j) tangentDifferential)
    (i := 0) (j := j.succ)
  · simp
  · exact (Fin.succ_ne_zero j).symm

/-- The ordered coordinate volume `dT ∧ dx₁ ∧ ... ∧ dx₄` in the actual
universal exterior power of the formal chart ring. -/
def normalVolume : TopForm :=
  exteriorPower.ιMulti S 5 (Matrix.vecCons (universalD PowerSeries.X) tangentDifferential)

/-- The wedge of the actual universal differentials of the substituted
five affine coordinates: the coordinate-generator exterior pullback. -/
def pulledBackCoordinateVolume : TopForm :=
  exteriorPower.ιMulti S 5 (fun i : Fin 5 => universalD (normalExpansion (X i)))

/-- The Jacobian factor also holds in genuine universal exterior forms,
not merely after evaluating against the five coordinate derivations. -/
theorem pulledBackCoordinateVolume_eq :
    pulledBackCoordinateVolume = normalVelocity • normalVolume := by
  have ht : (fun i : Fin 5 => universalD (normalExpansion (X i))) =
      Matrix.vecCons (universalD normalRoot) tangentDifferential := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [tangentDifferential]
  unfold pulledBackCoordinateVolume
  rw [ht]
  change wedgeWithTangents (universalD normalRoot) = _
  rw [universal_normal_differential, map_sub, map_smul, map_sum]
  simp only [map_smul, wedgeWithTangents_tangent, smul_zero,
    Finset.sum_const_zero, sub_zero]
  rfl

section UniversalExteriorPullback

abbrev AmbientOmega := Ω[(AmbientPoly 4)⁄ℂ]

local instance normalAlgebra : Algebra (AmbientPoly 4) S :=
  normalAlgHom.toRingHom.toAlgebra

local instance normalOmegaModule : Module (AmbientPoly 4) Omega :=
  Module.compHom Omega normalAlgHom.toRingHom

local instance normalTopModule : Module (AmbientPoly 4) TopForm :=
  Module.compHom TopForm normalAlgHom.toRingHom

local instance normalOmegaTower : IsScalarTower (AmbientPoly 4) S Omega where
  smul_assoc a b η := by
    change (normalAlgHom a * b) • η = normalAlgHom a • (b • η)
    exact mul_smul _ _ _

local instance normalTopTower : IsScalarTower (AmbientPoly 4) S TopForm where
  smul_assoc a b η := by
    change (normalAlgHom a * b) • η = normalAlgHom a • (b • η)
    exact mul_smul _ _ _

local instance normalComplexOmegaTower : IsScalarTower ℂ (AmbientPoly 4) Omega where
  smul_assoc c a η := by
    change normalAlgHom (c • a) • η = c • (normalAlgHom a • η)
    rw [map_smul]
    exact smul_assoc _ _ _

/-- The actual map of universal one-forms induced by the normal chart. -/
def oneFormPullback : AmbientOmega →ₗ[AmbientPoly 4] Omega :=
  (universalD.compAlgebraMap (AmbientPoly 4)).liftKaehlerDifferential

@[simp] theorem oneFormPullback_D (P : AmbientPoly 4) :
    oneFormPullback (KaehlerDifferential.D ℂ (AmbientPoly 4) P) =
      universalD (normalExpansion P) := by
  rw [oneFormPullback, Derivation.liftKaehlerDifferential_comp_D]
  rfl

private def targetWedgeOverAmbient :
    Omega [⋀^Fin 5]→ₗ[AmbientPoly 4] TopForm where
  toMultilinearMap := (exteriorPower.ιMulti S 5).toMultilinearMap.restrictScalars (AmbientPoly 4)
  map_eq_zero_of_eq' := (exteriorPower.ιMulti S 5).map_eq_zero_of_eq

/-- The induced exterior pullback, defined by the universal alternating
property and the genuine one-form pullback. -/
def exteriorPullback : (⋀[AmbientPoly 4]^5 AmbientOmega) →ₗ[AmbientPoly 4] TopForm :=
  exteriorPower.alternatingMapLinearEquiv
    (targetWedgeOverAmbient.compLinearMap oneFormPullback)

def ambientCoordinateVolume : ⋀[AmbientPoly 4]^5 AmbientOmega :=
  exteriorPower.ιMulti (AmbientPoly 4) 5
    (fun i : Fin 5 => KaehlerDifferential.D ℂ (AmbientPoly 4) (X i))

theorem exteriorPullback_ambientCoordinateVolume :
    exteriorPullback ambientCoordinateVolume = normalVelocity • normalVolume := by
  rw [exteriorPullback, ambientCoordinateVolume,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  simp only [oneFormPullback_D]
  exact pulledBackCoordinateVolume_eq

end UniversalExteriorPullback

end CycleQ2NormalChart

#print axioms CycleQ2PowerSeriesTangents.extend
#print axioms CycleQ2NormalChart.tangent_normalExpansion
#print axioms CycleQ2NormalChart.jacobian_det
#print axioms CycleQ2NormalChart.universal_normal_differential
#print axioms CycleQ2NormalChart.pulledBackCoordinateVolume_eq
#print axioms CycleQ2NormalChart.exteriorPullback_ambientCoordinateVolume
end
end


/- Component: continuation_2/PureM2Certificate.lean -/
section
/-!+# An exact certificate along the genuine one-term Fermat deformation

For every complex parameter `s`, this module gives a complete certificate for
`sum X_i^6 + s * X₂^3 X₀ X₅ X₃`, with the original protected source monomial.
The denominator is `36 * (X₂^6+X₅^6) * (X₁^6+X₄^6)`.  The factor 36 clears
the rational scalar coefficients of the vector field.  This is a distinct
one-term family, not an assertion about the protected three-term sextic.
-/

noncomputable section
namespace CycleQ2PureM2

set_option maxRecDepth 10000

open MvPolynomial HodgeComputer

abbrev Poly := AmbientPoly 5
abbrev A : Poly := HodgeSubmission.A

def U : Poly := X 2 ^ 6 + X 5 ^ 6
def V : Poly := X 1 ^ 6 + X 4 ^ 6
def M : Poly := X 2 ^ 3 * X 0 * X 5 * X 3
def F (s : ℂ) : Poly :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6 + C s * M

def D : Poly := C 36 * (U * V)

def N (s : ℂ) : Fin 6 → Poly :=
  ![0, C (-2 * s) * (A * M * X 1), C 3 * (A * V * X 2),
    0, C (-2 * s) * (A * M * X 4), C 3 * (A * V * X 5)]

theorem U_homogeneous : U.IsHomogeneous 6 := by
  exact (isHomogeneous_X_pow (2 : Fin 6) 6).add (isHomogeneous_X_pow 5 6)

theorem V_homogeneous : V.IsHomogeneous 6 := by
  exact (isHomogeneous_X_pow (1 : Fin 6) 6).add (isHomogeneous_X_pow 4 6)

theorem M_homogeneous : M.IsHomogeneous 6 := by
  have hx (i : Fin 6) : (X i : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ i
  simpa [M] using ((((hx 2).pow 3).mul (hx 0)).mul (hx 5)).mul (hx 3)

theorem F_homogeneous (s : ℂ) : (F s).IsHomogeneous 6 := by
  exact ((((((isHomogeneous_X_pow (0 : Fin 6) 6).add
    (isHomogeneous_X_pow 1 6)).add (isHomogeneous_X_pow 2 6)).add
    (isHomogeneous_X_pow 3 6)).add (isHomogeneous_X_pow 4 6)).add
    (isHomogeneous_X_pow 5 6)).add (M_homogeneous.C_mul s)

theorem D_homogeneous : D.IsHomogeneous 12 := by
  simpa [D] using (U_homogeneous.mul V_homogeneous).C_mul (36 : ℂ)

theorem D_ne_zero : D ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (fun _ : Fin 6 => (1 : ℂ))) h
  norm_num [D, U, V] at hh

theorem D_totalDegree : D.totalDegree = 12 := D_homogeneous.totalDegree D_ne_zero

theorem N_homogeneous (s : ℂ) (i : Fin 6) : (N s i).IsHomogeneous 19 := by
  have hA : A.IsHomogeneous 12 := CycleQ2Workspace.originalA_homogeneous
  have hx (j : Fin 6) : (X j : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ j
  have hU (j : Fin 6) : (C (3 : ℂ) * (A * V * X j)).IsHomogeneous 19 := by
    simpa using ((hA.mul V_homogeneous).mul (hx j)).C_mul (3 : ℂ)
  have hM (j : Fin 6) : (C (-2 * s) * (A * M * X j)).IsHomogeneous 19 := by
    simpa using ((hA.mul M_homogeneous).mul (hx j)).C_mul (-2 * s)
  fin_cases i
  · exact isHomogeneous_zero (Fin 6) ℂ 19
  · exact hM 1
  · exact hU 2
  · exact isHomogeneous_zero (Fin 6) ℂ 19
  · exact hM 4
  · exact hU 5

/- The elementary univariate retraction and monic argument also used for the
Fermat subset denominators.  Here the perturbation is linear in `X 0`, so it
preserves monicity and both denominator factors are constant in this variable. -/
private def toUni : Poly →+* Polynomial Poly :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => if i = 0 then Polynomial.X else Polynomial.C (X i))

private def fromUni : Polynomial Poly →+* Poly :=
  Polynomial.eval₂RingHom (RingHom.id Poly) (X 0)

private theorem retract : fromUni.comp toUni = RingHom.id Poly := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [toUni, fromUni]
  · intro i
    by_cases hi : i = 0 <;> simp [toUni, fromUni, hi]

private theorem monic_relPrime_constant {R : Type*} [CommRing R] [IsDomain R]
    {f : Polynomial R} (hf : f.Monic) {c : R} (hc : c ≠ 0) :
    IsRelPrime f (Polynomial.C c) := by
  intro p hpf hpc
  by_contra hunit
  have hpos := Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hf hunit hpf
  have hle := Polynomial.natDegree_le_of_dvd hpc (Polynomial.C_ne_zero.mpr hc)
  simp only [Polynomial.natDegree_C] at hle
  omega

private theorem toUni_F_monic (s : ℂ) : (toUni (F s)).Monic := by
  have hrepr : toUni (F s) = (Polynomial.X : Polynomial Poly) ^ 6 +
      (Polynomial.C (C s * X 2 ^ 3 * X 5 * X 3) * Polynomial.X +
       Polynomial.C (X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6)) := by
    simp [toUni, F, M]
    ring
  rw [hrepr]
  apply Polynomial.monic_X_pow_add
  exact (Polynomial.degree_add_le_of_le (Polynomial.degree_C_mul_X_le _)
    Polynomial.degree_C_le).trans_lt (by norm_num)

private theorem toUni_D : toUni D = Polynomial.C D := by
  simp [toUni, D, U, V]

theorem F_ne_zero (s : ℂ) : F s ≠ 0 := by
  intro h
  exact (toUni_F_monic s).ne_zero (by rw [h, map_zero])

theorem denominator_legal (s : ℂ) : IsRelPrime (F s) D := by
  apply HodgeComputer.relPrime_of_retract toUni fromUni retract
  rw [toUni_D]
  exact monic_relPrime_constant (toUni_F_monic s) D_ne_zero

private theorem sum_six (f : Fin 6 → Poly) :
    ∑ i, f i = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

set_option maxHeartbeats 2000000 in
theorem normalized_directional (s : ℂ) :
    (2 : Poly) * HodgeTestbed.directional (F s) (N s) = A * D := by
  unfold HodgeTestbed.directional
  rw [sum_six]
  simp [F, N, A,
    HodgeSubmission.A, D, U, V, M, map_add, pderiv_X, map_mul, map_neg, map_ofNat]
  ring

set_option maxHeartbeats 2000000 in
theorem divergence_zero (s : ℂ) : HodgeTestbed.divergenceNumerator D (N s) = 0 := by
  have h2 (i : Fin 6) : pderiv i (2 : Poly) = 0 := (pderiv i).map_natCast 2
  have h3 (i : Fin 6) : pderiv i (3 : Poly) = 0 := (pderiv i).map_natCast 3
  have h36 (i : Fin 6) : pderiv i (36 : Poly) = 0 := (pderiv i).map_natCast 36
  unfold HodgeTestbed.divergenceNumerator HodgeTestbed.divergence HodgeTestbed.directional
  rw [sum_six, sum_six]
  simp [N, A, HodgeSubmission.A,
    D, U, V, M, map_add, pderiv_mul, pderiv_X,
    h2, h3, h36, map_mul, map_neg, map_ofNat]
  ring

theorem verified (s : ℂ) : Verify (F s) A 6 2 D (N s) 0 where
  hypersurface_ne_zero := F_ne_zero s
  hypersurface_homogeneous := F_homogeneous s
  source_homogeneous := by
    simpa using Homogeneous.of_isHomogeneous CycleQ2Workspace.originalA_homogeneous
  denominator_ne_zero := D_ne_zero
  denominator_homogeneous := by simpa only [D_totalDegree] using D_homogeneous
  numerator_homogeneous := by
    intro i
    simpa [D_totalDegree] using Homogeneous.of_isHomogeneous (N_homogeneous s i)
  denominator_legal := denominator_legal s
  identity := normalized_identity (normalized_directional s) (by
    simpa only [mul_zero] using divergence_zero s)

/-- A complete, unconditional certificate along this one-term family. -/
theorem hasCertificate (s : ℂ) : HasCertificate (F s) 2 HodgeSubmission.A :=
  (verified s).hasCertificate

end CycleQ2PureM2

#print axioms CycleQ2PureM2.denominator_legal
#print axioms CycleQ2PureM2.normalized_directional
#print axioms CycleQ2PureM2.divergence_zero
#print axioms CycleQ2PureM2.hasCertificate
end
end


/- Component: continuation_2/CartierMatrixFactorization.lean -/
section
/-!
# Actual polynomial resolution data for the invariant Cartier curve

All entries below are literal polynomials over an arbitrary commutative ring.
The six by six matrices factor the actual cubic a^3-b^3+c^3+d^3.
The augmentation is the previously constructed elliptic-sextic residual ideal.
The two original second syzygies alone do not give the full hypersurface
resolution: the four columns of H0 are necessary.

No geometric deformation theorem or characteristic-zero rank lifting is
asserted in this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CycleQ2CartierResolution

variable {R : Type*} [CommRing R] (a b c d : R)

def cubic : R := a ^ 3 - b ^ 3 + c ^ 3 + d ^ 3

def first : Matrix (Fin 4) (Fin 6) R :=
  !![a^2, b^2, -c^2, d^2, a*d, -b*c;
     c, -d, a, -b, 0, 0;
     b, a, 0, 0, c, -d;
     0, 0, d, c, b, a]

def second : Matrix (Fin 6) (Fin 2) R :=
  !![d, 0; c, 0; 0, b; 0, a; -a, -d; b, -c]

def homotopy0 : Matrix (Fin 6) (Fin 4) R :=
  !![a, c^2, -b^2, b*c;
     -b, -d^2, a^2, a*d;
     -c, a^2, a*d, d^2;
     d, b^2, -b*c, c^2;
     0, -b*c, c^2, -b^2;
     0, -a*d, -d^2, a^2]

def homotopy1 : Matrix (Fin 2) (Fin 6) R :=
  !![d^2, c^2, -b*c, -a*d, -a^2, -b^2;
     -a*d, b*c, -b^2, a^2, -d^2, -c^2]

def even : Matrix (Fin 6) (Fin 6) R :=
  !![d, 0, a, c^2, -b^2, b*c;
     c, 0, -b, -d^2, a^2, a*d;
     0, b, -c, a^2, a*d, d^2;
     0, a, d, b^2, -b*c, c^2;
     -a, -d, 0, -b*c, c^2, -b^2;
     b, -c, 0, -a*d, -d^2, a^2]

def odd : Matrix (Fin 6) (Fin 6) R :=
  !![d^2, c^2, -b*c, -a*d, -a^2, -b^2;
     -a*d, b*c, -b^2, a^2, -d^2, -c^2;
     a^2, b^2, -c^2, d^2, a*d, -b*c;
     c, -d, a, -b, 0, 0;
     b, a, 0, 0, c, -d;
     0, 0, d, c, b, a]

def generators : Matrix (Fin 1) (Fin 4) R :=
  !![a^2*b - c*d^2 + 2*c*(a*c+b*d),
     -2*a^3*c+a^2*d^2+a*b*c^2+2*b^3*c-b^2*c*d,
     -2*a^2*c*d-a*b^3+a*d^3-2*b^2*c^2+b*c^2*d,
     a*b^2*c-2*a*c*d^2-b^3*d+2*b*c^3+d^4]

def cubicColumn : Matrix (Fin 1) (Fin 6) R :=
  !![-a*b, 0, 2*a*c-d^2, -2*b*c, -b*d, 0]

theorem first_second : first a b c d * second a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, second, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem first_homotopy0 : first a b c d * homotopy0 a b c d =
    cubic a b c d • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, homotopy0, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy_identity :
    second a b c d * homotopy1 a b c d + homotopy0 a b c d * first a b c d =
      cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, second, homotopy0, homotopy1, cubic,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy1_second : homotopy1 a b c d * second a b c d =
    cubic a b c d • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [homotopy1, second, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy1_homotopy0 : homotopy1 a b c d * homotopy0 a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [homotopy1, homotopy0, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem even_odd : even a b c d * odd a b c d =
    cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [even, odd, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem odd_even : odd a b c d * even a b c d =
    cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [even, odd, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem augmentation_first :
    generators a b c d * first a b c d + cubic a b c d • cubicColumn a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [generators, first, cubicColumn, cubic,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem cubicColumn_second : cubicColumn a b c d * second a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicColumn, second, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem cubicColumn_homotopy0 :
    cubicColumn a b c d * homotopy0 a b c d + generators a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicColumn, homotopy0, generators,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end CycleQ2CartierResolution

#print axioms CycleQ2CartierResolution.even_odd
#print axioms CycleQ2CartierResolution.odd_even
#print axioms CycleQ2CartierResolution.homotopy_identity
#print axioms CycleQ2CartierResolution.augmentation_first
#print axioms CycleQ2CartierResolution.cubicColumn_homotopy0
end


/- Component: continuation_2/CartierMatrixFactorizationExactness.lean -/
section
/-!
# Genuine exactness of the actual periodic complex modulo the cubic

A matrix factorization over a domain gives an exact two-periodic complex
after quotienting by its nonzero scalar. The proof lifts a kernel vector,
uses divisibility by the scalar, and cancels that scalar in the domain.
The resulting theorem is applied to the actual six by six cubic matrices.

This proves quotient-module exactness. It does not assert saturation,
base change through the cubic section, or nonlinear geometric lifting.
-/

set_option autoImplicit false

noncomputable section
namespace CycleQ2CartierResolution

open Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

theorem matrixFactorization_exact_mod
    {n : Type*} [Fintype n] [DecidableEq n]
    (g : R) (hg : g ≠ 0) (A B : Matrix n n R)
    (hAB : A * B = g • (1 : Matrix n n R))
    (hBA : B * A = g • (1 : Matrix n n R))
    (x : n → R ⧸ Ideal.span ({g} : Set R)) :
    A.map (Ideal.Quotient.mk (Ideal.span ({g} : Set R))) *ᵥ x = 0 ↔
      ∃ y, B.map (Ideal.Quotient.mk (Ideal.span ({g} : Set R))) *ᵥ y = x := by
  let I : Ideal R := Ideal.span ({g} : Set R)
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  change A.map q *ᵥ x = 0 ↔ ∃ y, B.map q *ᵥ y = x
  have hqg : q g = 0 := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.subset_span (Set.mem_singleton g)
  have hqAB : A.map q * B.map q = 0 := by
    rw [← Matrix.map_mul, hAB]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hqg]
  constructor
  · intro hx
    choose z hz using fun i => Ideal.Quotient.mk_surjective (x i)
    have hqz : q ∘ z = x := funext hz
    have hdiv : ∀ i, g ∣ (A *ᵥ z) i := by
      intro i
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      change q ((A *ᵥ z) i) = 0
      rw [RingHom.map_mulVec, hqz, hx]
      rfl
    choose y hy using hdiv
    have hAz : A *ᵥ z = g • y := by
      funext i
      exact hy i
    have hcancel : g • z = g • (B *ᵥ y) := by
      calc
        g • z = (B * A) *ᵥ z := by
          rw [hBA, smul_mulVec, one_mulVec]
        _ = B *ᵥ (A *ᵥ z) := (mulVec_mulVec z B A).symm
        _ = B *ᵥ (g • y) := by rw [hAz]
        _ = g • (B *ᵥ y) := mulVec_smul B g y
    have hzy : z = B *ᵥ y := by
      funext i
      apply mul_left_cancel₀ hg
      exact congrArg (fun v : n → R => v i) hcancel
    refine ⟨q ∘ y, ?_⟩
    funext i
    rw [← RingHom.map_mulVec, ← hzy]
    exact hz i
  · rintro ⟨y, rfl⟩
    rw [mulVec_mulVec, hqAB, zero_mulVec]

abbrev cubicQuotient (a b c d : R) := R ⧸ Ideal.span ({cubic a b c d} : Set R)

def cubicQuotientMap (a b c d : R) : R →+* cubicQuotient a b c d :=
  Ideal.Quotient.mk (Ideal.span ({cubic a b c d} : Set R))

theorem even_exact_mod_cubic (a b c d : R) (hg : cubic a b c d ≠ 0)
    (x : Fin 6 → cubicQuotient a b c d) :
    (even a b c d).map (cubicQuotientMap a b c d) *ᵥ x = 0 ↔
      ∃ y, (odd a b c d).map (cubicQuotientMap a b c d) *ᵥ y = x :=
  matrixFactorization_exact_mod (cubic a b c d) hg (even a b c d) (odd a b c d)
    (even_odd a b c d) (odd_even a b c d) x

theorem odd_exact_mod_cubic (a b c d : R) (hg : cubic a b c d ≠ 0)
    (x : Fin 6 → cubicQuotient a b c d) :
    (odd a b c d).map (cubicQuotientMap a b c d) *ᵥ x = 0 ↔
      ∃ y, (even a b c d).map (cubicQuotientMap a b c d) *ᵥ y = x :=
  matrixFactorization_exact_mod (cubic a b c d) hg (odd a b c d) (even a b c d)
    (odd_even a b c d) (even_odd a b c d) x

end CycleQ2CartierResolution

#print axioms CycleQ2CartierResolution.matrixFactorization_exact_mod
#print axioms CycleQ2CartierResolution.even_exact_mod_cubic
#print axioms CycleQ2CartierResolution.odd_exact_mod_cubic
end
end


