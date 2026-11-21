import Proposal.SeedChartRelationsAndRankTransfer
import Proposal.FermatJacobianHiggsForms

/-!
# The gradient open and the incidence basepoint charts
-/

set_option Elab.async false

/- Component: continuation_3/GenericSexticGradient.lean -/
section
/-! The actual generic invariant sextic has no nonzero common gradient
zero. A finite homogeneous multiplication map is surjective at the Fermat
specialization. Its proved determinant open is nonzero in the independent
coefficient ring, hence remains a unit over its fraction field and every
field extension. This proves the algebraic gradient condition; it does not
silently invoke a geometric smoothness or cohomology comparison theorem. -/

noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2GenericSexticGradient
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2HomogeneousIdealArithmetic

abbrev CoeffRing := MvPolynomial (FullInvariantIndex 6) ℂ

def universalF : Poly CoeffRing := fullInvariantPolynomial 6 X
def generators : Fin 5 → Poly CoeffRing := fun j => X j * pderiv j universalF
def degree : Fin 5 → ℕ := fun _ => 6
def purePower : Fin 5 → ℕ := ![6,6,6,6,3]
def coordinatePower : Fin 5 → ℕ := ![30,30,30,30,15]

theorem euler_homogeneous {R : Type*} [CommRing R] {p : Poly R}
    {d : Grade} (hp : HG p d) (j : Fin 5) : HG (X j * pderiv j p) d := by
  classical
  rw [p.as_sum]
  simp only [map_sum,Finset.mul_sum,X_mul_pderiv_monomial]
  apply (weightedHomogeneousSubmodule R fullGrading d).sum_mem
  intro e he
  apply (weightedHomogeneousSubmodule R fullGrading d).nsmul_mem
  exact isWeightedHomogeneous_monomial fullGrading _ _ (hp (mem_support_iff.mp he))

theorem generators_homogeneous (j : Fin 5) : HG (generators j) (degree j,0) :=
  euler_homogeneous (fullInvariantPolynomial_homogeneous 6 X) j

theorem purePower_homogeneous (j : Fin 5) :
    HG ((X j : Poly ℂ)^purePower j) (6,0) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_single]
  fin_cases j <;> decide

theorem fermat_homogeneous : HG CycleQ2FermatJacobian.fermat (6,0) :=
  ((((purePower_homogeneous 0).add (purePower_homogeneous 1)).add
    (purePower_homogeneous 2)).add (purePower_homogeneous 3)).add
    (purePower_homogeneous 4)

def fermatCoefficients : FullInvariantIndex 6 → ℂ :=
  fun e => CycleQ2FermatJacobian.fermat.coeff (fullExponentOf e.val)
def seedEvaluation : CoeffRing →+* ℂ := eval fermatCoefficients

theorem universalF_seed : MvPolynomial.map seedEvaluation universalF =
    CycleQ2FermatJacobian.fermat := by
  rw [universalF,map_fullInvariantPolynomial]
  have h : seedEvaluation ∘ (X : FullInvariantIndex 6 → CoeffRing)=fermatCoefficients := by
    funext e
    simp only [Function.comp_apply,seedEvaluation,eval_X]
  rw [h]
  exact fullInvariantPolynomial_of_homogeneous fermat_homogeneous

theorem generators_seed (j : Fin 5) :
    MvPolynomial.map seedEvaluation (generators j) =
      C (CycleQ2FermatJacobian.derivativeScalar j) * X j ^ purePower j := by
  rw [generators,map_mul,map_X,←pderiv_map,universalF_seed,
    CycleQ2FermatJacobian.derivative_eq]
  have hp : purePower j=CycleQ2FermatJacobian.cutoff j+1 := by
    fin_cases j <;> rfl
  rw [hp,pow_succ]
  unfold CycleQ2FermatJacobian.generator
  ring

theorem purePower_seed_mem (j : Fin 5) :
    (X j : Poly ℂ)^purePower j ∈
      generatorIdeal (fun j => MvPolynomial.map seedEvaluation (generators j)) := by
  have h := Ideal.subset_span (Set.mem_range_self
    (f := fun j => MvPolynomial.map seedEvaluation (generators j)) j)
  change MvPolynomial.map seedEvaluation (generators j) ∈
    generatorIdeal (fun j => MvPolynomial.map seedEvaluation (generators j)) at h
  have hh := Ideal.mul_mem_left _ (C ((CycleQ2FermatJacobian.derivativeScalar j)⁻¹)) h
  rwa [generators_seed,←mul_assoc,←map_mul,
    inv_mul_cancel₀ (CycleQ2FermatJacobian.derivativeScalar_ne_zero j),map_one,one_mul] at hh

theorem degree30_divisible (e : FullInvariantIndex 30) :
    ∃ j : Fin 5, purePower j ≤ fullExponentOf e.val j := by
  by_contra h
  push Not at h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have hd := e.property.1
  rw [fullExponentOf_apply,show purePower 0=6 by decide] at h0
  rw [fullExponentOf_apply,show purePower 1=6 by decide] at h1
  rw [fullExponentOf_apply,show purePower 2=6 by decide] at h2
  rw [fullExponentOf_apply,show purePower 3=6 by decide] at h3
  rw [fullExponentOf_apply,show purePower 4=3 by decide] at h4
  simp only [fullDegree] at hd
  omega

theorem seed_monomial_mem (e : FullInvariantIndex 30) :
    (monomial (fullExponentOf e.val) 1 : Poly ℂ) ∈
      generatorIdeal (fun j => MvPolynomial.map seedEvaluation (generators j)) := by
  obtain ⟨j,hj⟩ := degree30_divisible e
  have he : Finsupp.single j (purePower j) ≤ fullExponentOf e.val :=
    Finsupp.single_le_iff.mpr hj
  have hm : (monomial (fullExponentOf e.val) 1 : Poly ℂ) =
      X j^purePower j * monomial (fullExponentOf e.val-Finsupp.single j (purePower j)) 1 := by
    rw [X_pow_eq_monomial,monomial_mul,one_mul,add_tsub_cancel_of_le he]
  rw [hm]
  exact Ideal.mul_mem_right _ _ (purePower_seed_mem j)

theorem seed_homogeneous_mem (p : Poly ℂ) (hp : HG p (30,0)) :
    p ∈ generatorIdeal (fun j => MvPolynomial.map seedEvaluation (generators j)) := by
  rw [←fullInvariantPolynomial_of_homogeneous hp]
  apply Ideal.sum_mem
  intro e _
  simpa only [C_mul_monomial,mul_one] using
    Ideal.mul_mem_left (generatorIdeal (fun j => MvPolynomial.map seedEvaluation (generators j)))
      (C (p.coeff (fullExponentOf e.val))) (seed_monomial_mem e)

theorem degree_le (j : Fin 5) : degree j ≤ 30 := by
  change 6≤30
  decide

def coefficientMatrix : Matrix (FullInvariantIndex 30) (Column 30 degree) CoeffRing :=
  multiplicationMatrix generators degree 30

theorem seed_surjective : Function.Surjective (coefficientMatrix.map seedEvaluation).mulVec := by
  rw [coefficientMatrix,multiplicationMatrix_map]
  exact multiplication_surjective_of_membership _ degree
    (fun j => homogeneous_map _ (generators_homogeneous j)) 30 degree_le seed_homogeneous_mem

theorem exists_gradient_open : ∃ s : CoeffRing, seedEvaluation s=1 ∧
    ∀ (S : Type) [CommRing S] (φ : CoeffRing →+* S), IsUnit (φ s) →
      Function.Surjective (coefficientMatrix.map φ).mulVec := by
  exact CycleQ2HomogeneousIdealOpen.exists_multiplication_open seedEvaluation
    (C : ℂ →+* CoeffRing) (fun x => by simp only [seedEvaluation,eval_C]) generators degree
    generators_homogeneous 30 degree_le seed_homogeneous_mem

def gradientOpen : CoeffRing := Classical.choose exists_gradient_open

theorem gradientOpen_seed : seedEvaluation gradientOpen=1 :=
  (Classical.choose_spec exists_gradient_open).1

theorem gradientOpen_ne_zero : gradientOpen ≠ 0 := by
  intro hz
  have h := gradientOpen_seed
  rw [hz,map_zero] at h
  exact zero_ne_one h

theorem homogeneous_mem_of_open {S : Type} [CommRing S]
    (φ : CoeffRing →+* S) (hs : IsUnit (φ gradientOpen))
    (p : Poly S) (hp : HG p (30,0)) :
    p ∈ generatorIdeal (fun j => MvPolynomial.map φ (generators j)) := by
  have h := (Classical.choose_spec exists_gradient_open).2 S φ hs
  rw [coefficientMatrix,multiplicationMatrix_map] at h
  exact membership_of_multiplication_surjective _ degree
    (fun j => homogeneous_map _ (generators_homogeneous j)) 30 degree_le h p hp

theorem coordinatePower_homogeneous {S : Type*} [CommRing S] (j : Fin 5) :
    HG ((X j : Poly S)^coordinatePower j) (30,0) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_single]
  fin_cases j <;> decide

theorem coordinate_power_mem {S : Type} [CommRing S]
    (φ : CoeffRing →+* S) (hs : IsUnit (φ gradientOpen)) (j : Fin 5) :
    (X j : Poly S)^coordinatePower j ∈
      generatorIdeal (fun j => MvPolynomial.map φ (generators j)) :=
  homogeneous_mem_of_open φ hs _ (coordinatePower_homogeneous j)

/-- Every faithful coefficient specialization, including the actual generic
field and its field extensions, has no nonzero common zero of all five
partial derivatives. The polynomial is the complete invariant sextic. -/
theorem nonzero_gradient_of_injective {K : Type} [Field K]
    (φ : CoeffRing →+* K) (hφ : Function.Injective φ) (x : Fin 5 → K)
    (hx : ∃ j, x j ≠ 0) :
    ∃ j, eval x (pderiv j (MvPolynomial.map φ universalF)) ≠ 0 := by
  have hs : IsUnit (φ gradientOpen) := isUnit_iff_ne_zero.mpr
    (fun hz => gradientOpen_ne_zero (hφ (hz.trans (map_zero φ).symm)))
  by_contra! hzero
  have hle : generatorIdeal (fun j => MvPolynomial.map φ (generators j)) ≤
      RingHom.ker (eval x) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change eval x (MvPolynomial.map φ (generators j))=0
    rw [generators,map_mul,map_X,←pderiv_map,map_mul,eval_X,hzero j,mul_zero]
  obtain ⟨j,hj⟩ := hx
  have hz := hle (coordinate_power_mem φ hs j)
  change eval x ((X j)^coordinatePower j)=0 at hz
  rw [map_pow,eval_X] at hz
  exact (pow_ne_zero _ hj) hz

/-- The preceding condition holds over every field extension of the actual
independent-coefficient fraction field. In particular, passing to a finite
field that carries an incidence solution introduces no new smoothness
assumption about the sextic. -/
theorem nonzero_gradient_over_fraction_extension {K : Type} [Field K]
    [Algebra (FractionRing CoeffRing) K] (x : Fin 5 → K)
    (hx : ∃ j, x j ≠ 0) :
    ∃ j, eval x (pderiv j (MvPolynomial.map
      ((algebraMap (FractionRing CoeffRing) K).comp
        (algebraMap CoeffRing (FractionRing CoeffRing))) universalF)) ≠ 0 :=
  nonzero_gradient_of_injective _
    ((algebraMap (FractionRing CoeffRing) K).injective.comp
      (IsFractionRing.injective CoeffRing (FractionRing CoeffRing))) x hx

end CycleQ2GenericSexticGradient

#print axioms CycleQ2GenericSexticGradient.gradientOpen_seed
#print axioms CycleQ2GenericSexticGradient.nonzero_gradient_of_injective
#print axioms CycleQ2GenericSexticGradient.nonzero_gradient_over_fraction_extension
end
end

/- Component: continuation_3/IncidenceBasepointOpen.lean -/
section
/-! # A genuine polynomial open with no projective matrix basepoints

The complete degree120 multiplication matrix is formed from the actual
moving matrix entries, cubic, and sextic. A seed right inverse determines
a polynomial whose seed value is one. On its principal open, the original
coordinate powers lie in the matrix-entry ideal modulo the moving cubic
and sextic. No list of maximal minors or geometric openness premise occurs.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceBasepointOpen

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2HomogeneousIdealArithmetic
open CycleQ2SegreComplexBasepoint (generatorDegree generatorDegree_le coordinatePower)

def rawMatrixCoefficient (i j : Fin 3) (e : StandardIndex 14) : Coeff :=
  X (Sum.inr (Sum.inr ((i,j),e)))

def familyMatrix : Matrix (Fin 3) (Fin 3) (Poly Coeff) :=
  incidenceMatrix 57 rawMatrixCoefficient

def generators {R : Type*} [CommRing R] (r : R)
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) : Fin 11 → Poly R :=
  ![incidenceMatrix r δ 0 0,incidenceMatrix r δ 0 1,incidenceMatrix r δ 0 2,
    incidenceMatrix r δ 1 0,incidenceMatrix r δ 1 1,incidenceMatrix r δ 1 2,
    incidenceMatrix r δ 2 0,incidenceMatrix r δ 2 1,incidenceMatrix r δ 2 2,
    fullInvariantPolynomial 3 hc,fullInvariantPolynomial 6 Fc]

def universalGenerators : Fin 11 → Poly Coeff :=
  generators 57 rawCubicCoefficient rawSexticCoefficient rawMatrixCoefficient

theorem generators_homogeneous {R : Type*} [CommRing R] (r : R)
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (j : Fin 11) :
    HG (generators r hc Fc δ j) (generatorDegree j,0) := by
  fin_cases j
  · exact incidenceMatrix_homogeneous r δ 0 0
  · exact incidenceMatrix_homogeneous r δ 0 1
  · exact incidenceMatrix_homogeneous r δ 0 2
  · exact incidenceMatrix_homogeneous r δ 1 0
  · exact incidenceMatrix_homogeneous r δ 1 1
  · exact incidenceMatrix_homogeneous r δ 1 2
  · exact incidenceMatrix_homogeneous r δ 2 0
  · exact incidenceMatrix_homogeneous r δ 2 1
  · exact incidenceMatrix_homogeneous r δ 2 2
  · exact fullInvariantPolynomial_homogeneous 3 hc
  · exact fullInvariantPolynomial_homogeneous 6 Fc

theorem generators_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (r : R)
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    (fun j => map φ (generators r hc Fc δ j))=
      generators (φ r) (φ ∘ hc) (φ ∘ Fc) (fun i j e => φ (δ i j e)) := by
  have hm (i j : Fin 3) : map φ (incidenceMatrix r δ i j)=
      incidenceMatrix (φ r) (fun i j e => φ (δ i j e)) i j := by
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using
      congrArg (fun M : Matrix (Fin 3) (Fin 3) (Poly S) => M i j)
        (map_incidenceMatrix φ r δ)
  funext j
  fin_cases j
  · exact hm 0 0
  · exact hm 0 1
  · exact hm 0 2
  · exact hm 1 0
  · exact hm 1 1
  · exact hm 1 2
  · exact hm 2 0
  · exact hm 2 1
  · exact hm 2 2
  · exact map_fullInvariantPolynomial φ 3 hc
  · exact map_fullInvariantPolynomial φ 6 Fc

def seedEvaluation : Coeff →+* ℂ :=
  (polynomialSpecialization (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (fun _ _ _ => 0)).toRingHom

theorem seedEvaluation_constant (c : ℂ) : seedEvaluation (C c)=c :=
  (polynomialSpecialization (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (fun _ _ _ => 0)).commutes c

def seedFamilyGenerators : Fin 11 → Poly ℂ :=
  ![rawSeedMatrix 57 0 0,rawSeedMatrix 57 0 1,rawSeedMatrix 57 0 2,
    rawSeedMatrix 57 1 0,rawSeedMatrix 57 1 1,rawSeedMatrix 57 1 2,
    rawSeedMatrix 57 2 0,rawSeedMatrix 57 2 1,rawSeedMatrix 57 2 2,
    smoothH Complex.I,smoothF 57 Complex.I]

theorem seed_universalGenerators :
    (fun j => map seedEvaluation (universalGenerators j))=seedFamilyGenerators := by
  have hh : seedEvaluation ∘ rawCubicCoefficient=seedCubicCoefficients Complex.I := by
    funext e
    simp [seedEvaluation,rawCubicCoefficient,polynomialSpecialization,coefficientPoint]
  have hF : seedEvaluation ∘ rawSexticCoefficient=seedSexticCoefficients (57:ℂ) Complex.I := by
    funext e
    simp [seedEvaluation,rawSexticCoefficient,polynomialSpecialization,coefficientPoint]
  have hδ : (fun i j e => seedEvaluation (rawMatrixCoefficient i j e))=
      (fun _ _ _ => (0:ℂ)) := by
    funext i j e
    simp [seedEvaluation,rawMatrixCoefficient,polynomialSpecialization,coefficientPoint]
  rw [universalGenerators,generators_map,hh,hF,hδ,map_ofNat]
  simp only [generators,incidenceMatrix_zero,seedCubicCoefficients_polynomial,
    seedSexticCoefficients_polynomial,seedFamilyGenerators]

private theorem eleven_span_replace {A : Type*} [CommRing A]
    (a0 a1 a2 a3 a4 a5 a6 a7 a8 h g k : A) :
    Ideal.span (Set.range ![a0,a1,a2,a3,a4,a5,a6,a7,a8,h,g])≤
      Ideal.span (Set.range ![a0,a1,a2,a3,a4,a5,a6,a7,a8,h,g+h*k]) := by
  have ht : (Ideal.span {h} : Ideal A) ⊔ Ideal.span {g+h*k}=
      Ideal.span {h} ⊔ Ideal.span {g} := by
    rw [←Ideal.span_union,←Ideal.span_union]
    simpa only [Set.singleton_union] using Ideal.span_pair_add_left_mul h g k
  simp only [Matrix.range_cons,Matrix.range_empty,Set.union_empty,
    Ideal.span_union,ht,le_refl]

theorem seed_ideal_le :
    generatorIdeal (CycleQ2SegreComplexBasepoint.seedGenerators (57:ℂ) Complex.I)≤
      generatorIdeal seedFamilyGenerators := by
  simpa only [generatorIdeal,CycleQ2SegreComplexBasepoint.seedGenerators,
    seedFamilyGenerators,smoothF] using
    eleven_span_replace
      (rawSeedMatrix (57:ℂ) 0 0) (rawSeedMatrix (57:ℂ) 0 1) (rawSeedMatrix (57:ℂ) 0 2)
      (rawSeedMatrix (57:ℂ) 1 0) (rawSeedMatrix (57:ℂ) 1 1) (rawSeedMatrix (57:ℂ) 1 2)
      (rawSeedMatrix (57:ℂ) 2 0) (rawSeedMatrix (57:ℂ) 2 1) (rawSeedMatrix (57:ℂ) 2 2)
      (smoothH Complex.I) (seedG (57:ℂ)) (smoothK Complex.I)

theorem seed_homogeneous_mem (p : Poly ℂ) (hp : HG p (120,0)) :
    p∈generatorIdeal seedFamilyGenerators :=
  seed_ideal_le (CycleQ2SegreComplexBasepoint.complex_homogeneous_mem p hp)

def familyMultiplicationMatrix :
    Matrix (FullInvariantIndex 120) (Column 120 generatorDegree) Coeff :=
  multiplicationMatrix universalGenerators generatorDegree 120

theorem seed_multiplication_surjective :
    Function.Surjective (familyMultiplicationMatrix.map seedEvaluation).mulVec := by
  rw [familyMultiplicationMatrix,multiplicationMatrix_map,seed_universalGenerators]
  have hg (j : Fin 11) : HG (seedFamilyGenerators j) (generatorDegree j,0) := by
    rw [←congrFun seed_universalGenerators j]
    exact homogeneous_map seedEvaluation
      (generators_homogeneous (57:Coeff) rawCubicCoefficient rawSexticCoefficient rawMatrixCoefficient j)
  exact multiplication_surjective_of_membership seedFamilyGenerators generatorDegree hg
    120 generatorDegree_le seed_homogeneous_mem

/-- A genuine polynomial, nonzero at the seed, controls basepoint freeness
over arbitrary commutative coefficient rings on its principal open. -/
theorem exists_basepoint_polynomial :
    ∃s : Coeff,seedEvaluation s=1 ∧
      ∀ (S : Type) [CommRing S] (g : Coeff →+* S),IsUnit (g s) →
        ∀p : Poly S,HG p (120,0) →
          p∈generatorIdeal (fun j => map g (universalGenerators j)) := by
  have hseed (p : Poly ℂ) (hp : HG p (120,0)) :
      p∈generatorIdeal (fun j => map seedEvaluation (universalGenerators j)) := by
    rw [seed_universalGenerators]
    exact seed_homogeneous_mem p hp
  exact CycleQ2HomogeneousIdealOpen.exists_homogeneous_open
    seedEvaluation (C : ℂ →+* Coeff) seedEvaluation_constant
    universalGenerators generatorDegree
    (generators_homogeneous (57:Coeff) rawCubicCoefficient rawSexticCoefficient rawMatrixCoefficient)
    120 generatorDegree_le hseed

def basepointPolynomial : Coeff := exists_basepoint_polynomial.choose

theorem seed_basepointPolynomial : seedEvaluation basepointPolynomial=1 :=
  exists_basepoint_polynomial.choose_spec.1

theorem basepointPolynomial_ne_zero : basepointPolynomial≠0 := by
  intro hz
  have h := seed_basepointPolynomial
  rw [hz,map_zero] at h
  exact zero_ne_one h

theorem specialized_homogeneous_mem {S : Type} [CommRing S]
    (g : Coeff →+* S) (hs : IsUnit (g basepointPolynomial))
    (p : Poly S) (hp : HG p (120,0)) :
    p∈generatorIdeal (fun j => map g (universalGenerators j)) :=
  exists_basepoint_polynomial.choose_spec.2 S g hs p hp

theorem coordinate_power_homogeneous {S : Type*} [CommRing S] (j : Fin 5) :
    HG ((X j : Poly S)^coordinatePower j) (120,0) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_single]
  fin_cases j <;> decide

section SpecializedQuotient

variable {S : Type} [CommRing S] (g : Coeff →+* S)

def curveQuotient : Poly S →+* CurveRing g := Ideal.Quotient.mk _
def curveCoordinate (j : Fin 5) : CurveRing g := curveQuotient g (X j)
def curveMatrix : Matrix (Fin 3) (Fin 3) (CurveRing g) :=
  fun i j => curveQuotient g (map g (familyMatrix i j))
def entryIdeal : Ideal (CurveRing g) :=
  Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => curveMatrix g ij.1 ij.2))

theorem quotient_h : curveQuotient g (map g familyH)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [equationsIdeal]))

theorem quotient_F : curveQuotient g (map g familyF)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [equationsIdeal]))

theorem generator_quotient_mem (t : Fin 11) :
    curveQuotient g (map g (universalGenerators t))∈entryIdeal g := by
  have hm (i j : Fin 3) : curveMatrix g i j∈entryIdeal g :=
    Ideal.subset_span (Set.mem_range_self (i,j))
  fin_cases t
  · exact hm 0 0
  · exact hm 0 1
  · exact hm 0 2
  · exact hm 1 0
  · exact hm 1 1
  · exact hm 1 2
  · exact hm 2 0
  · exact hm 2 1
  · exact hm 2 2
  · change curveQuotient g (map g familyH)∈_
    rw [quotient_h]
    exact Ideal.zero_mem _
  · change curveQuotient g (map g familyF)∈_
    rw [quotient_F]
    exact Ideal.zero_mem _

theorem specialized_coordinate_power_mem (hs : IsUnit (g basepointPolynomial)) (j : Fin 5) :
    curveCoordinate g j^coordinatePower j∈entryIdeal g := by
  have hle : generatorIdeal (fun t => map g (universalGenerators t))≤
      (entryIdeal g).comap (curveQuotient g) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨t,rfl⟩
    exact generator_quotient_mem g t
  have h := hle (specialized_homogeneous_mem g hs _ (coordinate_power_homogeneous (S:=S) j))
  change curveQuotient g ((X j : Poly S)^coordinatePower j)∈entryIdeal g at h
  simpa only [map_pow,curveCoordinate] using h

theorem specialized_prime_pivot_cover (hs : IsUnit (g basepointPolynomial))
    (P : Ideal (CurveRing g)) [P.IsPrime]
    (hx : ∃j,curveCoordinate g j∉P) : ∃i j,curveMatrix g i j∉P := by
  classical
  by_contra! hzero
  have hle : entryIdeal g≤P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨ij,rfl⟩
    exact hzero ij.1 ij.2
  obtain ⟨j,hj⟩ := hx
  exact hj ((inferInstance : P.IsPrime).mem_of_pow_mem _
    (hle (specialized_coordinate_power_mem g hs j)))

theorem entries_generate_if_coordinate_unit (hs : IsUnit (g basepointPolynomial))
    {T : Type*} [CommRing T] (φ : CurveRing g →+* T) (j : Fin 5)
    (hu : IsUnit (φ (curveCoordinate g j))) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => φ (curveMatrix g ij.1 ij.2)))=⊤ := by
  have hm := Ideal.mem_map_of_mem φ (specialized_coordinate_power_mem g hs j)
  have hunit : IsUnit (φ (curveCoordinate g j^coordinatePower j)) := by
    rw [map_pow]
    exact hu.pow _
  have ht := Ideal.eq_top_of_isUnit_mem _ hm hunit
  simpa only [entryIdeal,Ideal.map_span,←Set.range_comp,Function.comp_def] using ht

end SpecializedQuotient

end CycleQ2IncidenceBasepointOpen

#print axioms CycleQ2IncidenceBasepointOpen.seed_basepointPolynomial
#print axioms CycleQ2IncidenceBasepointOpen.specialized_prime_pivot_cover
#print axioms CycleQ2IncidenceBasepointOpen.entries_generate_if_coordinate_unit
end
end

/- Component: continuation_3/IncidenceBasepointChart.lean -/
section
/-! The actual two-leading-coefficient incidence chart intersected with the
proved basepoint-free polynomial open. The literal seed remains a point of
this localization, and every relevant prime of its moving (h,F) quotient
has a nonzero matrix pivot. -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceBasepointChart

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceBasepointOpen
open CycleQ2SegreComplexBasepoint (coordinatePower)

def chartDenominator : Coeff := leadingProduct ℂ*basepointPolynomial

theorem chartDenominator_ne_zero : chartDenominator≠0 :=
  mul_ne_zero (leadingProduct_ne_zero ℂ) basepointPolynomial_ne_zero

abbrev OpenCoefficients := Localization.Away chartDenominator

instance : IsDomain OpenCoefficients :=
  Localization.Away.isDomain chartDenominator_ne_zero

def coefficientMap : Coeff →+* OpenCoefficients := algebraMap _ _

theorem denominator_isUnit : IsUnit (coefficientMap chartDenominator) :=
  IsLocalization.Away.algebraMap_isUnit chartDenominator

theorem basepoint_isUnit : IsUnit (coefficientMap basepointPolynomial) := by
  apply isUnit_of_mul_isUnit_right
  simpa only [chartDenominator,map_mul] using denominator_isUnit

theorem leading_coefficients_units :
    IsUnit (coefficientMap (rawCubicCoefficient fullCubicLeadingIndex)) ∧
      IsUnit (coefficientMap (rawSexticCoefficient fullSexticLeadingIndex)) := by
  have hlead : IsUnit (coefficientMap (leadingProduct ℂ)) := by
    apply isUnit_of_mul_isUnit_left
    simpa only [chartDenominator,map_mul] using denominator_isUnit
  have hpair : IsUnit (coefficientMap (rawCubicCoefficient fullCubicLeadingIndex)*
      coefficientMap (rawSexticCoefficient fullSexticLeadingIndex)) := by
    simpa only [leadingProduct,rawCubicCoefficient,rawSexticCoefficient,map_mul] using hlead
  exact ⟨isUnit_of_mul_isUnit_left hpair,isUnit_of_mul_isUnit_right hpair⟩

theorem seed_leadingProduct : seedEvaluation (leadingProduct ℂ)=1 := by
  change polynomialSpecialization (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (fun _ _ _ => 0) (leadingProduct ℂ)=1
  rw [polynomialSpecialization_leadingProduct]
  simp only [seedCubicCoefficients,seedSexticCoefficients,fullCubicLeadingIndex_exponent,
    fullSexticLeadingIndex_exponent,smoothH_leading_coefficient,smoothF_leading_coefficient,one_mul]

theorem seed_denominator : seedEvaluation chartDenominator=1 := by
  rw [chartDenominator,map_mul,seed_leadingProduct,seed_basepointPolynomial,one_mul]

def seedChart : OpenCoefficients →+* ℂ :=
  IsLocalization.Away.lift chartDenominator
    (show IsUnit (seedEvaluation chartDenominator) by rw [seed_denominator]; exact isUnit_one)

theorem seedChart_coefficientMap (p : Coeff) : seedChart (coefficientMap p)=seedEvaluation p :=
  IsLocalization.Away.lift_eq chartDenominator _ p

theorem universal_coordinate_power_mem (j : Fin 5) :
    curveCoordinate coefficientMap j^coordinatePower j∈entryIdeal coefficientMap :=
  specialized_coordinate_power_mem coefficientMap basepoint_isUnit j

theorem universal_prime_pivot_cover (P : Ideal (CurveRing coefficientMap)) [P.IsPrime]
    (hx : ∃j,curveCoordinate coefficientMap j∉P) :
    ∃i j,curveMatrix coefficientMap i j∉P :=
  specialized_prime_pivot_cover coefficientMap basepoint_isUnit P hx

theorem universal_entries_generate_if_coordinate_unit {T : Type*} [CommRing T]
    (φ : CurveRing coefficientMap →+* T) (j : Fin 5)
    (hu : IsUnit (φ (curveCoordinate coefficientMap j))) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => φ (curveMatrix coefficientMap ij.1 ij.2)))=⊤ :=
  entries_generate_if_coordinate_unit coefficientMap basepoint_isUnit φ j hu

end CycleQ2IncidenceBasepointChart

#print axioms CycleQ2IncidenceBasepointChart.seed_denominator
#print axioms CycleQ2IncidenceBasepointChart.universal_prime_pivot_cover
end
end
