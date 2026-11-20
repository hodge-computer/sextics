import Proposal.SegreModularBinding

/-!
# Specializing the seed Čech coefficients

The incidence arithmetic and the specialized Čech fractions and columns.
-/

set_option Elab.async false

/- Component: continuation_3/CurveCechTwoOpen.lean -/
section
/-! # Exact Laurent calculations for the actual six curve summands -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveCechTwoOpen

open CycleQ2CurveRestriction CycleQ2CurveQuotientFiniteFree

variable {R : Type*} [CommRing R]

abbrev LaurentExponent := Fin 2 → ℤ
abbrev Laurent := AddMonoidAlgebra R LaurentExponent

def HasPoles (t : Finset (Fin 2)) (p : Laurent (R:=R)) : Prop :=
  ∀ e i, i∉t → e i<0 → p.coeff e=0

def shiftedDegree {s : Side} (ab : ShiftIndex s) (e : LaurentExponent) : ℤ :=
  ab.1.val+ab.2.val+e 0+e 1

def HasDegree {s : Side} (ab : ShiftIndex s) (d : ℤ) (p : Laurent (R:=R)) : Prop :=
  ∀ e, shiftedDegree ab e≠d → p.coeff e=0

def nonnegativePart (p : Laurent (R:=R)) : Laurent (R:=R) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.filter (fun e => 0≤e 0))

@[simp] theorem nonnegativePart_apply (p : Laurent (R:=R)) (e : LaurentExponent) :
    (nonnegativePart p).coeff e=if 0≤e 0 then p.coeff e else 0 := rfl

theorem degree_nonnegativePart {s : Side} (ab : ShiftIndex s) (d : ℤ)
    {p : Laurent (R:=R)} (hp : HasDegree ab d p) : HasDegree ab d (nonnegativePart p) := by
  intro e he
  simp only [nonnegativePart_apply]
  split <;> simp [hp e he]

theorem degree_sub {s : Side} (ab : ShiftIndex s) (d : ℤ)
    {p q : Laurent (R:=R)} (hp : HasDegree ab d p) (hq : HasDegree ab d q) :
    HasDegree ab d (p-q) := by
  intro e he
  simp [AddMonoidAlgebra.coeff_sub,hp e he,hq e he]

/-- Every overlap section of total degree at least two is a boundary.
The largest of the actual six basis shifts is three. -/
theorem twoOpen_exact {s : Side} (ab : ShiftIndex s) (d : ℤ) (hd : 2≤d)
    (p : Laurent (R:=R)) (hp : HasDegree ab d p) :
    HasPoles {0} (nonnegativePart p-p) ∧ HasPoles {1} (nonnegativePart p) ∧
    HasDegree ab d (nonnegativePart p-p) ∧ HasDegree ab d (nonnegativePart p) ∧
    p=nonnegativePart p-(nonnegativePart p-p) := by
  have hb := basis_degree_bound s ab
  have hb' : (ab.1.val:ℤ)+ab.2.val≤3 := by exact_mod_cast hb
  have hn := degree_nonnegativePart ab d hp
  refine ⟨?_,?_,degree_sub ab d hn hp,hn,by abel⟩
  · intro e i hi hneg
    fin_cases i
    · simp at hi
    · by_cases h0 : 0≤e 0
      · simp [AddMonoidAlgebra.coeff_sub,h0]
      · have he : shiftedDegree ab e≠d := by
          dsimp [shiftedDegree]
          change e 1<0 at hneg
          omega
        simp [AddMonoidAlgebra.coeff_sub,h0,hp e he]
  · intro e i hi hneg
    fin_cases i
    · change e 0<0 at hneg
      simp [not_le.mpr hneg]
    · simp at hi

theorem sixSummand_exact (s : Side) (d : ℤ) (hd : 2≤d)
    (p : ShiftIndex s → Laurent (R:=R)) (hp : ∀ ab, HasDegree ab d (p ab)) :
    ∃ q0 q1 : ShiftIndex s → Laurent (R:=R),
      (∀ ab,HasPoles {0} (q0 ab)) ∧ (∀ ab,HasPoles {1} (q1 ab)) ∧
      (∀ ab,HasDegree ab d (q0 ab)) ∧ (∀ ab,HasDegree ab d (q1 ab)) ∧ p=q1-q0 := by
  refine ⟨fun ab => nonnegativePart (p ab)-p ab,fun ab => nonnegativePart (p ab),
    fun ab => (twoOpen_exact ab d hd (p ab) (hp ab)).1,
    fun ab => (twoOpen_exact ab d hd (p ab) (hp ab)).2.1,
    fun ab => (twoOpen_exact ab d hd (p ab) (hp ab)).2.2.1,
    fun ab => (twoOpen_exact ab d hd (p ab) (hp ab)).2.2.2.1,?_⟩
  funext ab
  exact (twoOpen_exact ab d hd (p ab) (hp ab)).2.2.2.2

/-- Compatible singleton sections have no poles. -/
theorem twoOpen_gluing (p0 p1 : Laurent (R:=R))
    (h0 : HasPoles {0} p0) (h1 : HasPoles {1} p1) (he : p0=p1) :
    HasPoles ∅ p0 := by
  intro e i hi hneg
  fin_cases i
  · rw [he]
    exact h1 e 0 (by decide) hneg
  · exact h0 e 1 (by decide) hneg

end CycleQ2CurveCechTwoOpen

#print axioms CycleQ2CurveCechTwoOpen.sixSummand_exact
end
end

/- Component: continuation_3/GenericEntryCoefficientBinding.lean -/
section
/-! # Coefficient and quotient ranks of the actual cofactor differential over any field -/

noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2GenericEntryCoefficientBinding

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder CycleQ2IncidenceJacobian
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceJacobianNaturality
  CycleQ2IncidenceCoefficientRelations CycleQ2SegreTangentLocal CycleQ2CurveRestriction

variable {K : Type*} [Field K] (r ι : K)

abbrev Input14 := Matrix (Fin 3) (Fin 3) (SeedPiece r ι 14 0)

instance input14_finite : Module.Finite K (Input14 r ι) := by
  letI : Module.Finite K (SeedPiece r ι 14 0) :=
    Module.Finite.of_basis (seedPieceBasis r ι 14 0 (by decide))
  infer_instance

def inputToGlobal : Input14 r ι →ₗ[K] Matrix (Fin 3) (Fin 3) (SeedRing r ι) where
  toFun N i j := (N i j).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def entryDifferential : Input14 r ι →ₗ[K] Matrix (Fin 3) (Fin 3) (SeedRing r ι) :=
  ((cofactorDifferentialLinear (seedQuotientMatrix r ι)).restrictScalars K).comp (inputToGlobal r ι)

def nf : Poly K →ₗ[K] Poly K :=
  fullRemainderLinear (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)

theorem nf_standard (p : Poly K) : FullStandard ((nf r ι) p) :=
  (fullRemainder_spec (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p).1

theorem nf_grade (d : ℕ) (p : Poly K) (hp : HG p (d,0)) : HG ((nf r ι) p) (d,0) :=
  fullRemainder_preserves_grading (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (seedCubicCoefficients_unit ι)
    (seedSexticCoefficients_unit r ι) hp

theorem nf_quotient (p : Poly K) :
    Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) ((nf r ι) p)=
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p := by
  apply Ideal.Quotient.eq.mpr
  change fullRemainder (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (seedCubicCoefficients_unit ι)
    (seedSexticCoefficients_unit r ι) p-p∈_
  have h := sub_fullRemainder_mem (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (seedCubicCoefficients_unit ι)
    (seedSexticCoefficients_unit r ι) p
  rw [seedCubicCoefficients_polynomial,seedSexticCoefficients_polynomial] at h
  simpa only [neg_sub] using (equationsIdeal (smoothH ι)
    (smoothF r ι)).neg_mem h

theorem nf_zero_iff (p : Poly K) : (nf r ι) p=0 ↔
    Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p=0 := by
  change fullRemainder (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (seedCubicCoefficients_unit ι)
    (seedSexticCoefficients_unit r ι) p=0 ↔ _
  rw [fullRemainder_eq_zero_iff,seedCubicCoefficients_polynomial,
    seedSexticCoefficients_polynomial,Ideal.Quotient.eq_zero_iff_mem]

def expansion (d : ℕ) (v : StandardIndex d → K) : Poly K :=
  ∑ e, v e • monomial (standardExponent e) 1

theorem expansion_grade (d : ℕ) (v : StandardIndex d → K) : HG (expansion d v) (d,0) := by
  apply (weightedHomogeneousSubmodule K fullGrading (d,0)).sum_mem
  intro e _
  exact (weightedHomogeneousSubmodule K fullGrading (d,0)).smul_mem (v e)
    (isWeightedHomogeneous_monomial fullGrading (standardExponent e) (1:K) (standardExponent_grade e))

theorem expansion_coefficients (d : ℕ) (p : Poly K) (hs : FullStandard p) (hg : HG p (d,0)) :
    expansion d (fun e => p.coeff (standardExponent e))=p :=
  standardExpansion_eq d p hs hg

abbrev PolynomialMatrices := Matrix (Fin 3) (Fin 3) (Poly K)

def rawInput : (MatrixParameter → K) →ₗ[K] (PolynomialMatrices (K:=K)) where
  toFun v i j := expansion 14 (fun e => v ((i,j),e))
  map_add' v w := by
    funext i j
    simp [expansion,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c v := by
    funext i j
    simp [expansion,Pi.smul_apply,Finset.smul_sum,smul_smul]

theorem rawInput_eq_perturbation (v : MatrixParameter → K) :
    rawInput v=perturbation (fun i j e => v ((i,j),e)) := by
  funext i j
  simp only [rawInput,LinearMap.coe_mk,AddHom.coe_mk,expansion,perturbation,
    smul_monomial,smul_eq_mul,mul_one]

def decodeInput : (MatrixParameter → K) →ₗ[K] (Input14 r ι) where
  toFun v i j := ⟨Ideal.Quotient.mk
      (equationsIdeal (smoothH ι) (smoothF r ι)) (rawInput v i j),
    Submodule.mem_map.mpr ⟨_,expansion_grade _ _,rfl⟩⟩
  map_add' v w := by
    funext i j
    apply Subtype.ext
    change Ideal.Quotient.mk _ (rawInput (v+w) i j)=_
    rw [map_add]
    exact map_add _ _ _
  map_smul' c v := by
    funext i j
    apply Subtype.ext
    change Ideal.Quotient.mk _ (rawInput (c • v) i j)=_
    rw [map_smul]
    exact map_smul (Ideal.Quotient.mkₐ K (equationsIdeal (smoothH ι)
      (smoothF r ι))).toLinearMap c _

theorem decodeInput_surjective : Function.Surjective (decodeInput r ι) := by
  intro N
  choose P hP hPN using fun i j => Submodule.mem_map.mp (N i j).property
  let v : MatrixParameter → K := fun ie => ((nf r ι) (P ie.1.1 ie.1.2)).coeff (standardExponent ie.2)
  refine ⟨v,?_⟩
  funext i j
  apply Subtype.ext
  change Ideal.Quotient.mk _ (expansion 14
    (fun e => ((nf r ι) (P i j)).coeff (standardExponent e)))=(N i j).val
  rw [expansion_coefficients 14 _ ((nf_standard r ι) _) ((nf_grade r ι) _ _ (hP i j)),(nf_quotient r ι)]
  exact hPN i j

def rawDifferential : (MatrixParameter → K) →ₗ[K] (PolynomialMatrices (K:=K)) :=
  ((cofactorDifferentialLinear (rawSeedMatrix r)).restrictScalars K).comp rawInput

def extractCoefficients : (PolynomialMatrices (K:=K)) →ₗ[K] (EquationIndex → K) where
  toFun P q := ((nf r ι) (P q.1.1 q.1.2)).coeff (standardExponent q.2)
  map_add' P Q := by
    funext q
    simp only [Matrix.add_apply,map_add,coeff_add,Pi.add_apply]
  map_smul' c P := by
    funext q
    simp only [Matrix.smul_apply,map_smul,coeff_smul,Pi.smul_apply,RingHom.id_apply]

def entryCoefficients : (MatrixParameter → K) →ₗ[K] (EquationIndex → K) :=
  (extractCoefficients r ι).comp (rawDifferential r)

theorem entryCoefficients_apply (v : MatrixParameter → K) (q : EquationIndex) :
    (entryCoefficients r ι) v q=((nf r ι) (cofactorDifferential (rawSeedMatrix r)
      (rawInput v) q.1.1 q.1.2)).coeff (standardExponent q.2) := rfl

theorem entryCoefficients_eq_linearized (v : MatrixParameter → K) (q : EquationIndex) :
    (entryCoefficients r ι) v q=linearizedEquations r ι
      (fun _ => 0) (fun _ => 0) (fun i j e => v ((i,j),e)) q := by
  rw [(entryCoefficients_apply r ι),rawInput_eq_perturbation]
  simp only [linearizedEquations,fullInvariantPolynomial,monomial_zero,Finset.sum_const_zero,
    fullFirstOrderResidual,firstOrderResidual,zero_mul,add_zero,sub_zero]
  rfl

/-- Exactly the 2151 columns belonging to the matrix-entry parameters in
 the existing universal incidence Jacobian. -/
def entryJacobianBlock : Matrix EquationIndex MatrixParameter K :=
  fun q j => linearizedMatrix r ι q (Sum.inr (Sum.inr j))

theorem entryCoefficients_matrix : LinearMap.toMatrix' (entryCoefficients r ι)=(entryJacobianBlock r ι) := by
  classical
  ext q j
  rw [LinearMap.toMatrix'_apply,(entryCoefficients_eq_linearized r ι)]
  unfold entryJacobianBlock linearizedMatrix
  congr 1 <;> simp [funext_iff,Pi.single_apply,eq_comm]

theorem entryJacobianBlock_map : Matrix.mulVecLin (entryJacobianBlock r ι)=(entryCoefficients r ι) := by
  rw [←(entryCoefficients_matrix r ι)]
  exact Matrix.toLin'_toMatrix' (entryCoefficients r ι)

theorem rawDifferential_grade (v : MatrixParameter → K) (i j : Fin 3) :
    HG ((rawDifferential r) v i j) (28,0) := by
  have hm := rawSeedMatrix_homogeneous r
  have hn : ∀ i j,HG (rawInput v i j) (14,0) := fun i j => expansion_grade _ _
  exact ((cofactors_homogeneous _ (fun i j => (hm i j).add (hn i j)) i j).sub
    (cofactors_homogeneous _ hm i j)).sub (cofactors_homogeneous _ hn i j)

theorem entryDifferential_decode (v : MatrixParameter → K) (i j : Fin 3) :
    (entryDifferential r ι) ((decodeInput r ι) v) i j=Ideal.Quotient.mk
      (equationsIdeal (smoothH ι) (smoothF r ι))
      ((rawDifferential r) v i j) := by
  have h := CycleQ2SegreTangentLocal.map_cofactorDifferential
    (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))
    (rawSeedMatrix r) (rawInput v)
  exact (congrArg (fun P : Matrix (Fin 3) (Fin 3) (SeedRing r ι) => P i j) h).symm

theorem entryCoefficients_zero_iff (v : MatrixParameter → K) :
    (entryCoefficients r ι) v=0 ↔ (entryDifferential r ι) ((decodeInput r ι) v)=0 := by
  constructor
  · intro h
    funext i j
    rw [(entryDifferential_decode r ι)]
    apply ((nf_zero_iff r ι) _).mp
    apply standard_eq_zero_of_coefficients ((nf_standard r ι) _)
      ((nf_grade r ι) _ _ ((rawDifferential_grade r) v i j))
    intro e
    exact congrFun h ((i,j),e)
  · intro h
    funext q
    have hz : (nf r ι) ((rawDifferential r) v q.1.1 q.1.2)=0 := by
      apply ((nf_zero_iff r ι) _).mpr
      rw [←(entryDifferential_decode r ι),h]
      rfl
    change ((nf r ι) ((rawDifferential r) v q.1.1 q.1.2)).coeff (standardExponent q.2)=0
    rw [hz,coeff_zero]

theorem entryCoefficients_kernel : LinearMap.ker (entryCoefficients r ι)=
    LinearMap.ker ((entryDifferential r ι).comp (decodeInput r ι)) := by
  ext v
  exact (entryCoefficients_zero_iff r ι) v

theorem entryDifferential_comp_range : LinearMap.range ((entryDifferential r ι).comp (decodeInput r ι))=
    LinearMap.range (entryDifferential r ι) := by
  ext y
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨(decodeInput r ι) v,rfl⟩
  · rintro ⟨N,rfl⟩
    obtain ⟨v,rfl⟩ := (decodeInput_surjective r ι) N
    exact ⟨v,rfl⟩

/-- No abstract dimension model: the rank is that of the literal original
9522-by-2151 matrix-entry block of the incidence Jacobian. -/
theorem entryJacobianBlock_rank_eq :
    Module.finrank K (LinearMap.range (Matrix.mulVecLin (entryJacobianBlock r ι)))=
      Module.finrank K (LinearMap.range (entryDifferential r ι)) := by
  rw [(entryJacobianBlock_map r ι)]
  have h1 := (entryCoefficients r ι).finrank_range_add_finrank_ker
  have h2 := ((entryDifferential r ι).comp (decodeInput r ι)).finrank_range_add_finrank_ker
  rw [(entryCoefficients_kernel r ι)] at h1
  rw [(entryDifferential_comp_range r ι)] at h2
  omega

/-- A standard representative is uniquely determined by its actual seed quotient class. -/
theorem nf_eq_of_standard_and_quotient {p q : Poly K}
    (hq : FullStandard q)
    (heq : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p =
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) q) :
    nf r ι p = q := by
  obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp (Ideal.Quotient.eq.mp heq)
  symm
  apply (existsUnique_full_invariant_representative
    (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p).choose_spec.2
  refine ⟨hq,a,b,?_⟩
  rw [seedCubicCoefficients_polynomial,seedSexticCoefficients_polynomial]
  rw [hab]
  ring

end CycleQ2GenericEntryCoefficientBinding

#print axioms CycleQ2GenericEntryCoefficientBinding.entryCoefficients_matrix
#print axioms CycleQ2GenericEntryCoefficientBinding.entryJacobianBlock_rank_eq
end
end

/- Component: continuation_3/IncidenceGaussianArithmetic.lean -/
section
/-!
# Arithmetic specialization of the literal incidence matrices

At r=57 and i=√(-1), the actual first-order matrix and the actual moving
coefficient-relation matrix are defined over the Gaussian integers.
Their reductions send i to33 modulo109, and their characteristic-zero
specializations send i to Complex.I. A proved nonzero modular minor of
either matrix therefore gives the corresponding complex minor.

This proves the transfer implication, not the numerical minor premise.
In particular it does not lift an arbitrary modular kernel vector.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CycleQ2IncidenceGaussianArithmetic

open Matrix CycleQ2IncidenceJacobianNaturality CycleQ2IncidenceEquations
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidenceUniversalChart

abbrev F109 := ZMod 109

instance : Fact (Nat.Prime 109) := ⟨by decide⟩
instance : Fact (1 < (109 : ℕ)) := ⟨by decide⟩

def gaussianI : GaussianInt := Zsqrtd.sqrtd

def reduction : GaussianInt →+* F109 := Zsqrtd.lift ⟨33, by decide⟩

@[simp] theorem reduction_I : reduction gaussianI = 33 := by
  simp [reduction, gaussianI, Zsqrtd.lift_apply_apply]

@[simp] theorem complex_I : GaussianInt.toComplex gaussianI = Complex.I := by
  simp [GaussianInt.toComplex, gaussianI, Zsqrtd.lift_apply_apply]

def integralJacobian : Matrix EquationIndex ParameterIndex GaussianInt :=
  linearizedMatrix 57 gaussianI

def integralRelations : Matrix RelationIndex ColumnIndex GaussianInt :=
  seedCoefficientRelations 57 gaussianI

theorem integralJacobian_modular :
    integralJacobian.map reduction = linearizedMatrix (57 : F109) 33 := by
  rw [integralJacobian, linearizedMatrix_map, reduction_I, map_ofNat]

theorem integralJacobian_complex :
    integralJacobian.map GaussianInt.toComplex = linearizedMatrix (57 : ℂ) Complex.I := by
  rw [integralJacobian, linearizedMatrix_map, complex_I, map_ofNat]

theorem integralRelations_modular :
    integralRelations.map reduction = seedCoefficientRelations (57 : F109) 33 := by
  rw [integralRelations, seedCoefficientRelations_map, reduction_I, map_ofNat]

theorem integralRelations_complex :
    integralRelations.map GaussianInt.toComplex = seedCoefficientRelations (57 : ℂ) Complex.I := by
  rw [integralRelations, seedCoefficientRelations_map, complex_I, map_ofNat]

theorem determinant_nonzero_of_reduction {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n GaussianInt) (hmod : (A.map reduction).det ≠ 0) :
    (A.map GaussianInt.toComplex).det ≠ 0 := by
  have hA : A.det ≠ 0 := by
    intro hz
    apply hmod
    change (reduction.mapMatrix A).det = 0
    rw [← reduction.map_det, hz, map_zero]
  intro hz
  apply hA
  apply GaussianInt.toComplex_injective
  rw [GaussianInt.toComplex.map_det, map_zero]
  exact hz

/-- Any actually verified modular Jacobian minor transfers to the literal
complex first-order incidence matrix at the Gaussian integral seed. -/
theorem jacobian_minor_nonzero {n : Type*} [Fintype n] [DecidableEq n]
    (rows : n → EquationIndex) (columns : n → ParameterIndex)
    (hmod : ((linearizedMatrix (57 : F109) 33).submatrix rows columns).det ≠ 0) :
    ((linearizedMatrix (57 : ℂ) Complex.I).submatrix rows columns).det ≠ 0 := by
  have h : ((integralJacobian.submatrix rows columns).map reduction).det ≠ 0 := by
    change ((integralJacobian.map reduction).submatrix rows columns).det ≠ 0
    rwa [integralJacobian_modular]
  have hc := determinant_nonzero_of_reduction (integralJacobian.submatrix rows columns) h
  change ((integralJacobian.map GaussianInt.toComplex).submatrix rows columns).det ≠ 0 at hc
  rwa [integralJacobian_complex] at hc

/-- The same transfer applies to a complementary block of the genuine
coefficient relations, rather than to an unrelated seed evaluation. -/
theorem relation_minor_nonzero {n : Type*} [Fintype n] [DecidableEq n]
    (rows : n → RelationIndex) (columns : n → ColumnIndex)
    (hmod : ((seedCoefficientRelations (57 : F109) 33).submatrix rows columns).det ≠ 0) :
    ((seedCoefficientRelations (57 : ℂ) Complex.I).submatrix rows columns).det ≠ 0 := by
  have h : ((integralRelations.submatrix rows columns).map reduction).det ≠ 0 := by
    change ((integralRelations.map reduction).submatrix rows columns).det ≠ 0
    rwa [integralRelations_modular]
  have hc := determinant_nonzero_of_reduction (integralRelations.submatrix rows columns) h
  change ((integralRelations.map GaussianInt.toComplex).submatrix rows columns).det ≠ 0 at hc
  rwa [integralRelations_complex] at hc

end CycleQ2IncidenceGaussianArithmetic

#print axioms CycleQ2IncidenceGaussianArithmetic.integralJacobian_modular
#print axioms CycleQ2IncidenceGaussianArithmetic.integralRelations_modular
#print axioms CycleQ2IncidenceGaussianArithmetic.jacobian_minor_nonzero
#print axioms CycleQ2IncidenceGaussianArithmetic.relation_minor_nonzero
end
end

/- Component: continuation_3/cylinder_bridge/IncidencePolynomialJacobianBinding.lean -/
section
/-! # The actual cleared-polynomial Jacobian is the literal incidence matrix

Evaluation at a single-coordinate dual-number point differentiates the actual
common-denominator polynomial presentation.  The already proved square-zero
incidence identity computes the same coefficient using the literal cofactor
linearization.  The leading product has constant coefficient one, so clearing
denominators does not change the seed Jacobian.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace CycleQ2IncidencePolynomialJacobianBinding

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder CycleQ2IncidenceJacobian
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialRelations CycleQ2IncidenceJacobianNaturality
open CycleQ2PolynomialDualEvaluation (Dual)

variable {R : Type*} [CommRing R] [IsDomain R]

def cubicDirection (R : Type*) [CommRing R] (j : ParameterIndex) : FullInvariantIndex 3 → R := by
  classical
  exact fun e => if j=Sum.inl e then 1 else 0
def sexticDirection (R : Type*) [CommRing R] (j : ParameterIndex) : FullInvariantIndex 6 → R := by
  classical
  exact fun e => if j=Sum.inr (Sum.inl e) then 1 else 0
def matrixDirection (R : Type*) [CommRing R] (j : ParameterIndex) :
    Fin 3 → Fin 3 → StandardIndex 14 → R := by
  classical
  exact fun i k e => if j=Sum.inr (Sum.inr ((i,k),e)) then 1 else 0

def epsilon (R : Type*) [CommRing R] : Dual R := TrivSqZeroExt.inr 1

theorem epsilon_sq (R : Type*) [CommRing R] : epsilon R^2=0 := by
  simp [epsilon,pow_two]

def dualCubic (r ι : R) (j : ParameterIndex) : FullInvariantIndex 3 → Dual R :=
  deformedCubicCoefficients (TrivSqZeroExt.inl ι) (epsilon R) (cubicDirection (Dual R) j)
def dualSextic (r ι : R) (j : ParameterIndex) : FullInvariantIndex 6 → Dual R :=
  deformedSexticCoefficients (TrivSqZeroExt.inl r) (TrivSqZeroExt.inl ι)
    (epsilon R) (sexticDirection (Dual R) j)
def dualMatrix (j : ParameterIndex) : Fin 3 → Fin 3 → StandardIndex 14 → Dual R :=
  fun i k e => epsilon R*matrixDirection (Dual R) j i k e


theorem dualCoefficientPoint (r ι : R) (j : ParameterIndex) :
    coefficientPoint (dualCubic r ι j) (dualSextic r ι j) (dualMatrix (R := R) j)=
      CycleQ2PolynomialDualEvaluation.point (seedPoint r ι) j := by
  classical
  have hc (e : FullInvariantIndex 3) : seedCubicCoefficients (TrivSqZeroExt.inl ι : Dual R) e=
      (TrivSqZeroExt.inl (seedCubicCoefficients ι e) : Dual R) := by
    exact (congrFun (map_seedCubicCoefficients (TrivSqZeroExt.inlHom R R) ι) e).symm
  have hF (e : FullInvariantIndex 6) :
      seedSexticCoefficients (TrivSqZeroExt.inl r : Dual R) (TrivSqZeroExt.inl ι) e=
        (TrivSqZeroExt.inl (seedSexticCoefficients r ι e) : Dual R) := by
    exact (congrFun (map_seedSexticCoefficients (TrivSqZeroExt.inlHom R R) r ι) e).symm
  funext k
  rcases k with e | e | ⟨⟨i,k⟩,e⟩
  · simp only [coefficientPoint, Sum.elim_inl, dualCubic, deformedCubicCoefficients, hc,
      cubicDirection, CycleQ2PolynomialDualEvaluation.point, seedPoint]
    split_ifs <;> apply TrivSqZeroExt.ext <;> simp [epsilon]
  · simp only [coefficientPoint, Sum.elim_inr, Sum.elim_inl, dualSextic,
      deformedSexticCoefficients, hF, sexticDirection,
      CycleQ2PolynomialDualEvaluation.point, seedPoint]
    split_ifs <;> apply TrivSqZeroExt.ext <;> simp [epsilon]
  · simp only [coefficientPoint, Sum.elim_inr, dualMatrix, matrixDirection,
      CycleQ2PolynomialDualEvaluation.point, seedPoint]
    split_ifs <;> apply TrivSqZeroExt.ext <;> simp [epsilon]

theorem dualCubic_unit (r ι : R) (j : ParameterIndex) :
    IsUnit (dualCubic r ι j fullCubicLeadingIndex) :=
  deformedCubicCoefficients_unit _ _ _ (epsilon_sq R)

theorem dualSextic_unit (r ι : R) (j : ParameterIndex) :
    IsUnit (dualSextic r ι j fullSexticLeadingIndex) :=
  deformedSexticCoefficients_unit _ _ _ _ (epsilon_sq R)

theorem dualLeading_fst (r ι : R) (j : ParameterIndex) :
    (dualCubic r ι j fullCubicLeadingIndex*dualSextic r ι j fullSexticLeadingIndex).fst=1 := by
  simp only [dualCubic, dualSextic, deformedCubicCoefficients, deformedSexticCoefficients,
    seedCubicCoefficients, seedSexticCoefficients, fullCubicLeadingIndex_exponent,
    fullSexticLeadingIndex_exponent, smoothH_leading_coefficient, smoothF_leading_coefficient]
  simp [epsilon]

theorem dualSpecialization_snd (r ι : R) (j : ParameterIndex) (p : ParameterPolynomial R) :
    (polynomialSpecialization (dualCubic r ι j) (dualSextic r ι j)
      (dualMatrix (R := R) j) p).snd=
      polynomialSpecialization (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
        (fun _ _ _ => 0) (pderiv j p) := by
  unfold polynomialSpecialization
  rw [dualCoefficientPoint, CycleQ2PolynomialDualEvaluation.eval_point_snd]
  rfl

theorem dualIncidence_eq (r ι : R) (j : ParameterIndex) (q : EquationIndex) :
    incidenceEquations (dualCubic r ι j) (dualSextic r ι j)
      (dualCubic_unit r ι j) (dualSextic_unit r ι j) (TrivSqZeroExt.inl r)
      (dualMatrix (R := R) j) q =
        epsilon R*linearizedMatrix (TrivSqZeroExt.inl r : Dual R) (TrivSqZeroExt.inl ι) q j := by
  exact infinitesimal_incidenceEquations_eq _ _ _ (epsilon_sq R) _ _ _ q

theorem dualLinearized_fst (r ι : R) (j : ParameterIndex) (q : EquationIndex) :
    (linearizedMatrix (TrivSqZeroExt.inl r : Dual R) (TrivSqZeroExt.inl ι) q j).fst=
      linearizedMatrix r ι q j := by
  have hh := congrArg (fun M : Matrix EquationIndex ParameterIndex R => M q j)
    (linearizedMatrix_map (TrivSqZeroExt.fstHom R R R).toRingHom
      (TrivSqZeroExt.inl r) (TrivSqZeroExt.inl ι))
  exact hh

/-- Entry-by-entry identification of the actual polynomial-system Jacobian
with the saved-matrix interface.  The only hypotheses are that the coefficient
ring is a domain; no rank, derivative comparison, or smoothness is assumed. -/
theorem seedJacobian_eq_linearizedMatrix (r ι : R) (q : ColumnIndex) (j : ParameterIndex) :
    seedJacobian R r ι q j=linearizedMatrix r ι (columnEquiv q) j := by
  have hh := equation_specialization (dualCubic r ι j) (dualSextic r ι j)
    (dualCubic_unit r ι j) (dualSextic_unit r ι j) (dualMatrix (R := R) j) r q
  change _ = _*incidenceEquations _ _ _ _ (TrivSqZeroExt.inl r) _ _ at hh
  rw [dualIncidence_eq] at hh
  have hs := congrArg TrivSqZeroExt.snd hh
  rw [dualSpecialization_snd] at hs
  change seedJacobian R r ι q j = _ at hs
  have hlead := dualLeading_fst r ι j
  rw [TrivSqZeroExt.fst_mul] at hlead
  simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow,
    epsilon, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
    smul_eq_mul, op_smul_eq_smul, zero_mul, zero_add, mul_zero, add_zero, one_mul, mul_one,
    hlead, one_pow, dualLinearized_fst] at hs
  exact hs

theorem seedJacobian_matrix (r ι : R) :
    seedJacobian R r ι=fun q j => linearizedMatrix r ι (columnEquiv q) j := by
  ext q j
  exact seedJacobian_eq_linearizedMatrix r ι q j

/-- The cleared relation matrix likewise has the actual coefficient-relation
matrix as its seed value.  Its clearing factor is one at this seed. -/
theorem seedRelationMatrix_eq_coefficientRelations (r ι : R) :
    seedRelationMatrix R r ι=seedCoefficientRelations r ι := by
  let φ : ParameterRing R →ₐ[R] R := seedSpecialization R r ι
  have hc : φ.toRingHom ∘ cubicCoefficient R=seedCubicCoefficients ι := by
    funext e
    exact specialization_cubicCoefficient _ _ _ _ _ e
  have hF : φ.toRingHom ∘ sexticCoefficient R=seedSexticCoefficients r ι := by
    funext e
    exact specialization_sexticCoefficient _ _ _ _ _ e
  have hδ : (fun i k e => φ.toRingHom (matrixCoefficient R i k e))=
      (fun _ _ _ => (0 : R)) := by
    funext i k e
    exact specialization_matrixCoefficient _ _ _ _ _ i k e
  have hr : φ.toRingHom (algebraMap R (ParameterRing R) r)=r := φ.commutes r
  have hm : (map φ.toRingHom).mapMatrix
      (incidenceMatrix (algebraMap R (ParameterRing R) r) (matrixCoefficient R))=rawSeedMatrix r := by
    rw [map_incidenceMatrix,hr,hδ,incidenceMatrix_zero]
  ext k q
  rw [seedRelationMatrix,seed_relation_value]
  have hh := coefficientRelations_map φ.toRingHom
    (cubicCoefficient R) (sexticCoefficient R) (leading_coefficients_units R).1
    (leading_coefficients_units R).2
    (incidenceMatrix (algebraMap R (ParameterRing R) r) (matrixCoefficient R)) k q
  simp only [hc,hF,hm] at hh
  simpa only [seedCoefficientRelations,universalRelations,φ,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using hh

/-- The relation-times-Jacobian identity now holds for both literal matrix
interfaces, including the fixed cofactor-column reindexing. -/
theorem actual_coefficientRelations_linearizedMatrix (r ι : R) :
    seedCoefficientRelations r ι*(show Matrix ColumnIndex ParameterIndex R from
      fun q j => linearizedMatrix r ι (columnEquiv q) j)=0 := by
  rw [← seedRelationMatrix_eq_coefficientRelations,← seedJacobian_matrix]
  exact seed_relations_jacobian R r ι

end CycleQ2IncidencePolynomialJacobianBinding

#print axioms CycleQ2IncidencePolynomialJacobianBinding.seedJacobian_eq_linearizedMatrix
#print axioms CycleQ2IncidencePolynomialJacobianBinding.seedRelationMatrix_eq_coefficientRelations
#print axioms CycleQ2IncidencePolynomialJacobianBinding.actual_coefficientRelations_linearizedMatrix
end
end

/- Component: continuation_3/SeedCechLocalization.lean -/
section
/-!
# Identifying the coordinate localizations with bounded Laurent sections

The map from the three-coordinate polynomial ring to Laurent polynomials is
injective. Its localization at any product of coordinate variables has image
exactly the Laurent polynomials whose poles occur only in those coordinates.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false


#print axioms CycleQ2SeedCechLocalization.mem_range_localizationToLaurent
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechThetaCancellation.lean -/
section
/-! The all-poles coboundary check for every h+θx₀³ curve. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
namespace CycleQ2SeedCechTheta
open MvPolynomial CycleQ2SeedTrace CycleQ2CechLinearCubic
open CycleQ2SeedCech (PS LS endpointX endpointY seriesMap uniformizerUnit scalar_endpoint_residue)

def laurentX0 (r θ : ℂ) (e : Bool) : LaurentChart r θ e :=
  x0 (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e)) (seriesMap (betaCoefficient r θ e))

def laurentX2 (r θ : ℂ) (e : Bool) : LaurentChart r θ e :=
  x2 (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e)) (seriesMap (betaCoefficient r θ e))

theorem laurentEval_monomial (r θ : ℂ) (e : Bool) (d : Exp) (z : ℂ) :
    laurentEval r θ e (monomial d z) =
      laurentBase r θ e (seriesMap (PowerSeries.C z)) * laurentX0 r θ e ^ d 0 *
        laurentBase r θ e (seriesMap (endpointX e)) ^ d 1 * laurentX2 r θ e ^ d 2 *
          laurentBase r θ e (seriesMap (endpointY e)) ^ d 3 := by
  rw [monomial_eq_C_mul_mon]
  simp [laurentEval, powerEval, mon, powerCoordinates, chartEmbedding,
    laurentBase, laurentX0, laurentX2, powerBase, powerX0, powerX2, Matrix.cons_val_succ, Fin.reduceSucc, mul_assoc]

theorem fraction_monomial_first_open (r θ : ℂ) (e : Bool) (d : Exp) (z : ℂ) (n : ℕ) :
    fraction r θ e (monomial d z) n 0 =
      laurentBase r θ e (seriesMap (PowerSeries.C z) *
        seriesMap (endpointX e) ^ d 1 * seriesMap (endpointY e) ^ d 3 *
          (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ n)) *
        laurentX0 r θ e ^ d 0 * laurentX2 r θ e ^ d 2 := by
  simp only [fraction, pow_zero, mul_one, laurentEval_monomial]
  simp only [chartAUnit, Units.coe_map_inv, Units.coe_map, ← map_pow,
    laurentBase, map_mul, map_pow, MonoidHom.coe_coe]
  ring

theorem first_open_monomial_coefficient (r θ : ℂ) (e : Bool) (d : Exp) (z : ℂ) (n : ℕ)
    (hd0 : d 0 < 2) (hd2 : d 2 < 3) :
    laurentCoefficient r θ e (fraction r θ e (monomial d z) n 0) =
      if d 0 = 1 ∧ d 2 = 2 then
        seriesMap (PowerSeries.C z) * seriesMap (endpointX e) ^ d 1 *
          seriesMap (endpointY e) ^ d 3 * (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ n)
      else 0 := by
  rw [fraction_monomial_first_open]
  exact coefficient_small_monomial _ _ _ _ _ _ _ _ hd0 hd2

theorem cechResidue_reduced_monomial (r θ : ℂ) (d : Exp) (z : ℂ) (n : ℕ)
    (hd0 : d 0 < 2) (hd2 : d 2 < 3)
    (hdegree : d 0 + d 1 + d 2 + d 3 = 2*n+1) :
    cechResidue r θ (monomial d z) n 0 = 0 := by
  change (laurentCoefficient r θ false (fraction r θ false (monomial d z) n 0)).coeff (-1) -
    (laurentCoefficient r θ true (fraction r θ true (monomial d z) n 0)).coeff (-1) = 0
  rw [first_open_monomial_coefficient _ _ _ _ _ _ hd0 hd2,
    first_open_monomial_coefficient _ _ _ _ _ _ hd0 hd2]
  by_cases he : d 0 = 1 ∧ d 2 = 2
  · rw [if_pos he, if_pos he, scalar_endpoint_residue, scalar_endpoint_residue]
    have hp : (d 3 : ℤ) - n = -1 ↔ (d 1 : ℤ) - n = -1 := by omega
    simp only [Bool.false_eq_true, if_false, if_true, hp, sub_self]
  · rw [if_neg he, if_neg he]
    simp

theorem cechResidue_sum (r θ : ℂ) {ι : Type*} (s : Finset ι) (p : ι → Poly) (n m : ℕ) :
    cechResidue r θ (∑ i ∈ s, p i) n m = ∑ i ∈ s, cechResidue r θ (p i) n m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cechResidue, fractionResidue, fraction]
  | @insert i s hi ih => simp [Finset.sum_insert hi, cechResidue_add, ih]

/-- The residues at the two endpoints cancel on every canonical-bundle
section over D₊(x₁x₃), with no bound on the denominator power. -/
theorem cechResidue_first_open (r θ : ℂ) (p : Poly) (n : ℕ)
    (hp : p.IsHomogeneous (2*n+1)) : cechResidue r θ p n 0 = 0 := by
  obtain ⟨q,hq,hqh,hpq⟩ := exists_homogeneous_curve_normal r θ p (2*n+1) hp
  have heq (e : Bool) : fraction r θ e p n 0 = fraction r θ e q n 0 := by
    have hh := fraction_zero_of_curveIdeal r θ e hpq n 0
    rwa [fraction_sub, sub_eq_zero] at hh
  have hceq : cechResidue r θ p n 0 = cechResidue r θ q n 0 := by
    simp only [cechResidue, fractionResidue, heq]
  rw [hceq]
  conv_lhs => rw [q.as_sum]
  rw [cechResidue_sum]
  apply Finset.sum_eq_zero
  intro d hd
  apply cechResidue_reduced_monomial r θ d (q.coeff d) n (hq d hd).1 (hq d hd).2
  have hh : d.degree = 2*n+1 := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hqh (mem_support_iff.mp hd)
  rw [Finsupp.degree_eq_sum] at hh
  simpa [Fin.sum_univ_succ, Matrix.cons_val_succ, Fin.reduceSucc, add_assoc] using hh

/-- The actual two-endpoint functional kills every Čech coboundary, including
ones requiring arbitrarily large denominator powers. -/
theorem cechResidue_zero_of_boundary (r θ : ℂ) (p : Poly) (n m : ℕ)
    (hboundary : CechBoundary r θ p n m) : cechResidue r θ p n m = 0 := by
  obtain ⟨N,M,q,s,hn,hm,hq,hs,hmem⟩ := hboundary
  have hfalse := fraction_of_boundary_witness r θ false p q s n m N M hn hm hmem
  have htrue := fraction_of_boundary_witness r θ true p q s n m N M hn hm hmem
  have heq : cechResidue r θ p n m = cechResidue r θ q 0 M + cechResidue r θ s N 0 := by
    simp only [cechResidue, fractionResidue_eq_endpointResidue, hfalse, htrue, map_add]
    ring
  rw [heq, cechResidue_x2_open, cechResidue_first_open r θ s N hs, add_zero]

end CycleQ2SeedCechTheta

#print axioms CycleQ2SeedCechTheta.cechResidue_zero_of_boundary
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechThetaColumns.lean -/
section
/-! The nine literal cubic columns used by the smooth Segre incidence
system.  This computes their residue directly in the h+θx₀³ curve charts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCechTheta
open CycleQ2CechLinearCubic
open CycleQ2SeedCech (PS Jet firstJet endpointX endpointY unit_pow_cancel)
open MvPolynomial CycleQ2SeedTrace



def derivativeIntegral (r θ : ℂ) (e : Bool) (p : Poly) : PowerChart r θ e :=
  -powerBase r θ e (endpointY e)^3 * powerEval r θ e p *
    (((powerX2Unit r θ e)⁻¹ : (PowerChart r θ e)ˣ) : PowerChart r θ e)

theorem derivative_fraction_integral (r θ : ℂ) (e : Bool) (p : Poly) :
    powerEval r θ e (derivativeNumerator p) *
      ((powerX2Unit r θ e)⁻¹ : (PowerChart r θ e)ˣ)^4 = derivativeIntegral r θ e p := by
  have hc : powerX2 r θ e^3 *
      (((powerX2Unit r θ e)⁻¹ : (PowerChart r θ e)ˣ) : PowerChart r θ e)^4 =
      (((powerX2Unit r θ e)⁻¹ : (PowerChart r θ e)ˣ) : PowerChart r θ e) := by
    simpa only [coe_powerX2Unit, pow_one] using
      unit_pow_cancel (powerX2Unit r θ e) 1 4 (by decide)
  simp only [derivativeNumerator, map_mul, map_neg, map_pow, powerEval_X_two,
    powerEval_X_three, derivativeIntegral]
  calc
    _ = (-powerBase r θ e (endpointY e)^3 * powerEval r θ e p) *
        (powerX2 r θ e^3 *
          (((powerX2Unit r θ e)⁻¹ : (PowerChart r θ e)ˣ) : PowerChart r θ e)^4) := by ring
    _ = _ := by rw [hc]

theorem derivative_fractionResidue (r θ : ℂ) (e : Bool) (p : Poly) :
    fractionResidue r θ e (derivativeNumerator p) 2 4 =
      PowerSeries.coeff 1 (powerCoefficient r θ e (derivativeIntegral r θ e p)) := by
  rw [fractionResidue_double_pole, derivative_fraction_integral]

@[simp] theorem jetEmbedding_powerBase (r θ : ℂ) (e : Bool) (z : PS) :
    jetEmbedding r θ e (powerBase r θ e z) = jetBase r θ e (firstJet z) :=
  curveMap_base firstJet _ _ _ _ _ _

@[simp] theorem jetEmbedding_powerX0 (r θ : ℂ) (e : Bool) :
    jetEmbedding r θ e (powerX0 r θ e) = jetX0 r θ e :=
  curveMap_x0 firstJet _ _ _ _ _

@[simp] theorem jetEmbedding_powerX2 (r θ : ℂ) (e : Bool) :
    jetEmbedding r θ e (powerX2 r θ e) = jetX2 r θ e :=
  curveMap_x2 firstJet _ _ _ _ _

@[simp] theorem true_jetEval_X_zero (r θ : ℂ) :
    jetEval r θ true (X 0) = jetX0 r θ true := by simp [jetEval]
@[simp] theorem true_jetEval_X_one (r θ : ℂ) :
    jetEval r θ true (X 1) = jetT r θ true := by simp [jetEval, endpointX, jetT]
@[simp] theorem true_jetEval_X_two (r θ : ℂ) :
    jetEval r θ true (X 2) = jetX2 r θ true := by simp [jetEval]
@[simp] theorem true_jetEval_X_three (r θ : ℂ) :
    jetEval r θ true (X 3) = 1 := by simp [jetEval, endpointY]

theorem jetEmbedding_derivativeIntegral (r θ : ℂ) (e : Bool) (p : Poly) :
    jetEmbedding r θ e (derivativeIntegral r θ e p) =
      -jetBase r θ e (firstJet (endpointY e))^3 * jetEval r θ e p *
        (((jetX2Unit r θ e)⁻¹ : (JetChart r θ e)ˣ) : JetChart r θ e) := by
  simp [derivativeIntegral, jetEval, jetX2Unit]

theorem false_jet_derivativeIntegral (r θ : ℂ) (p : Poly) :
    jetEmbedding r θ false (derivativeIntegral r θ false p) = 0 := by
  rw [jetEmbedding_derivativeIntegral]
  change -(jetT r θ false)^3 * _ * _ = 0
  rw [pow_succ, jetT_sq, zero_mul, neg_zero, zero_mul, zero_mul]

theorem true_jet_derivativeIntegral (r θ : ℂ) (p : Poly) :
    jetEmbedding r θ true (derivativeIntegral r θ true p) =
      -jetEval r θ true p *
        (((jetX2Unit r θ true)⁻¹ : (JetChart r θ true)ˣ) : JetChart r θ true) := by
  rw [jetEmbedding_derivativeIntegral]
  simp only [endpointY, map_one, one_pow, neg_one_mul]

@[simp] theorem jetCoefficient_base (r θ : ℂ) (e : Bool) (z : Jet) :
    jetCoefficient r θ e (jetBase r θ e z) = 0 := by
  simpa using jetCoefficient_small r θ e z 0 0 (by decide) (by decide)

@[simp] theorem jetCoefficient_x0 (r θ : ℂ) (e : Bool) :
    jetCoefficient r θ e (jetX0 r θ e) = 0 := by
  simpa using jetCoefficient_small r θ e 1 1 0 (by decide) (by decide)

@[simp] theorem jetCoefficient_x2 (r θ : ℂ) (e : Bool) :
    jetCoefficient r θ e (jetX2 r θ e) = 0 := by
  simpa using jetCoefficient_small r θ e 1 0 1 (by decide) (by decide)

@[simp] theorem jetCoefficient_x2_sq (r θ : ℂ) (e : Bool) :
    jetCoefficient r θ e (jetX2 r θ e^2) = 0 := by
  simpa using jetCoefficient_small r θ e 1 0 2 (by decide) (by decide)

@[simp] theorem jetCoefficient_t (r θ : ℂ) (e : Bool) :
    jetCoefficient r θ e (jetT r θ e) = 0 := jetCoefficient_base r θ e _

def trueJetVector (r θ : ℂ) : Fin 9 → Jet := ![
  0,
  -firstJet (PowerSeries.C θ)*firstJet (PowerSeries.C r)*firstJet PowerSeries.X*
    firstJet (PowerSeries.C kappa)^2,
  0,0,0,0,0,0,
  firstJet (PowerSeries.C r)*firstJet PowerSeries.X*firstJet (PowerSeries.C kappa)]

theorem true_jet_derivative_columns (r θ : ℂ) (j : Fin 9) :
    jetCoefficient r θ true
      (jetEmbedding r θ true (derivativeIntegral r θ true (cubicColumn j))) =
        trueJetVector r θ j := by
  rw [true_jet_derivativeIntegral]
  have hu : jetX2 r θ true *
      (((jetX2Unit r θ true)⁻¹ : (JetChart r θ true)ˣ) : JetChart r θ true) = 1 := by
    rw [← coe_jetX2Unit]
    exact (jetX2Unit r θ true).mul_inv
  have hc2 : jetX2 r θ true^2 *
      (((jetX2Unit r θ true)⁻¹ : (JetChart r θ true)ˣ) : JetChart r θ true) =
      jetX2 r θ true := by
    rw [pow_two, mul_assoc, hu, mul_one]
  have hc3 : jetX2 r θ true^3 *
      (((jetX2Unit r θ true)⁻¹ : (JetChart r θ true)ˣ) : JetChart r θ true) =
      jetX2 r θ true^2 := by
    rw [pow_succ, mul_assoc, hu, mul_one]
  fin_cases j
  all_goals simp only [cubicColumn, trueJetVector,
    Matrix.cons_val_zero', Matrix.cons_val_succ',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_succ,
    Fin.reduceSucc, mon, map_mul, map_neg, map_pow,
    true_jetEval_X_zero, true_jetEval_X_one, true_jetEval_X_two, true_jetEval_X_three,
    pow_zero, pow_one, one_pow, one_mul, mul_one]
  · rw [neg_neg, hc2, jetCoefficient_x2]
  · simpa using jetCoefficient_neg_inverse r θ
  · rw [neg_mul, hc3, map_neg, jetCoefficient_x2_sq, neg_zero]
  · rw [neg_mul, mul_assoc, hu, mul_one, map_neg, jetCoefficient_t, neg_zero]
  · rw [pow_succ, jetT_sq, zero_mul, neg_zero, zero_mul, map_zero]
  · rw [neg_mul, mul_assoc, hu, mul_one, map_neg, jetCoefficient_x0, neg_zero]
  · rw [jetT_sq, mul_zero, neg_zero, zero_mul, map_zero]
  · rw [mul_comm (jetX0 r θ true^2), true_jet_t_mul_a_sq,
      neg_zero, zero_mul, map_zero]
  · rw [neg_mul, ← mul_neg]
    exact jetCoefficient_a_cube_neg_inverse r θ

end CycleQ2SeedCechTheta

#print axioms CycleQ2SeedCechTheta.true_jet_derivative_columns
end
end
