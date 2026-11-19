import Proposal.BundleConicSeed
import HodgeComputer.Constructions.PolynomialCurves.ComplexPoint
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting

/-!
The exact modular conic first supplies a complex conic at a=0,b=-2 and
endpoint (1,1,4,1). That endpoint satisfies its equation over the integers.
A complex specialization then proves nontriviality of the generic incidence.
The shared étale/flatness theorem supplies the finite separable field factor.
This instantiates the accepted machinery of fqlx and hodgepodgeconjecture;
prepared with OpenAI ChatGPT assistance.
-/
noncomputable section
namespace HoldoutBundle
open HoldoutConstruction Polynomial

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
def integerEndpoint : Fin 4 → ℤ := ![1,1,4,1]
def integerEquations : Fin 12 → MvPolynomial (Fin 12) ℤ :=
  equations 0 (-2) integerEndpoint
def complexEndpoint : Fin 4 → ℂ := ![1,1,4,1]

lemma curveEval_integer_seed :
    curveEval integerEndpoint (Int.castRingHom SeedField) seed=seedCurve := by
  rw [curveEval_eq_valueCurve]
  have hk : (fun i => (Int.castRingHom SeedField) (integerEndpoint i))=seedEndpoint := by
    funext i
    fin_cases i <;> simp [integerEndpoint,seedEndpoint]
  rw [hk]
  simpa only [curveEval_eq_valueCurve,RingHom.id_apply] using curveEval_seed

lemma integer_seed_equations (i : Fin 12) :
    MvPolynomial.aeval seed (integerEquations i)=0 := by
  change MvPolynomial.eval₂Hom (Int.castRingHom SeedField) seed
    (equations 0 (-2) integerEndpoint i)=0
  rw [equations_eval,curveEval_integer_seed]
  have hneg : (C ((Int.castRingHom SeedField) (-2)) : Polynomial SeedField)=3 := by
    have h : (Int.castRingHom SeedField) (-2)=3 := by decide
    rw [h,map_ofNat]
  simp only [map_zero,Polynomial.C_0,hneg,seed_incidence,Polynomial.coeff_zero]

lemma integer_seed_jacobian :
    IsUnit (Matrix.det (fun i j : Fin 12 => MvPolynomial.aeval seed
      (MvPolynomial.pderiv i (integerEquations j)))) := by
  have hm : (fun i j : Fin 12 => MvPolynomial.aeval seed
      (MvPolynomial.pderiv i (integerEquations j)))=seedJacobian.transpose := by
    funext i j
    change MvPolynomial.eval₂Hom (Int.castRingHom SeedField) seed
      (MvPolynomial.pderiv i (equations 0 (-2) integerEndpoint j)) = _
    rw [equations_pderiv_eval,curveEval_integer_seed]
    have hneg : (C ((Int.castRingHom SeedField) (-2)) : Polynomial SeedField)=3 := by
      have h : (Int.castRingHom SeedField) (-2)=3 := by decide
      rw [h,map_ofNat]
    simp only [map_zero,Polynomial.C_0,hneg]
    rw [seedJacobian_eq,← gradientJacobian_eq]
    simp only [Matrix.transpose_apply,gradientJacobian,seed_gradient]
  rw [hm,Matrix.det_transpose]
  exact seed_jacobian_unit

instance integer_incidence_nontrivial : Nontrivial (SquareEtaleRing integerEquations) :=
  square_system_jacobian_nontrivial integerEquations seed
    integer_seed_equations integer_seed_jacobian

lemma curveEval_integer_complex (v : Fin 12 → ℂ) :
    curveEval integerEndpoint (Int.castRingHom ℂ) v=valueCurve complexEndpoint v := by
  rw [curveEval_eq_valueCurve]
  congr 1
  funext i
  fin_cases i <;> norm_num [integerEndpoint,complexEndpoint]

/-- An actual complex polynomial conic with nonzero complete Jacobian. -/
theorem exists_complex_seed :
    ∃ v : Fin 12 → ℂ,
      K (C (0 : ℂ)) (C (-2 : ℂ)) (valueCurve complexEndpoint v)=0 ∧
      IsUnit (valueJacobian 0 (-2) complexEndpoint v).det := by
  obtain ⟨v,he,hj⟩ := DeformedConic.complex_point_of_etale_nontrivial integerEquations
  have hcoeff (i : Fin 12) :
      (K (C (0 : ℂ)) (C (-2 : ℂ)) (valueCurve complexEndpoint v)).coeff (i.val+1)=0 := by
    have h := he i
    change MvPolynomial.eval₂Hom (Int.castRingHom ℂ) v
      (equations 0 (-2) integerEndpoint i)=0 at h
    rw [equations_eval,curveEval_integer_complex] at h
    simpa only [map_zero,map_neg,map_ofNat,Polynomial.C_0,Polynomial.C_neg,
      Polynomial.C_ofNat] using h
  have hc : K (C (0 : ℂ)) (C (-2 : ℂ)) (valueCurve complexEndpoint v)=0 := by
    ext n
    rw [Polynomial.coeff_zero]
    by_cases hn : n=0
    · subst n
      rw [K_valueCurve_constant]
      change (1 : ℂ)^6+1^6+0*4^3+(-2)*1^3=0
      norm_num
    · by_cases hn' : n≤12
      · have h := hcoeff ⟨n-1,by omega⟩
        simpa only [Fin.val_mk,show n-1+1=n by omega] using h
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (K_valueCurve_natDegree_le 0 (-2) complexEndpoint v) (by omega))
  have hm : (fun i j : Fin 12 => MvPolynomial.aeval v
      (MvPolynomial.pderiv i (integerEquations j)))=
      (valueJacobian 0 (-2) complexEndpoint v).transpose := by
    funext i j
    change MvPolynomial.eval₂Hom (Int.castRingHom ℂ) v
      (MvPolynomial.pderiv i (equations 0 (-2) integerEndpoint j)) = _
    rw [equations_pderiv_eval,curveEval_integer_complex]
    simp only [map_zero,map_neg,map_ofNat,Polynomial.C_0,Polynomial.C_neg,
      Polynomial.C_ofNat,Matrix.transpose_apply,valueJacobian]
  refine ⟨v,hc,?_⟩
  rw [hm,Matrix.det_transpose] at hj
  exact hj

/-- The complex seed proves nontriviality over any coefficient ring with
this specialization; the endpoint-domain work is supplied by the application. -/
theorem conic_incidence_nontrivial {R : Type*} [CommRing R]
    (a b : R) (k : Fin 4 → R) (σ : R →+* ℂ)
    (ha : σ a=0) (hb : σ b=-2) (hk : ∀ i, σ (k i)=complexEndpoint i) :
    Nontrivial (SquareEtaleRing (equations a b k)) := by
  letI : Algebra R ℂ := σ.toAlgebra
  obtain ⟨v,hc,hj⟩ := exists_complex_seed
  have hcv : curveEval k σ v=valueCurve complexEndpoint v := by
    rw [curveEval_eq_valueCurve]
    congr 1
    funext i
    exact hk i
  have he (i : Fin 12) : MvPolynomial.aeval v (equations a b k i)=0 := by
    change MvPolynomial.eval₂Hom σ v (equations a b k i)=0
    rw [equations_eval,hcv,ha,hb,hc,Polynomial.coeff_zero]
  have hm : (fun i j : Fin 12 => MvPolynomial.aeval v
      (MvPolynomial.pderiv i (equations a b k j)))=
      (valueJacobian 0 (-2) complexEndpoint v).transpose := by
    funext i j
    change MvPolynomial.eval₂Hom σ v
      (MvPolynomial.pderiv i (equations a b k j)) = _
    rw [equations_pderiv_eval,hcv,ha,hb]
    simp only [Polynomial.C_0,Polynomial.C_neg,Polynomial.C_ofNat,
      Matrix.transpose_apply,valueJacobian]
  apply square_system_jacobian_nontrivial (equations a b k) v he
  rwa [hm,Matrix.det_transpose]

/-- The exact conic equations have a finite separable generic solution.
The injective coefficient-field map prevents any specialization-only conclusion. -/
theorem conic_generic_field_exists {R E : Type*} [CommRing R] [Field E]
    [Algebra R E] (a b : R) (k : Fin 4 → R) (σ : R →+* ℂ)
    (ha : σ a=0) (hb : σ b=-2) (hk : ∀ i, σ (k i)=complexEndpoint i)
    (hinj : Function.Injective (algebraMap R E)) :
    ∃ I : Ideal (SquareGenericAlgebra E (equations a b k)), I.IsMaximal ∧
      Module.Finite E ((SquareGenericAlgebra E (equations a b k)) ⧸ I) ∧
      Algebra.IsSeparable E ((SquareGenericAlgebra E (equations a b k)) ⧸ I) ∧
      (∀ i, MvPolynomial.aeval (squareGenericCoordinates (equations a b k) I)
        (equations a b k i)=0) ∧
      IsUnit (Matrix.det (fun i j => MvPolynomial.aeval
        (squareGenericCoordinates (equations a b k) I)
          (MvPolynomial.pderiv i (equations a b k j)))) := by
  letI := conic_incidence_nontrivial a b k σ ha hb hk
  exact squareGeneric_exists_fieldFactor (equations a b k) hinj

#print axioms exists_complex_seed
#print axioms conic_generic_field_exists
end HoldoutBundle
