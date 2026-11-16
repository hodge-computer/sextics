import Proposal.JacobianSeedBinding
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
Arithmetic lifting of the mixed-polar conic with all four independent
parameters retained. The characteristic-changing step uses the shared
square-system theorem of fqlx, not a continuity claim about the modular seed.
Adapted from the accepted constructions of fqlx and hodgepodgeconjecture.
Prepared for benediamond with OpenAI Codex assistance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace MixedPolarJacobianLifting
open HoldoutConstruction MixedPolarJacobianIncidence MixedPolarJacobianSeedBinding
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev ParameterRing := MvPolynomial (Fin 4) ℤ
def parameter : Fin 4 → ParameterRing := MvPolynomial.X
def endpoints : Fin 2 → ParameterRing := ![parameter 2,parameter 3]
def genericEquations : Fin 13 → MvPolynomial (Fin 13) ParameterRing :=
  equations (parameter 0) (parameter 1) endpoints

def seedMap : ParameterRing →+* ZMod 5 :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod 5)) ![1,3,1,4]
lemma seedMap_parameter (i : Fin 4) : seedMap (parameter i)=(![1,3,1,4] : Fin 4 → ZMod 5) i := by
  simp [seedMap,parameter]
lemma seed_curve_binding : curveEval endpoints seedMap seed=seedCurve := by
  rw [curveEval_eq_valueCurve,← curveEval_seed,curveEval_eq_valueCurve]
  congr 1
  funext i
  fin_cases i <;> simp [endpoints,seedMap_parameter,MixedPolarJacobianSeedBinding.endpoints]

section Seed
local instance : Algebra ParameterRing (ZMod 5) := seedMap.toAlgebra
lemma generic_seed_equations (i : Fin 13) :
    MvPolynomial.aeval seed (genericEquations i)=0 := by
  change MvPolynomial.eval₂Hom seedMap seed
    (equations (parameter 0) (parameter 1) endpoints i)=0
  rw [equations_eval,seed_curve_binding,seedMap_parameter,seedMap_parameter]
  simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,map_one,map_ofNat,Polynomial.coeff_zero] using
    congrArg (fun p : Polynomial (ZMod 5) => p.coeff i.val) seed_incidence
lemma generic_seed_jacobian : IsUnit (Matrix.det (fun i j : Fin 13 =>
    MvPolynomial.aeval seed (MvPolynomial.pderiv i (genericEquations j)))) := by
  have hm : (fun i j : Fin 13 => MvPolynomial.aeval seed
      (MvPolynomial.pderiv i (genericEquations j)))=gradientJacobian.transpose := by
    funext i j
    change MvPolynomial.eval₂Hom seedMap seed
      (MvPolynomial.pderiv i (equations (parameter 0) (parameter 1) endpoints j))=_
    rw [equations_pderiv_eval,seed_curve_binding,seedMap_parameter,seedMap_parameter]
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,map_one,map_ofNat,
      seed_gradient,gradientJacobian,Matrix.transpose_apply]
  rw [hm,Matrix.det_transpose]
  exact gradientJacobian_unit
instance incidence_nontrivial : Nontrivial (SquareEtaleRing genericEquations) :=
  square_system_jacobian_nontrivial genericEquations seed
    generic_seed_equations generic_seed_jacobian
end Seed

/-- The very same integral incidence has a nonsingular solution over a finite
separable extension of any field containing its parameter ring injectively. -/
theorem generic_lift {K : Type*} [Field K] [Algebra ParameterRing K]
    (hinj : Function.Injective (algebraMap ParameterRing K)) :
    ∃ I : Ideal (SquareGenericAlgebra K genericEquations), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K genericEquations) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K genericEquations) ⧸ I) ∧
      (∀ i, MvPolynomial.aeval (squareGenericCoordinates genericEquations I)
        (genericEquations i)=0) ∧
      IsUnit (Matrix.det (fun i j => MvPolynomial.aeval
        (squareGenericCoordinates genericEquations I)
        (MvPolynomial.pderiv i (genericEquations j)))) :=
  squareGeneric_exists_fieldFactor genericEquations hinj

abbrev ComplexParameterRing := MvPolynomial (Fin 4) ℂ
abbrev ComplexParameterField := FractionRing ComplexParameterRing
def complexParameterMap : ParameterRing →+* ComplexParameterField :=
  (algebraMap ComplexParameterRing ComplexParameterField).comp
    (MvPolynomial.map (Int.castRingHom ℂ))
instance complexParameterAlgebra : Algebra ParameterRing ComplexParameterField :=
  complexParameterMap.toAlgebra
noncomputable instance (priority := 2000) complexParameterModule : Module ParameterRing ComplexParameterField :=
  Algebra.toModule
noncomputable instance (priority := 2000) complexParameterSMul : SMul ParameterRing ComplexParameterField :=
  complexParameterModule.toSMul
lemma complexParameterMap_injective : Function.Injective complexParameterMap :=
  (IsFractionRing.injective ComplexParameterRing ComplexParameterField).comp
    (MvPolynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective)

/-- An unconditional finite generic field factor over C(c1,c2,r0,x0). -/
theorem complex_generic_factor_exists :
    ∃ I : Ideal (SquareGenericAlgebra ComplexParameterField genericEquations),
      I.IsMaximal ∧ Module.Finite ComplexParameterField
        ((SquareGenericAlgebra ComplexParameterField genericEquations) ⧸ I) := by
  obtain ⟨I,hI,hfin,hsep,heq,hjac⟩ :=
    generic_lift (K := ComplexParameterField) complexParameterMap_injective
  exact ⟨I,hI,hfin⟩

#print axioms generic_lift
#print axioms complex_generic_factor_exists
end MixedPolarJacobianLifting
