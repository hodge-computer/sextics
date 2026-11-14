import Proposal.Workspace
import HodgeTarget
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Equiv
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import HodgeComputer.CertificateOperations
import HodgeComputer.Verify
import HodgeComputer.Constructions.RationalFields.Calculus
import HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Isomorphisms
import Proposal.GeometricSeed
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import HodgeComputer.Constructions.HigherResidues.HigherResidue
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.RationalFields.Homogenization
import HodgeComputer.Constructions.RationalFields.CommonDenominatorSubstitution
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FreeModule.Basic
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting
import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import Mathlib.RingTheory.Smooth.AdicCompletion
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FunProp
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Fintype.Fin
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Localization.AtPrime.Basic
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Proposal.GeometricFormalInputs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Proposal.GeometricTarget02Part03

/-! Source partition of GeometricTarget.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/PolynomialProjectiveTrace.lean -/
section
/-! A literal polynomial open detects motion of a projective coefficient
vector.  It retains the numerator of the derivative of a ratio of two
linear coefficient functionals, so scalar rescaling cannot account for
the nonvanishing. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialProjectiveTrace
open Matrix MvPolynomial CycleQ2PolynomialAffineSlice
  CycleQ2PolynomialDerivationChainRule CycleQ2PolynomialImplicitTrace
  CycleQ2ImplicitTraceNumerator
open scoped BigOperators

variable {R S σ m ι : Type*} [CommRing R] [CommRing S]
  [Fintype σ] [Fintype m] [Fintype ι] [DecidableEq ι]

def linearValue (weights : σ → R) : MvPolynomial σ R :=
  ∑ k, C (weights k)*X k

theorem eval_linearValue (φ : R →+* S) (x : σ → S) (weights : σ → R) :
    eval₂Hom φ x (linearValue weights)=(φ ∘ weights) ⬝ᵥ x := by
  simp only [linearValue,map_sum,map_mul,eval₂Hom_C,eval₂Hom_X',dotProduct,
    Function.comp_apply]

def projectiveTracePolynomial (P : Matrix ι m R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) (weights leading direction : σ → R) :
    MvPolynomial σ R :=
  linearValue leading*tracePolynomial P B e weights direction-
    linearValue weights*tracePolynomial P B e leading direction

theorem seed_projectiveTracePolynomial_one (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights leading direction : σ → R)
    (hJ : P.map φ*jacobian φ x e*B.map φ=1)
    (hkernel : jacobian φ x e*ᵥ(φ ∘ direction)=0)
    (htrace : (φ ∘ weights) ⬝ᵥ (φ ∘ direction)=1)
    (hleading : (φ ∘ leading) ⬝ᵥ x=1)
    (hvalue : (φ ∘ weights) ⬝ᵥ x=0) :
    eval₂Hom φ x (projectiveTracePolynomial P B e weights leading direction)=1 := by
  rw [projectiveTracePolynomial,map_sub,map_mul,map_mul,eval_linearValue,
    eval_linearValue,hleading,hvalue,zero_mul,sub_zero,one_mul]
  exact seed_tracePolynomial_one φ x P B e weights direction hJ hkernel htrace

theorem derivative_tracePolynomial [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R)
    (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=algebraMap R S (direction k)+
      (B.map (algebraMap R S)*ᵥ(fun j => D (z j))) k) :
    aeval x (tracePolynomial P B e weights direction)=
      aeval x (retainedJacobian P B e).det*
        ((algebraMap R S ∘ weights) ⬝ᵥ (fun k => D (x k))) := by
  have hu := implicit_derivative_relation D x z P B ((algebraMap R S) ∘ direction) e he hder
  have hx : (fun k => D (x k))=((algebraMap R S) ∘ direction)+
      B.map (algebraMap R S)*ᵥ(fun j => D (z j)) := funext hder
  change eval₂Hom (algebraMap R S) x (tracePolynomial P B e weights direction)=_
  rw [eval_tracePolynomial,traceNumerator_eq_scaled_trace _ _ _ _ _ _ hu,←hx]
  congr 1
  change _=eval₂Hom (algebraMap R S) x (retainedJacobian P B e).det
  rw [RingHom.map_det]
  exact congrArg Matrix.det (eval_retainedJacobian (algebraMap R S) x P B e).symm

theorem derivation_linear_value [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (weights : σ → R) :
    D ((algebraMap R S ∘ weights) ⬝ᵥ x)=
      (algebraMap R S ∘ weights) ⬝ᵥ (fun k => D (x k)) := by
  simp only [dotProduct,map_sum,Function.comp_apply,Derivation.leibniz,
    Derivation.map_algebraMap,smul_eq_mul,mul_zero,add_zero]

theorem derivative_projectiveTracePolynomial [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights leading direction : σ → R)
    (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=algebraMap R S (direction k)+
      (B.map (algebraMap R S)*ᵥ(fun j => D (z j))) k) :
    aeval x (projectiveTracePolynomial P B e weights leading direction)=
      aeval x (retainedJacobian P B e).det*
        (((algebraMap R S ∘ leading) ⬝ᵥ x)*
          D ((algebraMap R S ∘ weights) ⬝ᵥ x)-
        ((algebraMap R S ∘ weights) ⬝ᵥ x)*
          D ((algebraMap R S ∘ leading) ⬝ᵥ x)) := by
  rw [projectiveTracePolynomial,map_sub,map_mul,map_mul]
  change eval₂Hom (algebraMap R S) x (linearValue leading)*_-
      eval₂Hom (algebraMap R S) x (linearValue weights)*_=_
  rw [eval_linearValue,eval_linearValue,
    derivative_tracePolynomial D x z P B e weights direction he hder,
    derivative_tracePolynomial D x z P B e leading direction he hder,
    derivation_linear_value,derivation_linear_value]
  ring

theorem derivative_projective_trace_isUnit [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights leading direction : σ → R)
    (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=algebraMap R S (direction k)+
      (B.map (algebraMap R S)*ᵥ(fun j => D (z j))) k)
    (hN : IsUnit (aeval x (projectiveTracePolynomial P B e weights leading direction))) :
    IsUnit (((algebraMap R S ∘ leading) ⬝ᵥ x)*
      D ((algebraMap R S ∘ weights) ⬝ᵥ x)-
      ((algebraMap R S ∘ weights) ⬝ᵥ x)*
        D ((algebraMap R S ∘ leading) ⬝ᵥ x)) := by
  rw [derivative_projectiveTracePolynomial D x z P B e weights leading direction he hder] at hN
  exact isUnit_of_mul_isUnit_right hN

end CycleQ2PolynomialProjectiveTrace

#print axioms CycleQ2PolynomialProjectiveTrace.seed_projectiveTracePolynomial_one
#print axioms CycleQ2PolynomialProjectiveTrace.derivative_projective_trace_isUnit
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechCancellation.lean -/
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

def laurentCoefficient (r : ℂ) (e : Bool) : LaurentChart r e →ₗ[LS] LS :=
  coefficient (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))

def laurentBase (r : ℂ) (e : Bool) : LS →+* LaurentChart r e :=
  base (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))

def laurentX0 (r : ℂ) (e : Bool) : LaurentChart r e :=
  x0 (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))

def laurentX2 (r : ℂ) (e : Bool) : LaurentChart r e :=
  x2 (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))

theorem laurentEval_monomial (r : ℂ) (e : Bool) (d : Exp) (z : ℂ) :
    laurentEval r e (monomial d z) =
      laurentBase r e (seriesMap (PowerSeries.C z)) * laurentX0 r e ^ d 0 *
        laurentBase r e (seriesMap (endpointX e)) ^ d 1 * laurentX2 r e ^ d 2 *
          laurentBase r e (seriesMap (endpointY e)) ^ d 3 := by
  rw [monomial_eq_C_mul_mon]
  simp [laurentEval, powerEval, mon, powerCoordinates, chartEmbedding,
    laurentBase, laurentX0, laurentX2, Matrix.cons_val_succ, Fin.reduceSucc, mul_assoc]

theorem fraction_monomial_first_open (r : ℂ) (e : Bool) (d : Exp) (z : ℂ) (n : ℕ) :
    fraction r e (monomial d z) n 0 =
      laurentBase r e (seriesMap (PowerSeries.C z) *
        seriesMap (endpointX e) ^ d 1 * seriesMap (endpointY e) ^ d 3 *
          (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ n)) *
        laurentX0 r e ^ d 0 * laurentX2 r e ^ d 2 := by
  simp only [fraction, pow_zero, mul_one, laurentEval_monomial]
  simp only [chartAUnit, Units.coe_map_inv, Units.coe_map, ← map_pow,
    laurentBase, map_mul, map_pow, MonoidHom.coe_coe]
  ring

theorem first_open_monomial_coefficient (r : ℂ) (e : Bool) (d : Exp) (z : ℂ) (n : ℕ)
    (hd0 : d 0 < 2) (hd2 : d 2 < 3) :
    laurentCoefficient r e (fraction r e (monomial d z) n 0) =
      if d 0 = 1 ∧ d 2 = 2 then
        seriesMap (PowerSeries.C z) * seriesMap (endpointX e) ^ d 1 *
          seriesMap (endpointY e) ^ d 3 * (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ n)
      else 0 := by
  rw [fraction_monomial_first_open]
  exact coefficient_small_monomial _ _ _ _ _ _ _ hd0 hd2

theorem scalar_endpoint_residue (z : ℂ) (b d n : ℕ) (e : Bool) :
    (seriesMap (PowerSeries.C z) * seriesMap (endpointX e) ^ b *
      seriesMap (endpointY e) ^ d * (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ n)).coeff (-1) =
        if (if e then (b : ℤ) else (d : ℤ)) - n = -1 then z else 0 := by
  cases e <;>
    simp [endpointX, endpointY, seriesMap, uniformizerUnit, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X, HahnSeries.C, HahnSeries.inv_single, HahnSeries.single_pow,
      HahnSeries.single_mul_single, HahnSeries.coeff_single, sub_eq_add_neg, eq_comm]

theorem cechResidue_reduced_monomial (r : ℂ) (d : Exp) (z : ℂ) (n : ℕ)
    (hd0 : d 0 < 2) (hd2 : d 2 < 3)
    (hdegree : d 0 + d 1 + d 2 + d 3 = 2*n+1) :
    cechResidue r (monomial d z) n 0 = 0 := by
  change (laurentCoefficient r false (fraction r false (monomial d z) n 0)).coeff (-1) -
    (laurentCoefficient r true (fraction r true (monomial d z) n 0)).coeff (-1) = 0
  rw [first_open_monomial_coefficient _ _ _ _ _ hd0 hd2,
    first_open_monomial_coefficient _ _ _ _ _ hd0 hd2]
  by_cases he : d 0 = 1 ∧ d 2 = 2
  · rw [if_pos he, if_pos he, scalar_endpoint_residue, scalar_endpoint_residue]
    have hp : (d 3 : ℤ) - n = -1 ↔ (d 1 : ℤ) - n = -1 := by omega
    simp only [Bool.false_eq_true, if_false, if_true, hp, sub_self]
  · rw [if_neg he, if_neg he]
    simp

theorem cechResidue_sum (r : ℂ) {ι : Type*} (s : Finset ι) (p : ι → Poly) (n m : ℕ) :
    cechResidue r (∑ i ∈ s, p i) n m = ∑ i ∈ s, cechResidue r (p i) n m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cechResidue, fractionResidue, fraction]
  | @insert i s hi ih => simp [Finset.sum_insert hi, cechResidue_add, ih]

/-- The residues at the two endpoints cancel on every canonical-bundle
section over D₊(x₁x₃), with no bound on the denominator power. -/
theorem cechResidue_first_open (r : ℂ) (p : Poly) (n : ℕ)
    (hp : p.IsHomogeneous (2*n+1)) : cechResidue r p n 0 = 0 := by
  obtain ⟨q,hq,hqh,hpq⟩ := exists_homogeneous_curve_normal r p (2*n+1) hp
  have heq (e : Bool) : fraction r e p n 0 = fraction r e q n 0 := by
    have hh := fraction_zero_of_curveIdeal r e hpq n 0
    rwa [fraction_sub, sub_eq_zero] at hh
  have hceq : cechResidue r p n 0 = cechResidue r q n 0 := by
    simp only [cechResidue, fractionResidue, heq]
  rw [hceq]
  conv_lhs => rw [q.as_sum]
  rw [cechResidue_sum]
  apply Finset.sum_eq_zero
  intro d hd
  apply cechResidue_reduced_monomial r d (q.coeff d) n (hq d hd).1 (hq d hd).2
  have hh : d.degree = 2*n+1 := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hqh (mem_support_iff.mp hd)
  rw [Finsupp.degree_eq_sum] at hh
  simpa [Fin.sum_univ_succ, Matrix.cons_val_succ, Fin.reduceSucc, add_assoc] using hh

/-- The actual two-endpoint functional kills every Čech coboundary, including
ones requiring arbitrarily large denominator powers. -/
theorem cechResidue_zero_of_boundary (r : ℂ) (p : Poly) (n m : ℕ)
    (hboundary : CechBoundary r p n m) : cechResidue r p n m = 0 := by
  obtain ⟨N,M,q,s,hn,hm,hq,hs,hmem⟩ := hboundary
  have hfalse := fraction_of_boundary_witness r false p q s n m N M hn hm hmem
  have htrue := fraction_of_boundary_witness r true p q s n m N M hn hm hmem
  have heq : cechResidue r p n m = cechResidue r q 0 M + cechResidue r s N 0 := by
    simp only [cechResidue, fractionResidue, hfalse, htrue, map_add]
    ring
  rw [heq, cechResidue_x2_open, cechResidue_first_open r s N hs, add_zero]

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.cechResidue_zero_of_boundary
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechMembership.lean -/
section
/-! The finite published Artinian trace is now identified with an actual
Čech residue functional on the sparse seed curve.  Arbitrary denominator
powers are allowed in the definition of a coboundary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace CycleQ2HomogeneousComponent

theorem relation_one_eq_curveA_sq (r : ℂ) : relation r 1 = curveA ^ 2 := by
  simp [relation, curveA, mul_pow]

theorem relation_two_eq_curveB_fourth (r : ℂ) : relation r 2 = curveB ^ 4 := by
  rfl

theorem curveA_sq_homogeneous : (curveA ^ 2).IsHomogeneous 4 := by
  simpa [curveA, mul_pow] using
    (isHomogeneous_X_pow (1 : Fin 4) 2).mul (isHomogeneous_X_pow (3 : Fin 4) 2)

theorem curveB_fourth_homogeneous : (curveB ^ 4).IsHomogeneous 4 :=
  isHomogeneous_X_pow (2 : Fin 4) 4

/-- Homogeneous projection turns arbitrary ideal-membership coefficients
into genuine canonical-bundle cochains on the two specified opens. -/
theorem boundary_of_mem_reducedIdeal (r : ℂ) {p : Poly}
    (hp : p.IsHomogeneous 9) (hmem : p ∈ reducedIdeal r) : CechBoundary r p 2 4 := by
  obtain ⟨u,hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have hu' : u 0 * curveF1 r + u 1 * curveA^2 + u 2 * curveB^4 + u 3 * curveH = p := by
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      relation_one_eq_curveA_sq, relation_two_eq_curveB_fourth,
      Matrix.cons_val_succ, Fin.reduceSucc, curveF1, curveH,
      show relation r 3 = h from rfl, add_assoc] using hu
  have hh := congrArg (homogeneousComponent 9) hu'
  rw [map_add, map_add, map_add,
    component_mul_of_homogeneous _ _ (curveF1_homogeneous r) (by decide),
    component_mul_of_homogeneous _ _ curveA_sq_homogeneous (by decide),
    component_mul_of_homogeneous _ _ curveB_fourth_homogeneous (by decide),
    component_mul_of_homogeneous _ _ curveH_homogeneous (by decide),
    homogeneousComponent_of_mem hp, if_pos rfl] at hh
  refine ⟨2,4,homogeneousComponent 5 (u 1),homogeneousComponent 5 (u 2),
    le_rfl,le_rfl,homogeneousComponent_isHomogeneous 5 (u 1),
    homogeneousComponent_isHomogeneous 5 (u 2),?_⟩
  simp only [Nat.sub_self, pow_zero, mul_one]
  apply Ideal.mem_span_pair.mpr
  refine ⟨homogeneousComponent 7 (u 0),homogeneousComponent 6 (u 3),?_⟩
  norm_num at hh
  linear_combination hh


end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.boundary_of_mem_reducedIdeal
end
end


/- Component: continuation_3/SegreModularTangentData.lean -/
section
/-! Literal modular Segre seed data used by the basepoint proof. Every
polynomial identity involving these coefficients is checked separately in the
kernel. The independent characteristic-zero tangent is proved in
SegreGaussianTangent; no modular lifting premise is used. -/
set_option maxRecDepth 20000
set_option Elab.async false
namespace CycleQ2SegreModularTangentData
open CycleQ2SparseModularPolynomial
def m00 : Blocks :=
  [
    [[],
    [((0,2,8,2,0),108),
    ((0,3,6,3,0),5)],
    [((0,2,8,0,0),108),
    ((0,3,6,1,0),5)],
    [((0,1,4,3,0),1),
    ((0,2,2,4,0),104)],
    [((0,1,4,1,0),1),
    ((0,2,2,2,0),104)]],
    [[],
    [((0,3,4,4,0),88),
    ((0,4,2,5,0),105),
    ((0,2,3,6,0),21),
    ((0,3,1,7,0),4)],
    [((0,3,4,2,0),88),
    ((0,4,2,3,0),105),
    ((0,2,3,4,0),21),
    ((0,3,1,5,0),4)]],
    [[],
    [],
    [((0,2,4,2,0),2)],
    [((0,2,4,0,0),2)],
    [((0,1,0,3,0),107)],
    [((0,1,0,1,0),107)]],
    [[],
    [],
    [((0,2,2,3,0),52),
    ((0,1,1,5,0),57)],
    [((0,2,2,1,0),52),
    ((0,1,1,3,0),57)]],
    [[((0,3,4,3,0),57)],
    [((0,3,4,1,0),57)],
    [((0,2,0,4,0),52)],
    [((0,2,0,2,0),52)]],
    [[((0,1,6,2,0),108),
    ((0,0,5,4,0),1)],
    [((0,1,6,0,0),108),
    ((0,0,5,2,0),1)]],
    [],
    [[],
    [((0,1,2,2,0),2),
    ((0,0,1,4,0),107)],
    [((0,1,2,0,0),2),
    ((0,0,1,2,0),107)]]
  ]

def q00 : Blocks :=
  [
    [],
    [],
    [],
    [[((0,6,3,10,0),88),
    ((0,3,6,10,0),21),
    ((0,7,1,11,0),21),
    ((0,4,4,11,0),88),
    ((0,2,5,12,0),88),
    ((0,6,0,13,0),21),
    ((0,2,2,15,0),21)],
    [((0,6,3,8,0),88),
    ((0,7,1,9,0),21),
    ((0,6,0,11,0),21)]],
    [[((0,8,0,10,0),21),
    ((0,5,3,10,0),88),
    ((0,4,2,12,0),21)],
    [((0,8,0,8,0),21),
    ((0,5,3,8,0),57),
    ((0,2,6,8,0),52),
    ((0,6,1,9,0),52),
    ((0,3,4,9,0),57),
    ((0,1,5,10,0),57),
    ((0,5,0,11,0),52),
    ((0,1,2,13,0),52)],
    [((0,5,3,6,0),57),
    ((0,6,1,7,0),52),
    ((0,5,0,9,0),52),
    ((0,2,3,9,0),21),
    ((0,3,1,10,0),88),
    ((0,2,0,12,0),88)]],
    [[((0,2,7,8,0),21),
    ((0,3,5,9,0),88),
    ((0,2,4,11,0),88)],
    [((0,7,0,8,0),52),
    ((0,4,3,8,0),57),
    ((0,3,2,10,0),52)],
    [((0,7,0,6,0),52),
    ((0,4,0,9,0),88)],
    [((0,1,3,7,0),52),
    ((0,2,1,8,0),57),
    ((0,1,0,10,0),57)]],
    [[((0,4,4,8,0),88)],
    [((0,1,7,6,0),52),
    ((0,2,5,7,0),57),
    ((0,1,4,9,0),57)],
    [],
    [((0,3,0,7,0),57)]],
    [[],
    [((0,3,4,6,0),57)]]
  ]

def m01 : Blocks :=
  [
    [[],
    [],
    [((0,2,8,0,0),108)],
    [],
    [((0,1,4,1,0),1)]],
    [[],
    [((0,3,7,1,0),57)],
    [((0,2,6,1,0),1),
    ((0,3,4,2,0),88),
    ((0,2,3,4,0),21)],
    [((0,2,3,2,0),52)],
    [((0,1,2,2,0),108)]],
    [[((0,3,8,1,0),57)],
    [((0,4,3,3,0),107),
    ((0,3,2,5,0),2)],
    [((0,2,4,2,0),52),
    ((0,3,2,3,0),21),
    ((0,2,1,5,0),88)]],
    [[((0,4,4,3,0),86),
    ((0,3,3,5,0),2)],
    [],
    [((0,2,5,0,0),1),
    ((0,3,0,4,0),21)],
    [((0,2,2,1,0),52),
    ((0,1,1,3,0),57)],
    [((0,1,1,1,0),108)]],
    [[((0,2,6,2,0),52),
    ((0,1,5,4,0),57)],
    [((0,2,6,0,0),1),
    ((0,3,4,1,0),57)],
    [],
    [((0,1,2,1,0),108),
    ((0,2,0,2,0),52)]],
    [[],
    [((0,1,6,0,0),108),
    ((0,0,5,2,0),1)]],
    [[],
    [((0,1,4,1,0),1),
    ((0,0,3,3,0),108)]],
    [],
    [[],
    [((0,1,3,0,0),1),
    ((0,0,2,2,0),108)]],
    [[((0,1,4,0,0),1),
    ((0,0,3,2,0),108)]]
  ]

def q01 : Blocks :=
  [
    [],
    [],
    [],
    [],
    [[((0,5,3,10,0),52),
    ((0,2,6,10,0),57),
    ((0,6,1,11,0),57),
    ((0,3,4,11,0),52),
    ((0,1,5,12,0),52),
    ((0,5,0,13,0),57),
    ((0,1,2,15,0),57)],
    [((0,5,3,8,0),104),
    ((0,2,6,8,0),57),
    ((0,6,1,9,0),5),
    ((0,3,4,9,0),52),
    ((0,1,5,10,0),52),
    ((0,5,0,11,0),5),
    ((0,1,2,13,0),57)],
    [((0,5,3,6,0),52),
    ((0,6,1,7,0),57),
    ((0,5,0,9,0),57)]],
    [[((0,7,0,10,0),57),
    ((0,4,3,10,0),52),
    ((0,3,2,12,0),57)],
    [((0,7,0,8,0),5),
    ((0,4,3,8,0),52),
    ((0,3,2,10,0),57)],
    [((0,7,0,6,0),57),
    ((0,1,3,9,0),57),
    ((0,2,1,10,0),52),
    ((0,1,0,12,0),52)],
    [((0,1,3,7,0),57),
    ((0,2,1,8,0),52),
    ((0,1,0,10,0),52)]],
    [[((0,1,7,8,0),57),
    ((0,2,5,9,0),52),
    ((0,1,4,11,0),52)],
    [((0,1,7,6,0),57),
    ((0,2,5,7,0),52),
    ((0,1,4,9,0),52)],
    [((0,3,0,9,0),52)],
    [((0,3,0,7,0),52)]],
    [[((0,3,4,8,0),52)],
    [((0,3,4,6,0),52)]]
  ]

def m02 : Blocks :=
  [
    [[((0,3,9,2,0),52),
    ((0,4,7,3,0),57),
    ((0,3,6,5,0),57)],
    [],
    [((0,2,5,3,0),57),
    ((0,3,3,4,0),52),
    ((0,2,2,6,0),52)]],
    [[((0,5,6,2,0),57),
    ((0,4,5,4,0),2),
    ((0,5,3,5,0),107),
    ((0,3,4,6,0),107),
    ((0,3,1,9,0),2)],
    [],
    [((0,4,2,3,0),52)]],
    [[((0,6,2,4,0),107),
    ((0,5,1,6,0),2)],
    [((0,2,7,1,0),108),
    ((0,3,5,2,0),1),
    ((0,2,4,4,0),1)],
    [],
    [((0,1,3,2,0),1),
    ((0,2,1,3,0),108),
    ((0,1,0,5,0),108)]],
    [[],
    [((0,4,4,1,0),1)],
    [],
    [((0,3,0,2,0),108)]],
    [],
    [],
    [],
    [[((0,1,5,1,0),108),
    ((0,2,3,2,0),1),
    ((0,0,4,3,0),1),
    ((0,0,1,6,0),108)]],
    [[((0,3,2,1,0),1),
    ((0,2,1,3,0),108)]]
  ]

def q02 : Blocks :=
  [
    [],
    [],
    [],
    [[],
    [((0,5,2,10,0),52),
    ((0,2,5,10,0),57),
    ((0,6,0,11,0),67),
    ((0,3,3,11,0),42),
    ((0,1,4,12,0),52),
    ((0,2,2,13,0),67)],
    [((0,5,2,8,0),104),
    ((0,2,5,8,0),57),
    ((0,6,0,9,0),25),
    ((0,3,3,9,0),42),
    ((0,1,4,10,0),52),
    ((0,2,2,11,0),67)],
    [((0,5,2,6,0),52),
    ((0,6,0,7,0),67)]],
    [[],
    [],
    [((0,5,0,9,0),5),
    ((0,2,3,9,0),104),
    ((0,1,2,11,0),5)],
    [((0,5,0,7,0),10),
    ((0,2,3,7,0),104),
    ((0,1,2,9,0),62),
    ((0,2,0,10,0),42)],
    [((0,5,0,5,0),5),
    ((0,1,2,7,0),57),
    ((0,2,0,8,0),42)]],
    [[],
    [((0,1,6,8,0),57),
    ((0,5,1,9,0),52),
    ((0,2,4,9,0),99),
    ((0,1,3,11,0),52)],
    [((0,1,6,6,0),57),
    ((0,5,1,7,0),104),
    ((0,2,4,7,0),99),
    ((0,1,3,9,0),52)],
    [((0,5,1,5,0),52)],
    [((0,1,0,8,0),104)],
    [((0,1,0,6,0),104)]],
    [[((0,5,2,9,0),52),
    ((0,2,5,9,0),57),
    ((0,1,4,11,0),52)],
    [((0,5,2,7,0),104),
    ((0,2,5,7,0),57),
    ((0,1,4,9,0),52)],
    [((0,5,2,5,0),52),
    ((0,1,4,7,0),104)],
    [((0,1,4,5,0),104),
    ((0,1,1,8,0),57)],
    [((0,1,1,6,0),57)]],
    [[],
    [((0,1,5,7,0),57)],
    [((0,1,5,5,0),57),
    ((0,1,2,8,0),57)],
    [((0,1,2,6,0),57)]],
    [[((0,1,6,7,0),57)],
    [((0,1,6,5,0),57)]]
  ]

def m10 : Blocks :=
  [
    [[],
    [((0,1,7,4,0),108),
    ((0,2,5,5,0),5),
    ((0,2,2,8,0),88),
    ((0,3,0,9,0),105)],
    [((0,4,4,2,0),1),
    ((0,1,7,2,0),108),
    ((0,5,2,3,0),104),
    ((0,2,5,3,0),5),
    ((0,2,2,6,0),88),
    ((0,3,0,7,0),105)],
    [((0,4,4,0,0),1),
    ((0,5,2,1,0),104)]],
    [],
    [[],
    [((0,0,8,2,0),108),
    ((0,1,6,3,0),5)],
    [((0,0,8,0,0),108),
    ((0,1,6,1,0),5),
    ((0,1,3,4,0),2),
    ((0,1,0,7,0),52)],
    [((0,4,0,2,0),107),
    ((0,1,3,2,0),2),
    ((0,1,0,5,0),52)],
    [((0,4,0,0,0),107)]],
    [],
    [[((0,2,3,5,0),57),
    ((0,0,4,6,0),108)],
    [((0,5,0,3,0),52),
    ((0,2,3,3,0),57),
    ((0,0,4,4,0),108)],
    [((0,5,0,1,0),52),
    ((0,0,4,2,0),2)],
    [((0,0,4,0,0),2)]],
    [],
    [[((0,1,4,3,0),57)],
    [((0,1,4,1,0),57),
    ((0,0,0,6,0),2)],
    [((0,0,0,4,0),2)]]
  ]

def q10 : Blocks :=
  [
    [],
    [],
    [],
    [[((0,4,7,8,0),88),
    ((0,5,5,9,0),21),
    ((0,4,4,11,0),21)],
    [],
    [((0,3,3,9,0),21),
    ((0,4,1,10,0),88),
    ((0,3,0,12,0),88)]],
    [[((0,7,5,6,0),21),
    ((0,8,3,7,0),88),
    ((0,3,7,8,0),21),
    ((0,4,5,9,0),88),
    ((0,2,6,10,0),88),
    ((0,6,1,11,0),21),
    ((0,2,3,13,0),21)],
    [((0,3,7,6,0),57),
    ((0,4,5,7,0),52),
    ((0,3,4,9,0),52)],
    [((0,5,0,9,0),88)],
    [((0,2,3,7,0),52),
    ((0,3,1,8,0),57),
    ((0,2,0,10,0),57)]],
    [[((0,9,2,6,0),88),
    ((0,8,1,8,0),21),
    ((0,5,4,8,0),88),
    ((0,4,3,10,0),21)],
    [((0,6,5,4,0),52),
    ((0,7,3,5,0),57),
    ((0,2,7,6,0),52),
    ((0,3,5,7,0),57),
    ((0,1,6,8,0),57),
    ((0,5,1,9,0),52),
    ((0,1,3,11,0),52)],
    [((0,3,5,5,0),88),
    ((0,4,3,6,0),21),
    ((0,2,4,7,0),21),
    ((0,2,1,10,0),88)],
    [((0,4,0,7,0),57)]],
    [[],
    [((0,8,2,4,0),57),
    ((0,7,1,6,0),52),
    ((0,4,4,6,0),57),
    ((0,3,3,8,0),52)],
    [((0,5,2,5,0),21),
    ((0,4,1,7,0),88)],
    [((0,2,5,3,0),57),
    ((0,3,3,4,0),52),
    ((0,1,4,5,0),52),
    ((0,1,1,8,0),57)]],
    [[],
    [],
    [],
    [((0,4,2,3,0),52),
    ((0,3,1,5,0),57)]]
  ]

def m11 : Blocks :=
  [
    [[],
    [],
    [((0,1,7,2,0),108),
    ((0,2,2,6,0),88)],
    [((0,4,4,0,0),1)]],
    [[],
    [((0,2,6,3,0),57),
    ((0,3,1,7,0),107)],
    [((0,5,3,1,0),52),
    ((0,1,5,3,0),1),
    ((0,2,0,7,0),21)],
    [((0,4,2,1,0),108)]],
    [[((0,2,7,3,0),57),
    ((0,3,2,7,0),107)],
    [((0,5,4,1,0),52)],
    [((0,0,8,0,0),108)],
    [((0,1,0,5,0),52)]],
    [[((0,3,3,5,0),88),
    ((0,1,4,6,0),52)],
    [((0,1,7,1,0),57),
    ((0,6,0,3,0),21)],
    [((0,0,6,1,0),1),
    ((0,1,4,2,0),1)],
    [((0,4,1,0,0),108)]],
    [[((0,1,8,1,0),57)],
    [((0,1,5,2,0),1),
    ((0,2,3,3,0),57),
    ((0,0,4,4,0),108)],
    [((0,4,2,0,0),108),
    ((0,5,0,1,0),52)]],
    [[((0,2,4,3,0),88)],
    [((0,0,2,5,0),1)],
    [((0,0,5,0,0),1)]],
    [[],
    [((0,0,6,0,0),1),
    ((0,1,4,1,0),57)]],
    [[],
    [((0,0,1,4,0),1)]],
    [[((0,0,2,4,0),1)]]
  ]

def q11 : Blocks :=
  [
    [],
    [],
    [],
    [],
    [[((0,3,7,8,0),52),
    ((0,4,5,9,0),57),
    ((0,3,4,11,0),57)],
    [((0,3,7,6,0),52),
    ((0,4,5,7,0),57),
    ((0,3,4,9,0),57)],
    [((0,2,3,9,0),57),
    ((0,3,1,10,0),52),
    ((0,2,0,12,0),52)],
    [((0,2,3,7,0),57),
    ((0,3,1,8,0),52),
    ((0,2,0,10,0),52)]],
    [[((0,6,5,6,0),57),
    ((0,7,3,7,0),52),
    ((0,2,7,8,0),57),
    ((0,3,5,9,0),52),
    ((0,1,6,10,0),52),
    ((0,5,1,11,0),57),
    ((0,1,3,13,0),57)],
    [((0,6,5,4,0),57),
    ((0,7,3,5,0),52),
    ((0,2,7,6,0),57),
    ((0,3,5,7,0),52),
    ((0,1,6,8,0),52),
    ((0,5,1,9,0),57),
    ((0,1,3,11,0),57)],
    [((0,4,0,9,0),52)],
    [((0,4,0,7,0),52)]],
    [[((0,8,2,6,0),52),
    ((0,7,1,8,0),57),
    ((0,4,4,8,0),52),
    ((0,3,3,10,0),57)],
    [((0,8,2,4,0),52),
    ((0,7,1,6,0),57),
    ((0,4,4,6,0),52),
    ((0,3,3,8,0),57)],
    [((0,2,5,5,0),52),
    ((0,3,3,6,0),57),
    ((0,1,4,7,0),57),
    ((0,1,1,10,0),52)],
    [((0,2,5,3,0),52),
    ((0,3,3,4,0),57),
    ((0,1,4,5,0),57),
    ((0,1,1,8,0),52)]],
    [[],
    [],
    [((0,4,2,5,0),57),
    ((0,3,1,7,0),52)],
    [((0,4,2,3,0),57),
    ((0,3,1,5,0),52)]]
  ]

def m12 : Blocks :=
  [
    [[((0,2,8,4,0),52),
    ((0,3,6,5,0),57),
    ((0,2,5,7,0),57),
    ((0,3,3,8,0),2),
    ((0,4,1,9,0),107),
    ((0,3,0,11,0),107)],
    [((0,5,5,2,0),57),
    ((0,6,3,3,0),52),
    ((0,5,2,5,0),52)]],
    [[((0,4,5,4,0),57),
    ((0,5,0,8,0),107)],
    [((0,7,2,2,0),52)]],
    [[((0,1,9,2,0),52),
    ((0,2,7,3,0),57),
    ((0,1,6,5,0),57)],
    [((0,1,6,3,0),108),
    ((0,2,4,4,0),1),
    ((0,1,3,6,0),1)],
    [((0,4,3,1,0),1),
    ((0,5,1,2,0),108),
    ((0,4,0,4,0),108)]],
    [[((0,3,6,2,0),57)],
    [((0,3,3,3,0),1)],
    [((0,6,0,1,0),108)]],
    [[],
    [((0,0,7,1,0),108),
    ((0,1,5,2,0),1),
    ((0,0,4,4,0),1)]],
    [[],
    [((0,2,4,1,0),1)]],
    [[((0,0,3,5,0),108),
    ((0,1,1,6,0),1),
    ((0,0,0,8,0),1)]],
    [[((0,2,0,5,0),1)]]
  ]

def q12 : Blocks :=
  [
    [],
    [],
    [],
    [[],
    [((0,3,6,8,0),52),
    ((0,4,4,9,0),67)],
    [((0,3,6,6,0),52),
    ((0,4,4,7,0),67)],
    [((0,2,2,9,0),57),
    ((0,3,0,10,0),42)],
    [((0,2,2,7,0),57),
    ((0,3,0,8,0),42)]],
    [[],
    [((0,6,4,6,0),57),
    ((0,7,2,7,0),42),
    ((0,5,3,8,0),52),
    ((0,2,6,8,0),57),
    ((0,6,1,9,0),67),
    ((0,3,4,9,0),42),
    ((0,1,5,10,0),52),
    ((0,2,3,11,0),67)],
    [((0,6,4,4,0),57),
    ((0,7,2,5,0),42),
    ((0,5,3,6,0),52),
    ((0,2,6,6,0),57),
    ((0,6,1,7,0),67),
    ((0,3,4,7,0),47),
    ((0,1,5,8,0),52),
    ((0,2,3,9,0),67)],
    [((0,3,4,5,0),5)],
    [((0,2,0,8,0),104)],
    [((0,2,0,6,0),104)]],
    [[],
    [((0,3,5,7,0),52)],
    [((0,6,2,5,0),104),
    ((0,3,5,5,0),52),
    ((0,5,1,7,0),5),
    ((0,2,4,7,0),104),
    ((0,1,3,9,0),5)],
    [((0,6,2,3,0),104),
    ((0,5,1,5,0),5),
    ((0,2,4,5,0),47),
    ((0,3,2,6,0),67),
    ((0,1,3,7,0),62),
    ((0,2,1,8,0),99)],
    [((0,2,4,3,0),52),
    ((0,3,2,4,0),67),
    ((0,1,3,5,0),57),
    ((0,2,1,6,0),99)]],
    [[((0,3,6,7,0),52)],
    [((0,6,3,5,0),57),
    ((0,3,6,5,0),52),
    ((0,5,2,7,0),52),
    ((0,2,5,7,0),57),
    ((0,1,4,9,0),52)],
    [((0,6,3,3,0),57),
    ((0,5,2,5,0),52),
    ((0,2,5,5,0),57),
    ((0,1,4,7,0),52),
    ((0,2,2,8,0),57)],
    [((0,2,2,6,0),57)],
    [((0,2,2,4,0),5),
    ((0,1,1,6,0),104)],
    [((0,2,2,2,0),5),
    ((0,1,1,4,0),104)]],
    [[((0,6,4,5,0),57),
    ((0,5,3,7,0),52),
    ((0,2,6,7,0),57),
    ((0,1,5,9,0),52)],
    [((0,6,4,3,0),57),
    ((0,5,3,5,0),52),
    ((0,2,6,5,0),57),
    ((0,1,5,7,0),52)],
    [],
    [((0,2,3,4,0),52),
    ((0,1,2,6,0),57)],
    [((0,2,3,2,0),52),
    ((0,1,2,4,0),57)]],
    [[],
    [],
    [((0,2,4,4,0),52),
    ((0,1,3,6,0),57)],
    [((0,2,4,2,0),52),
    ((0,1,3,4,0),57)]]
  ]

def m20 : Blocks :=
  [
    [[],
    [((0,4,4,4,0),108),
    ((0,5,2,5,0),5),
    ((0,0,6,6,0),108),
    ((0,1,4,7,0),5),
    ((0,2,2,8,0),88),
    ((0,3,0,9,0),105)],
    [((0,4,4,2,0),108),
    ((0,5,2,3,0),5),
    ((0,0,6,4,0),108),
    ((0,1,4,5,0),5),
    ((0,2,2,6,0),88),
    ((0,3,0,7,0),105)]],
    [[],
    [],
    [],
    [((0,0,4,3,0),1),
    ((0,1,2,4,0),104)],
    [((0,0,4,1,0),1),
    ((0,1,2,2,0),104)]],
    [[],
    [],
    [((0,4,0,4,0),2),
    ((0,0,2,6,0),2),
    ((0,1,0,7,0),52)],
    [((0,4,0,2,0),2),
    ((0,0,2,4,0),2),
    ((0,1,0,5,0),52)]],
    [[],
    [],
    [],
    [],
    [((0,0,0,3,0),107)],
    [((0,0,0,1,0),107)]],
    [[((0,5,0,5,0),57),
    ((0,0,4,6,0),108),
    ((0,1,2,7,0),57)],
    [((0,5,0,3,0),57),
    ((0,0,4,4,0),108),
    ((0,1,2,5,0),57)]],
    [[],
    [],
    [((0,1,0,4,0),52)],
    [((0,1,0,2,0),52)]],
    [[],
    [((0,0,0,6,0),2)],
    [((0,0,0,4,0),2)]]
  ]

def q20 : Blocks :=
  [
    [],
    [],
    [],
    [[((0,4,7,8,0),21),
    ((0,5,5,9,0),88),
    ((0,4,4,11,0),88)],
    [],
    [((0,3,3,9,0),88),
    ((0,4,1,10,0),21),
    ((0,3,0,12,0),21)]],
    [[((0,4,8,6,0),88),
    ((0,5,6,7,0),21),
    ((0,6,4,8,0),88),
    ((0,3,7,8,0),21),
    ((0,3,4,11,0),88)],
    [((0,7,5,4,0),21),
    ((0,8,3,5,0),88),
    ((0,6,4,6,0),88),
    ((0,3,7,6,0),52),
    ((0,4,5,7,0),57),
    ((0,6,1,9,0),21),
    ((0,3,4,9,0),57)],
    [((0,5,0,9,0),21)],
    [((0,2,3,7,0),57),
    ((0,3,1,8,0),52),
    ((0,2,0,10,0),52)]],
    [[((0,6,5,6,0),21),
    ((0,5,4,8,0),88)],
    [((0,9,2,4,0),88),
    ((0,3,8,4,0),57),
    ((0,4,6,5,0),52),
    ((0,8,1,6,0),21),
    ((0,5,4,6,0),57),
    ((0,2,7,6,0),52),
    ((0,2,4,9,0),57)],
    [((0,6,5,2,0),52),
    ((0,7,3,3,0),57),
    ((0,5,4,4,0),57),
    ((0,5,1,7,0),52)],
    [((0,4,0,7,0),52)]],
    [[((0,3,9,4,0),88),
    ((0,4,7,5,0),21),
    ((0,2,8,6,0),21),
    ((0,2,5,9,0),88)],
    [((0,5,5,4,0),52),
    ((0,4,4,6,0),57)],
    [((0,8,2,2,0),57),
    ((0,7,1,4,0),52)]],
    [[((0,5,6,4,0),21),
    ((0,4,5,6,0),88)],
    [((0,2,9,2,0),57),
    ((0,3,7,3,0),52),
    ((0,1,8,4,0),52),
    ((0,1,5,7,0),57)]],
    [[],
    [((0,4,6,2,0),52),
    ((0,3,5,4,0),57)]]
  ]

def m21 : Blocks :=
  [
    [[],
    [],
    [((0,4,4,2,0),108),
    ((0,0,6,4,0),108),
    ((0,2,2,6,0),88)]],
    [[],
    [((0,5,3,3,0),57),
    ((0,1,5,5,0),57),
    ((0,3,1,7,0),107)],
    [((0,4,2,3,0),1),
    ((0,0,4,5,0),1),
    ((0,2,0,7,0),21)],
    [],
    [((0,0,4,1,0),1)]],
    [[((0,5,4,3,0),57),
    ((0,1,6,5,0),57),
    ((0,3,2,7,0),107)],
    [],
    [],
    [((0,1,3,2,0),52),
    ((0,1,0,5,0),52)],
    [((0,0,2,2,0),108)]],
    [[((0,6,0,5,0),88),
    ((0,1,4,6,0),52),
    ((0,2,2,7,0),88)],
    [],
    [((0,4,1,2,0),1),
    ((0,1,4,2,0),52),
    ((0,0,3,4,0),1)]],
    [[],
    [((0,4,2,2,0),1),
    ((0,5,0,3,0),57),
    ((0,1,2,5,0),57)],
    [((0,2,0,4,0),21)],
    [],
    [((0,0,1,1,0),108)]],
    [[],
    [((0,0,2,5,0),1)],
    [],
    [((0,0,2,1,0),108),
    ((0,1,0,2,0),52)]],
    [],
    [[],
    [((0,0,1,4,0),1)]],
    [[((0,0,2,4,0),1)]]
  ]

def q21 : Blocks :=
  [
    [],
    [],
    [],
    [],
    [[((0,3,7,8,0),57),
    ((0,4,5,9,0),52),
    ((0,3,4,11,0),52)],
    [((0,3,7,6,0),57),
    ((0,4,5,7,0),52),
    ((0,3,4,9,0),52)],
    [((0,2,3,9,0),52),
    ((0,3,1,10,0),57),
    ((0,2,0,12,0),57)],
    [((0,2,3,7,0),52),
    ((0,3,1,8,0),57),
    ((0,2,0,10,0),57)]],
    [[((0,3,8,6,0),52),
    ((0,4,6,7,0),57),
    ((0,5,4,8,0),52),
    ((0,2,7,8,0),57),
    ((0,2,4,11,0),52)],
    [((0,6,5,4,0),57),
    ((0,3,8,4,0),52),
    ((0,7,3,5,0),52),
    ((0,4,6,5,0),57),
    ((0,5,4,6,0),104),
    ((0,2,7,6,0),57),
    ((0,5,1,9,0),57),
    ((0,2,4,9,0),52)],
    [((0,6,5,2,0),57),
    ((0,7,3,3,0),52),
    ((0,5,4,4,0),52),
    ((0,5,1,7,0),57),
    ((0,4,0,9,0),57)],
    [((0,4,0,7,0),57)]],
    [[((0,5,5,6,0),57),
    ((0,4,4,8,0),52)],
    [((0,8,2,4,0),52),
    ((0,5,5,4,0),57),
    ((0,7,1,6,0),57),
    ((0,4,4,6,0),52)],
    [((0,8,2,2,0),52),
    ((0,7,1,4,0),57)]],
    [[((0,2,9,4,0),52),
    ((0,3,7,5,0),57),
    ((0,1,8,6,0),57),
    ((0,1,5,9,0),52)],
    [((0,2,9,2,0),52),
    ((0,3,7,3,0),57),
    ((0,1,8,4,0),57),
    ((0,1,5,7,0),52)]],
    [[((0,4,6,4,0),57),
    ((0,3,5,6,0),52)],
    [((0,4,6,2,0),57),
    ((0,3,5,4,0),52)]]
  ]

def m22 : Blocks :=
  [
    [[((0,5,5,4,0),52),
    ((0,6,3,5,0),57),
    ((0,1,7,6,0),52),
    ((0,5,2,7,0),57),
    ((0,2,5,7,0),57),
    ((0,3,3,8,0),2),
    ((0,4,1,9,0),107),
    ((0,1,4,9,0),57),
    ((0,3,0,11,0),107)]],
    [[((0,7,2,4,0),57),
    ((0,3,4,6,0),57),
    ((0,5,0,8,0),107)],
    [],
    [((0,1,5,3,0),57),
    ((0,2,3,4,0),52),
    ((0,1,2,6,0),52)]],
    [[],
    [((0,4,3,3,0),108),
    ((0,5,1,4,0),1),
    ((0,0,5,5,0),108),
    ((0,4,0,6,0),1),
    ((0,1,3,6,0),1),
    ((0,0,2,8,0),1)],
    [((0,3,2,3,0),52)]],
    [[],
    [((0,6,0,3,0),1),
    ((0,2,2,5,0),1)],
    [],
    [((0,0,3,2,0),1),
    ((0,1,1,3,0),108),
    ((0,0,0,5,0),108)]],
    [[],
    [],
    [],
    [((0,2,0,2,0),108)]],
    [],
    [[((0,0,3,5,0),108),
    ((0,1,1,6,0),1),
    ((0,0,0,8,0),1)]],
    [[((0,2,0,5,0),1)]]
  ]

def q22 : Blocks :=
  [
    [],
    [],
    [],
    [[],
    [((0,3,6,8,0),57),
    ((0,4,4,9,0),42)],
    [((0,3,6,6,0),57),
    ((0,4,4,7,0),42)],
    [((0,2,2,9,0),52),
    ((0,3,0,10,0),67)],
    [((0,2,2,7,0),52),
    ((0,3,0,8,0),67)]],
    [[],
    [((0,3,7,6,0),52),
    ((0,4,5,7,0),67),
    ((0,2,6,8,0),57),
    ((0,3,4,9,0),42)],
    [((0,6,4,4,0),57),
    ((0,3,7,4,0),52),
    ((0,7,2,5,0),42),
    ((0,4,5,5,0),67),
    ((0,5,3,6,0),52),
    ((0,2,6,6,0),57),
    ((0,6,1,7,0),67),
    ((0,3,4,7,0),37)],
    [((0,6,4,2,0),57),
    ((0,7,2,3,0),42),
    ((0,5,3,4,0),52),
    ((0,6,1,5,0),67),
    ((0,3,4,5,0),104)],
    [((0,2,0,8,0),5)],
    [((0,2,0,6,0),5)]],
    [[],
    [((0,3,5,7,0),57)],
    [((0,3,5,5,0),62),
    ((0,2,4,7,0),104)],
    [((0,6,2,3,0),104),
    ((0,3,5,3,0),5),
    ((0,5,1,5,0),5),
    ((0,2,4,5,0),104),
    ((0,2,1,8,0),52)],
    [((0,6,2,1,0),104),
    ((0,5,1,3,0),5),
    ((0,2,1,6,0),52)]],
    [[((0,3,6,7,0),57)],
    [((0,2,8,4,0),52),
    ((0,3,6,5,0),67),
    ((0,1,7,6,0),57),
    ((0,2,5,7,0),99)],
    [((0,2,8,2,0),52),
    ((0,6,3,3,0),57),
    ((0,3,6,3,0),10),
    ((0,1,7,4,0),57),
    ((0,5,2,5,0),52),
    ((0,2,5,5,0),99),
    ((0,2,2,8,0),52)],
    [((0,6,3,1,0),57),
    ((0,5,2,3,0),52),
    ((0,2,2,6,0),52)]],
    [[((0,3,7,5,0),52),
    ((0,2,6,7,0),57)],
    [((0,6,4,3,0),57),
    ((0,3,7,3,0),52),
    ((0,5,3,5,0),52),
    ((0,2,6,5,0),57)],
    [((0,6,4,1,0),57),
    ((0,5,3,3,0),52),
    ((0,2,6,3,0),5),
    ((0,1,5,5,0),104)],
    [((0,2,6,1,0),5),
    ((0,1,5,3,0),104)]],
    [[],
    [((0,2,7,3,0),52),
    ((0,1,6,5,0),57)],
    [((0,2,7,1,0),52),
    ((0,1,6,3,0),57)]],
    [[((0,2,8,3,0),52),
    ((0,1,7,5,0),57)],
    [((0,2,8,1,0),52),
    ((0,1,7,3,0),57)]]
  ]

def h : Blocks :=
  [
    [[((0,3,0,0,0),76),
    ((0,0,3,0,0),1),
    ((0,1,1,1,0),1),
    ((0,0,0,3,0),77)]],
    [[((0,2,0,0,0),1),
    ((0,0,1,1,0),1)]],
    [],
    [[((0,0,0,0,0),1)]]
  ]

def k : Blocks :=
  [
    [[((0,3,0,0,0),33),
    ((0,0,3,0,0),1),
    ((0,1,1,1,0),1),
    ((0,0,0,3,0),34)]],
    [[((0,2,0,0,0),1),
    ((0,0,1,1,0),1)]],
    [],
    [[((0,0,0,0,0),1)]]
  ]

def g : Blocks :=
  [
    [[((0,0,6,0,0),1),
    ((0,3,0,3,0),107)],
    [],
    [],
    [((0,0,0,0,0),1)]],
    [],
    [],
    [],
    [],
    [],
    [[((0,0,0,0,0),1)]]
  ]

end CycleQ2SegreModularTangentData
end


/- Component: continuation_3/SparseGaussianTowers.lean -/
section
/-! Three Horner variables for independent exact Gaussian coefficient checks. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

abbrev Towers := List Blocks

def addTowers : Towers → Towers → Towers
  | [], q => q
  | p, [] => p
  | a::p, b::q => addBlocks a b :: addTowers p q

def mulTowers (p q : Towers) : Towers :=
  p.foldr (fun a acc => addTowers (q.map (mulBlocks a)) ([]::acc)) []

def negTowers (p : Towers) : Towers := p.map negBlocks

def checkTower (p : Towers) (n m l : ℕ) : Bool :=
  checkBlock (p[n]?.getD []) m l

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

def evalTowers (φ : GaussianInt →+* R) (x : Fin 5 → R)
    (z w v : R) : Towers → R
  | [] => 0
  | a::p => evalBlocks φ x w v a + z * evalTowers φ x z w v p

theorem eval_addTowers (x : Fin 5 → R) (z w v : R) (p q : Towers) :
    evalTowers φ x z w v (addTowers p q) =
      evalTowers φ x z w v p + evalTowers φ x z w v q := by
  induction p generalizing q with
  | nil => simp [addTowers, evalTowers]
  | cons a p ih =>
    cases q with
    | nil => simp [addTowers, evalTowers]
    | cons b q => simp only [addTowers, evalTowers, eval_addBlocks, ih]; ring

theorem eval_scaleTowers (x : Fin 5 → R) (z w v : R) (a : Blocks) (q : Towers) :
    evalTowers φ x z w v (q.map (mulBlocks a)) =
      evalBlocks φ x w v a * evalTowers φ x z w v q := by
  induction q with
  | nil => simp [evalTowers]
  | cons b q ih => simp only [List.map_cons, evalTowers, eval_mulBlocks, ih]; ring

theorem eval_mulTowers (x : Fin 5 → R) (z w v : R) (p q : Towers) :
    evalTowers φ x z w v (mulTowers p q) =
      evalTowers φ x z w v p * evalTowers φ x z w v q := by
  induction p with
  | nil => simp [mulTowers, evalTowers]
  | cons a p ih =>
    change evalTowers φ x z w v
      (addTowers (q.map (mulBlocks a)) ([]::mulTowers p q)) = _
    rw [eval_addTowers, eval_scaleTowers, evalTowers, evalBlocks, ih, evalTowers]
    ring

theorem eval_negTowers (x : Fin 5 → R) (z w v : R) (p : Towers) :
    evalTowers φ x z w v (negTowers p) = -evalTowers φ x z w v p := by
  induction p with
  | nil => simp [negTowers, evalTowers]
  | cons a p ih =>
    change evalBlocks φ x w v (negBlocks a) +
      z * evalTowers φ x z w v (negTowers p) = _
    rw [eval_negBlocks, ih, evalTowers]
    ring

theorem evalTowers_eq_zero_of_checks (x : Fin 5 → R) (z w v : R)
    (N M L : ℕ) (p : Towers)
    (hlen : p.length ≤ N)
    (hinner : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M)
    (hdeep : ∀ n : Fin N, ∀ m : Fin M,
      ((p[n.val]?.getD [])[m.val]?.getD []).length ≤ L)
    (h : ∀ n : Fin N, ∀ m : Fin M, ∀ l : Fin L, checkTower p n m l = true) :
    evalTowers φ x z w v p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalTowers]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have hla : a.length ≤ M := by
        simpa only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using hinner 0
      have hda : ∀ m : Fin M, (a[m.val]?.getD []).length ≤ L := by
        intro m
        simpa only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using hdeep 0 m
      have ha : evalBlocks φ x w v a = 0 :=
        evalBlocks_eq_zero_of_checks φ x w v M L a hla hda (fun m l => by
          simpa only [checkTower, Fin.val_zero, List.getElem?_cons_zero, Option.getD_some]
            using h 0 m l)
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hli : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M := by
        intro n
        simpa only [Fin.val_succ, List.getElem?_cons_succ] using hinner n.succ
      have hld : ∀ n : Fin N, ∀ m : Fin M,
          ((p[n.val]?.getD [])[m.val]?.getD []).length ≤ L := by
        intro n m
        simpa only [Fin.val_succ, List.getElem?_cons_succ] using hdeep n.succ m
      have hh : ∀ n : Fin N, ∀ m : Fin M, ∀ l : Fin L,
          checkTower p n m l = true := by
        intro n m l
        simpa only [checkTower, Fin.val_succ, List.getElem?_cons_succ] using h n.succ m l
      rw [evalTowers, ha, ih p hp hli hld hh, mul_zero, add_zero]

end Soundness
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.evalTowers_eq_zero_of_checks
#print axioms CycleQ2SparseGaussianPolynomial.eval_mulTowers
end


/- Component: continuation_3/CurveRestrictionIndices.lean -/
section
/-! Exhaustive finite monomial indices for the two curve restrictions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2CurveRestriction

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceGradedBasis

abbrev TargetRawIndex (s : Side) (d : ℕ) :=
  Fin (xBound s) × Fin (zBound s) × Fin (d+1)

def TargetAllowed (s : Side) (d : ℕ) (q : TargetRawIndex s d) : Prop :=
  q.1.val + q.2.1.val + q.2.2.val ≤ d

instance (s : Side) (d : ℕ) (q : TargetRawIndex s d) : Decidable (TargetAllowed s d q) :=
  inferInstanceAs (Decidable (_ ≤ _))

abbrev TargetIndex (s : Side) (d : ℕ) := {q : TargetRawIndex s d // TargetAllowed s d q}

def targetCoordinates {s : Side} {d : ℕ} (q : TargetIndex s d) : Fin 4 → ℕ :=
  ![q.val.1.val, q.val.2.2.val, q.val.2.1.val,
    d-(q.val.1.val+q.val.2.1.val+q.val.2.2.val)]

abbrev TargetExponents (s : Side) (d : ℕ) :=
  {e : Fin 4 → ℕ // e 0 < xBound s ∧ e 2 < zBound s ∧ e 0+e 1+e 2+e 3=d}

def targetExponentEquiv (s : Side) (d : ℕ) : TargetIndex s d ≃ TargetExponents s d where
  toFun q := ⟨targetCoordinates q, by
    have h := q.property
    change q.val.1.val<xBound s ∧ q.val.2.1.val<zBound s ∧
      q.val.1.val+q.val.2.2.val+q.val.2.1.val+
        (d-(q.val.1.val+q.val.2.1.val+q.val.2.2.val))=d
    exact ⟨q.val.1.isLt,q.val.2.1.isLt,by dsimp [TargetAllowed] at h; omega⟩⟩
  invFun e := ⟨(⟨e.val 0,e.property.1⟩,⟨e.val 2,e.property.2.1⟩,
    ⟨e.val 1,by have := e.property.2.2; omega⟩), by
      have := e.property.2.2
      change e.val 0+e.val 2+e.val 1≤d
      omega⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv e := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change d-(e.val 0+e.val 2+e.val 1)=e.val 3
      have := e.property.2.2
      omega

def targetExponent {s : Side} {d : ℕ} (q : TargetIndex s d) : CurveExponent :=
  exponent (targetCoordinates q)

@[simp] theorem targetExponent_apply {s : Side} {d : ℕ} (q : TargetIndex s d) (i : Fin 4) :
    targetExponent q i = targetCoordinates q i := rfl

theorem targetExponent_injective {s : Side} {d : ℕ} :
    Function.Injective (targetExponent (s:=s) (d:=d)) := by
  intro q q' h
  apply (targetExponentEquiv s d).injective
  apply Subtype.ext
  funext i
  exact congrArg (fun e : CurveExponent => e i) h

theorem left_target_count : Fintype.card (TargetIndex .left 10) = 57 := by decide

theorem right_target_count : Fintype.card (TargetIndex .right 8) = 45 := by decide

abbrev SourceRawIndex (d : ℕ) := (Fin 3 × Fin 3) × (Fin (d+1) × Fin (d+1))

def SourceAllowed (d ch : ℕ) (q : SourceRawIndex d) : Prop :=
  q.1.1.val+q.2.1.val+q.2.2.val+2*q.1.2.val≤d ∧
    (2*q.1.1.val+2*q.2.1.val+q.2.2.val)%3=ch

instance (d ch : ℕ) (q : SourceRawIndex d) : Decidable (SourceAllowed d ch q) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev SourceIndex (d ch : ℕ) := {q : SourceRawIndex d // SourceAllowed d ch q}

def sourceCoordinates {d ch : ℕ} (q : SourceIndex d ch) : Fin 5 → ℕ :=
  ![q.val.1.1.val,q.val.2.1.val,q.val.2.2.val,
    d-(q.val.1.1.val+q.val.2.1.val+q.val.2.2.val+2*q.val.1.2.val),q.val.1.2.val]

abbrev SourceExponents (d ch : ℕ) :=
  {e : Fin 5 → ℕ // e 0<3 ∧ e 4<3 ∧
    e 0+e 1+e 2+e 3+2*e 4=d ∧ (2*e 0+2*e 1+e 2)%3=ch}

def sourceExponentEquiv (d ch : ℕ) : SourceIndex d ch ≃ SourceExponents d ch where
  toFun q := ⟨sourceCoordinates q, by
    have hw := q.property.1
    have hc := q.property.2
    change q.val.1.1.val<3 ∧ q.val.1.2.val<3 ∧
      q.val.1.1.val+q.val.2.1.val+q.val.2.2.val+
        (d-(q.val.1.1.val+q.val.2.1.val+q.val.2.2.val+2*q.val.1.2.val))+
        2*q.val.1.2.val=d ∧ (2*q.val.1.1.val+2*q.val.2.1.val+q.val.2.2.val)%3=ch
    exact ⟨q.val.1.1.isLt,q.val.1.2.isLt,by omega,hc⟩⟩
  invFun e := ⟨((⟨e.val 0,e.property.1⟩,⟨e.val 4,e.property.2.1⟩),
    (⟨e.val 1,by have := e.property.2.2.1; omega⟩,
     ⟨e.val 2,by have := e.property.2.2.1; omega⟩)), by
    constructor
    · have := e.property.2.2.1
      change e.val 0+e.val 1+e.val 2+2*e.val 4≤d
      omega
    · exact e.property.2.2.2⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv e := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change d-(e.val 0+e.val 1+e.val 2+2*e.val 4)=e.val 3
      have := e.property.2.2.1
      omega
    · rfl

def sourceExponent {d ch : ℕ} (q : SourceIndex d ch) : FullExponent :=
  Finsupp.equivFunOnFinite.symm (sourceCoordinates q)

@[simp] theorem sourceExponent_apply {d ch : ℕ} (q : SourceIndex d ch) (i : Fin 5) :
    sourceExponent q i = sourceCoordinates q i := rfl

theorem sourceExponent_injective {d ch : ℕ} :
    Function.Injective (sourceExponent (d:=d) (ch:=ch)) := by
  intro q q' h
  apply (sourceExponentEquiv d ch).injective
  apply Subtype.ext
  funext i
  exact congrArg (fun e : FullExponent => e i) h

theorem left_source_count : Fintype.card (SourceIndex 10 0) = 113 := by decide

theorem right_source_count : Fintype.card (SourceIndex 8 1) = 68 := by decide

theorem targetExponent_degree {s : Side} {d : ℕ} (q : TargetIndex s d) :
    (targetExponent q).degree=d := by
  have h := ((targetExponentEquiv s d) q).property.2.2
  change targetCoordinates q 0+targetCoordinates q 1+targetCoordinates q 2+targetCoordinates q 3=d at h
  simpa [Finsupp.degree_eq_sum,Fin.sum_univ_succ,add_assoc] using h

theorem sourceExponent_grade {d ch : ℕ} (q : SourceIndex d ch) :
    Finsupp.weight fullGrading (sourceExponent q)=(d,(ch : ZMod 3)) := by
  have h := ((sourceExponentEquiv d ch) q).property
  rw [fullGrading_weight]
  apply Prod.ext
  · exact h.2.2.1
  · change ((2*sourceCoordinates q 0+2*sourceCoordinates q 1+sourceCoordinates q 2 : ℕ) : ZMod 3)=_
    have hc : (2*sourceCoordinates q 0+2*sourceCoordinates q 1+sourceCoordinates q 2)%3=ch := h.2.2.2
    simpa using congrArg (fun n : ℕ => (n : ZMod 3)) hc

theorem sourceMonomial_standard {R : Type*} [CommRing R] {d ch : ℕ}
    (q : SourceIndex d ch) (c : R) : FullStandard (monomial (sourceExponent q) c) := by
  intro e he
  obtain rfl := Finset.mem_singleton.mp (support_monomial_subset he)
  have h := ((sourceExponentEquiv d ch) q).property
  exact ⟨h.1,h.2.1⟩

theorem sourceMonomial_homogeneous {R : Type*} [CommRing R] {d ch : ℕ}
    (q : SourceIndex d ch) (c : R) :
    (monomial (sourceExponent q) c).IsWeightedHomogeneous fullGrading (d,(ch : ZMod 3)) :=
  isWeightedHomogeneous_monomial _ _ _ (sourceExponent_grade q)

section CurveBasis
variable {R : Type*} [CommRing R] [Nontrivial R]

theorem curve_reduced_exponent_iff (s : Side) (r ι : R) (e : CurveExponent) :
    e ∈ reducedExponents (curveOrder s) (quadric s r) (cubic s r ι) ↔
      e 0<xBound s ∧ e 2<zBound s := by
  change (¬ (curveOrder s).degree (quadric s r)≤e) ∧
    (¬ (curveOrder s).degree (cubic s r ι)≤e) ↔ _
  rw [(quadric_leading s r).1,(cubic_leading s r ι).1]
  cases s <;> simp only [quadricLead,cubicLead,Finsupp.single_le_iff,xBound,zBound] <;> omega

def curveGradedExponentEquiv (s : Side) (r ι : R) (d : ℕ) :
    gradedExponents (1 : Fin 4 → ℕ) (curveOrder s) (quadric s r) (cubic s r ι) d ≃
      TargetExponents s d where
  toFun e := ⟨e.val, by
    have hb := (curve_reduced_exponent_iff s r ι e.val).mp e.property.1
    refine ⟨hb.1,hb.2,?_⟩
    have hd := e.property.2
    simp only [Pi.one_def] at hd
    rw [← Finsupp.degree_eq_weight_one] at hd
    simpa [Finsupp.degree_eq_sum,Fin.sum_univ_succ,add_assoc] using hd⟩
  invFun e := ⟨exponent e.val, by
    constructor
    · apply (curve_reduced_exponent_iff s r ι _).mpr
      exact ⟨e.property.1,e.property.2.1⟩
    · simp only [Pi.one_def]
      rw [← Finsupp.degree_eq_weight_one]
      simpa [Finsupp.degree_eq_sum,Fin.sum_univ_succ,add_assoc] using e.property.2.2⟩
  left_inv e := by apply Subtype.ext; exact Finsupp.equivFunOnFinite.symm_apply_apply e.val
  right_inv e := by apply Subtype.ext; rfl

abbrev CurvePiece (s : Side) (r ι : R) (d : ℕ) :=
  quotientPiece (1 : Fin 4 → ℕ) (quadric s r) (cubic s r ι) d

def curvePieceBasis (s : Side) (r ι : R) (d : ℕ) :
    Module.Basis (TargetIndex s d) R (CurvePiece s r ι d) :=
  (CycleQ2IncidenceGradedBasis.basis (1 : Fin 4 → ℕ) (curveOrder s)
    (quadric s r) (cubic s r ι) d (quadric_leading s r).2
    (cubic_leading s r ι).2 (leading_coprime s r ι)
    (quadric_homogeneous s r) (cubic_homogeneous s r ι)).reindex
      ((curveGradedExponentEquiv s r ι d).trans (targetExponentEquiv s d).symm)

theorem curvePieceBasis_apply (s : Side) (r ι : R) (d : ℕ) (q : TargetIndex s d) :
    (curvePieceBasis s r ι d q).val =
      Ideal.Quotient.mk (curveIdeal s r ι) (monomial (targetExponent q) 1) := by
  rw [curvePieceBasis,Module.Basis.reindex_apply,CycleQ2IncidenceGradedBasis.basis_apply]
  rfl

theorem left_curvePiece_rank (r ι : R) : Module.finrank R (CurvePiece .left r ι 10) = 57 := by
  rw [Module.finrank_eq_card_basis (curvePieceBasis .left r ι 10),left_target_count]

theorem right_curvePiece_rank (r ι : R) : Module.finrank R (CurvePiece .right r ι 8) = 45 := by
  rw [Module.finrank_eq_card_basis (curvePieceBasis .right r ι 8),right_target_count]

end CurveBasis
end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.left_source_count
#print axioms CycleQ2CurveRestriction.right_source_count
#print axioms CycleQ2CurveRestriction.left_curvePiece_rank
#print axioms CycleQ2CurveRestriction.right_curvePiece_rank
end
end


