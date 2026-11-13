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
import Proposal.GeometricTarget02

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


/- Component: continuation_3/CurveRestrictionReflection.lean -/
section
/-! Soundness of the finite polynomial and coefficient checks used by the
curve restriction minors. All executable checks use natural numbers and lists. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestrictionReflection

open MvPolynomial CycleQ2CurveRestriction CycleQ2SparseModularPolynomial

abbrev CurveTuple := ℕ × ℕ × ℕ × ℕ

def curveTuple (e : Exponent) : CurveTuple := (e.1,e.2.1,e.2.2.1,e.2.2.2.1)

def coefficient (e : CurveTuple) : Sparse → ℕ
  | [] => 0
  | a::p => ((if curveTuple a.1=e then a.2 else 0)+coefficient e p)%109

def goodTerm (s : Side) (d : ℕ) (a : Term) : Bool :=
  decide (a.1.1<xBound s ∧ a.1.2.2.1<zBound s ∧
    a.1.1+a.1.2.1+a.1.2.2.1+a.1.2.2.2.1=d)

def goodPolynomial (s : Side) (d : ℕ) (p : Sparse) : Bool := p.all (goodTerm s d)

def residual (p n a b q h : Sparse) : Sparse :=
  add p (neg (add n (add (mul a q) (mul b h))))

noncomputable section
variable {R : Type*} [CommRing R]

def tupleExponent (e : CurveTuple) : CurveExponent :=
  exponent ![e.1,e.2.1,e.2.2.1,e.2.2.2]

def sourceTupleExponent (e : Exponent) : CycleQ2IncidenceNormalForm.FullExponent :=
  Finsupp.equivFunOnFinite.symm ![e.1,e.2.1,e.2.2.1,e.2.2.2.1,e.2.2.2.2]

def sourceMonomial (e : Exponent) : MvPolynomial (Fin 5) R :=
  X 0^e.1*X 1^e.2.1*X 2^e.2.2.1*X 3^e.2.2.2.1*X 4^e.2.2.2.2

theorem sourceMonomial_eq_monomial (e : Exponent) :
    (sourceMonomial e : MvPolynomial (Fin 5) R) = MvPolynomial.monomial (sourceTupleExponent e) 1 := by
  simp only [sourceMonomial, X_pow_eq_monomial, monomial_mul, one_mul]
  apply congrArg (fun f : Fin 5 →₀ ℕ => MvPolynomial.monomial f (1 : R))
  ext i
  fin_cases i <;> simp [sourceTupleExponent,Finsupp.single_apply,Fin.ext_iff]

@[simp] theorem map_sourceMonomial {S : Type*} [CommRing S] (φ : R →+* S) (e : Exponent) :
    MvPolynomial.map φ (sourceMonomial e) = sourceMonomial e := by
  simp [sourceMonomial]

def curveVariables : Fin 5 → CurvePoly R := ![X 0,X 1,X 2,X 3,1]

def value [CharP R 109] (p : Sparse) : CurvePoly R := eval curveVariables p

@[simp] theorem value_nil [CharP R 109] : value (R:=R) []=0 := rfl

@[simp] theorem value_cons [CharP R 109] (a : Term) (p : Sparse) :
    value (R:=R) (a::p)=termValue curveVariables a+value p := rfl

theorem tupleExponent_injective : Function.Injective tupleExponent := by
  intro e f h
  have h0 := congrArg (fun q : CurveExponent => q 0) h
  have h1 := congrArg (fun q : CurveExponent => q 1) h
  have h2 := congrArg (fun q : CurveExponent => q 2) h
  have h3 := congrArg (fun q : CurveExponent => q 3) h
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))

theorem monomial_curveVariables [CharP R 109] (e : Exponent) :
    CycleQ2SparseModularPolynomial.monomial (curveVariables (R:=R)) e =
      MvPolynomial.monomial (tupleExponent (curveTuple e)) 1 := by
  change (X 0^e.1*X 1^e.2.1*X 2^e.2.2.1*X 3^e.2.2.2.1*(1 : CurvePoly R)^e.2.2.2.2)=_
  rw [one_pow,mul_one]
  exact mon_eq_monomial _ _ _ _

theorem termValue_curveVariables [CharP R 109] (a : Term) :
    termValue (curveVariables (R:=R)) a =
      MvPolynomial.monomial (tupleExponent (curveTuple a.1)) (a.2:R) := by
  rw [termValue,monomial_curveVariables]
  rw [←map_natCast (C : R →+* CurvePoly R) a.2,C_mul_monomial,mul_one]

theorem value_coefficient [CharP R 109] (e : CurveTuple) (p : Sparse) :
    (value (R:=R) p).coeff (tupleExponent e)=(coefficient e p:R) := by
  induction p with
  | nil => simp [coefficient]
  | cons a p ih =>
    rw [value_cons,coeff_add,termValue_curveVariables,coeff_monomial,ih]
    by_cases he : curveTuple a.1=e
    · simp [coefficient,he,←CharP.cast_eq_mod R 109,Nat.cast_add]
    · have he' : tupleExponent (curveTuple a.1)≠tupleExponent e :=
        fun h => he (tupleExponent_injective h)
      simp only [coefficient,if_neg he,if_neg he',←CharP.cast_eq_mod R 109,Nat.cast_add,Nat.cast_zero]

theorem goodTerm_value [CharP R 109] (s : Side) (d : ℕ) (a : Term)
    (ha : goodTerm s d a=true) :
    Standard s (termValue (curveVariables (R:=R)) a) ∧
      (termValue (curveVariables (R:=R)) a).IsHomogeneous d := by
  have h : a.1.1<xBound s ∧ a.1.2.2.1<zBound s ∧
      a.1.1+a.1.2.1+a.1.2.2.1+a.1.2.2.2.1=d := of_decide_eq_true ha
  rw [termValue_curveVariables]
  constructor
  · intro e he
    have heq : e=tupleExponent (curveTuple a.1) :=
      Finset.mem_singleton.mp (support_monomial_subset he)
    subst e
    exact ⟨h.1,h.2.1⟩
  · apply isHomogeneous_monomial
    simpa [tupleExponent,curveTuple,Finsupp.degree_eq_sum,Fin.sum_univ_succ,
      Matrix.cons_val_succ,Fin.reduceSucc,add_assoc] using h.2.2

theorem goodPolynomial_value [CharP R 109] (s : Side) (d : ℕ) (p : Sparse)
    (hp : goodPolynomial s d p=true) :
    Standard s (value (R:=R) p) ∧ (value (R:=R) p).IsHomogeneous d := by
  induction p with
  | nil => exact ⟨by simp [Standard],(homogeneousSubmodule (Fin 4) R d).zero_mem⟩
  | cons a p ih =>
    simp only [goodPolynomial,List.all_cons,Bool.and_eq_true] at hp
    have ha := goodTerm_value (R:=R) s d a hp.1
    have hb := ih hp.2
    rw [value_cons]
    exact ⟨standard_add ha.1 hb.1,ha.2.add hb.2⟩

theorem checked_normal [CharP R 109] [Nontrivial R]
    (s : Side) (r ι : R) (d : ℕ) (p n a b q h : Sparse)
    (hq : value (R:=R) q=quadric s r) (hh : value (R:=R) h=cubic s r ι)
    (hn : goodPolynomial s d n=true) (hc : checkZero (residual p n a b q h)=true) :
    normal s r ι (value p)=value n := by
  have hz := eval_eq_zero_of_check (curveVariables (R:=R)) _ hc
  simp only [residual,CycleQ2SparseModularPolynomial.eval_add,
    CycleQ2SparseModularPolynomial.eval_neg,CycleQ2SparseModularPolynomial.eval_mul] at hz
  change value p+ -(value n+(value a*value q+value b*value h))=0 at hz
  rw [hq,hh] at hz
  symm
  apply normal_unique
  · exact (goodPolynomial_value s d n hn).1
  · refine ⟨value a,value b,?_⟩
    linear_combination hz

def matrixCoefficient [Nontrivial R] (s : Side) (r ι : R)
    (row : CurveTuple) (column : Exponent) : R :=
  (restrictionNormal s r ι (sourceMonomial column)).coeff (tupleExponent row)

theorem matrixCoefficient_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (row : CurveTuple) (column : Exponent) :
    φ (matrixCoefficient s r ι row column)=matrixCoefficient s (φ r) (φ ι) row column := by
  unfold matrixCoefficient
  rw [←coeff_map,restrictionNormal_map,map_sourceMonomial]

end
end CycleQ2CurveRestrictionReflection

#print axioms CycleQ2CurveRestrictionReflection.checked_normal
#print axioms CycleQ2CurveRestrictionReflection.value_coefficient
#print axioms CycleQ2CurveRestrictionReflection.matrixCoefficient_map
end


/- Component: continuation_3/IncidenceJacobian.lean -/
section
/-! # The actual first-order coefficient equations

The normal-form derivative includes both moving equations.  The formula below
is proved by an equality of the actual incidence equations over every ring with
a square-zero element; it is not an assumed identification of a numerical matrix.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceJacobian

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder

variable {R : Type*} [CommRing R]

theorem fullStandard_add {p q : Poly R} (hp : FullStandard p) (hq : FullStandard q) :
    FullStandard (p + q) := by
  intro e he
  rcases Finset.mem_union.mp (support_add he) with h | h
  · exact hp e h
  · exact hq e h

theorem fullStandard_C_mul {p : Poly R} (hp : FullStandard p) (c : R) :
    FullStandard (C c * p) := by
  intro e he
  apply hp e
  apply mem_support_iff.mpr
  intro hz
  exact (mem_support_iff.mp he) (by rw [coeff_C_mul, hz, mul_zero])

theorem fullRemainder_add [Nontrivial R]
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex))
    (p q : Poly R) :
    fullRemainder hc Fc hu Fu (p + q) =
      fullRemainder hc Fc hu Fu p + fullRemainder hc Fc hu Fu q := by
  obtain ⟨hp, a, b, hab⟩ := fullRemainder_spec hc Fc hu Fu p
  obtain ⟨hq, c, d, hcd⟩ := fullRemainder_spec hc Fc hu Fu q
  symm
  apply (existsUnique_full_invariant_representative hc Fc hu Fu (p + q)).choose_spec.2
  refine ⟨fullStandard_add hp hq, a + c, b + d, ?_⟩
  linear_combination hab + hcd

theorem fullRemainder_C_mul [Nontrivial R]
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex))
    (c : R) (p : Poly R) :
    fullRemainder hc Fc hu Fu (C c * p) = C c * fullRemainder hc Fc hu Fu p := by
  obtain ⟨hp, a, b, hab⟩ := fullRemainder_spec hc Fc hu Fu p
  symm
  apply (existsUnique_full_invariant_representative hc Fc hu Fu (C c * p)).choose_spec.2
  refine ⟨fullStandard_C_mul hp c, C c * a, C c * b, ?_⟩
  linear_combination C c * hab

def fullRemainderLinear [Nontrivial R]
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex)) :
    Poly R →ₗ[R] Poly R where
  toFun := fullRemainder hc Fc hu Fu
  map_add' := fullRemainder_add hc Fc hu Fu
  map_smul' := fun c p ↦ by
    simpa only [smul_eq_C_mul, RingHom.id_apply] using fullRemainder_C_mul hc Fc hu Fu c p

def fullFirstOrderResidual (r ι : R) (H J : Poly R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R)) : Matrix (Fin 3) (Fin 3) (Poly R) :=
  fun i j ↦ firstOrderResidual r ι H N i j - J * rawCofactorQuotient r i j

theorem full_cofactor_seed_deformation (r ι : R) (H J t : Poly R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    CycleQ2SegreLocal.cofactors (fun i j ↦ rawSeedMatrix r i j + t * N i j) i j =
      -(smoothK ι * rawCofactorQuotient r i j) * (smoothH ι + t * H) +
        rawCofactorQuotient r i j * (smoothF r ι + t * J) +
        t * fullFirstOrderResidual r ι H J N i j +
        t ^ 2 * CycleQ2SegreLocal.cofactors N i j := by
  rw [cofactor_seed_deformation r ι H t N i j]
  unfold fullFirstOrderResidual
  ring

def deformedSexticCoefficients (r ι t : R) (ζ : FullInvariantIndex 6 → R) :
    FullInvariantIndex 6 → R := fun e ↦ seedSexticCoefficients r ι e + t * ζ e

theorem deformedSexticCoefficients_polynomial (r ι t : R) (ζ : FullInvariantIndex 6 → R) :
    fullInvariantPolynomial 6 (deformedSexticCoefficients r ι t ζ) =
      smoothF r ι + C t * fullInvariantPolynomial 6 ζ := by
  rw [← seedSexticCoefficients_polynomial]
  simp [fullInvariantPolynomial, deformedSexticCoefficients, map_add,
    Finset.sum_add_distrib, Finset.mul_sum, C_mul_monomial]

theorem deformedSexticCoefficients_unit (r ι t : R) (ζ : FullInvariantIndex 6 → R)
    (ht : t ^ 2 = 0) : IsUnit (deformedSexticCoefficients r ι t ζ fullSexticLeadingIndex) := by
  simp only [deformedSexticCoefficients, seedSexticCoefficients,
    fullSexticLeadingIndex_exponent, smoothF_leading_coefficient]
  apply IsUnit.of_mul_eq_one (1 - t * ζ fullSexticLeadingIndex)
  calc
    (1 + t * ζ fullSexticLeadingIndex) * (1 - t * ζ fullSexticLeadingIndex) =
        1 - t ^ 2 * (ζ fullSexticLeadingIndex) ^ 2 := by ring
    _ = 1 := by rw [ht]; ring

/-- The full first-order remainder, proved by the uniqueness of the concrete
normal form over the deformed leading-unit chart. -/
theorem infinitesimal_remainder_eq [Nontrivial R]
    (r ι t : R) (ht : t ^ 2 = 0)
    (η : FullInvariantIndex 3 → R) (ζ : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (i j : Fin 3) :
    fullRemainder (deformedCubicCoefficients ι t η) (deformedSexticCoefficients r ι t ζ)
      (deformedCubicCoefficients_unit ι t η ht) (deformedSexticCoefficients_unit r ι t ζ ht)
      (CycleQ2SegreLocal.cofactors (incidenceMatrix r (fun i j e ↦ t * δ i j e)) i j) =
        C t * fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
          (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
          (fullFirstOrderResidual r ι (fullInvariantPolynomial 3 η)
            (fullInvariantPolynomial 6 ζ) (perturbation δ) i j) := by
  obtain ⟨hstd, a, b, hab⟩ := fullRemainder_spec (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (seedCubicCoefficients_unit ι)
    (seedSexticCoefficients_unit r ι)
    (fullFirstOrderResidual r ι (fullInvariantPolynomial 3 η)
      (fullInvariantPolynomial 6 ζ) (perturbation δ) i j)
  rw [seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial] at hab
  symm
  apply (existsUnique_full_invariant_representative
    (deformedCubicCoefficients ι t η) (deformedSexticCoefficients r ι t ζ)
    (deformedCubicCoefficients_unit ι t η ht) (deformedSexticCoefficients_unit r ι t ζ ht)
    (CycleQ2SegreLocal.cofactors (incidenceMatrix r (fun i j e ↦ t * δ i j e)) i j)).choose_spec.2
  refine ⟨fullStandard_C_mul hstd t,
    -(smoothK ι * rawCofactorQuotient r i j) + C t * a,
    rawCofactorQuotient r i j + C t * b, ?_⟩
  rw [deformedCubicCoefficients_polynomial, deformedSexticCoefficients_polynomial,
    incidenceMatrix_scaled, full_cofactor_seed_deformation r ι (fullInvariantPolynomial 3 η)
      (fullInvariantPolynomial 6 ζ) (C t) (perturbation δ) i j]
  have ht' : (C t : Poly R) ^ 2 = 0 := by rw [← map_pow, ht, map_zero]
  linear_combination C t * hab +
    (CycleQ2SegreLocal.cofactors (perturbation δ) i j -
      a * fullInvariantPolynomial 3 η - b * fullInvariantPolynomial 6 ζ) * ht'

def linearizedEquations [Nontrivial R] (r ι : R)
    (η : FullInvariantIndex 3 → R) (ζ : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (q : EquationIndex) : R :=
  (fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
    (fullFirstOrderResidual r ι (fullInvariantPolynomial 3 η)
      (fullInvariantPolynomial 6 ζ) (perturbation δ) q.1.1 q.1.2)).coeff (standardExponent q.2)

/-- Exact first-jet identity for each of the actual 9522 coefficient equations. -/
theorem infinitesimal_incidenceEquations_eq [Nontrivial R]
    (r ι t : R) (ht : t ^ 2 = 0)
    (η : FullInvariantIndex 3 → R) (ζ : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (q : EquationIndex) :
    incidenceEquations (deformedCubicCoefficients ι t η) (deformedSexticCoefficients r ι t ζ)
      (deformedCubicCoefficients_unit ι t η ht) (deformedSexticCoefficients_unit r ι t ζ ht)
      r (fun i j e ↦ t * δ i j e) q = t * linearizedEquations r ι η ζ δ q := by
  unfold incidenceEquations cofactorEquations linearizedEquations
  rw [infinitesimal_remainder_eq r ι t ht η ζ δ q.1.1 q.1.2, coeff_C_mul]

end CycleQ2IncidenceJacobian

#print axioms CycleQ2IncidenceJacobian.fullRemainderLinear
#print axioms CycleQ2IncidenceJacobian.infinitesimal_incidenceEquations_eq
end
end


/- Component: continuation_3/IncidencePolynomialPresentation.lean -/
section
/-!
# Genuine polynomial representatives of the actual incidence equations

Localization supplies an ordinary polynomial numerator for each of the
9522 universal remainder equations.  On the actual principal open, their
vanishing is exactly equivalent to incidence.  Differentiating the proved
denominator identity gives the expected nonzero row scaling at every seed
solution, rather than assuming that the localized remainders are globally
polynomial in unconstrained inverse variables.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CycleQ2IncidencePolynomialPresentation

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart

variable (R : Type*) [CommRing R] [IsDomain R]

def numerator (r : R) (q : EquationIndex) : ParameterPolynomial R :=
  (IsLocalization.Away.sec (leadingProduct R) (equations R r q)).1

def denominatorExponent (r : R) (q : EquationIndex) : ℕ :=
  (IsLocalization.Away.sec (leadingProduct R) (equations R r q)).2

theorem denominator_identity (r : R) (q : EquationIndex) :
    equations R r q * algebraMap (ParameterPolynomial R) (ParameterRing R)
      (leadingProduct R ^ denominatorExponent R r q) =
        algebraMap (ParameterPolynomial R) (ParameterRing R) (numerator R r q) :=
  IsLocalization.Away.sec_spec (leadingProduct R) (equations R r q)

theorem denominator_isUnit (r : R) (q : EquationIndex) :
    IsUnit (algebraMap (ParameterPolynomial R) (ParameterRing R)
      (leadingProduct R ^ denominatorExponent R r q)) := by
  rw [map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit (S := ParameterRing R) (leadingProduct R)).pow _

section Specialization

variable {R} {S : Type*} [CommRing S] [Nontrivial S] [Algebra R S]

theorem numerator_specialization
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) (q : EquationIndex) :
    polynomialSpecialization hcoeff Fcoeff δ (numerator R r q) =
      incidenceEquations hcoeff Fcoeff hu Fu (algebraMap R S r) δ q *
        (hcoeff fullCubicLeadingIndex * Fcoeff fullSexticLeadingIndex) ^
          denominatorExponent R r q := by
  have hm := congrArg (specialization hcoeff Fcoeff hu Fu δ) (denominator_identity R r q)
  rw [map_mul, specialization_equations, specialization_polynomial,
    specialization_polynomial, map_pow, polynomialSpecialization_leadingProduct] at hm
  exact hm.symm

theorem numerator_zero_iff
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) (q : EquationIndex) :
    polynomialSpecialization hcoeff Fcoeff δ (numerator R r q) = 0 ↔
      incidenceEquations hcoeff Fcoeff hu Fu (algebraMap R S r) δ q = 0 := by
  rw [numerator_specialization hcoeff Fcoeff hu Fu δ r q]
  have hd := (hu.mul Fu).pow (denominatorExponent R r q)
  exact hd.mul_left_eq_zero

/-- The chosen ordinary polynomial system has exactly the actual incidence
solutions on the two-leading-coefficient open. -/
theorem polynomial_system_zero_iff
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) :
    (∀ q, polynomialSpecialization hcoeff Fcoeff δ (numerator R r q) = 0) ↔
      ∀ i j, CycleQ2SegreLocal.cofactors (incidenceMatrix (algebraMap R S r) δ) i j ∈
        equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) := by
  rw [← incidenceEquations_zero_iff hcoeff Fcoeff hu Fu (algebraMap R S r) δ]
  exact forall_congr' (fun q => numerator_zero_iff hcoeff Fcoeff hu Fu δ r q)

end Specialization

theorem polynomial_seed_zero (r ι : R) (q : EquationIndex) :
    polynomialSpecialization (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (fun _ _ _ => 0) (numerator R r q) = 0 := by
  apply (numerator_zero_iff (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
    (fun _ _ _ => 0) r q).mpr
  simpa using smoothSeed_equations_zero r ι q

section Derivative

variable {S : Type*} [CommRing S] [Algebra (ParameterRing R) S]

/-- At an actual incidence solution, numerator differentiation differs from
the intrinsic localized equation only by its invertible denominator factor.
This applies simultaneously to every coordinate derivation of the parameter
space and justifies transferring a Jacobian minor to polynomial equations. -/
theorem numerator_differential_at_solution (r : R) (q : EquationIndex)
    (D : Derivation ℤ (ParameterRing R) S)
    (hzero : algebraMap (ParameterRing R) S (equations R r q) = 0) :
    D (algebraMap (ParameterPolynomial R) (ParameterRing R) (numerator R r q)) =
      algebraMap (ParameterRing R) S
        (algebraMap (ParameterPolynomial R) (ParameterRing R)
          (leadingProduct R ^ denominatorExponent R r q)) * D (equations R r q) := by
  rw [← denominator_identity, Derivation.leibniz]
  simp only [Algebra.smul_def, hzero, zero_mul, zero_add]

end Derivative

end CycleQ2IncidencePolynomialPresentation

#print axioms CycleQ2IncidencePolynomialPresentation.polynomial_system_zero_iff
#print axioms CycleQ2IncidencePolynomialPresentation.polynomial_seed_zero
#print axioms CycleQ2IncidencePolynomialPresentation.numerator_differential_at_solution
end
end


/- Component: continuation_3/cylinder_bridge/PointedCompatibleAffineLifting.lean -/
section
/-! A compatible affine incidence slice has a finite generic point on a
component through the actual nonsingular seed.  The extra conclusion is
an implication for the original parameter polynomials, obtained from the
proved containment of prime ideals in the Jacobian-localized algebra. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PointedCompatibleAffineLifting
open MvPolynomial Matrix HoldoutConstruction
  CycleQ2PolynomialAffineSlice CycleQ2CompatibleEquationCoordinates
  CycleQ2SlicedCompatibleSystem CycleQ2CompatibleAffineGenericLifting

variable {R S T K m l ι κ σ : Type*}
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ] [Fintype σ]
  [DecidableEq m] [DecidableEq ι] [DecidableEq κ]

theorem affine_lift_semantics
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R)
    (hdecomp : Q*P+V*W=1) (hrelations : D*ᵥe=0)
    (x : ι → S) (hP : ∀q, aeval x (equations a B P e q)=0)
    (hopen : IsUnit (aeval x (substitute a B c*(relationA a B T₀ D V).det))) :
    (∀q, aeval (pointValue (algebraMap R S) a B x) (e q)=0) ∧
      IsUnit (aeval (pointValue (algebraMap R S) a B x) c) := by
  let φ : MvPolynomial ι R →+* S := (aeval x).toRingHom
  have hprod : IsUnit (aeval x (substitute a B c)*aeval x (relationA a B T₀ D V).det) :=
    (congrArg IsUnit ((aeval x).map_mul _ _)).mp hopen
  have heq : φ ∘ equations a B P e=0 := funext hP
  have hres := CycleQ2SegreRelations.evaluated_residual_eq_zero φ
    (relationA a B T₀ D V) (relationC a B T₀ D Q)
    (residual a B W e) (equations a B P e)
    (relation_identity a B P Q V W T₀ D hdecomp e hrelations) heq
    (isUnit_of_mul_isUnit_right hprod)
  refine ⟨evaluated_equations_zero (algebraMap R S) a B P Q V W hdecomp e x hP
    (fun q => congrFun hres q),?_⟩
  exact (congrArg IsUnit (eval_substitute (algebraMap R S) a B x c)).mp
    (isUnit_of_mul_isUnit_left hprod)

variable [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field T] [Algebra R T]

theorem pointed_lift_all_on_compatible_affine_slice
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R)
    (hdecomp : Q*P+V*W=1)
    (hrelations : D*ᵥe=0)
    (hseed : ∀q,eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) (e q)=0)
    (hjac : P.map (algebraMap R T)*
      jacobian (algebraMap R T) ((algebraMap R T) ∘ a) e*B.map (algebraMap R T)=1)
    (hcomplement : T₀.map (algebraMap R T)*
      D.map (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a))*V.map (algebraMap R T)=1)
    (hc : IsUnit (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) c)) :
    ∃ I : Ideal (GenericAlgebra K a B P T₀ D V e c), I.IsMaximal ∧
      Module.Finite K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      Algebra.IsSeparable K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      ∃ x : ι → ((GenericAlgebra K a B P T₀ D V e c) ⧸ I),
        (∀q,aeval (pointValue (algebraMap R _) a B x) (e q)=0) ∧
        IsUnit (aeval (pointValue (algebraMap R _) a B x) c) ∧
        (∀p : MvPolynomial σ R,
          aeval (pointValue (algebraMap R _) a B x) p=0 →
            eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) p=0) := by
  have hseed' (q : ι) : aeval (0 : ι → T) (equations a B P e q)=0 :=
    seed_equations_zero (algebraMap R T) a B P e hseed q
  have hjac' : IsUnit (Matrix.det (fun i j =>
      aeval (0 : ι → T) (pderiv i (equations a B P e j)))) := by
    change IsUnit (Matrix.det (fun i j =>
      eval₂Hom (algebraMap R T) (0 : ι → T) (pderiv i (equations a B P e j))))
    rw [seed_jacobian_det_one (algebraMap R T) a B P e hjac]
    exact isUnit_one
  have hcomplement' : IsUnit (aeval (0 : ι → T) (relationA a B T₀ D V).det) := by
    change IsUnit (eval₂Hom (algebraMap R T) (0 : ι → T) (relationA a B T₀ D V).det)
    rw [seed_relationA_det_one (algebraMap R T) a B T₀ D V hcomplement]
    exact isUnit_one
  have hc' : IsUnit (aeval (0 : ι → T) (substitute a B c)) := by
    change IsUnit (eval₂Hom (algebraMap R T) (0 : ι → T) (substitute a B c))
    rw [eval_zero_substitute]
    exact hc
  have hopen : IsUnit (aeval (0 : ι → T)
      (substitute a B c*(relationA a B T₀ D V).det)) := by
    rw [map_mul]
    exact hc'.mul hcomplement'
  obtain ⟨I,hI,hfinite,hsep,x,hP,ho,hspecializes⟩ :=
    CycleQ2PointedOpenLifting.square_system_pointed_lift_on_open (K := K)
      (equations a B P e) (substitute a B c*(relationA a B T₀ D V).det)
      (0 : ι → T) hseed' hjac' hopen
  have hsem := affine_lift_semantics a B P Q V W T₀ D e c hdecomp hrelations x hP ho
  refine ⟨I,hI,hfinite,hsep,x,hsem.1,hsem.2,?_⟩
  intro p hp
  have hp' : aeval x (substitute a B p)=0 :=
    (eval_substitute (algebraMap R _) a B x p).trans hp
  exact (eval_zero_substitute (algebraMap R T) a B p).symm.trans
    (hspecializes (substitute a B p) hp')

end CycleQ2PointedCompatibleAffineLifting

#print axioms CycleQ2PointedCompatibleAffineLifting.affine_lift_semantics
#print axioms CycleQ2PointedCompatibleAffineLifting.pointed_lift_all_on_compatible_affine_slice
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechNormalization.lean -/
section
/-! The normalization of the actual two-endpoint Čech functional is obtained
from a checked identity in the first infinitesimal neighborhood of the two
endpoints.  No residue value is supplied as a hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

def powerCoefficient (r : ℂ) (e : Bool) : PowerChart r e →ₗ[PS] PS :=
  coefficient (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)

theorem firstJet_powerCoefficient (r : ℂ) (e : Bool) (z : PowerChart r e) :
    firstJet (powerCoefficient r e z) = jetCoefficient r e (jetEmbedding r e z) := by
  symm
  exact coefficient_curveMap firstJet _ _ _ _ z

theorem uniformizer_inv_sq : (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ 2) =
    HahnSeries.single (-2 : ℤ) 1 := by
  simp [uniformizerUnit, seriesMap, HahnSeries.ofPowerSeries_X,
    HahnSeries.inv_single, HahnSeries.single_pow]

/-- The double pole in x₁x₃ extracts the linear coefficient of an integral
power-series chart, for every power of the other cover equation. -/
theorem fractionResidue_double_pole (r : ℂ) (e : Bool) (p : Poly) (m : ℕ) :
    fractionResidue r e p 2 m =
      PowerSeries.coeff 1 (powerCoefficient r e
        (powerEval r e p * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ m)) := by
  let z : PowerChart r e :=
    powerEval r e p * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ m
  have heq : fraction r e p 2 m =
      laurentBase r e (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ 2) * chartEmbedding r e z := by
    simp only [fraction, laurentEval, RingHom.comp_apply, z, map_mul, map_pow,
      laurentBase, chartAUnit, laurentX2Unit, Units.coe_map_inv, Units.coe_map,
      MonoidHom.coe_coe]
    ring
  change (laurentCoefficient r e (fraction r e p 2 m)).coeff (-1) = _
  rw [heq]
  unfold laurentCoefficient laurentBase chartEmbedding
  rw [coefficient_base_mul, coefficient_curveMap, uniformizer_inv_sq,
    HahnSeries.coeff_single_mul]
  norm_num [seriesMap, powerCoefficient, PowerSeries.coeff_coe, z]

def soclePower (r : ℂ) (e : Bool) : PowerChart r e :=
  powerEval r e (mon 1 8 0 0) * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ 4

theorem jetEmbedding_soclePower (r : ℂ) (e : Bool) :
    jetEmbedding r e (soclePower r e) =
      jetX0 r e * (jetBase r e (firstJet (endpointX e)))^8 *
        ((jetX2Unit r e)⁻¹ : (JetChart r e)ˣ) ^ 4 := by
  simp only [soclePower, mon, map_mul, map_pow, powerEval_X,
    powerCoordinates_zero, powerCoordinates_one, powerCoordinates_two,
    powerCoordinates_three, pow_zero, pow_one, mul_one,
    jetEmbedding, curveMap_x0, curveMap_base, jetX0, jetBase,
    jetX2Unit, Units.coe_map_inv, MonoidHom.coe_coe]

theorem jetEmbedding_soclePower_false (r : ℂ) :
    jetEmbedding r false (soclePower r false) =
      jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4 := by
  rw [jetEmbedding_soclePower]
  simp only [endpointX, map_one, one_pow, mul_one]

theorem jetEmbedding_soclePower_true (r : ℂ) :
    jetEmbedding r true (soclePower r true) = 0 := by
  have ht : firstJet (PowerSeries.X : PS) ^ 8 = 0 := by
    rw [show 8 = 2 * 4 from rfl, pow_mul, firstJet_X_sq, zero_pow (by decide)]
  have ht' : (jetBase r true (firstJet PowerSeries.X)) ^ 8 = 0 := by
    rw [← map_pow, ht, map_zero]
  rw [jetEmbedding_soclePower]
  change jetX0 r true * (jetBase r true (firstJet PowerSeries.X))^8 * _ = 0
  rw [ht', mul_zero, zero_mul]

theorem soclePower_false_coefficient (r : ℂ) :
    PowerSeries.coeff 1 (powerCoefficient r false (soclePower r false)) = 3*r := by
  have hh : firstJet (powerCoefficient r false (soclePower r false)) =
      -1 + 3 * firstJet (PowerSeries.C r) * firstJet PowerSeries.X := by
    rw [firstJet_powerCoefficient, jetEmbedding_soclePower_false, false_jet_coefficient]
  have hs := congrArg TrivSqZeroExt.snd hh
  norm_num [firstJet, smul_eq_mul, op_smul_eq_smul, TrivSqZeroExt.fst_natCast] at hs ⊢
  exact hs

theorem soclePower_true_coefficient (r : ℂ) :
    PowerSeries.coeff 1 (powerCoefficient r true (soclePower r true)) = 0 := by
  have hh : firstJet (powerCoefficient r true (soclePower r true)) = 0 := by
    rw [firstJet_powerCoefficient, jetEmbedding_soclePower_true, map_zero]
  exact congrArg TrivSqZeroExt.snd hh

/-- The actual Laurent-series functional evaluates the published socle
representative to 3r at denominator (x₁x₃)²x₂⁴. -/
theorem cechResidue_socle (r : ℂ) :
    cechResidue r (mon 1 8 0 0) 2 4 = 3*r := by
  simp only [cechResidue, fractionResidue_double_pole]
  change PowerSeries.coeff 1 (powerCoefficient r false (soclePower r false)) -
    PowerSeries.coeff 1 (powerCoefficient r true (soclePower r true)) = 3*r
  rw [soclePower_false_coefficient, soclePower_true_coefficient, sub_zero]

theorem endpointResidue_scalar (r : ℂ) (e : Bool) (c : ℂ) (z : LaurentChart r e) :
    endpointResidue r e (laurentBase r e (seriesMap (PowerSeries.C c)) * z) =
      c * endpointResidue r e z := by
  change (laurentCoefficient r e
    (laurentBase r e (seriesMap (PowerSeries.C c)) * z)).coeff (-1) = _
  unfold laurentCoefficient laurentBase
  rw [coefficient_base_mul]
  change (seriesMap (PowerSeries.C c) * laurentCoefficient r e z).coeff (-1) = _
  rw [show seriesMap (PowerSeries.C c) = HahnSeries.single (0 : ℤ) c from
    HahnSeries.ofPowerSeries_C c, HahnSeries.coeff_single_zero_mul]
  rfl

theorem cechResidue_C_mul (r : ℂ) (c : ℂ) (p : Poly) (n m : ℕ) :
    cechResidue r (C c * p) n m = c * cechResidue r p n m := by
  have he (e : Bool) : fraction r e (C c * p) n m =
      laurentBase r e (seriesMap (PowerSeries.C c)) * fraction r e p n m := by
    simp [fraction, laurentEval, powerEval, chartEmbedding, laurentBase, mul_assoc]
  simp only [cechResidue, fractionResidue, he, endpointResidue_scalar]
  ring

theorem cechResidue_sub (r : ℂ) (p q : Poly) (n m : ℕ) :
    cechResidue r (p-q) n m = cechResidue r p n m - cechResidue r q n m := by
  simp only [cechResidue, fractionResidue, fraction_sub, map_sub]
  ring

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.cechResidue_socle
end
end


