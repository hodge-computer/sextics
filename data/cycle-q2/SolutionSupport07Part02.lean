import Proposal.SolutionSupport07Part01
import Proposal.GeometricSeedNormalIdeals
import Proposal.GeometricSeedConormalBases
import Proposal.GeometricNormalConnecting

/-! Components extracted from SolutionSupport07.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_20261111/SegreKodairaSpencer.lean -/
section
/-!
# The actual Segre transition cocycle and the Kodaira--Spencer contraction

The local derivations below may differ.  This retains the variation of the
surface coordinates, which a single global parameter derivation would lose.
All logarithmic forms are in the actual universal Kaehler module; all Segre
units are the previously constructed matrix-entry units, including the
degree twist.  The main identity identifies their contracted Chern cocycle
with an explicit Cech boundary.  It is a chain-level identity on overlap
rings, not an assumed Abel--Jacobi or global de Rham comparison.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace CycleQ2SegreKodairaSpencer

open CycleQ2SegreCech

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

/-- Evaluation of the actual universal logarithmic differential. -/
def logDerivative (D : Derivation K R R) (u : Rˣ) : R :=
  D.liftKaehlerDifferential (unitDlog K u)

theorem logDerivative_eq (D : Derivation K R R) (u : Rˣ) :
    logDerivative D u = (↑(u⁻¹) : R) * D (u : R) := by
  simp [logDerivative, unitDlog_apply, smul_eq_mul]

theorem logDerivative_mul (D : Derivation K R R) (u v : Rˣ) :
    logDerivative D (u * v) = logDerivative D u + logDerivative D v := by
  simp only [logDerivative, unitDlog_mul, map_add]

theorem logDerivative_inv (D : Derivation K R R) (u : Rˣ) :
    logDerivative D u⁻¹ = -logDerivative D u := by
  simp only [logDerivative, unitDlog_inv, map_neg]

theorem logDerivative_pow (D : Derivation K R R) (u : Rˣ) (n : ℕ) :
    logDerivative D (u ^ n) = n • logDerivative D u := by
  simp only [logDerivative, unitDlog_pow, map_nsmul]

theorem logDerivative_add (D E : Derivation K R R) (u : Rˣ) :
    logDerivative (D + E) u = logDerivative D u + logDerivative E u := by
  simp only [logDerivative_eq, Derivation.add_apply, mul_add]

theorem logDerivative_sub (D E : Derivation K R R) (u : Rˣ) :
    logDerivative (D - E) u = logDerivative D u - logDerivative E u := by
  simp only [logDerivative_eq, Derivation.sub_apply, mul_sub]

/-- The Cech boundary of the local logarithmic variations equals the
Kodaira--Spencer difference contracted against the actual Chern form.
The sign convention is delta(a) = a_qr - a_pr + a_pq. -/
theorem boundary_eq_contraction
    (Dp Dq : Derivation K R R) (gpq gqr gpr : Rˣ)
    (hg : gpq * gqr = gpr) :
    logDerivative Dq gqr - logDerivative Dp gpr + logDerivative Dp gpq =
      (Dq - Dp).liftKaehlerDifferential (unitDlog K gqr) := by
  change _ = logDerivative (Dq - Dp) gqr
  rw [← hg, logDerivative_mul, logDerivative_sub]
  abel

/-- On a quadruple overlap the contracted cochain is a genuine cocycle.
This uses both the transition cocycle and the additive cocycle of local
derivation differences; no commutativity of derivations is required. -/
theorem contraction_cocycle
    (Dp Dq Dr : Derivation K R R) (gqr grs gqs : Rˣ)
    (hg : gqr * grs = gqs) :
    logDerivative (Dr - Dq) grs - logDerivative (Dr - Dp) grs +
      logDerivative (Dq - Dp) gqs - logDerivative (Dq - Dp) gqr = 0 := by
  rw [← hg, logDerivative_mul]
  simp only [logDerivative_sub]
  abel

/-- The exact entrywise inverse rule works in overlap rings with zero
divisors as well; only the displayed element is assumed invertible. -/
theorem derivative_unit_inverse (D : Derivation K R R) (u : Rˣ) :
    D (↑(u⁻¹) : R) = -(↑(u⁻¹) : R)^2 * D (u : R) := by
  have h := congrArg D u.mul_inv
  simp only [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul] at h
  linear_combination (↑(u⁻¹) : R) * h - D (↑(u⁻¹) : R) * u.inv_mul

/-- An explicit matrix-entry formula for the contraction. -/
theorem transition_logDerivative_entries
    (D : Derivation K R R)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    logDerivative D (transition M hM p q up uq hp hq) =
      (↑((transition M hM p q up uq hp hq)⁻¹) : R) *
        (D (M q.1 p.2) * (↑(up⁻¹) : R) -
          M q.1 p.2 * (↑(up⁻¹) : R)^2 * D (M p.1 p.2)) := by
  rw [logDerivative_eq]
  change _ * D (M q.1 p.2 * (↑(up⁻¹) : R)) = _
  rw [Derivation.leibniz, derivative_unit_inverse D up, hp]
  simp only [smul_eq_mul]
  ring

/-- The obstruction identity for the literal Segre image line. -/
theorem segre_boundary_eq_contraction
    (Dp Dq : Derivation K R R)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) :
    logDerivative Dq (transition M hM q r uq ur hq hr) -
        logDerivative Dp (transition M hM p r up ur hp hr) +
        logDerivative Dp (transition M hM p q up uq hp hq) =
      (Dq - Dp).liftKaehlerDifferential
        (unitDlog K (transition M hM q r uq ur hq hr)) :=
  boundary_eq_contraction Dp Dq _ _ _ (transition_cocycle M hM p q r up uq ur hp hq hr)

/-- The homogeneous divisor bundle includes O(d).  Its logarithmic
variation retains the coordinate-trivialization terms. -/
theorem twisted_logDerivative
    (D : Derivation K R R)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) :
    logDerivative D (twistedTransition M hM p q up uq hp hq xp xq d) =
      d • (logDerivative D xp - logDerivative D xq) +
        logDerivative D (transition M hM p q up uq hp hq) := by
  simp only [twistedTransition, logDerivative_mul, logDerivative_pow,
    logDerivative_inv, sub_eq_add_neg]

/-- The actual degree-twisted Chern cocycle satisfies the same obstruction
identity.  This is the cocycle appropriate to the degree-fourteen entries,
not the untwisted image-line class. -/
theorem twisted_boundary_eq_contraction
    (Dp Dq : Derivation K R R)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) (xp xq xr : Rˣ) (d : ℕ) :
    logDerivative Dq (twistedTransition M hM q r uq ur hq hr xq xr d) -
        logDerivative Dp (twistedTransition M hM p r up ur hp hr xp xr d) +
        logDerivative Dp (twistedTransition M hM p q up uq hp hq xp xq d) =
      (Dq - Dp).liftKaehlerDifferential
        (unitDlog K (twistedTransition M hM q r uq ur hq hr xq xr d)) :=
  boundary_eq_contraction Dp Dq _ _ _
    (twistedTransition_cocycle M hM p q r up uq ur hp hq hr xp xq xr d)

/-- Changing local derivation lifts changes the contracted cochain by the
explicit Cech boundary of their difference, with the same transition units. -/
theorem change_lifts_boundary
    (Dp Dq Ep Eq : Derivation K R R) (gpq gqr gpr : Rˣ)
    (hg : gpq * gqr = gpr) :
    logDerivative ((Dq + Eq) - (Dp + Ep)) gqr - logDerivative (Dq - Dp) gqr =
      logDerivative Eq gqr - logDerivative Ep gpr + logDerivative Ep gpq := by
  rw [← hg, logDerivative_mul]
  simp only [logDerivative_sub, logDerivative_add]
  abel

/-- The contraction is compatible with a restriction map whenever the
local derivations are compatible with that restriction. -/
theorem logDerivative_natural
    {S : Type*} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (D : Derivation K R R) (E : Derivation K S S)
    (hDE : ∀ x : R, E (f x) = f (D x)) (u : Rˣ) :
    f (logDerivative D u) =
      logDerivative E (Units.map f.toMonoidHom u) := by
  simp only [logDerivative_eq, Units.coe_map, Units.coe_map_inv, map_mul]
  change f (↑(u⁻¹) : R) * f (D (u : R)) =
    f (↑(u⁻¹) : R) * E (f (u : R))
  rw [hDE]

end CycleQ2SegreKodairaSpencer

#print axioms CycleQ2SegreKodairaSpencer.boundary_eq_contraction
#print axioms CycleQ2SegreKodairaSpencer.contraction_cocycle
#print axioms CycleQ2SegreKodairaSpencer.segre_boundary_eq_contraction
#print axioms CycleQ2SegreKodairaSpencer.twisted_boundary_eq_contraction
#print axioms CycleQ2SegreKodairaSpencer.change_lifts_boundary
#print axioms CycleQ2SegreKodairaSpencer.logDerivative_natural
end
end


/- Component: continuation_20261111/PolynomialCoefficientDerivation.lean -/
section
/-!
# The actual coefficient motion on a multivariate polynomial ring

This extends a derivation of the coefficient ring while holding every
polynomial coordinate fixed.  The construction uses the actual polynomial
evaluation into dual numbers, not a postulated coefficient operator.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2PolynomialCoefficientDerivation

open MvPolynomial CycleQ2LocalizationDerivation

variable {K A : Type*} {σ : Type*} [CommRing K] [CommRing A] [Algebra K A]

abbrev Poly := MvPolynomial σ A

def polynomialGraph (D : Derivation K A A) : Poly (σ := σ) (A := A) →ₐ[K]
    Jet (Poly (σ := σ) (A := A)) where
  __ := eval₂Hom (graph (S := Poly (σ := σ) (A := A)) D).toRingHom
    (fun j => TrivSqZeroExt.inl (X j))
  commutes' k := by
    change eval₂Hom _ _ (C (algebraMap K A k)) = _
    rw [eval₂Hom_C]
    exact (graph (S := Poly (σ := σ) (A := A)) D).commutes k

@[simp] theorem polynomialGraph_C (D : Derivation K A A) (a : A) :
    polynomialGraph (σ := σ) D (C a) =
      graph (S := Poly (σ := σ) (A := A)) D a :=
  eval₂Hom_C _ _ _

@[simp] theorem polynomialGraph_X (D : Derivation K A A) (j : σ) :
    polynomialGraph D (X j) = TrivSqZeroExt.inl (X j) := by
  exact eval₂Hom_X' (graph (S := Poly (σ := σ) (A := A)) D).toRingHom
    (fun k => TrivSqZeroExt.inl (X k)) j

theorem polynomialGraph_fst (D : Derivation K A A) (p : Poly (σ := σ) (A := A)) :
    (polynomialGraph D p).fst = p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [polynomialGraph_C, graph_fst]; rfl
  | add p q hp hq =>
      rw [map_add, TrivSqZeroExt.fst_add, hp, hq]
  | mul_X p j hp =>
      rw [map_mul, TrivSqZeroExt.fst_mul, hp, polynomialGraph_X]
      rfl

def coefficientDerivation (D : Derivation K A A) :
    Derivation K (Poly (σ := σ) (A := A)) (Poly (σ := σ) (A := A)) where
  toLinearMap := (TrivSqZeroExt.sndHom _ _).restrictScalars K |>.comp
    (polynomialGraph D).toLinearMap
  map_one_eq_zero' := by simp
  leibniz' p q := by
    change (polynomialGraph D (p * q)).snd =
      p * (polynomialGraph D q).snd + q * (polynomialGraph D p).snd
    rw [map_mul, TrivSqZeroExt.snd_mul]
    simp only [polynomialGraph_fst, smul_eq_mul, op_smul_eq_smul]

@[simp] theorem coefficientDerivation_C (D : Derivation K A A) (a : A) :
    coefficientDerivation (σ := σ) D (C a) = C (D a) := by
  change (polynomialGraph D (C a)).snd = _
  rw [polynomialGraph_C, graph_snd]
  rfl

@[simp] theorem coefficientDerivation_X (D : Derivation K A A) (j : σ) :
    coefficientDerivation D (X j) = 0 := by
  change (polynomialGraph D (X j)).snd = 0
  rw [polynomialGraph_X]
  rfl

theorem coefficientDerivation_monomial (D : Derivation K A A)
    (e : σ →₀ ℕ) (a : A) :
    coefficientDerivation D (monomial e a) = monomial e (D a) := by
  classical
  rw [MvPolynomial.monomial_eq]
  rw [Derivation.leibniz, coefficientDerivation_C]
  have hz' (s : Finset σ) :
      coefficientDerivation D (∏ j ∈ s, (X j : Poly (A := A)) ^ e j) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp [Derivation.map_one_eq_zero]
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj, Derivation.leibniz, ih,
          Derivation.leibniz_pow, coefficientDerivation_X]
        simp
  have hz : coefficientDerivation D (e.prod fun j n => (X j : Poly (A := A)) ^ n) = 0 :=
    hz' e.support
  rw [hz, smul_zero, zero_add]
  simpa only [smul_eq_mul, mul_comm] using
    (MvPolynomial.monomial_eq (s := e) (a := D a)).symm

/-- Uniqueness follows from the genuine polynomial induction principle. -/
theorem coefficientDerivation_unique (D : Derivation K A A)
    (E : Derivation K (Poly (σ := σ) (A := A)) (Poly (σ := σ) (A := A)))
    (hC : ∀ a : A, E (C a) = C (D a)) (hX : ∀ j : σ, E (X j) = 0) :
    E = coefficientDerivation D := by
  apply Derivation.ext
  intro p
  induction p using MvPolynomial.induction_on with
  | C a => rw [hC, coefficientDerivation_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p j hp =>
      rw [Derivation.leibniz, Derivation.leibniz, hX, coefficientDerivation_X, hp]

end CycleQ2PolynomialCoefficientDerivation

#print axioms CycleQ2PolynomialCoefficientDerivation.coefficientDerivation_C
#print axioms CycleQ2PolynomialCoefficientDerivation.coefficientDerivation_monomial
#print axioms CycleQ2PolynomialCoefficientDerivation.coefficientDerivation_unique
end
end


/- Component: continuation_20261111/RelativeKodairaSpencer.lean -/
section
/-!
# The overlap correction is a genuine relative derivation

Two local lifts of the same coefficient motion have a difference which
annihilates the coefficient ring.  Thus the preceding Cech identity lives
in the actual relative Kaehler module of the surface, not just in absolute
differentials over the complex constants.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2RelativeKodairaSpencer

open CycleQ2SegreCech CycleQ2SegreKodairaSpencer

variable {K A R : Type*} [CommRing K] [CommRing A] [CommRing R]
  [Algebra K A] [Algebra A R] [Algebra K R] [IsScalarTower K A R]

/-- The Kodaira--Spencer difference is linear over the coefficient ring
because the two actual local lifts induce the same coefficient motion. -/
def relativeDifference (Dp Dq : Derivation K R R)
    (h : ∀ a : A, Dp (algebraMap A R a) = Dq (algebraMap A R a)) :
    Derivation A R R where
  toFun x := Dq x - Dp x
  map_add' x y := by simp only [map_add]; abel
  map_smul' a x := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    simp only [Derivation.leibniz, h, smul_eq_mul]
    ring
  map_one_eq_zero' := by
    change Dq 1 - Dp 1 = 0
    simp only [Derivation.map_one_eq_zero, sub_self]
  leibniz' x y := by
    change Dq (x * y) - Dp (x * y) =
      x * (Dq y - Dp y) + y * (Dq x - Dp x)
    simp only [Derivation.leibniz, smul_eq_mul]
    ring

theorem relativeDifference_coefficients (Dp Dq : Derivation K R R)
    (h : ∀ a : A, Dp (algebraMap A R a) = Dq (algebraMap A R a)) (a : A) :
    relativeDifference Dp Dq h (algebraMap A R a) = 0 := by
  simp [relativeDifference, h]

/-- The absolute and relative evaluations are the same actual scalar. -/
theorem contraction_eq_relative (Dp Dq : Derivation K R R)
    (h : ∀ a : A, Dp (algebraMap A R a) = Dq (algebraMap A R a)) (u : Rˣ) :
    (Dq - Dp).liftKaehlerDifferential (unitDlog K u) =
      (relativeDifference Dp Dq h).liftKaehlerDifferential (unitDlog A u) := by
  rw [unitDlog_apply, unitDlog_apply]
  rfl

/-- The Cech boundary is identified with the contraction against the
relative Chern form over the actual coefficient ring. -/
theorem boundary_eq_relative_contraction
    (Dp Dq : Derivation K R R)
    (h : ∀ a : A, Dp (algebraMap A R a) = Dq (algebraMap A R a))
    (gpq gqr gpr : Rˣ) (hg : gpq * gqr = gpr) :
    logDerivative Dq gqr - logDerivative Dp gpr + logDerivative Dp gpq =
      (relativeDifference Dp Dq h).liftKaehlerDifferential (unitDlog A gqr) := by
  rw [boundary_eq_contraction Dp Dq gpq gqr gpr hg,
    contraction_eq_relative Dp Dq h gqr]

end CycleQ2RelativeKodairaSpencer

#print axioms CycleQ2RelativeKodairaSpencer.contraction_eq_relative
#print axioms CycleQ2RelativeKodairaSpencer.boundary_eq_relative_contraction
end
end


/- Component: continuation_20261111/SeedConormalBasis.lean -/
section
/-! # Actual conormal bases on a literal seed Jacobian open

The cotangent module is the genuine ideal quotient I/I², then base changed
to the chosen localization of the actual curve.  Its coordinate functionals
are induced by genuine polynomial partial derivations.
-/

noncomputable section
open scoped BigOperators TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ConormalJacobian

section LiteralSeed
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting


def firstPivot (r : ℂ) : P := -C r * X 3
def secondPivot : P := 3*X 2^2+X 1*X 3+X 0*X 3
def crossPartial : P := X 2*X 3+2*X 0*X 1-3*C Complex.I*X 1^2
def jacobianMinor (r : ℂ) : P := firstPivot r*secondPivot

theorem firstPivot_is_partial (r : ℂ) : pderiv 1 (originalF1 r)=firstPivot r := by
  simp [originalF1,firstPivot] <;> ring

theorem secondPivot_is_partial (θ : ℂ) : pderiv 2 (thetaH θ)=secondPivot := by
  simp [thetaH,originalH,originalB,secondPivot] <;> ring

theorem crossPartial_is_partial (θ : ℂ) : pderiv 1 (thetaH θ)=crossPartial := by
  simp [thetaH,originalH,originalB,crossPartial] <;> ring

variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

def mappedPartial (j : Fin 5) : Derivation ℂ P S :=
  (Algebra.linearMap P S).compDer (pderiv j)

@[simp] theorem mappedPartial_apply (j : Fin 5) (p : P) :
    mappedPartial (S := S) j p=algebraMap P S (pderiv j p) := rfl

/-- The same binding applies on any actual unit Jacobian-minor chart. -/
def seedConormalBasisOnMinor (r θ : ℂ)
    (hI : ∀ p∈ambientCurveIdeal r θ, algebraMap P S p=0)
    (c : Fin 3 → Fin 5)
    (hc : IsUnit (derivationMatrix (curveEquations r θ)
      (fun i => mappedPartial (S := S) (c i))).det) :
    Module.Basis (Fin 3) S (S ⊗[P] (ambientCurveIdeal r θ).Cotangent) :=
  conormalBasisOfJacobian (ambientCurveIdeal r θ) hI (curveEquations r θ) rfl
    (fun i => mappedPartial (c i)) hc

/-- Duals to (f1,f2,h), with the actual triangular Jacobian inverted. -/
def seedDualDerivations (u v : Sˣ) : Fin 3 → Derivation ℂ P S := ![
    (↑(u⁻¹):S) • mappedPartial 1 -
      ((↑(u⁻¹):S)*(↑(v⁻¹):S)*algebraMap P S crossPartial) • mappedPartial 2 +
      (2*algebraMap P S (X 2)*(↑(u⁻¹):S)*(↑(v⁻¹):S)*
        algebraMap P S crossPartial) • mappedPartial 4,
    mappedPartial 4,
    (↑(v⁻¹):S) • mappedPartial 2 -
      (2*algebraMap P S (X 2)*(↑(v⁻¹):S)) • mappedPartial 4]

theorem seedDualDerivations_equations (r θ : ℂ) (u v : Sˣ)
    (hu : (u:S)=algebraMap P S (firstPivot r))
    (hv : (v:S)=algebraMap P S secondPivot) (i j : Fin 3) :
    seedDualDerivations u v i (curveEquations r θ j)=if i=j then 1 else 0 := by
  have hf11 := congrArg (algebraMap P S) (firstPivot_is_partial r)
  have hh1 := congrArg (algebraMap P S) (crossPartial_is_partial θ)
  have hh2 := congrArg (algebraMap P S) (secondPivot_is_partial θ)
  rw [←hu] at hf11
  rw [←hv] at hh2
  fin_cases i <;> fin_cases j <;>
    simp [seedDualDerivations,curveEquations,Derivation.add_apply,
      Derivation.sub_apply,Derivation.smul_apply,mappedPartial_apply,
      hf11,hh1,hh2,smul_eq_mul]
  all_goals try simp [originalF1,originalF2,thetaH,originalH,originalB,
    map_ofNat,mul_assoc,mul_left_comm,mul_comm]
  all_goals ring_nf <;> simp [mul_assoc]

theorem sourceDual_F (r θ : ℂ)
    (hI : ∀ p∈ambientCurveIdeal r θ, algebraMap P S p=0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j)=if i=j then 1 else 0)
    (i : Fin 3) :
    d i (actualSeedEquation r θ)=
      ![algebraMap P S (originalG1 r),algebraMap P S originalG2,
        algebraMap P S (thetaK θ)] i := by
  have hf1 : algebraMap P S (originalF1 r)=0 := hI _ (curveEquation_mem r θ 0)
  have hf2 : algebraMap P S originalF2=0 := hI _ (curveEquation_mem r θ 1)
  have hh : algebraMap P S (thetaH θ)=0 := hI _ (curveEquation_mem r θ 2)
  have hd0 : d i (originalF1 r)=if i=0 then 1 else 0 := hd i 0
  have hd1 : d i originalF2=if i=1 then 1 else 0 := hd i 1
  have hd2 : d i (thetaH θ)=if i=2 then 1 else 0 := hd i 2
  simp only [actualSeedEquation,map_add,Derivation.leibniz,Algebra.smul_def,
    hf1,hf2,hh,zero_mul,zero_add,hd0,hd1,hd2]
  fin_cases i <;> simp

def surfaceDualDerivations (d : Fin 3 → Derivation ℂ P S) (u : Sˣ) (k : S) :
    Fin 2 → Derivation ℂ P S :=
  ![(↑(u⁻¹):S) • d 0,d 2-(k*(↑(u⁻¹):S)) • d 0]

theorem surfaceDualDerivations_equations (r θ : ℂ)
    (hI : ∀ p∈ambientCurveIdeal r θ, algebraMap P S p=0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j)=if i=j then 1 else 0)
    (u : Sˣ) (hu : (u:S)=algebraMap P S (originalG1 r)) (i j : Fin 2) :
    surfaceDualDerivations d u (algebraMap P S (thetaK θ)) i
      (surfaceEquations r θ j)=if i=j then 1 else 0 := by
  have hF0 := sourceDual_F r θ hI d hd 0
  have hF2 := sourceDual_F r θ hI d hd 2
  have hh0 : d 0 (thetaH θ)=0 := by simpa [curveEquations] using hd 0 2
  have hh2 : d 2 (thetaH θ)=1 := by simpa [curveEquations] using hd 2 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_two] at hF0 hF2
  rw [←hu] at hF0
  fin_cases i <;> fin_cases j <;>
    simp [surfaceDualDerivations,surfaceEquations,Derivation.smul_apply,
      Derivation.sub_apply,hF0,hF2,hh0,hh2,smul_eq_mul,mul_assoc]

/-- The target two-equation conormal module also has its actual equation
classes as a basis on every g1-unit chart. Together with the source basis,
this removes both normal-presentation assumptions. -/
def surfaceConormalBasisOnFirstOpen (r θ : ℂ)
    (hI : ∀ p∈ambientCurveIdeal r θ, algebraMap P S p=0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j)=if i=j then 1 else 0)
    (u : Sˣ) (hu : (u:S)=algebraMap P S (originalG1 r)) :
    Module.Basis (Fin 2) S (S ⊗[P] (surfaceIdeal r θ).Cotangent) :=
  conormalBasis (surfaceIdeal r θ)
    (fun p hp => hI p (surfaceIdeal_le_curveIdeal r θ hp))
    (surfaceEquations r θ) rfl
    (surfaceDualDerivations d u (algebraMap P S (thetaK θ)))
    (surfaceDualDerivations_equations r θ hI d hd u hu)

end LiteralSeed

section ActualLocalization
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting

abbrev ActualCurve (r θ : ℂ) := P ⧸ ambientCurveIdeal r θ
abbrev ActualLocalCurve (r θ : ℂ) :=
  Localization.Away (Ideal.Quotient.mk (ambientCurveIdeal r θ) (jacobianMinor r))

def actualLocalMap (r θ : ℂ) : P →+* ActualLocalCurve r θ :=
  (algebraMap (ActualCurve r θ) (ActualLocalCurve r θ)).comp
    (Ideal.Quotient.mk (ambientCurveIdeal r θ))

instance localScalarTower (r θ : ℂ) : IsScalarTower ℂ P (ActualLocalCurve r θ) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := P) (A := ActualLocalCurve r θ)
    fun _ => rfl

theorem actualLocalMap_ideal (r θ : ℂ) (p : P) (hp : p∈ambientCurveIdeal r θ) :
    algebraMap P (ActualLocalCurve r θ) p=0 := by
  change algebraMap (ActualCurve r θ) (ActualLocalCurve r θ)
    (Ideal.Quotient.mk (ambientCurveIdeal r θ) p)=0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp,map_zero]

theorem actualLocalMap_minor_unit (r θ : ℂ) :
    IsUnit (algebraMap P (ActualLocalCurve r θ) (jacobianMinor r)) := by
  change IsUnit (algebraMap (ActualCurve r θ) (ActualLocalCurve r θ)
    (Ideal.Quotient.mk (ambientCurveIdeal r θ) (jacobianMinor r)))
  exact IsLocalization.Away.algebraMap_isUnit (S := ActualLocalCurve r θ) _

def actualFirstUnit (r θ : ℂ) : (ActualLocalCurve r θ)ˣ :=
  (isUnit_of_mul_isUnit_left (x := algebraMap P (ActualLocalCurve r θ) (firstPivot r))
    (y := algebraMap P (ActualLocalCurve r θ) secondPivot) (by
    rw [← map_mul]
    exact actualLocalMap_minor_unit r θ)).unit

def actualSecondUnit (r θ : ℂ) : (ActualLocalCurve r θ)ˣ :=
  (isUnit_of_mul_isUnit_right (x := algebraMap P (ActualLocalCurve r θ) (firstPivot r))
    (y := algebraMap P (ActualLocalCurve r θ) secondPivot) (by
    rw [← map_mul]
    exact actualLocalMap_minor_unit r θ)).unit

@[simp] theorem actualFirstUnit_value (r θ : ℂ) :
    (actualFirstUnit r θ : ActualLocalCurve r θ)=
      algebraMap P (ActualLocalCurve r θ) (firstPivot r) := IsUnit.unit_spec _

@[simp] theorem actualSecondUnit_value (r θ : ℂ) :
    (actualSecondUnit r θ : ActualLocalCurve r θ)=
      algebraMap P (ActualLocalCurve r θ) secondPivot := IsUnit.unit_spec _

/-- The genuine localized conormal module of the actual seed curve. -/
abbrev ActualConormal (r θ : ℂ) :=
  ActualLocalCurve r θ ⊗[P] (ambientCurveIdeal r θ).Cotangent

/-- A basis of the actual conormal module on the literal Jacobian open. -/
def actualConormalBasis (r θ : ℂ) :
    Module.Basis (Fin 3) (ActualLocalCurve r θ) (ActualConormal r θ) :=
  conormalBasis (ambientCurveIdeal r θ) (actualLocalMap_ideal r θ)
    (curveEquations r θ) rfl
    (seedDualDerivations (actualFirstUnit r θ) (actualSecondUnit r θ))
    (seedDualDerivations_equations r θ _ _
      (actualFirstUnit_value r θ) (actualSecondUnit_value r θ))

@[simp] theorem actualConormalBasis_apply (r θ : ℂ) (i : Fin 3) :
    actualConormalBasis r θ i=(1:ActualLocalCurve r θ) ⊗ₜ[P] conormalGenerator r θ i := by
  exact conormalBasis_apply _ _ _ _ _ _ _

/-- Coordinates in this proved basis identify the actual normal module with
three scalar normal coordinates; no presentation is assumed. -/
def actualNormalCoordinates (r θ : ℂ) :
    (ActualConormal r θ →ₗ[ActualLocalCurve r θ] ActualLocalCurve r θ) ≃ₗ[ActualLocalCurve r θ]
      (Fin 3 → ActualLocalCurve r θ) :=
  (actualConormalBasis r θ).constr (ActualLocalCurve r θ) |>.symm

def localConormalClass (r θ : ℂ) (p : P) (hp : p∈ambientCurveIdeal r θ) :
    ActualConormal r θ :=
  (1:ActualLocalCurve r θ) ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent ⟨p,hp⟩

theorem localConormalClass_equation (r θ : ℂ) :
    localConormalClass r θ (actualSeedEquation r θ) (actualSeedEquation_mem r θ)=
      algebraMap P (ActualLocalCurve r θ) (originalG1 r) • actualConormalBasis r θ 0+
      algebraMap P (ActualLocalCurve r θ) originalG2 • actualConormalBasis r θ 1+
      algebraMap P (ActualLocalCurve r θ) (thetaK θ) • actualConormalBasis r θ 2 := by
  simpa only [localConormalClass,actualConormalBasis_apply] using
    (baseChangedConormal_relation (S := ActualLocalCurve r θ) r θ)

theorem localConormalClass_section (r θ : ℂ) :
    localConormalClass r θ (thetaH θ) (curveEquation_mem r θ 2)=
      actualConormalBasis r θ 2 := by
  rw [actualConormalBasis_apply]
  rfl

/-- Evaluate an actual normal homomorphism on the two actual equation
classes. Identifying the target with the full two-equation normal module
additionally uses its conormal basis, as constructed on a g1-unit chart. -/
def actualEquationNormalMap (r θ : ℂ) :
    (ActualConormal r θ →ₗ[ActualLocalCurve r θ] ActualLocalCurve r θ) →ₗ[ActualLocalCurve r θ]
      (Fin 2 → ActualLocalCurve r θ) where
  toFun φ := ![
    φ (localConormalClass r θ (actualSeedEquation r θ) (actualSeedEquation_mem r θ)),
    φ (localConormalClass r θ (thetaH θ) (curveEquation_mem r θ 2))]
  map_add' φ ψ := by ext i; fin_cases i <;> rfl
  map_smul' c φ := by ext i; fin_cases i <;> rfl

/-- The previously checked equation-normal matrix is exactly evaluation
on the actual (F,h) classes, in the proved source conormal basis. -/
theorem actualEquationNormalMap_eq (r θ : ℂ)
    (φ : ActualConormal r θ →ₗ[ActualLocalCurve r θ] ActualLocalCurve r θ) :
    actualEquationNormalMap r θ φ=
      equationMap
        (algebraMap P (ActualLocalCurve r θ) (originalG1 r))
        (algebraMap P (ActualLocalCurve r θ) originalG2)
        (algebraMap P (ActualLocalCurve r θ) (thetaK θ))
        (actualNormalCoordinates r θ φ) := by
  ext i
  fin_cases i
  · change φ (localConormalClass r θ (actualSeedEquation r θ) _) = _
    rw [localConormalClass_equation,map_add,map_add,map_smul,map_smul,map_smul]
    rfl
  · change φ (localConormalClass r θ (thetaH θ) _)=_
    rw [localConormalClass_section]
    rfl

/-- The explicit Jacobian open contains an actual complex point for every
nonzero r, including r=57.  Its conormal basis is not vacuous. -/
theorem exists_point_in_jacobian_open (r θ : ℂ) (hr : r≠0) :
    ∃ x : Fin 5 → ℂ,
      (∀ i : Fin 3, eval x (curveEquations r θ i)=0) ∧
      eval x (jacobianMinor r)≠0 := by
  let c : ℂ := (Complex.I-1)^((3:ℂ)⁻¹)
  have hc : c^3=Complex.I-1 := Complex.cpow_nat_inv_pow _ (by norm_num)
  have hi : Complex.I-1≠0 := by
    intro hh
    have him := congrArg Complex.im hh
    norm_num at him
  have hc0 : c≠0 := by
    intro hh
    apply hi
    simpa [hh] using hc.symm
  refine ⟨![0,0,c,1,-c^2],?_,?_⟩
  · intro j
    fin_cases j <;>
      simp [curveEquations,originalF1,originalF2,thetaH,originalH,originalB,hc] <;> ring
  · have he : eval ![0,0,c,1,-c^2] (jacobianMinor r)= -3*r*c^2 := by
      simp [jacobianMinor,firstPivot,secondPivot] <;> ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hr) (pow_ne_zero _ hc0)

end ActualLocalization
end CycleQ2ConormalJacobian

#print axioms CycleQ2ConormalJacobian.actualConormalBasis
#print axioms CycleQ2ConormalJacobian.surfaceConormalBasisOnFirstOpen
#print axioms CycleQ2ConormalJacobian.actualEquationNormalMap_eq
#print axioms CycleQ2ConormalJacobian.exists_point_in_jacobian_open
end
end


/- Component: continuation_20261111/SeedCurveGradient.lean -/
section
/-! The exact polynomial certificate binds to the literal r=57 curve
f1=h=0 after eliminating w=-x2^2.  Every relevant prime admits a
nonzero two-column normal Jacobian minor. This is the algebraic cover
needed before applying a geometric smoothness/Jacobian theorem. -/

noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CycleQ2SeedCurveGradient
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

def quadric : Poly ℂ := X 0^2 - C 57*X 1*X 3

def minor (j k : Fin 4) : Poly ℂ :=
  pderiv j.castSucc quadric * pderiv k.castSucc (smoothH Complex.I) -
    pderiv k.castSucc quadric * pderiv j.castSucc (smoothH Complex.I)

def minorPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def generators : Fin 8 → Poly ℂ :=
  ![quadric, smoothH Complex.I, minor 0 1, minor 0 2, minor 0 3,
    minor 1 2, minor 1 3, minor 2 3]

theorem quadric_derivative (j : Fin 4) :
    pderiv j.castSucc quadric =
      ![2*X 0, -C 57*X 3, 0, -C 57*X 1] j := by
  fin_cases j <;> simp [quadric, Derivation.leibniz, Fin.castSucc] <;> ring

theorem generators_binding (j : Fin 8) :
    CycleQ2SeedCurveGradientArithmetic.generators
      (C Complex.I) (X 0) (X 1) (X 2) (X 3) j = generators j := by
  have hc : (C (57 : ℂ) : Poly ℂ) = 57 := map_ofNat _ _
  have hn (k : Fin 5) : pderiv k (57 : Poly ℂ) = 0 := by
    rw [←hc]
    exact pderiv_C
  fin_cases j <;>
    simp [CycleQ2SeedCurveGradientArithmetic.generators, generators, minor,
      quadric, smoothH, smoothB, smoothA, map_ofNat, hn] <;>
    ring

theorem coordinate_power_identity (j : Fin 4) :
    (CycleQ2SeedCurveGradientArithmetic.denominator j : Poly ℂ) * X j.castSucc^6 =
      ∑ k, CycleQ2SeedCurveGradientArithmetic.numerators j
        (C Complex.I) (X 0) (X 1) (X 2) (X 3) k * generators k := by
  have hi : (C Complex.I : Poly ℂ)^2+1=0 := by
    rw [←map_pow, Complex.I_sq, map_neg, map_one]
    ring
  simp_rw [←generators_binding]
  fin_cases j
  · exact CycleQ2SeedCurveGradientArithmetic.identity0 _ _ _ _ _ hi
  · exact CycleQ2SeedCurveGradientArithmetic.identity1 _ _ _ _ _ hi
  · exact CycleQ2SeedCurveGradientArithmetic.identity2 _ _ _ _ _ hi
  · exact CycleQ2SeedCurveGradientArithmetic.identity3 _ _ _ _ _ hi

theorem denominator_ne_zero (j : Fin 4) :
    (CycleQ2SeedCurveGradientArithmetic.denominator j : ℂ) ≠ 0 := by
  fin_cases j <;> norm_num [CycleQ2SeedCurveGradientArithmetic.denominator]

def jacobianIdeal : Ideal (Poly ℂ) := Ideal.span (Set.range generators)

/-- Four actual coordinate sixth powers lie in the actual curve Jacobian
ideal over the complex numbers. -/
theorem coordinate_power_mem_jacobian (j : Fin 4) :
    (X j.castSucc : Poly ℂ)^6 ∈ jacobianIdeal := by
  have hsum : (CycleQ2SeedCurveGradientArithmetic.denominator j : Poly ℂ)*
      X j.castSucc^6 ∈ jacobianIdeal := by
    rw [coordinate_power_identity]
    apply Ideal.sum_mem
    intro k _
    apply Ideal.mul_mem_left
    exact Ideal.subset_span (Set.mem_range_self k)
  have h := Ideal.mul_mem_left jacobianIdeal
    (C ((CycleQ2SeedCurveGradientArithmetic.denominator j : ℂ)⁻¹)) hsum
  have hc : C ((CycleQ2SeedCurveGradientArithmetic.denominator j : ℂ)⁻¹)*
      (CycleQ2SeedCurveGradientArithmetic.denominator j : Poly ℂ)=1 := by
    rw [←map_natCast C, ←map_mul, inv_mul_cancel₀ (denominator_ne_zero j), map_one]
  simpa only [←mul_assoc, hc, one_mul] using h

/-- The curve Jacobian minors cover all relevant primes of the literal
quadric-cubic curve. -/
theorem prime_minor_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hf : quadric ∈ P) (hh : smoothH Complex.I ∈ P)
    (hx : ∃ j : Fin 4, X j.castSucc ∉ P) :
    ∃ j : Fin 6, minor (minorPairs j).1 (minorPairs j).2 ∉ P := by
  by_contra! hzero
  have hgen (j : Fin 8) : generators j ∈ P := by
    fin_cases j
    · exact hf
    · exact hh
    · exact hzero 0
    · exact hzero 1
    · exact hzero 2
    · exact hzero 3
    · exact hzero 4
    · exact hzero 5
  have hle : jacobianIdeal ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hgen j
  obtain ⟨j,hj⟩ := hx
  exact hj ((inferInstance : P.IsPrime).mem_of_pow_mem _
    (hle (coordinate_power_mem_jacobian j)))

/-- The same nonzero minor statement over every extension of the actual
complex coefficients. -/
theorem field_minor_cover {K : Type*} [Field K] (φ : Poly ℂ →+* K)
    (hf : φ quadric=0) (hh : φ (smoothH Complex.I)=0)
    (hx : ∃ j : Fin 4, φ (X j.castSucc) ≠ 0) :
    ∃ j : Fin 6, φ (minor (minorPairs j).1 (minorPairs j).2) ≠ 0 := by
  letI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  exact prime_minor_cover (RingHom.ker φ) hf hh hx


/-- Restore the eliminated weight-two coordinate. -/
def weightedEquation : Poly ℂ := X 4 + X 2^2

def curveEquations : Fin 3 → Poly ℂ := ![quadric, smoothH Complex.I, weightedEquation]

def normalMinor (j k : Fin 4) : Poly ℂ :=
  Matrix.det (fun a b : Fin 3 =>
    pderiv (![j.castSucc, k.castSucc, (4 : Fin 5)] b) (curveEquations a))

theorem normalMinor_eq (j k : Fin 4) : normalMinor j k = minor j k := by
  have hf : pderiv (4 : Fin 5) quadric=0 := by simp [quadric, Derivation.leibniz]
  have hh : pderiv (4 : Fin 5) (smoothH Complex.I : Poly ℂ)=0 := by
    simp [smoothH, smoothB, smoothA, Derivation.leibniz]
  have hw : pderiv (4 : Fin 5) weightedEquation=1 := by
    simp [weightedEquation]
  unfold normalMinor
  rw [Matrix.det_fin_three]
  simp [curveEquations, hf, hh, hw, minor]

theorem base_coordinate_of_weighted_equation (P : Ideal (Poly ℂ))
    (hw : weightedEquation ∈ P) (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j : Fin 4, X j.castSucc ∉ P := by
  by_contra! hbase
  have hfour : (X (4 : Fin 5) : Poly ℂ) ∈ P := by
    have hx2 : (X (2 : Fin 5) : Poly ℂ)^2 ∈ P :=
      Ideal.pow_mem_of_mem P (hbase 2) 2 (by decide)
    have he : X (4 : Fin 5) = weightedEquation-X 2^2 := by
      unfold weightedEquation
      ring
    rw [he]
    exact P.sub_mem hw hx2
  obtain ⟨j,hj⟩ := hx
  fin_cases j
  · exact hj (hbase 0)
  · exact hj (hbase 1)
  · exact hj (hbase 2)
  · exact hj (hbase 3)
  · exact hj hfour

/-- Actual three-equation normal Jacobian cover for the weighted seed
curve f1=h=(w+x2^2)=0, including all projective coordinate charts. -/
theorem weighted_prime_normal_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (he : ∀ a : Fin 3, curveEquations a ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j : Fin 6, normalMinor (minorPairs j).1 (minorPairs j).2 ∉ P := by
  have hbase := base_coordinate_of_weighted_equation P (he 2) hx
  obtain ⟨j,hj⟩ := prime_minor_cover P (he 0) (he 1) hbase
  exact ⟨j, by simpa only [normalMinor_eq] using hj⟩

theorem weighted_field_normal_cover {K : Type*} [Field K]
    (φ : Poly ℂ →+* K) (he : ∀ a : Fin 3, φ (curveEquations a)=0)
    (hx : ∃ j : Fin 5, φ (X j) ≠ 0) :
    ∃ j : Fin 6, IsUnit (φ (normalMinor (minorPairs j).1 (minorPairs j).2)) := by
  letI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨j,hj⟩ := weighted_prime_normal_cover (RingHom.ker φ) he hx
  exact ⟨j, isUnit_iff_ne_zero.mpr hj⟩

end CycleQ2SeedCurveGradient

#print axioms CycleQ2SeedCurveGradient.prime_minor_cover
#print axioms CycleQ2SeedCurveGradient.field_minor_cover

#print axioms CycleQ2SeedCurveGradient.weighted_prime_normal_cover
#print axioms CycleQ2SeedCurveGradient.weighted_field_normal_cover
end
end


/- Component: continuation_20261111/SurfaceLocalDerivations.lean -/
section
/-!
# Actual local lifts of a deformation derivation on a complete intersection

For F=h=0 the inverse of a two-by-two Jacobian minor gives a literal
correction of the coefficient derivation.  It annihilates both defining
equations, preserves their ideal, and descends to the actual quotient ring.
The localization constructor below supplies the ambient derivations on the
minor open; no tangent derivation or quotient compatibility is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SurfaceLocalDerivations

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

def minor (Da Db : Derivation K R R) (F h : R) : R :=
  Da F * Db h - Db F * Da h

/-- Cramer's rule, with signs chosen so D(F)=D(h)=0. -/
def corrected (D Da Db : Derivation K R R) (F h : R) (u : Rˣ) :
    Derivation K R R :=
  D + ((Db F * D h - Db h * D F) * (↑(u⁻¹) : R)) • Da +
    ((Da h * D F - Da F * D h) * (↑(u⁻¹) : R)) • Db

theorem corrected_F (D Da Db : Derivation K R R) (F h : R) (u : Rˣ)
    (hu : (u : R) = minor Da Db F h) :
    corrected D Da Db F h u F = 0 := by
  have hi := u.mul_inv
  rw [hu] at hi
  dsimp [minor] at hi
  simp only [corrected, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]
  linear_combination -(D F) * hi

theorem corrected_h (D Da Db : Derivation K R R) (F h : R) (u : Rˣ)
    (hu : (u : R) = minor Da Db F h) :
    corrected D Da Db F h u h = 0 := by
  have hi := u.mul_inv
  rw [hu] at hi
  dsimp [minor] at hi
  simp only [corrected, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]
  linear_combination -(D h) * hi

theorem corrected_on_constants (D Da Db : Derivation K R R) (F h c : R) (u : Rˣ)
    (ha : Da c = 0) (hb : Db c = 0) :
    corrected D Da Db F h u c = D c := by
  simp [corrected, ha, hb]

def equationIdeal (F h : R) : Ideal R := Ideal.span ({F, h} : Set R)

theorem preserves_equationIdeal (E : Derivation K R R) (F h : R)
    (hF : E F = 0) (hh : E h = 0) (a : R) (ha : a ∈ equationIdeal F h) :
    E a ∈ equationIdeal F h := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · rw [hx, hF]; exact Ideal.zero_mem _
      · rw [Set.mem_singleton_iff.mp hx, hh]; exact Ideal.zero_mem _
  | zero => simpa only [map_zero] using (Ideal.zero_mem (equationIdeal F h))
  | add x y hx hy hdx hdy =>
      rw [map_add]
      exact Ideal.add_mem _ hdx hdy
  | smul a x hx hdx =>
      change E (a * x) ∈ equationIdeal F h
      rw [Derivation.leibniz]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ a hdx)
        (Ideal.mul_mem_right (E a) _ hx)

/-- A derivation annihilating the equations descends to the actual quotient. -/
def quotientDerivation (E : Derivation K R R) (F h : R)
    (hF : E F = 0) (hh : E h = 0) :
    Derivation K (R ⧸ equationIdeal F h) (R ⧸ equationIdeal F h) :=
  Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective K (equationIdeal F h))
    (d := E) (by
      intro x hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (preserves_equationIdeal E F h hF hh x (Ideal.Quotient.eq_zero_iff_mem.mp hx)))

@[simp] theorem quotientDerivation_mk (E : Derivation K R R) (F h : R)
    (hF : E F = 0) (hh : E h = 0) (a : R) :
    quotientDerivation E F h hF hh (Ideal.Quotient.mk (equationIdeal F h) a) =
      Ideal.Quotient.mk (equationIdeal F h) (E a) := by
  unfold quotientDerivation
  exact Derivation.liftOfSurjective_apply _ _ a

/-- The local lift is constructed from the ambient coefficient motion and
two ambient coordinate derivations by the proved Cramer's correction. -/
def localLift (D Da Db : Derivation K R R) (F h : R) (u : Rˣ)
    (hu : (u : R) = minor Da Db F h) :
    Derivation K (R ⧸ equationIdeal F h) (R ⧸ equationIdeal F h) :=
  quotientDerivation (corrected D Da Db F h u) F h
    (corrected_F D Da Db F h u hu) (corrected_h D Da Db F h u hu)

theorem localLift_mk (D Da Db : Derivation K R R) (F h : R) (u : Rˣ)
    (hu : (u : R) = minor Da Db F h) (a : R) :
    localLift D Da Db F h u hu (Ideal.Quotient.mk (equationIdeal F h) a) =
      Ideal.Quotient.mk (equationIdeal F h)
        (D a + (Db F * D h - Db h * D F) * (↑(u⁻¹) : R) * Da a +
          (Da h * D F - Da F * D h) * (↑(u⁻¹) : R) * Db a) := by
  rw [localLift, quotientDerivation_mk]
  rfl

theorem localLift_on_constants (D Da Db : Derivation K R R) (F h c : R) (u : Rˣ)
    (hu : (u : R) = minor Da Db F h) (ha : Da c = 0) (hb : Db c = 0) :
    localLift D Da Db F h u hu (Ideal.Quotient.mk (equationIdeal F h) c) =
      Ideal.Quotient.mk (equationIdeal F h) (D c) := by
  rw [localLift, quotientDerivation_mk, corrected_on_constants D Da Db F h c u ha hb]

section Localization

variable (D Da Db : Derivation K R R) (F h : R)

abbrev MinorOpen := Localization.Away (minor Da Db F h)

def openDerivation (E : Derivation K R R) :
    Derivation K (MinorOpen Da Db F h) (MinorOpen Da Db F h) :=
  CycleQ2LocalizationDerivation.extend (Submonoid.powers (minor Da Db F h)) E

theorem openDerivation_map (E : Derivation K R R) (a : R) :
    openDerivation Da Db F h E (algebraMap R (MinorOpen Da Db F h) a) =
      algebraMap R (MinorOpen Da Db F h) (E a) :=
  CycleQ2LocalizationDerivation.extend_map _ E a

theorem open_minor :
    minor (openDerivation Da Db F h Da) (openDerivation Da Db F h Db)
      (algebraMap R (MinorOpen Da Db F h) F) (algebraMap R (MinorOpen Da Db F h) h) =
      algebraMap R (MinorOpen Da Db F h) (minor Da Db F h) := by
  simp only [minor, openDerivation_map, map_sub, map_mul]

/-- The actual localization makes the required Jacobian minor a unit. -/
def minorUnit : (MinorOpen Da Db F h)ˣ :=
  (IsLocalization.map_units (MinorOpen Da Db F h)
    ⟨minor Da Db F h, Submonoid.mem_powers _⟩).unit

theorem minorUnit_val :
    (minorUnit Da Db F h : MinorOpen Da Db F h) =
      minor (openDerivation Da Db F h Da) (openDerivation Da Db F h Db)
        (algebraMap R (MinorOpen Da Db F h) F) (algebraMap R (MinorOpen Da Db F h) h) := by
  rw [open_minor]
  exact IsUnit.unit_spec _

abbrev LocalSurface := (MinorOpen Da Db F h) ⧸
  equationIdeal (algebraMap R (MinorOpen Da Db F h) F)
    (algebraMap R (MinorOpen Da Db F h) h)

/-- A local derivation on the literal minor-localized surface, produced
without assuming a coordinate lift or quotient stability. -/
def surfaceDerivation : Derivation K (LocalSurface Da Db F h) (LocalSurface Da Db F h) :=
  localLift (openDerivation Da Db F h D) (openDerivation Da Db F h Da)
    (openDerivation Da Db F h Db) _ _ (minorUnit Da Db F h) (minorUnit_val Da Db F h)

/-- The actual local lift induces the original motion on every coefficient
annihilated by the chosen coordinate derivations. -/
theorem surfaceDerivation_on_constants (c : R) (ha : Da c = 0) (hb : Db c = 0) :
    surfaceDerivation D Da Db F h
      (Ideal.Quotient.mk _ (algebraMap R (MinorOpen Da Db F h) c)) =
      Ideal.Quotient.mk _ (algebraMap R (MinorOpen Da Db F h) (D c)) := by
  unfold surfaceDerivation
  rw [localLift_on_constants (openDerivation Da Db F h D)
    (openDerivation Da Db F h Da) (openDerivation Da Db F h Db) _ _ _
    (minorUnit Da Db F h) (minorUnit_val Da Db F h)
    (by rw [openDerivation_map, ha, map_zero])
    (by rw [openDerivation_map, hb, map_zero]), openDerivation_map]

end Localization
end CycleQ2SurfaceLocalDerivations

#print axioms CycleQ2SurfaceLocalDerivations.localLift_mk
#print axioms CycleQ2SurfaceLocalDerivations.localLift_on_constants
#print axioms CycleQ2SurfaceLocalDerivations.surfaceDerivation
#print axioms CycleQ2SurfaceLocalDerivations.surfaceDerivation_on_constants
end
end


/- Component: continuation_20261111/IncidenceLocalDerivations.lean -/
section
/-!
# Local deformation lifts for the actual finite trace family

The coefficient motion is the already constructed derivative on the actual
finite extension of the trace parameter field.  The two equations are the
actual specialized invariant sextic and cubic, not independent model
equations.  The sextic is fixed by this motion.  On every two-by-two Jacobian
minor open, a derivation on the actual quotient is constructed explicitly.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceLocalDerivations

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2SegreFullJacobianBounds CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceFieldDerivation CycleQ2IncidenceTraceGeometry
  CycleQ2IncidenceGenericPointSemantics CycleQ2SurfaceLocalDerivations
  CycleQ2PolynomialCoefficientDerivation CycleQ2PolynomialAffineSlice
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

variable {L : Type} [Field L] [Algebra TraceField L]
  [Algebra TraceRing L] [IsScalarTower TraceRing TraceField L]
  [Algebra ℂ L] [IsScalarTower ℂ TraceRing L] [FiniteDimensional TraceField L]

def timePolynomial : Derivation ℂ (MvPolynomial (Fin 5) L) (MvPolynomial (Fin 5) L) :=
  coefficientDerivation (timeDerivation (L := L))

def coordinateDerivation (j : Fin 5) :
    Derivation ℂ (MvPolynomial (Fin 5) L) (MvPolynomial (Fin 5) L) :=
  (pderiv j : Derivation L (MvPolynomial (Fin 5) L) (MvPolynomial (Fin 5) L)).restrictScalars ℂ

theorem time_fullInvariantPolynomial (d : ℕ) (c : FullInvariantIndex d → L) :
    timePolynomial (fullInvariantPolynomial d c) =
      fullInvariantPolynomial d (fun j => timeDerivation (c j)) := by
  unfold fullInvariantPolynomial timePolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact coefficientDerivation_monomial _ _ _

def actualF (B : Matrix FixedSexticParameters SquareIndex ℂ) (z : SquareIndex → L) :
    MvPolynomial (Fin 5) L :=
  fullInvariantPolynomial 6 (pointSextic (tracePointValue B z))

def actualH (B : Matrix FixedSexticParameters SquareIndex ℂ) (z : SquareIndex → L) :
    MvPolynomial (Fin 5) L :=
  fullInvariantPolynomial 3 (pointCubic (tracePointValue B z))

theorem actualF_eq_specialized (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) :
    actualF B z = MvPolynomial.map
      (CycleQ2IncidenceImageLine.pointMap (tracePointValue B z))
      CycleQ2IncidenceBasepointOpen.familyF :=
  (CycleQ2IncidenceImageLine.pointMap_familyF (tracePointValue B z)).symm

theorem actualH_eq_specialized (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) :
    actualH B z = MvPolynomial.map
      (CycleQ2IncidenceImageLine.pointMap (tracePointValue B z))
      CycleQ2IncidenceBasepointOpen.familyH :=
  (CycleQ2IncidenceImageLine.pointMap_familyH (tracePointValue B z)).symm

/-- The actual family keeps the sextic fixed under its trace parameter. -/
theorem time_actualF (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) : timePolynomial (actualF B z) = 0 := by
  rw [actualF, time_fullInvariantPolynomial]
  have hc (j : FullInvariantIndex 6) :
      timeDerivation (pointSextic (tracePointValue B z) j) = 0 := by
    change timeDerivation
      (pointValue (algebraMap TraceRing L) centre (directions B) z
        (Sum.inr (Sum.inl j))) = 0
    rw [sextic_coordinate_fixed, timeDerivation_sexticParameter]
  simp only [hc, fullInvariantPolynomial, map_zero, Finset.sum_const_zero]

theorem coordinateDerivation_C (j : Fin 5) (c : L) :
    coordinateDerivation j (C c) = 0 := by
  exact pderiv_C

abbrev ActualLocalSurface (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) (i j : Fin 5) :=
  LocalSurface (coordinateDerivation i) (coordinateDerivation j) (actualF B z) (actualH B z)

/-- This derivation exists on the actual minor-localized quotient without
assuming a tangent lift or its compatibility with either defining equation.
A separate Jacobian-cover theorem is needed to cover the surface by these
opens; this constructor alone does not assert that an open is nonempty. -/
def actualLocalTime (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) (i j : Fin 5) :
    Derivation ℂ (ActualLocalSurface B z i j) (ActualLocalSurface B z i j) :=
  surfaceDerivation timePolynomial (coordinateDerivation i) (coordinateDerivation j)
    (actualF B z) (actualH B z)

/-- Every constructed local lift restricts to the same actual derivation
of the finite coefficient field. -/
theorem actualLocalTime_coefficients (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) (i j : Fin 5) (c : L) :
    actualLocalTime B z i j
      (Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin 5) L)
        (MinorOpen (coordinateDerivation i) (coordinateDerivation j)
          (actualF B z) (actualH B z)) (C c))) =
      Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin 5) L)
        (MinorOpen (coordinateDerivation i) (coordinateDerivation j)
          (actualF B z) (actualH B z)) (C (timeDerivation c))) := by
  unfold actualLocalTime
  rw [surfaceDerivation_on_constants _ _ _ _ _ (C c)
    (coordinateDerivation_C i c) (coordinateDerivation_C j c)]
  rw [timePolynomial, coefficientDerivation_C]

end CycleQ2IncidenceLocalDerivations

#print axioms CycleQ2IncidenceLocalDerivations.time_actualF
#print axioms CycleQ2IncidenceLocalDerivations.actualLocalTime
#print axioms CycleQ2IncidenceLocalDerivations.actualLocalTime_coefficients
end
end


/- Component: continuation_20261111/SeedConormalCover.lean -/
section
/-! The exact seed Jacobian certificate supplies actual conormal bases at
every relevant prime of the curve, including nonclosed primes. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ConormalCover
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian

abbrev I : Ideal P := ambientCurveIdeal 57 1
abbrev Q := ActualCurve 57 1

def generatorOrder : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

theorem gradient_generator_eq (j : Fin 3) :
    CycleQ2SeedCurveGradient.curveEquations j=
      curveEquations 57 1 (generatorOrder j) := by
  fin_cases j <;>
    simp [CycleQ2SeedCurveGradient.curveEquations,CycleQ2SeedCurveGradient.quadric,
      CycleQ2SeedCurveGradient.weightedEquation,curveEquations,generatorOrder,
      Equiv.swap_apply_def,originalF1,originalF2,←smoothH_eq_thetaH]

theorem gradient_span_eq :
    Ideal.span (Set.range CycleQ2SeedCurveGradient.curveEquations)=I := by
  unfold I ambientCurveIdeal
  congr 1
  ext p
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨generatorOrder j,(gradient_generator_eq j).symm⟩
  · rintro ⟨j,rfl⟩
    refine ⟨generatorOrder.symm j,?_⟩
    simpa using gradient_generator_eq (generatorOrder.symm j)

variable (q : Ideal Q) [q.IsPrime]

abbrev PrimeCurve := Localization.AtPrime q

def primeMap : P →+* PrimeCurve q :=
  (algebraMap Q (PrimeCurve q)).comp (Ideal.Quotient.mk I)

instance primeScalarTower : IsScalarTower ℂ P (PrimeCurve q) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := P) (A := PrimeCurve q)
    fun _ => rfl

theorem primeMap_ideal (p : P) (hp : p∈I) :
    algebraMap P (PrimeCurve q) p=0 := by
  change algebraMap Q (PrimeCurve q) (Ideal.Quotient.mk I p)=0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp,map_zero]

def minorCoordinates (j : Fin 6) : Fin 3 → Fin 5 :=
  ![(CycleQ2SeedCurveGradient.minorPairs j).1.castSucc,
    (CycleQ2SeedCurveGradient.minorPairs j).2.castSucc,4]

theorem mapped_minor_det (j : Fin 6) :
    (derivationMatrix CycleQ2SeedCurveGradient.curveEquations
      (fun i => mappedPartial (S := PrimeCurve q) (minorCoordinates j i))).det=
      algebraMap P (PrimeCurve q)
        (CycleQ2SeedCurveGradient.normalMinor
          (CycleQ2SeedCurveGradient.minorPairs j).1
          (CycleQ2SeedCurveGradient.minorPairs j).2) := by
  let A : Matrix (Fin 3) (Fin 3) P := fun a b =>
    pderiv (minorCoordinates j b) (CycleQ2SeedCurveGradient.curveEquations a)
  have hm : derivationMatrix CycleQ2SeedCurveGradient.curveEquations
      (fun i => mappedPartial (S := PrimeCurve q) (minorCoordinates j i))=
        ((algebraMap P (PrimeCurve q)).mapMatrix A).transpose := by
    ext a b
    rfl
  rw [hm,Matrix.det_transpose,←RingHom.map_det]
  rfl

/-- The ideal cotangent module localized at every relevant prime has the
actual three equation classes as a basis. The Jacobian-unit premise has
been discharged by the exact coordinate-power certificate. -/
theorem exists_actual_conormal_basis
    (hx : ∃ j : Fin 5, Ideal.Quotient.mk I (X j)∉q) :
    ∃ b : Module.Basis (Fin 3) (PrimeCurve q) (PrimeCurve q ⊗[P] I.Cotangent),
      ∀ i, b i=(1:PrimeCurve q) ⊗ₜ[P] conormalGenerator 57 1 i := by
  let p : Ideal P := q.comap (Ideal.Quotient.mk I)
  have he (a : Fin 3) : CycleQ2SeedCurveGradient.curveEquations a∈p := by
    change Ideal.Quotient.mk I (CycleQ2SeedCurveGradient.curveEquations a)∈q
    have ha : CycleQ2SeedCurveGradient.curveEquations a∈I :=
      gradient_span_eq ▸ Ideal.subset_span ⟨a,rfl⟩
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact q.zero_mem
  obtain ⟨j,hj⟩ := CycleQ2SeedCurveGradient.weighted_prime_normal_cover p he hx
  have hu : IsUnit (algebraMap P (PrimeCurve q)
      (CycleQ2SeedCurveGradient.normalMinor
        (CycleQ2SeedCurveGradient.minorPairs j).1
        (CycleQ2SeedCurveGradient.minorPairs j).2)) :=
    IsLocalization.map_units (M := q.primeCompl) (PrimeCurve q) ⟨_,hj⟩
  have hd : IsUnit (derivationMatrix CycleQ2SeedCurveGradient.curveEquations
      (fun i => mappedPartial (S := PrimeCurve q) (minorCoordinates j i))).det := by
    rwa [mapped_minor_det]
  let b := conormalBasisOfJacobian I (primeMap_ideal q)
    CycleQ2SeedCurveGradient.curveEquations gradient_span_eq
    (fun i => mappedPartial (S := PrimeCurve q) (minorCoordinates j i)) hd
  refine ⟨b.reindex generatorOrder,?_⟩
  intro i
  rw [Module.Basis.reindex_apply]
  dsimp [b]
  rw [conormalBasisOfJacobian_apply]
  simp only [generator,conormalGenerator,gradient_generator_eq,Equiv.apply_symm_apply]

end CycleQ2ConormalCover

#print axioms CycleQ2ConormalCover.exists_actual_conormal_basis
end
end

/- Component: continuation_20261111/SeedNaturalNormalMap.lean -/
section
/-!
# The natural conormal map and the actual normal matrix

For the literal seed ideals J=(F,h) and I=(f1,f2,h), the inclusion J <= I
induces the actual map J/J^2 -> I/I^2. Scalar extension and dualization give
an S-linear map between the genuine normal modules. Evaluation on the
actual equation classes identifies this dual map with the existing normal
matrix, and with the existing actualEquationNormalMap on its seed chart.

The local basis comparison uses the already constructed source derivative
duals and a unit value of g1. Both coordinate identifications are therefore
actual conormal bases. The graded global normal sequence and its connecting
class require further chart compatibility and gluing.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2NaturalNormalMap

open CycleQ2ConormalJacobian CycleQ2NormalConnecting CycleQ2SeedTrace

section ScalarExtension

variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

/-- With the already constructed source and target conormal bases, the
same identity is an identity in coordinates on both genuine normal modules.
The hypotheses are the existing local source derivation duals and a g1 unit;
no assumed normal presentation or normal-map comparison is introduced. -/
theorem naturalNormalMap_in_equation_bases (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap P S p = 0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j) = if i = j then 1 else 0)
    (u : Sˣ) (hu : (u : S) = algebraMap P S (originalG1 r))
    (φ : S ⊗[P] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S) :
    ((surfaceConormalBasisOnFirstOpen r θ hI d hd u hu).constr S).symm
        (naturalNormalMap r θ φ) =
      equationMap (algebraMap P S (originalG1 r))
        (algebraMap P S originalG2) (algebraMap P S (thetaK θ))
        (((conormalBasis (ambientCurveIdeal r θ) hI
          (curveEquations r θ) rfl d hd).constr S).symm φ) := by
  change (fun j => naturalNormalMap r θ φ
      (surfaceConormalBasisOnFirstOpen r θ hI d hd u hu j)) =
    equationMap (algebraMap P S (originalG1 r))
      (algebraMap P S originalG2) (algebraMap P S (thetaK θ))
      (fun i => φ (conormalBasis (ambientCurveIdeal r θ) hI
        (curveEquations r θ) rfl d hd i))
  simpa only [surfaceConormalBasisOnFirstOpen, conormalBasis_apply,
    generator, conormalGenerator] using
      naturalNormalMap_equation_coordinates (S := S) r θ φ

end ScalarExtension

/-- Direct binding to the existing actualEquationNormalMap on its literal
nonempty Jacobian chart. This identifies the local evaluation map with the natural dual map. -/
theorem actualEquationNormalMap_eq_naturalNormalMap (r θ : ℂ)
    (φ : ActualConormal r θ →ₗ[ActualLocalCurve r θ] ActualLocalCurve r θ) :
    actualEquationNormalMap r θ φ =
      (fun j : Fin 2 => naturalNormalMap (S := ActualLocalCurve r θ) r θ φ
        (generator (S := ActualLocalCurve r θ)
          (surfaceIdeal r θ) (surfaceEquations r θ) rfl j)) := by
  funext j
  fin_cases j <;> rfl

end CycleQ2NaturalNormalMap

#print axioms CycleQ2NaturalNormalMap.naturalNormalMap_equation_coordinates
#print axioms CycleQ2NaturalNormalMap.naturalNormalMap_in_equation_bases
#print axioms CycleQ2NaturalNormalMap.actualEquationNormalMap_eq_naturalNormalMap

end
end

/- Preserved entry-point body; the sole admission follows all helpers. -/


/- Component: continuation_20261112/ConormalRegularSequence.lean -/
section
/-! Genuine conormal coordinates from relations among ideal generators.
The finite-relation criterion below is proved for regular sequences of
length two and three. It does not require the ambient quotient to be smooth.
-/

noncomputable section
open scoped BigOperators TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false



#print axioms CycleQ2ConormalRegular.conormalBasis
#print axioms CycleQ2ConormalRegular.triple_relation_coefficients
end
end


/- Component: continuation_20261112/SeedRegularLeading.lean -/
section
/-!
# Leading terms of the actual seed equations

The auxiliary weights on (x0,x1,x2,x3,w) are (3,1,4,1,9).
They give pairwise disjoint monic leading terms x0^2, w, x2^3 for
the actual three curve equations, and w^3, x2^3 for the two surface
equations.  Every statement holds for arbitrary complex r and theta;
there is no Jacobian localization or cube-root restriction.

The standalone algebraic dependency chain supplies the definitions and
earlier lemmas.  No admitted declaration is used by these proofs.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false



#print axioms CycleQ2SeedRegularLeading.f1_leading_data
#print axioms CycleQ2SeedRegularLeading.f2_leading_data
#print axioms CycleQ2SeedRegularLeading.h_leading_data
#print axioms CycleQ2SeedRegularLeading.F_leading_data
#print axioms CycleQ2SeedRegularLeading.F_h_coprime
end
end


