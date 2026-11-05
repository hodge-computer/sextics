import HodgeTarget
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring

/-!
# A strict certificate for the protected one-reflection instance

Prepared with OpenAI ChatGPT assistance for a contribution through GitHub account fqlx.

This source contains the certificate construction, the two polynomial identities,
homogeneity and denominator legality proofs, and the final exact-target theorem.
The named sections retain the original proof organization while placing every
candidate declaration in one compilation unit. Section names do not change the
namespaces of any definitions or theorems.

The protected polynomial F, numerator A, and pole order q are imported exclusively
from HodgeTarget. The final declaration is Submission.certificate.
-/

/-! ## CertificateConstruction -/

section CertificateConstructionSection

/-!
# Constructive operations on exact certificates

Developmental helper lemmas for the fixed one-reflection search. These do not
supply a certificate for that instance. Prepared with OpenAI ChatGPT assistance
for a contribution through GitHub account fqlx.

The hidden P/M reflections and target decomposition are credited to fringewidth
in data/one-reflection/why.md and instance discussion #54. The constructions here
show how to assemble a future sector witness using the exact Verify predicate.
-/

noncomputable section

namespace HodgeComputer.Construction

open MvPolynomial HodgeTestbed
open scoped BigOperators

theorem directional_add (P : Poly) (N M : Fin 6 → Poly) :
    directional P (fun i => N i + M i) = directional P N + directional P M := by
  simp [directional, mul_add, Finset.sum_add_distrib]

theorem divergence_add (N M : Fin 6 → Poly) :
    divergence (fun i => N i + M i) = divergence N + divergence M := by
  simp [divergence, map_add, Finset.sum_add_distrib]

theorem divergenceNumerator_add (D : Poly) (N M : Fin 6 → Poly) :
    divergenceNumerator D (fun i => N i + M i) =
      divergenceNumerator D N + divergenceNumerator D M := by
  simp only [divergenceNumerator, divergence_add, directional_add]
  ring

theorem defect_add_same_denominator (F A B D : Poly) (q : ℕ)
    (N M : Fin 6 → Poly) :
    defect F (A+B) D q (fun i => N i + M i) =
      defect F A D q N + defect F B D q M := by
  simp only [defect, directional_add, divergenceNumerator_add]
  ring

theorem defect_scale_denominator (F A D H : Poly) (q : ℕ)
    (N : Fin 6 → Poly) :
    defect F A (H*D) q (fun i => H*N i) = H^2 * defect F A D q N := by
  simp only [defect, HodgeTestbed.directional_mul, HodgeTestbed.divergenceNumerator_mul]
  ring

/-- Add rational fields using the product of their denominators. The quotient
contains both old remainders; neither certificate has to be strict. -/
theorem defect_add (F A B D E : Poly) (q : ℕ) (N M : Fin 6 → Poly) :
    defect F (A+B) (D*E) q (fun i => E*N i + D*M i) =
      E^2 * defect F A D q N + D^2 * defect F B E q M := by
  rw [defect_add_same_denominator]
  conv_lhs => lhs; rw [mul_comm D E]
  rw [defect_scale_denominator, defect_scale_denominator]

/-- Construct an exact certificate for the sum of targets at pole parameter one.
The new denominator degree is the sum of the original degrees. -/
theorem Verify.add_q1 {F A B D E Q R : Poly} {d e : ℕ}
    {N M : Fin 6 → Poly}
    (h : Verify F A 1 d D N Q) (k : Verify F B 1 e E M R) :
    Verify F (A+B) 1 (d+e) (D*E) (fun i => E*N i + D*M i)
      (E^2*Q + D^2*R) where
  denominator_ne_zero := mul_ne_zero h.denominator_ne_zero k.denominator_ne_zero
  denominator_homogeneous := h.denominator_homogeneous.mul k.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    have hn := k.denominator_homogeneous.mul (h.numerator_homogeneous i)
    have hm := h.denominator_homogeneous.mul (k.numerator_homogeneous i)
    have hnd : e + (d + 6*1 - 5) = (d+e) + 6*1 - 5 := by omega
    have hmd : d + (e + 6*1 - 5) = (d+e) + 6*1 - 5 := by omega
    rw [hnd] at hn
    rw [hmd] at hm
    exact hn.add hm
  denominator_legal := h.denominator_legal.mul_right k.denominator_legal
  identity := by
    rw [defect_add, h.identity, k.identity]
    ring

theorem HasCertificate.add_q1 {F A B : Poly}
    (h : HasCertificate F A 1) (k : HasCertificate F B 1) :
    HasCertificate F (A+B) 1 := by
  obtain ⟨d, D, N, Q, h⟩ := h
  obtain ⟨e, E, M, R, k⟩ := k
  exact ⟨d+e, D*E, (fun i => E*N i + D*M i), E^2*Q+D^2*R, Verify.add_q1 h k⟩

def signChange (s : Fin 6 → ℂ) : Poly →+* Poly :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => C (s i) * X i)

@[simp] theorem signChange_C (s : Fin 6 → ℂ) (c : ℂ) :
    signChange s (C c) = C c := by simp [signChange]

@[simp] theorem signChange_X (s : Fin 6 → ℂ) (i : Fin 6) :
    signChange s (X i) = C (s i) * X i := by simp [signChange]

theorem signChange_involutive (s : Fin 6 → ℂ) (hs : ∀ i, s i * s i = 1) :
    (signChange s).comp (signChange s) = RingHom.id Poly := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp
  · intro i
    simp only [RingHom.comp_apply, RingHom.id_apply, signChange_X, map_mul, signChange_C]
    rw [← mul_assoc, ← map_mul, hs, map_one, one_mul]

@[simp] theorem signChange_twice (s : Fin 6 → ℂ) (hs : ∀ i, s i * s i = 1) (p : Poly) :
    signChange s (signChange s p) = p :=
  DFunLike.congr_fun (signChange_involutive s hs) p

theorem pderiv_signChange (s : Fin 6 → ℂ) (i : Fin 6) (p : Poly) :
    pderiv i (signChange s p) = C (s i) * signChange s (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, mul_add]
  | mul_X p j hp =>
    simp only [map_mul, signChange_X, pderiv_mul, pderiv_C, hp, map_add]
    by_cases hj : j = i
    · subst j; simp only [pderiv_X_self, map_one]; ring
    · simp only [pderiv_X_of_ne hj, map_zero]; ring

def signField (s : Fin 6 → ℂ) (N : Fin 6 → Poly) : Fin 6 → Poly :=
  fun i => C (s i) * signChange s (N i)

theorem directional_signChange (s : Fin 6 → ℂ) (hs : ∀ i, s i * s i = 1)
    (p : Poly) (N : Fin 6 → Poly) :
    directional (signChange s p) (signField s N) = signChange s (directional p N) := by
  simp only [directional, signField, pderiv_signChange, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [show C (s i) * signChange s (pderiv i p) *
      (C (s i) * signChange s (N i)) =
      C (s i * s i) * (signChange s (pderiv i p) * signChange s (N i)) by
        rw [map_mul]; ring, hs, map_one, one_mul]

theorem divergence_signField (s : Fin 6 → ℂ) (hs : ∀ i, s i * s i = 1)
    (N : Fin 6 → Poly) :
    divergence (signField s N) = signChange s (divergence N) := by
  simp only [divergence, signField, pderiv_C_mul, pderiv_signChange, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← mul_assoc, ← map_mul, hs, map_one, one_mul]

theorem divergenceNumerator_signChange (s : Fin 6 → ℂ) (hs : ∀ i, s i * s i = 1)
    (D : Poly) (N : Fin 6 → Poly) :
    divergenceNumerator (signChange s D) (signField s N) =
      signChange s (divergenceNumerator D N) := by
  simp only [divergenceNumerator, divergence_signField s hs,
    directional_signChange s hs, map_sub, map_mul]

theorem signChange_homogeneous (s : Fin 6 → ℂ) {p : Poly} {d : ℕ}
    (h : p.IsHomogeneous d) : (signChange s p).IsHomogeneous d := by
  simpa only [signChange, coe_eval₂Hom, one_mul] using
    h.eval₂ C (fun i => C (s i) * X i)
      (fun c => isHomogeneous_C (Fin 6) c)
      (fun i => isHomogeneous_C_mul_X (s i) i)

/-- Pull a certificate through a diagonal sign involution. Polynomial
substitution alone is insufficient: every field component also receives its
coordinate's sign, which is necessary for both derivative identities. -/
theorem Verify.sign_change (s : Fin 6 → ℂ) (hs : ∀ i, s i * s i = 1)
    {F A D Q : Poly} {q d : ℕ} {N : Fin 6 → Poly}
    (h : Verify F A q d D N Q) :
    Verify (signChange s F) (signChange s A) q d (signChange s D)
      (signField s N) (signChange s Q) where
  denominator_ne_zero := by
    intro hz
    have ht := congrArg (signChange s) hz
    rw [signChange_twice s hs, map_zero] at ht
    exact h.denominator_ne_zero ht
  denominator_homogeneous := signChange_homogeneous s h.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    exact (signChange_homogeneous s (h.numerator_homogeneous i)).C_mul (s i)
  denominator_legal := by
    apply relPrime_of_retract (signChange s) (signChange s) (signChange_involutive s hs)
    simpa only [signChange_twice s hs] using h.denominator_legal
  identity := by
    have hi := congrArg (signChange s) h.identity
    simpa only [defect, directional_signChange s hs,
      divergenceNumerator_signChange s hs, map_add, map_sub, map_mul, map_pow, map_natCast] using hi

namespace OneReflection

def P : Poly := X 3 + X 4
def M : Poly := X 3 - X 4
def Aplus : Poly := C (1/8 : ℂ) * X 0 ^ 3 * P * (P^2 + 3*M^2)
def Aminus : Poly := C (1/8 : ℂ) * X 0 ^ 3 * M * (M^2 + 3*P^2)

def signs (i : Fin 6) : ℂ := if i.val = 1 ∨ i.val = 4 then -1 else 1

theorem signs_square : ∀ i, signs i * signs i = 1 := by
  intro i
  unfold signs
  split_ifs <;> norm_num

theorem signChange_F : signChange signs HodgeSubmission.F = HodgeSubmission.F := by
  simp only [HodgeSubmission.F, map_add, map_mul, map_pow, signChange_X]
  apply MvPolynomial.funext
  intro x
  norm_num [signs]
  ring

theorem signChange_Aplus : signChange signs Aplus = Aminus := by
  simp only [Aplus, Aminus, P, M, map_mul, map_add, map_sub, map_pow, map_ofNat,
    signChange_C, signChange_X]
  apply MvPolynomial.funext
  intro x
  norm_num [signs]
  ring

theorem target_decomposition : HodgeSubmission.A = Aplus + Aminus := by
  apply MvPolynomial.funext
  intro x
  norm_num [HodgeSubmission.A, Aplus, Aminus, P, M]
  ring

/-- One certificate for each hidden reflection sector suffices for the exact
protected statement. This is conditional: no sector witness is asserted here. -/
theorem certificate_of_reflection_sectors
    (hp : HasCertificate HodgeSubmission.F Aplus 1)
    (hm : HasCertificate HodgeSubmission.F Aminus 1) :
    HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  rw [HodgeSubmission.q, target_decomposition]
  exact HasCertificate.add_q1 hp hm

/-- The involution changing the signs of X₁ and Y₁ preserves the exact F and
interchanges the two hidden-reflection sectors. Only one sector witness is
therefore needed. The conclusion remains conditional on that witness. -/
theorem certificate_of_one_reflection_sector
    (hp : HasCertificate HodgeSubmission.F Aplus 1) :
    HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q := by
  apply certificate_of_reflection_sectors hp
  obtain ⟨d, D, N, Q, h⟩ := hp
  have hm := Verify.sign_change signs signs_square h
  rw [signChange_F, signChange_Aplus] at hm
  exact ⟨d, signChange signs D, signField signs N, signChange signs Q, hm⟩

end OneReflection

#print axioms Verify.add_q1
#print axioms HasCertificate.add_q1
#print axioms OneReflection.certificate_of_reflection_sectors
#print axioms Verify.sign_change
#print axioms OneReflection.certificate_of_one_reflection_sector

end HodgeComputer.Construction

end -- close the original noncomputable section

end CertificateConstructionSection

/-! ## OneReflectionDivergenceCore -/

section OneReflectionDivergenceCoreSection

set_option maxHeartbeats 12000000
set_option maxRecDepth 6000
noncomputable section

namespace OneReflectionDivergenceCore

/- A polynomial identity in five independent scalar variables.  The names
`dX`, `dP`, and `dK` record the derivations
  X = 6g ∂g + 4c ∂c,
  P = ∂p,
  K = (3r+12t) ∂r + 9t ∂t.
Every displayed jet is an explicit polynomial, not an assumed derivative. -/

def delta (g c : ℂ) : ℂ := 324 * g ^ 2 + 24 * c ^ 3
def h (g c p : ℂ) : ℂ := -c ^ 2 + 18 * g * p + 6 * c * p ^ 2
def f (g c p : ℂ) : ℂ := g + c * p + 2 * p ^ 3
def W (g c p r t : ℂ) : ℂ := r ^ 3 + f g c p * t
def Z (g c p r t : ℂ) : ℂ := r ^ 3 * (r ^ 3 + 2 * f g c p * t)
def D (g c p r t : ℂ) : ℂ :=
  9 * delta g c * Z g c p r t + 4 * h g c p ^ 3 * t ^ 2
def p0 (g c p : ℂ) : ℂ :=
  g * c + 12 * g * p ^ 2 + c ^ 2 * p / 3 + 6 * c * p ^ 3
def p1 (g c p : ℂ) : ℂ := -3 * g * p + c ^ 2 / 3 + c * p ^ 2 + 6 * p ^ 4
def U (g c p r t : ℂ) : ℂ :=
  81 * g * Z g c p r t - 3 * c * h g c p * W g c p r t * t +
    3 * h g c p * p0 g c p * t ^ 2
def V (g c p r t : ℂ) : ℂ :=
  9 * c ^ 2 * Z g c p r t - 3 * c * h g c p * W g c p r t * p * t +
    c * h g c p * p1 g c p * t ^ 2
def B (g c p r t : ℂ) : ℂ := -3 * c * h g c p * W g c p r t * r

def dXh (g c p : ℂ) : ℂ := -8 * c ^ 2 + 108 * g * p + 24 * c * p ^ 2
def dXf (g c p : ℂ) : ℂ := 6 * g + 4 * c * p
def dXW (g c p _r t : ℂ) : ℂ := dXf g c p * t
def dXZ (g c p r t : ℂ) : ℂ := 2 * r ^ 3 * dXf g c p * t
def dXp0 (g c p : ℂ) : ℂ :=
  10 * g * c + 72 * g * p ^ 2 + 8 * c ^ 2 * p / 3 + 24 * c * p ^ 3
def dXD (g c p r t : ℂ) : ℂ :=
  108 * delta g c * Z g c p r t + 9 * delta g c * dXZ g c p r t +
    12 * h g c p ^ 2 * dXh g c p * t ^ 2
def dXU (g c p r t : ℂ) : ℂ :=
  81 * (6 * g * Z g c p r t + g * dXZ g c p r t) -
    3 * (4 * c * h g c p * W g c p r t + c * dXh g c p * W g c p r t +
      c * h g c p * dXW g c p r t) * t +
    3 * (dXh g c p * p0 g c p + h g c p * dXp0 g c p) * t ^ 2

def dPh (g c p : ℂ) : ℂ := 18 * g + 12 * c * p
def dPf (_g c p : ℂ) : ℂ := c + 6 * p ^ 2
def dPW (g c p _r t : ℂ) : ℂ := dPf g c p * t
def dPZ (g c p r t : ℂ) : ℂ := 2 * r ^ 3 * dPf g c p * t
def dPp1 (g c p : ℂ) : ℂ := -3 * g + 2 * c * p + 24 * p ^ 3
def dPD (g c p r t : ℂ) : ℂ :=
  9 * delta g c * dPZ g c p r t + 12 * h g c p ^ 2 * dPh g c p * t ^ 2
def dPV (g c p r t : ℂ) : ℂ :=
  9 * c ^ 2 * dPZ g c p r t -
    3 * c * (dPh g c p * W g c p r t * p + h g c p * dPW g c p r t * p +
      h g c p * W g c p r t) * t +
    c * (dPh g c p * p1 g c p + h g c p * dPp1 g c p) * t ^ 2

def dKr (r t : ℂ) : ℂ := 3 * r + 12 * t
def dKt (t : ℂ) : ℂ := 9 * t
def dKW (g c p r t : ℂ) : ℂ := 3 * r ^ 2 * dKr r t + f g c p * dKt t
def dKZ (g c p r t : ℂ) : ℂ :=
  3 * r ^ 2 * dKr r t * (r ^ 3 + 2 * f g c p * t) +
    r ^ 3 * (3 * r ^ 2 * dKr r t + 2 * f g c p * dKt t)
def dKD (g c p r t : ℂ) : ℂ :=
  9 * delta g c * dKZ g c p r t + 8 * h g c p ^ 3 * t * dKt t
def dKB (g c p r t : ℂ) : ℂ :=
  -3 * c * h g c p * (dKW g c p r t * r + W g c p r t * dKr r t)

theorem divergence_core (g c p r t : ℂ) :
    D g c p r t * (3 * dXU g c p r t + 18 * U g c p r t +
      6 * dPV g c p r t + dKB g c p r t + 6 * B g c p r t) =
    3 * U g c p r t * dXD g c p r t +
      6 * V g c p r t * dPD g c p r t + B g c p r t * dKD g c p r t := by
  simp only [D, U, V, B, dXD, dXU, dPD, dPV, dKD, dKB,
    dXh, dXf, dXW, dXZ, dXp0, dPh, dPf, dPW, dPZ, dPp1, dKW, dKZ, dKr, dKt,
    delta, h, f, W, Z, p0, p1]
  ring

end OneReflectionDivergenceCore

end -- close the original noncomputable section

end OneReflectionDivergenceCoreSection

/-! ## OneReflectionLegality -/

section OneReflectionLegalitySection

/-!
Legality by a univariate fiber for the exact protected one-reflection target.
The method is HodgeComputer.relPrime_of_specialization, already present in the
trusted verifier.  The explicit coordinate retraction follows the approach of
the accepted two-ternary-dense-two-odd-hessian-d48 submission (PDenseP0.lean).
-/

noncomputable section
namespace OneReflectionLegality
open MvPolynomial HodgeComputer

def toUni : Poly →+* Polynomial Coeff :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => if i.val = 0 then Polynomial.C (X 0)
      else if i.val = 1 then Polynomial.C (X 1)
      else if i.val = 2 then Polynomial.C (X 2)
      else if i.val = 3 then Polynomial.C (X 3)
      else if i.val = 4 then Polynomial.C (X 4)
      else Polynomial.X)

def fromUni : Polynomial Coeff →+* Poly :=
  Polynomial.eval₂RingHom
    (MvPolynomial.eval₂Hom MvPolynomial.C (fun i : Fin 5 => X i.castSucc)) (X 5)

@[simp] theorem toUni_C (c : ℂ) : toUni (C c) = Polynomial.C (C c) := by
  simp [toUni]

@[simp] theorem toUni_X0 : toUni (X 0) = Polynomial.C (X 0) := by simp [toUni]
@[simp] theorem toUni_X1 : toUni (X 1) = Polynomial.C (X 1) := by simp [toUni]
@[simp] theorem toUni_X2 : toUni (X 2) = Polynomial.C (X 2) := by simp [toUni]
@[simp] theorem toUni_X3 : toUni (X 3) = Polynomial.C (X 3) := by simp [toUni]
@[simp] theorem toUni_X4 : toUni (X 4) = Polynomial.C (X 4) := by simp [toUni]
@[simp] theorem toUni_X5 : toUni (X 5) = Polynomial.X := by simp [toUni]

theorem retract : fromUni.comp toUni = RingHom.id Poly := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp [toUni, fromUni]
  · intro i; fin_cases i <;> simp [toUni, fromUni]

def rest : Coeff := X 0 ^ 6 + X 0 ^ 3 * X 1 * X 3 * X 4 + X 1 ^ 6 +
  X 1 ^ 3 * X 2 * X 3 * X 4 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6

theorem toUni_F : toUni HodgeSubmission.F = Polynomial.X ^ 6 + Polynomial.C rest := by
  simp [HodgeSubmission.F, rest]
  ring

theorem monic_F : (toUni HodgeSubmission.F).Monic := by
  rw [toUni_F]
  exact Polynomial.monic_X_pow_add_C rest (by decide)

def specialize : Coeff →+* ℂ := MvPolynomial.eval (fun _ => 1)
def fiber : Poly →+* Polynomial ℂ := (Polynomial.mapRingHom specialize).comp toUni

@[simp] theorem fiber_C (c : ℂ) : fiber (C c) = Polynomial.C c := by
  simp [fiber, specialize]

@[simp] theorem fiber_X0 : fiber (X 0) = 1 := by simp [fiber, specialize]
@[simp] theorem fiber_X1 : fiber (X 1) = 1 := by simp [fiber, specialize]
@[simp] theorem fiber_X2 : fiber (X 2) = 1 := by simp [fiber, specialize]
@[simp] theorem fiber_X3 : fiber (X 3) = 1 := by simp [fiber, specialize]
@[simp] theorem fiber_X4 : fiber (X 4) = 1 := by simp [fiber, specialize]
@[simp] theorem fiber_X5 : fiber (X 5) = Polynomial.X := by simp [fiber, specialize]

theorem fiber_F : fiber HodgeSubmission.F = Polynomial.X ^ 6 + 7 := by
  simp [HodgeSubmission.F]
  ring

theorem legal_of_fiber (D : Poly)
    (h : IsRelPrime (Polynomial.X ^ 6 + 7 : Polynomial ℂ) (fiber D)) :
    IsRelPrime HodgeSubmission.F D := by
  apply HodgeComputer.relPrime_of_retract toUni fromUni retract
  apply HodgeComputer.relPrime_of_specialization specialize
  · rw [monic_F.leadingCoeff]
    exact isUnit_one
  · change IsRelPrime (fiber HodgeSubmission.F) (fiber D)
    simpa only [fiber_F] using h

theorem ne_zero_of_fiber (D : Poly) (h : fiber D ≠ 0) : D ≠ 0 := by
  intro hz
  exact h (by rw [hz, map_zero])

end OneReflectionLegality

#print axioms OneReflectionLegality.legal_of_fiber

end -- close the original noncomputable section

end OneReflectionLegalitySection

/-! ## OneReflectionPhysical -/

section OneReflectionPhysicalSection

/-!
An explicit degree-30 denominator for the positive hidden-reflection sector.
All definitions are polynomials over the permitted coefficient field ℂ.
The only algebraic constant is the positive real square root of 3, cast to ℂ.
The rational-coordinate and Sylvester trace derivation is recorded separately.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
noncomputable section
namespace OneReflectionPhysical
open MvPolynomial HodgeComputer HodgeTestbed

def tau : ℂ := (Real.sqrt 3 : ℝ)
theorem tau_sq : tau ^ 2 = 3 := by
  unfold tau
  norm_cast
  exact Real.sq_sqrt (by norm_num)

def P : Poly := X 3 * X 4
def s : Poly := X 3 ^ 3 - X 4 ^ 3
def S : Poly := X 3 ^ 3 + X 4 ^ 3
def T : Poly := X 5 ^ 3
def G : Poly := X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6
def c : Poly := X 0 ^ 3 * X 1 + X 1 ^ 3 * X 2
def delta : Poly := 324 * G ^ 2 + 24 * c ^ 3
def h : Poly := -c ^ 2 + 18 * G * P + 6 * c * P ^ 2
def f : Poly := G + c * P + 2 * P ^ 3
def R : Poly := T + C (tau / 3) * s
def W : Poly := R ^ 3 + f * T
def Z : Poly := R ^ 3 * (R ^ 3 + 2 * f * T)
def D : Poly := 9 * delta * Z + 4 * h ^ 3 * T ^ 2
def p0 : Poly := G * c + 12 * G * P ^ 2 + C (1/3 : ℂ) * c ^ 2 * P + 6 * c * P ^ 3
def p1 : Poly := -3 * G * P + C (1/3 : ℂ) * c ^ 2 + c * P ^ 2 + 6 * P ^ 4
def U : Poly := 81 * G * Z - 3 * c * h * W * T + 3 * h * p0 * T ^ 2
def V : Poly := 9 * c ^ 2 * Z - 3 * c * h * W * P * T + c * h * p1 * T ^ 2
def B : Poly := -3 * c * h * W * R
def N0 : Poly := X 0 ^ 3 * (3 * S * X 0 * U)
def N1 : Poly := X 0 ^ 3 * (3 * S * X 1 * U)
def N2 : Poly := X 0 ^ 3 * (3 * S * X 2 * U)
def N3 : Poly := X 0 ^ 3 * (6 * X 4 ^ 2 * V + X 3 * (s + C (2*tau) * T) * B)
def N4 : Poly := X 0 ^ 3 * (6 * X 3 ^ 2 * V - X 4 * (s + C (2*tau) * T) * B)
def N5 : Poly := X 0 ^ 3 * (3 * S * X 5 * B)
def N : Fin 6 → Poly := ![N0,N1,N2,N3,N4,N5]
def Aplus : Poly := C (1/2 : ℂ) * X 0 ^ 3 * S

theorem F_decomposition : HodgeSubmission.F = f + s ^ 2 + X 5 ^ 6 := by
  unfold HodgeSubmission.F f G c P s
  ring

end OneReflectionPhysical

end -- close the original noncomputable section

end OneReflectionPhysicalSection

/-! ## OneReflectionDenominator -/

section OneReflectionDenominatorSection

/-!
The all-ones specialization of the other five variables is a legal fiber for
the degree-30 denominator. The explicit constant remainder proves coprimality
over ℂ, while a nonzero value proves that the denominator is not zero.
-/

noncomputable section
namespace OneReflectionPhysical
open MvPolynomial HodgeComputer OneReflectionLegality

theorem fiber_D : fiber D =
    27972*Polynomial.X^18 + 391608*Polynomial.X^12 + 953312*Polynomial.X^6 := by
  simp [D, delta, Z, R, f, h, G, c, P, s, T, map_ofNat]
  ring

theorem fiber_D_remainder :
    fiber D = (Polynomial.X^6+7)*
      (27972*Polynomial.X^12+195804*Polynomial.X^6-417316)+2921212 := by
  rw [fiber_D]
  ring

theorem fiber_D_coprime :
    IsCoprime (Polynomial.X^6+7 : Polynomial ℂ) (fiber D) := by
  refine ⟨-Polynomial.C (1/2921212 : ℂ)*
    (27972*Polynomial.X^12+195804*Polynomial.X^6-417316),
    Polynomial.C (1/2921212 : ℂ), ?_⟩
  rw [fiber_D_remainder]
  apply Polynomial.funext
  intro x
  norm_num
  ring

theorem D_legal : IsRelPrime HodgeSubmission.F D :=
  legal_of_fiber D fiber_D_coprime.isRelPrime

theorem D_ne_zero : D ≠ 0 := by
  apply ne_zero_of_fiber
  intro hz
  have he := congrArg (Polynomial.eval (1 : ℂ)) hz
  rw [fiber_D] at he
  norm_num at he

end OneReflectionPhysical

#print axioms OneReflectionPhysical.D_legal
#print axioms OneReflectionPhysical.D_ne_zero

end -- close the original noncomputable section

end OneReflectionDenominatorSection

/-! ## OneReflectionDifferentiation -/

section OneReflectionDifferentiationSection

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
noncomputable section
namespace OneReflectionPhysical
open MvPolynomial HodgeComputer HodgeTestbed

def EX : Fin 6 → Poly := ![X 0, X 1, X 2, 0, 0, 0]
def JY : Fin 6 → Poly := ![0, 0, 0, X 4 ^ 2, X 3 ^ 2, 0]
def KY : Fin 6 → Poly :=
  ![0, 0, 0, X 3 * (s + C (2*tau) * T),
    -X 4 * (s + C (2*tau) * T), 3*S*X 5]

theorem dir_add (a b : Poly) (v : Fin 6 → Poly) :
    directional (a+b) v = directional a v + directional b v := by
  simp [directional, add_mul, Finset.sum_add_distrib]

theorem dir_sub (a b : Poly) (v : Fin 6 → Poly) :
    directional (a-b) v = directional a v - directional b v := by
  simp [directional, sub_mul, Finset.sum_sub_distrib]

theorem dir_neg (a : Poly) (v : Fin 6 → Poly) :
    directional (-a) v = -directional a v := by
  simp [directional]

theorem dir_C (a : ℂ) (v : Fin 6 → Poly) : directional (C a) v = 0 := by
  simp [directional]

theorem dir_nat (n : ℕ) (v : Fin 6 → Poly) : directional (n : Poly) v = 0 := by
  simp [directional]

theorem dir_mul (a b : Poly) (v : Fin 6 → Poly) :
    directional (a*b) v = b*directional a v + a*directional b v :=
  directional_product b a v

theorem dir_pow (a : Poly) (n : ℕ) (v : Fin 6 → Poly) :
    directional (a^n) v = (n : Poly)*a^(n-1)*directional a v := by
  simp only [directional, pderiv_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem EX_G : directional G EX = 6*G := by
  simp only [directional, EX, G, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]
  ring

theorem EX_c : directional c EX = 4*c := by
  simp only [directional, EX, c, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, pderiv_mul, pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]
  ring

theorem EX_P : directional P EX = 0 := by
  simp only [directional, EX, P, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    pderiv_mul]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

theorem EX_R : directional R EX = 0 := by
  simp only [directional, EX, R, T, s, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, map_sub, pderiv_mul, pderiv_pow, pderiv_C]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

theorem EX_T : directional T EX = 0 := by
  simp only [directional, EX, T, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

theorem JY_G : directional G JY = 0 := by
  simp only [directional, JY, G, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

theorem JY_c : directional c JY = 0 := by
  simp only [directional, JY, c, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, pderiv_mul, pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

theorem JY_P : directional P JY = S := by
  simp only [directional, JY, P, S, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    pderiv_mul]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]
  ring

theorem JY_R : directional R JY = 0 := by
  simp only [directional, JY, R, T, s, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, map_sub, pderiv_mul, pderiv_pow, pderiv_C]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]
  ring

theorem JY_T : directional T JY = 0 := by
  simp only [directional, JY, T, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

theorem KY_G : directional G KY = 0 := by
  simp only [directional, KY, G, S, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

theorem KY_c : directional c KY = 0 := by
  simp only [directional, KY, c, S, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, pderiv_mul, pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

theorem KY_P : directional P KY = 0 := by
  simp only [directional, KY, P, S, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    pderiv_mul]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]
  ring

theorem KY_R : directional R KY = S*(3*R+12*T) := by
  simp only [directional, KY, R, T, s, S, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    map_add, map_sub, pderiv_mul, pderiv_pow, pderiv_C]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]
  apply MvPolynomial.funext
  intro x
  norm_num
  ring_nf
  rw [tau_sq]
  ring

theorem KY_T : directional T KY = S*(9*T) := by
  simp only [directional, KY, T, S, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]
  ring

theorem pd3 (i : Fin 6) : pderiv i (3 : Poly) = 0 := by
  exact (pderiv i).map_natCast 3

theorem pd6 (i : Fin 6) : pderiv i (6 : Poly) = 0 := by
  exact (pderiv i).map_natCast 6

theorem normal_derivative_grouped (a : Poly) :
    directional a N = X 0 ^ 3 *
      (3*S*U*directional a EX + 6*V*directional a JY + B*directional a KY) := by
  simp only [directional, N, EX, JY, KY, N0, N1, N2, N3, N4, N5,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  ring

theorem divergence_grouped :
    divergence N = X 0 ^ 3 *
      (3*S*(directional U EX+6*U) + 6*directional V JY +
        directional B KY + 6*S*B) := by
  simp only [divergence, directional, N, EX, JY, KY, N0, N1, N2, N3, N4, N5,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, map_add, map_sub,
    pderiv_mul, pderiv_pow, pderiv_C]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]
  simp only [S, s, T, map_add, map_sub, pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]
  simp only [pd3, pd6]
  ring

end OneReflectionPhysical

end -- close the original noncomputable section

end OneReflectionDifferentiationSection

/-! ## OneReflectionFirstIdentity -/

section OneReflectionFirstIdentitySection

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
noncomputable section

namespace OneReflectionPhysical
open MvPolynomial HodgeComputer HodgeTestbed

/- The large physical identity factors through a small scalar polynomial
identity in G,c,P,R,T.  No coordinate or denominator is inverted here. -/
theorem first_scalar_identity :
    12 * ((3 * G + 2 * c * P) * U + (c + 6 * P ^ 2) * V +
      3 * R ^ 2 * B) = D := by
  unfold U V B D delta Z W h p0 p1 f
  apply MvPolynomial.funext
  intro x
  norm_num
  ring

theorem three_R_sq :
    3 * R ^ 2 = s ^ 2 + C (2 * tau) * s * T + 3 * T ^ 2 := by
  unfold R
  apply MvPolynomial.funext
  intro x
  norm_num
  ring_nf
  rw [tau_sq]
  ring

theorem directional_grouped :
    directional HodgeSubmission.F N =
      6 * X 0 ^ 3 * S * ((3 * G + 2 * c * P) * U +
        (c + 6 * P ^ 2) * V +
        (s ^ 2 + C (2 * tau) * s * T + 3 * T ^ 2) * B) := by
  simp only [directional, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change pderiv (0 : Fin 6) HodgeSubmission.F * N0 +
    (pderiv (1 : Fin 6) HodgeSubmission.F * N1 +
    (pderiv (2 : Fin 6) HodgeSubmission.F * N2 +
    (pderiv (3 : Fin 6) HodgeSubmission.F * N3 +
    (pderiv (4 : Fin 6) HodgeSubmission.F * N4 +
      pderiv (5 : Fin 6) HodgeSubmission.F * N5)))) = _
  simp only [HodgeSubmission.F, map_add, pderiv_mul, pderiv_pow]
  norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]
  unfold N0 N1 N2 N3 N4 N5 S G c P s T
  apply MvPolynomial.funext
  intro x
  norm_num
  ring

theorem first_identity :
    directional HodgeSubmission.F N = Aplus * D := by
  rw [directional_grouped, ← three_R_sq]
  have hscalar := first_scalar_identity
  unfold Aplus
  apply MvPolynomial.funext
  intro x
  have hx := congrArg (MvPolynomial.eval x) hscalar
  norm_num at hx ⊢
  linear_combination (x 0)^3 * MvPolynomial.eval x S / 2 * hx

end OneReflectionPhysical

end -- close the original noncomputable section

end OneReflectionFirstIdentitySection

/-! ## OneReflectionHomogeneity -/

section OneReflectionHomogeneitySection

/-!
Homogeneous degrees of the factored polynomial witness. This proof follows the
products and sums in the source definitions and does not expand the witness.
-/

noncomputable section
namespace OneReflectionPhysical
open MvPolynomial HodgeComputer

theorem P_homogeneous : P.IsHomogeneous 2 := by
  exact (isHomogeneous_X ℂ (3 : Fin 6)).mul (isHomogeneous_X ℂ (4 : Fin 6))

theorem s_homogeneous : s.IsHomogeneous 3 := by
  exact (isHomogeneous_X_pow (3 : Fin 6) 3).sub (isHomogeneous_X_pow (4 : Fin 6) 3)

theorem S_homogeneous : S.IsHomogeneous 3 := by
  exact (isHomogeneous_X_pow (3 : Fin 6) 3).add (isHomogeneous_X_pow (4 : Fin 6) 3)

theorem T_homogeneous : T.IsHomogeneous 3 := isHomogeneous_X_pow _ _

theorem G_homogeneous : G.IsHomogeneous 6 := by
  exact ((isHomogeneous_X_pow (0 : Fin 6) 6).add
    (isHomogeneous_X_pow (1 : Fin 6) 6)).add (isHomogeneous_X_pow (2 : Fin 6) 6)

theorem c_homogeneous : c.IsHomogeneous 4 := by
  exact ((isHomogeneous_X_pow (0 : Fin 6) 3).mul (isHomogeneous_X ℂ (1 : Fin 6))).add
    ((isHomogeneous_X_pow (1 : Fin 6) 3).mul (isHomogeneous_X ℂ (2 : Fin 6)))

theorem delta_homogeneous : delta.IsHomogeneous 12 := by
  exact ((G_homogeneous.pow 2).C_mul 324).add ((c_homogeneous.pow 3).C_mul 24)

theorem h_homogeneous : h.IsHomogeneous 8 := by
  exact (((c_homogeneous.pow 2).neg).add
    ((G_homogeneous.C_mul 18).mul P_homogeneous)).add
    ((c_homogeneous.C_mul 6).mul (P_homogeneous.pow 2))

theorem f_homogeneous : f.IsHomogeneous 6 := by
  exact (G_homogeneous.add (c_homogeneous.mul P_homogeneous)).add
    ((P_homogeneous.pow 3).C_mul 2)

theorem R_homogeneous : R.IsHomogeneous 3 := by
  exact T_homogeneous.add (s_homogeneous.C_mul (tau/3))

theorem W_homogeneous : W.IsHomogeneous 9 := by
  exact (R_homogeneous.pow 3).add (f_homogeneous.mul T_homogeneous)

theorem Z_homogeneous : Z.IsHomogeneous 18 := by
  exact (R_homogeneous.pow 3).mul
    ((R_homogeneous.pow 3).add ((f_homogeneous.C_mul 2).mul T_homogeneous))

theorem D_homogeneous : D.IsHomogeneous 30 := by
  exact ((delta_homogeneous.C_mul 9).mul Z_homogeneous).add
    (((h_homogeneous.pow 3).C_mul 4).mul (T_homogeneous.pow 2))

theorem p0_homogeneous : p0.IsHomogeneous 10 := by
  exact (((G_homogeneous.mul c_homogeneous).add
    ((G_homogeneous.C_mul 12).mul (P_homogeneous.pow 2))).add
    (((c_homogeneous.pow 2).C_mul (1/3)).mul P_homogeneous)).add
    ((c_homogeneous.C_mul 6).mul (P_homogeneous.pow 3))

theorem p1_homogeneous : p1.IsHomogeneous 8 := by
  simpa only [p1, map_neg, map_ofNat] using ((((G_homogeneous.C_mul (-3)).mul P_homogeneous).add
    ((c_homogeneous.pow 2).C_mul (1/3))).add
    (c_homogeneous.mul (P_homogeneous.pow 2))).add
    ((P_homogeneous.pow 4).C_mul 6)

theorem U_homogeneous : U.IsHomogeneous 24 := by
  exact (((G_homogeneous.C_mul 81).mul Z_homogeneous).sub
    ((((c_homogeneous.C_mul 3).mul h_homogeneous).mul W_homogeneous).mul
      T_homogeneous)).add
    (((h_homogeneous.C_mul 3).mul p0_homogeneous).mul (T_homogeneous.pow 2))

theorem V_homogeneous : V.IsHomogeneous 26 := by
  exact ((((c_homogeneous.pow 2).C_mul 9).mul Z_homogeneous).sub
    (((((c_homogeneous.C_mul 3).mul h_homogeneous).mul W_homogeneous).mul
      P_homogeneous).mul T_homogeneous)).add
    (((c_homogeneous.mul h_homogeneous).mul p1_homogeneous).mul (T_homogeneous.pow 2))

theorem B_homogeneous : B.IsHomogeneous 24 := by
  simpa only [B, map_neg, map_ofNat] using (((c_homogeneous.C_mul (-3)).mul h_homogeneous).mul W_homogeneous).mul
    R_homogeneous

theorem N0_homogeneous : N0.IsHomogeneous 31 := by
  exact (isHomogeneous_X_pow (0 : Fin 6) 3).mul
    (((S_homogeneous.C_mul 3).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul U_homogeneous)

theorem N1_homogeneous : N1.IsHomogeneous 31 := by
  exact (isHomogeneous_X_pow (0 : Fin 6) 3).mul
    (((S_homogeneous.C_mul 3).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul U_homogeneous)

theorem N2_homogeneous : N2.IsHomogeneous 31 := by
  exact (isHomogeneous_X_pow (0 : Fin 6) 3).mul
    (((S_homogeneous.C_mul 3).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul U_homogeneous)

theorem N3_homogeneous : N3.IsHomogeneous 31 := by
  exact (isHomogeneous_X_pow (0 : Fin 6) 3).mul
    ((((isHomogeneous_X_pow (4 : Fin 6) 2).C_mul 6).mul V_homogeneous).add
      (((isHomogeneous_X ℂ (3 : Fin 6)).mul
        (s_homogeneous.add (T_homogeneous.C_mul (2*tau)))).mul B_homogeneous))

theorem N4_homogeneous : N4.IsHomogeneous 31 := by
  exact (isHomogeneous_X_pow (0 : Fin 6) 3).mul
    ((((isHomogeneous_X_pow (3 : Fin 6) 2).C_mul 6).mul V_homogeneous).sub
      (((isHomogeneous_X ℂ (4 : Fin 6)).mul
        (s_homogeneous.add (T_homogeneous.C_mul (2*tau)))).mul B_homogeneous))

theorem N5_homogeneous : N5.IsHomogeneous 31 := by
  exact (isHomogeneous_X_pow (0 : Fin 6) 3).mul
    (((S_homogeneous.C_mul 3).mul (isHomogeneous_X ℂ (5 : Fin 6))).mul B_homogeneous)

theorem N_homogeneous : ∀ i, (N i).IsHomogeneous 31 := by
  intro i
  fin_cases i
  · exact N0_homogeneous
  · exact N1_homogeneous
  · exact N2_homogeneous
  · exact N3_homogeneous
  · exact N4_homogeneous
  · exact N5_homogeneous

end OneReflectionPhysical

#print axioms OneReflectionPhysical.D_homogeneous
#print axioms OneReflectionPhysical.N_homogeneous

end -- close the original noncomputable section

end OneReflectionHomogeneitySection

/-! ## OneReflectionCertificate -/

section OneReflectionCertificateSection

/-!
Assembly of the exact protected target from the positive reflection sector.
The only input of the assembly theorem is the second polynomial identity;
the separate identity module supplies that input in the final solution.
-/

noncomputable section
namespace OneReflectionPhysical
open MvPolynomial HodgeComputer HodgeTestbed HodgeComputer.Construction

theorem sector_verify (second_identity : divergenceNumerator D N = 0) :
    Verify HodgeSubmission.F Aplus 1 30 D N 0 where
  denominator_ne_zero := D_ne_zero
  denominator_homogeneous := D_homogeneous
  numerator_homogeneous := N_homogeneous
  denominator_legal := D_legal
  identity := by
    apply normalized_identity
    · simpa only [Nat.cast_one, one_mul] using first_identity
    · rw [second_identity, mul_zero]

theorem Aplus_eq_hidden_sector :
    Aplus = HodgeComputer.Construction.OneReflection.Aplus := by
  unfold Aplus S HodgeComputer.Construction.OneReflection.Aplus
    HodgeComputer.Construction.OneReflection.P HodgeComputer.Construction.OneReflection.M
  apply MvPolynomial.funext
  intro x
  norm_num
  ring

def sigma : Poly →+* Poly := signChange HodgeComputer.Construction.OneReflection.signs
def reflectedN : Fin 6 → Poly := signField HodgeComputer.Construction.OneReflection.signs N

theorem target_sum : Aplus + sigma Aplus = HodgeSubmission.A := by
  rw [Aplus_eq_hidden_sector]
  change HodgeComputer.Construction.OneReflection.Aplus +
    signChange HodgeComputer.Construction.OneReflection.signs
      HodgeComputer.Construction.OneReflection.Aplus = HodgeSubmission.A
  rw [HodgeComputer.Construction.OneReflection.signChange_Aplus]
  exact HodgeComputer.Construction.OneReflection.target_decomposition.symm

def fullD : Poly := D * sigma D
def fullN : Fin 6 → Poly := fun i => sigma D * N i + D * reflectedN i

theorem full_verify (second_identity : divergenceNumerator D N = 0) :
    Verify HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q 60 fullD fullN 0 := by
  have hp := sector_verify second_identity
  have hm := HodgeComputer.Construction.Verify.sign_change
    HodgeComputer.Construction.OneReflection.signs
    HodgeComputer.Construction.OneReflection.signs_square hp
  rw [HodgeComputer.Construction.OneReflection.signChange_F] at hm
  have hsum := HodgeComputer.Construction.Verify.add_q1 hp hm
  change Verify HodgeSubmission.F (Aplus + sigma Aplus) 1 (30+30)
    (D*sigma D) (fun i => sigma D*N i+D*reflectedN i)
    ((sigma D)^2*0+D^2*sigma 0) at hsum
  change Verify HodgeSubmission.F HodgeSubmission.A 1 (30+30)
    (D*sigma D) (fun i => sigma D*N i+D*reflectedN i) 0
  simpa only [target_sum, map_zero, mul_zero, add_zero] using hsum

theorem certificate_from_second_identity (second_identity : divergenceNumerator D N = 0) :
    HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q :=
  ⟨60, fullD, fullN, 0, full_verify second_identity⟩

end OneReflectionPhysical

#print axioms OneReflectionPhysical.full_verify
#print axioms OneReflectionPhysical.certificate_from_second_identity

end -- close the original noncomputable section

end OneReflectionCertificateSection

/-! ## OneReflectionSecondIdentity -/

section OneReflectionSecondIdentitySection

set_option maxHeartbeats 8000000
set_option maxRecDepth 6000
noncomputable section
namespace OneReflectionPhysical
open MvPolynomial HodgeComputer HodgeTestbed

/- The only substantial scalar polynomial identity is proved in
OneReflectionDivergenceCore.  Here explicit differentiation connects its six
jets with the physical vector fields, including the common X0^3 factor. -/

private theorem dn2 (v : Fin 6 → Poly) : directional (2 : Poly) v = 0 :=
  dir_nat 2 v

private theorem dn3 (v : Fin 6 → Poly) : directional (3 : Poly) v = 0 :=
  dir_nat 3 v

private theorem dn4 (v : Fin 6 → Poly) : directional (4 : Poly) v = 0 :=
  dir_nat 4 v

private theorem dn6 (v : Fin 6 → Poly) : directional (6 : Poly) v = 0 :=
  dir_nat 6 v

private theorem dn9 (v : Fin 6 → Poly) : directional (9 : Poly) v = 0 :=
  dir_nat 9 v

private theorem dn12 (v : Fin 6 → Poly) : directional (12 : Poly) v = 0 :=
  dir_nat 12 v

private theorem dn18 (v : Fin 6 → Poly) : directional (18 : Poly) v = 0 :=
  dir_nat 18 v

private theorem dn24 (v : Fin 6 → Poly) : directional (24 : Poly) v = 0 :=
  dir_nat 24 v

private theorem dn81 (v : Fin 6 → Poly) : directional (81 : Poly) v = 0 :=
  dir_nat 81 v

private theorem dn324 (v : Fin 6 → Poly) : directional (324 : Poly) v = 0 :=
  dir_nat 324 v

theorem eval_D (x : Fin 6 → ℂ) :
    eval x D = OneReflectionDivergenceCore.D (eval x G) (eval x c) (eval x P) (eval x R) (eval x T) := by
  simp only [D, delta, h, f, Z]
  simp only [OneReflectionDivergenceCore.delta, OneReflectionDivergenceCore.h,
    OneReflectionDivergenceCore.f, OneReflectionDivergenceCore.Z, OneReflectionDivergenceCore.D]
  norm_num

theorem eval_U (x : Fin 6 → ℂ) :
    eval x U = OneReflectionDivergenceCore.U (eval x G) (eval x c) (eval x P) (eval x R) (eval x T) := by
  simp only [U, h, f, W, Z, p0]
  simp only [OneReflectionDivergenceCore.h, OneReflectionDivergenceCore.f,
    OneReflectionDivergenceCore.W, OneReflectionDivergenceCore.Z, OneReflectionDivergenceCore.p0,
    OneReflectionDivergenceCore.U]
  norm_num
  ring
  simp

theorem eval_V (x : Fin 6 → ℂ) :
    eval x V = OneReflectionDivergenceCore.V (eval x G) (eval x c) (eval x P) (eval x R) (eval x T) := by
  simp only [V, h, f, W, Z, p1]
  simp only [OneReflectionDivergenceCore.h, OneReflectionDivergenceCore.f,
    OneReflectionDivergenceCore.W, OneReflectionDivergenceCore.Z, OneReflectionDivergenceCore.p1,
    OneReflectionDivergenceCore.V]
  norm_num
  ring
  simp

theorem eval_B (x : Fin 6 → ℂ) :
    eval x B = OneReflectionDivergenceCore.B (eval x G) (eval x c) (eval x P) (eval x R) (eval x T) := by
  simp only [B, h, f, W]
  simp only [OneReflectionDivergenceCore.h, OneReflectionDivergenceCore.f,
    OneReflectionDivergenceCore.W, OneReflectionDivergenceCore.B]
  norm_num

theorem EX_D_eval (x : Fin 6 → ℂ) :
    eval x (directional D EX) = OneReflectionDivergenceCore.dXD (eval x G) (eval x c) (eval x P) (eval x R) (eval x T) := by
  simp only [D, delta, h, f, Z, dir_add, dir_neg, dir_mul, dir_pow, dn2, dn4, dn6, dn9, dn18, dn24,
    dn324, EX_G, EX_c, EX_P, EX_R, EX_T]
  simp only [OneReflectionDivergenceCore.delta, OneReflectionDivergenceCore.h,
    OneReflectionDivergenceCore.f, OneReflectionDivergenceCore.Z, OneReflectionDivergenceCore.dXh,
    OneReflectionDivergenceCore.dXf, OneReflectionDivergenceCore.dXZ,
    OneReflectionDivergenceCore.dXD]
  norm_num
  ring

theorem EX_U_eval (x : Fin 6 → ℂ) :
    eval x (directional U EX) = OneReflectionDivergenceCore.dXU (eval x G) (eval x c) (eval x P) (eval x R) (eval x T) := by
  simp only [U, h, f, W, Z, p0, dir_add, dir_sub, dir_neg, dir_mul, dir_pow, dir_C, dn2, dn3, dn6,
    dn12, dn18, dn81, EX_G, EX_c, EX_P, EX_R, EX_T]
  simp only [OneReflectionDivergenceCore.h, OneReflectionDivergenceCore.f,
    OneReflectionDivergenceCore.W, OneReflectionDivergenceCore.Z, OneReflectionDivergenceCore.p0,
    OneReflectionDivergenceCore.dXh, OneReflectionDivergenceCore.dXf,
    OneReflectionDivergenceCore.dXW, OneReflectionDivergenceCore.dXZ,
    OneReflectionDivergenceCore.dXp0, OneReflectionDivergenceCore.dXU]
  norm_num
  ring

theorem JY_D_eval (x : Fin 6 → ℂ) :
    eval x (directional D JY) = eval x S * OneReflectionDivergenceCore.dPD (eval x G) (eval x c) (eval x P) (eval x R) (eval x T) := by
  simp only [D, delta, h, f, Z, dir_add, dir_neg, dir_mul, dir_pow, dn2, dn4, dn6, dn9, dn18, dn24,
    dn324, JY_G, JY_c, JY_P, JY_R, JY_T]
  simp only [OneReflectionDivergenceCore.delta, OneReflectionDivergenceCore.h,
    OneReflectionDivergenceCore.dPh, OneReflectionDivergenceCore.dPf,
    OneReflectionDivergenceCore.dPZ, OneReflectionDivergenceCore.dPD]
  norm_num
  ring

theorem JY_V_eval (x : Fin 6 → ℂ) :
    eval x (directional V JY) = eval x S * OneReflectionDivergenceCore.dPV (eval x G) (eval x c) (eval x P) (eval x R) (eval x T) := by
  simp only [V, h, f, W, Z, p1, dir_add, dir_sub, dir_neg, dir_mul, dir_pow, dir_C, dn2, dn3, dn6,
    dn9, dn18, JY_G, JY_c, JY_P, JY_R, JY_T]
  simp only [OneReflectionDivergenceCore.h, OneReflectionDivergenceCore.f,
    OneReflectionDivergenceCore.W, OneReflectionDivergenceCore.p1, OneReflectionDivergenceCore.dPh,
    OneReflectionDivergenceCore.dPf, OneReflectionDivergenceCore.dPW,
    OneReflectionDivergenceCore.dPZ, OneReflectionDivergenceCore.dPp1,
    OneReflectionDivergenceCore.dPV]
  norm_num
  ring

theorem KY_D_eval (x : Fin 6 → ℂ) :
    eval x (directional D KY) = eval x S * OneReflectionDivergenceCore.dKD (eval x G) (eval x c) (eval x P) (eval x R) (eval x T) := by
  simp only [D, delta, h, f, Z, dir_add, dir_neg, dir_mul, dir_pow, dn2, dn4, dn6, dn9, dn18, dn24,
    dn324, KY_G, KY_c, KY_P, KY_R, KY_T]
  simp only [OneReflectionDivergenceCore.delta, OneReflectionDivergenceCore.h,
    OneReflectionDivergenceCore.f, OneReflectionDivergenceCore.dKr, OneReflectionDivergenceCore.dKt,
    OneReflectionDivergenceCore.dKZ, OneReflectionDivergenceCore.dKD]
  norm_num
  ring

theorem KY_B_eval (x : Fin 6 → ℂ) :
    eval x (directional B KY) = eval x S * OneReflectionDivergenceCore.dKB (eval x G) (eval x c) (eval x P) (eval x R) (eval x T) := by
  simp only [B, h, f, W, dir_add, dir_neg, dir_mul, dir_pow, dn2, dn3, dn6, dn18, KY_G, KY_c, KY_P,
    KY_R, KY_T]
  simp only [OneReflectionDivergenceCore.h, OneReflectionDivergenceCore.f,
    OneReflectionDivergenceCore.W, OneReflectionDivergenceCore.dKr, OneReflectionDivergenceCore.dKt,
    OneReflectionDivergenceCore.dKW, OneReflectionDivergenceCore.dKB]
  norm_num
  ring

theorem second_identity : divergenceNumerator D N = 0 := by
  unfold divergenceNumerator
  rw [divergence_grouped, normal_derivative_grouped]
  apply MvPolynomial.funext
  intro x
  have hc := OneReflectionDivergenceCore.divergence_core
    (eval x G) (eval x c) (eval x P) (eval x R) (eval x T)
  norm_num
  rw [EX_D_eval, EX_U_eval, JY_D_eval, JY_V_eval, KY_D_eval, KY_B_eval]
  rw [eval_D, eval_U, eval_V, eval_B]
  linear_combination (x 0)^3 * eval x S * hc

end OneReflectionPhysical
#print axioms OneReflectionPhysical.second_identity

end -- close the original noncomputable section

end OneReflectionSecondIdentitySection

/-! ## Final certificate -/

section FinalCertificateSection

/-! A strict degree-60 certificate for the exact protected one-reflection target. -/

theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.A HodgeSubmission.q :=
  OneReflectionPhysical.certificate_from_second_identity
    OneReflectionPhysical.second_identity

#print axioms Submission.certificate

end FinalCertificateSection
