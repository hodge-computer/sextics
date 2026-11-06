import HodgeComputer.CertificateOperations
import Mathlib.Data.Fin.Tuple.NatAntidiagonal

/-!
# Fermat certificates for every homogeneous odd source

Benjamin E. Diamond's subset Euler construction for the sign-flip involution:
both pole parameters `q = 1, 2` and every homogeneous source of odd Y-degree.
The finite subset lemma is checked by Lean's kernel; monomial certificates are
combined using the certificate addition formula (from fqlx's construction).
Formalization prepared with OpenAI Codex assistance.

Mathematical context: Diamond, arXiv:2603.29157, and Chapter 2 of the project book.
-/

set_option autoImplicit false
noncomputable section
namespace HodgeComputer.Fermat
open MvPolynomial
open scoped BigOperators

abbrev n : ℕ := 5
abbrev d : ℕ := 6
def F : HodgeComputer.AmbientPoly n := ∑ i : Fin 6, X i ^ 6

def OddSource (A : HodgeComputer.AmbientPoly n) : Prop :=
  ∀ ⦃m : Fin 6 →₀ ℕ⦄, coeff m A ≠ 0 → Odd (m 3 + m 4 + m 5)

end HodgeComputer.Fermat

namespace HodgeComputer.Fermat
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators

def EulerCondition (a : Fin 6 → ℕ) : Prop :=
  a 3 + a 4 + a 5 ≡ 1 [MOD 2] →
  ∃ I ∈ (Finset.univ : Finset (Fin 6)).powerset, ∑ i ∈ I, (a i + 1) = 6

theorem euler_q1 : ∀ a ∈ Finset.Nat.antidiagonalTuple 6 6, EulerCondition a := by unfold EulerCondition; decide +kernel
theorem euler_q2 : ∀ a ∈ Finset.Nat.antidiagonalTuple 6 12, EulerCondition a := by unfold EulerCondition; decide +kernel

theorem subset_euler (a : Fin 6 → ℕ) (q : ℕ) (hq : q = 1 ∨ q = 2)
    (ha : ∑ i, a i = 6*q) (ho : Odd (a 3 + a 4 + a 5)) :
    ∃ I : Finset (Fin 6), ∑ i ∈ I, (a i + 1) = 6 := by
  have hodd : a 3 + a 4 + a 5 ≡ 1 [MOD 2] := by
    obtain ⟨k,hk⟩ := ho
    unfold Nat.ModEq
    omega
  have hw : EulerCondition a := by
    rcases hq with rfl | rfl
    · exact euler_q1 a (Finset.Nat.mem_antidiagonalTuple.mpr (by simpa using ha))
    · exact euler_q2 a (Finset.Nat.mem_antidiagonalTuple.mpr (by simpa using ha))
  obtain ⟨I,_,hI⟩ := hw hodd
  exact ⟨I,hI⟩

end HodgeComputer.Fermat


set_option maxHeartbeats 1000000
noncomputable section
namespace HodgeComputer.Fermat
open MvPolynomial HodgeTestbed
open scoped BigOperators

abbrev R := AmbientPoly 5

def partialF (I : Finset (Fin 6)) : R := ∑ i ∈ I, X i ^ 6

lemma partialF_homogeneous (I : Finset (Fin 6)) : (partialF I).IsHomogeneous 6 := by
  apply IsHomogeneous.sum
  intro i hi
  simpa using (isHomogeneous_X ℂ i).pow 6

lemma partialF_ne_zero (I : Finset (Fin 6)) (hI : I.Nonempty) : partialF I ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin 6 => (1 : ℂ))) h
  simp [partialF] at he
  exact hI.ne_empty he

lemma F_ne_zero : F ≠ 0 := by
  exact partialF_ne_zero Finset.univ ⟨0, Finset.mem_univ _⟩

lemma F_homogeneous : F.IsHomogeneous 6 := partialF_homogeneous Finset.univ

lemma monic_relPrime_constant {S : Type*} [CommRing S] [IsDomain S]
    {f : Polynomial S} (hf : f.Monic) {c : S} (hc : c ≠ 0) :
    IsRelPrime f (Polynomial.C c) := by
  intro p hpf hpc
  by_contra hunit
  have hpos := Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hf hunit hpf
  have hle := Polynomial.natDegree_le_of_dvd hpc (Polynomial.C_ne_zero.mpr hc)
  simp only [Polynomial.natDegree_C] at hle
  omega

def toUni (j : Fin 6) : R →+* Polynomial R :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => if i = j then Polynomial.X else Polynomial.C (X i))

def fromUni (j : Fin 6) : Polynomial R →+* R :=
  Polynomial.eval₂RingHom (RingHom.id R) (X j)

lemma retract (j : Fin 6) : (fromUni j).comp (toUni j) = RingHom.id R := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [toUni, fromUni]
  · intro i
    by_cases hi : i = j <;> simp [toUni, fromUni, hi]

lemma toUni_partialF (I : Finset (Fin 6)) (j : Fin 6) (hj : j ∉ I) :
    toUni j (partialF I) = Polynomial.C (partialF I) := by
  simp only [partialF, map_sum, map_pow]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  simp [toUni, hij]

lemma toUni_F (j : Fin 6) :
    toUni j F = Polynomial.X ^ 6 + Polynomial.C (partialF (Finset.univ.erase j)) := by
  change toUni j (partialF Finset.univ) = _
  have hsplit : partialF Finset.univ = partialF (Finset.univ.erase j) + (X j : R) ^ 6 := by
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
  rw [hsplit, map_add, toUni_partialF _ _ (Finset.notMem_erase j _)]
  simp [toUni, add_comm]

lemma partialF_legal (I : Finset (Fin 6)) (hI : I.Nonempty) (j : Fin 6) (hj : j ∉ I) :
    IsRelPrime F (partialF I) := by
  have h : IsRelPrime (toUni j F) (toUni j (partialF I)) := by
    rw [toUni_F, toUni_partialF I j hj]
    apply monic_relPrime_constant
    · change (Polynomial.X ^ 6 + Polynomial.C (partialF (Finset.univ.erase j))).leadingCoeff = 1
      exact Polynomial.leadingCoeff_X_pow_add_C (by decide)
    · exact partialF_ne_zero I hI
  intro p hpF hpI
  have hu := (h (map_dvd (toUni j) hpF) (map_dvd (toUni j) hpI)).map (fromUni j)
  have hr : fromUni j (toUni j p) = p := RingHom.congr_fun (retract j) p
  rwa [hr] at hu


def eulerNumerator (I : Finset (Fin 6)) (A : R) (i : Fin 6) : R :=
  if i ∈ I then A * X i else 0

lemma pderiv_partialF (I : Finset (Fin 6)) (i : Fin 6) :
    pderiv i (partialF I) = if i ∈ I then 6 * X i ^ 5 else 0 := by
  simp [partialF, pderiv_pow, pderiv_X, Pi.single_apply, Finset.sum_ite_eq']

lemma pderiv_F (i : Fin 6) : pderiv i F = 6 * X i ^ 5 := by
  change pderiv i (partialF Finset.univ) = _
  simp [pderiv_partialF]

lemma directional_F_euler (I : Finset (Fin 6)) (A : R) :
    directional F (eulerNumerator I A) = 6 * A * partialF I := by
  change (∑ i : Fin 6, (pderiv i (F : R)) * eulerNumerator I A i) = _
  simp only [pderiv_F, eulerNumerator, mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [partialF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma directional_partialF_euler (I : Finset (Fin 6)) (A : R) :
    directional (partialF I) (eulerNumerator I A) = 6 * A * partialF I := by
  change (∑ i : Fin 6, pderiv i (partialF I) * eulerNumerator I A i) = _
  simp only [pderiv_partialF, eulerNumerator, ite_mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [partialF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma divergence_euler (I : Finset (Fin 6)) (A : R) :
    divergence (eulerNumerator I A) = ∑ i ∈ I, (X i * pderiv i A + A) := by
  unfold divergence
  simp only [eulerNumerator, apply_ite, map_zero, Finset.sum_ite_mem, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pderiv_mul, pderiv_X, mul_comm]
  ring


lemma monomial_euler_weight (I : Finset (Fin 6)) (a : Fin 6 →₀ ℕ) (c : ℂ)
    (hI : ∑ i ∈ I, (a i + 1) = 6) :
    ∑ i ∈ I, (X i * pderiv i (monomial a c) + monomial a c) =
      6 * (monomial a c : R) := by
  have he (i : Fin 6) : X i * pderiv i (monomial a c) + monomial a c =
      ((a i + 1 : ℕ) : R) * monomial a c := by
    rw [X_mul_pderiv_monomial]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [he]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hI]
  norm_num

lemma monomial_hasCertificate (q : ℕ) (hq : q ≠ 0) (a : Fin 6 →₀ ℕ) (c : ℂ)
    (ha : a.degree = 6*q) (I : Finset (Fin 6))
    (hI : ∑ i ∈ I, (a i + 1) = 6) (hIp : ∃ j, j ∉ I) :
    HasCertificate F q (monomial a c) := by
  have hIn : I.Nonempty := by
    by_contra h
    have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hI
  obtain ⟨j,hj⟩ := hIp
  let D : R := (6*q) * partialF I
  let N : Fin 6 → R := eulerNumerator I (monomial a c)
  have hqR : (q : R) ≠ 0 := by exact_mod_cast hq
  have hscalar : (6 : R) * q ≠ 0 := mul_ne_zero (by norm_num) hqR
  have hD0 : D ≠ 0 := mul_ne_zero hscalar (partialF_ne_zero I hIn)
  have hDhom : D.IsHomogeneous 6 := by
    simpa only [map_mul, map_ofNat, map_natCast, zero_add] using
      (isHomogeneous_C (σ := Fin 6) (6*(q:ℂ))).mul (partialF_homogeneous I)
  have hdegree : D.totalDegree = 6 := hDhom.totalDegree hD0
  have hAhom : (monomial a c : R).IsHomogeneous (6*q) := by
    exact isHomogeneous_monomial c ha
  refine (show Verify F (monomial a c) 6 q D N 0 from ?_).hasCertificate
  refine {
    hypersurface_ne_zero := F_ne_zero
    hypersurface_homogeneous := F_homogeneous
    source_homogeneous := ?_
    denominator_ne_zero := hD0
    denominator_homogeneous := by simpa only [hdegree] using hDhom
    numerator_homogeneous := ?_
    denominator_legal := ?_
    identity := ?_
  }
  · convert Homogeneous.of_isHomogeneous hAhom using 1 <;> push_cast <;> ring
  · intro i
    change Homogeneous (eulerNumerator I (monomial a c) i) _
    unfold eulerNumerator
    split_ifs with hi
    · convert Homogeneous.of_isHomogeneous (hAhom.mul (isHomogeneous_X ℂ i)) using 1 <;>
        simp only [hdegree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] <;> ring
    · exact homogeneous_zero _
  · apply IsRelPrime.mul_right
    · apply IsUnit.isRelPrime_right
      simpa only [map_mul, map_ofNat, map_natCast] using (isUnit_iff_ne_zero.mpr (show (6 : ℂ)*(q:ℂ) ≠ 0 from
        mul_ne_zero (by norm_num) (by exact_mod_cast hq))).map (MvPolynomial.C : ℂ →+* R)
    · exact partialF_legal I hIn j hj
  · have hdir : directional F N = 6 * monomial a c * partialF I :=
      directional_F_euler I (monomial a c)
    have hdiv : divergence N = 6 * monomial a c := by
      rw [show N = eulerNumerator I (monomial a c) from rfl, divergence_euler]
      exact monomial_euler_weight I a c hI
    have hDdir : directional D N = 6 * monomial a c * D := by
      have hc : directional (6*(q:R)) N = 0 := by
        have hh : directional (C (6*(q:ℂ))) N = 0 := by
          simp only [directional, pderiv_C, zero_mul, Finset.sum_const_zero]
        simpa only [map_mul, map_ofNat, map_natCast] using hh
      change directional ((6*(q:R)) * partialF I) N = _
      rw [directional_product, hc, mul_zero, zero_add]
      change (6*(q:R)) * directional (partialF I) (eulerNumerator I (monomial a c)) = _
      rw [directional_partialF_euler]
      dsimp [D]
      ring
    let f : R := F
    change monomial a c * D^2 - (q:R)*D*directional f N +
      f*(D*divergence N-directional D N) = f^(q+1)*(0:R)
    rw [hdir, hdiv, hDdir]
    simp only [mul_zero]
    dsimp [D]
    ring

end HodgeComputer.Fermat


set_option autoImplicit false
noncomputable section
namespace HodgeComputer.Fermat
open MvPolynomial
open scoped BigOperators

/-- Every homogeneous odd source on the Fermat sextic has a certificate
at pole parameter one or two, by the subset Euler construction. -/
theorem certificate
    (q : ℕ) (hq : q = 1 ∨ q = 2)
    (A : HodgeComputer.AmbientPoly HodgeComputer.Fermat.n)
    (hA : A.IsHomogeneous (HodgeComputer.Fermat.d * q))
    (hodd : HodgeComputer.Fermat.OddSource A) :
    HodgeComputer.HasCertificate HodgeComputer.Fermat.F q A := by
  classical
  let A0 : R := A
  have hA0 : A0.IsHomogeneous (6*q) := hA
  have hodd0 : ∀ ⦃a : Fin 6 →₀ ℕ⦄, coeff a A0 ≠ 0 → Odd (a 3+a 4+a 5) := hodd
  change HasCertificate F q A0
  have hmono (a : Fin 6 →₀ ℕ) (ha : a ∈ A0.support) :
      HasCertificate F q (monomial a (coeff a A0)) := by
    have hc : coeff a A0 ≠ 0 := mem_support_iff.mp ha
    have hdegree : a.degree = 6*q := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hA0 hc
    obtain ⟨I,hI⟩ := subset_euler a q hq
      (by simpa only [← Finsupp.degree_eq_sum] using hdegree) (hodd0 hc)
    have hproper : ∃ j : Fin 6, j ∉ I := by
      by_contra h
      have hfull : I = Finset.univ := Finset.eq_univ_of_forall (by
        intro j
        by_contra hj
        exact h ⟨j,hj⟩)
      have hsum : (∑ i : Fin 6, (a i+1)) = 6*q+6 := by
        rw [Finset.sum_add_distrib, ← Finsupp.degree_eq_sum, hdegree]
        simp
      rw [hfull, hsum] at hI
      rcases hq with rfl | rfl <;> omega
    exact monomial_hasCertificate q (by omega) a (coeff a A0) hdegree I hI hproper
  have hsum (s : Finset (Fin 6 →₀ ℕ)) :
      (∀ a ∈ s, HasCertificate F q (monomial a (coeff a A0))) →
      HasCertificate F q (∑ a ∈ s, monomial a (coeff a A0)) := by
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa only [Finset.sum_empty] using HasCertificate.zero F q F_ne_zero F_homogeneous
    | @insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      exact (hs a (Finset.mem_insert_self a s)).add
        (ih (fun b hb => hs b (Finset.mem_insert_of_mem hb)))
  simpa only [support_sum_monomial_coeff] using hsum A0.support hmono

end HodgeComputer.Fermat
