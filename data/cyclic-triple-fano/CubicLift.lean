import Proposal.CyclicDomain
import HodgeComputer.Verify
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace CyclicTriple
open MvPolynomial
open scoped BigOperators

def cubeVariable {σ : Type*} [DecidableEq σ] (j : σ) :
    MvPolynomial σ ℂ →+* MvPolynomial σ ℂ :=
  eval₂Hom C (fun i => if i=j then X i^3 else X i)

theorem cubeVariable_X {σ : Type*} [DecidableEq σ] (j i : σ) :
    cubeVariable j (X i) = if i=j then X i^3 else X i := by
  simp [cubeVariable]

theorem cubeVariable_C {σ : Type*} [DecidableEq σ] (j : σ) (c : ℂ) :
    cubeVariable j (C c) = C c := by
  simp [cubeVariable]

theorem cubeVariable_pderiv {σ : Type*} [DecidableEq σ] (j i : σ)
    (p : MvPolynomial σ ℂ) :
    pderiv i (cubeVariable j p) =
      (if i=j then 3*X j^2 else 1) * cubeVariable j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [cubeVariable_C]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add]
  | mul_X p k hp =>
    simp only [map_mul, pderiv_mul, map_add, hp, cubeVariable_X, pderiv_X]
    by_cases hik : i=k <;> by_cases hij : i=j <;> by_cases hkj : k=j
    all_goals simp [hik, hij, hkj, Pi.single_apply, pderiv_pow, cubeVariable_C] <;> ring

theorem eval_cubeVariable {σ : Type*} [DecidableEq σ] (j : σ)
    (x : σ → ℂ) (p : MvPolynomial σ ℂ) :
    eval x (cubeVariable j p) =
      eval (fun i => if i=j then (x i)^3 else x i) p := by
  have h : (eval₂Hom (RingHom.id ℂ) x).comp (cubeVariable j) =
      eval₂Hom (RingHom.id ℂ) (fun i => if i=j then (x i)^3 else x i) := by
    ext i
    · simp [cubeVariable_C]
    · by_cases hi : i=j <;> simp [cubeVariable_X, hi]
  exact congrArg (fun f : MvPolynomial σ ℂ →+* ℂ => f p) h

theorem cubeVariable_injective {σ : Type*} [DecidableEq σ] (j : σ) :
    Function.Injective (cubeVariable (σ := σ) j) := by
  intro p q hpq
  apply MvPolynomial.funext
  intro x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x j) (by decide : 0 < 3)
  let y : σ → ℂ := Function.update x j z
  have heval : (fun i => if i=j then (y i)^3 else y i) = x := by
    funext i
    by_cases hij : i=j
    · subst i; simpa [y] using hz
    · simp [y, hij]
  have h := congrArg (eval y) hpq
  simpa only [eval_cubeVariable, heval] using h

abbrev cubeLast := cubeVariable (5 : Fin 6)

theorem third_mul_three : (C ((3 : ℂ)⁻¹) : HodgeComputer.Poly)*3 = 1 := by
  have h := congrArg (C (σ := Fin 6)) (show (3 : ℂ)⁻¹*3 = 1 by norm_num)
  simpa only [map_mul, map_ofNat, map_one] using h

def liftNumerators (N : Fin 6 → HodgeComputer.Poly) : Fin 6 → HodgeComputer.Poly :=
  fun i => if i=5 then C ((3 : ℂ)⁻¹)*cubeLast (N i) else X 5^2*cubeLast (N i)

theorem lift_directional (p : HodgeComputer.Poly) (N : Fin 6 → HodgeComputer.Poly) :
    HodgeTestbed.directional (cubeLast p) (liftNumerators N) =
      X 5^2*cubeLast (HodgeTestbed.directional p N) := by
  simp only [HodgeTestbed.directional, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [cubeVariable_pderiv, map_mul]
  by_cases hi : i=5
  · simp [liftNumerators, hi]
    linear_combination (X 5^2 * cubeLast (pderiv 5 p) * cubeLast (N 5)) * third_mul_three
  · simp [liftNumerators, hi]
    ring

theorem lift_divergence (N : Fin 6 → HodgeComputer.Poly) :
    HodgeTestbed.divergence (liftNumerators N) =
      X 5^2*cubeLast (HodgeTestbed.divergence N) := by
  simp only [HodgeTestbed.divergence, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i=5
  · simp [liftNumerators, hi, pderiv_mul, cubeVariable_pderiv]
    linear_combination (X 5^2 * cubeLast (pderiv 5 (N 5))) * third_mul_three
  · simp [liftNumerators, hi, pderiv_mul, pderiv_X, pderiv_pow, Pi.single_apply, cubeVariable_pderiv]

theorem lift_divergenceNumerator (D : HodgeComputer.Poly) (N : Fin 6 → HodgeComputer.Poly) :
    HodgeTestbed.divergenceNumerator (cubeLast D) (liftNumerators N) =
      X 5^2*cubeLast (HodgeTestbed.divergenceNumerator D N) := by
  simp only [HodgeTestbed.divergenceNumerator, lift_divergence, lift_directional,
    map_sub, map_mul]
  ring

theorem cubeLast_hypersurface (k : ℂ) :
    cubeLast (hypersurface k 2 1) = hypersurface k 6 3 := by
  simp only [hypersurface, map_add, map_mul, map_pow, map_ofNat, cubeVariable_C, cubeVariable_X]
  simp only [show (0 : Fin 6) ≠ 5 by decide, show (1 : Fin 6) ≠ 5 by decide,
    show (2 : Fin 6) ≠ 5 by decide, show (3 : Fin 6) ≠ 5 by decide,
    show (4 : Fin 6) ≠ 5 by decide, if_false, if_true]
  ring


theorem cubeLast_univariate (p : HodgeComputer.Poly) :
    MvPolynomial.finSuccEquiv ℂ 5 (cubeLast p) =
      (MvPolynomial.finSuccEquiv ℂ 5 p).map (cubeVariable (4 : Fin 5)) := by
  have he : (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 5) ℂ))
      (fun j => Polynomial.C (MvPolynomial.X j))) =
      ![Polynomial.X, Polynomial.C (MvPolynomial.X 0), Polynomial.C (MvPolynomial.X 1),
        Polynomial.C (MvPolynomial.X 2), Polynomial.C (MvPolynomial.X 3),
        Polynomial.C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  have hX (i : Fin 6) :
      MvPolynomial.finSuccEquiv ℂ 5 (cubeLast (X i)) =
        (MvPolynomial.finSuccEquiv ℂ 5 (X i)).map (cubeVariable (4 : Fin 5)) := by
    fin_cases i <;>
      simp [cubeVariable_X, MvPolynomial.finSuccEquiv_apply, he, cubeVariable_C]
  induction p using MvPolynomial.induction_on with
  | C c => simp [cubeVariable_C, MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul, hp, Polynomial.map_mul, hX]

theorem cubeLast_not_dvd (k : ℂ) (D : HodgeComputer.Poly)
    (hD : ¬ hypersurface k 2 1 ∣ D) :
    ¬ hypersurface k 6 3 ∣ cubeLast D := by
  intro hd
  rw [← cubeLast_hypersurface] at hd
  have hm := map_dvd (MvPolynomial.finSuccEquiv ℂ 5) hd
  rw [cubeLast_univariate, cubeLast_univariate, hypersurface_univariate] at hm
  have hd' := (Polynomial.map_dvd_map (cubeVariable (4 : Fin 5))
    (cubeVariable_injective (4 : Fin 5)) (polynomial_monic k 2 1)).mp hm
  apply hD
  apply (map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp
  simpa only [hypersurface_univariate] using hd'

theorem cubeLast_legal (k : ℂ) (D : HodgeComputer.Poly)
    (hD : IsRelPrime (hypersurface k 2 1) D) :
    IsRelPrime (hypersurface k 6 3) (cubeLast D) := by
  apply (physical_irreducible k).isRelPrime_iff_not_dvd.mpr
  apply cubeLast_not_dvd k D
  exact (weighted_quotient_irreducible k).isRelPrime_iff_not_dvd.mp hD

theorem cubic_normalized_identities
    (k : ℂ) (A D Q : HodgeComputer.Poly) (N : Fin 6 → HodgeComputer.Poly)
    (h1 : HodgeTestbed.directional (hypersurface k 2 1) N = A*D)
    (h2 : HodgeTestbed.divergenceNumerator D N = hypersurface k 2 1*Q) :
    HodgeTestbed.directional (hypersurface k 6 3) (liftNumerators N) =
      (X 5^2*cubeLast A)*cubeLast D ∧
    HodgeTestbed.divergenceNumerator (cubeLast D) (liftNumerators N) =
      hypersurface k 6 3*(X 5^2*cubeLast Q) := by
  constructor
  · rw [← cubeLast_hypersurface, lift_directional, h1, map_mul]
    ring
  · rw [lift_divergenceNumerator, h2, map_mul, cubeLast_hypersurface]
    ring


end CyclicTriple

#print axioms CyclicTriple.cubic_normalized_identities
#print axioms CyclicTriple.cubeLast_legal
