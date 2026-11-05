import Proposal.CoupledDomain
import HodgeComputer.Verify
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace ReflectionCoupledFano
open MvPolynomial
open scoped BigOperators

def squareVariable {σ : Type*} [DecidableEq σ] (j : σ) :
    MvPolynomial σ ℂ →+* MvPolynomial σ ℂ :=
  eval₂Hom C (fun i => if i=j then X i^2 else X i)

theorem squareVariable_X {σ : Type*} [DecidableEq σ] (j i : σ) :
    squareVariable j (X i) = if i=j then X i^2 else X i := by
  simp [squareVariable]

theorem squareVariable_C {σ : Type*} [DecidableEq σ] (j : σ) (c : ℂ) :
    squareVariable j (C c) = C c := by
  simp [squareVariable]

theorem squareVariable_pderiv {σ : Type*} [DecidableEq σ] (j i : σ)
    (p : MvPolynomial σ ℂ) :
    pderiv i (squareVariable j p) =
      (if i=j then 2*X j else 1) * squareVariable j (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [squareVariable_C]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add]
  | mul_X p k hp =>
    simp only [map_mul, pderiv_mul, map_add, hp, squareVariable_X, pderiv_X]
    by_cases hik : i=k <;> by_cases hij : i=j <;> by_cases hkj : k=j
    all_goals simp [hik, hij, hkj, Pi.single_apply, pderiv_pow, squareVariable_C] <;> ring

theorem eval_squareVariable {σ : Type*} [DecidableEq σ] (j : σ)
    (x : σ → ℂ) (p : MvPolynomial σ ℂ) :
    eval x (squareVariable j p) =
      eval (fun i => if i=j then (x i)^2 else x i) p := by
  have h : (eval₂Hom (RingHom.id ℂ) x).comp (squareVariable j) =
      eval₂Hom (RingHom.id ℂ) (fun i => if i=j then (x i)^2 else x i) := by
    ext i
    · simp [squareVariable_C]
    · by_cases hi : i=j <;> simp [squareVariable_X, hi]
  exact congrArg (fun f : MvPolynomial σ ℂ →+* ℂ => f p) h

theorem squareVariable_injective {σ : Type*} [DecidableEq σ] (j : σ) :
    Function.Injective (squareVariable (σ := σ) j) := by
  intro p q hpq
  apply MvPolynomial.funext
  intro x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x j) (by decide : 0 < 2)
  let y : σ → ℂ := Function.update x j z
  have heval : (fun i => if i=j then (y i)^2 else y i) = x := by
    funext i
    by_cases hij : i=j
    · subst i; simpa [y] using hz
    · simp [y, hij]
  have h := congrArg (eval y) hpq
  simpa only [eval_squareVariable, heval] using h

abbrev squareLast := squareVariable (5 : Fin 6)

theorem half_mul_two : (C ((2 : ℂ)⁻¹) : HodgeComputer.Poly)*2 = 1 := by
  have h := congrArg (C (σ := Fin 6)) (show (2 : ℂ)⁻¹*2 = 1 by norm_num)
  simpa only [map_mul, map_ofNat, map_one] using h

def liftNumerators (N : Fin 6 → HodgeComputer.Poly) : Fin 6 → HodgeComputer.Poly :=
  fun i => if i=5 then C ((2 : ℂ)⁻¹)*squareLast (N i) else X 5*squareLast (N i)

theorem lift_directional (p : HodgeComputer.Poly) (N : Fin 6 → HodgeComputer.Poly) :
    HodgeTestbed.directional (squareLast p) (liftNumerators N) =
      X 5*squareLast (HodgeTestbed.directional p N) := by
  simp only [HodgeTestbed.directional, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [squareVariable_pderiv, map_mul]
  by_cases hi : i=5
  · simp [liftNumerators, hi]
    linear_combination (X 5 * squareLast (pderiv 5 p) * squareLast (N 5)) * half_mul_two
  · simp [liftNumerators, hi]
    ring

theorem lift_divergence (N : Fin 6 → HodgeComputer.Poly) :
    HodgeTestbed.divergence (liftNumerators N) =
      X 5*squareLast (HodgeTestbed.divergence N) := by
  simp only [HodgeTestbed.divergence, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i=5
  · simp [liftNumerators, hi, pderiv_mul, squareVariable_pderiv]
    linear_combination (X 5 * squareLast (pderiv 5 (N 5))) * half_mul_two
  · simp [liftNumerators, hi, pderiv_mul, pderiv_X, Pi.single_apply, squareVariable_pderiv]

theorem lift_divergenceNumerator (D : HodgeComputer.Poly) (N : Fin 6 → HodgeComputer.Poly) :
    HodgeTestbed.divergenceNumerator (squareLast D) (liftNumerators N) =
      X 5*squareLast (HodgeTestbed.divergenceNumerator D N) := by
  simp only [HodgeTestbed.divergenceNumerator, lift_divergence, lift_directional,
    map_sub, map_mul]
  ring

theorem squareLast_hypersurface (k : ℂ) :
    squareLast (hypersurface k 3 1) = hypersurface k 6 2 := by
  simp only [hypersurface, map_add, map_mul, map_pow, map_ofNat, squareVariable_C, squareVariable_X]
  simp only [show (0 : Fin 6) ≠ 5 by decide, show (1 : Fin 6) ≠ 5 by decide,
    show (2 : Fin 6) ≠ 5 by decide, show (3 : Fin 6) ≠ 5 by decide,
    show (4 : Fin 6) ≠ 5 by decide, if_false, if_true]
  ring


theorem squareLast_univariate (p : HodgeComputer.Poly) :
    MvPolynomial.finSuccEquiv ℂ 5 (squareLast p) =
      (MvPolynomial.finSuccEquiv ℂ 5 p).map (squareVariable (4 : Fin 5)) := by
  have he : (Fin.cases (Polynomial.X : Polynomial (MvPolynomial (Fin 5) ℂ))
      (fun j => Polynomial.C (MvPolynomial.X j))) =
      ![Polynomial.X, Polynomial.C (MvPolynomial.X 0), Polynomial.C (MvPolynomial.X 1),
        Polynomial.C (MvPolynomial.X 2), Polynomial.C (MvPolynomial.X 3),
        Polynomial.C (MvPolynomial.X 4)] := by
    funext i
    fin_cases i <;> rfl
  have hX (i : Fin 6) :
      MvPolynomial.finSuccEquiv ℂ 5 (squareLast (X i)) =
        (MvPolynomial.finSuccEquiv ℂ 5 (X i)).map (squareVariable (4 : Fin 5)) := by
    fin_cases i <;>
      simp [squareVariable_X, MvPolynomial.finSuccEquiv_apply, he, squareVariable_C]
  induction p using MvPolynomial.induction_on with
  | C c => simp [squareVariable_C, MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul, hp, Polynomial.map_mul, hX]

theorem squareLast_not_dvd (k : ℂ) (D : HodgeComputer.Poly)
    (hD : ¬ hypersurface k 3 1 ∣ D) :
    ¬ hypersurface k 6 2 ∣ squareLast D := by
  intro hd
  rw [← squareLast_hypersurface] at hd
  have hm := map_dvd (MvPolynomial.finSuccEquiv ℂ 5) hd
  rw [squareLast_univariate, squareLast_univariate, hypersurface_univariate] at hm
  have hd' := (Polynomial.map_dvd_map (squareVariable (4 : Fin 5))
    (squareVariable_injective (4 : Fin 5)) (polynomial_monic k 3 1)).mp hm
  apply hD
  apply (map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp
  simpa only [hypersurface_univariate] using hd'

theorem squareLast_legal (k : ℂ) (D : HodgeComputer.Poly)
    (hD : IsRelPrime (hypersurface k 3 1) D) :
    IsRelPrime (hypersurface k 6 2) (squareLast D) := by
  apply (physical_irreducible k).isRelPrime_iff_not_dvd.mpr
  apply squareLast_not_dvd k D
  exact (weighted_quotient_irreducible k).isRelPrime_iff_not_dvd.mp hD

theorem reflection_normalized_identities
    (k : ℂ) (A D Q : HodgeComputer.Poly) (N : Fin 6 → HodgeComputer.Poly)
    (h1 : HodgeTestbed.directional (hypersurface k 3 1) N = A*D)
    (h2 : HodgeTestbed.divergenceNumerator D N = hypersurface k 3 1*Q) :
    HodgeTestbed.directional (hypersurface k 6 2) (liftNumerators N) =
      (X 5*squareLast A)*squareLast D ∧
    HodgeTestbed.divergenceNumerator (squareLast D) (liftNumerators N) =
      hypersurface k 6 2*(X 5*squareLast Q) := by
  constructor
  · rw [← squareLast_hypersurface, lift_directional, h1, map_mul]
    ring
  · rw [lift_divergenceNumerator, h2, map_mul, squareLast_hypersurface]
    ring


theorem reflection_source :
    X 5*squareLast (quotientSource (R := ℂ)) = physicalSource := by
  simp only [quotientSource, physicalSource, map_mul, map_pow, squareVariable_X]
  simp only [show (0 : Fin 6) ≠ 5 by decide, if_false, if_true]
  ring

theorem reflection_normalized_data
    (k : ℂ) (D Q : HodgeComputer.Poly) (N : Fin 6 → HodgeComputer.Poly)
    (hlegal : IsRelPrime (hypersurface k 3 1) D)
    (h1 : HodgeTestbed.directional (hypersurface k 3 1) N = quotientSource*D)
    (h2 : HodgeTestbed.divergenceNumerator D N = hypersurface k 3 1*Q) :
    IsRelPrime (hypersurface k 6 2) (squareLast D) ∧
    HodgeTestbed.directional (hypersurface k 6 2) (liftNumerators N) =
      physicalSource*squareLast D ∧
    HodgeTestbed.divergenceNumerator (squareLast D) (liftNumerators N) =
      hypersurface k 6 2*(X 5*squareLast Q) := by
  refine ⟨squareLast_legal k D hlegal, ?_⟩
  have h := reflection_normalized_identities k quotientSource D Q N h1 h2
  simpa only [reflection_source] using h

end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.reflection_normalized_identities

#print axioms ReflectionCoupledFano.squareLast_legal
#print axioms ReflectionCoupledFano.reflection_normalized_data
