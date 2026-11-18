import Proposal.SolutionSupport02Part02
import Proposal.GeometricHodgeEulerChartDerivations
import Proposal.GeometricSurfaceBindings
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The normalized gradient and Euler vector on a weight-one sextic chart

Set the chosen weight-one coordinate to one and use the remaining four
unshifted coordinates. On the quotient by the actual specialized sextic,
the corresponding four ambient partials are the derivatives of the chart
equation. The weighted Euler vector annihilates the full gradient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeEuler

open MvPolynomial CycleQ2GenericSexticGradient CycleQ2IncidenceNormalForm
open CycleQ2GeometricIncidenceProj

variable {R : Type*} [CommRing R]

def dehom (i : Fin 4) : MvPolynomial (Fin 5) R →ₐ[R] MvPolynomial (Fin 4) R :=
  aeval (i.castSucc.insertNth 1 (fun j : Fin 4 => X j))

@[simp] theorem dehom_X_self (i : Fin 4) : dehom (R := R) i (X i.castSucc) = 1 := by
  simp [dehom]

@[simp] theorem dehom_X_succAbove (i j : Fin 4) :
    dehom (R := R) i (X (i.castSucc.succAbove j)) = X j := by
  simp [dehom]

def F (φ : CoeffRing →+* R) (i : Fin 4) := dehom i (MvPolynomial.map φ universalF)

abbrev chart (φ : CoeffRing →+* R) (i : Fin 4) := CycleQ2HodgeEulerChartDerivations.Hyp (F φ i)

def chartMap (φ : CoeffRing →+* R) (i : Fin 4) :
    MvPolynomial (Fin 4) R →ₐ[R] chart φ i := CycleQ2HodgeEulerChartDerivations.mk (F φ i)

@[simp] theorem chartMap_F (φ : CoeffRing →+* R) (i : Fin 4) : chartMap φ i (F φ i) = 0 :=
  CycleQ2HodgeEulerChartDerivations.mk_equation _

private theorem pderiv_dehom_X (i k : Fin 4) (j : Fin 5) :
    pderiv k (dehom (R := R) i (X j)) = dehom i (pderiv (i.castSucc.succAbove k) (X j)) := by
  refine Fin.succAboveCases i.castSucc ?_ (fun a => ?_) j
  · rw [dehom_X_self, pderiv_X_of_ne (Fin.succAbove_ne _ _).symm, map_zero, Derivation.map_one_eq_zero]
  · by_cases h : a = k
    · subst a
      rw [dehom_X_succAbove, pderiv_X_self, pderiv_X_self, map_one]
    · rw [dehom_X_succAbove, pderiv_X_of_ne h, pderiv_X_of_ne (Fin.succAbove_right_injective.ne h), map_zero]

theorem pderiv_dehom (i k : Fin 4) (p : MvPolynomial (Fin 5) R) :
    pderiv k (dehom i p) = dehom i (pderiv (i.castSucc.succAbove k) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [dehom]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, pderiv_mul, map_add, hp, pderiv_dehom_X]

def coordinate (φ : CoeffRing →+* R) (i : Fin 4) (j : Fin 5) : chart φ i :=
  chartMap φ i (dehom i (X j))

def radial (φ : CoeffRing →+* R) (i : Fin 4) (j : Fin 5) : chart φ i :=
  (geometricWeight j : chart φ i) * coordinate φ i j

def conePartial (φ : CoeffRing →+* R) (i : Fin 4) (j : Fin 5) : chart φ i :=
  chartMap φ i (dehom i (pderiv j (MvPolynomial.map φ universalF)))

@[simp] theorem radial_self (φ : CoeffRing →+* R) (i : Fin 4) : radial φ i i.castSucc = 1 := by
  have hi : geometricWeight i.castSucc = 1 := by fin_cases i <;> rfl
  simp [radial, hi, coordinate]

theorem partial_succAbove (φ : CoeffRing →+* R) (i j : Fin 4) :
    conePartial φ i (i.castSucc.succAbove j) = chartMap φ i (pderiv j (F φ i)) :=
  congrArg (chartMap φ i) (pderiv_dehom i j (MvPolynomial.map φ universalF)).symm

theorem family_homogeneous (φ : CoeffRing →+* R) :
    (MvPolynomial.map φ universalF).IsWeightedHomogeneous geometricWeight 6 := by
  rw [universalF, map_fullInvariantPolynomial]
  exact homogeneous_of_character (fullInvariantPolynomial_homogeneous 6 _)

private theorem evalEuler {S : Type*} [CommRing S] (f : MvPolynomial (Fin 5) R →+* S)
    (G : MvPolynomial (Fin 5) R) (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (hz : f G = 0) :
    ∑ j : Fin 5, f (pderiv j G) * ((geometricWeight j : S) * f (X j)) = 0 := by
  calc
    _ = ∑ j : Fin 5, geometricWeight j • f (X j * pderiv j G) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [nsmul_eq_mul, map_mul]
      ring
    _ = f (∑ j : Fin 5, geometricWeight j • (X j * pderiv j G)) := by simp
    _ = 0 := by rw [hG.sum_weight_X_mul_pderiv, map_nsmul, hz, nsmul_zero]

theorem radial_equation (φ : CoeffRing →+* R) (i : Fin 4) :
    ∑ j : Fin 5, conePartial φ i j * radial φ i j = 0 :=
  evalEuler ((chartMap φ i).toRingHom.comp (dehom i).toRingHom)
    (MvPolynomial.map φ universalF) (family_homogeneous φ) (chartMap_F φ i)

end CycleQ2HodgeEuler
end

#print axioms CycleQ2HodgeEuler.pderiv_dehom
#print axioms CycleQ2HodgeEuler.radial_equation
