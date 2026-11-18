import Proposal.GeometricHodgeThreefoldCubic
import Proposal.GeometricHodgeEuler
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cubic normal coordinates of the original affine chart

Reorder the four dehomogenized variables to view the weight-two variable as
the polynomial indeterminate over the three weight-one affine coordinates.
The resulting algebra equivalence carries the actual dehomogenized sextic
to the original cubic multiplied by its invertible leading coefficient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricHodgeThreefoldCubic

open MvPolynomial CycleQ2HodgeEuler
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation vertexCoefficient)

variable {R : Type} [CommRing R]

/-- The original last variable becomes the univariate indeterminate. -/
def pack : MvPolynomial (Fin 4) R ≃ₐ[R] Polynomial (Base R) :=
  (MvPolynomial.renameEquiv R (finRotate 4)).trans (MvPolynomial.finSuccEquiv R 3)

theorem pack_X (j : Fin 4) : pack (X j : MvPolynomial (Fin 4) R) =
    Fin.snoc (α := fun _ => Polynomial (Base R)) (fun k : Fin 3 => Polynomial.C (X k : Base R)) Polynomial.X j := by
  induction j using Fin.lastCases with
  | last =>
    rw [Fin.snoc_last]
    simp [pack, MvPolynomial.finSuccEquiv_X_zero]
  | cast j =>
    have h : finRotate 4 j.castSucc = j.succ := by fin_cases j <;> decide
    simp [pack, h, MvPolynomial.finSuccEquiv_X_succ]

theorem pack_dehom (i : Fin 4) (p : MvPolynomial (Fin 5) R) :
    pack (dehom i p) = expand i p := by
  have hh : pack.toAlgHom.comp (dehom (R := R) i) = expand i := by
    apply MvPolynomial.algHom_ext
    intro j
    induction j using Fin.lastCases with
    | last =>
      have hj : i.castSucc.succAbove (Fin.last 3) = Fin.last 4 := by fin_cases i <;> decide
      change pack (dehom i (X (Fin.last 4)) : MvPolynomial (Fin 4) R) = _
      rw [← hj, dehom_X_succAbove, pack_X, Fin.snoc_last, hj]
      unfold expand
      rw [aeval_X, Fin.snoc_last]
    | cast k =>
      by_cases hk : k = i
      · subst k
        simp [expand, baseValue]
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
        have hj : i.castSucc.succAbove l.castSucc = (i.succAbove l).castSucc := by
          fin_cases i <;> fin_cases l <;> decide
        rw [AlgHom.comp_apply, ← hj, dehom_X_succAbove]
        change pack (X l.castSucc : MvPolynomial (Fin 4) R) = _
        rw [pack_X, hj]
        simp [expand, baseValue]
  exact DFunLike.congr_fun hh p

theorem pack_F (φ : CoeffRing →+* R) (i : Fin 4) (h : IsUnit (φ vertexCoefficient)) :
    pack (F φ i) = Polynomial.C (C (φ vertexCoefficient)) * cubic φ i h :=
  (pack_dehom i _).trans (expand_equation φ i h)

def chartEquivAdjoinRoot (φ : CoeffRing →+* R) (i : Fin 4) (h : IsUnit (φ vertexCoefficient)) :
    chart φ i ≃ₐ[R] AdjoinRoot (cubic φ i h) :=
  Ideal.quotientEquivAlg (Ideal.span {F φ i}) (Ideal.span {cubic φ i h}) pack (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {cubic φ i h} = Ideal.span {pack (F φ i)}
    rw [pack_F φ i h, Ideal.span_singleton_mul_left_unit
      ((h.map (C : R →+* Base R)).map Polynomial.C)])

theorem chartEquivAdjoinRoot_polynomial (φ : CoeffRing →+* R) (i : Fin 4)
    (h : IsUnit (φ vertexCoefficient)) (p : MvPolynomial (Fin 4) R) :
    chartEquivAdjoinRoot φ i h (chartMap φ i p) = AdjoinRoot.mk _ (pack p) := rfl

theorem chartEquivAdjoinRoot_weightTwo (φ : CoeffRing →+* R) (i : Fin 4)
    (h : IsUnit (φ vertexCoefficient)) :
    chartEquivAdjoinRoot φ i h (chartMap φ i (X (Fin.last 3))) = AdjoinRoot.root (cubic φ i h) := by
  rw [chartEquivAdjoinRoot_polynomial, pack_X, Fin.snoc_last, AdjoinRoot.mk_X]

theorem chartEquivAdjoinRoot_weightOne (φ : CoeffRing →+* R) (i : Fin 4)
    (h : IsUnit (φ vertexCoefficient)) (j : Fin 3) :
    chartEquivAdjoinRoot φ i h (chartMap φ i (X j.castSucc)) =
      algebraMap (Base R) (AdjoinRoot (cubic φ i h)) (X j) := by
  rw [chartEquivAdjoinRoot_polynomial, pack_X, Fin.snoc_castSucc, AdjoinRoot.mk_C]
  rfl

def chartCoordinates [Nontrivial R] (φ : CoeffRing →+* R) (i : Fin 4)
    (h : IsUnit (φ vertexCoefficient)) : chart φ i ≃ₗ[R] (Fin 3 → Base R) :=
  (chartEquivAdjoinRoot φ i h).toLinearEquiv.trans ((basis φ i h).equivFun.restrictScalars R)

end CycleQ2GeometricHodgeThreefoldCubic
end

#print axioms CycleQ2GeometricHodgeThreefoldCubic.pack_F
#print axioms CycleQ2GeometricHodgeThreefoldCubic.chartCoordinates
