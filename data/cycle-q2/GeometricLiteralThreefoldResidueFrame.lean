import Proposal.GeometricLiteralAbelJacobiContraction
import Proposal.GeometricSurfaceResidueFunctoriality
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Threefold Kähler frames on the gradient opens of the fixed sextic

On the open where the chosen partial of the fixed equation is invertible,
the differentials of the three other coordinates form a basis. Thus their
signed wedge divided by the partial generates the top exterior power.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldResidueFrame

open Module MvPolynomial CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEquations
  CycleQ2ExteriorTopBaseChange

abbrev gradient (i j : Fin 4) := (Ideal.Quotient.mkₐ ℂ (fixedIdeal i))
    (pderiv ((_root_.finSuccEquiv 3) j) (seedF i))
abbrev Patch (i j : Fin 4) := Localization.Away (gradient i j)

private def equationPresentation (i j : Fin 4) :
    Algebra.PreSubmersivePresentation ℂ (T i) (Option (Fin 3)) Unit where
  toPresentation :=
    { toGenerators := Algebra.Generators.naive (I := fixedIdeal i)
      relation := fun _ => seedF i
      span_range_relation_eq_ker := by rw [Algebra.Generators.ker_naive, Set.range_const] }
  map := fun _ => (_root_.finSuccEquiv 3) j
  map_inj := fun _ _ _ => Subsingleton.elim _ _

private theorem equationPresentation_jacobian (i j : Fin 4) :
    (equationPresentation i j).jacobian = gradient i j := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

private def localizedPresentation (i j : Fin 4) :
    Algebra.PreSubmersivePresentation ℂ (Patch i j) (Unit ⊕ Option (Fin 3)) (Unit ⊕ Unit) :=
  (Algebra.PreSubmersivePresentation.localizationAway (Patch i j) (gradient i j)).comp
    (equationPresentation i j)

private def smoothPresentation (i j : Fin 4) :
    Algebra.SubmersivePresentation ℂ (Patch i j) (Unit ⊕ Option (Fin 3)) (Unit ⊕ Unit) where
  toPreSubmersivePresentation := localizedPresentation i j
  jacobian_isUnit := by
    rw [localizedPresentation, Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      equationPresentation_jacobian, Algebra.PreSubmersivePresentation.localizationAway_jacobian,
      Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Patch i j) _).mul
      (IsLocalization.Away.algebraMap_isUnit (S := Patch i j) _)

private def omitted (j : Fin 4) (k : Fin 3) : Unit ⊕ Option (Fin 3) :=
  Sum.inr ((_root_.finSuccEquiv 3) (j.succAbove k))

private theorem omitted_injective (j : Fin 4) : Function.Injective (omitted j) :=
  Sum.inr_injective.comp ((_root_.finSuccEquiv 3).injective.comp j.succAbove_right_injective)

private theorem complement (i j : Fin 4) :
    IsCompl (Set.range (omitted j)) (Set.range (smoothPresentation i j).map) := by
  classical
  have hs : Set.range (smoothPresentation i j).map = {Sum.inl (), Sum.inr ((_root_.finSuccEquiv 3) j)} := by
    ext x
    change (∃ q : Unit ⊕ Unit, Sum.elim (fun _ => Sum.inl ()) (fun _ => Sum.inr ((_root_.finSuccEquiv 3) j)) q = x) ↔ _
    simp [Sum.exists, eq_comm]
  rw [hs]
  apply IsCompl.of_eq
  all_goals
    ext x
    cases x with
    | inl u => simp [omitted]
    | inr a =>
        obtain ⟨n, rfl⟩ := (_root_.finSuccEquiv 3).surjective a
        have h : (∃ k, j.succAbove k = n) ↔ n ≠ j := by
          change n ∈ Set.range j.succAbove ↔ _
          rw [Fin.range_succAbove]
          rfl
        simp [omitted, Set.mem_range, (_root_.finSuccEquiv 3).injective.eq_iff, h] <;> exact em _

/-- The complementary derivatives of the chosen presentation. -/
def basis (i j : Fin 4) :
    Basis (Fin 3) (Patch i j) (KaehlerDifferential ℂ (Patch i j)) :=
  (smoothPresentation i j).basisKaehlerOfIsCompl (omitted_injective j) (complement i j)

theorem basis_apply (i j : Fin 4) (k : Fin 3) :
    basis i j k = KaehlerDifferential.D ℂ (Patch i j)
      (algebraMap (T i) (Patch i j) (Ideal.Quotient.mk _ (X ((_root_.finSuccEquiv 3) (j.succAbove k))))) := by
  rw [basis, Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply]
  rfl

/-- Scaling the wedge of the three retained coordinate differentials by a
unit gives a frame of the actual localized exterior cube. -/
theorem unique_scaled_wedge (i j : Fin 4) (u : (Patch i j)ˣ)
    (w : ⋀[Patch i j]^3 (KaehlerDifferential ℂ (Patch i j))) :
    ∃! c : Patch i j, c • ((u : Patch i j) • exteriorPower.ιMulti _ 3 (basis i j)) = w := by
  let e := (LinearEquiv.smulOfUnit u : Patch i j ≃ₗ[Patch i j] Patch i j).trans
    (topCoordinateEquiv (basis i j)).symm
  have he (a : Patch i j) :
      e a = a • ((u : Patch i j) • exteriorPower.ιMulti _ 3 (basis i j)) := by
    change ((u : Patch i j) * a) • exteriorPower.ιMulti _ 3 (basis i j) = _
    rw [smul_smul, mul_comm]
  simpa only [he] using e.bijective.existsUnique w

/-- Every localized three-form has a unique coefficient in the oriented
Jacobian residue frame. -/
theorem residue_frame (i j : Fin 4) (w : ⋀[Patch i j]^3 (KaehlerDifferential ℂ (Patch i j))) :
    ∃! c : Patch i j, c •
      ((↑((IsLocalization.Away.algebraMap_isUnit (S := Patch i j) (gradient i j)).unit⁻¹) : Patch i j) •
        ((-1 : Patch i j) ^ j.val • exteriorPower.ιMulti _ 3 (fun k : Fin 3 =>
          KaehlerDifferential.D ℂ (Patch i j) (algebraMap (T i) (Patch i j)
            (Ideal.Quotient.mk _ (X ((_root_.finSuccEquiv 3) (j.succAbove k)))))))) = w := by
  let u := (IsLocalization.Away.algebraMap_isUnit (S := Patch i j) (gradient i j)).unit
  have hb : (basis i j : Fin 3 → _) = fun k => KaehlerDifferential.D ℂ (Patch i j)
      (algebraMap (T i) (Patch i j)
        (Ideal.Quotient.mk _ (X ((_root_.finSuccEquiv 3) (j.succAbove k))))) :=
    funext (basis_apply i j)
  simpa only [u, hb, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    mul_smul] using unique_scaled_wedge i j (u⁻¹ * (-1 : (Patch i j)ˣ) ^ j.val) w

end CycleQ2LiteralThreefoldResidueFrame
end

#print axioms CycleQ2LiteralThreefoldResidueFrame.basis_apply
#print axioms CycleQ2LiteralThreefoldResidueFrame.unique_scaled_wedge
#print axioms CycleQ2LiteralThreefoldResidueFrame.residue_frame
