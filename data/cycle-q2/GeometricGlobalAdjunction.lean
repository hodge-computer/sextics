import Proposal.GeometricAffineOverlap
import Proposal.GeometricGlobalResidue

/-!
# The full overlap transition of the affine residue frames

The actual coordinate Jacobian sends the second gradient cokernel to the
first. Its residue coefficient scales by minus the coordinate x2/x1.
Consequently the global frames constructed from the unit Jacobian ideals
have the required projective transition on the entire coordinate overlap,
including points where the middle Jacobian minor vanishes.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricGlobalAdjunction

open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricAdjunctionOverlap
  CycleQ2GeometricCofactorResidue CycleQ2GeometricGlobalResidue

variable {R : Type*} [CommRing R]

/-- Pullback of coordinate one-forms by (a,b,c) ↦ (a/b,1/b,c/b). -/
def pullForm (a c t : R) : Coordinates R →ₗ[R] Coordinates R where
  toFun v := ![t * v 0,
    -(a * t ^ 2) * v 0 - t ^ 2 * v 1 - c * t ^ 2 * v 2,
    t * v 2]
  map_add' v w := by
    ext j
    fin_cases j <;> simp <;> ring
  map_smul' q v := by
    ext j
    fin_cases j <;> simp <;> ring

theorem pullForm_eq_pullRow (a c t : R) (v : Coordinates R) :
    pullForm a c t v = pullRow a c t v := by
  ext j
  fin_cases j <;>
    simp [pullForm, pullRow, coordinateJacobian, Fin.sum_univ_succ] <;> ring

variable (r i θ a b c t : R)
  (ht : b * t = 1) (hf : quadricOne r a b c = 0) (hh : cubicOne i θ a b c = 0)

include hf in
theorem pullForm_quadric :
    pullForm a c t (gradQuadricTwo r (a * t) t (c * t)) =
      t ^ 2 • gradQuadricOne r a := by
  rw [pullForm_eq_pullRow, quadratic_differential_change]
  have hf' : quadricOne r a 0 c = 0 := hf
  ext j
  simp only [hf', mul_zero, sub_zero, Pi.smul_apply, smul_eq_mul, ite_self]

include ht hh in
theorem pullForm_cubic :
    pullForm a c t (gradCubicTwo i θ (a * t) t (c * t)) =
      t ^ 3 • gradCubicOne i θ a b c := by
  rw [pullForm_eq_pullRow, cubic_differential_change i θ a b c t ht]
  ext j
  simp only [hh, mul_zero, sub_zero, Pi.smul_apply, smul_eq_mul, ite_self]

abbrev FirstResidue := ResidueModule (gradQuadricOne r a) (gradCubicOne i θ a b c)
abbrev SecondResidue := ResidueModule (gradQuadricTwo r (a * t) t (c * t))
  (gradCubicTwo i θ (a * t) t (c * t))

include ht hf hh in
private theorem relations_le_pull_kernel :
    relations (gradQuadricTwo r (a * t) t (c * t))
        (gradCubicTwo i θ (a * t) t (c * t)) ≤
      LinearMap.ker
        ((toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)).comp (pullForm a c t)) := by
  apply Submodule.span_le.mpr
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with hv | hv
  · subst v
    change toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)
      (pullForm a c t (gradQuadricTwo r (a * t) t (c * t))) = 0
    rw [pullForm_quadric r a b c t hf, map_smul]
    have hz : toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)
        (gradQuadricOne r a) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (first_relation_mem _ _)
    rw [hz, smul_zero]
  · subst v
    change toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)
      (pullForm a c t (gradCubicTwo i θ (a * t) t (c * t))) = 0
    rw [pullForm_cubic i θ a b c t ht hh, map_smul]
    have hz : toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)
        (gradCubicOne i θ a b c) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (second_relation_mem _ _)
    rw [hz, smul_zero]

/-- The coordinate pullback on the actual two-gradient cokernels. -/
def residuePullback : SecondResidue r i θ a c t →ₗ[R] FirstResidue r i θ a b c :=
  (relations (gradQuadricTwo r (a * t) t (c * t))
    (gradCubicTwo i θ (a * t) t (c * t))).liftQ
    ((toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)).comp (pullForm a c t))
    (relations_le_pull_kernel r i θ a b c t ht hf hh)

@[simp] theorem residuePullback_toResidue (v : Coordinates R) :
    residuePullback r i θ a b c t ht hf hh
      (toResidue (gradQuadricTwo r (a * t) t (c * t))
        (gradCubicTwo i θ (a * t) t (c * t)) v) =
      toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c) (pullForm a c t v) := rfl

include ht hf hh in
/-- The complete cofactor transformation, with no chosen invertible minor. -/
theorem coefficient_pullForm (v : Coordinates R) :
    coefficient (gradQuadricOne r a) (gradCubicOne i θ a b c) (pullForm a c t v) =
      -b * coefficient (gradQuadricTwo r (a * t) t (c * t))
        (gradCubicTwo i θ (a * t) t (c * t)) v := by
  have he := CycleQ2GeometricAffineOverlap.cofactor_change_on_curve
    r i θ a b c t ht hf hh
  change cofactor (gradQuadricTwo r (a * t) t (c * t))
      (gradCubicTwo i θ (a * t) t (c * t)) =
    ![-t ^ 2 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 0 +
        a * t ^ 3 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 1,
      t ^ 3 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 1,
      -t ^ 2 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 2 +
        c * t ^ 3 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 1] at he
  simp only [coefficient_apply, he]
  simp [pullForm]
  linear_combination
    (t ^ 2 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 1 *
        (a * v 0 + v 1 + c * v 2) -
      t * (cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 0 * v 0 +
        cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 2 * v 2)) * ht

theorem residueFunctional_pullback (η : SecondResidue r i θ a c t) :
    residueFunctional (gradQuadricOne r a) (gradCubicOne i θ a b c)
      (residuePullback r i θ a b c t ht hf hh η) =
      -b * residueFunctional (gradQuadricTwo r (a * t) t (c * t))
        (gradCubicTwo i θ (a * t) t (c * t)) η := by
  refine Quotient.inductionOn' η (fun v => ?_)
  exact coefficient_pullForm r i θ a b c t ht hf hh v

/-- The global affine frames have the expected transition everywhere on
the coordinate overlap. Projective orientation changes the sign to +b. -/
theorem globalResidue_transport
    (hfirst : minorIdeal (gradQuadricOne r a) (gradCubicOne i θ a b c) = ⊤)
    (hsecond : minorIdeal (gradQuadricTwo r (a * t) t (c * t))
      (gradCubicTwo i θ (a * t) t (c * t)) = ⊤) :
    residuePullback r i θ a b c t ht hf hh
      (globalResidue _ _ hsecond) = -b • globalResidue _ _ hfirst := by
  apply CycleQ2GeometricGlobalResidue.residueFunctional_injective _ _ hfirst
  rw [residueFunctional_pullback, residueFunctional_globalResidue, mul_one,
    map_smul, residueFunctional_globalResidue, smul_eq_mul, mul_one]

#print axioms residuePullback
#print axioms residueFunctional_pullback
#print axioms globalResidue_transport

end CycleQ2GeometricGlobalAdjunction
end
