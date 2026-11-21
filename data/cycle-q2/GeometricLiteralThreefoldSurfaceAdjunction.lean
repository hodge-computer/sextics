import Proposal.GeometricLiteralThreefoldResidueGluing
import Proposal.GeometricLiteralAbelJacobiRelativeNormal

/-!
# Restriction of the threefold volume along the cubic surface

The cubic conormal followed by two polynomial differentials wedges to the
ordered augmented Jacobian times the fixed threefold's regular volume.
Evaluation on a moving normal and two vectors tangent to the cubic thus
only uses the cubic component of the normal.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldSurfaceAdjunction

open Module MvPolynomial CycleQ2LiteralThreefoldResidueGluing
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueMinors
  CycleQ2LiteralThreefoldChartVolume CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2GeometricExteriorSheaf CycleQ2ExteriorSectionNaturality CycleQ2GeometricAffineOverlap
  CycleQ2GeometricSurfaceAdjunction CycleQ2ExteriorTopBaseChange

attribute [local irreducible] seedF seedH chartVolume

variable (i : Fin 4)
private abbrev mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
private abbrev basis₄ := Pi.basisFun (T i) (Fin 4)
private abbrev covector (p : P) (j : Fin 4) : T i := mk i (pderiv (coordIndex j) p)
private def toForms : (Fin 4 → T i) →ₗ[T i] KaehlerDifferential ℂ (T i) :=
  (basis₄ i).constr (T i) (coordinateForm i (AlgHom.id ℂ (T i)))

private theorem toForms_basis (j : Fin 4) :
    toForms i (basis₄ i j) = coordinateForm i (AlgHom.id ℂ (T i)) j := by
  simp [toForms]

private theorem toForms_covector (p : P) :
    toForms i (covector i p) = KaehlerDifferential.D ℂ (T i) (mk i p) := by
  rw [← (basis₄ i).sum_repr (covector i p), map_sum]
  simp only [map_smul, toForms_basis, Pi.basisFun_repr]
  exact (Equiv.sum_comp coordIndex (fun j => mk i (pderiv j p) •
    KaehlerDifferential.D ℂ (T i) (mk i (X j)))).trans (differential_polynomial (mk i) p).symm

private theorem toForms_fixed : toForms i (covector i (seedF i)) = 0 := by
  rw [toForms_covector, show mk i (seedF i) = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero]

/-- The determinant in the original coordinate order: the sextic equation,
the seed cubic, and the two chosen surface coordinates. -/
def jacobian (n t : P) : T i :=
  (basis₄ i).det (Fin.cons (covector i (seedF i)) ![covector i (seedH i), covector i n, covector i t])

/-- Exterior identity inside the fixed threefold, before restricting any coefficients to the surface. -/
theorem jacobian_smul_chartVolume (n t : P) :
    jacobian i n t • chartVolume i =
      exteriorPower.ιMulti (T i) 3 ![KaehlerDifferential.D ℂ (T i) (cubicOnT i),
        KaehlerDifferential.D ℂ (T i) (mk i n), KaehlerDifferential.D ℂ (T i) (mk i t)] := by
  let b := basis₄ i
  let u := ![covector i (seedH i), covector i n, covector i t]
  let v := exteriorPower.ιMulti (T i) 3 (toForms i ∘ u)
  have he : exteriorDifferentialMap (AlgHom.id ℂ (T i)) 3 (chartVolume i) = chartVolume i :=
    exteriorMap_identity (AlgHom.id ℂ (T i)).toRingHom
      (differentialSemilinearMap (AlgHom.id ℂ (T i))) (fun _ => rfl) (fun x => differentialMap_id x) 3 (chartVolume i)
  have h (j : Fin 4) : gradient i j • v = gradient i j • (jacobian i n t • chartVolume i) := by
    have hh := wedge_conormal_det b j (toForms i) _ (toForms_fixed i) u
    have hg := gradient_smul_chartVolume i (AlgHom.id ℂ (T i)) j
    rw [he] at hg
    simp only [b, Basis.coord_apply, Pi.basisFun_repr] at hh
    change gradient i j • v = jacobian i n t • signedOmitted (T i) (toForms i ∘ b) j at hh
    have hcoord : toForms i ∘ b = coordinateForm i (AlgHom.id ℂ (T i)) := funext (toForms_basis i)
    rw [hcoord, ← hg] at hh
    exact hh.trans (smul_comm (jacobian i n t) (gradient i j) (chartVolume i))
  obtain ⟨c, hc⟩ := chartBezout i
  have hw : v = jacobian i n t • chartVolume i := by
    calc
      v = (∑ j, c j * gradient i j) • v := by rw [hc, one_smul]
      _ = (∑ j, c j * gradient i j) • (jacobian i n t • chartVolume i) := by
        simp only [Finset.sum_smul, mul_smul, h]
      _ = _ := by rw [hc, one_smul]
  have hp : toForms i ∘ u = ![KaehlerDifferential.D ℂ (T i) (cubicOnT i),
      KaehlerDifferential.D ℂ (T i) (mk i n), KaehlerDifferential.D ℂ (T i) (mk i t)] := by
    funext j
    fin_cases j <;> exact toForms_covector i _
  exact hw.symm.trans (congrArg (exteriorPower.ιMulti (T i) 3) hp)

section Evaluation

variable {Q S : Type} [CommRing Q] [CommRing S] [Algebra ℂ Q] [Algebra ℂ S] [Algebra Q S] [IsScalarTower ℂ Q S]

private def vectors {d : ℕ} (v : Fin d → Derivation ℂ Q S) :
    KaehlerDifferential ℂ Q →ₛₗ[algebraMap Q S] (Fin d → S) where
  toFun ω j := (v j).liftKaehlerDifferential ω
  map_add' x y := funext fun j => (v j).liftKaehlerDifferential.map_add x y
  map_smul' r x := funext fun j => ((v j).liftKaehlerDifferential.map_smul r x).trans (Algebra.smul_def _ _)

/-- Evaluate an actual exterior differential on an ordered family of vectors along a ring map. -/
def evaluate {d : ℕ} (v : Fin d → Derivation ℂ Q S) :
    (⋀[Q]^d (KaehlerDifferential ℂ Q)) →ₛₗ[algebraMap Q S] S :=
  (topCoordinate (Pi.basisFun S (Fin d))).comp (exteriorMap (algebraMap Q S) (vectors v) d)

theorem evaluate_wedge {d : ℕ} (v : Fin d → Derivation ℂ Q S) (α : Fin d → KaehlerDifferential ℂ Q) :
    evaluate v (exteriorPower.ιMulti Q d α) =
      Matrix.det (Matrix.of fun a b => (v b).liftKaehlerDifferential (α a)) := by
  simp only [evaluate, LinearMap.comp_apply, exteriorMap_wedge, topCoordinate_wedge, ← Basis.det_apply,
    Pi.basisFun_det_apply]
  rfl

theorem evaluate_differentials {d : ℕ} (v : Fin d → Derivation ℂ Q S) (p : Fin d → Q) :
    evaluate v (exteriorPower.ιMulti Q d (fun a => KaehlerDifferential.D ℂ Q (p a))) =
      Matrix.det (Matrix.of fun a b => v b (p a)) := by
  simp only [evaluate_wedge, Derivation.liftKaehlerDifferential_comp_D]

theorem evaluate_swap (v x y : Derivation ℂ Q S) (ω : ⋀[Q]^3 (KaehlerDifferential ℂ Q)) :
    evaluate ![x,v,y] ω = -evaluate ![v,x,y] ω := by
  have hω : ω ∈ Submodule.span Q (Set.range (exteriorPower.ιMulti Q 3)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨α,rfl⟩ := hz
    simp only [evaluate_wedge, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  | zero => simp only [map_zero, neg_zero]
  | add z w _ _ hz hw => simp only [map_add, hz, hw, neg_add]
  | smul r z _ hz => simp only [map_smulₛₗ, hz, smul_neg]

theorem evaluate_two (x y : Derivation ℂ Q S) (n a : Q) :
    evaluate ![x,y] (exteriorPower.ιMulti Q 2 ![KaehlerDifferential.D ℂ Q n, KaehlerDifferential.D ℂ Q a]) =
      x n * y a - y n * x a := by
  have he := evaluate_differentials ![x,y] (![n,a] : Fin 2 → Q)
  have hf : (fun j : Fin 2 => KaehlerDifferential.D ℂ Q (![n,a] j)) =
      ![KaehlerDifferential.D ℂ Q n, KaehlerDifferential.D ℂ Q a] := by
    funext j; fin_cases j <;> rfl
  rw [hf] at he
  simpa only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using he

theorem evaluate_conormal_three (v x y : Derivation ℂ Q S) (h n a : Q)
    (hx : x h = 0) (hy : y h = 0) :
    evaluate ![v,x,y] (exteriorPower.ιMulti Q 3
      ![KaehlerDifferential.D ℂ Q h, KaehlerDifferential.D ℂ Q n, KaehlerDifferential.D ℂ Q a]) =
      v h * (x n * y a - y n * x a) := by
  have he := evaluate_differentials ![v,x,y] (![h,n,a] : Fin 3 → Q)
  have hf : (fun j : Fin 3 => KaehlerDifferential.D ℂ Q (![h,n,a] j)) =
      ![KaehlerDifferential.D ℂ Q h, KaehlerDifferential.D ℂ Q n, KaehlerDifferential.D ℂ Q a] := by
    funext j; fin_cases j <;> rfl
  rw [hf] at he
  refine he.trans ?_
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hx, hy]
  ring

end Evaluation

section Threefold

variable {S : Type} [CommRing S] [Algebra ℂ S] [Algebra (T i) S] [IsScalarTower ℂ (T i) S]

/-- Only the value on the cubic is retained when the other two vectors are tangent to the surface. -/
theorem tangent_evaluation (v x y : Derivation ℂ (T i) S) (n a : P)
    (hx : x (cubicOnT i) = 0) (hy : y (cubicOnT i) = 0) :
    algebraMap (T i) S (jacobian i n a) * evaluate ![v,x,y] (chartVolume i) =
      v (cubicOnT i) * (x (mk i n) * y (mk i a) - y (mk i n) * x (mk i a)) := by
  have hw := congrArg (evaluate ![v,x,y]) (jacobian_smul_chartVolume i n a)
  rw [map_smulₛₗ, smul_eq_mul, evaluate_conormal_three _ _ _ _ _ _ hx hy] at hw
  exact hw

end Threefold

end CycleQ2LiteralThreefoldSurfaceAdjunction
end

#print axioms CycleQ2LiteralThreefoldSurfaceAdjunction.jacobian_smul_chartVolume
#print axioms CycleQ2LiteralThreefoldSurfaceAdjunction.evaluate_differentials
