import Proposal.GeometricLiteralAbelJacobiEvaluationAffine
import Proposal.GeometricExteriorPullComposition

/-!
# Evaluating the pullback of two exact differentials

On every open, restriction along a scheme morphism sends the wedge of
two exact differentials to the wedge of the corresponding restrictions.
A tangent on an affine chart then evaluates this wedge by its derivation
on the restricted functions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiEvaluationWedge

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricExteriorSheaf
  CycleQ2GeometricSchemeDifferentialMap CycleQ2ExteriorPullComposition
  CycleQ2LiteralAbelJacobiQPullback CycleQ2LiteralAbelJacobiEvaluationAffine
  CycleQ2GeometricAffineDifferentialSheaf

variable {X Y : Scheme.{0}}

abbrev exactWedge (X : Scheme.{0}) (c : ℂ →+* Γ(X,⊤)) (U : X.Opens)
    (a : Fin 2 → Γ(X,U)) :=
  wedgeSection X.sheaf (differentialSheaf X.sheaf c).val 2 U
    (fun p => (universalDifferential X.sheaf c).d (a p))

theorem pull_exactWedge (j : X ⟶ Y) (cX : ℂ →+* Γ(X,⊤)) (cY : ℂ →+* Γ(Y,⊤))
    (h : compatible j cX cY) (U : Y.Opens) (a : Fin 2 → Γ(Y,U)) :
    (schemeExteriorPull j cX cY h 2).val.app (op U) (exactWedge Y cY U a) =
      exactWedge X cX (j ⁻¹ᵁ U) (fun p => j.app U (a p)) := by
  unfold exactWedge wedgeSection
  rw [exteriorPull_section]
  apply congrArg (exteriorSection X.sheaf (differentialSheaf X.sheaf cX).val 2 (j ⁻¹ᵁ U))
  refine (exteriorMap_wedge (j.app U).hom (onSections j (schemeDifferentialMap j cX cY h) U) 2
    (fun p => (universalDifferential Y.sheaf cY).d (X := op U) (a p))).trans ?_
  apply congrArg (exteriorPower.ιMulti _ 2)
  funext p
  exact schemeDifferentialMap_D j cX cY h U (a p)

variable {B A : Type} [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A]
  [IsScalarTower ℂ B A]

set_option maxHeartbeats 750000 in
/-- The sign and both coefficient functions on an arbitrary chart subopen. -/
theorem evaluation_exactWedge (v : Derivation ℂ B A) (U : (Spec (CommRingCat.of B)).Opens)
    (a : Fin 2 → Γ(Spec (CommRingCat.of B),U)) :
    (evaluation v).val.app (op U) (exactWedge (Spec (CommRingCat.of B)) (affineCoefficient B) U a) =
      velocityOn v U (a 0) • (universalDifferential (Spec.structureSheaf A) (affineCoefficient A)).d
        ((reduction B A).app U (a 1)) -
      velocityOn v U (a 1) • (universalDifferential (Spec.structureSheaf A) (affineCoefficient A)).d
        ((reduction B A).app U (a 0)) := by
  let d := (affineUniversalDifferential B).d (X := op U)
  refine (evaluation_wedge v U (fun p => d (a p))).trans ?_
  have hd (p : Fin 2) :
      (pulledOne (B := B) (A := A)).val.app (op U) (d (a p)) =
        (affineUniversalDifferential A).d ((reduction B A).app U (a p)) :=
    schemeDifferentialMap_D (reduction B A) (affineCoefficient A) (affineCoefficient B)
      (CycleQ2GeometricAffineCotangentReduction.affineMap_coefficient (IsScalarTower.toAlgHom ℂ B A)) U (a p)
  exact congrArg₂ (· - ·)
    (congrArg (fun x : (affineDifferentialSheaf A).val.obj (op (reduction B A ⁻¹ᵁ U)) =>
      velocityOn v U (a 0) • x) (hd 1))
    (congrArg (fun x : (affineDifferentialSheaf A).val.obj (op (reduction B A ⁻¹ᵁ U)) =>
      velocityOn v U (a 1) • x) (hd 0))

end CycleQ2LiteralAbelJacobiEvaluationWedge
end

#print axioms CycleQ2LiteralAbelJacobiEvaluationWedge.pull_exactWedge
#print axioms CycleQ2LiteralAbelJacobiEvaluationWedge.evaluation_exactWedge
