import Proposal.GeometricLiteralAbelJacobiEvaluationChartTransport

/-!
# Restriction along the actual seed-to-time square

A section transported along equal scheme maps has the same value on
every common subopen. Composing the tangent-germ and seed restrictions
therefore computes the time-family evaluation even when its argument
is further restricted on the projective seed curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQEvaluationTransport

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralAbelJacobiEvaluationChartTransport

variable {X Y G : Scheme.{0}}

abbrev onSubopen (M : X.Modules) {O W : X.Opens} (h : W ≤ O) :=
  M.val.map (homOfLE h).op

theorem onSubopen_trans (M : X.Modules) {O P W : X.Opens} (h : W ≤ P) (k : P ≤ O)
    (x : M.val.obj (op O)) :
    onSubopen M h (onSubopen M k x) = onSubopen M (h.trans k) x :=
  (M.val.map_comp_apply (homOfLE k).op (homOfLE h).op x).symm

theorem onSubopen_congr {f g : X ⟶ Y} (e : f = g) (M : X.Modules) (U : Y.Opens) (W : X.Opens)
    (hf : W ≤ f ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ U) (x : M.val.obj (op (f ⁻¹ᵁ U))) :
    onSubopen M hg (((Scheme.Modules.pushforwardCongr e).hom.app M).val.app (op U) x) =
      onSubopen M hf x := by
  rw [pushforwardCongr_apply]
  unfold onSubopen
  rw [← PresheafOfModules.map_comp_apply]
  rfl

variable (r : X ⟶ G) (b : G ⟶ Y) (c : X ⟶ Y) (e : r ≫ b = c)
  {M : Y.Modules} {N : G.Modules} {P : X.Modules}
  (u : M ⟶ (Scheme.Modules.pushforward b).obj N)
  (v : N ⟶ (Scheme.Modules.pushforward r).obj P)

abbrev alongSquare : M ⟶ (Scheme.Modules.pushforward c).obj P :=
  u ≫ (Scheme.Modules.pushforward b).map v ≫
    (Scheme.Modules.pushforwardComp r b).hom.app P ≫
    (Scheme.Modules.pushforwardCongr e).hom.app P

/-- Restrict the first map to a genuine germ subopen before applying the
second, or restrict their composed map at the end. -/
theorem alongSquare_restrict (U : Y.Opens) (O : G.Opens) (hO : O ≤ b ⁻¹ᵁ U)
    (W : X.Opens) (hW : W ≤ r ⁻¹ᵁ O) (hWU : W ≤ c ⁻¹ᵁ U) (x : M.val.obj (op U)) :
    onSubopen P hWU ((alongSquare r b c e u v).val.app (op U) x) =
      onSubopen P hW (v.val.app (op O) (onSubopen N hO (u.val.app (op U) x))) := by
  let h := hW.trans (r.preimage_mono hO)
  refine (onSubopen_congr e P U W h hWU _).trans ?_
  have hnat := PresheafOfModules.naturality_apply v.val (homOfLE hO).op (u.val.app (op U) x)
  change v.val.app (op O) (onSubopen N hO (u.val.app (op U) x)) =
    onSubopen P (r.preimage_mono hO) (v.val.app (op (b ⁻¹ᵁ U)) (u.val.app (op U) x)) at hnat
  rw [hnat, onSubopen_trans]
  rfl

end CycleQ2LiteralAbelJacobiQEvaluationTransport
end

#print axioms CycleQ2LiteralAbelJacobiQEvaluationTransport.alongSquare_restrict
