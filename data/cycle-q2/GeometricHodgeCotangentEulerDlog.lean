import Proposal.GeometricHodgeCotangentSectionFrames

/-!
# The actual Euler lift difference is the hyperplane logarithmic form

A local lift of an O(0) section occupies only the chosen weight-one
slot. The difference of two such lifts is a section of the actual
Euler kernel. Its image under the original global cotangent map is
the chart coefficient times dlog(X_k/X_i) on every common subopen.
The comparison of its derived class with the connecting map is separate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentEulerDlog
open AlgebraicGeometry CategoryTheory Limits Opposite
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricIncidenceProj
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2HodgeCotangentEulerSheaf
open CycleQ2HodgeCotangentAtlasForms (complexOn Form nativeForm coordinate localForm_eq_toSheaf)
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)
open CycleQ2GeometricProjectiveCurve.Twisted (res)
open CycleQ2SeedSectionSheafLimits
open CycleQ2HodgeCotangentGlobalMap (toCotangent toCotangent_on_subopen)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricSectionDifferentials (toSheaf)
attribute [local instance] complexOn
variable (φ : CoeffRing →+* ℂ)

def lift (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (s : Γ(twist φ 0,V)) : Γ(raw φ,V) :=
  (sectionProductEquiv (pieces φ) V).symm
    (fun j => (chartFrame φ _ i V hi).symm
      (if j = i.castSucc then chartFrame φ 0 i V hi s else 0))

theorem lift_frame (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (s : Γ(twist φ 0,V)) (j : Fin 5) :
    chartFrame φ (-(geometricWeight j : ℤ)) i V hi ((Pi.π (pieces φ) j).app V (lift φ i V hi s)) =
      if j = i.castSucc then chartFrame φ 0 i V hi s else 0 := by
  simp only [lift,sectionProductEquiv_symm_apply,LinearEquiv.apply_symm_apply]

theorem lift_euler (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (s : Γ(twist φ 0,V)) : (eulerMap φ).app V (lift φ i V hi s) = s := by
  classical
  apply (chartFrame φ 0 i V hi).injective
  rw [euler_frame]
  simp_rw [lift_frame]
  rw [Finset.sum_eq_single i.castSucc]
  · rw [if_pos rfl,CycleQ2HodgeCotangentEulerExact.normalized_radial_self,one_mul]
  · intro j _ hj
    rw [if_neg hj,mul_zero]
  · simp

theorem lift_otherFrame (i k : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (hk : V ≤ U φ k)
    (s : Γ(twist φ 0,V)) (j : Fin 5) :
    chartFrame φ (-(geometricWeight j : ℤ)) i V hi ((Pi.π (pieces φ) j).app V (lift φ k V hk s)) =
      if j = k.castSucc then ((transition φ i k V hi hk)⁻¹ : Γ(threefold φ,V)ˣ).val *
        chartFrame φ 0 i V hi s else 0 := by
  classical
  rw [chartFrame_transition φ (-(geometricWeight j : ℤ)) i k V hi hk,lift_frame]
  by_cases hj : j = k.castSucc
  · subst j
    rw [if_pos rfl,if_pos rfl]
    have hs := chartFrame_transition φ 0 i k V hi hk s
    simp only [zpow_zero,Units.val_one,one_mul] at hs
    rw [← hs]
    simp only [CycleQ2SeedFermatProj.geometricWeight_castSucc,Nat.cast_one,zpow_neg_one]
  · rw [if_neg hj,if_neg hj,mul_zero]

def edge (i k : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (hk : V ≤ U φ k)
    (s : Γ(twist φ 0,V)) : Γ(ambient φ,V) :=
  (sectionKernelEquiv (eulerMap φ) V).symm
    ⟨lift φ k V hk s - lift φ i V hi s,by
      change (eulerMap φ).app V (lift φ k V hk s - lift φ i V hi s) = 0
      rw [map_sub,lift_euler,lift_euler,sub_self]⟩

theorem edge_ι (i k : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (hk : V ≤ U φ k)
    (s : Γ(twist φ 0,V)) :
    (kernel.ι (eulerMap φ)).app V (edge φ i k V hi hk s) = lift φ k V hk s - lift φ i V hi s :=
  sectionKernelEquiv_symm_val _ _ _

theorem frame_restrict (n : ℤ) (i : Fin 4) {V W : (threefold φ).Opens}
    (hi : V ≤ U φ i) (hW : W ≤ V) (s : Γ(twist φ n,V)) :
    chartFrame φ n i W (hW.trans hi) (moduleRes (twist φ n) hW s) =
      res (threefold φ).sheaf hW (chartFrame φ n i V hi s) :=
  CycleQ2HodgeAtlasLine.coordinate_restrict (cocycle φ n) i hi hW s

theorem lift_restrict (i : Fin 4) {V W : (threefold φ).Opens}
    (hi : V ≤ U φ i) (hW : W ≤ V) (s : Γ(twist φ 0,V)) :
    moduleRes (raw φ) hW (lift φ i V hi s) =
      lift φ i W (hW.trans hi) (moduleRes (twist φ 0) hW s) := by
  apply (sectionProductEquiv (pieces φ) W).injective
  funext j
  rw [sectionProductEquiv_apply,sectionProductEquiv_apply]
  apply (chartFrame φ (-(geometricWeight j : ℤ)) i W (hW.trans hi)).injective
  rw [← moduleRes_app,frame_restrict,lift_frame,lift_frame]
  by_cases hj : j = i.castSucc
  · rw [if_pos hj,if_pos hj]
    exact (frame_restrict φ 0 i hi hW s).symm
  · rw [if_neg hj,if_neg hj,map_zero]

theorem edge_restrict (i k : Fin 4) {V W : (threefold φ).Opens}
    (hi : V ≤ U φ i) (hk : V ≤ U φ k) (hW : W ≤ V) (s : Γ(twist φ 0,V)) :
    moduleRes (ambient φ) hW (edge φ i k V hi hk s) =
      edge φ i k W (hW.trans hi) (hW.trans hk) (moduleRes (twist φ 0) hW s) := by
  apply (sectionKernelEquiv (eulerMap φ) W).injective
  apply Subtype.ext
  rw [sectionKernelEquiv_val,sectionKernelEquiv_val,← moduleRes_app,edge_ι,
    map_sub,lift_restrict,lift_restrict,edge_ι]

def rawForm (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (a : Γ(raw φ,V)) : Form φ V :=
  ∑ j : Fin 5, chartFrame φ (-(geometricWeight j : ℤ)) i V hi ((Pi.π (pieces φ) j).app V a) •
    KaehlerDifferential.D ℂ Γ(threefold φ,V) (coordinate φ i V hi j)

def logarithmic (i k : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (hk : V ≤ U φ k) : Form φ V :=
  ((transition φ i k V hi hk)⁻¹ : Γ(threefold φ,V)ˣ).val •
    KaehlerDifferential.D ℂ Γ(threefold φ,V) (transition φ i k V hi hk : Γ(threefold φ,V))

theorem rawForm_lift (i k : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (hk : V ≤ U φ k)
    (s : Γ(twist φ 0,V)) :
    rawForm φ i V hi (lift φ k V hk s) = chartFrame φ 0 i V hi s • logarithmic φ i k V hi hk := by
  classical
  unfold rawForm
  simp_rw [lift_otherFrame]
  rw [Finset.sum_eq_single k.castSucc]
  · rw [if_pos rfl]
    have hcoord : coordinate φ i V hi k.castSucc = (transition φ i k V hi hk : Γ(threefold φ,V)) := by
      simp only [coordinate,CycleQ2SeedFermatProj.geometricWeight_castSucc,transition,ratio,x]
    rw [hcoord]
    change (((transition φ i k V hi hk)⁻¹ : Γ(threefold φ,V)ˣ).val * chartFrame φ 0 i V hi s) •
      KaehlerDifferential.D ℂ Γ(threefold φ,V) (transition φ i k V hi hk : Γ(threefold φ,V)) = _
    rw [mul_comm,mul_smul]
    rfl
  · intro j _ hj
    rw [if_neg hj,zero_smul]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem nativeForm_edge (i k : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (hk : V ≤ U φ k)
    (s : Γ(twist φ 0,V)) :
    nativeForm φ i V hi (edge φ i k V hi hk s) = chartFrame φ 0 i V hi s • logarithmic φ i k V hi hk := by
  have he : nativeForm φ i V hi (edge φ i k V hi hk s) =
      rawForm φ i V hi (lift φ k V hk s) - rawForm φ i V hi (lift φ i V hi s) := by
    unfold nativeForm rawForm CycleQ2HodgeCotangentEulerSheaf.coefficient pieceMap
    change (∑ j : Fin 5, chartFrame φ (-(geometricWeight j : ℤ)) i V hi ((Pi.π (pieces φ) j).app V
      ((kernel.ι (eulerMap φ)).app V (edge φ i k V hi hk s))) •
        KaehlerDifferential.D ℂ Γ(threefold φ,V) (coordinate φ i V hi j)) = _
    rw [edge_ι]
    simp only [map_sub,sub_smul,Finset.sum_sub_distrib]
  rw [he,rawForm_lift,rawForm_lift]
  have hz : logarithmic φ i i V hi hi = 0 := by
    unfold logarithmic
    rw [transition_self]
    simp only [Units.val_one,inv_one,Derivation.map_one_eq_zero,smul_zero]
  rw [hz,smul_zero,sub_zero]

/-- The global cotangent map takes the actual local Euler lift difference
exactly to the scalar multiple of the ordinary hyperplane dlog form. -/
theorem globalMap_edge (h : IsUnit (φ vertexCoefficient)) (i k : Fin 4) (V : (threefold φ).Opens)
    (hi : V ≤ U φ i) (hk : V ≤ U φ k) (s : Γ(twist φ 0,V)) :
    (toCotangent φ h).app V (edge φ i k V hi hk s) =
      toSheaf (threefold φ).sheaf (schemeCoefficient (toBase φ)) V
        (chartFrame φ 0 i V hi s • logarithmic φ i k V hi hk) := by
  rw [toCotangent_on_subopen φ h i V hi,localForm_eq_toSheaf,nativeForm_edge]

end CycleQ2HodgeCotangentEulerDlog
end
#print axioms CycleQ2HodgeCotangentEulerDlog.lift_euler
#print axioms CycleQ2HodgeCotangentEulerDlog.nativeForm_edge
#print axioms CycleQ2HodgeCotangentEulerDlog.globalMap_edge
