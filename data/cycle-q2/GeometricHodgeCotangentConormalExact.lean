import Proposal.GeometricHodgeCotangentConormalLocal
import Proposal.GeometricHodgeThreefoldLiteralGradient

/-!
# The genuine conormal short exact sequence on the fixed smooth fiber

The original fixed-sextic Jacobian certificate makes the conormal map
injective in every chart frame. The principal affine section calculation
then proves short exactness of the actual global sheaf complex.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentConormalExact
open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2HodgeCotangentEulerSheaf (ambient conormalMap)
open CycleQ2HodgeCotangentSectionFrames (drop drop_conormal)
open CycleQ2HodgeCotangentConormalComplex (affineMap conormalSequence)
open CycleQ2HodgeCotangentGlobalMap (toCotangent)
open CycleQ2HodgeCotangentAffineSections (principal principal_le chart_isAffine)
open CycleQ2HodgeCotangentConormalLocal (principal_exact principal_surjective)

private theorem gradient_scalar_injective {A B : Type} [CommRing A] [CommRing B]
    (f : A →+* B) (g : Fin 4 → A) (hg : Ideal.span (Set.range g) = ⊤) :
    Function.Injective (fun c : B => c • (fun j : Fin 4 => f (g j))) := by
  have h1 : (1 : A) ∈ Ideal.span (Set.range g) := by rw [hg]; trivial
  obtain ⟨u,hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  have hf : (∑ j : Fin 4, f (u j) * f (g j)) = 1 := by
    simpa only [map_sum,map_mul,map_one] using congrArg f hu
  have hc (c : B) : (∑ j : Fin 4, f (u j) * (c * f (g j))) = c := by
    calc
      _ = c * (∑ j : Fin 4, f (u j) * f (g j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = c := by rw [hf,mul_one]
  intro c d h
  have he := congrArg (fun v : Fin 4 → B => ∑ j : Fin 4, f (u j) * v j) h
  change (∑ j : Fin 4, f (u j) * (c * f (g j))) =
    (∑ j : Fin 4, f (u j) * (d * f (g j))) at he
  rwa [hc,hc] at he

attribute [local instance] CycleQ2HodgeCotangentAtlasForms.complexOn

variable (φ : CoeffRing →+* ℂ)

theorem conormal_section_injective (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (hg : Ideal.span (Set.range (fun j : Fin 4 =>
      CycleQ2HodgeEuler.chartMap φ i (pderiv j (CycleQ2HodgeEuler.F φ i)))) = ⊤) :
    Function.Injective ((conormalMap φ).app V) := by
  intro s t hst
  apply (chartFrame φ (-6) i V hi).injective
  apply gradient_scalar_injective (affineMap φ i V hi).toRingHom _ hg
  funext j
  have he := congrFun (congrArg (drop φ i V hi) hst) j
  rw [drop_conormal,drop_conormal] at he
  change chartFrame φ (-6) i V hi s * affineMap φ i V hi _ =
    chartFrame φ (-6) i V hi t * affineMap φ i V hi _
  simpa only [mul_comm] using he

/-- The actual cotangent map is locally surjective on the original monic locus. -/
theorem cotangent_additive_epi (h : IsUnit (φ vertexCoefficient)) :
    Epi ((SheafOfModules.toSheaf (threefold φ).ringCatSheaf).map (toCotangent φ h)) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro V s x hx
  have hxc : x ∈ ⨆ i : Fin 4, U φ i := by rw [coordinateOpens_cover φ h]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hxc
  obtain ⟨r,hr,hxr⟩ := (chart_isAffine φ i).exists_basicOpen_le ⟨x,hx⟩ hi
  exact ⟨principal φ i r,hr,principal_surjective φ i h r _,hxr⟩

/-- The global sheaf complex is short exact whenever its original chart
Jacobian ideals are the unit ideal. -/
theorem conormal_shortExact_of_gradient (h : IsUnit (φ vertexCoefficient))
    (hg : ∀ i : Fin 4, Ideal.span (Set.range (fun j : Fin 4 =>
      CycleQ2HodgeEuler.chartMap φ i (pderiv j (CycleQ2HodgeEuler.F φ i)))) = ⊤) :
    (conormalSequence φ h).ShortExact := by
  apply CycleQ2GeometricSheafLocalExactness.moduleSheaf_shortExact_of_neighborhoods
    (threefold φ).ringCatSheaf (conormalSequence φ h)
  intro V x hx
  have hxc : x ∈ ⨆ i : Fin 4, U φ i := by rw [coordinateOpens_cover φ h]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hxc
  obtain ⟨r,hr,hxr⟩ := (chart_isAffine φ i).exists_basicOpen_le ⟨x,hx⟩ hi
  exact ⟨principal φ i r,hr,hxr,
    conormal_section_injective φ i _ (principal_le φ i r) (hg i),
    principal_exact φ i h r,principal_surjective φ i h r⟩

/-- No smoothness or exactness premise remains: the original fixed-fiber
Jacobian certificate supplies every hypothesis of the actual sequence. -/
theorem literal_conormal_shortExact :
    (conormalSequence literalEval literal_vertex_unit).ShortExact :=
  conormal_shortExact_of_gradient literalEval literal_vertex_unit literal_chartGradient_span

end CycleQ2HodgeCotangentConormalExact
end
#print axioms CycleQ2HodgeCotangentConormalExact.conormal_section_injective
#print axioms CycleQ2HodgeCotangentConormalExact.literal_conormal_shortExact
