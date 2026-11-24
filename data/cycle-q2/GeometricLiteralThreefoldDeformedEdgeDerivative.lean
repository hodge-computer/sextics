import Proposal.GeometricLiteralThreefoldDeformedCocycle
import Proposal.GeometricLiteralThreefoldChartVolumeFrame
import Proposal.GeometricLiteralThreefoldDeformedOverlap
import Proposal.GeometricLiteralThreefoldCartanLift
import Proposal.GeometricLiteralThreefoldTestEdges
import Proposal.GeometricLiteralThreefoldExteriorDerivative

/-!
# The derivative of the native edge on the entire affine chart intersection

The regular chart residue generates all three-forms on the overlap. Its
coefficient can be read on the sixteen principal opens where both chart
gradients have a unit component.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldDeformedEdgeDerivative

open Module CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldChartVolume CycleQ2LiteralThreefoldChartVolumeFrame
  CycleQ2LiteralThreefoldCartan CycleQ2LiteralThreefoldCartanLift
  CycleQ2LiteralThreefoldDeformedOverlap CycleQ2LiteralThreefoldOverlapLocalization
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldExteriorDerivative
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueMinors
  CycleQ2ExteriorSectionNaturality CycleQ2ExteriorTopBaseChange
  CycleQ2GeometricAffineOverlap CycleQ2GeometricExteriorSheaf

private theorem exterior_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C)
    (w : Forms A 3) :
    exteriorDifferentialMap g 3 (exteriorDifferentialMap f 3 w) =
      exteriorDifferentialMap (g.comp f) 3 w :=
  (exteriorMap_composition f.toRingHom g.toRingHom (g.comp f).toRingHom
    (differentialSemilinearMap f) (differentialSemilinearMap g)
    (differentialSemilinearMap (g.comp f)) (fun _ => rfl)
    (fun z => (differentialMap_comp f g z).symm) 3 w).symm

/-- The affine residue still generates all three-forms after localization.
The triples of differentials of unlocalized functions suffice to test generation. -/
theorem localized_volume_surjective (i : Fin 4) {A : Type} [CommRing A] [Algebra ℂ A]
    [Algebra (T i) A] [IsScalarTower ℂ (T i) A] (m : Submonoid (T i)) [IsLocalization m A] :
    Function.Surjective (fun c : A => c • exteriorDifferentialMap
      (IsScalarTower.toAlgHom ℂ (T i) A) 3 (chartVolume i)) := by
  let f := IsScalarTower.toAlgHom ℂ (T i) A
  let v := exteriorDifferentialMap f 3 (chartVolume i)
  let L := LinearMap.toSpanSingleton A (Forms A 3) v
  let D := KaehlerDifferential.map ℂ ℂ (T i) A ∘ KaehlerDifferential.D ℂ (T i)
  have hs : Submodule.span A (Set.range D) = ⊤ :=
    KaehlerDifferential.span_range_map_derivation_of_isLocalization ℂ (T i) A m
  have ht := exteriorPower.ιMulti_span_of_span A 3 (KaehlerDifferential ℂ A) hs
  have hle : Submodule.span A (exteriorPower.ιMulti A 3 ''
      {w : Fin 3 → KaehlerDifferential ℂ A | Set.range w ⊆ Set.range D}) ≤ L.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    choose p hp using fun j : Fin 3 => hw (Set.mem_range_self j)
    let t := fun j => KaehlerDifferential.D ℂ (T i) (p j)
    obtain ⟨c, hc⟩ := (chartVolume_bijective i).surjective (exteriorPower.ιMulti (T i) 3 t)
    change c • chartVolume i = _ at hc
    refine ⟨f c, ?_⟩
    change f c • exteriorDifferentialMap f 3 (chartVolume i) = _
    rw [← map_smulₛₗ, hc, exteriorDifferentialMap_wedge]
    apply congrArg (exteriorPower.ιMulti A 3)
    funext j
    rw [show t j = KaehlerDifferential.D ℂ (T i) (p j) from rfl, differentialMap_D]
    simpa only [D, f, IsScalarTower.toAlgHom_apply, Function.comp_apply, KaehlerDifferential.map_D] using hp j
  exact LinearMap.range_eq_top.mp (top_le_iff.mp (ht ▸ hle) : L.range = ⊤)

private theorem detect_scalars {A I : Type} [CommRing A] (s : I → A)
    (hs : ∀ p : PrimeSpectrum A, ∃ i, s i ∉ p.asIdeal) {x y : A}
    (h : ∀ i, algebraMap A (Localization.Away (s i)) x =
              algebraMap A (Localization.Away (s i)) y) : x = y := by
  have htop : Ideal.span (Set.range s) = ⊤ := by
    by_contra hn
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ hn
    obtain ⟨i, hi⟩ := hs ⟨p, hp.isPrime⟩
    exact hi (hle (Ideal.subset_span (Set.mem_range_self i)))
  apply Localization.algebraMap_injective_of_span_eq_top _ htop
  funext r
  obtain ⟨_, i, rfl⟩ := r
  simpa only [Pi.algebraMap_apply] using h i

/-- On a single native affine chart, equality on its four Jacobian opens detects
equality of global three-forms. -/
theorem chart_restrictions_injective (i : Fin 4) {x y : Forms (T i) 3}
    (h : ∀ a : Fin 4, exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ (T i) (Patch i a)) 3 x =
      exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ (T i) (Patch i a)) 3 y) : x = y := by
  obtain ⟨c, rfl⟩ := (chartVolume_bijective i).surjective x
  obtain ⟨d, rfl⟩ := (chartVolume_bijective i).surjective y
  refine congrArg (fun r : T i => r • chartVolume i) ?_
  obtain ⟨t, ht⟩ := chartBezout i
  have htop : Ideal.span (Set.range (gradient i)) = ⊤ :=
    (Ideal.eq_top_iff_one _).mpr (Ideal.mem_span_range_iff_exists_fun.mpr ⟨t, ht⟩)
  apply Localization.algebraMap_injective_of_span_eq_top _ htop
  funext r
  obtain ⟨_, a, rfl⟩ := r
  simp only [Pi.algebraMap_apply]
  have hh := h a
  simp only [map_smulₛₗ, chartVolume_on_patch] at hh
  exact ((Function.bijective_iff_existsUnique _).mpr (patchResidue_frame i a)).injective hh

private def overlapVolume (i : Fin 4) (k : Fin 3) :=
  exteriorDifferentialMap (fixedTargetMap i k) 3 (chartVolume (i.succAbove k))

private theorem overlap_generates (i : Fin 4) (k : Fin 3) :
    Function.Surjective (fun c : FixedOverlap i k => c • overlapVolume i k) := by
  let f := fixedTargetMap i k
  letI := f.toRingHom.toAlgebra
  letI : SMul (T (i.succAbove k)) (FixedOverlap i k) := f.toRingHom.toAlgebra.toSMul
  letI : Module (T (i.succAbove k)) (FixedOverlap i k) := f.toRingHom.toAlgebra.toModule
  letI : IsScalarTower ℂ (T (i.succAbove k)) (FixedOverlap i k) := IsScalarTower.of_algHom f
  letI : IsLocalization.Away (sourceAxis i k) (FixedOverlap i k) := fixedTargetMap_isLocalization i k
  exact localized_volume_surjective (i.succAbove k) (Submonoid.powers (sourceAxis i k))

private theorem volume_basis {j : Fin 4} {A : Type} [CommRing A] [Algebra ℂ A]
    (f : T j →ₐ[ℂ] A) (b : Fin 4) (h : IsUnit (f (gradient j b)))
    (B : Basis (Fin 3) A (OneForms A))
    (hb : ∀ r, B r = KaehlerDifferential.D ℂ A (f (coord j (b.succAbove r)))) :
    exteriorDifferentialMap f 3 (chartVolume j) =
      ((↑h.unit⁻¹ : A) * (-1 : A)^b.val) • orderedVolume B := by
  rw [chartVolume_eq_residue j f b h, residue, signedOmitted, mul_smul]
  congr 2
  apply congrArg (exteriorPower.ιMulti A 3)
  funext r
  exact (hb r).symm

private theorem patch_detects_scalars (i : Fin 4) (k : Fin 3) (a b : Fin 4) :
    Function.Injective (fun c : Ring i k a b =>
      c • exteriorDifferentialMap (κ i k a b) 3 (overlapVolume i k)) := by
  let h := target_unit i k a b
  let B := basisOn i k a b
  let c : Ring i k a b := (↑h.unit⁻¹ : Ring i k a b) * (-1 : Ring i k a b)^b.val
  have hv : exteriorDifferentialMap (κ i k a b) 3 (overlapVolume i k) =
      c • orderedVolume B :=
    (exterior_comp (fixedTargetMap i k) (κ i k a b) (chartVolume (i.succAbove k))).trans
      (volume_basis (targetMap i k a b) b h B (basisOn_apply i k a b))
  have hu : IsUnit c := (h.unit⁻¹).isUnit.mul ((isUnit_neg_one (α := Ring i k a b)).pow b.val)
  intro x y hxy
  have he := congrArg (topCoordinate B) hxy
  apply hu.mul_right_cancel
  simpa only [hv, map_smul, orderedVolume, topCoordinate_basis, smul_eq_mul, mul_one] using he

private theorem semilinear_coefficients {A B M N : Type} [CommRing A] [CommRing B]
    [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
    (f : A →+* B) (L : M →ₛₗ[f] N) (v : M)
    (hi : Function.Injective (fun c : B => c • L v)) (x y : A)
    (h : L (x • v) = L (y • v)) : f x = f y :=
  hi ((map_smulₛₗ L x v).symm.trans (h.trans (map_smulₛₗ L y v)))

/-- The sixteen distinguished restrictions on the original chart overlap jointly
detect equality of all three-forms. -/
theorem triple_restrictions_injective (i : Fin 4) (k : Fin 3) {x y : Forms (FixedOverlap i k) 3}
    (h : ∀ a b : Fin 4, exteriorDifferentialMap (κ i k a b) 3 x =
      exteriorDifferentialMap (κ i k a b) 3 y) : x = y := by
  obtain ⟨c, rfl⟩ := overlap_generates i k x
  obtain ⟨d, rfl⟩ := overlap_generates i k y
  apply congrArg (fun r : FixedOverlap i k => r • overlapVolume i k)
  apply detect_scalars (fun ab : Fin 4 × Fin 4 => denominator i k ab.1 ab.2)
  · intro p
    obtain ⟨a, b, h⟩ := denominator_cover i k p
    exact ⟨(a,b),h⟩
  · rintro ⟨a,b⟩
    exact semilinear_coefficients (κ i k a b).toRingHom
      (exteriorDifferentialMap (κ i k a b) 3) (overlapVolume i k)
      (patch_detects_scalars i k a b) c d (h a b)


-- The native differential on the whole overlap.
open CycleQ2LiteralThreefoldDeformedCocycle

def edgeDerivative (i : Fin 4) (k : Fin 3) : Forms (FixedOverlap i k) 3 :=
  exteriorDifferentialMap (sourceMap i k) 3 (chartThreeForm i) -
    exteriorDifferentialMap (fixedTargetMap i k) 3 (chartThreeForm (i.succAbove k))

theorem edgeDerivative_restrict (i : Fin 4) (k : Fin 3) (a b : Fin 4) :
    exteriorDifferentialMap (κ i k a b) 3 (edgeDerivative i k) =
      exteriorD2 (basisOn i k a b) (exteriorDifferentialMap (κ i k a b) 2 (nativeEdge i k)) := by
  refine ((exteriorDifferentialMap (κ i k a b) 3).map_sub _ _).trans ?_
  exact (congrArg₂ (· - ·) (exterior_comp (sourceMap i k) (κ i k a b) (chartThreeForm i))
    (exterior_comp (fixedTargetMap i k) (κ i k a b) (chartThreeForm (i.succAbove k)))).trans
      (pair_patch i k a b)

/-- There is a unique three-form on the full overlap whose restrictions are the
exterior derivatives of the native edge in each local exact frame. -/
theorem existsUnique_edgeDerivative (i : Fin 4) (k : Fin 3) :
    ∃! z : Forms (FixedOverlap i k) 3, ∀ a b : Fin 4, exteriorDifferentialMap (κ i k a b) 3 z =
      exteriorD2 (basisOn i k a b) (exteriorDifferentialMap (κ i k a b) 2 (nativeEdge i k)) := by
  refine ⟨edgeDerivative i k, edgeDerivative_restrict i k, ?_⟩
  intro y hy
  exact triple_restrictions_injective i k (fun a b => (hy a b).trans (edgeDerivative_restrict i k a b).symm)

end CycleQ2LiteralThreefoldDeformedEdgeDerivative

#print axioms CycleQ2LiteralThreefoldDeformedEdgeDerivative.chart_restrictions_injective
#print axioms CycleQ2LiteralThreefoldDeformedEdgeDerivative.triple_restrictions_injective
#print axioms CycleQ2LiteralThreefoldDeformedEdgeDerivative.existsUnique_edgeDerivative
