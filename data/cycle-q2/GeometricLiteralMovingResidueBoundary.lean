import Proposal.GeometricLiteralMovingResidueFaces
import Proposal.GeometricLiteralMovingResiduePole
import Proposal.GeometricLiteralMovingDivisorChern

/-!
# Simple-pole lifts on the moving divisor's pivot cover

The second-vertex lift of a differential edge cocycle takes values in
the internal Hom from the actual moving curve ideal to the canonical sheaf.
Its boundary on every triple intersection is the regular inclusion of the
positive divisor transition wedged with the first edge.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingResidueBoundary

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricExteriorSheaf
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralMovingResidueFaces
  CycleQ2LiteralMovingResiduePole CycleQ2LiteralMovingDivisorChern
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionSheafKernel CycleQ2SeedSectionSheafCurveBinding
  CycleQ2GeometricIntrinsicCartierSequence CycleQ2LocalHomFrame CycleQ2FiniteInjectiveCech
  CycleQ2InjectiveCech CycleQ2FiniteCechDescent CycleQ2LiteralNativeChernCocycle

open CycleQ2CanonicalResidueSheaf (CanonicalForms)

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

def lift {W : Surface.Opens} (j : FrameData W) (β : OneForms W) :
    (PoleForms t).val.obj (op W) :=
  poleOfNumerator t ht j (poleNumerator t j β)

theorem frameEquation_restrict {W V : Surface.Opens} (j : FrameData W) (h : V ≤ W) :
    Surface.presheaf.map (homOfLE h).op (frameEquation t j) = frameEquation t (j.restrict h) :=
  sectionRows_restrict t j.chart W V h j.within j.pivot.1

theorem poleNumerator_restrict {W V : Surface.Opens} (j : FrameData W) (h : V ≤ W)
    (β : OneForms W) :
    CanonicalForms.val.map (homOfLE h).op (poleNumerator t j β) =
      poleNumerator t (j.restrict h) (DifferentialSheaf.val.map (homOfLE h).op β) := by
  unfold poleNumerator
  refine (wedgeSection_restrict Surface.sheaf DifferentialSheaf.val 2 (homOfLE h)
    ![equationDifferential W (frameEquation t j), β]).trans ?_
  apply congrArg (wedgeSection Surface.sheaf DifferentialSheaf.val 2 V)
  funext i
  fin_cases i
  · change DifferentialSheaf.val.map (homOfLE h).op (equationDifferential W (frameEquation t j)) =
      equationDifferential V (frameEquation t (j.restrict h))
    exact ((universalDifferential Surface.sheaf globalCoefficient).d_map (homOfLE h).op _).symm.trans
      (congrArg (equationDifferential V) (frameEquation_restrict t j h))
  · rfl

theorem lift_restrict {W V : Surface.Opens} (j : FrameData W) (h : V ≤ W)
    (β : OneForms W) :
    (PoleForms t).val.map (homOfLE h).op (lift t ht j β) =
      lift t ht (j.restrict h) (DifferentialSheaf.val.map (homOfLE h).op β) := by
  unfold lift
  rw [poleOfNumerator_restrict]
  congr 1
  exact poleNumerator_restrict t j h β

/-- Equality of actual Hom-sheaf sections, before quotienting by regular forms. -/
theorem lift_boundary {W : Surface.Opens} (j k : FrameData W)
    (bᵢⱼ bⱼₖ bᵢₖ : OneForms W) (hb : bᵢₖ = bᵢⱼ + bⱼₖ) :
    lift t ht k bⱼₖ - lift t ht k bᵢₖ + lift t ht j bᵢⱼ =
      (idealRegularInclusion (curveToSurface t) CanonicalForms).val.app (op W)
        (wedgeSection Surface.sheaf DifferentialSheaf.val 2 W
          ![sheafLogDifferential W (positiveTransition j k), bᵢⱼ]) := by
  unfold lift
  rw [pole_change_frame t ht j k, regular_eq_poleOfNumerator t ht k]
  change poleMap t ht k _ - poleMap t ht k _ + poleMap t ht k _ = poleMap t ht k _
  rw [← map_sub, ← map_add]
  apply congrArg (poleMap t ht k)
  have h := poleNumerator_boundary t j k bᵢⱼ bⱼₖ bᵢₖ hb
  rw [show (positiveTransition j k)⁻¹ = divisorTransition j k from inv_inv _] at h
  exact h

abbrev poleSheaf := (SheafOfModules.toSheaf (ringSheaf Surface.sheaf)).obj (PoleForms t)

def poleOne (b : One differentialAddSheaf pivotCover) : One (poleSheaf t) pivotCover :=
  fun i j => lift t ht (frameAt j _ inf_le_right) (b i j)

private theorem frame_eq {W : Surface.Opens} (f g : FrameData W)
    (hc : f.chart = g.chart) (hp : f.pivot = g.pivot) : f = g := by
  rcases f with ⟨i, hi, p, u, hu⟩
  rcases g with ⟨i', hi', p', u', hu'⟩
  dsimp at hc hp
  subst i'
  subst p'
  have he : u = u' := Units.ext (hu.trans hu'.symm)
  subst u'
  rfl

theorem poleOne_common (b : One differentialAddSheaf pivotCover) (i j : VertexIndex)
    (W : Surface.Opens) (hi : W ≤ pivotCover i) (hj : W ≤ pivotCover j) :
    edgeValue (poleSheaf t) pivotCover (poleOne t ht b) i j W hi hj =
      lift t ht (frameAt j W hj) (edgeValue differentialAddSheaf pivotCover b i j W hi hj) := by
  change (PoleForms t).val.map (homOfLE (le_inf hi hj)).op _ = _
  refine (lift_restrict t ht (frameAt j (pivotCover i ⊓ pivotCover j) inf_le_right)
    (le_inf hi hj) (b i j)).trans ?_
  have he : (frameAt j (pivotCover i ⊓ pivotCover j) inf_le_right).restrict (le_inf hi hj) =
      frameAt j W hj := frame_eq _ _ rfl rfl
  rw [he]
  rfl

/-- The pole lift of any differential cocycle on the actual pivot cover has this
regular boundary on every common subopen. -/
theorem poleOne_boundary (b : One differentialAddSheaf pivotCover)
    (hb : IsOneCocycle differentialAddSheaf pivotCover b)
    (i j k : VertexIndex) (W : Surface.Opens)
    (hi : W ≤ pivotCover i) (hj : W ≤ pivotCover j) (hk : W ≤ pivotCover k) :
    boundaryValue (poleSheaf t) pivotCover (poleOne t ht b) i j k W hi hj hk =
      (idealRegularInclusion (curveToSurface t) CanonicalForms).val.app (op W)
        (wedgeSection Surface.sheaf DifferentialSheaf.val 2 W
          ![sheafLogDifferential W (positiveTransition (frameAt j W hj) (frameAt k W hk)),
            edgeValue differentialAddSheaf pivotCover b i j W hi hj]) := by
  unfold boundaryValue
  rw [poleOne_common, poleOne_common, poleOne_common]
  exact lift_boundary t ht _ _ _ _ _ (hb i j k W hi hj hk)

end CycleQ2LiteralMovingResidueBoundary
end

#print axioms CycleQ2LiteralMovingResidueBoundary.poleOne_boundary
