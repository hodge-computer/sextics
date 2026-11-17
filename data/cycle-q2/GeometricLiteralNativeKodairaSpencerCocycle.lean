import Proposal.GeometricLiteralNativeTangentNaturality

/-!
# The actual native Kodaira--Spencer tangent-sheaf cocycle

The same original, faithfully normalized splitting differences now give
sections of the genuine internal Hom(Ω,O) sheaf. Compatibility of native
derivations under localization proves their actual sheaf restrictions.
Their additive cocycle therefore holds on every common subopen of the
original twelve-open cover.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeKodairaSpencerCocycle

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralNativeKodairaSpencer
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeTangentEvaluation
  CycleQ2LiteralNativeTangentNaturality CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeCupSectionValues

attribute [local instance] CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule

abbrev tangentAddSheaf := CycleQ2GeometricModuleLocalIso.addSheaf tangentSheaf

theorem evaluateTangent_add (U : Surface.Opens)
    (x y : tangentSheaf.val.obj (op U)) (ω : DifferentialSheaf.val.obj (op U)) :
    evaluateTangent U (x + y) ω = evaluateTangent U x ω + evaluateTangent U y ω := rfl

theorem nativeTangent_add (s : Finset Vertex) (hs : s.Nonempty)
    (δ η : Derivation ℂ (ClosedRing s) (ClosedRing s)) :
    nativeTangent s hs (δ + η) = nativeTangent s hs δ + nativeTangent s hs η := by
  apply nativeTangent_ext s hs
  intro a
  have hD (d : Derivation ℂ (ClosedRing s) (ClosedRing s)) :
      evaluateTangent (closedOpen s) (nativeTangent s hs d)
        (nativeFormToSheaf s hs (KaehlerDifferential.D ℂ (ClosedRing s) a)) =
        nativeSectionsAlgEquiv s hs (d a) :=
    (nativeTangent_on_form s hs d _).trans
      (congrArg (nativeSectionsAlgEquiv s hs) (d.liftKaehlerDifferential_comp_D a))
  rw [evaluateTangent_add, hD (δ + η), hD δ, hD η]
  exact map_add (nativeSectionsAlgEquiv s hs) (δ a) (η a)

theorem nativeKodairaSpencerSection_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    res tangentAddSheaf (closedOpen_mono hst) (nativeKodairaSpencerSection s hs u v hu hv) =
      nativeKodairaSpencerSection t ht u v (hst hu) (hst hv) :=
  nativeTangent_restrict hst hs ht (vertexKodairaSpencer s u v hu hv)
    (vertexKodairaSpencer t u v (hst hu) (hst hv))
    (kodairaSpencer_restrict hst u.1 v.1 ⟨u.2,hu⟩ ⟨v.2,hv⟩)

theorem nativeKodairaSpencerSection_cocycle (s : Finset Vertex) (hs : s.Nonempty) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    nativeKodairaSpencerSection s hs u w hu hw =
      nativeKodairaSpencerSection s hs u v hu hv + nativeKodairaSpencerSection s hs v w hv hw :=
  (congrArg (nativeTangent s hs) (vertexKodairaSpencer_cocycle s u v w hu hv hw)).trans
    (nativeTangent_add s hs _ _)

def kodairaSpencerValue (u v : Vertex) (W : Surface.Opens) (hu : W ≤ cover u) (hv : W ≤ cover v) :
    Sections tangentAddSheaf W :=
  res tangentAddSheaf (common_le_pair u v W hu hv)
    (nativeKodairaSpencerSection {u,v} (by simp) u v (by simp) (by simp))

theorem kodairaSpencerValue_restrict (u v : Vertex) {W V : Surface.Opens} (hVW : V ≤ W)
    (hu : W ≤ cover u) (hv : W ≤ cover v) :
    res tangentAddSheaf hVW (kodairaSpencerValue u v W hu hv) =
      kodairaSpencerValue u v V (hVW.trans hu) (hVW.trans hv) := res_comp tangentAddSheaf _ _ _

theorem kodairaSpencerValue_common (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (W : Surface.Opens) (hW : W ≤ closedOpen s)
    (hU : W ≤ cover u) (hV : W ≤ cover v) :
    kodairaSpencerValue u v W hU hV =
      res tangentAddSheaf hW (nativeKodairaSpencerSection s hs u v hu hv) := by
  have hpair : ({u,v} : Finset Vertex) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hu
    · exact hv
  rw [← nativeKodairaSpencerSection_restrict hpair (by simp) hs u v (by simp) (by simp)]
  exact (res_comp tangentAddSheaf _ _ _).symm

def kodairaSpencerOne : One tangentAddSheaf cover := fun u v =>
  kodairaSpencerValue u v (cover u ⊓ cover v) inf_le_left inf_le_right

theorem edgeValue_kodairaSpencerOne (u v : Vertex) (W : Surface.Opens)
    (hu : W ≤ cover u) (hv : W ≤ cover v) :
    edgeValue tangentAddSheaf cover kodairaSpencerOne u v W hu hv = kodairaSpencerValue u v W hu hv :=
  kodairaSpencerValue_restrict u v (le_inf hu hv) inf_le_left inf_le_right

theorem kodairaSpencerOne_closed : IsOneCocycle tangentAddSheaf cover kodairaSpencerOne := by
  intro u v w W hu hv hw
  change edgeValue tangentAddSheaf cover kodairaSpencerOne u w W hu hw =
    edgeValue tangentAddSheaf cover kodairaSpencerOne u v W hu hv +
      edgeValue tangentAddSheaf cover kodairaSpencerOne v w W hv hw
  rw [edgeValue_kodairaSpencerOne, edgeValue_kodairaSpencerOne, edgeValue_kodairaSpencerOne,
    kodairaSpencerValue_common {u,v,w} (by simp) u w (by simp) (by simp) W (common_le_triple u v w W hu hv hw),
    kodairaSpencerValue_common {u,v,w} (by simp) u v (by simp) (by simp) W (common_le_triple u v w W hu hv hw),
    kodairaSpencerValue_common {u,v,w} (by simp) v w (by simp) (by simp) W (common_le_triple u v w W hu hv hw),
    nativeKodairaSpencerSection_cocycle, map_add]

def kodairaSpencerCocycle : CartierCechCoverTransfer.OneCocycle tangentAddSheaf cover where
  val := kodairaSpencerOne
  condition u v w W hu hv hw := (kodairaSpencerOne_closed u v w W hu hv hw).symm

end CycleQ2LiteralNativeKodairaSpencerCocycle

end

#print axioms CycleQ2LiteralNativeKodairaSpencerCocycle.nativeKodairaSpencerSection_restrict
#print axioms CycleQ2LiteralNativeKodairaSpencerCocycle.kodairaSpencerOne_closed
