import Proposal.GeometricCechRefinement
import Proposal.GeometricAffinePairLifts
import Proposal.GeometricAffineTwoCocycle

/-!
# Second cohomology of the affine structure sheaf

Differences of local representatives lift on principal pair intersections.
The defects on triples form an actual structure-sheaf cocycle. A primitive
for that cocycle corrects the pair lifts, which then glue through the two
injective presentations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricAffineHTwo

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
open CycleQ2FiniteCechDescent (Zero globalZero globalZero_exists globalZero_injective)
open CycleQ2CechTwoToDerived (app app_res app_comp app_zero)

variable {X : TopCat.{0}} {ι : Type} [Fintype ι] {I E Q : AbSheaf X} [Injective I]

/-- A closed edge cochain in an injective sheaf corrects local lifts to a
single global lift when its image gives the differences on overlaps. -/
theorem global_lift_of_closed_edges (U : ι → Opens X) (hcover : (⨆ i, U i) = ⊤)
    (φ : I ⟶ E) (ψ : E ⟶ Q) (hzero : φ ≫ ψ = 0)
    (z : Sections Q ⊤) (u : Zero E U)
    (hu : ∀ i, app ψ (U i) (u i) = res Q le_top z)
    (b : One I U) (hb : IsOneCocycle I U b)
    (hedge : ∀ i j (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      res E hj (u j) - res E hi (u i) = app φ W (edgeValue I U b i j W hi hj)) :
    ∃ y : Sections E ⊤, app ψ ⊤ y = z := by
  obtain ⟨p, hp⟩ := oneCocycle_has_primitive b hb
  let v : Zero E U := fun i => u i - app φ (U i) (p i)
  have hglue : ∀ i j (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
      res E hi (v i) = res E hj (v j) := by
    intro i j W hi hj
    have hp' := congrArg (app φ W) (hp i j W hi hj)
    rw [map_sub] at hp'
    change _ = app φ W (edgeValue I U b i j W hi hj) at hp'
    dsimp only [v]
    rw [map_sub, map_sub, ← app_res, ← app_res]
    linear_combination (norm := abel) hp' - hedge i j W hi hj
  obtain ⟨y, hy⟩ := globalZero_exists U hcover v hglue
  refine ⟨y, globalZero_injective U hcover ?_⟩
  funext i
  change res Q le_top (app ψ ⊤ y) = res Q le_top z
  rw [← app_res]
  change app ψ (U i) (globalZero U y i) = res Q le_top z
  rw [hy]
  dsimp only [v]
  rw [map_sub, app_comp, hzero, app_zero, sub_zero, hu]

open CategoryTheory.Abelian
open CycleQ2CechTwoToDerived (presentation presentation_shortExact app_injective)
open CycleQ2FiniteCechDescent (mapOne edgeValue_mapOne edgeValue_sub
  boundaryValue_mapOne boundaryValue_sub)

private theorem section_preimage (S : ShortComplex (AbSheaf X))
    (hS : S.ShortExact) (W : Opens X) (x : Sections S.X₂ W)
    (hx : app S.g W x = 0) : ∃ y : Sections S.X₁ W, app S.f W y = x := by
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
    (evaluation _ AddCommGrpCat).obj (op W)
  have he := hS.exact.map_of_mono_of_preservesKernel E hS.mono_f (by infer_instance)
  exact (ShortComplex.ab_exact_iff (S.map E)).mp he x hx

/-- Two successive injective presentations reduce a global lifting problem
to the degree-two Čech equation on the chosen finite cover. -/
theorem lift_of_two_cocycle_primitives (F : AbSheaf X) (U : ι → Opens X)
    (hcover : (⨆ i, U i) = ⊤)
    (hpair : ∀ i j, Function.Surjective (app (presentation F).g (U i ⊓ U j)))
    (hprimitive : ∀ c : Two F U, IsTwoCocycle F U c → ∃ b : One F U,
      ∀ i j k W hi hj hk, boundaryValue F U b i j k W hi hj hk =
        faceValue F U c i j k W hi hj hk)
    (z : Sections (presentation (presentation F).X₃).X₃ ⊤)
    (u : Zero (presentation (presentation F).X₃).X₂ U)
    (hu : ∀ i, app (presentation (presentation F).X₃).g (U i) (u i) =
      res _ le_top z) :
    ∃ y, app (presentation (presentation F).X₃).g ⊤ y = z := by
  classical
  let S := presentation F
  let T := presentation S.X₃
  change ∀ i, app T.g (U i) (u i) = res T.X₃ le_top z at hu
  have hg (i j : ι) : ∃ a : Sections S.X₂ (U i ⊓ U j),
      app T.f _ (app S.g _ a) =
        res T.X₂ inf_le_right (u j) - res T.X₂ inf_le_left (u i) := by
    have hz : app T.g (U i ⊓ U j)
        (res T.X₂ inf_le_right (u j) - res T.X₂ inf_le_left (u i)) = 0 := by
      simp only [map_sub, app_res, hu, res_comp, sub_self]
    obtain ⟨v, hv⟩ := section_preimage T (presentation_shortExact S.X₃) _ _ hz
    obtain ⟨a, ha⟩ := hpair i j v
    exact ⟨a, by rw [show app S.g _ a = v from ha, hv]⟩
  choose a ha using hg
  have hedge (i j : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
      app T.f W (app S.g W (edgeValue S.X₂ U a i j W hi hj)) =
        res T.X₂ hj (u j) - res T.X₂ hi (u i) := by
    rw [edgeValue, app_res S.g, app_res T.f]
    simpa only [map_sub, res_comp] using
      congrArg (res T.X₂ (le_inf hi hj)) (ha i j)
  have hcycle (i j k : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
      app S.g W (boundaryValue S.X₂ U a i j k W hi hj hk) = 0 := by
    apply app_injective T.f W
    simp only [boundaryValue, map_add, map_sub, hedge, map_zero]
    abel
  choose c hc using fun i j k => section_preimage S (presentation_shortExact F)
    ((U i ⊓ U j) ⊓ U k) _ (hcycle i j k _ (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) inf_le_right)
  have hface (i j k : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
      app S.f W (faceValue F U c i j k W hi hj hk) =
        boundaryValue S.X₂ U a i j k W hi hj hk := by
    rw [faceValue, app_res S.f]
    simpa only [boundaryValue, edgeValue, map_add, map_sub, res_comp] using
      congrArg (res S.X₂ (le_inf (le_inf hi hj) hk)) (hc i j k)
  have hcoc : IsTwoCocycle F U c := by
    intro i j k l W hi hj hk hl
    apply app_injective S.f W
    simp only [map_add, map_sub, map_zero, hface, boundaryValue]
    abel
  obtain ⟨b, hb⟩ := hprimitive c hcoc
  let d : One S.X₂ U := a - mapOne U S.f b
  have hd : IsOneCocycle S.X₂ U d := by
    intro i j k W hi hj hk
    have heq : boundaryValue S.X₂ U d i j k W hi hj hk = 0 := by
      rw [show d = a - mapOne U S.f b from rfl, boundaryValue_sub, boundaryValue_mapOne,
        hb i j k W hi hj hk, hface, sub_self]
    dsimp only [boundaryValue, edgeValue] at heq
    linear_combination (norm := abel) -heq
  apply global_lift_of_closed_edges U hcover (S.g ≫ T.f) T.g (by simp [Category.assoc, T.zero])
    z u hu d hd
  intro i j W hi hj
  dsimp only [d]
  rw [edgeValue_sub, edgeValue_mapOne, ← app_comp, map_sub, app_comp, S.zero,
    app_zero, sub_zero, hedge]

local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- Two successive injective presentations express degree-two cohomology
as a quotient of global sections of the second cokernel. -/
theorem hTwo_subsingleton_of_global_lift (F : AbSheaf X)
    (hlift : Function.Surjective (app (presentation (presentation F).X₃).g ⊤)) :
    Subsingleton (F.H 2) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let P := (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift ℤ))
  let S := presentation F
  let T := presentation S.X₃
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ P (presentation_shortExact F)
    x (Ext.eq_zero_of_injective _) (n₀ := 1) rfl
  obtain ⟨v, hv⟩ := Ext.covariant_sequence_exact₁ P (presentation_shortExact S.X₃)
    y (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  let eI := Sheaf.H.equiv₀ T.X₂ (T := ⊤) isTerminalTop
  let eQ := Sheaf.H.equiv₀ T.X₃ (T := ⊤) isTerminalTop
  obtain ⟨s, hs⟩ := hlift (eQ v)
  let w : T.X₂.H 0 := eI.symm s
  have hw : Sheaf.H.map T.g 0 w = v := by
    apply eQ.injective
    rw [← Sheaf.H.equiv₀_naturality]
    change T.g.hom.app _ (eI (eI.symm s)) = eQ v
    rw [eI.apply_symm_apply]
    exact hs
  rw [← hy, ← hv, ← hw]
  simp only [Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.comp_extClass, Ext.comp_zero, Ext.zero_comp]

open CycleQ2GeometricAffineCohomology (additiveStructureSheaf finite_local_lifts)

/-- Every derived degree-two class of the additive structure sheaf on an
affine spectrum vanishes. -/
theorem affine_H_two_subsingleton (A : Type) [CommRing A] :
    Subsingleton ((additiveStructureSheaf A).H 2) := by
  classical
  let F := additiveStructureSheaf A
  let T := presentation (presentation F).X₃
  have : Sheaf.IsLocallySurjective T.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat T.g).mpr
      (presentation_shortExact (presentation F).X₃).epi_g
  apply hTwo_subsingleton_of_global_lift F
  intro z
  obtain ⟨s, u, hs, hu⟩ := finite_local_lifts T.g z
  let f (i : s) : A := i
  have hf : Ideal.span (Set.range f) = ⊤ := by
    have h : Set.range f = (s : Set A) := Subtype.range_coe
    rwa [h]
  exact lift_of_two_cocycle_primitives F (fun i => PrimeSpectrum.basicOpen (f i))
    (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hf)
    (fun i j => CycleQ2AffinePairLifts.pair_lift A (f i) (f j))
    (CycleQ2GeometricAffineTwoCocycle.primitive f hf) z u hu

#print axioms affine_H_two_subsingleton
end CycleQ2GeometricAffineHTwo
