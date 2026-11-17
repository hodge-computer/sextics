import Proposal.GeometricSeedSectionSheafLimits
import Proposal.GeometricSeedSectionSheafIdealOverlap

/-!
# Local effectiveness of the original twisted ideal source

The original chart projections are studied on actual open subsets of the
surface.  Restriction of a pushed-forward chart sheaf from V to V intersect
that chart is a canonical section isomorphism.  Together with the literal
ideal inclusions, this permits comparison inside the original structure
sheaf without replacing any chart map. Equal actual ideal ranges provide
the prescribed negative-fourth-power transfers. Their original unit
cocycle constructs an inverse section in the native kernel, and hence an
actual isomorphism from the restricted source to each original chart ideal.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafLocal

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheaf
  CycleQ2SeedSectionSheafSections CycleQ2SeedSectionSheafTwist
  CycleQ2SeedSectionSheafLimits CycleQ2SeedSectionSheafMono
  CycleQ2SeedSectionSheafIdealOverlap

section Restrictions

variable {X : Scheme.{0}}

def moduleRes (M : X.Modules) {V W : X.Opens} (h : W ≤ V) :
    Γ(M, V) →+ Γ(M, W) := (M.presheaf.map (homOfLE h).op).hom

theorem moduleRes_comp (M : X.Modules) {U V W : X.Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : Γ(M, U)) :
    moduleRes M hWV (moduleRes M hVU s) = moduleRes M (hWV.trans hVU) s := by
  change (M.presheaf.map (homOfLE hVU).op ≫ M.presheaf.map (homOfLE hWV).op) s = _
  rw [← Functor.map_comp] <;> rfl

@[simp] theorem moduleRes_refl (M : X.Modules) (V : X.Opens) (s : Γ(M, V)) :
    moduleRes M (le_refl V) s = s := by
  change M.presheaf.map (𝟙 (op V)) s = s
  simp only [M.presheaf.map_id, ConcreteCategory.id_apply]

theorem moduleRes_app {M N : X.Modules} (f : M ⟶ N)
    {V W : X.Opens} (h : W ≤ V) (s : Γ(M, V)) :
    moduleRes N h (f.app V s) = f.app W (moduleRes M h s) :=
  (ConcreteCategory.congr_hom (f.mapPresheaf.naturality (homOfLE h).op) s).symm

theorem open_preimage_inf_self (U V : X.Opens) :
    U.ι ⁻¹ᵁ (V ⊓ U) = U.ι ⁻¹ᵁ V := by
  ext x
  change (x.1 ∈ V ∧ x.1 ∈ U) ↔ x.1 ∈ V
  exact and_iff_left x.2

/-- This is the actual pushforward restriction, not an abstract extension
of a section beyond the chart on which it is defined. -/
def pushforwardInfEquiv (U : X.Opens) (M : U.toScheme.Modules) (V : X.Opens) :
    Γ((Scheme.Modules.pushforward U.ι).obj M, V) ≃+
      Γ((Scheme.Modules.pushforward U.ι).obj M, V ⊓ U) :=
  (M.presheaf.mapIso (eqToIso (open_preimage_inf_self U V)).op).addCommGroupIsoToAddEquiv

theorem pushforwardInfEquiv_apply (U : X.Opens) (M : U.toScheme.Modules)
    (V : X.Opens) (s : Γ((Scheme.Modules.pushforward U.ι).obj M, V)) :
    pushforwardInfEquiv U M V s =
      moduleRes ((Scheme.Modules.pushforward U.ι).obj M)
        (show V ⊓ U ≤ V from inf_le_left) s := by
  change M.presheaf.map _ s = M.presheaf.map _ s
  exact congrArg (fun f => M.presheaf.map f s) (Subsingleton.elim _ _)

theorem pushforwardInfEquiv_symm_restrict (U : X.Opens) (M : U.toScheme.Modules)
    (V : X.Opens) (s : Γ((Scheme.Modules.pushforward U.ι).obj M, V ⊓ U)) :
    moduleRes ((Scheme.Modules.pushforward U.ι).obj M)
        (show V ⊓ U ≤ V from inf_le_left) ((pushforwardInfEquiv U M V).symm s) = s := by
  rw [← pushforwardInfEquiv_apply, AddEquiv.apply_symm_apply]

theorem pushforwardInfEquiv_symm_restrict_subopen (U : X.Opens)
    (M : U.toScheme.Modules) (V W : X.Opens) (hWV : W ≤ V) (hWU : W ≤ U)
    (s : Γ((Scheme.Modules.pushforward U.ι).obj M, V ⊓ U)) :
    moduleRes ((Scheme.Modules.pushforward U.ι).obj M) hWV
        ((pushforwardInfEquiv U M V).symm s) =
      moduleRes ((Scheme.Modules.pushforward U.ι).obj M) (le_inf hWV hWU) s := by
  calc
    _ = moduleRes ((Scheme.Modules.pushforward U.ι).obj M) (le_inf hWV hWU)
        (moduleRes ((Scheme.Modules.pushforward U.ι).obj M)
          (show V ⊓ U ≤ V from inf_le_left) ((pushforwardInfEquiv U M V).symm s)) := by
      rw [moduleRes_comp]
    _ = _ := by rw [pushforwardInfEquiv_symm_restrict]

end Restrictions

def idealPatchInfEquiv (i : Fin 3) (V : Surface.Opens) :
    Γ(idealPatch i, V) ≃+ Γ(idealPatch i, V ⊓ Patch i) :=
  pushforwardInfEquiv (X := Surface) (Patch i) (chartIdeal i) V

theorem idealPatchInfEquiv_apply (i : Fin 3) (V : Surface.Opens)
    (s : Γ(idealPatch i, V)) :
    idealPatchInfEquiv i V s =
      moduleRes (X := Surface) (idealPatch i) (show V ⊓ Patch i ≤ V from inf_le_left) s :=
  pushforwardInfEquiv_apply (X := Surface) (Patch i) (chartIdeal i) V s

theorem idealPatchInfEquiv_symm_restrict_subopen (i : Fin 3)
    (V W : Surface.Opens) (hWV : W ≤ V) (hWi : W ≤ Patch i)
    (s : Γ(idealPatch i, V ⊓ Patch i)) :
    moduleRes (X := Surface) (idealPatch i) hWV ((idealPatchInfEquiv i V).symm s) =
      moduleRes (X := Surface) (idealPatch i) (le_inf hWV hWi) s :=
  pushforwardInfEquiv_symm_restrict_subopen (X := Surface)
    (Patch i) (chartIdeal i) V W hWV hWi s

def pairPatchInfEquiv (i j : Fin 3) (V : Surface.Opens) :
    Γ(patchStructure (PairPatch i j), V) ≃+
      Γ(patchStructure (PairPatch i j), V ⊓ PairPatch i j) :=
  pushforwardInfEquiv (X := Surface) (PairPatch i j)
    (structureModule (PairPatch i j).toScheme) V

theorem pairPatchInfEquiv_apply (i j : Fin 3) (V : Surface.Opens)
    (s : Γ(patchStructure (PairPatch i j), V)) :
    pairPatchInfEquiv i j V s = moduleRes (X := Surface) (patchStructure (PairPatch i j))
      (show V ⊓ PairPatch i j ≤ V from inf_le_left) s :=
  pushforwardInfEquiv_apply (X := Surface) (PairPatch i j)
    (structureModule (PairPatch i j).toScheme) V s

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- On each original chart, its projection already detects every section
of the independent global source.  The other coordinates are forced by
the original transition equation and the literal ideal embeddings. -/
theorem chartProjection_app_injective (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) : Function.Injective ((chartProjection i).app V) := by
  intro s t hst
  apply sourceFamily_injective V
  funext j
  change (chartProjection j).app V s = (chartProjection j).app V t
  apply (idealPatchInfEquiv j V).injective
  rw [idealPatchInfEquiv_apply, idealPatchInfEquiv_apply]
  apply idealCoordinate_injective j (V ⊓ Patch j) inf_le_right
  rw [moduleRes_app (X := Surface) (M := twistedIdeal) (N := idealPatch j) (chartProjection j),
    moduleRes_app (X := Surface) (M := twistedIdeal) (N := idealPatch j) (chartProjection j)]
  change sourceCoordinate j (V ⊓ Patch j) inf_le_right
      (moduleRes (X := Surface) twistedIdeal inf_le_left s) =
    sourceCoordinate j (V ⊓ Patch j) inf_le_right
      (moduleRes (X := Surface) twistedIdeal inf_le_left t)
  have hc : sourceCoordinate i V hi s = sourceCoordinate i V hi t :=
    congrArg (idealCoordinate i V hi) hst
  have hr := congrArg (Surface.presheaf.map
    (homOfLE (show V ⊓ Patch j ≤ V from inf_le_left)).op) hc
  rw [sourceCoordinate_restrict, sourceCoordinate_restrict] at hr
  rw [sourceCoordinate_transition j i (V ⊓ Patch j) inf_le_right
      (inf_le_left.trans hi) (moduleRes (X := Surface) twistedIdeal inf_le_left s),
    sourceCoordinate_transition j i (V ⊓ Patch j) inf_le_right
      (inf_le_left.trans hi) (moduleRes (X := Surface) twistedIdeal inf_le_left t)]
  exact congrArg (fun a =>
    (transitionUnit j i (V ⊓ Patch j) inf_le_right (inf_le_left.trans hi) :
      Γ(Surface, V ⊓ Patch j)) ^ 4 * a) hr

/-! ## The inverse uses the actual ideal ranges and the prescribed twist -/

theorem overlapTransfer_exists (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (x : Γ(idealPatch i, V)) :
    ∃ y : Γ(idealPatch j, V), idealCoordinate j V hj y =
      (transitionUnit j i V hj hi : Γ(Surface, V)) ^ 4 * idealCoordinate i V hi x := by
  have hx : idealCoordinate i V hi x ∈ LinearMap.range (idealCoordinate j V hj) := by
    rw [← idealCoordinate_range_eq i j V hi hj]
    exact ⟨x, rfl⟩
  have h := (LinearMap.range (idealCoordinate j V hj)).smul_mem
    ((transitionUnit j i V hj hi : Γ(Surface, V)) ^ 4) hx
  exact h

/-- The unique original ideal section whose coordinate is multiplied by
u_ji^4 = u_ij^(-4). This is independent of the curve parameter. -/
def overlapTransfer (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (x : Γ(idealPatch i, V)) :
    Γ(idealPatch j, V) :=
  Classical.choose (overlapTransfer_exists i j V hi hj x)

theorem overlapTransfer_coordinate (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (x : Γ(idealPatch i, V)) :
    idealCoordinate j V hj (overlapTransfer i j V hi hj x) =
      (transitionUnit j i V hj hi : Γ(Surface, V)) ^ 4 * idealCoordinate i V hi x :=
  Classical.choose_spec (overlapTransfer_exists i j V hi hj x)

theorem overlapTransfer_self (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (x : Γ(idealPatch i, V)) :
    overlapTransfer i i V hi hi x = x := by
  apply idealCoordinate_injective i V hi
  rw [overlapTransfer_coordinate, transitionUnit_self]
  simp only [Units.val_one, one_pow, one_mul]

theorem overlapTransfer_restrict (i j : Fin 3) {V W : Surface.Opens}
    (hWV : W ≤ V) (hi : V ≤ Patch i) (hj : V ≤ Patch j)
    (x : Γ(idealPatch i, V)) :
    moduleRes (X := Surface) (idealPatch j) hWV (overlapTransfer i j V hi hj x) =
      overlapTransfer i j W (hWV.trans hi) (hWV.trans hj)
        (moduleRes (X := Surface) (idealPatch i) hWV x) := by
  apply idealCoordinate_injective j W (hWV.trans hj)
  have hu := congrArg (fun u : Γ(Surface, W)ˣ => (u : Γ(Surface, W)))
    (transitionUnit_restrict j i V W hWV hj hi)
  change Surface.presheaf.map (homOfLE hWV).op
      (transitionUnit j i V hj hi : Γ(Surface, V)) =
    (transitionUnit j i W (hWV.trans hj) (hWV.trans hi) : Γ(Surface, W)) at hu
  calc
    _ = Surface.presheaf.map (homOfLE hWV).op
        (idealCoordinate j V hj (overlapTransfer i j V hi hj x)) :=
      (idealCoordinate_restrict j hWV hj _).symm
    _ = Surface.presheaf.map (homOfLE hWV).op
        ((transitionUnit j i V hj hi : Γ(Surface, V)) ^ 4 *
          idealCoordinate i V hi x) := by rw [overlapTransfer_coordinate]
    _ = (transitionUnit j i W (hWV.trans hj) (hWV.trans hi) : Γ(Surface, W)) ^ 4 *
        idealCoordinate i W (hWV.trans hi) (moduleRes (X := Surface) (idealPatch i) hWV x) := by
      rw [map_mul, map_pow, hu, idealCoordinate_restrict]
      rfl
    _ = _ := (overlapTransfer_coordinate i j W (hWV.trans hi) (hWV.trans hj) _).symm

/-- Starting with one original chart-ideal section, the other components
are its prescribed negative-fourth-power transfers on the real overlaps. -/
def chartFamily (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (x : Γ(idealPatch i, V)) (j : Fin 3) : Γ(idealPatch j, V) :=
  (idealPatchInfEquiv j V).symm
    (overlapTransfer i j (V ⊓ Patch j) (inf_le_left.trans hi) inf_le_right
      (moduleRes (X := Surface) (idealPatch i) inf_le_left x))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem chartFamily_restrict (i j : Fin 3) (V W : Surface.Opens)
    (hi : V ≤ Patch i) (hWV : W ≤ V) (hj : W ≤ Patch j)
    (x : Γ(idealPatch i, V)) :
    moduleRes (X := Surface) (idealPatch j) hWV (chartFamily i V hi x j) =
      overlapTransfer i j W (hWV.trans hi) hj (moduleRes (X := Surface) (idealPatch i) hWV x) := by
  unfold chartFamily
  rw [idealPatchInfEquiv_symm_restrict_subopen j V W hWV hj,
    overlapTransfer_restrict, moduleRes_comp (X := Surface)]

theorem chartFamily_self (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (x : Γ(idealPatch i, V)) : chartFamily i V hi x i = x := by
  have h := chartFamily_restrict i i V V hi (le_refl V) hi x
  simpa only [moduleRes_refl (X := Surface), overlapTransfer_self] using h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem chartFamily_compatible (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (x : Γ(idealPatch i, V)) :
    FamilyCompatible V (chartFamily i V hi x) := by
  intro j k
  let W : Surface.Opens := V ⊓ PairPatch j k
  have hWV : W ≤ V := inf_le_left
  have hWj : W ≤ Patch j := inf_le_right.trans inf_le_left
  have hWk : W ≤ Patch k := inf_le_right.trans inf_le_right
  have hWi : W ≤ Patch i := hWV.trans hi
  letI : CommRing Γ(patchStructure (PairPatch j k), W) :=
    CycleQ2SeedSectionSheafSections.patchSectionsCommRing (PairPatch j k) W
  apply (pairPatchInfEquiv j k V).injective
  rw [pairPatchInfEquiv_apply, pairPatchInfEquiv_apply]
  rw [moduleRes_app (X := Surface) (M := idealPatch j)
      (N := patchStructure (PairPatch j k)) (leftIdealToPair j k),
    moduleRes_app (X := Surface) (M := patchStructure (PairPatch j k))
      (N := patchStructure (PairPatch j k)) (pairTwist j k),
    moduleRes_app (X := Surface) (M := idealPatch k)
      (N := patchStructure (PairPatch j k)) (rightIdealToPair j k)]
  change (leftIdealToPair j k).app W
      (moduleRes (X := Surface) (idealPatch j) hWV (chartFamily i V hi x j)) =
    (pairTwist j k).app W ((rightIdealToPair j k).app W
      (moduleRes (X := Surface) (idealPatch k) hWV (chartFamily i V hi x k)))
  rw [chartFamily_restrict i j V W hi hWV hWj,
    chartFamily_restrict i k V W hi hWV hWk]
  apply (patchSectionsEquiv (PairPatch j k) W (le_inf hWj hWk)).injective
  change patchSectionsEquiv (PairPatch j k) W (le_inf hWj hWk)
      ((patchStructureRestriction (show PairPatch j k ≤ Patch j from inf_le_left)).app W
        ((idealPatchInclusion j).app W
          (overlapTransfer i j W hWi hWj (moduleRes (X := Surface) (idealPatch i) hWV x)))) =
    patchSectionsEquiv (PairPatch j k) W (le_inf hWj hWk)
      ((pairTwist j k).app W
        ((patchStructureRestriction (show PairPatch j k ≤ Patch k from inf_le_right)).app W
          ((idealPatchInclusion k).app W
            (overlapTransfer i k W hWi hWk (moduleRes (X := Surface) (idealPatch i) hWV x)))))
  rw [patchSectionsEquiv_patchRestriction, pairTwist_coordinate,
    patchSectionsEquiv_patchRestriction]
  change idealCoordinate j W hWj
      (overlapTransfer i j W hWi hWj (moduleRes (X := Surface) (idealPatch i) hWV x)) =
    (transitionUnit j k W hWj hWk : Γ(Surface, W)) ^ 4 *
      idealCoordinate k W hWk
        (overlapTransfer i k W hWi hWk (moduleRes (X := Surface) (idealPatch i) hWV x))
  rw [overlapTransfer_coordinate, overlapTransfer_coordinate]
  have hu' := congrArg (fun u : Γ(Surface, W)ˣ => (u : Γ(Surface, W)))
    (transitionUnit_cocycle j k i W hWj hWk hWi)
  change (transitionUnit k i W hWk hWi : Γ(Surface, W)) *
      (transitionUnit j k W hWj hWk : Γ(Surface, W)) =
    (transitionUnit j i W hWj hWi : Γ(Surface, W)) at hu'
  have hu : (transitionUnit j k W hWj hWk : Γ(Surface, W)) *
      (transitionUnit k i W hWk hWi : Γ(Surface, W)) =
    (transitionUnit j i W hWj hWi : Γ(Surface, W)) := (mul_comm _ _).trans hu'
  rw [← mul_assoc, ← mul_pow, hu]

/-- The inverse lands in the already defined kernel, using its native
limit universal property and the original overlap compatibility. -/
def sourceOfChartSection (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (x : Γ(idealPatch i, V)) : Γ(twistedIdeal, V) :=
  compatibleFamilySection V (chartFamily i V hi x) (chartFamily_compatible i V hi x)

theorem chartProjection_sourceOfChartSection (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (x : Γ(idealPatch i, V)) :
    (chartProjection i).app V (sourceOfChartSection i V hi x) = x := by
  rw [sourceOfChartSection, compatibleFamilySection_projection, chartFamily_self]

theorem chartProjection_app_surjective (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) : Function.Surjective ((chartProjection i).app V) :=
  fun x => ⟨sourceOfChartSection i V hi x,
    chartProjection_sourceOfChartSection i V hi x⟩

theorem chartProjection_app_bijective (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) : Function.Bijective ((chartProjection i).app V) :=
  ⟨chartProjection_app_injective i V hi, chartProjection_app_surjective i V hi⟩

/-- The actual chart projection is a linear equivalence on every subopen. -/
def chartProjectionSectionsEquiv (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) :
    Γ(twistedIdeal, V) ≃ₗ[Γ(Surface, V)] Γ(idealPatch i, V) :=
  LinearEquiv.ofBijective ((chartProjection i).val.app (op V)).hom
    (chartProjection_app_bijective i V hi)

theorem chartProjectionSectionsEquiv_apply (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (s : Γ(twistedIdeal, V)) :
    chartProjectionSectionsEquiv i V hi s = (chartProjection i).app V s := rfl

/-! ## An actual isomorphism on the original open subscheme -/

def chartRestrictionProjection (i : Fin 3) :
    (Scheme.Modules.restrictFunctor (Patch i).ι).obj twistedIdeal ⟶ chartIdeal i :=
  (Scheme.Modules.restrictFunctor (Patch i).ι).map (chartProjection i) ≫
    (Scheme.Modules.restrictAdjunction (Patch i).ι).counit.app (chartIdeal i)

theorem chartRestrictionProjection_app_bijective (i : Fin 3)
    (U : (Patch i).toScheme.Opens) :
    Function.Bijective ((chartRestrictionProjection i).app U) := by
  have hi : (Patch i).ι ''ᵁ U ≤ Patch i := by
    simpa only [Scheme.Opens.opensRange_ι] using (Patch i).ι.image_le_opensRange U
  change Function.Bijective (fun s =>
    ((Scheme.Modules.restrictAdjunction (Patch i).ι).counit.app (chartIdeal i)).app U
      ((chartProjection i).app ((Patch i).ι ''ᵁ U) s))
  exact (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictAdjunction (Patch i).ι).counit.app (chartIdeal i)).app U)).comp
      (chartProjection_app_bijective i ((Patch i).ι ''ᵁ U) hi)

instance chartRestrictionProjection_isIso (i : Fin 3) :
    IsIso (chartRestrictionProjection i) :=
  Scheme.Modules.Hom.isIso_iff_isIso_app.mpr fun U =>
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (chartRestrictionProjection_app_bijective i U)

/-- CLOSED SOURCE-LEVEL ENDPOINT: the independent global kernel source
restricts to the unchanged original ideal sheaf on every original chart.
Its transition remains x_i = u_ij^4*x_j, hence the negative-fourth twist. -/
def chartRestrictionIso (i : Fin 3) :
    (Scheme.Modules.restrictFunctor (Patch i).ι).obj twistedIdeal ≅ chartIdeal i :=
  asIso (chartRestrictionProjection i)

end CycleQ2SeedSectionSheafLocal

end

#print axioms CycleQ2SeedSectionSheafLocal.pushforwardInfEquiv
#print axioms CycleQ2SeedSectionSheafLocal.chartProjection_app_injective
#print axioms CycleQ2SeedSectionSheafLocal.chartProjection_app_bijective
#print axioms CycleQ2SeedSectionSheafLocal.chartRestrictionIso
