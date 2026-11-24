import Proposal.GeometricAffineCohomology
import Proposal.GeometricCartierDerivedClass
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Proposal.GeometricAffineOpenOrdinaryDifferentials
import Proposal.GeometricLiteralAmbientCharts
import Proposal.GeometricLiteralThreefoldFirstDifferential
import Proposal.GeometricExteriorPullComposition
import Proposal.GeometricLiteralNegativeTwistDescent
import Proposal.GeometricFiniteCechOneAdditivity
import Proposal.GeometricLiteralThreefoldOneFormPrimitives
import Proposal.GeometricFiniteCechHOne
import Proposal.GeometricThreeOpenH2
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Proposal.GeometricLiteralThreefoldUnfilteredCech
import Proposal.GeometricLiteralNonzeroSweptRestriction
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Proposal.GeometricLiteralThreefoldFunctionPrimitives
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The fixed test class in the additive derived de Rham complex

The corrected vertex forms and the original edge cocycle determine a
derived morphism through the first two maps of the genuine free-sheaf
resolution of the cover. Its coherent edge projection proves
nonvanishing. Attaching one-forms and functions preserves this class
by closed-form lifting and the vanishing of ordinary H² of functions.
The last differential's cokernel recovers the class of each vertex form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

section

/-!
# Degree-one cohomology of a finite projective module on an affine scheme

A finite projective module is a retract of a finite free module. This
retract persists under the associated-sheaf functor and degree-one
cohomology, so vanishing for the structure sheaf gives the result.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2AffineProjectiveHOne

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech
open CycleQ2GeometricSheafCohomologyRestriction (terminalFreeSheafIso)

variable (A : Type) [CommRing A]

abbrev X := Spec (CommRingCat.of A)
abbrev OpenSheaves := AbSheaf (show TopCat from X A)
private abbrev freeTop := freeOpen (⊤ : (X A).Opens)

attribute [local instance] HasExt.standard

abbrev associated : ModuleCat.{0} A ⥤ OpenSheaves A :=
  tilde.functor (CommRingCat.of A) ⋙ SheafOfModules.toSheaf.{0} (X A).ringCatSheaf

private instance : (SheafOfModules.toSheaf.{0} (X A).ringCatSheaf).Additive := {}

instance : (associated A).Additive where
  map_add {M N} f g := by
    let F : ModuleCat.{0} A ⥤ (X A).Modules := tilde.functor (CommRingCat.of A)
    let G := SheafOfModules.toSheaf.{0} (X A).ringCatSheaf
    have h : F.map (f + g) = F.map f + F.map g :=
      tilde.map_add (R := CommRingCat.of A) (M := M) (N := N) f g
    exact (congrArg G.map h).trans (G.map_add (f := F.map f) (g := F.map g))

private def unitIso :
    (associated A).obj (ModuleCat.of A A) ≅
      CycleQ2GeometricAffineCohomology.additiveStructureSheaf A :=
  (SheafOfModules.toSheaf.{0} (X A).ringCatSheaf).mapIso (tildeSelf (R := CommRingCat.of A))

private abbrev cohomology : ModuleCat.{0} A ⥤ AddCommGrpCat.{1} :=
  associated A ⋙ extFunctorObj (freeTop A) 1

private theorem unit_acyclic :
    IsZero ((cohomology A).obj (ModuleCat.of A A)) := by
  let G := CycleQ2GeometricAffineCohomology.additiveStructureSheaf A
  apply ((extFunctorObj (freeTop A) 1).mapIso (unitIso A)).isZero_iff.mpr
  let J := Opens.grothendieckTopology (X A)
  let e := ((extFunctor 1).mapIso (terminalFreeSheafIso J
    (⊤ : (X A).Opens) isTerminalTop).op).app G
  apply e.isZero_iff.mp
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr
    (CycleQ2GeometricAffineCohomology.affine_H_one_subsingleton A)

private theorem free_acyclic (m : ℕ) :
    IsZero ((cohomology A).obj (ModuleCat.of A (Fin m → A))) := by
  classical
  let M := ModuleCat.of A (Fin m → A)
  let U := ModuleCat.of A A
  let p (i : Fin m) : M ⟶ U := ModuleCat.ofHom (LinearMap.proj i)
  let j (i : Fin m) : U ⟶ M := ModuleCat.ofHom (LinearMap.single A (fun _ : Fin m => A) i)
  let H := cohomology A
  have h : (∑ i : Fin m, p i ≫ j i) = 𝟙 M := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext k
    simp only [p, j, ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
      LinearMap.sum_apply, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
    erw [Finset.sum_apply]
    change (∑ i : Fin m, Pi.single i ((x : Fin m → A) i) k) = x k
    simp [Pi.single_apply]
  let : H.Additive := inferInstanceAs ((associated A ⋙ extFunctorObj
    (freeTop A) 1).Additive)
  have hmap : 𝟙 (H.obj M) = ∑ i, H.map (p i ≫ j i) :=
    (H.map_id M).symm.trans ((congrArg H.map h).symm.trans (H.map_sum _ _))
  apply (IsZero.iff_id_eq_zero _).mpr
  refine hmap.trans (Finset.sum_eq_zero fun i _ => ?_)
  exact (H.map_comp (p i) (j i)).trans (by
    rw [(unit_acyclic A).eq_of_tgt (H.map (p i)) 0, zero_comp])

/-- The additive sheaf of a finite projective module on an affine scheme
has zero degree-one cohomology. -/
theorem module_acyclic (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] :
    IsZero ((cohomology A).obj (ModuleCat.of A M)) := by
  obtain ⟨m, p, hp⟩ := Module.Finite.exists_fin' A M
  obtain ⟨j, hj⟩ := Module.projective_lifting_property p (LinearMap.id (R := A) (M := M)) hp
  let q : ModuleCat.of A (Fin m → A) ⟶ ModuleCat.of A M := ModuleCat.ofHom p
  let s : ModuleCat.of A M ⟶ ModuleCat.of A (Fin m → A) := ModuleCat.ofHom j
  let H := cohomology A
  have h : s ≫ q = 𝟙 _ := ModuleCat.hom_ext hj
  have hz : 𝟙 (H.obj (ModuleCat.of A M)) = H.map s ≫ H.map q :=
    (H.map_id _).symm.trans ((congrArg H.map h).symm.trans (H.map_comp s q))
  apply (IsZero.iff_id_eq_zero _).mpr
  refine hz.trans ?_
  rw [(free_acyclic A m).eq_of_tgt (H.map s) 0, zero_comp]

end CycleQ2AffineProjectiveHOne

#print axioms CycleQ2AffineProjectiveHOne.module_acyclic

end

section

/-!
# Ordinary closed-form lifts on the native first chart cover

The ordinary differential sheaf on each literal affine chart is the
associated sheaf of its relative Kähler module. Smoothness of the charts
and the projective-module acyclicity proof give vanishing on this cover.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2LiteralAffineFormAcyclic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricAffineChartSections CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2GeometricAffineKahlerSheaf CycleQ2GeometricOpenDifferentialSheaf
  CycleQ2GeometricModuleLocalIso
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2GeometricSheafCohomologyRestriction (chartCohomologyEquiv terminalFreeSheafIso)

local instance (Z : Scheme.{0}) : HasExt.{1} (AbSheaf (show TopCat from Z)) :=
  HasExt.standard _

section General
variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))

private abbrev chartOpenInclusion : Spec (CommRingCat.of A) ⟶ X := e.inv ≫ U.ι

private theorem chartImage (W : Over U) :
    chartOpenInclusion e ''ᵁ (chartOpensEquiv e).functor.obj W = W.left := by
  rw [chartOpensEquiv_obj, ← Scheme.Hom.comp_preimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr W.hom.le]

private def chartPush : AbSheaf (show TopCat from Spec (CommRingCat.of A)) ⥤
    Sheaf (((Opens.grothendieckTopology X)).over U) AddCommGrpCat.{0} :=
  (chartOpensEquiv e).functor.sheafPushforwardContinuous AddCommGrpCat
    ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology (Spec (CommRingCat.of A)))

/-- The affine chart comparison on the original additive module sheaf. -/
def moduleOverIso (M : X.Modules) : (addSheaf M).over U ≅
    (chartPush e).obj (addSheaf (M.restrict (chartOpenInclusion e))) := by
  let F := addSheaf M
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun W =>
    F.obj.mapIso (eqToIso (chartImage e W.unop)).op) ?_)
  intro V W f
  change F.obj.map f.unop.left.op ≫
      F.obj.map (eqToHom (chartImage e W.unop)).op =
    F.obj.map (eqToHom (chartImage e V.unop)).op ≫
      F.obj.map (((chartOpenInclusion e).opensFunctor.map
        ((chartOpensEquiv e).functor.map f.unop)).op)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)

end General

open CycleQ2LiteralThreefoldFirstDifferential (X coeff structural One OneModule)
open CycleQ2LiteralAmbientCharts (fixedOpen fixedChart chartInclusion
  chartInclusion_overComplex affine_smooth)
open CycleQ2LiteralAbelJacobiContraction (T)

private theorem coefficient_eq (i : Fin 4) :
    affineCoefficient (T i) =
      schemeCoefficient (Spec.map (CommRingCat.ofHom (algebraMap ℂ (T i)))) := by
  apply RingHom.ext
  intro c
  exact ConcreteCategory.congr_hom (affineCoefficient_structureMorphism (T i)) c

private theorem compatible (i : Fin 4) :
    CycleQ2ExteriorPullComposition.compatible (chartInclusion i) (affineCoefficient (T i)) coeff := by
  rw [coefficient_eq]
  exact CycleQ2ExteriorPullComposition.compatible_over (chartInclusion i)
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ (T i)))) structural
    (chartInclusion_overComplex i)

private def chartForms (i : Fin 4) : AbSheaf (show TopCat from Spec (CommRingCat.of (T i))) :=
  addSheaf (kahlerTilde (A := T i))

private def chartOverOne (i : Fin 4) :
    One.over (fixedOpen i) ≅ (chartPush (fixedChart i).symm).obj (chartForms i) := by
  let e := (fixedChart i).symm
  let G := SheafOfModules.toSheaf.{0} (Spec (CommRingCat.of (T i))).ringCatSheaf
  let q := openDifferentialIso (chartInclusion i) (affineCoefficient (T i)) coeff (compatible i) ≪≫
    affineKahlerIso (A := T i)
  exact moduleOverIso e OneModule ≪≫ (chartPush e).mapIso (G.mapIso q)

private theorem chartSmooth (i : Fin 4) : Algebra.Smooth ℂ (T i) := by
  have hs : Smooth (Spec.map (CommRingCat.ofHom (algebraMap ℂ (T i)))) :=
    letI := affine_smooth i
    SmoothOfRelativeDimension.smooth 3 _
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)

theorem chart_forms_acyclic (i : Fin 4) : Subsingleton ((chartForms i).H 1) := by
  letI := chartSmooth i
  let A := T i
  let Z := Spec (CommRingCat.of A)
  let G := chartForms i
  let J := Opens.grothendieckTopology Z
  let e := ((extFunctor 1).mapIso (terminalFreeSheafIso J (⊤ : Z.Opens) isTerminalTop).op).app G
  have h : IsZero _ := e.isZero_iff.mpr
    (CycleQ2AffineProjectiveHOne.module_acyclic A (KaehlerDifferential ℂ A))
  exact AddCommGrpCat.isZero_iff_subsingleton.mp h

/-- Actual degree-one affine vanishing for the ordinary one-form sheaf
on every one of the literal four opens. -/
theorem localHOne (i : Fin 4) : Subsingleton (One.H' 1 (fixedOpen i)) := by
  letI := chart_forms_acyclic i
  let e := (fixedChart i).symm
  exact (chartCohomologyEquiv (Opens.grothendieckTopology X) (fixedOpen i)
    (Opens.grothendieckTopology (Spec (CommRingCat.of (T i))))
    (chartOpensEquiv e) ⊤ isTerminalTop One (chartForms i) (chartOverOne i) 1).injective.subsingleton

end CycleQ2LiteralAffineFormAcyclic

#print axioms CycleQ2LiteralAffineFormAcyclic.localHOne

end

section

/-!
# Derived classes represented by closed one-forms

Subtracting an ordinary Čech boundary from a one-cocycle does not
change its cohomology class. If the adjusted edge forms are closed,
the cocycle descends to the kernel sheaf of the exterior differential.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2ClosedOneFormClasses

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2FiniteCechOneAdditivity
open CycleQ2CechTwoToDerived (app app_comp app_zero app_injective freeOpenSections_postcomp)
open CycleQ2LiteralNegativeTwistDescent (cechOneClass_surjective_of_local_vanishing)

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) [Fintype ι]
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G : AbSheaf X} (d : F ⟶ G)

private def boundaryOf (p : Zero F U) : One F U :=
  fun i j => res F inf_le_right (p j) - res F inf_le_left (p i)

private theorem boundaryOf_restrict (p : Zero F U) (i j : ι)
    (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
    edgeValue F U (boundaryOf U p) i j W hi hj =
      res F hj (p j) - res F hi (p i) := by
  simp only [edgeValue, boundaryOf, map_sub]
  exact congrArg₂ (· - ·) (res_comp F inf_le_right (le_inf hi hj) (p j))
    (res_comp F inf_le_left (le_inf hi hj) (p i))

private theorem boundaryOf_closed (p : Zero F U) : IsOneCocycle F U (boundaryOf U p) := by
  intro i j k W hi hj hk
  change edgeValue F U (boundaryOf U p) i k W hi hk =
    edgeValue F U (boundaryOf U p) i j W hi hj + edgeValue F U (boundaryOf U p) j k W hj hk
  rw [boundaryOf_restrict, boundaryOf_restrict, boundaryOf_restrict]
  abel

private theorem section_lift {W : Opens X} (s : Sections F W) (hs : app d W s = 0) :
    ∃ a : Sections (kernel d) W, app (kernel.ι d) W a = s := by
  let k := (freeOpenSections F W).symm s
  have hk : k ≫ d = 0 := by
    apply (freeOpenSections G W).injective
    rw [← freeOpenSections_postcomp, AddEquiv.apply_symm_apply, hs, map_zero]
  let l := kernel.lift d k hk
  refine ⟨freeOpenSections (kernel d) W l, ?_⟩
  rw [freeOpenSections_postcomp, kernel.lift_ι, AddEquiv.apply_symm_apply]

variable (cover : (⨆ i, U i) = ⊤)

/-- The ordinary degree-one class comes from the closed-form kernel if its
Čech representative differs from a closed edge cochain by a Čech boundary. -/
theorem class_lift (c : One F U) (hc : IsOneCocycle F U c) (p : Zero F U)
    (hp : ∀ i j, app d (U i ⊓ U j) (c i j) = app d (U i ⊓ U j) (boundaryOf U p i j)) :
    ∃ a : (kernel d).H' 1 ⊤, a.comp (Ext.mk₀ (kernel.ι d)) (add_zero 1) =
      cechOneClass U cover c hc := by
  let b := boundaryOf U p
  let q := c - b
  have hb : IsOneCocycle F U b := boundaryOf_closed U p
  have hq : IsOneCocycle F U q := (oneCocycles U).sub_mem hc hb
  have hz (i j : ι) : app d (U i ⊓ U j) (q i j) = 0 := by
    change app d _ (c i j - b i j) = 0
    rw [map_sub, hp, sub_self]
  choose a ha using fun i j => section_lift d (q i j) (hz i j)
  have ha' : mapOne U (kernel.ι d) a = q := funext fun i => funext fun j => ha i j
  have ha_closed : IsOneCocycle (kernel d) U a := by
    intro i j k W hi hj hk
    change edgeValue (kernel d) U a i k W hi hk =
      edgeValue (kernel d) U a i j W hi hj + edgeValue (kernel d) U a j k W hj hk
    apply app_injective (kernel.ι d) W
    simp only [map_add, ← edgeValue_mapOne, ha']
    exact hq i j k W hi hj hk
  have hzero : cechOneClass U cover b hb = 0 :=
    cechOneClass_eq_zero_of_primitive U cover b hb p
      (fun i j W hi hj => (boundaryOf_restrict U p i j W hi hj).symm)
  have he : cechOneClass U cover q hq = cechOneClass U cover c hc := by
    have h := (cechOneClassHom (F := F) U cover).map_sub ⟨c, hc⟩ ⟨b, hb⟩
    change cechOneClass U cover q hq = cechOneClass U cover c hc - cechOneClass U cover b hb at h
    rw [h, hzero, sub_zero]
  refine ⟨cechOneClass U cover a ha_closed, ?_⟩
  refine (cechOneClass_naturality U cover (kernel.ι d) a ha_closed).trans ?_
  have hq' : (⟨mapOne U (kernel.ι d) a, mapOne_closed U (kernel.ι d) a ha_closed⟩ :
      oneCocycles (F := F) U) = ⟨q, hq⟩ := Subtype.ext ha'
  exact (congrArg (cechOneClassHom (F := F) U cover) hq').trans he

end CycleQ2ClosedOneFormClasses

namespace CycleQ2LiteralClosedOneForms

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  TopologicalSpace Opposite CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
  CycleQ2FiniteCechDescent CycleQ2FiniteInjectiveCech CycleQ2FiniteCechHOne
  CycleQ2LiteralThreefoldFirstDifferential
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)
open CycleQ2CechTwoToDerived (app)
open CycleQ2LiteralThreefoldOneFormPrimitives (one_primitive logUnit)
open CycleQ2LiteralNegativeTwistDescent (cechOneClass_surjective_of_local_vanishing)

local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _

/-- Every degree-one class on this cover has a representative in the actual
sheaf of closed one-forms. The retained correction is an actual unit logarithm. -/
theorem liftČech (c : CycleQ2FiniteInjectiveCech.One One fixedOpen)
    (hc : IsOneCocycle One fixedOpen c) :
    ∃ a : (kernel differential).H' 1 ⊤,
      a.comp (Ext.mk₀ (kernel.ι differential)) (add_zero 1) =
        cechOneClass fixedOpen fixedOpen_cover c hc := by
  obtain ⟨k, p, hp⟩ := one_primitive c hc
  apply CycleQ2ClosedOneFormClasses.class_lift fixedOpen differential fixedOpen_cover c hc p
  intro i j
  let W := fixedOpen i ⊓ fixedOpen j
  let ℓ := scalarLog W k (logUnit i j W inf_le_left inf_le_right)
  let c' := edgeValue One fixedOpen c i j W inf_le_left inf_le_right
  have h : app differential W (CycleQ2ClosedOneFormClasses.boundaryOf fixedOpen p i j) =
      app differential W (c' - ℓ) := congrArg (app differential W) (hp i j W inf_le_left inf_le_right)
  have hl : app differential W ℓ = 0 := scalar_log_closed W k (logUnit i j W inf_le_left inf_le_right)
  have hℓ : app differential W (c' - ℓ) = app differential W c' :=
    ((app differential W).map_sub c' ℓ).trans (by erw [hl, sub_zero])
  exact (congrArg (app differential W) (res_self One _ _)).symm.trans (h.trans hℓ).symm

/-- The ordinary Hodge term admits lifts through the kernel of the
exterior differential whenever it is computed on the literal affine cover. -/
theorem liftHOne (hlocal : ∀ i, Subsingleton (One.H' 1 (fixedOpen i))) (x : One.H' 1 ⊤) :
    ∃ a : (kernel differential).H' 1 ⊤, a.comp (Ext.mk₀ (kernel.ι differential)) (add_zero 1) = x := by
  obtain ⟨c, hc, rfl⟩ := cechOneClass_surjective_of_local_vanishing One fixedOpen fixedOpen_cover hlocal x
  exact liftČech c hc

end CycleQ2LiteralClosedOneForms

#print axioms CycleQ2ClosedOneFormClasses.class_lift
#print axioms CycleQ2LiteralClosedOneForms.liftHOne

end

section

/-!
# The free-sheaf resolution at the start of an open cover

The first two Čech maps are formed from the genuine free additive sheaves
of the opens and pair intersections. The sheaf gluing condition identifies
the augmentation as the cokernel of the pair difference map.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2CechRoof

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
  CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
open CycleQ2MayerVietorisRestriction (freeOpenSheaf)

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)
variable [HasCoproductsOfShape ι (AbSheaf X)] [HasCoproductsOfShape (ι × ι) (AbSheaf X)]

private theorem freeOpenMap_comp {V W Z : Opens X} (h : V ≤ W) (k : W ≤ Z) :
    freeOpenMap h ≫ freeOpenMap k = freeOpenMap (h.trans k) :=
  ((freeOpenSheaf (X := X)).map_comp (homOfLE h) (homOfLE k)).symm

abbrev vertex (i : ι) := freeOpen (U i)
abbrev pair (p : ι × ι) := freeOpen (U p.1 ⊓ U p.2)

abbrev Vertices := ∐ (vertex U)
abbrev Pairs := ∐ (pair U)

def augmentation : Vertices U ⟶ freeOpen (⊤ : Opens X) :=
  Sigma.desc (fun _ => freeOpenMap le_top)

def pairBoundary : Pairs U ⟶ Vertices U :=
  Sigma.desc (fun p =>
    freeOpenMap inf_le_right ≫ Sigma.ι (vertex U) p.2 -
      freeOpenMap inf_le_left ≫ Sigma.ι (vertex U) p.1)

theorem boundary_augmentation : pairBoundary U ≫ augmentation U = 0 := by
  apply Sigma.hom_ext
  intro p
  simp only [pairBoundary, augmentation, Sigma.ι_desc_assoc, Preadditive.sub_comp,
    Category.assoc, Sigma.ι_desc, freeOpenMap_comp, sub_self, comp_zero]

abbrev augmentCofork := CokernelCofork.ofπ (augmentation U) (boundary_augmentation U)

private def vertexValues {F : AbSheaf X} (q : Vertices U ⟶ F) (i : ι) : Sections F (U i) :=
  freeOpenSections F (U i) (Sigma.ι (vertex U) i ≫ q)

private theorem vertexValues_agree {F : AbSheaf X} (q : Vertices U ⟶ F)
    (hq : pairBoundary U ≫ q = 0) (i j : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
    res F hi (vertexValues U q i) = res F hj (vertexValues U q j) := by
  have h := congrArg (fun a => Sigma.ι (pair U) (i, j) ≫ a) hq
  simp only [pairBoundary, Sigma.ι_desc_assoc, Preadditive.sub_comp, Category.assoc,
    comp_zero] at h
  have h' := (sub_eq_zero.mp h).symm
  have h'' := congrArg (fun a => freeOpenMap (le_inf hi hj) ≫ a) h'
  simp only [← Category.assoc, freeOpenMap_comp] at h''
  let u : freeOpen (U i) ⟶ F := Sigma.ι (vertex U) i ≫ q
  let v : freeOpen (U j) ⟶ F := Sigma.ι (vertex U) j ≫ q
  have he : freeOpenMap hi ≫ u = freeOpenMap hj ≫ v := h''
  exact (freeOpenSections_naturality F hi u).symm.trans
    ((congrArg (fun k : freeOpen W ⟶ F => freeOpenSections F W k) he).trans
      (freeOpenSections_naturality F hj v))

section Gluing

variable [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
variable {F : AbSheaf X} (q : Vertices U ⟶ F) (hq : pairBoundary U ≫ q = 0)

include hcover hq in
private theorem exists_glue : ∃ a : Sections F ⊤, globalZero U a = vertexValues U q :=
  CycleQ2FiniteCechDescent.globalZero_exists U hcover (vertexValues U q)
    (vertexValues_agree U q hq)

private def glueSection : Sections F ⊤ :=
  Classical.choose (exists_glue U hcover q hq)

private theorem glueSection_restrict (i : ι) :
    res F (show U i ≤ ⊤ from le_top) (glueSection U hcover q hq) = vertexValues U q i :=
  congrFun (Classical.choose_spec (exists_glue U hcover q hq)) i

private def glue : freeOpen (⊤ : Opens X) ⟶ F :=
  (freeOpenSections F ⊤).symm (glueSection U hcover q hq)

private theorem glue_fac : augmentation U ≫ glue U hcover q hq = q := by
  apply Sigma.hom_ext
  intro i
  have h : Sigma.ι (vertex U) i ≫ augmentation U = freeOpenMap le_top :=
    Sigma.ι_desc _ _
  apply (freeOpenSections F (U i)).injective
  erw [← Category.assoc, h, freeOpenSections_naturality, glue, AddEquiv.apply_symm_apply]
  exact glueSection_restrict U hcover q hq i

private theorem glue_unique (m : freeOpen (⊤ : Opens X) ⟶ F) (hm : augmentation U ≫ m = q) :
    m = glue U hcover q hq := by
  apply (freeOpenSections F ⊤).injective
  have he : freeOpenSections F ⊤ (glue U hcover q hq) = glueSection U hcover q hq :=
    (freeOpenSections F ⊤).apply_symm_apply _
  rw [he]
  apply globalZero_injective U hcover
  funext i
  have h : Sigma.ι (vertex U) i ≫ augmentation U = freeOpenMap le_top :=
    Sigma.ι_desc _ _
  have hi : freeOpenMap (show U i ≤ ⊤ from le_top) ≫ m = Sigma.ι (vertex U) i ≫ q :=
    (congrArg (fun f => f ≫ m) h).symm.trans
      ((Category.assoc (Sigma.ι (vertex U) i) (augmentation U) m).trans
        (congrArg (fun f => Sigma.ι (vertex U) i ≫ f) hm))
  exact (freeOpenSections_naturality F le_top m).symm.trans
    ((congrArg (fun k : freeOpen (U i) ⟶ F => freeOpenSections F (U i) k) hi).trans
      (glueSection_restrict U hcover q hq i).symm)

end Gluing

/-- The augmentation is the actual cokernel of the Čech pair boundaries. -/
def augmentationCokernel [Fintype ι] (hcover : (⨆ i, U i) = ⊤) :
    IsColimit (augmentCofork U) :=
  CokernelCofork.IsColimit.ofπ (augmentation U) (boundary_augmentation U)
    (glue U hcover) (glue_fac U hcover) (glue_unique U hcover)

/-- The augmentation is surjective as a morphism of sheaves. -/
theorem augmentation_epi [Fintype ι] (hcover : (⨆ i, U i) = ⊤) :
    Epi (augmentation U) := epi_of_isColimit_cofork (augmentationCokernel U hcover)

abbrev Kernel := kernel (augmentation U)

def boundaryToKernel : Pairs U ⟶ Kernel U :=
  kernel.lift _ (pairBoundary U) (boundary_augmentation U)

theorem boundaryToKernel_fac :
    boundaryToKernel U ≫ kernel.ι (augmentation U) = pairBoundary U :=
  kernel.lift_ι _ _ _

theorem boundaryToKernel_epi [Fintype ι] (hcover : (⨆ i, U i) = ⊤) :
    Epi (boundaryToKernel U) := by
  let S := ShortComplex.mk (pairBoundary U) (augmentation U) (boundary_augmentation U)
  have hE : S.Exact := S.exact_of_g_is_cokernel (augmentationCokernel U hcover)
  exact S.exact_iff_epi_kernel_lift.mp hE

end CycleQ2CechRoof

#print axioms CycleQ2CechRoof.augmentationCokernel
#print axioms CycleQ2CechRoof.boundaryToKernel_epi

end

section

/-!
# A derived class of an edge cocycle and its corrected vertex sections

The local primitive in an injective presentation descends the edge
cochains to the kernel of the Čech augmentation. The vertex
corrections give a commutative square with the differential between
the two sheaves. The derived morphism is represented by the mapping
cone of this square and restricts to the stated vertex sections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2CechUpperClass

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechHOne CycleQ2FiniteCechDescent CycleQ2CechRoof
open CycleQ2CechTwoToDerived (presentation presentation_shortExact app app_comp sectionExtZero freeOpenSections_postcomp)
open CochainComplex.mappingCone

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) [Fintype ι]
variable [HasCoproductsOfShape ι (AbSheaf X)] [HasCoproductsOfShape (ι × ι) (AbSheaf X)]

local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
attribute [local instance] HasDerivedCategory.standard

variable (cover : (⨆ i, U i) = ⊤)

def sequence : ShortComplex (AbSheaf X) :=
  ShortComplex.mk (kernel.ι (augmentation U)) (augmentation U) (kernel.condition _)

include cover in
theorem shortExact : (sequence U).ShortExact := by
  let : Epi (augmentation U) := augmentation_epi U cover
  exact ShortComplex.ShortExact.mk' ((sequence U).exact_of_f_is_kernel (kernelIsKernel _))
    (inferInstanceAs (Mono (kernel.ι (augmentation U)))) (inferInstanceAs (Epi (augmentation U)))

variable {F G : AbSheaf X} (d : F ⟶ G)

def fromVertices {H : AbSheaf X} (a : Zero H U) : Vertices U ⟶ H :=
  Sigma.desc (fun i => (freeOpenSections H (U i)).symm (a i))

def fromPairs (c : One F U) : Pairs U ⟶ F :=
  Sigma.desc (fun p => (freeOpenSections F (U p.1 ⊓ U p.2)).symm (c p.1 p.2))

private theorem pairBoundary_values {H : AbSheaf X} (a : Zero H U) (p : ι × ι) :
    freeOpenSections H (U p.1 ⊓ U p.2)
      (Sigma.ι (CycleQ2CechRoof.pair U) p ≫ pairBoundary U ≫ fromVertices U a) =
        res H inf_le_right (a p.2) - res H inf_le_left (a p.1) := by
  simp only [pairBoundary, Sigma.ι_desc_assoc, Preadditive.sub_comp, Category.assoc,
    fromVertices, Sigma.ι_desc, map_sub, freeOpenSections_naturality, AddEquiv.apply_symm_apply]

private theorem fromPairs_values (c : One F U) (p : ι × ι) (d : F ⟶ G) :
    freeOpenSections G (U p.1 ⊓ U p.2) (Sigma.ι (CycleQ2CechRoof.pair U) p ≫ fromPairs U c ≫ d) =
      app d (U p.1 ⊓ U p.2) (c p.1 p.2) := by
  erw [← Category.assoc, fromPairs, Sigma.ι_desc, ← freeOpenSections_postcomp,
    AddEquiv.apply_symm_apply]

variable {c : One F U} (z : OneDescent U c)

private def toPresentation : Vertices U ⟶ (presentation F).X₂ :=
  fromVertices U z.primitive

private def toCokernel : freeOpen (⊤ : Opens X) ⟶ (presentation F).X₃ :=
  (freeOpenSections _ ⊤).symm z.globalSection

private theorem presentation_comm :
    toPresentation U z ≫ (presentation F).g = augmentation U ≫ toCokernel U z := by
  apply Sigma.hom_ext
  intro i
  apply (freeOpenSections (presentation F).X₃ (U i)).injective
  simp only [toPresentation, fromVertices, augmentation, toCokernel, Sigma.ι_desc_assoc,
    ← Category.assoc, ← freeOpenSections_postcomp, Sigma.ι_desc,
    AddEquiv.apply_symm_apply]
  have hh := congrFun z.global_restriction i
  have hr := freeOpenSections_naturality (presentation F).X₃ (show U i ≤ ⊤ from le_top)
    ((freeOpenSections (presentation F).X₃ ⊤).symm z.globalSection)
  simp only [AddEquiv.apply_symm_apply] at hr
  exact hh.symm.trans hr.symm

def fromKernel : Kernel U ⟶ F :=
  (presentation_shortExact F).fIsKernel.lift (KernelFork.ofι
    (kernel.ι (augmentation U) ≫ toPresentation U z) (by
      rw [Category.assoc, presentation_comm, ← Category.assoc, kernel.condition, zero_comp]))

theorem fromKernel_fac :
    fromKernel U z ≫ (presentation F).f = kernel.ι (augmentation U) ≫ toPresentation U z :=
  Fork.IsLimit.lift_ι _

theorem fromKernel_pairs : boundaryToKernel U ≫ fromKernel U z = fromPairs U c := by
  let : Mono (presentation F).f := (presentation_shortExact F).mono_f
  apply (cancel_mono (presentation F).f).mp
  rw [Category.assoc, fromKernel_fac, ← Category.assoc, boundaryToKernel_fac]
  apply Sigma.hom_ext
  intro p
  apply (freeOpenSections (presentation F).X₂ (U p.1 ⊓ U p.2)).injective
  refine (pairBoundary_values U z.primitive p).trans ?_
  have hz : res (presentation F).X₂ inf_le_right (z.primitive p.2) -
      res (presentation F).X₂ inf_le_left (z.primitive p.1) =
        app (presentation F).f (U p.1 ⊓ U p.2)
          (edgeValue F U c p.1 p.2 (U p.1 ⊓ U p.2) inf_le_left inf_le_right) := z.differential p.1 p.2 (U p.1 ⊓ U p.2) inf_le_left inf_le_right
  exact hz.trans ((congrArg (app (presentation F).f (U p.1 ⊓ U p.2)) (res_self F _ _)).trans
    (fromPairs_values U c p (presentation F).f).symm)

/-- The descent gives the same element of ordinary degree-one cohomology. -/
theorem edgeComparison :
    (shortExact U cover).extClass.comp (Ext.mk₀ (fromKernel U z)) (add_zero 1) =
      oneDescentClass U z := by
  let m : sequence U ⟶ presentation F :=
    { τ₁ := fromKernel U z
      τ₂ := toPresentation U z
      τ₃ := toCokernel U z
      comm₁₂ := fromKernel_fac U z
      comm₂₃ := presentation_comm U z }
  exact ShortComplex.ShortExact.extClass_naturality (shortExact U cover)
    (presentation_shortExact F) m

variable (a : Zero G U)
variable (hc : ∀ i j, app d (U i ⊓ U j) (c i j) =
    res G inf_le_right (a j) - res G inf_le_left (a i))

include cover hc in
theorem square :
    kernel.ι (augmentation U) ≫ fromVertices U a = fromKernel U z ≫ d := by
  let : Epi (boundaryToKernel U) := boundaryToKernel_epi U cover
  apply (cancel_epi (boundaryToKernel U)).mp
  rw [← Category.assoc, boundaryToKernel_fac, ← Category.assoc, fromKernel_pairs]
  apply Sigma.hom_ext
  intro p
  apply (freeOpenSections G (U p.1 ⊓ U p.2)).injective
  exact (pairBoundary_values U a p).trans
    ((hc p.1 p.2).symm.trans (fromPairs_values U c p d).symm)

abbrev single := CochainComplex.singleFunctor (AbSheaf X) 0
abbrev upperCone := CochainComplex.mappingCone ((single (X := X)).map d)

include cover hc in
private theorem coneSquare :
    ((sequence U).map (single (X := X))).f ≫ (single (X := X)).map (fromVertices U a) =
      (single (X := X)).map (fromKernel U z) ≫ (single (X := X)).map d := by
  let S := single (X := X)
  change S.map (kernel.ι (augmentation U)) ≫ S.map (fromVertices U a) =
    S.map (fromKernel U z) ≫ S.map d
  exact (S.map_comp _ _).symm.trans
    ((congrArg S.map (square U cover d z a hc)).trans (S.map_comp _ _))

def coneMap :
    CochainComplex.mappingCone (((sequence U).map (single (X := X))).f) ⟶ upperCone d :=
  CochainComplex.mappingCone.map _ _
    ((single (X := X)).map (fromKernel U z)) ((single (X := X)).map (fromVertices U a))
    (coneSquare U cover d z a hc)

private def coneTriangles :
    CochainComplex.mappingCone.triangle (((sequence U).map (single (X := X))).f) ⟶
      CochainComplex.mappingCone.triangle ((single (X := X)).map d) :=
  CochainComplex.mappingCone.triangleMap _ _
    ((single (X := X)).map (fromKernel U z)) ((single (X := X)).map (fromVertices U a))
    (coneSquare U cover d z a hc)

include cover in
private theorem liftedShortExact : ((sequence U).map (single (X := X))).ShortExact :=
  (shortExact U cover).map_of_exact (HomologicalComplex.single (AbSheaf X) (.up ℤ) 0)

private def augmentIso :
    DerivedCategory.Q.obj (CochainComplex.mappingCone (((sequence U).map (single (X := X))).f)) ≅
      DerivedCategory.Q.obj ((single (X := X)).obj (freeOpen (⊤ : Opens X))) :=
  let e := descShortComplex ((sequence U).map (single (X := X)))
  let D := DerivedCategory.Q (C := AbSheaf X)
  let hq := quasiIso_descShortComplex (liftedShortExact U cover)
  @asIso _ _ _ _ (D.map e) ((DerivedCategory.isIso_Q_map_iff_quasiIso (AbSheaf X) e).mpr hq)

/-- The corrected cocycle defines a morphism from the constant additive sheaf
to the actual cone of its last exterior differential. -/
def derivedClass :
    DerivedCategory.Q.obj ((single (X := X)).obj (freeOpen (⊤ : Opens X))) ⟶
      DerivedCategory.Q.obj (upperCone d) :=
  (augmentIso U cover).inv ≫ DerivedCategory.Q.map (coneMap U cover d z a hc)

private abbrev localValue (i : ι) : freeOpen (U i) ⟶ G :=
  (freeOpenSections G (U i)).symm (a i)

/-- The global derived class restricts to the original vertex form on each
open. This equality uses the actual map of the free open sheaves. -/
theorem vertexRestriction (i : ι) :
    DerivedCategory.Q.map ((single (X := X)).map (freeOpenMap (show U i ≤ ⊤ from le_top))) ≫
      derivedClass U cover d z a hc =
    DerivedCategory.Q.map ((single (X := X)).map (localValue U a i)) ≫
      DerivedCategory.Q.map (inr ((single (X := X)).map d)) := by
  let S := single (X := X)
  let P := (sequence U).map S
  let D := DerivedCategory.Q (C := AbSheaf X)
  let j := S.map (Sigma.ι (vertex U) i)
  let e := descShortComplex P
  let b := inr P.f
  let v := S.map (freeOpenMap (show U i ≤ ⊤ from le_top))
  let m := coneMap U cover d z a hc
  have heq : j ≫ b ≫ e = v := by
    have h₁ : b ≫ e = S.map (augmentation U) := inr_descShortComplex P
    exact (congrArg (fun k => j ≫ k) h₁).trans
      ((S.map_comp _ _).symm.trans (congrArg S.map (Sigma.ι_desc _ _)))
  let E := augmentIso U cover
  have hE : E.hom = D.map e := rfl
  have hb : D.map v ≫ E.inv = D.map j ≫ D.map b := by
    apply (cancel_mono E.hom).mp
    have hmap : D.map j ≫ D.map b ≫ D.map e = D.map v :=
      (congrArg (fun u => D.map j ≫ u) (D.map_comp b e).symm).trans
        ((D.map_comp j (b ≫ e)).symm.trans (congrArg D.map heq))
    erw [Category.assoc, E.inv_hom_id, Category.comp_id, Category.assoc, hE]
    exact hmap.symm
  have hcm : b ≫ m = S.map (fromVertices U a) ≫ inr (S.map d) :=
    (coneTriangles U cover d z a hc).comm₂
  have hj : j ≫ S.map (fromVertices U a) = S.map (localValue U a i) :=
    (S.map_comp _ _).symm.trans (congrArg S.map (Sigma.ι_desc _ _))
  change D.map v ≫ E.inv ≫ D.map m = _
  rw [← Category.assoc, hb]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => D.map j ≫ k) ((D.map_comp b m).symm.trans
      ((congrArg D.map hcm).trans (D.map_comp _ _)))).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun k => k ≫ D.map (inr (S.map d))) ((D.map_comp _ _).symm.trans (congrArg D.map hj)))))

/-- The edge projection is the cone boundary to the first coefficient sheaf. -/
def edgeProjection :
    DerivedCategory.Q.obj (upperCone d) ⟶
      (DerivedCategory.Q.obj ((single (X := X)).obj F))⟦(1 : ℤ)⟧ :=
  let S := single (X := X)
  let D := DerivedCategory.Q (C := AbSheaf X)
  D.map (CochainComplex.mappingCone.triangle (S.map d)).mor₃ ≫
    (D.commShiftIso 1).hom.app (S.obj F)

private theorem class_edge_projection :
    derivedClass U cover d z a hc ≫ edgeProjection d =
      DerivedCategory.triangleOfSESδ (liftedShortExact U cover) ≫
        (DerivedCategory.Q.map ((single (X := X)).map (fromKernel U z)))⟦(1 : ℤ)⟧' := by
  let S := single (X := X)
  let D := DerivedCategory.Q (C := AbSheaf X)
  let P := (sequence U).map S
  let u := S.map (fromKernel U z)
  let m := coneMap U cover d z a hc
  let b₁ := (CochainComplex.mappingCone.triangle P.f).mor₃
  let b₂ := (CochainComplex.mappingCone.triangle (S.map d)).mor₃
  let I := (D.commShiftIso (1 : ℤ)).hom
  have he : m ≫ b₂ = b₁ ≫ u⟦(1 : ℤ)⟧' := (coneTriangles U cover d z a hc).comm₃.symm
  have hc' : D.map m ≫ D.map b₂ ≫ I.app (S.obj F) =
      D.map b₁ ≫ I.app P.X₁ ≫ (D.map u)⟦(1 : ℤ)⟧' := by
    have h := (D.map_comp m b₂).symm.trans ((congrArg D.map he).trans (D.map_comp b₁ _))
    refine (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ I.app (S.obj F)) h).trans ((Category.assoc _ _ _).trans ?_))
    exact congrArg (fun g => D.map b₁ ≫ g) (I.naturality u)
  let E := augmentIso U cover
  change (E.inv ≫ D.map m) ≫ D.map b₂ ≫ I.app (S.obj F) = _
  erw [Category.assoc, hc']
  change E.inv ≫ D.map b₁ ≫ I.app P.X₁ ≫ (D.map u)⟦(1 : ℤ)⟧' =
    (E.inv ≫ D.map b₁ ≫ I.app P.X₁) ≫ (D.map u)⟦(1 : ℤ)⟧'
  let v := (D.map u)⟦(1 : ℤ)⟧'
  exact (congrArg (fun k => E.inv ≫ k)
      (Category.assoc (D.map b₁) (I.app P.X₁) v).symm).trans
    (Category.assoc E.inv (D.map b₁ ≫ I.app P.X₁) v).symm

private theorem singleBoundary_eq {C : Type 1} [Category.{0} C] [Abelian C]
    {S : ShortComplex C} (h : S.ShortExact) :
    h.singleδ = DerivedCategory.triangleOfSESδ
      (h.map_of_exact (HomologicalComplex.single C (.up ℤ) 0)) := by
  let I := DerivedCategory.singleFunctorsPostcompQIso C
  let t := DerivedCategory.triangleOfSESδ
    (h.map_of_exact (HomologicalComplex.single C (.up ℤ) 0))
  have ha : (I.hom.hom 0).app S.X₃ = 𝟙 _ :=
    congrArg (fun e => e.app S.X₃) (DerivedCategory.singleFunctorsPostcompQIso_hom_hom C 0)
  have hb : (I.inv.hom 0).app S.X₁ = 𝟙 _ :=
    congrArg (fun e => e.app S.X₁) (DerivedCategory.singleFunctorsPostcompQIso_inv_hom C 0)
  change (I.hom.hom 0).app S.X₃ ≫ t ≫ ((I.inv.hom 0).app S.X₁)⟦(1 : ℤ)⟧' = t
  erw [ha, hb, Category.id_comp]
  let P := shiftFunctor (DerivedCategory C) (1 : ℤ)
  exact (congrArg (fun k => t ≫ k)
    (P.map_id (DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj S.X₁)))).trans
      (Category.comp_id t)

/-- Forgetting the vertex corrections recovers the ordinary coherent edge class. -/
theorem edgeRestriction :
    derivedClass U cover d z a hc ≫ edgeProjection d = (oneDescentClass U z).hom := by
  let H := shortExact U cover
  let u : (sequence U).X₁ ⟶ F := fromKernel U z
  have hd : H.singleδ = DerivedCategory.triangleOfSESδ (liftedShortExact U cover) :=
    singleBoundary_eq H
  have hh : (H.extClass.comp (Ext.mk₀ u) (add_zero 1)).hom =
      H.singleδ ≫ (DerivedCategory.Q.map ((single (X := X)).map u))⟦(1 : ℤ)⟧' := by
    rw [Ext.comp_hom, H.extClass_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
    rfl
  exact (class_edge_projection U cover d z a hc).trans
    ((congrArg (fun k => k ≫ (DerivedCategory.Q.map ((single (X := X)).map u))⟦(1 : ℤ)⟧') hd.symm).trans
      (hh.symm.trans (congrArg Ext.hom (edgeComparison U cover z))))

theorem derivedClass_ne_zero (h : oneDescentClass U z ≠ 0) :
    derivedClass U cover d z a hc ≠ 0 := by
  intro hz
  apply h
  apply Ext.homEquiv.injective
  change (oneDescentClass U z).hom = (0 : (Abelian.Ext (freeOpen (⊤ : Opens X)) F 1)).hom
  exact (edgeRestriction U cover d z a hc).symm.trans
    ((congrArg (fun f => f ≫ edgeProjection d) hz).trans
      ((zero_comp : 0 ≫ edgeProjection d = 0).trans (Ext.zero_hom (X := freeOpen (⊤ : Opens X)) (Y := F) (n := 1)).symm))

end CycleQ2CechUpperClass

#print axioms CycleQ2CechUpperClass.edgeComparison
#print axioms CycleQ2CechUpperClass.derivedClass
#print axioms CycleQ2CechUpperClass.vertexRestriction
#print axioms CycleQ2CechUpperClass.derivedClass_ne_zero

end

section

/-!
# The original corrected residue class in the derived category

The actual edge two-forms and negative vertex corrections form the cone
class on the same four opens. Its edge projection is the original
nonzero coherent class. The ordinary degree-one classes of the genuine
one-form sheaf admit lifts through the sheaf of closed forms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2LiteralDerivedTest

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent
  CycleQ2FiniteCechHOne CycleQ2LiteralThreefoldFirstDifferential
open CycleQ2LiteralThreefoldSecondDifferential (Three secondDifferential vertexThree)
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)
open CycleQ2LiteralThreefoldUnfilteredCech (test_edge_correction)
open CycleQ2LiteralThreefoldHodgeCech (hodgeCocycle)
open CycleQ2LiteralThreefoldTestClass (ambientTestClass face)
open CycleQ2LiteralThreefoldTestEdges (nativeEdge)

private abbrev C := AbSheaf (show TopCat from X)
attribute [local instance] HasDerivedCategory.standard
local instance : HasExt.{1} C := HasExt.standard _

private theorem finiteCoproducts (Y : TopCat.{0}) : HasFiniteCoproducts (AbSheaf Y) := by
  let : HasFiniteBiproducts (AbSheaf Y) := Abelian.hasFiniteBiproducts
  exact hasFiniteCoproducts_of_hasFiniteBiproducts (AbSheaf Y)

local instance : HasCoproductsOfShape (Fin 4) C :=
  (finiteCoproducts (show TopCat from X)).out 4

local instance : HasCoproductsOfShape (Fin 4 × Fin 4) C := by
  let : HasFiniteCoproducts C := finiteCoproducts (show TopCat from X)
  exact hasColimitsOfShape_discrete C (Fin 4 × Fin 4)

private abbrev edges : CycleQ2FiniteInjectiveCech.One Two fixedOpen :=
  (hodgeCocycle nativeEdge face).val

private abbrev vertices : CycleQ2FiniteCechDescent.Zero Three fixedOpen :=
  fun i => -(vertexThree i)

private theorem closedEdges : IsOneCocycle Two fixedOpen edges :=
  fun i j k W hi hj hk => ((hodgeCocycle nativeEdge face).condition i j k W hi hj hk).symm

private def descent : OneDescent fixedOpen edges :=
  Classical.choice (oneDescent_nonempty fixedOpen fixedOpen_cover edges closedEdges)

theorem descentClass_eq :
    oneDescentClass fixedOpen descent = ambientTestClass :=
  (cechOneClass_eq_descentClass fixedOpen fixedOpen_cover edges closedEdges descent).symm

abbrev upperCone := CycleQ2CechUpperClass.upperCone secondDifferential

def fixedClass :
    (DerivedCategory.singleFunctor C 0).obj (freeOpen (⊤ : Opens (show TopCat from X))) ⟶
      DerivedCategory.Q.obj upperCone :=
  CycleQ2CechUpperClass.derivedClass fixedOpen fixedOpen_cover secondDifferential
    descent vertices test_edge_correction

theorem fixedClass_nonzero : fixedClass ≠ 0 := by
  refine CycleQ2CechUpperClass.derivedClass_ne_zero fixedOpen fixedOpen_cover secondDifferential
    descent vertices test_edge_correction ?_
  exact fun h => CycleQ2LiteralNonzeroSweptRestriction.ambient_nonzero (descentClass_eq.symm.trans h)

/-- The degree-zero map attached to the actual corrected vertex form. -/
def vertexMap (i : Fin 4) : freeOpen (fixedOpen i) ⟶ Three :=
  (freeOpenSections Three (fixedOpen i)).symm (vertices i)

theorem fixedClass_vertex (i : Fin 4) :
    DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map
      (freeOpenMap (show fixedOpen i ≤ ⊤ from le_top))) ≫ fixedClass =
    DerivedCategory.Q.map ((CochainComplex.singleFunctor C 0).map (vertexMap i)) ≫
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr
        ((CochainComplex.singleFunctor C 0).map secondDifferential)) :=
  CycleQ2CechUpperClass.vertexRestriction fixedOpen fixedOpen_cover secondDifferential
    descent vertices test_edge_correction i

theorem closed_forms_surjective (x : One.H' 1 ⊤) :
    ∃ a : (kernel differential).H' 1 ⊤, a.comp (Ext.mk₀ (kernel.ι differential)) (add_zero 1) = x :=
  CycleQ2LiteralClosedOneForms.liftHOne CycleQ2LiteralAffineFormAcyclic.localHOne x

end CycleQ2LiteralDerivedTest

#print axioms CycleQ2LiteralDerivedTest.fixedClass_nonzero
#print axioms CycleQ2LiteralDerivedTest.closed_forms_surjective

end

section

/-!
# Attaching consecutive terms of a cochain complex

A map to the first term of a cone with zero composite into the second
term induces a map from its shift to the cone. This construction gives
the successive inclusions of the upper terms of a bounded complex.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2ShiftedCone

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex CochainComplex.mappingCone

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {K L M N : CochainComplex C ℤ}

private def shiftedCocycle (g : K ⟶ L) : Cocycle (K⟦(1 : ℤ)⟧) L 1 :=
  (Cocycle.ofHom (-g)).leftShift 1 1 (zero_add 1)

private theorem shiftedCocycle_comp (g : K ⟶ L) (f : L ⟶ M) (h : g ≫ f = 0) :
    (shiftedCocycle g).1.comp (Cochain.ofHom f) (add_zero 1) = 0 := by
  change ((Cochain.ofHom (-g)).leftShift 1 1 (zero_add 1)).comp
    (Cochain.ofHom f) (add_zero 1) = 0
  rw [← Cochain.leftShift_comp_zero_cochain, ← Cochain.ofHom_comp,
    Preadditive.neg_comp, h, neg_zero, Cochain.ofHom_zero, Cochain.leftShift_zero]

/-- The shifted map enters the first summand of the cone, with no
component in the second summand. -/
def attach (g : K ⟶ L) (f : L ⟶ M) (h : g ≫ f = 0) :
    K⟦(1 : ℤ)⟧ ⟶ mappingCone f :=
  lift f (shiftedCocycle g) 0 (by rw [shiftedCocycle_comp g f h, δ_zero, add_zero])

@[reassoc]
theorem attach_f_fst (g : K ⟶ L) (f : L ⟶ M) (h : g ≫ f = 0) (i : ℤ) :
    (attach g f h).f i ≫ (fst f).1.v i (i + 1) rfl = g.f (i + 1) := by
  rw [attach, lift_f_fst_v]
  change ((Cochain.ofHom (-g)).leftShift 1 1 (zero_add 1)).v i (i + 1) rfl = _
  rw [Cochain.leftShift_v _ _ _ _ _ _ rfl (i + 1) (add_zero _)]
  simp only [shiftFunctorObjXIso, Int.mul_one, Int.sub_self, Int.mul_zero,
    Int.zero_ediv, add_zero, Int.negOnePow_one, Units.neg_smul, one_smul,
    HomologicalComplex.XIsoOfEq_rfl, Cochain.ofHom_v]
  change -(𝟙 (K.X (i + 1)) ≫ (-g.f (i + 1))) = g.f (i + 1)
  exact (congrArg Neg.neg (Category.id_comp (-g.f (i + 1)))).trans (neg_neg _)

@[reassoc]
theorem attach_f_snd (g : K ⟶ L) (f : L ⟶ M) (h : g ≫ f = 0) (i : ℤ) :
    (attach g f h).f i ≫ (snd f).v i i (add_zero i) = 0 := by
  rw [attach, lift_f_snd_v, Cochain.zero_v]

theorem attach_zero (f : L ⟶ M) :
    attach (0 : K ⟶ L) f zero_comp = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ext_to f i (i + 1) rfl
  · simp only [attach_f_fst, zero_f, zero_comp]; rfl
  · rw [attach_f_snd, zero_f, zero_comp]

theorem shift_comp_attach (k : N ⟶ K) (g : K ⟶ L) (f : L ⟶ M) (h : g ≫ f = 0) :
    k⟦(1 : ℤ)⟧' ≫ attach g f h =
      attach (k ≫ g) f (by rw [Category.assoc, h, comp_zero]) := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ext_to f i (i + 1) rfl
  · change (k.f (i + 1) ≫ (attach g f h).f i) ≫ (fst f).1.v i (i + 1) rfl = _
    exact (Category.assoc _ _ _).trans ((congrArg (fun x => k.f (i + 1) ≫ x)
      (attach_f_fst g f h i)).trans (attach_f_fst (k ≫ g) f _ i).symm)
  · change (k.f (i + 1) ≫ (attach g f h).f i) ≫ (snd f).v i i (add_zero i) = _
    exact (Category.assoc _ _ _).trans ((congrArg (fun x => k.f (i + 1) ≫ x)
      (attach_f_snd g f h i)).trans (comp_zero.trans (attach_f_snd (k ≫ g) f _ i).symm))

theorem shift_comp_attach_zero (k : N ⟶ K) (g : K ⟶ L) (f : L ⟶ M)
    (h : g ≫ f = 0) (hk : k ≫ g = 0) :
    k⟦(1 : ℤ)⟧' ≫ attach g f h = 0 := by
  have aux (u : N ⟶ L) (hu : u ≫ f = 0) (hz : u = 0) : attach u f hu = 0 := by
    subst u
    exact attach_zero f
  exact (shift_comp_attach k g f h).trans (aux _ _ hk)

/-- A morphism from a complex whose degree-zero term vanishes to an
object placed in degree zero is zero. -/
theorem hom_to_single_zero (A : C) (hz : Limits.IsZero (L.X 0))
    (f : L ⟶ (CochainComplex.singleFunctor C 0).obj A) : f = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    exact hz.eq_of_src _ _
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A i hi).eq_of_tgt _ _

/-- The cokernel of the top differential can be tested after adding
lower-degree terms to the mapping cone. -/
def extendProjection (f : L ⟶ M) (A : C) (p : M ⟶ (CochainComplex.singleFunctor C 0).obj A)
    (hz : Limits.IsZero (L.X 0)) : mappingCone f ⟶ (CochainComplex.singleFunctor C 0).obj A :=
  desc f 0 p (by rw [hom_to_single_zero A hz (f ≫ p), Cochain.ofHom_zero, δ_zero])

@[reassoc]
theorem inr_extendProjection (f : L ⟶ M) (A : C)
    (p : M ⟶ (CochainComplex.singleFunctor C 0).obj A) (hz : Limits.IsZero (L.X 0)) :
    inr f ≫ extendProjection f A p hz = p :=
  inr_desc f 0 p _

private abbrev singleZero := CochainComplex.singleFunctor C 0

/-- The cone of a differential has its natural map to the cokernel
in degree zero. -/
def cokernelProjection {A B : C} (d : A ⟶ B) :
    mappingCone ((singleZero (C := C)).map d) ⟶ (singleZero (C := C)).obj (cokernel d) :=
  let S := singleZero (C := C)
  desc (S.map d) 0 (S.map (cokernel.π d)) (by
    rw [← S.map_comp, cokernel.condition, S.map_zero, Cochain.ofHom_zero, δ_zero])

@[reassoc]
theorem inr_cokernelProjection {A B : C} (d : A ⟶ B) :
    inr ((singleZero (C := C)).map d) ≫ cokernelProjection d =
      (singleZero (C := C)).map (cokernel.π d) :=
  inr_desc _ 0 _ (by
    rw [← (singleZero (C := C)).map_comp, cokernel.condition, Functor.map_zero,
      Cochain.ofHom_zero, δ_zero])

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- Surjectivity on ordinary degree-one Ext gives the corresponding
factorization through shifted single complexes. -/
theorem factorShiftedSingle [HasExt C] {P A B : C} (k : A ⟶ B)
    (lift : ∀ a : Abelian.Ext P B 1,
      ∃ b : Abelian.Ext P A 1, b.comp (Abelian.Ext.mk₀ k) (add_zero 1) = a)
    (x : DerivedCategory.Q.obj (singleZero.obj P) ⟶
      DerivedCategory.Q.obj ((singleZero.obj B)⟦(1 : ℤ)⟧)) :
    ∃ y : DerivedCategory.Q.obj (singleZero.obj P) ⟶
        DerivedCategory.Q.obj ((singleZero.obj A)⟦(1 : ℤ)⟧),
      y ≫ DerivedCategory.Q.map ((singleZero.map k)⟦(1 : ℤ)⟧') = x := by
  let S := singleZero (C := C)
  let Q := DerivedCategory.Q (C := C)
  let I := Q.commShiftIso (1 : ℤ)
  let a : Ext P B 1 := Ext.homEquiv.symm (x ≫ I.hom.app (S.obj B))
  obtain ⟨b,hb⟩ := lift a
  refine ⟨b.hom ≫ I.inv.app (S.obj A), ?_⟩
  have ha : a.hom = x ≫ I.hom.app (S.obj B) := Ext.homEquiv.apply_symm_apply _
  have hh : (b.comp (Ext.mk₀ k) (add_zero 1)).hom =
      b.hom ≫ (Q.map (S.map k))⟦(1 : ℤ)⟧' := by
    rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
    rfl
  have h := hh.symm.trans (congrArg Ext.hom hb)
  have hs := I.inv.naturality (S.map k)
  exact (Category.assoc _ _ _).trans ((congrArg (fun q => b.hom ≫ q) hs.symm).trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ I.inv.app (S.obj B)) (h.trans ha)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun q => x ≫ q) (I.hom_inv_id_app (S.obj B))).trans
            (Category.comp_id x))))))

/-- If all maps from a fixed source to the attaching term act by zero,
the previous complex embeds on maps from the same source. -/
theorem inclusion_injective {Z : DerivedCategory C} (f : L ⟶ M)
    (h : ∀ x : Z ⟶ DerivedCategory.Q.obj L, x ≫ DerivedCategory.Q.map f = 0) :
    Function.Injective (fun x : Z ⟶ DerivedCategory.Q.obj M =>
      x ≫ DerivedCategory.Q.map (inr f)) := by
  intro a b hab
  apply sub_eq_zero.mp
  let T := DerivedCategory.Q.mapTriangle.obj (triangle f)
  have hz : (a - b) ≫ T.mor₂ = 0 := by
    change (a - b) ≫ DerivedCategory.Q.map (inr f) = 0
    exact (Preadditive.sub_comp _ _ _).trans (sub_eq_zero.mpr hab)
  obtain ⟨x, hx⟩ := T.coyoneda_exact₂ (DerivedCategory.mappingCone_triangle_distinguished f) _ hz
  exact hx.trans (h x)

end Derived

end CycleQ2ShiftedCone

#print axioms CycleQ2ShiftedCone.shift_comp_attach
#print axioms CycleQ2ShiftedCone.inclusion_injective

end

section

/-!
# Nonvanishing of the fixed test in the actual additive de Rham complex

The cone of the second exterior differential is extended downwards
by the original one-form and function sheaves. In the degree of the
test, attaching the one-forms preserves nonvanishing because ordinary
one-form classes lift to closed forms. Attaching functions preserves
nonvanishing by the vanishing of their second coherent cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2LiteralDerivedUnfiltered

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
  CycleQ2InjectiveCech CycleQ2LiteralThreefoldFirstDifferential
  CycleQ2ShiftedCone CochainComplex.mappingCone
open CycleQ2LiteralThreefoldSecondDifferential (Three secondDifferential first_second_zero)
open CycleQ2LiteralDerivedTest (upperCone fixedClass fixedClass_nonzero closed_forms_surjective
  vertexMap fixedClass_vertex)
open CycleQ2LiteralAmbientCharts (fixedOpen)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)

private abbrev C := AbSheaf (show TopCat from X)
attribute [local instance] HasDerivedCategory.standard
local instance : HasExt.{1} C := HasExt.standard _

private abbrev S := CochainComplex.singleFunctor C 0
private abbrev Q := DerivedCategory.Q (C := C)
abbrev Source := Q.obj (S.obj (freeOpen (⊤ : Opens (show TopCat from X))))

private abbrev O := structureAdditiveSheaf X
private abbrev d₀ := S.map functionDifferential
private abbrev d₁ := S.map differential
private abbrev d₂ := S.map secondDifferential

private theorem consecutive_one_two : d₁ ≫ d₂ = 0 :=
  (S.map_comp differential secondDifferential).symm.trans
    ((congrArg S.map first_second_zero).trans (S.map_zero _ _))

private theorem consecutive_zero_one : d₀ ≫ d₁ = 0 :=
  (S.map_comp functionDifferential differential).symm.trans
    ((congrArg S.map function_differential_zero).trans (S.map_zero _ _))

def attachOne : (S.obj One)⟦(1 : ℤ)⟧ ⟶ upperCone :=
  attach d₁ d₂ consecutive_one_two

abbrev middle := CochainComplex.mappingCone attachOne

private theorem attachZero_condition : d₀⟦(1 : ℤ)⟧' ≫ attachOne = 0 := by
  change d₀⟦(1 : ℤ)⟧' ≫ attach d₁ d₂ consecutive_one_two = 0
  exact shift_comp_attach_zero d₀ d₁ d₂ consecutive_one_two consecutive_zero_one

def attachZero : ((S.obj O)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧ ⟶ middle :=
  attach (d₀⟦(1 : ℤ)⟧') attachOne attachZero_condition

/-- The additive de Rham complex placed in degrees minus three to zero. -/
abbrev full := CochainComplex.mappingCone attachZero

private abbrev closedInclusion := kernel.ι differential

private theorem closed_comp_attach :
    (S.map closedInclusion)⟦(1 : ℤ)⟧' ≫ attachOne = 0 := by
  have h : S.map closedInclusion ≫ d₁ = 0 :=
    (S.map_comp closedInclusion differential).symm.trans
      ((congrArg S.map (kernel.condition differential)).trans (S.map_zero _ _))
  change (S.map closedInclusion)⟦(1 : ℤ)⟧' ≫ attach d₁ d₂ consecutive_one_two = 0
  exact shift_comp_attach_zero (S.map closedInclusion) d₁ d₂ consecutive_one_two h

private theorem attachOne_kills (x : Source ⟶ Q.obj ((S.obj One)⟦(1 : ℤ)⟧)) :
    x ≫ Q.map attachOne = 0 := by
  obtain ⟨y,hy⟩ := factorShiftedSingle (C := C) closedInclusion closed_forms_surjective x
  exact (congrArg (fun k => k ≫ Q.map attachOne) hy.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun k => y ≫ k) ((Q.map_comp _ _).symm.trans
      ((congrArg Q.map closed_comp_attach).trans (Q.map_zero _ _)))).trans comp_zero))

private def shiftTwo :
    Q.obj (((S.obj O)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧) ≅ (Q.obj (S.obj O))⟦(2 : ℤ)⟧ :=
  (Q.mapIso ((shiftFunctorAdd' (CochainComplex C ℤ) (1 : ℤ) 1 2 (by decide)).app (S.obj O))).symm ≪≫
    (Q.commShiftIso 2).app (S.obj O)

private theorem attachZero_source_zero
    (x : Source ⟶ Q.obj (((S.obj O)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)) :
    x = 0 := by
  let : Subsingleton (Ext (freeOpen (⊤ : Opens (show TopCat from X))) O 2) :=
    CycleQ2LiteralThreefoldFunctionPrimitives.terminal_two_subsingleton
  have h : Subsingleton (Source ⟶ (Q.obj (S.obj O))⟦(2 : ℤ)⟧) :=
    (Ext.homEquiv (X := freeOpen (⊤ : Opens (show TopCat from X))) (Y := O) (n := 2)).surjective.subsingleton
  apply (cancel_mono shiftTwo.hom).mp
  exact h.elim _ _

def upperToFull : Q.obj upperCone ⟶ Q.obj full :=
  Q.map (inr attachOne) ≫ Q.map (inr attachZero)

theorem upperToFull_injective :
    Function.Injective (fun a : Source ⟶ Q.obj upperCone => a ≫ upperToFull) := by
  have h₁ := inclusion_injective (Z := Source) attachOne attachOne_kills
  have h₀ := inclusion_injective (Z := Source) attachZero
    (fun x => (congrArg (fun y => y ≫ Q.map attachZero) (attachZero_source_zero x)).trans zero_comp)
  intro a b h
  apply h₁
  apply h₀
  exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

def fullClass : Source ⟶ Q.obj full := fixedClass ≫ upperToFull

theorem fullClass_ne_zero : fullClass ≠ 0 := by
  intro h
  apply fixedClass_nonzero
  apply upperToFull_injective
  exact h.trans zero_comp.symm

private theorem zero_shiftedOne :
    IsZero (((S.obj One)⟦(1 : ℤ)⟧).X 0) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 CycleQ2LiteralThreefoldFirstDifferential.One 1 (by decide)

private theorem zero_shiftedFunctions :
    IsZero ((((S.obj O)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧).X 0) :=
  HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 O 2 (by decide)

private def middleProjection : middle ⟶ S.obj (cokernel secondDifferential) :=
  extendProjection attachOne _ (cokernelProjection secondDifferential) zero_shiftedOne

/-- The natural map to the cokernel of the top exterior differential
retains the local top-form class. -/
def fullProjection : full ⟶ S.obj (cokernel secondDifferential) :=
  extendProjection attachZero _ middleProjection zero_shiftedFunctions

private theorem path_projection :
    inr d₂ ≫ inr attachOne ≫ inr attachZero ≫ fullProjection =
      S.map (cokernel.π secondDifferential) := by
  exact (congrArg (fun k => inr d₂ ≫ inr attachOne ≫ k)
      (inr_extendProjection attachZero _ middleProjection zero_shiftedFunctions)).trans
    ((congrArg (fun k => inr d₂ ≫ k)
      (inr_extendProjection attachOne _ (cokernelProjection secondDifferential) zero_shiftedOne)).trans
        (inr_cokernelProjection secondDifferential))

/-- On each original vertex the full test projects to that vertex form
modulo the actual image of the exterior differential. -/
theorem fullClass_vertex_cokernel (i : Fin 4) :
    Q.map (S.map (freeOpenMap (show fixedOpen i ≤ ⊤ from le_top))) ≫
      fullClass ≫ Q.map fullProjection =
    Q.map (S.map (vertexMap i ≫ cokernel.π secondDifferential)) := by
  let v := Q.map (S.map (freeOpenMap (show fixedOpen i ≤ ⊤ from le_top)))
  let w := Q.map (S.map (vertexMap i))
  let u := Q.map (inr attachOne)
  let z := Q.map (inr attachZero)
  let q := Q.map fullProjection
  have hp : Q.map (inr d₂) ≫ u ≫ z ≫ q = Q.map (S.map (cokernel.π secondDifferential)) := by
    dsimp only [u, z, q]
    erw [← Q.map_comp, ← Q.map_comp, ← Q.map_comp, path_projection]
    rfl
  have hw : w ≫ Q.map (S.map (cokernel.π secondDifferential)) =
      Q.map (S.map (vertexMap i ≫ cokernel.π secondDifferential)) :=
    (Q.map_comp _ _).symm.trans (congrArg Q.map (S.map_comp _ _).symm)
  have hv : v ≫ fixedClass = w ≫ Q.map (inr d₂) := fixedClass_vertex i
  change v ≫ (fixedClass ≫ u ≫ z) ≫ q = _
  exact (congrArg (fun k => v ≫ k)
      ((Category.assoc fixedClass (u ≫ z) q).trans
        (congrArg (fun k => fixedClass ≫ k) (Category.assoc u z q)))).trans
    ((Category.assoc v fixedClass (u ≫ z ≫ q)).symm.trans
      ((congrArg (fun k => k ≫ u ≫ z ≫ q) hv).trans
        ((Category.assoc w (Q.map (inr d₂)) (u ≫ z ≫ q)).trans
          ((congrArg (fun k => w ≫ k) hp).trans hw))))

end CycleQ2LiteralDerivedUnfiltered

#print axioms CycleQ2LiteralDerivedUnfiltered.upperToFull_injective
#print axioms CycleQ2LiteralDerivedUnfiltered.fullClass_ne_zero
#print axioms CycleQ2LiteralDerivedUnfiltered.fullClass_vertex_cokernel

end

section

/-!
# A supported derived morphism gives exactness at a function point

If a derived class restricts at a vertex to the actual top form modulo
the last differential, vanishing under the exact stalk functor forces
that form to be a boundary in the stalk. The proof uses the canonical
single-complex comparison of the exact functor and preservation of
the actual cokernel.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2DerivedVertexExactness

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
attribute [local instance] HasDerivedCategory.standard

variable (F : C ⥤ AddCommGrpCat.{v}) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The functor induced on derived categories detects the actual map on
a single sheaf degree, after passing to the original additive functor. -/
theorem map_zero_of_single_map_zero {A B : C} (g : A ⟶ B)
    (h : F.mapDerivedCategory.map ((DerivedCategory.singleFunctor C 0).map g) = 0) :
    F.map g = 0 := by
  let J := F.mapDerivedCategorySingleFunctor 0
  let S := DerivedCategory.singleFunctor AddCommGrpCat.{v} 0
  have hn : F.mapDerivedCategory.map ((DerivedCategory.singleFunctor C 0).map g) ≫ J.hom.app B =
      J.hom.app A ≫ S.map (F.map g) := J.hom.naturality g
  apply S.map_injective
  have hh : S.map (F.map g) = 0 := (cancel_epi (J.hom.app A)).mp
    (hn.symm.trans ((congrArg (fun k => k ≫ J.hom.app B) h).trans (zero_comp.trans comp_zero.symm)))
  exact hh.trans (S.map_zero _ _).symm

private theorem cokernel_preimage {A B : C} (d : A ⟶ B) (b : F.obj B)
    (h : F.map (cokernel.π d) b = 0) : ∃ a : F.obj A, F.map d a = b := by
  let S := ShortComplex.mk d (cokernel.π d) (cokernel.condition d)
  have hs : S.Exact := S.exact_of_g_is_cokernel (cokernelIsCokernel d)
  have hg : (S.map F).Exact := hs.map F
  exact (ShortComplex.ab_exact_iff (S.map F)).mp hg b h

/-- Given the vertex comparison with the genuine cokernel, a derived
class killed by an exact functor has an actual primitive for the
corresponding vertex value after applying that functor. -/
theorem primitive_of_derived_vanishing {P A B : C} (d : A ⟶ B) (w : P ⟶ B)
    {X Y : DerivedCategory C}
    (vertex : (DerivedCategory.singleFunctor C 0).obj P ⟶ X)
    (cohomologyClass : X ⟶ Y)
    (projection : Y ⟶ (DerivedCategory.singleFunctor C 0).obj (cokernel d))
    (comparison : vertex ≫ cohomologyClass ≫ projection =
      (DerivedCategory.singleFunctor C 0).map (w ≫ cokernel.π d))
    (h : F.mapDerivedCategory.map cohomologyClass = 0) (a : F.obj P) :
    ∃ b : F.obj A, F.map d b = F.map w a := by
  have hzero : F.mapDerivedCategory.map ((DerivedCategory.singleFunctor C 0).map
      (w ≫ cokernel.π d)) = 0 := by
    rw [← comparison, Functor.map_comp, Functor.map_comp, h, zero_comp, comp_zero]
  have hmap := map_zero_of_single_map_zero F _ hzero
  have hw : F.map (cokernel.π d) (F.map w a) = 0 :=
    (ConcreteCategory.congr_hom (F.map_comp w (cokernel.π d)) a).symm.trans
      (ConcreteCategory.congr_hom hmap a)
  exact cokernel_preimage F d (F.map w a) hw

end CycleQ2DerivedVertexExactness

#print axioms CycleQ2DerivedVertexExactness.primitive_of_derived_vanishing

end
