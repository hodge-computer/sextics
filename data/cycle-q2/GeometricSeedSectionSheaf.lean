import Proposal.GeometricSeedSectionIdealComparison
import Proposal.GeometricSeedProjectiveImageCocycle
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# The original twisted ideal as a global kernel sheaf

The source below is defined before choosing a section vector.  It is the
kernel of the actual coordinate-chart ideal inclusions on the pairwise
intersections, with the prescribed compatibility x_i = (X_i/X_j)^4 x_j.
Thus its construction retains the negative-fourth-power source transition
and does not define its compatibility using evaluation at a chosen t.

The local ideals are the original OrbitIdeal modules, transported along
the original affine chart isomorphisms and pushed forward to the original
surface.  All objects and morphisms live in Surface.Modules.

The global evaluation and comparison with the closed-curve ideal are
subsequent constructions; no certificate exactness is asserted here.
Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md for the
geometric route, its attribution, and the remaining protected obligation.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheaf

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageCocycle
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2SeedSectionInverse

abbrev structureModule (X : Scheme.{0}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

local instance ringCatSectionsCommRing (X : Scheme.{0}) (O : (Opens X)ᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj O) :=
  inferInstanceAs (CommRing (X.presheaf.obj O))

section StructureMaps

variable {X Y : Scheme.{0}}

/-- The ordinary structure restriction, supplied by the actual open
immersion adjunction and its canonical structure-module identification. -/
def openStructureMap (f : X ⟶ Y) [IsOpenImmersion f] :
    structureModule Y ⟶ (Scheme.Modules.pushforward f).obj (structureModule X) :=
  (Scheme.Modules.restrictAdjunction f).unit.app (structureModule Y) ≫
    (Scheme.Modules.pushforward f).map (Scheme.Modules.restrictUnitIso f).hom

@[simp] theorem openStructureMap_app (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) (a : Γ(Y, U)) :
    (openStructureMap f).app U a = f.app U a := by
  change (f.appIso (f ⁻¹ᵁ U)).hom
      (Y.presheaf.map (homOfLE (f.image_preimage_le U)).op a) = f.app U a
  have h : f.app U = Y.presheaf.map (homOfLE (f.image_preimage_le U)).op ≫
      (f.appIso (f ⁻¹ᵁ U)).hom :=
    (Iso.comp_inv_eq _).mp (f.app_appIso_inv U)
  simpa only [ConcreteCategory.comp_apply] using (ConcreteCategory.congr_hom h a).symm

@[reassoc] theorem openStructureMap_comp {Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    openStructureMap g ≫ (Scheme.Modules.pushforward g).map (openStructureMap f) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app (structureModule X) =
      openStructureMap (f ≫ g) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro a
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    openStructureMap_app]
  erw [openStructureMap_app f]
  exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_app f g U) a).symm

theorem openStructureMap_congr {f g : X ⟶ Y} (h : f = g)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    openStructureMap f ≫ (Scheme.Modules.pushforwardCongr h).hom.app
        (structureModule X) = openStructureMap g := by
  subst g
  apply Scheme.Modules.hom_ext
  intro U
  simp only [Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, eqToHom_refl, op_id]
  apply ConcreteCategory.hom_ext
  intro a
  change X.presheaf.map (𝟙 (op (f ⁻¹ᵁ U))) ((openStructureMap f).app U a) =
    (openStructureMap f).app U a
  erw [X.presheaf.map_id (op (f ⁻¹ᵁ U))]
  rfl

/-- Multiplication by one actual global regular function on every open. -/
def structureScalar (X : Scheme.{0}) (a : Γ(X, ⊤)) :
    structureModule X ⟶ structureModule X where
  val.app O := ModuleCat.ofHom (R := X.ringCatSheaf.obj.obj O)
    { toFun := fun b =>
        (show X.ringCatSheaf.obj.obj O from
          X.presheaf.map (homOfLE (show O.unop ≤ ⊤ from le_top)).op a) *
            (show X.ringCatSheaf.obj.obj O from b)
      map_add' := by intro b c; exact mul_add _ _ _
      map_smul' := by
        intro b c
        change _ * (b * c) = b * (_ * c)
        ring }
  val.naturality {O P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change (show Γ(X, P.unop) from
        X.presheaf.map (homOfLE (show P.unop ≤ ⊤ from le_top)).op a) *
        (show Γ(X, P.unop) from X.presheaf.map f b) =
      X.presheaf.map f
        ((show Γ(X, O.unop) from
          X.presheaf.map (homOfLE (show O.unop ≤ ⊤ from le_top)).op a) *
            (show Γ(X, O.unop) from b))
    rw [map_mul]
    congr 1
    change X.presheaf.map _ a =
      (X.presheaf.map (homOfLE (show O.unop ≤ ⊤ from le_top)).op ≫
        X.presheaf.map f) a
    rw [← Functor.map_comp]
    exact congrArg (fun h => X.presheaf.map h a) (Subsingleton.elim _ _)

@[simp] theorem structureScalar_app (X : Scheme.{0}) (a : Γ(X, ⊤))
    (O : X.Opens) (b : Γ(X, O)) :
    (structureScalar X a).app O b =
      X.presheaf.map (homOfLE (show O ≤ ⊤ from le_top)).op a * b := rfl

/-- Pushforward of the structure module of an actual open. -/
def patchStructure (U : Surface.Opens) : Surface.Modules :=
  (Scheme.Modules.pushforward U.ι).obj (structureModule U.toScheme)

/-- The restriction from one actual patch to an actual subpatch. -/
def patchStructureRestriction {U V : Surface.Opens} (h : V ≤ U) :
    patchStructure U ⟶ patchStructure V :=
  (Scheme.Modules.pushforward U.ι).map
      (openStructureMap (Surface.homOfLE h)) ≫
    (Scheme.Modules.pushforwardComp (Surface.homOfLE h) U.ι).hom.app
      (structureModule V.toScheme) ≫
    (Scheme.Modules.pushforwardCongr
      (show Surface.homOfLE h ≫ U.ι = V.ι by simp)).hom.app
        (structureModule V.toScheme)

theorem structureMap_patchRestriction {U V : Surface.Opens} (h : V ≤ U) :
    openStructureMap U.ι ≫ patchStructureRestriction h = openStructureMap V.ι := by
  dsimp only [patchStructureRestriction, patchStructure]
  erw [openStructureMap_comp_assoc (Surface.homOfLE h) U.ι]
  exact openStructureMap_congr (by simp)

end StructureMaps

/-! ## The original ideal sheaves and their literal inclusions -/

def affineIdeal (i : Fin 3) : (Spec (CommRingCat.of (AffineRing i))).Modules :=
  tilde (ModuleCat.of (AffineRing i) (OrbitIdeal i))

def affineInclusion (i : Fin 3) :
    affineIdeal i ⟶ structureModule (Spec (CommRingCat.of (AffineRing i))) :=
  tilde.map (ModuleCat.ofHom (OrbitIdeal i).subtype) ≫
    (tildeSelf (R := CommRingCat.of (AffineRing i))).hom

def chartIdeal (i : Fin 3) : (Patch i).toScheme.Modules :=
  (Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).obj
    (affineIdeal i)

def chartInclusion (i : Fin 3) : chartIdeal i ⟶ structureModule (Patch i).toScheme :=
  (Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).map
      (affineInclusion i) ≫
    (Scheme.Modules.restrictUnitIso (coordinateAffineChart 57 1 i.succ).hom).hom

/-- These are pushforwards of the actual chart ideals, not free modules
chosen to model an unspecified line bundle. -/
def idealPatch (i : Fin 3) : Surface.Modules :=
  (Scheme.Modules.pushforward (Patch i).ι).obj (chartIdeal i)

def idealPatchInclusion (i : Fin 3) : idealPatch i ⟶ patchStructure (Patch i) :=
  (Scheme.Modules.pushforward (Patch i).ι).map (chartInclusion i)

abbrev PairPatch (i j : Fin 3) : Surface.Opens := Patch i ⊓ Patch j

def pairTwist (i j : Fin 3) :
    patchStructure (PairPatch i j) ⟶ patchStructure (PairPatch i j) :=
  (Scheme.Modules.pushforward (PairPatch i j).ι).map
    (structureScalar (PairPatch i j).toScheme
      ((PairPatch i j).topIso.inv
        ((transitionUnit i j (PairPatch i j) inf_le_left inf_le_right :
          Γ(Surface, PairPatch i j)) ^ 4)))

def leftIdealToPair (i j : Fin 3) :
    idealPatch i ⟶ patchStructure (PairPatch i j) :=
  idealPatchInclusion i ≫ patchStructureRestriction inf_le_left

def rightIdealToPair (i j : Fin 3) :
    idealPatch j ⟶ patchStructure (PairPatch i j) :=
  idealPatchInclusion j ≫ patchStructureRestriction inf_le_right

def idealProduct : Surface.Modules := ∏ᶜ idealPatch

def overlapProduct : Surface.Modules :=
  ∏ᶜ (fun p : Fin 3 × Fin 3 => patchStructure (PairPatch p.1 p.2))

/-- The source descent condition is fixed independently of the chosen
curve parameter: x_i = u_ij^4*x_j in the actual overlap structure sheaf. -/
def twistedDifference : idealProduct ⟶ overlapProduct :=
  Pi.lift fun p : Fin 3 × Fin 3 =>
    Pi.π idealPatch p.1 ≫ leftIdealToPair p.1 p.2 -
      Pi.π idealPatch p.2 ≫ rightIdealToPair p.1 p.2 ≫ pairTwist p.1 p.2

/-- A genuine global sheaf defined by the original ideals and the
prescribed negative fourth-power transition. No section vector occurs. -/
def twistedIdeal : Surface.Modules := kernel twistedDifference

def chartProjection (i : Fin 3) : twistedIdeal ⟶ idealPatch i :=
  kernel.ι twistedDifference ≫ Pi.π idealPatch i

/-- The actual global source has its required literal overlap relation. -/
theorem chartProjection_compatibility (i j : Fin 3) :
    chartProjection i ≫ leftIdealToPair i j =
      chartProjection j ≫ rightIdealToPair i j ≫ pairTwist i j := by
  apply sub_eq_zero.mp
  have h := congrArg
    (fun f : twistedIdeal ⟶ overlapProduct =>
      f ≫ Pi.π (fun p : Fin 3 × Fin 3 => patchStructure (PairPatch p.1 p.2)) (i, j))
    (kernel.condition twistedDifference)
  simpa only [twistedDifference, chartProjection, Category.assoc,
    Pi.lift_π, Preadditive.comp_sub, Limits.zero_comp] using h

/-! ## Evaluation by the unchanged original vector -/

def affineEvaluation (t : Fin 3 → ℂ) (i : Fin 3) :
    affineIdeal i ⟶ structureModule (Spec (CommRingCat.of (AffineRing i))) :=
  tilde.map (ModuleCat.ofHom
      (sectionFunctional (chartFactorData i) (fun b => algebraMap ℂ (AffineRing i) (t b)))) ≫
    (tildeSelf (R := CommRingCat.of (AffineRing i))).hom

def chartEvaluation (t : Fin 3 → ℂ) (i : Fin 3) :
    chartIdeal i ⟶ structureModule (Patch i).toScheme :=
  (Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).map
      (affineEvaluation t i) ≫
    (Scheme.Modules.restrictUnitIso (coordinateAffineChart 57 1 i.succ).hom).hom

def patchEvaluation (t : Fin 3 → ℂ) (i : Fin 3) :
    idealPatch i ⟶ patchStructure (Patch i) :=
  (Scheme.Modules.pushforward (Patch i).ι).map (chartEvaluation t i)

/-- Each component of evaluation starts on the fixed twisted source and
uses exactly the original affine functional transported by its chart. -/
def localEvaluation (t : Fin 3 → ℂ) (i : Fin 3) :
    twistedIdeal ⟶ patchStructure (Patch i) :=
  chartProjection i ≫ patchEvaluation t i

end CycleQ2SeedSectionSheaf

end

#print axioms CycleQ2SeedSectionSheaf.twistedIdeal
#print axioms CycleQ2SeedSectionSheaf.chartProjection_compatibility
#print axioms CycleQ2SeedSectionSheaf.localEvaluation
