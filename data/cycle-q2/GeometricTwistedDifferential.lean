import Proposal.GeometricTwistedModuleCore
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Proposal.GeometricDifferentialSheaf
import Proposal.GeometricAffineOverlap
import Proposal.GeometricAffineDifferentialSheaf
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

section ConsolidatedGeometricTwistedDifferential

section SourceGeometricTwistedFrameMap

/-!
# Gluing actual local frames into a morphism of sheaves of modules

Two sections with the specified transition define a morphism from the
existing twisted kernel sheaf to an arbitrary sheaf of structure modules.
The map is obtained by genuine sheaf gluing of the two scalar multiples.
Its restriction formulas, linearity, and naturality refer to the original
sections and restriction maps.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricTwistedFrameMap

open CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricProjectiveCurve

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
variable (M : SheafOfModules.{0} (TwistedModule.ringSheaf R))

abbrev Sections (O : Opens X) := M.val.obj (op O)

def restrict {O P : Opens X} (h : P ≤ O) (s : Sections R M O) : Sections R M P :=
  M.val.map (homOfLE h).op s

@[simp] theorem restrict_self (O : Opens X) (s : Sections R M O) :
    restrict R M (le_refl O) s = s := by
  change M.val.presheaf.map (𝟙 (op O)) s = s
  rw [M.val.presheaf.map_id]
  rfl

theorem restrict_comp {O P Q : Opens X} (hPO : P ≤ O) (hQP : Q ≤ P)
    (s : Sections R M O) :
    restrict R M hQP (restrict R M hPO s) = restrict R M (hQP.trans hPO) s := by
  exact (M.val.map_comp_apply (homOfLE hPO).op (homOfLE hQP).op s).symm

@[simp] theorem restrict_add {O P : Opens X} (h : P ≤ O) (s t : Sections R M O) :
    restrict R M h (s + t) = restrict R M h s + restrict R M h t :=
  map_add _ _ _

theorem restrict_smul {O P : Opens X} (h : P ≤ O)
    (a : R.obj.obj (op O)) (s : Sections R M O) :
    restrict R M h (a • s) = Twisted.res R h a • restrict R M h s :=
  M.val.map_smul (homOfLE h).op a s

def underlyingSheaf : X.Sheaf AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf (TwistedModule.ringSheaf R)).obj M

theorem sections_ext₂ {U V O : Opens X} (hU : U ≤ O) (hV : V ≤ O)
    (hcover : O ≤ U ⊔ V) (s t : Sections R M O)
    (h₁ : restrict R M hU s = restrict R M hU t)
    (h₂ : restrict R M hV s = restrict R M hV t) : s = t :=
  (underlyingSheaf R M).eq_of_locally_eq₂ (homOfLE hU) (homOfLE hV) hcover s t h₁ h₂

theorem existsUnique_glueTwo {U V O : Opens X} (hU : U ≤ O) (hV : V ≤ O)
    (hcover : O ≤ U ⊔ V) (s : Sections R M U) (t : Sections R M V)
    (hcompat : restrict R M (show U ⊓ V ≤ U from inf_le_left) s =
      restrict R M (show U ⊓ V ≤ V from inf_le_right) t) :
    ∃! w : Sections R M O, restrict R M hU w = s ∧ restrict R M hV w = t := by
  let B : Bool → Opens X := fun b => if b then U else V
  let sf : ∀ b, Sections R M (B b) := fun b => by
    cases b
    · exact t
    · exact s
  have hB : O ≤ iSup B := hcover.trans (sup_le (le_iSup B true) (le_iSup B false))
  have hBO : ∀ b, B b ≤ O := by rintro (_ | _) <;> assumption
  have hc : TopCat.Presheaf.IsCompatible (underlyingSheaf R M).obj B sf := by
    rintro (_ | _) (_ | _)
    · rfl
    · change restrict R M (show V ⊓ U ≤ V from inf_le_left) t =
        restrict R M (show V ⊓ U ≤ U from inf_le_right) s
      have hh := congrArg (restrict R M (show V ⊓ U ≤ U ⊓ V from
        le_inf inf_le_right inf_le_left)) hcompat
      simpa only [restrict_comp] using hh.symm
    · exact hcompat
    · rfl
  obtain ⟨w, hw, hu⟩ := (underlyingSheaf R M).existsUnique_gluing' B O
    (fun b => homOfLE (hBO b)) hB sf hc
  refine ⟨w, ⟨hw true, hw false⟩, ?_⟩
  intro w' hw'
  apply hu w'
  rintro (_ | _)
  · exact hw'.2
  · exact hw'.1

def glueTwo {U V O : Opens X} (hU : U ≤ O) (hV : V ≤ O)
    (hcover : O ≤ U ⊔ V) (s : Sections R M U) (t : Sections R M V)
    (hcompat : restrict R M (show U ⊓ V ≤ U from inf_le_left) s =
      restrict R M (show U ⊓ V ≤ V from inf_le_right) t) : Sections R M O :=
  Classical.choose (existsUnique_glueTwo R M hU hV hcover s t hcompat)

theorem glueTwo_first {U V O : Opens X} (hU : U ≤ O) (hV : V ≤ O)
    (hcover : O ≤ U ⊔ V) (s : Sections R M U) (t : Sections R M V)
    (hcompat : restrict R M (show U ⊓ V ≤ U from inf_le_left) s =
      restrict R M (show U ⊓ V ≤ V from inf_le_right) t) :
    restrict R M hU (glueTwo R M hU hV hcover s t hcompat) = s :=
  (Classical.choose_spec (existsUnique_glueTwo R M hU hV hcover s t hcompat)).1.1

theorem glueTwo_second {U V O : Opens X} (hU : U ≤ O) (hV : V ≤ O)
    (hcover : O ≤ U ⊔ V) (s : Sections R M U) (t : Sections R M V)
    (hcompat : restrict R M (show U ⊓ V ≤ U from inf_le_left) s =
      restrict R M (show U ⊓ V ≤ V from inf_le_right) t) :
    restrict R M hV (glueTwo R M hU hV hcover s t hcompat) = t :=
  (Classical.choose_spec (existsUnique_glueTwo R M hU hV hcover s t hcompat)).1.2

variable (U V W : Opens X) (hW : W = U ⊓ V)
  (t : (R.obj.obj (op W))ˣ) (hcover : U ⊔ V = ⊤)
  (ηU : Sections R M U) (ηV : Sections R M V)
  (hη : restrict R M (hW.le.trans inf_le_right) ηV =
    (t : R.obj.obj (op W)) • restrict R M (hW.le.trans inf_le_left) ηU)

def firstValue (O : Opens X) (p : Twisted.Pairs R U V W hW t O) : Sections R M (O ⊓ U) :=
  p.val.1 • restrict R M (show O ⊓ U ≤ U from inf_le_right) ηU

def secondValue (O : Opens X) (p : Twisted.Pairs R U V W hW t O) : Sections R M (O ⊓ V) :=
  p.val.2 • restrict R M (show O ⊓ V ≤ V from inf_le_right) ηV

include hη in
theorem values_compatible_on_overlap (O : Opens X) (p : Twisted.Pairs R U V W hW t O) :
    restrict R M (inf_le_inf_left O (hW.le.trans inf_le_left))
        (firstValue R M U V W hW t ηU O p) =
      restrict R M (inf_le_inf_left O (hW.le.trans inf_le_right))
        (secondValue R M U V W hW t ηV O p) := by
  have hp : Twisted.res R (inf_le_inf_left O (hW.le.trans inf_le_left)) p.val.1 =
      Twisted.res R (show O ⊓ W ≤ W from inf_le_right) (t : _) *
        Twisted.res R (inf_le_inf_left O (hW.le.trans inf_le_right)) p.val.2 :=
    sub_eq_zero.mp p.property
  have hframe := congrArg (restrict R M (show O ⊓ W ≤ W from inf_le_right)) hη
  rw [restrict_smul, restrict_comp, restrict_comp] at hframe
  unfold firstValue secondValue
  rw [restrict_smul, restrict_smul, restrict_comp, restrict_comp, hp, hframe]
  rw [mul_smul, smul_comm]

include hη in
theorem values_compatible (O : Opens X) (p : Twisted.Pairs R U V W hW t O) :
    restrict R M (show (O ⊓ U) ⊓ (O ⊓ V) ≤ O ⊓ U from inf_le_left)
        (firstValue R M U V W hW t ηU O p) =
      restrict R M (show (O ⊓ U) ⊓ (O ⊓ V) ≤ O ⊓ V from inf_le_right)
        (secondValue R M U V W hW t ηV O p) := by
  have hsub : (O ⊓ U) ⊓ (O ⊓ V) ≤ O ⊓ W := by
    rw [hW]
    exact le_inf (inf_le_left.trans inf_le_left)
      (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
  have h := congrArg (restrict R M hsub)
    (values_compatible_on_overlap R M U V W hW t ηU ηV hη O p)
  simpa only [restrict_comp] using h

include hcover in
theorem intersect_cover (O : Opens X) : O ≤ (O ⊓ U) ⊔ (O ⊓ V) := by
  rw [← inf_sup_left, hcover, inf_top_eq]

def gluePair (O : Opens X) (p : Twisted.Pairs R U V W hW t O) : Sections R M O :=
  glueTwo R M inf_le_left inf_le_left (intersect_cover U V hcover O)
    (firstValue R M U V W hW t ηU O p) (secondValue R M U V W hW t ηV O p)
    (values_compatible R M U V W hW t ηU ηV hη O p)

theorem gluePair_first (O : Opens X) (p : Twisted.Pairs R U V W hW t O) :
    restrict R M (show O ⊓ U ≤ O from inf_le_left)
      (gluePair R M U V W hW t hcover ηU ηV hη O p) =
        firstValue R M U V W hW t ηU O p :=
  glueTwo_first R M inf_le_left inf_le_left (intersect_cover U V hcover O) _ _ _

theorem gluePair_second (O : Opens X) (p : Twisted.Pairs R U V W hW t O) :
    restrict R M (show O ⊓ V ≤ O from inf_le_left)
      (gluePair R M U V W hW t hcover ηU ηV hη O p) =
        secondValue R M U V W hW t ηV O p :=
  glueTwo_second R M inf_le_left inf_le_left (intersect_cover U V hcover O) _ _ _

def sectionFrameMap (O : Opens X) (s : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    Sections R M O :=
  gluePair R M U V W hW t hcover ηU ηV hη O (Twisted.sectionPairsEquiv R U V W hW t O s)

theorem sectionFrameMap_first (O : Opens X)
    (s : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    restrict R M (show O ⊓ U ≤ O from inf_le_left)
        (sectionFrameMap R M U V W hW t hcover ηU ηV hη O s) =
      (Twisted.sectionPairsEquiv R U V W hW t O s).val.1 •
        restrict R M (show O ⊓ U ≤ U from inf_le_right) ηU :=
  gluePair_first R M U V W hW t hcover ηU ηV hη O _

theorem sectionFrameMap_second (O : Opens X)
    (s : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    restrict R M (show O ⊓ V ≤ O from inf_le_left)
        (sectionFrameMap R M U V W hW t hcover ηU ηV hη O s) =
      (Twisted.sectionPairsEquiv R U V W hW t O s).val.2 •
        restrict R M (show O ⊓ V ≤ V from inf_le_right) ηV :=
  gluePair_second R M U V W hW t hcover ηU ηV hη O _

theorem sectionFrameMap_add (O : Opens X)
    (s s' : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    sectionFrameMap R M U V W hW t hcover ηU ηV hη O (s + s') =
      sectionFrameMap R M U V W hW t hcover ηU ηV hη O s +
        sectionFrameMap R M U V W hW t hcover ηU ηV hη O s' := by
  apply sections_ext₂ R M inf_le_left inf_le_left (intersect_cover U V hcover O)
  · rw [restrict_add, sectionFrameMap_first, sectionFrameMap_first, sectionFrameMap_first, map_add]
    exact add_smul _ _ _
  · rw [restrict_add, sectionFrameMap_second, sectionFrameMap_second, sectionFrameMap_second, map_add]
    exact add_smul _ _ _

theorem sectionFrameMap_smul (O : Opens X) (a : R.obj.obj (op O))
    (s : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    sectionFrameMap R M U V W hW t hcover ηU ηV hη O (a • s) =
      a • sectionFrameMap R M U V W hW t hcover ηU ηV hη O s := by
  apply sections_ext₂ R M inf_le_left inf_le_left (intersect_cover U V hcover O)
  · rw [restrict_smul, sectionFrameMap_first, sectionFrameMap_first,
      TwistedModule.sectionPairs_fst_smul, mul_smul]
  · rw [restrict_smul, sectionFrameMap_second, sectionFrameMap_second,
      TwistedModule.sectionPairs_snd_smul, mul_smul]

def sectionLinearMap (O : Opens X) :
    (Twisted.sheaf R U V W hW t).obj.obj (op O) →ₗ[R.obj.obj (op O)] Sections R M O where
  toFun := sectionFrameMap R M U V W hW t hcover ηU ηV hη O
  map_add' := sectionFrameMap_add R M U V W hW t hcover ηU ηV hη O
  map_smul' := sectionFrameMap_smul R M U V W hW t hcover ηU ηV hη O

theorem sectionFrameMap_naturality {O P : Opens X} (h : P ≤ O)
    (s : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    sectionFrameMap R M U V W hW t hcover ηU ηV hη P
        ((Twisted.sheaf R U V W hW t).obj.map (homOfLE h).op s) =
      restrict R M h (sectionFrameMap R M U V W hW t hcover ηU ηV hη O s) := by
  apply sections_ext₂ R M inf_le_left inf_le_left (intersect_cover U V hcover P)
  · have hright : restrict R M (show P ⊓ U ≤ P from inf_le_left)
        (restrict R M h (sectionFrameMap R M U V W hW t hcover ηU ηV hη O s)) =
      Twisted.res R (inf_le_inf_right U h) (Twisted.sectionPairsEquiv R U V W hW t O s).val.1 •
        restrict R M (show P ⊓ U ≤ U from inf_le_right) ηU := by
      calc
        _ = restrict R M (inf_le_inf_right U h)
            (restrict R M (show O ⊓ U ≤ O from inf_le_left)
              (sectionFrameMap R M U V W hW t hcover ηU ηV hη O s)) := by
          rw [restrict_comp, restrict_comp]
        _ = _ := by rw [sectionFrameMap_first, restrict_smul, restrict_comp]
    rw [hright, sectionFrameMap_first, Twisted.sectionPairs_fst_naturality]
  · have hright : restrict R M (show P ⊓ V ≤ P from inf_le_left)
        (restrict R M h (sectionFrameMap R M U V W hW t hcover ηU ηV hη O s)) =
      Twisted.res R (inf_le_inf_right V h) (Twisted.sectionPairsEquiv R U V W hW t O s).val.2 •
        restrict R M (show P ⊓ V ≤ V from inf_le_right) ηV := by
      calc
        _ = restrict R M (inf_le_inf_right V h)
            (restrict R M (show O ⊓ V ≤ O from inf_le_left)
              (sectionFrameMap R M U V W hW t hcover ηU ηV hη O s)) := by
          rw [restrict_comp, restrict_comp]
        _ = _ := by rw [sectionFrameMap_second, restrict_smul, restrict_comp]
    rw [hright, sectionFrameMap_second, Twisted.sectionPairs_snd_naturality]

/-- The actual sheaf morphism supplied by the two local frame sections. -/
def frameMorphism : TwistedModule.moduleSheaf R U V W hW t ⟶ M where
  val :=
    { app O := by
        letI : Module ((TwistedModule.ringSheaf R).obj.obj O)
            ((Twisted.sheaf R U V W hW t).obj.obj O) :=
          TwistedModule.sectionsModule R U V W hW t O.unop
        exact ModuleCat.ofHom (sectionLinearMap R M U V W hW t hcover ηU ηV hη O.unop)
      naturality {O P} f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro s
        have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
        change sectionFrameMap R M U V W hW t hcover ηU ηV hη P.unop
          ((Twisted.sheaf R U V W hW t).obj.map f s) =
            M.val.map f (sectionFrameMap R M U V W hW t hcover ηU ηV hη O.unop s)
        rw [hf]
        exact sectionFrameMap_naturality R M U V W hW t hcover ηU ηV hη
          (leOfHom f.unop) s }

@[simp] theorem frameMorphism_apply (O : Opens X)
    (s : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    (frameMorphism R M U V W hW t hcover ηU ηV hη).val.app (op O) s =
      sectionFrameMap R M U V W hW t hcover ηU ηV hη O s := rfl

/-- On any subopen of the first chart, the map is multiplication by the
restricted first frame in the existing trivialization of the twisted sheaf. -/
theorem frameMorphism_first_local (O : Opens X) (hO : O ≤ U)
    (s : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    (frameMorphism R M U V W hW t hcover ηU ηV hη).val.app (op O) s =
      Twisted.firstLocalSectionsEquiv R U V W hW t O hO s • restrict R M hO ηU := by
  have h := congrArg (restrict R M (le_inf le_rfl hO))
    (sectionFrameMap_first R M U V W hW t hcover ηU ηV hη O s)
  rw [restrict_comp, restrict_smul, restrict_comp, restrict_self] at h
  exact h

/-- The analogous formula in the second chart. -/
theorem frameMorphism_second_local (O : Opens X) (hO : O ≤ V)
    (s : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    (frameMorphism R M U V W hW t hcover ηU ηV hη).val.app (op O) s =
      Twisted.secondLocalSectionsEquiv R U V W hW t O hO s • restrict R M hO ηV := by
  have h := congrArg (restrict R M (le_inf le_rfl hO))
    (sectionFrameMap_second R M U V W hW t hcover ηU ηV hη O s)
  rw [restrict_comp, restrict_smul, restrict_comp, restrict_self] at h
  exact h

#print axioms gluePair
#print axioms frameMorphism
#print axioms sectionFrameMap_naturality
#print axioms frameMorphism_first_local

end CycleQ2GeometricTwistedFrameMap
end

/-!
# The inverse criterion for two glued frames

A morphism back to the twisted sheaf is a left inverse to the glued frame
map as soon as it sends each of the two actual frame sections to coefficient
one. The proof propagates these two equalities by naturality to every open
and then uses separatedness on the actual two-open cover.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricTwistedFrameInverse

open CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricTwistedFrameMap

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})

theorem morphism_restrict
    (M N : SheafOfModules.{0} (TwistedModule.ringSheaf R)) (g : M ⟶ N)
    {O P : Opens X} (h : P ≤ O) (s : Sections R M O) :
    g.val.app (op P) (restrict R M h s) = restrict R N h (g.val.app (op O) s) :=
  PresheafOfModules.naturality_apply g.val (homOfLE h).op s

variable (M : SheafOfModules.{0} (TwistedModule.ringSheaf R))
  (U V W : Opens X) (hW : W = U ⊓ V) (t : (R.obj.obj (op W))ˣ)
  (hcover : U ⊔ V = ⊤) (ηU : Sections R M U) (ηV : Sections R M V)
  (hη : restrict R M (hW.le.trans inf_le_right) ηV =
    (t : R.obj.obj (op W)) • restrict R M (hW.le.trans inf_le_left) ηU)
  (g : M ⟶ TwistedModule.moduleSheaf R U V W hW t)
  (hU : Twisted.firstLocalSectionsEquiv R U V W hW t U le_rfl
    (g.val.app (op U) ηU) = 1)
  (hV : Twisted.secondLocalSectionsEquiv R U V W hW t V le_rfl
    (g.val.app (op V) ηV) = 1)

include hU in
theorem first_normalization (O : Opens X) (hO : O ≤ U) :
    Twisted.firstLocalSectionsEquiv R U V W hW t O hO
      (g.val.app (op O) (restrict R M hO ηU)) = 1 := by
  rw [morphism_restrict]
  change Twisted.firstLocalSectionsEquiv R U V W hW t O hO
    ((Twisted.sheaf R U V W hW t).obj.map (homOfLE hO).op (g.val.app (op U) ηU)) = 1
  rw [Twisted.firstLocalSectionsEquiv_naturality R U V W hW t hO le_rfl, hU, map_one]

include hV in
theorem second_normalization (O : Opens X) (hO : O ≤ V) :
    Twisted.secondLocalSectionsEquiv R U V W hW t O hO
      (g.val.app (op O) (restrict R M hO ηV)) = 1 := by
  rw [morphism_restrict]
  change Twisted.secondLocalSectionsEquiv R U V W hW t O hO
    ((Twisted.sheaf R U V W hW t).obj.map (homOfLE hO).op (g.val.app (op V) ηV)) = 1
  rw [Twisted.secondLocalSectionsEquiv_naturality R U V W hW t hO le_rfl, hV, map_one]

include hU in
theorem first_inverse (O : Opens X) (hO : O ≤ U)
    (s : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    g.val.app (op O) ((frameMorphism R M U V W hW t hcover ηU ηV hη).val.app (op O) s) = s := by
  rw [frameMorphism_first_local R M U V W hW t hcover ηU ηV hη O hO, map_smul]
  apply (Twisted.firstLocalSectionsEquiv R U V W hW t O hO).injective
  rw [TwistedModule.firstLocalSections_smul,
    first_normalization R M U V W hW t ηU g hU O hO, mul_one]

include hV in
theorem second_inverse (O : Opens X) (hO : O ≤ V)
    (s : (Twisted.sheaf R U V W hW t).obj.obj (op O)) :
    g.val.app (op O) ((frameMorphism R M U V W hW t hcover ηU ηV hη).val.app (op O) s) = s := by
  rw [frameMorphism_second_local R M U V W hW t hcover ηU ηV hη O hO, map_smul]
  apply (Twisted.secondLocalSectionsEquiv R U V W hW t O hO).injective
  rw [TwistedModule.secondLocalSections_smul,
    second_normalization R M U V W hW t ηV g hV O hO, mul_one]

include hU hV in
/-- Normalizing the two frame sections proves the full inverse identity
on the original twisted sheaf of modules. -/
theorem frameMorphism_comp :
    frameMorphism R M U V W hW t hcover ηU ηV hη ≫ g =
      𝟙 (TwistedModule.moduleSheaf R U V W hW t) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro O
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change g.val.app O ((frameMorphism R M U V W hW t hcover ηU ηV hη).val.app O s) = s
  apply sections_ext₂ R (TwistedModule.moduleSheaf R U V W hW t)
    inf_le_left inf_le_left (intersect_cover U V hcover O.unop)
  · rw [← morphism_restrict, ← morphism_restrict]
    exact first_inverse R M U V W hW t hcover ηU ηV hη g hU
      (O.unop ⊓ U) inf_le_right _
  · rw [← morphism_restrict, ← morphism_restrict]
    exact second_inverse R M U V W hW t hcover ηU ηV hη g hV
      (O.unop ⊓ V) inf_le_right _

#print axioms frameMorphism_comp

end CycleQ2GeometricTwistedFrameInverse
end

end SourceGeometricTwistedFrameMap

section SourceGeometricTwistedDifferential

/-!
# Gluing local differential coefficients into the actual twisted sheaf

Natural coefficient derivations on two open charts glue by the specified
transition unit. The resulting derivation takes values in the original
twisted kernel module sheaf. The universal property of the genuine
differential sheaf then supplies its coefficient morphism.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricTwistedDifferential

open CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricDifferentialSheaf

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤))

/-- A derivation coefficient on every subopen of a chart, using the actual
ring restrictions and the actual global complex coefficient map. -/
structure LocalCoefficient (U : Opens X) where
  app (O : Opens X) (hO : O ≤ U) : R.obj.obj (op O) →+ R.obj.obj (op O)
  leibniz (O : Opens X) (hO : O ≤ U) (a b : R.obj.obj (op O)) :
    app O hO (a * b) = a * app O hO b + b * app O hO a
  naturality {O P : Opens X} (h : P ≤ O) (hO : O ≤ U) (hP : P ≤ U)
      (a : R.obj.obj (op O)) :
    app P hP (Twisted.res R h a) = Twisted.res R h (app O hO a)
  coefficient (O : Opens X) (hO : O ≤ U) (z : ℂ) : app O hO (coefficientOn R c O z) = 0

theorem coefficientOn_restrict {O P : Opens X} (h : P ≤ O) (z : ℂ) :
    Twisted.res R h (coefficientOn R c O z) = coefficientOn R c P z :=
  (CategoryTheory.congr_fun ((coefficientMap R c).naturality (homOfLE h).op) z).symm

variable (U V W : Opens X) (hW : W = U ⊓ V) (t : (R.obj.obj (op W))ˣ)
  (dU : LocalCoefficient R c U) (dV : LocalCoefficient R c V)

def Compatible : Prop :=
  ∀ (O : Opens X) (hO : O ≤ W) (a : R.obj.obj (op O)),
    dU.app O (hO.trans (hW.le.trans inf_le_left)) a =
      Twisted.res R hO (t : _) * dV.app O (hO.trans (hW.le.trans inf_le_right)) a

def firstCoefficient (O : Opens X) : R.obj.obj (op O) →+ R.obj.obj (op (O ⊓ U)) :=
  (dU.app (O ⊓ U) inf_le_right).comp
    (Twisted.res R (show O ⊓ U ≤ O from inf_le_left)).toAddMonoidHom

def secondCoefficient (O : Opens X) : R.obj.obj (op O) →+ R.obj.obj (op (O ⊓ V)) :=
  (dV.app (O ⊓ V) inf_le_right).comp
    (Twisted.res R (show O ⊓ V ≤ O from inf_le_left)).toAddMonoidHom

theorem firstCoefficient_mul (O : Opens X) (a b : R.obj.obj (op O)) :
    firstCoefficient R c U dU O (a * b) =
      Twisted.res R (show O ⊓ U ≤ O from inf_le_left) a * firstCoefficient R c U dU O b +
        Twisted.res R (show O ⊓ U ≤ O from inf_le_left) b * firstCoefficient R c U dU O a := by
  change dU.app _ _ (Twisted.res R _ (a * b)) = _
  rw [map_mul, dU.leibniz]
  rfl

theorem secondCoefficient_mul (O : Opens X) (a b : R.obj.obj (op O)) :
    secondCoefficient R c V dV O (a * b) =
      Twisted.res R (show O ⊓ V ≤ O from inf_le_left) a * secondCoefficient R c V dV O b +
        Twisted.res R (show O ⊓ V ≤ O from inf_le_left) b * secondCoefficient R c V dV O a := by
  change dV.app _ _ (Twisted.res R _ (a * b)) = _
  rw [map_mul, dV.leibniz]
  rfl

theorem firstCoefficient_restrict {O P : Opens X} (h : P ≤ O) (a : R.obj.obj (op O)) :
    firstCoefficient R c U dU P (Twisted.res R h a) =
      Twisted.res R (inf_le_inf_right U h) (firstCoefficient R c U dU O a) := by
  change dU.app (P ⊓ U) inf_le_right
    (Twisted.res R inf_le_left (Twisted.res R h a)) =
      Twisted.res R (inf_le_inf_right U h)
        (dU.app (O ⊓ U) inf_le_right (Twisted.res R inf_le_left a))
  rw [← dU.naturality (inf_le_inf_right U h) inf_le_right inf_le_right,
    Twisted.res_comp, Twisted.res_comp]

theorem secondCoefficient_restrict {O P : Opens X} (h : P ≤ O) (a : R.obj.obj (op O)) :
    secondCoefficient R c V dV P (Twisted.res R h a) =
      Twisted.res R (inf_le_inf_right V h) (secondCoefficient R c V dV O a) := by
  change dV.app (P ⊓ V) inf_le_right
    (Twisted.res R inf_le_left (Twisted.res R h a)) =
      Twisted.res R (inf_le_inf_right V h)
        (dV.app (O ⊓ V) inf_le_right (Twisted.res R inf_le_left a))
  rw [← dV.naturality (inf_le_inf_right V h) inf_le_right inf_le_right,
    Twisted.res_comp, Twisted.res_comp]

theorem firstCoefficient_constant (O : Opens X) (z : ℂ) :
    firstCoefficient R c U dU O (coefficientOn R c O z) = 0 := by
  change dU.app _ _ (Twisted.res R _ (coefficientOn R c O z)) = 0
  rw [coefficientOn_restrict, dU.coefficient]

theorem secondCoefficient_constant (O : Opens X) (z : ℂ) :
    secondCoefficient R c V dV O (coefficientOn R c O z) = 0 := by
  change dV.app _ _ (Twisted.res R _ (coefficientOn R c O z)) = 0
  rw [coefficientOn_restrict, dV.coefficient]

variable (hcompat : Compatible R c U V W hW t dU dV)

include hcompat in
theorem coefficients_mem (O : Opens X) (a : R.obj.obj (op O)) :
    (firstCoefficient R c U dU O a, secondCoefficient R c V dV O a) ∈
      Twisted.Pairs R U V W hW t O := by
  apply sub_eq_zero.mpr
  change Twisted.res R (inf_le_inf_left O (hW.le.trans inf_le_left))
      (dU.app _ _ (Twisted.res R _ a)) =
    Twisted.res R (show O ⊓ W ≤ W from inf_le_right) (t : _) *
      Twisted.res R (inf_le_inf_left O (hW.le.trans inf_le_right))
        (dV.app _ _ (Twisted.res R _ a))
  rw [← dU.naturality (inf_le_inf_left O (hW.le.trans inf_le_left)) inf_le_right
      (inf_le_right.trans (hW.le.trans inf_le_left)),
    ← dV.naturality (inf_le_inf_left O (hW.le.trans inf_le_right)) inf_le_right
      (inf_le_right.trans (hW.le.trans inf_le_right)), Twisted.res_comp, Twisted.res_comp]
  exact hcompat (O ⊓ W) inf_le_right _

def pairDerivative (O : Opens X) : R.obj.obj (op O) →+ Twisted.Pairs R U V W hW t O :=
  ((firstCoefficient R c U dU O).prod (secondCoefficient R c V dV O)).codRestrict _
    (coefficients_mem R c U V W hW t dU dV hcompat O)

def toTwisted (O : Opens X) :
    R.obj.obj (op O) →+ (Twisted.sheaf R U V W hW t).obj.obj (op O) :=
  (Twisted.sectionPairsEquiv R U V W hW t O).symm.toAddMonoidHom.comp
    (pairDerivative R c U V W hW t dU dV hcompat O)

@[simp] theorem sectionPairs_toTwisted (O : Opens X) (a : R.obj.obj (op O)) :
    Twisted.sectionPairsEquiv R U V W hW t O (toTwisted R c U V W hW t dU dV hcompat O a) =
      pairDerivative R c U V W hW t dU dV hcompat O a :=
  (Twisted.sectionPairsEquiv R U V W hW t O).apply_symm_apply _

/-- In the first existing trivialization the constructed derivation is
exactly its specified local coefficient on every subopen. -/
theorem toTwisted_first_local (O : Opens X) (hO : O ≤ U) (a : R.obj.obj (op O)) :
    Twisted.firstLocalSectionsEquiv R U V W hW t O hO
      (toTwisted R c U V W hW t dU dV hcompat O a) = dU.app O hO a := by
  rw [Twisted.firstLocalSectionsEquiv_apply, sectionPairs_toTwisted]
  change Twisted.res R (le_inf le_rfl hO)
    (dU.app (O ⊓ U) inf_le_right (Twisted.res R inf_le_left a)) = _
  rw [← dU.naturality (le_inf le_rfl hO) inf_le_right hO,
    Twisted.res_comp, Twisted.res_self]

theorem toTwisted_second_local (O : Opens X) (hO : O ≤ V) (a : R.obj.obj (op O)) :
    Twisted.secondLocalSectionsEquiv R U V W hW t O hO
      (toTwisted R c U V W hW t dU dV hcompat O a) = dV.app O hO a := by
  rw [Twisted.secondLocalSectionsEquiv_apply, sectionPairs_toTwisted]
  change Twisted.res R (le_inf le_rfl hO)
    (dV.app (O ⊓ V) inf_le_right (Twisted.res R inf_le_left a)) = _
  rw [← dV.naturality (le_inf le_rfl hO) inf_le_right hO,
    Twisted.res_comp, Twisted.res_self]

/-- The two local coefficient derivations form one actual derivation with
values in the genuine twisted module sheaf. -/
def twistedDerivation :
    (TwistedModule.moduleSheaf R U V W hW t).val.Derivation' (coefficientMap R c) where
  d {O} := toTwisted R c U V W hW t dU dV hcompat O.unop
  d_mul {O} a b := by
    letI : Module (R.obj.obj O) ((Twisted.sheaf R U V W hW t).obj.obj (op O.unop)) :=
      TwistedModule.sectionsModule R U V W hW t O.unop
    let a' : R.obj.obj (op O.unop) := a
    let b' : R.obj.obj (op O.unop) := b
    change toTwisted R c U V W hW t dU dV hcompat O.unop (a' * b') =
      a' • toTwisted R c U V W hW t dU dV hcompat O.unop b' +
        b' • toTwisted R c U V W hW t dU dV hcompat O.unop a'
    apply (Twisted.sectionPairsEquiv R U V W hW t O.unop).injective
    rw [map_add]
    apply Subtype.ext
    apply Prod.ext
    · change (Twisted.sectionPairsEquiv R U V W hW t O.unop
          (toTwisted R c U V W hW t dU dV hcompat O.unop (a' * b'))).val.1 =
        (Twisted.sectionPairsEquiv R U V W hW t O.unop
          (a' • toTwisted R c U V W hW t dU dV hcompat O.unop b')).val.1 +
        (Twisted.sectionPairsEquiv R U V W hW t O.unop
          (b' • toTwisted R c U V W hW t dU dV hcompat O.unop a')).val.1
      simp only [TwistedModule.sectionPairs_fst_smul, sectionPairs_toTwisted]
      exact firstCoefficient_mul R c U dU O.unop a' b'
    · change (Twisted.sectionPairsEquiv R U V W hW t O.unop
          (toTwisted R c U V W hW t dU dV hcompat O.unop (a' * b'))).val.2 =
        (Twisted.sectionPairsEquiv R U V W hW t O.unop
          (a' • toTwisted R c U V W hW t dU dV hcompat O.unop b')).val.2 +
        (Twisted.sectionPairsEquiv R U V W hW t O.unop
          (b' • toTwisted R c U V W hW t dU dV hcompat O.unop a')).val.2
      simp only [TwistedModule.sectionPairs_snd_smul, sectionPairs_toTwisted]
      exact secondCoefficient_mul R c V dV O.unop a' b'
  d_map {O P} f a := by
    have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
    change toTwisted R c U V W hW t dU dV hcompat P.unop (R.obj.map f a) =
      (Twisted.sheaf R U V W hW t).obj.map f
        (toTwisted R c U V W hW t dU dV hcompat O.unop a)
    rw [hf]
    apply (Twisted.sectionPairsEquiv R U V W hW t P.unop).injective
    apply Subtype.ext
    apply Prod.ext
    · rw [Twisted.sectionPairs_fst_naturality, sectionPairs_toTwisted, sectionPairs_toTwisted]
      exact firstCoefficient_restrict R c U dU (leOfHom f.unop) a
    · rw [Twisted.sectionPairs_snd_naturality, sectionPairs_toTwisted, sectionPairs_toTwisted]
      exact secondCoefficient_restrict R c V dV (leOfHom f.unop) a
  d_app {O} z := by
    change toTwisted R c U V W hW t dU dV hcompat O.unop (coefficientOn R c O.unop z) = 0
    apply (Twisted.sectionPairsEquiv R U V W hW t O.unop).injective
    rw [map_zero, sectionPairs_toTwisted]
    apply Subtype.ext
    apply Prod.ext
    · exact firstCoefficient_constant R c U dU O.unop z
    · exact secondCoefficient_constant R c V dV O.unop z

/-- The universal differential sheaf maps to the existing twisted sheaf
through the constructed, compatible local coefficient derivations. -/
def coefficientMorphism : differentialSheaf R c ⟶ TwistedModule.moduleSheaf R U V W hW t :=
  differentialLift R c (TwistedModule.moduleSheaf R U V W hW t)
    (twistedDerivation R c U V W hW t dU dV hcompat)

theorem coefficientMorphism_D (O : Opens X) (a : R.obj.obj (op O)) :
    (coefficientMorphism R c U V W hW t dU dV hcompat).val.app (op O)
      ((universalDifferential R c).d a) =
        toTwisted R c U V W hW t dU dV hcompat O a :=
  PresheafOfModules.Derivation.congr_d
    (differentialLift_fac R c (TwistedModule.moduleSheaf R U V W hW t)
      (twistedDerivation R c U V W hW t dU dV hcompat)) a

theorem coefficientMorphism_D_first (O : Opens X) (hO : O ≤ U)
    (a : R.obj.obj (op O)) :
    Twisted.firstLocalSectionsEquiv R U V W hW t O hO
      ((coefficientMorphism R c U V W hW t dU dV hcompat).val.app (op O)
        ((universalDifferential R c).d a)) = dU.app O hO a := by
  rw [coefficientMorphism_D, toTwisted_first_local]

theorem coefficientMorphism_D_second (O : Opens X) (hO : O ≤ V)
    (a : R.obj.obj (op O)) :
    Twisted.secondLocalSectionsEquiv R U V W hW t O hO
      ((coefficientMorphism R c U V W hW t dU dV hcompat).val.app (op O)
        ((universalDifferential R c).d a)) = dV.app O hO a := by
  rw [coefficientMorphism_D, toTwisted_second_local]

#print axioms twistedDerivation
#print axioms coefficientMorphism

end CycleQ2GeometricTwistedDifferential
end

/-!
# A genuine differential-sheaf isomorphism from compatible local frames

The coefficient derivation and the glued frame morphism are inverse when
the actual local differentials reconstruct in the frames and the actual
coefficient morphism sends the frames to one. Both assertions are local
equalities of specified sections; the two global inverse identities are
proved here using sheaf separatedness and the differential universal
property.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricTwistedDifferentialIso

open CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricTwistedFrameMap CycleQ2GeometricTwistedFrameInverse
  CycleQ2GeometricTwistedDifferential

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤))
  (U V W : Opens X) (hW : W = U ⊓ V) (t : (R.obj.obj (op W))ˣ)
  (hcover : U ⊔ V = ⊤)
  (dU : LocalCoefficient R c U) (dV : LocalCoefficient R c V)
  (hcompat : Compatible R c U V W hW t dU dV)

section Reconstruction

variable (M : SheafOfModules.{0} (ringSheaf R))
  (d : M.val.Derivation' (coefficientMap R c))
  (ηU : Sections R M U) (ηV : Sections R M V)
  (hη : restrict R M (hW.le.trans inf_le_right) ηV =
    (t : R.obj.obj (op W)) • restrict R M (hW.le.trans inf_le_left) ηU)
  (hrecU : ∀ (O : Opens X) (hO : O ≤ U) (a : R.obj.obj (op O)),
    d.d a = dU.app O hO a • restrict R M hO ηU)
  (hrecV : ∀ (O : Opens X) (hO : O ≤ V) (a : R.obj.obj (op O)),
    d.d a = dV.app O hO a • restrict R M hO ηV)

include hrecU hrecV in
/-- Local reconstruction in actual frames identifies the reconstructed
global sheaf-valued derivation with the original derivation. -/
theorem derivation_reconstruction :
    (twistedDerivation R c U V W hW t dU dV hcompat).postcomp
      (frameMorphism R M U V W hW t hcover ηU ηV hη).val = d := by
  ext O a
  change (frameMorphism R M U V W hW t hcover ηU ηV hη).val.app O
    (toTwisted R c U V W hW t dU dV hcompat O.unop a) = d.d a
  apply sections_ext₂ R M inf_le_left inf_le_left (intersect_cover U V hcover O.unop)
  · rw [frameMorphism_apply, sectionFrameMap_first, sectionPairs_toTwisted]
    change firstCoefficient R c U dU O.unop a •
      restrict R M (show O.unop ⊓ U ≤ U from inf_le_right) ηU =
        restrict R M (show O.unop ⊓ U ≤ O.unop from inf_le_left) (d.d a)
    exact (hrecU (O.unop ⊓ U) inf_le_right
      (Twisted.res R (show O.unop ⊓ U ≤ O.unop from inf_le_left) a)).symm.trans
        (d.d_map (homOfLE (show O.unop ⊓ U ≤ O.unop from inf_le_left)).op a)
  · rw [frameMorphism_apply, sectionFrameMap_second, sectionPairs_toTwisted]
    change secondCoefficient R c V dV O.unop a •
      restrict R M (show O.unop ⊓ V ≤ V from inf_le_right) ηV =
        restrict R M (show O.unop ⊓ V ≤ O.unop from inf_le_left) (d.d a)
    exact (hrecV (O.unop ⊓ V) inf_le_right
      (Twisted.res R (show O.unop ⊓ V ≤ O.unop from inf_le_left) a)).symm.trans
        (d.d_map (homOfLE (show O.unop ⊓ V ≤ O.unop from inf_le_left)).op a)

include hrecV hη in
/-- An independently constructed local coefficient map in the first chart
proves the coefficient transition from the actual frame transition. This
does not use the glued coefficient morphism. -/
theorem coefficients_compatible_of_frame
    (lU : ∀ (O : Opens X) (hO : O ≤ U), Sections R M O →ₗ[R.obj.obj (op O)] R.obj.obj (op O))
    (hld : ∀ (O : Opens X) (hO : O ≤ U) (a : R.obj.obj (op O)),
      lU O hO (d.d a) = dU.app O hO a)
    (hlnorm : ∀ (O : Opens X) (hO : O ≤ U),
      lU O hO (restrict R M hO ηU) = 1) :
    Compatible R c U V W hW t dU dV := by
  intro O hO a
  have hframe := congrArg (restrict R M hO) hη
  rw [restrict_smul, restrict_comp, restrict_comp] at hframe
  rw [← hld O (hO.trans (hW.le.trans inf_le_left)) a,
    hrecV O (hO.trans (hW.le.trans inf_le_right)) a, hframe,
    map_smul, map_smul, hlnorm]
  change dV.app O (hO.trans (hW.le.trans inf_le_right)) a *
      (Twisted.res R hO (t : _) * 1) =
    Twisted.res R hO (t : _) * dV.app O (hO.trans (hW.le.trans inf_le_right)) a
  rw [mul_one, mul_comm]

end Reconstruction

variable (ηU : Sections R (differentialSheaf R c) U)
  (ηV : Sections R (differentialSheaf R c) V)
  (hη : restrict R (differentialSheaf R c) (hW.le.trans inf_le_right) ηV =
    (t : R.obj.obj (op W)) •
      restrict R (differentialSheaf R c) (hW.le.trans inf_le_left) ηU)
  (hrecU : ∀ (O : Opens X) (hO : O ≤ U) (a : R.obj.obj (op O)),
    (universalDifferential R c).d a = dU.app O hO a •
      restrict R (differentialSheaf R c) hO ηU)
  (hrecV : ∀ (O : Opens X) (hO : O ≤ V) (a : R.obj.obj (op O)),
    (universalDifferential R c).d a = dV.app O hO a •
      restrict R (differentialSheaf R c) hO ηV)

include hrecU hrecV in
/-- The actual differential universal property upgrades reconstruction
of derivatives to an identity on the whole differential sheaf. -/
theorem coefficientMorphism_comp_frameMorphism :
    coefficientMorphism R c U V W hW t dU dV hcompat ≫
      frameMorphism R (differentialSheaf R c) U V W hW t hcover ηU ηV hη =
        𝟙 (differentialSheaf R c) := by
  apply differentialLift_unique R c
  have hh := derivation_reconstruction R c U V W hW t hcover dU dV hcompat
    (differentialSheaf R c) (universalDifferential R c) ηU ηV hη hrecU hrecV
  ext O a
  change (frameMorphism R (differentialSheaf R c) U V W hW t hcover ηU ηV hη).val.app O
    ((coefficientMorphism R c U V W hW t dU dV hcompat).val.app O
      ((universalDifferential R c).d a)) = (universalDifferential R c).d a
  rw [coefficientMorphism_D]
  exact PresheafOfModules.Derivation.congr_d hh a

variable
  (hnormU : Twisted.firstLocalSectionsEquiv R U V W hW t U le_rfl
    ((coefficientMorphism R c U V W hW t dU dV hcompat).val.app (op U) ηU) = 1)
  (hnormV : Twisted.secondLocalSectionsEquiv R U V W hW t V le_rfl
    ((coefficientMorphism R c U V W hW t dU dV hcompat).val.app (op V) ηV) = 1)

/-- The explicit coefficient map and the glued actual frames define an
isomorphism with the original twisted module sheaf. -/
def differentialTwistedIso : differentialSheaf R c ≅ TwistedModule.moduleSheaf R U V W hW t where
  hom := coefficientMorphism R c U V W hW t dU dV hcompat
  inv := frameMorphism R (differentialSheaf R c) U V W hW t hcover ηU ηV hη
  hom_inv_id := coefficientMorphism_comp_frameMorphism R c U V W hW t hcover dU dV hcompat
    ηU ηV hη hrecU hrecV
  inv_hom_id := frameMorphism_comp R (differentialSheaf R c) U V W hW t hcover ηU ηV hη
    (coefficientMorphism R c U V W hW t dU dV hcompat) hnormU hnormV

#print axioms derivation_reconstruction
#print axioms coefficientMorphism_comp_frameMorphism
#print axioms differentialTwistedIso

end CycleQ2GeometricTwistedDifferentialIso
end

end SourceGeometricTwistedDifferential

end ConsolidatedGeometricTwistedDifferential

section ConsolidatedGeometricChartCoefficient

section SourceGeometricSectionDifferentials

/-!
# Section differentials and the actual differential sheaf

The sheafification map is related to ordinary universal Kähler modules
over the actual rings of sections, with the complex algebra structures
given by the global coefficient map. The comparison commutes with every
restriction, including restriction to a projective coordinate overlap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSectionDifferentials

open CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineOverlap

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤))

abbrev SectionRing (U : Opens X) := R.obj.obj (op U)

abbrev sectionAlgebra (U : Opens X) : Algebra ℂ (SectionRing R U) :=
  (coefficientOn R c U).toAlgebra

abbrev SectionForms (U : Opens X) :=
  letI := sectionAlgebra R c U
  KaehlerDifferential ℂ (SectionRing R U)

/-- The ordinary universal Kähler module maps to the actual sheafification. -/
def toSheaf (U : Opens X) :
    SectionForms R c U →ₗ[SectionRing R U] (differentialSheaf R c).val.obj (op U) := by
  letI := sectionAlgebra R c U
  exact ((toDifferentialSheaf R c).app (op U)).hom

@[simp] theorem toSheaf_D (U : Opens X) (a : SectionRing R U) :
    letI := sectionAlgebra R c U
    toSheaf R c U (KaehlerDifferential.D ℂ (SectionRing R U) a) =
      (universalDifferential R c).d (X := op U) a := rfl

def sectionRestriction {U V : Opens X} (h : V ≤ U) :
    letI := sectionAlgebra R c U
    letI := sectionAlgebra R c V
    SectionRing R U →ₐ[ℂ] SectionRing R V := by
  letI := sectionAlgebra R c U
  letI := sectionAlgebra R c V
  refine { toRingHom := (R.obj.map (homOfLE h).op).hom, commutes' := ?_ }
  intro a
  change R.obj.map (homOfLE h).op (coefficientOn R c U a) = coefficientOn R c V a
  exact (CategoryTheory.congr_fun ((coefficientMap R c).naturality (homOfLE h).op) a).symm

@[simp] theorem sectionRestriction_apply {U V : Opens X} (h : V ≤ U)
    (a : SectionRing R U) :
    sectionRestriction R c h a = R.obj.map (homOfLE h).op a := rfl

/-- Restriction of a differential section is induced by the actual
algebra map on section rings. This uses the sheafification unit itself. -/
theorem toSheaf_restrict {U V : Opens X} (h : V ≤ U) (ω : SectionForms R c U) :
    letI := sectionAlgebra R c U
    letI := sectionAlgebra R c V
    (differentialSheaf R c).val.map (homOfLE h).op (toSheaf R c U ω) =
      toSheaf R c V (differentialMap (sectionRestriction R c h) ω) := by
  letI := sectionAlgebra R c U
  letI := sectionAlgebra R c V
  have hω : ω ∈ Submodule.span (SectionRing R U)
      (Set.range (KaehlerDifferential.D ℂ (SectionRing R U))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [differentialMap_D, toSheaf_D, toSheaf_D]
      exact ((universalDifferential R c).d_map (homOfLE h).op a).symm
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [map_smul, PresheafOfModules.map_smul, differentialMap_smul, map_smul, hx]
      rfl

/-- Every finite identity between ordinary chart differentials therefore
gives the same identity in the actual differential sheaf. -/
theorem toSheaf_relation {U V W : Opens X} (hWU : W ≤ U) (hWV : W ≤ V)
    (ω : SectionForms R c U) (η : SectionForms R c V) (a : SectionRing R W)
    (h : letI := sectionAlgebra R c U
      letI := sectionAlgebra R c V
      letI := sectionAlgebra R c W
      differentialMap (sectionRestriction R c hWV) η =
      a • differentialMap (sectionRestriction R c hWU) ω) :
    (differentialSheaf R c).val.map (homOfLE hWV).op (toSheaf R c V η) =
      a • (differentialSheaf R c).val.map (homOfLE hWU).op (toSheaf R c U ω) := by
  letI := sectionAlgebra R c U
  letI := sectionAlgebra R c V
  letI := sectionAlgebra R c W
  rw [toSheaf_restrict, toSheaf_restrict, h, map_smul]

#print axioms toSheaf_restrict

end CycleQ2GeometricSectionDifferentials

end

end SourceGeometricSectionDifferentials

section SourceGeometricChartDerivation

/-!
# Actual differential coefficients on subopens of an affine chart

The restriction map of an open immersion is an isomorphism on every open
contained in its image. Conjugating the actual structure-sheaf derivation
through this isomorphism gives local coefficients on the original scheme.
Both regularity and restriction compatibility are proved, using the actual
section maps of the chart morphism.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricChartDerivation

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricStructureDerivation

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable {Y : Scheme.{0}} (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]

/-- The literal section map of the actual chart, viewed as an isomorphism. -/
def sectionEquiv (O : Y.Opens) (hO : O ≤ j.opensRange) :
    Γ(Y, O) ≃+* Γ(Spec (CommRingCat.of A), j ⁻¹ᵁ O) := by
  letI := Scheme.Hom.isIso_app j O hO
  exact (asIso (j.app O)).commRingCatIsoToRingEquiv

@[simp] theorem sectionEquiv_apply (O : Y.Opens) (hO : O ≤ j.opensRange)
    (a : Γ(Y, O)) : sectionEquiv j O hO a = j.app O a := rfl

theorem sectionEquiv_naturality {O P : Y.Opens} (h : P ≤ O)
    (hO : O ≤ j.opensRange) (hP : P ≤ j.opensRange) (a : Γ(Y, O)) :
    sectionEquiv j P hP (Y.presheaf.map (homOfLE h).op a) =
      (Spec (CommRingCat.of A)).presheaf.map
        ((Opens.map j.base).map (homOfLE h)).op (sectionEquiv j O hO a) := by
  exact congrArg (fun f : Γ(Y, O) ⟶ Γ(Spec (CommRingCat.of A), j ⁻¹ᵁ P) => f a)
    (j.naturality (homOfLE h).op)

/-- The coefficient of an actual differential on an arbitrary subopen of
the chart image, transported back to the original structure sheaf. -/
def chartDerivative (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (O : Y.Opens) (hO : O ≤ j.opensRange) (a : Γ(Y, O)) : Γ(Y, O) :=
  (sectionEquiv j O hO).symm
    (sectionDerivative e (j ⁻¹ᵁ O) (sectionEquiv j O hO a))

@[simp] theorem sectionEquiv_chartDerivative (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (O : Y.Opens) (hO : O ≤ j.opensRange) (a : Γ(Y, O)) :
    sectionEquiv j O hO (chartDerivative j e O hO a) =
      sectionDerivative e (j ⁻¹ᵁ O) (sectionEquiv j O hO a) :=
  (sectionEquiv j O hO).apply_symm_apply _

theorem chartDerivative_add (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (O : Y.Opens) (hO : O ≤ j.opensRange) (a b : Γ(Y, O)) :
    chartDerivative j e O hO (a + b) =
      chartDerivative j e O hO a + chartDerivative j e O hO b := by
  apply (sectionEquiv j O hO).injective
  simp only [sectionEquiv_chartDerivative, map_add]
  exact sectionDerivative_add e (j ⁻¹ᵁ O) _ _

theorem chartDerivative_mul (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (O : Y.Opens) (hO : O ≤ j.opensRange) (a b : Γ(Y, O)) :
    chartDerivative j e O hO (a * b) =
      a * chartDerivative j e O hO b + b * chartDerivative j e O hO a := by
  apply (sectionEquiv j O hO).injective
  simp only [sectionEquiv_chartDerivative, map_add, map_mul]
  exact sectionDerivative_mul e (j ⁻¹ᵁ O) _ _

/-- Restriction is respected on every subopen of the original scheme,
using the actual naturality square of the chart morphism. -/
theorem chartDerivative_restrict (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    {O P : Y.Opens} (h : P ≤ O) (hO : O ≤ j.opensRange)
    (hP : P ≤ j.opensRange) (a : Γ(Y, O)) :
    chartDerivative j e P hP (Y.presheaf.map (homOfLE h).op a) =
      Y.presheaf.map (homOfLE h).op (chartDerivative j e O hO a) := by
  apply (sectionEquiv j P hP).injective
  rw [sectionEquiv_chartDerivative, sectionEquiv_naturality j h hO hP,
    sectionEquiv_naturality j h hO hP, sectionEquiv_chartDerivative]
  exact sectionDerivative_restrict e ((Opens.map j.base).map (homOfLE h)) _

def chartDerivativeAddHom (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (O : Y.Opens) (hO : O ≤ j.opensRange) : Γ(Y, O) →+ Γ(Y, O) :=
  AddMonoidHom.mk' (chartDerivative j e O hO) (chartDerivative_add j e O hO)

/-- The local complex coefficient map is transported by the actual chart. -/
def chartCoefficient (O : Y.Opens) (hO : O ≤ j.opensRange) : ℂ →+* Γ(Y, O) :=
  (sectionEquiv j O hO).symm.toRingHom.comp
    ((algebraMap A (AffineSections (j ⁻¹ᵁ O))).comp (algebraMap ℂ A))

/-- Elements of the affine chart ring are actual regular sections on all
subopens of the chart image. -/
def chartRingMap (O : Y.Opens) (hO : O ≤ j.opensRange) : A →+* Γ(Y, O) :=
  (sectionEquiv j O hO).symm.toRingHom.comp (algebraMap A (AffineSections (j ⁻¹ᵁ O)))

@[simp] theorem sectionEquiv_chartRingMap (O : Y.Opens) (hO : O ≤ j.opensRange) (a : A) :
    sectionEquiv j O hO (chartRingMap j O hO a) =
      algebraMap A (AffineSections (j ⁻¹ᵁ O)) a :=
  (sectionEquiv j O hO).apply_symm_apply _

theorem chartDerivative_chartRingMap (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (O : Y.Opens) (hO : O ≤ j.opensRange) (a : A) :
    chartDerivative j e O hO (chartRingMap j O hO a) =
      chartRingMap j O hO (e (KaehlerDifferential.D ℂ A a)) := by
  apply (sectionEquiv j O hO).injective
  rw [sectionEquiv_chartDerivative, sectionEquiv_chartRingMap, sectionEquiv_chartRingMap]
  exact sectionDerivative_algebraMap e (j ⁻¹ᵁ O) a

theorem chartRingMap_restrict {O P : Y.Opens} (h : P ≤ O)
    (hO : O ≤ j.opensRange) (hP : P ≤ j.opensRange) (a : A) :
    Y.presheaf.map (homOfLE h).op (chartRingMap j O hO a) = chartRingMap j P hP a := by
  apply (sectionEquiv j P hP).injective
  rw [sectionEquiv_naturality j h hO hP, sectionEquiv_chartRingMap, sectionEquiv_chartRingMap]
  rfl

theorem chartDerivative_coefficient (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (O : Y.Opens) (hO : O ≤ j.opensRange) (c : ℂ) :
    chartDerivative j e O hO (chartCoefficient j O hO c) = 0 := by
  apply (sectionEquiv j O hO).injective
  change sectionEquiv j O hO (chartDerivative j e O hO
    ((sectionEquiv j O hO).symm
      (algebraMap A (AffineSections (j ⁻¹ᵁ O)) (algebraMap ℂ A c)))) =
        sectionEquiv j O hO 0
  rw [sectionEquiv_chartDerivative, RingEquiv.apply_symm_apply, map_zero,
    sectionDerivative_algebraMap, Derivation.map_algebraMap, map_zero, map_zero]

theorem chartDerivative_coefficient_of_app (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (O : Y.Opens) (hO : O ≤ j.opensRange) (c : ℂ) (a : Γ(Y, O))
    (ha : j.app O a = algebraMap A (AffineSections (j ⁻¹ᵁ O)) (algebraMap ℂ A c)) :
    chartDerivative j e O hO a = 0 := by
  have h : a = chartCoefficient j O hO c := by
    apply (sectionEquiv j O hO).injective
    change sectionEquiv j O hO a =
      sectionEquiv j O hO ((sectionEquiv j O hO).symm _)
    rw [RingEquiv.apply_symm_apply]
    exact ha
  rw [h, chartDerivative_coefficient]

#print axioms chartDerivative_restrict
#print axioms chartDerivative_coefficient

end CycleQ2GeometricChartDerivation
end

end SourceGeometricChartDerivation

section SourceGeometricChartModules

/-!
# Sheaf-valued derivations in an actual affine chart

An open immersion transports an arbitrary structure-module sheaf to the
affine chart. The module action is transported through the inverse of the
actual section isomorphism, and the sheaf condition follows from the
continuous image functor on opens. This allows the proved affine
derivation factorization to apply to sections of the original scheme.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricChartModules

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable {Y : Scheme.{0}} (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]

local instance chartContinuous :
    j.opensFunctor.IsContinuous (Opens.grothendieckTopology (PrimeSpectrum.Top A))
      (Opens.grothendieckTopology Y) :=
  inferInstanceAs (j.opensFunctor.IsContinuous
    (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (Opens.grothendieckTopology Y))

/-- The actual chart section inverses form a morphism of ring sheaves. -/
def chartRingSheafMap :
    ringSheaf (Spec.structureSheaf A) ⟶
      (j.opensFunctor.sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)).obj
          (ringSheaf Y.sheaf) where
  hom :=
    { app U := RingCat.ofHom (j.appIso U.unop).inv.hom
      naturality {U V} f := by
        ext a
        exact congrArg (fun g : Γ(Spec (CommRingCat.of A), U.unop) ⟶
          Γ(Y, j ''ᵁ V.unop) => g a) (j.appIso_inv_naturality f) }

/-- A genuine affine sheaf of modules, retaining the original sheaf's
sections on image opens and its original restriction maps. -/
def chartModule (M : SheafOfModules.{0} (ringSheaf Y.sheaf)) : AffineModule A :=
  (SheafOfModules.pushforward (F := j.opensFunctor) (chartRingSheafMap j)).obj M

variable (c : ℂ →+* Γ(Y, ⊤))

/-- Compatibility of the complex coefficients with the actual chart.
This is an equality of existing scalar maps, not a differential comparison. -/
def CoefficientCompatible : Prop :=
  ∀ (U : (Spec (CommRingCat.of A)).Opens) (z : ℂ),
    (j.appIso U).inv (algebraMap A (AffineSections A U) (algebraMap ℂ A z)) =
      coefficientOn Y.sheaf c (j ''ᵁ U) z

/-- It is enough to verify the actual global coefficient map once; all
subopen comparisons then follow from the scheme morphism's naturality. -/
theorem coefficientCompatible_of_appTop
    (h : ∀ z : ℂ, j.appTop (c z) =
      algebraMap A (AffineSections A ⊤) (algebraMap ℂ A z)) :
    CoefficientCompatible j c := by
  intro U z
  apply (j.appIso U).commRingCatIsoToRingEquiv.injective
  change (j.appIso U).commRingCatIsoToRingEquiv
    ((j.appIso U).commRingCatIsoToRingEquiv.symm
      (algebraMap A (AffineSections A U) (algebraMap ℂ A z))) =
    (j.appIso U).hom (coefficientOn Y.sheaf c (j ''ᵁ U) z)
  rw [RingEquiv.apply_symm_apply]
  have hnat := j.map_appLE (j.preimage_image_eq U).ge
    (homOfLE (show j ''ᵁ U ≤ ⊤ from le_top)).op
  rw [← j.appIso_hom' U] at hnat
  have hv := congrArg (fun f : Γ(Y, ⊤) ⟶ Γ(Spec (CommRingCat.of A), U) => f (c z)) hnat
  change (j.appIso U).hom (coefficientOn Y.sheaf c (j ''ᵁ U) z) =
    (Spec.structureSheaf A).obj.map (homOfLE (show U ≤ ⊤ from le_top)).op
      (j.appTop (c z)) at hv
  rw [h z] at hv
  exact hv.symm

/-- Being an affine chart over the complex field establishes the scalar
compatibility needed by the actual sheaf-valued derivation construction. -/
theorem coefficientCompatible_of_overComplex (f : Y ⟶ Spec (CommRingCat.of ℂ))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) :
    CoefficientCompatible j (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appTop).hom) := by
  apply coefficientCompatible_of_appTop
  intro z
  have hmaps : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appTop ≫ j.appTop =
      CommRingCat.ofHom (algebraMap ℂ A) ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv := by
    rw [← Scheme.Hom.comp_appTop, hj, ← Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (fun g : CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of A), ⊤) => g z) hmaps

variable (M : SheafOfModules.{0} (ringSheaf Y.sheaf))
variable (d : M.val.Derivation' (coefficientMap Y.sheaf c))

/-- Restrict a sheaf-valued derivation through the actual chart section
isomorphisms. The target is the transported actual module sheaf. -/
def chartDerivation (hc : CoefficientCompatible j c) :
    AffineDerivation A (chartModule j M) where
  d {U} := d.d.comp (j.appIso U.unop).inv.hom.toAddMonoidHom
  d_mul {U} a b := by
    change d.d ((j.appIso U.unop).inv (a * b)) =
      (j.appIso U.unop).inv a • d.d ((j.appIso U.unop).inv b) +
        (j.appIso U.unop).inv b • d.d ((j.appIso U.unop).inv a)
    rw [map_mul, d.d_mul]
  d_map {U V} f a := by
    change d.d ((j.appIso V.unop).inv ((Spec.structureSheaf A).obj.map f a)) =
      M.val.map (j.opensFunctor.op.map f) (d.d ((j.appIso U.unop).inv a))
    have h := congrArg (fun g : Γ(Spec (CommRingCat.of A), U.unop) ⟶
      Γ(Y, j ''ᵁ V.unop) => g a) (j.appIso_inv_naturality f)
    change (j.appIso V.unop).inv ((Spec.structureSheaf A).obj.map f a) =
      Y.presheaf.map (j.opensFunctor.op.map f) ((j.appIso U.unop).inv a) at h
    exact (congrArg d.d h).trans (d.d_map (j.opensFunctor.op.map f) _)
  d_app {U} z := by
    change d.d ((j.appIso U.unop).inv
      (algebraMap A (AffineSections A U.unop) (algebraMap ℂ A z))) = 0
    rw [hc U.unop z]
    exact d.d_app z

@[simp] theorem chartDerivation_apply (hc : CoefficientCompatible j c)
    (U : (Spec (CommRingCat.of A)).Opens) (a : Γ(Spec (CommRingCat.of A), U)) :
    (chartDerivation j c M d hc).d (X := op U) a = d.d ((j.appIso U).inv a) := rfl

/-- The image of the actual affine frame under the restricted derivation. -/
def chartFrame (hc : CoefficientCompatible j c) (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    (chartModule j M).val.obj (op ⊤) :=
  globalKaehlerMap (chartModule j M) (chartDerivation j c M d hc) (e.symm 1)

/-- The arbitrary sheaf-valued differential on the chart factors through
the proved coefficient derivation, with its own actual frame as coefficient. -/
theorem chartDerivation_factorization (hc : CoefficientCompatible j c)
    (e : KaehlerDifferential ℂ A ≃ₗ[A] A) :
    chartDerivation j c M d hc = (affineFrameDerivation e).postcomp
      (unitMapFromGlobal (chartModule j M) (chartFrame j c M d hc e)).val :=
  derivation_factorization e (chartModule j M) (chartDerivation j c M d hc)

/-- The factorization on actual sections, with the original module action
and the original restriction map displayed explicitly. -/
theorem chartDerivation_factorization_apply (hc : CoefficientCompatible j c)
    (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : (Spec (CommRingCat.of A)).Opens) (a : Γ(Spec (CommRingCat.of A), U)) :
    d.d ((j.appIso U).inv a) =
      (j.appIso U).inv (CycleQ2GeometricStructureDerivation.sectionDerivative e U a) •
        M.val.map (j.opensFunctor.op.map (homOfLE (show U ≤ ⊤ from le_top)).op)
          (chartFrame j c M d hc e) := by
  have h := PresheafOfModules.Derivation.congr_d
    (chartDerivation_factorization j c M d hc e) (X := op U) a
  change d.d ((j.appIso U).inv a) =
    (unitMapFromGlobal (chartModule j M) (chartFrame j c M d hc e)).val.app (op U)
      ((affineFrameDerivation e).d a) at h
  rw [unitMapFromGlobal_apply] at h
  exact h

/-- Every regular function on an actual image subopen has this frame
expression for its differential in the original sheaf of modules. -/
theorem chartDerivation_factorization_section (hc : CoefficientCompatible j c)
    (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : (Spec (CommRingCat.of A)).Opens) (a : Γ(Y, j ''ᵁ U)) :
    d.d a =
      (j.appIso U).inv
        (CycleQ2GeometricStructureDerivation.sectionDerivative e U ((j.appIso U).hom a)) •
        M.val.map (j.opensFunctor.op.map (homOfLE (show U ≤ ⊤ from le_top)).op)
          (chartFrame j c M d hc e) := by
  have h := chartDerivation_factorization_apply j c M d hc e U ((j.appIso U).hom a)
  simpa only [Iso.hom_inv_id_apply] using h

#print axioms chartModule
#print axioms chartDerivation_factorization
#print axioms coefficientCompatible_of_overComplex
#print axioms chartDerivation_factorization_section

end CycleQ2GeometricChartModules
end

end SourceGeometricChartModules

section SourceGeometricChartCoefficient

/-!
# Independent local coefficient maps on an actual affine chart

The coefficient derivation is pushed forward from the affine chart along
the genuine preimage functor on opens. The differential universal property
then gives a global morphism into that actual direct-image module sheaf.
On every open contained in the chart, the inverse section isomorphism
turns this morphism into a linear coefficient map. This construction does
not depend on any overlap compatibility or on a global differential frame.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricChartCoefficient

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2GeometricChartDerivation CycleQ2GeometricChartModules
  CycleQ2GeometricTwistedDifferential

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable {Y : Scheme.{0}} (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
variable (c : ℂ →+* Γ(Y, ⊤))

/-- The scalar equality follows from an actual morphism over the complex
field and uses the canonical section map of affine space. -/
theorem coefficients_appTop_of_overComplex (f : Y ⟶ Spec (CommRingCat.of ℂ))
    (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) (z : ℂ) :
    j.appTop ((((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appTop).hom) z) =
      algebraMap A (AffineSections A ⊤) (algebraMap ℂ A z) := by
  have hmaps : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appTop ≫ j.appTop =
      CommRingCat.ofHom (algebraMap ℂ A) ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv := by
    rw [← Scheme.Hom.comp_appTop, hj, ← Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (fun g : CommRingCat.of ℂ ⟶ Γ(Spec (CommRingCat.of A), ⊤) => g z) hmaps

variable (hcoeff : ∀ z : ℂ, j.appTop (c z) =
  algebraMap A (AffineSections A ⊤) (algebraMap ℂ A z))

include hcoeff in
theorem coefficients_app (O : Y.Opens) (z : ℂ) :
    j.app O (coefficientOn Y.sheaf c O z) =
      algebraMap A (AffineSections A (j ⁻¹ᵁ O)) (algebraMap ℂ A z) := by
  have hn := congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(Spec (CommRingCat.of A), j ⁻¹ᵁ O) => g (c z))
    (j.naturality (homOfLE (show O ≤ ⊤ from le_top)).op)
  change j.app O (coefficientOn Y.sheaf c O z) =
    (Spec.structureSheaf A).obj.map
      ((Opens.map j.base).map (homOfLE (show O ≤ ⊤ from le_top))).op (j.appTop (c z)) at hn
  rw [hcoeff z] at hn
  exact hn

/-- Bundle the already constructed actual chart derivation on any
specified open contained in its image. -/
def chartLocalCoefficient (e : KaehlerDifferential ℂ A ≃ₗ[A] A)
    (U : Y.Opens) (hU : U ≤ j.opensRange) : LocalCoefficient Y.sheaf c U where
  app O hO := chartDerivativeAddHom j e O (hO.trans hU)
  leibniz O hO := chartDerivative_mul j e O (hO.trans hU)
  naturality h hO hP := chartDerivative_restrict j e h (hO.trans hU) (hP.trans hU)
  coefficient O hO z := chartDerivative_coefficient_of_app j e O (hO.trans hU) z _
    (coefficients_app j c hcoeff O z)

local instance preimageContinuous :
    (Opens.map j.base).IsContinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology (PrimeSpectrum.Top A)) :=
  inferInstanceAs ((Opens.map j.base).IsContinuous (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology (Spec (CommRingCat.of A))))

/-- The actual scheme section maps, now as a morphism of ring sheaves. -/
def pushforwardRingMap :
    ringSheaf Y.sheaf ⟶
      ((Opens.map j.base).sheafPushforwardContinuous RingCat.{0}
        (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)).obj
          (ringSheaf (Spec.structureSheaf A)) where
  hom :=
    { app O := RingCat.ofHom (j.app O.unop).hom
      naturality {O P} f := by
        ext a
        exact congrArg (fun g : Γ(Y, O.unop) ⟶ Γ(Spec (CommRingCat.of A), j ⁻¹ᵁ P.unop) =>
          g a) (j.naturality f) }

/-- The genuine direct image of the affine structure module; its sections
over an arbitrary open are regular functions on its actual preimage. -/
def pushforwardModule : SheafOfModules.{0} (ringSheaf Y.sheaf) :=
  (SheafOfModules.pushforward (F := Opens.map j.base) (pushforwardRingMap j)).obj
    (affineStructureModule A)

variable (e : KaehlerDifferential ℂ A ≃ₗ[A] A)

/-- Differentiate functions after their actual pullback to the chart.
This is globally defined, including on opens not contained in the chart. -/
def pushforwardDerivation :
    (pushforwardModule j).val.Derivation' (coefficientMap Y.sheaf c) where
  d {O} := ((affineFrameDerivation e).d (X := op (j ⁻¹ᵁ O.unop))).comp
    (j.app O.unop).hom.toAddMonoidHom
  d_mul {O} a b := by
    let a' : AffineSections A (j ⁻¹ᵁ O.unop) := j.app O.unop a
    let b' : AffineSections A (j ⁻¹ᵁ O.unop) := j.app O.unop b
    change CycleQ2GeometricStructureDerivation.sectionDerivative e (j ⁻¹ᵁ O.unop)
      (j.app O.unop (a * b)) =
        a' * CycleQ2GeometricStructureDerivation.sectionDerivative e
          (j ⁻¹ᵁ O.unop) b' +
        b' * CycleQ2GeometricStructureDerivation.sectionDerivative e
          (j ⁻¹ᵁ O.unop) a'
    rw [map_mul]
    exact CycleQ2GeometricStructureDerivation.sectionDerivative_mul e _ a' b'
  d_map {O P} f a := by
    change CycleQ2GeometricStructureDerivation.sectionDerivative e (j ⁻¹ᵁ P.unop)
      (j.app P.unop (Y.presheaf.map f a)) =
        (Spec.structureSheaf A).obj.map ((Opens.map j.base).map f.unop).op
          (CycleQ2GeometricStructureDerivation.sectionDerivative e (j ⁻¹ᵁ O.unop)
            (j.app O.unop a))
    have hn := congrArg (fun g : Γ(Y, O.unop) ⟶ Γ(Spec (CommRingCat.of A), j ⁻¹ᵁ P.unop) =>
      g a) (j.naturality f)
    change j.app P.unop (Y.presheaf.map f a) =
      (Spec.structureSheaf A).obj.map ((Opens.map j.base).map f.unop).op (j.app O.unop a) at hn
    rw [hn]
    exact CycleQ2GeometricStructureDerivation.sectionDerivative_restrict e
      ((Opens.map j.base).map f.unop) _
  d_app {O} z := by
    change CycleQ2GeometricStructureDerivation.sectionDerivative e (j ⁻¹ᵁ O.unop)
      (j.app O.unop (coefficientOn Y.sheaf c O.unop z)) = 0
    rw [coefficients_app j c hcoeff,
      CycleQ2GeometricStructureDerivation.sectionDerivative_algebraMap,
      Derivation.map_algebraMap, map_zero, map_zero]

/-- An independent coefficient morphism obtained before any transition or
gluing argument, into the actual direct-image sheaf. -/
def pushforwardCoefficient : differentialSheaf Y.sheaf c ⟶ pushforwardModule j :=
  differentialLift Y.sheaf c (pushforwardModule j) (pushforwardDerivation j c hcoeff e)

theorem pushforwardCoefficient_D (O : Y.Opens) (a : Γ(Y, O)) :
    (pushforwardCoefficient j c hcoeff e).val.app (op O)
      ((universalDifferential Y.sheaf c).d a) =
        CycleQ2GeometricStructureDerivation.sectionDerivative e (j ⁻¹ᵁ O) (j.app O a) :=
  PresheafOfModules.Derivation.congr_d
    (differentialLift_fac Y.sheaf c (pushforwardModule j) (pushforwardDerivation j c hcoeff e)) a

/-- On every subopen of the chart, the independent coefficient morphism
takes values in the original regular functions and is linear over them. -/
def localCoefficientMap (O : Y.Opens) (hO : O ≤ j.opensRange) :
    (differentialSheaf Y.sheaf c).val.obj (op O) →ₗ[Γ(Y, O)] Γ(Y, O) where
  toFun m := (sectionEquiv j O hO).symm
    ((pushforwardCoefficient j c hcoeff e).val.app (op O) m)
  map_add' a b := by rw [map_add, map_add]
  map_smul' a m := by
    let b : Γ(Spec (CommRingCat.of A), j ⁻¹ᵁ O) :=
      (pushforwardCoefficient j c hcoeff e).val.app (op O) m
    rw [map_smul]
    change (sectionEquiv j O hO).symm
      (j.app O a * b) = _
    rw [map_mul]
    change (sectionEquiv j O hO).symm (sectionEquiv j O hO a) * _ = _
    rw [RingEquiv.symm_apply_apply]
    rfl

@[simp] theorem sectionEquiv_localCoefficientMap (O : Y.Opens) (hO : O ≤ j.opensRange)
    (m : (differentialSheaf Y.sheaf c).val.obj (op O)) :
    sectionEquiv j O hO (localCoefficientMap j c hcoeff e O hO m) =
      (pushforwardCoefficient j c hcoeff e).val.app (op O) m :=
  (sectionEquiv j O hO).apply_symm_apply _

theorem localCoefficientMap_D (O : Y.Opens) (hO : O ≤ j.opensRange) (a : Γ(Y, O)) :
    localCoefficientMap j c hcoeff e O hO ((universalDifferential Y.sheaf c).d a) =
      chartDerivative j e O hO a := by
  apply (sectionEquiv j O hO).injective
  rw [sectionEquiv_localCoefficientMap, pushforwardCoefficient_D, sectionEquiv_chartDerivative]
  rfl

theorem localCoefficientMap_restrict {O P : Y.Opens} (h : P ≤ O)
    (hO : O ≤ j.opensRange) (hP : P ≤ j.opensRange)
    (m : (differentialSheaf Y.sheaf c).val.obj (op O)) :
    localCoefficientMap j c hcoeff e P hP
      ((differentialSheaf Y.sheaf c).val.map (homOfLE h).op m) =
        Y.presheaf.map (homOfLE h).op (localCoefficientMap j c hcoeff e O hO m) := by
  apply (sectionEquiv j P hP).injective
  rw [sectionEquiv_localCoefficientMap, sectionEquiv_naturality j h hO hP,
    sectionEquiv_localCoefficientMap]
  exact PresheafOfModules.naturality_apply (pushforwardCoefficient j c hcoeff e).val (homOfLE h).op m

open CycleQ2GeometricSectionDifferentials CycleQ2GeometricAffineOverlap

local instance sectionRingModule (O : Y.Opens) : Module (SectionRing Y.sheaf O) Γ(Y, O) :=
  inferInstanceAs (Module (SectionRing Y.sheaf O) (SectionRing Y.sheaf O))

/-- Any other linear coefficient map with the same derivative formula
agrees on the image of every ordinary sectionwise Kähler differential.
In particular this compares a later glued coefficient morphism on the
actual finite form representing a chart frame. -/
theorem localCoefficientMap_compare_on_forms (O : Y.Opens) (hO : O ≤ j.opensRange)
    (f : (differentialSheaf Y.sheaf c).val.obj (op O) →ₗ[Γ(Y, O)] Γ(Y, O))
    (hf : ∀ a : Γ(Y, O), f ((universalDifferential Y.sheaf c).d a) =
      chartDerivative j e O hO a) (ω : SectionForms Y.sheaf c O) :
    f (toSheaf Y.sheaf c O ω) =
      localCoefficientMap j c hcoeff e O hO (toSheaf Y.sheaf c O ω) := by
  letI := sectionAlgebra Y.sheaf c O
  have hω : ω ∈ Submodule.span (SectionRing Y.sheaf O)
      (Set.range (KaehlerDifferential.D ℂ (SectionRing Y.sheaf O))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [toSheaf_D, hf, localCoefficientMap_D]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => rw [map_smul, map_smul, map_smul, hx]

/-- On an actual section-ring image of the affine chart, the independent
coefficient map is the given algebraic Kähler frame coefficient. -/
theorem localCoefficientMap_on_form (O : Y.Opens) (hO : O ≤ j.opensRange)
    (φ : letI := sectionAlgebra Y.sheaf c O
      A →ₐ[ℂ] SectionRing Y.sheaf O)
    (hφ : ∀ a : A, j.app O (φ a) = algebraMap A (AffineSections A (j ⁻¹ᵁ O)) a)
    (ω : KaehlerDifferential ℂ A) :
    letI := sectionAlgebra Y.sheaf c O
    localCoefficientMap j c hcoeff e O hO
      (toSheaf Y.sheaf c O (differentialMap φ ω)) = φ (e ω) := by
  letI := sectionAlgebra Y.sheaf c O
  have hmap (a : A) : φ a = chartRingMap j O hO a := by
    apply (sectionEquiv j O hO).injective
    rw [sectionEquiv_chartRingMap]
    exact hφ a
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [differentialMap_D, toSheaf_D, localCoefficientMap_D]
      simpa only [hmap] using chartDerivative_chartRingMap j e O hO a
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [differentialMap_smul, map_smul, map_smul, hx, map_smul]
      change φ a * φ (e x) = φ (a * e x)
      exact (map_mul φ a (e x)).symm

/-- The actual image of the normalized affine differential frame has
coefficient one before either of the two chart derivations is glued. -/
theorem localCoefficientMap_normalized_frame (O : Y.Opens) (hO : O ≤ j.opensRange)
    (φ : letI := sectionAlgebra Y.sheaf c O
      A →ₐ[ℂ] SectionRing Y.sheaf O)
    (hφ : ∀ a : A, j.app O (φ a) = algebraMap A (AffineSections A (j ⁻¹ᵁ O)) a) :
    letI := sectionAlgebra Y.sheaf c O
    localCoefficientMap j c hcoeff e O hO
      (toSheaf Y.sheaf c O (differentialMap φ (e.symm 1))) = 1 := by
  letI := sectionAlgebra Y.sheaf c O
  rw [localCoefficientMap_on_form j c hcoeff e O hO φ hφ,
    LinearEquiv.apply_symm_apply, map_one]

open CycleQ2GeometricTwistedFrameMap

/-- The inverse-image chart section map is the original scheme map after
the tautological restriction to its image. -/
theorem appIso_preimage_restrict (O : Y.Opens) (a : Γ(Y, O)) :
    (j.appIso (j ⁻¹ᵁ O)).hom
      (Y.presheaf.map (homOfLE (j.image_preimage_le O)).op a) = j.app O a := by
  have hn := j.map_appLE (j.preimage_image_eq (j ⁻¹ᵁ O)).ge
    (homOfLE (j.image_preimage_le O)).op
  rw [← j.appIso_hom'] at hn
  have hh := congrArg (fun g : Γ(Y, O) ⟶ Γ(Spec (CommRingCat.of A), j ⁻¹ᵁ O) => g a) hn
  change (j.appIso (j ⁻¹ᵁ O)).hom
      (Y.presheaf.map (homOfLE (j.image_preimage_le O)).op a) =
    j.appLE O (j ⁻¹ᵁ O) _ a at hh
  rw [j.appLE_eq_app] at hh
  exact hh

theorem chartDerivative_preimage_restrict (O : Y.Opens) (hO : O ≤ j.opensRange)
    (a : Γ(Y, O)) :
    Y.presheaf.map (homOfLE (j.image_preimage_le O)).op (chartDerivative j e O hO a) =
      (j.appIso (j ⁻¹ᵁ O)).inv
        (CycleQ2GeometricStructureDerivation.sectionDerivative e (j ⁻¹ᵁ O)
          ((j.appIso (j ⁻¹ᵁ O)).hom
            (Y.presheaf.map (homOfLE (j.image_preimage_le O)).op a))) := by
  apply (j.appIso (j ⁻¹ᵁ O)).commRingCatIsoToRingEquiv.injective
  change (j.appIso (j ⁻¹ᵁ O)).hom
      (Y.presheaf.map (homOfLE (j.image_preimage_le O)).op (chartDerivative j e O hO a)) =
    (j.appIso (j ⁻¹ᵁ O)).hom ((j.appIso (j ⁻¹ᵁ O)).inv _)
  rw [Iso.inv_hom_id_apply, appIso_preimage_restrict, appIso_preimage_restrict]
  exact sectionEquiv_chartDerivative j e O hO a

variable (M : SheafOfModules.{0} (ringSheaf Y.sheaf))
  (d : M.val.Derivation' (coefficientMap Y.sheaf c))
  (hc : CoefficientCompatible j c)

/-- The actual chart frame, placed on the original open image of the
chart by its tautological equality with the image of the affine top. -/
def chartRangeFrame : M.val.obj (op j.opensRange) :=
  restrict Y.sheaf M j.image_top_eq_opensRange.ge (chartFrame j c M d hc e)

/-- The affine derivation factorization holds on every actual subopen of
the chart image, expressed with the original scheme's sections and the
already constructed coefficient derivation. -/
theorem chartDerivation_factorization_subopen (O : Y.Opens) (hO : O ≤ j.opensRange)
    (a : Γ(Y, O)) :
    d.d a = chartDerivative j e O hO a •
      restrict Y.sheaf M hO (chartRangeFrame j c e M d hc) := by
  have hlocal := chartDerivation_factorization_section j c M d hc e (j ⁻¹ᵁ O)
    (Y.presheaf.map (homOfLE (j.image_preimage_le O)).op a)
  rw [← chartDerivative_preimage_restrict j e O hO a] at hlocal
  have hframe :
      M.val.map (j.opensFunctor.op.map (homOfLE (show j ⁻¹ᵁ O ≤ ⊤ from le_top)).op)
        (chartFrame j c M d hc e) =
      restrict Y.sheaf M (j.image_preimage_le O)
        (restrict Y.sheaf M hO (chartRangeFrame j c e M d hc)) := by
    change restrict Y.sheaf M (j.image_mono (show j ⁻¹ᵁ O ≤ ⊤ from le_top))
        (chartFrame j c M d hc e) = _
    rw [chartRangeFrame, restrict_comp, restrict_comp]
  rw [hframe] at hlocal
  have hn := d.d_map (homOfLE (j.image_preimage_le O)).op a
  change d.d (Y.presheaf.map (homOfLE (j.image_preimage_le O)).op a) =
    restrict Y.sheaf M (j.image_preimage_le O) (d.d a) at hn
  rw [hn] at hlocal
  have heq : restrict Y.sheaf M (j.image_preimage_le O) (d.d a) =
      restrict Y.sheaf M (j.image_preimage_le O)
        (chartDerivative j e O hO a • restrict Y.sheaf M hO (chartRangeFrame j c e M d hc)) :=
    hlocal.trans (restrict_smul Y.sheaf M (j.image_preimage_le O)
      (chartDerivative j e O hO a)
      (restrict Y.sheaf M hO (chartRangeFrame j c e M d hc))).symm
  have hback : O ≤ j ''ᵁ (j ⁻¹ᵁ O) := by
    rw [j.image_preimage_eq_opensRange_inf]
    exact le_inf hO le_rfl
  have hh := congrArg (restrict Y.sheaf M hback) heq
  simpa only [restrict_comp, restrict_self] using hh

#print axioms pushforwardCoefficient
#print axioms localCoefficientMap_D
#print axioms localCoefficientMap_restrict
#print axioms localCoefficientMap_normalized_frame
#print axioms chartDerivation_factorization_subopen

end CycleQ2GeometricChartCoefficient
end

end SourceGeometricChartCoefficient

end ConsolidatedGeometricChartCoefficient
