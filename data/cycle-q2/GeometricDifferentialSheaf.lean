import Proposal.GeometricProjectiveCharts
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Topology.Sheaves.Functors

/-!
# The actual sheaf of complex differentials on the projective curve

The module of differentials on each ring of sections is formed using the
universal Kähler construction, with restriction induced by the actual ring
restriction. Sheafification supplies a genuine sheaf of structure-ring
modules. Its universal property for sheaf-valued complex derivations is
proved from the two adjunctions; no differential comparison is assumed.

The construction is specialized to the actual projective curve via its
canonical map to the spectrum of its degree-zero ring and the coefficient
map from the complex numbers. Identifying this sheaf with the existing
degree-one twist and constructing a Serre trace are further steps.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricDifferentialSheaf

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

def constantComplex (X : TopCat.{0}) : (Opens X)ᵒᵖ ⥤ CommRingCat.{0} :=
  (Functor.const _).obj (CommRingCat.of ℂ)

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤))

/-- A scalar acts on an open by restriction of its actual global section. -/
def coefficientOn (O : Opens X) : ℂ →+* R.obj.obj (op O) :=
  (R.obj.map (homOfLE (show O ≤ ⊤ from le_top)).op).hom.comp c

/-- The coefficient homomorphisms form a morphism of ring presheaves. -/
def coefficientMap : constantComplex X ⟶ R.obj where
  app O := CommRingCat.ofHom (coefficientOn R c O.unop)
  naturality {O P} f := by
    ext z
    change coefficientOn R c P.unop z = R.obj.map f (coefficientOn R c O.unop z)
    unfold coefficientOn
    change R.obj.map (homOfLE le_top).op (c z) =
      (R.obj.map (homOfLE le_top).op ≫ R.obj.map f) (c z)
    rw [← R.obj.map_comp]
    congr 2

def ringSheaf : X.Sheaf RingCat.{0} :=
  (sheafCompose _ (forget₂ CommRingCat RingCat)).obj R

/-- The actual universal Kähler modules and their actual restriction maps. -/
def differentialPresheaf : PresheafOfModules.{0} (ringSheaf R).obj :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' (coefficientMap R c)

/-- The sheaf of relative complex differentials, obtained by sheafification. -/
def differentialSheaf : SheafOfModules.{0} (ringSheaf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj
    (differentialPresheaf R c)

/-- The canonical map from actual sectionwise Kähler modules to their sheaf. -/
def toDifferentialSheaf :
    differentialPresheaf R c ⟶ (differentialSheaf R c).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
    (differentialPresheaf R c)

/-- The sheaf-valued universal differential, retaining the literal
sectionwise universal differential before sheafification. -/
def universalDifferential :
    (differentialSheaf R c).val.Derivation' (coefficientMap R c) :=
  (PresheafOfModules.DifferentialsConstruction.derivation' (coefficientMap R c)).postcomp
    (toDifferentialSheaf R c)

/-- The sectionwise universal property, as a bijection of actual morphisms. -/
def presheafHomEquiv (M : PresheafOfModules.{0} (ringSheaf R).obj) :
    (differentialPresheaf R c ⟶ M) ≃ M.Derivation' (coefficientMap R c) where
  toFun := (PresheafOfModules.DifferentialsConstruction.derivation' (coefficientMap R c)).postcomp
  invFun := (PresheafOfModules.DifferentialsConstruction.isUniversal' (coefficientMap R c)).desc
  left_inv f :=
    (PresheafOfModules.DifferentialsConstruction.isUniversal' (coefficientMap R c)).postcomp_injective _ _
        ((PresheafOfModules.DifferentialsConstruction.isUniversal' (coefficientMap R c)).fac _)
  right_inv :=
    (PresheafOfModules.DifferentialsConstruction.isUniversal' (coefficientMap R c)).fac

/-- Morphisms from the constructed differential sheaf correspond precisely
to complex derivations with values in the given actual sheaf of modules. -/
def sheafHomEquiv (M : SheafOfModules.{0} (ringSheaf R)) :
    (differentialSheaf R c ⟶ M) ≃ M.val.Derivation' (coefficientMap R c) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf R).obj)).trans
    (presheafHomEquiv R c M.val)

theorem sheafHomEquiv_apply (M : SheafOfModules.{0} (ringSheaf R))
    (f : differentialSheaf R c ⟶ M) :
    sheafHomEquiv R c M f = (universalDifferential R c).postcomp f.val := by
  ext O z
  rfl

/-- The unique sheaf morphism induced by an actual complex derivation. -/
def differentialLift (M : SheafOfModules.{0} (ringSheaf R))
    (d : M.val.Derivation' (coefficientMap R c)) : differentialSheaf R c ⟶ M :=
  (sheafHomEquiv R c M).symm d

theorem differentialLift_fac (M : SheafOfModules.{0} (ringSheaf R))
    (d : M.val.Derivation' (coefficientMap R c)) :
    (universalDifferential R c).postcomp (differentialLift R c M d).val = d := by
  rw [← sheafHomEquiv_apply]
  exact (sheafHomEquiv R c M).apply_symm_apply d

theorem differentialLift_unique (M : SheafOfModules.{0} (ringSheaf R))
    (f g : differentialSheaf R c ⟶ M)
    (h : (universalDifferential R c).postcomp f.val =
      (universalDifferential R c).postcomp g.val) : f = g := by
  apply (sheafHomEquiv R c M).injective
  simpa only [sheafHomEquiv_apply] using h

/-! ## Specialization to the literal projective curve -/

open CycleQ2GeometricProjectiveCurve

def projectiveCoefficient (r θ : ℂ) : ℂ →+* curveGrade r θ 0 :=
  algebraMap ℂ (curveGrade r θ 0)

def projectiveToComplex (r θ : ℂ) : projectiveCurve r θ ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero (curveGrade r θ) ≫
    Spec.map (CommRingCat.ofHom (projectiveCoefficient r θ))

/-- The global coefficient map induced by the actual structure morphism. -/
def projectiveGlobalCoefficient (r θ : ℂ) : ℂ →+* Γ(projectiveCurve r θ, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (projectiveToComplex r θ).appTop).hom

/-- A genuine differential sheaf on the actual projective curve, with the
complex structure supplied by its coefficient ring. -/
def projectiveDifferentialSheaf (r θ : ℂ) :
    SheafOfModules.{0} (ringSheaf (projectiveCurve r θ).sheaf) :=
  differentialSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)

def projectiveUniversalDifferential (r θ : ℂ) :=
  universalDifferential (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)

def projectiveDifferentialHomEquiv (r θ : ℂ)
    (M : SheafOfModules.{0} (ringSheaf (projectiveCurve r θ).sheaf)) :=
  sheafHomEquiv (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) M

end CycleQ2GeometricDifferentialSheaf

end
