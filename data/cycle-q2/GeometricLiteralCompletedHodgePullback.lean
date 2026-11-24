import Proposal.GeometricExteriorPullComposition
import Proposal.GeometricLiteralAbelJacobiQPullbackDerived
import Proposal.GeometricLiteralThreefoldTestClass
import Proposal.GeometricLiteralTimeCorrespondenceCompletion

/-!
# Pullback of the Hodge class to the completed correspondence and swept image

The map into the smooth fixed threefold factors through both the closure of the
family and its scheme-theoretic image. For a native two-form cocycle each of
these schemes therefore carries a degree-one class that pulls back to the
original class on the family.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralCompletedHodgePullback

open CategoryTheory AlgebraicGeometry
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2LiteralThreefoldHodgeCech
open CycleQ2ExteriorPullComposition
open CycleQ2LiteralAbelJacobiQPullbackDerived (pullH qHodge)
open CycleQ2LiteralAbelJacobiQPullback (toThreefold familyCoefficient familyHodgeSheaf toThreefold_overComplex)
open CycleQ2LiteralAbelJacobiTimeFamily (family projection timeOpen)
open CycleQ2LiteralAbelJacobiTimeProjection (q)
open CycleQ2LiteralTimeCorrespondenceCompletion (Correspondence fromFamily fixedProjection fromFamily_toFixed)
open CycleQ2LiteralAmbientCylinder (fixedIso)
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2LiteralIncidenceTimeCurve (toComplex)
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)
open CycleQ2InjectiveCech (AbSheaf)

local instance (X : Scheme.{0}) : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _

variable {S : Scheme.{0}} (j : S ⟶ Threefold)

abbrev coefficient := schemeCoefficient (j ≫ structureMap)

abbrev twoFormSheaf := additiveForms S (coefficient j) 2

/-- Pullback of a class on the threefold using the actual map of Kähler sheaves. -/
def pullToModel : Hodge21 →+ (twoFormSheaf j).H' 1 ⊤ :=
  pullH j.base (additivePull j (coefficient j) coefficients (compatible_over j _ _ rfl) 2) 1

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)
variable (f : family V t ⟶ S) (h : f ≫ j = toThreefold V t)

include h in
private theorem overBase :
    f ≫ (j ≫ structureMap) = projection V t ≫ (timeOpen V).ι ≫ toComplex := by
  rw [← Category.assoc, h, toThreefold_overComplex]

/-- Restrict a class on the intermediate scheme to the original family. -/
def pullToFamily : (twoFormSheaf j).H' 1 ⊤ →+ (familyHodgeSheaf V t).H' 1 ⊤ :=
  pullH f.base (additivePull f (familyCoefficient V t) (coefficient j)
    (compatible_over f _ _ (overBase j V t f h)) 2) 1

private theorem pull_congr {X : Scheme.{0}} (c : ℂ →+* Γ(X, ⊤))
    (u v : X ⟶ Threefold) (hu : compatible u c coefficients) (hv : compatible v c coefficients)
    (e : u = v) :
    pullH u.base (additivePull u c coefficients hu 2) 1 =
      pullH v.base (additivePull v c coefficients hv 2) 1 := by
  subst v
  rfl

variable (ω : NativeEdges)
  (faces : ∀ (i j k : Fin 4) (hij : i < j) (hjk : j < k), Face ω i j k hij hjk)

private theorem pull_through :
    pullToFamily j V t f h (pullToModel j (hodgeClass ω faces)) =
      qHodge V t (hodgeClass ω faces) := by
  let a := hodgeCocycle ω faces
  have ha : CycleQ2FiniteInjectiveCech.IsOneCocycle _ fixedOpen a.val :=
    fun i j k W hi hj hk => (a.condition i j k W hi hj hk).symm
  let hf := compatible_over f _ _ (overBase j V t f h)
  let hg := compatible_over j (j ≫ structureMap) structureMap rfl
  let hu := CycleQ2GeometricSchemeCotangentMaps.compositionCoefficient j _ _ hg f _ hf
  let hv := compatible_over (toThreefold V t) _ _ (toThreefold_overComplex V t)
  exact (pullH_comp_cech f j (familyCoefficient V t) (coefficient j) coefficients hf hg 2
    fixedOpen a.val fixedOpen_cover ha).symm.trans
    (DFunLike.congr_fun (pull_congr (familyCoefficient V t) _ _ hu hv h) (hodgeClass ω faces))

abbrev completionMap := fixedProjection V t ≫ fixedIso.hom

abbrev sweptMap := (q V t).imageι ≫ fixedIso.hom

theorem fromFamily_completionMap : fromFamily V t ≫ completionMap V t = toThreefold V t := by
  rw [completionMap, ← Category.assoc, fromFamily_toFixed]
  rfl

theorem toImage_sweptMap : (q V t).toImage ≫ sweptMap V t = toThreefold V t := by
  rw [sweptMap, ← Category.assoc, Scheme.Hom.toImage_imageι]
  rfl

/-- The class on the completed correspondence restricts to the same derived class
on the time family as the original projection to the threefold. -/
theorem restrict_completion :
    pullToFamily (completionMap V t) V t (fromFamily V t) (fromFamily_completionMap V t)
        (pullToModel (completionMap V t) (hodgeClass ω faces)) =
      qHodge V t (hodgeClass ω faces) :=
  pull_through _ _ _ _ _ ω faces

/-- The coherent two-form class also pulls back through the actual swept subscheme. -/
theorem restrict_sweptImage :
    pullToFamily (sweptMap V t) V t (q V t).toImage (toImage_sweptMap V t)
        (pullToModel (sweptMap V t) (hodgeClass ω faces)) =
      qHodge V t (hodgeClass ω faces) :=
  pull_through _ _ _ _ _ ω faces

/-- Both factorizations recover the pullback of the actual ambient test. -/
theorem ambientTest_factorizations :
    let η := CycleQ2LiteralThreefoldTestClass.ambientTestClass
    let x := qHodge V t η
    pullToFamily (completionMap V t) V t (fromFamily V t) (fromFamily_completionMap V t)
      (pullToModel (completionMap V t) η) = x ∧
    pullToFamily (sweptMap V t) V t (q V t).toImage (toImage_sweptMap V t)
      (pullToModel (sweptMap V t) η) = x :=
  ⟨restrict_completion V t _ CycleQ2LiteralThreefoldTestClass.face,
    restrict_sweptImage V t _ CycleQ2LiteralThreefoldTestClass.face⟩

end CycleQ2LiteralCompletedHodgePullback

#print axioms CycleQ2LiteralCompletedHodgePullback.restrict_completion
#print axioms CycleQ2LiteralCompletedHodgePullback.restrict_sweptImage
