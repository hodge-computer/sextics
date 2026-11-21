import Proposal.GeometricExteriorLocalFrames
import Proposal.GeometricIntrinsicNormal
import Proposal.GeometricAffineOpenOrdinaryDifferentials

/-!
# Detecting maps from an exterior sheaf on affine wedges

The canonical exterior presentation stays locally bijective after restriction to
an open. A basis of subopens therefore detects morphisms out of the sheafified
exterior power by evaluating them on wedges of local sections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiEvaluationExt

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricExteriorSheaf
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricExteriorLocalFrames
  CycleQ2LocalSheafificationFrame

variable {X : Scheme.{0}} (M N : X.Modules) (n : ℕ) (U : X.Opens)

private abbrev E := exteriorSheaf X.sheaf M.val n
private abbrev raw := exteriorPresheaf X.sheaf.obj M.val n
private abbrev presentation := @overPresentation (show TopCat from X)
  (ringSheaf X.sheaf) (raw M n) U (E M n) (toExteriorSheaf X.sheaf M.val n)

private def evaluateRaw (f : LocalLinearHom X.sheaf (E M n) N U) (W : Over U) :
    (⋀[Γ(X,W.left)]^n (M.val.obj (op W.left))) →ₗ[Γ(X,W.left)] N.val.obj (op W.left) :=
  (((localLinearHomEquiv X.sheaf (E M n) N U f).val.app (op W)).hom).comp
    (exteriorSection X.sheaf M.val n W.left)

/-- Agreement on pure wedges on members of a basis detects the entire
restricted morphism, including its action on sheafified sections. -/
theorem localLinearHom_ext_of_basis (S : Set X.Opens) (hS : Opens.IsBasis S)
    (f g : LocalLinearHom X.sheaf (exteriorSheaf X.sheaf M.val n) N U)
    (hfg : ∀ (W : X.Opens) (h : W ≤ U), W ∈ S → ∀ a : Fin n → M.val.obj (op W),
      f.val.app (op (Over.mk (homOfLE h))) (wedgeSection X.sheaf M.val n W a) =
        g.val.app (op (Over.mk (homOfLE h))) (wedgeSection X.sheaf M.val n W a)) : f = g := by
  let := @overPresentation_locallyInjective (show TopCat from X) (ringSheaf X.sheaf)
    (raw M n) U (E M n) (toExteriorSheaf X.sheaf M.val n)
    (exteriorPresentation_locallyInjective X.sheaf M.val n)
  let := @overPresentation_locallySurjective (show TopCat from X) (ringSheaf X.sheaf)
    (raw M n) U (E M n) (toExteriorSheaf X.sheaf M.val n)
    (exteriorPresentation_locallySurjective X.sheaf M.val n)
  have hraw (W : X.Opens) (h : W ≤ U) (hW : W ∈ S) :
      evaluateRaw M N n U f (Over.mk (homOfLE h)) =
        evaluateRaw M N n U g (Over.mk (homOfLE h)) := by
    apply exteriorPower.linearMap_ext
    exact AlternatingMap.ext (hfg W h hW)
  apply (localLinearHomEquiv X.sheaf (E M n) N U).injective
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.homEquivOfIsLocallyBijective
    (presentation M n U) (N.over U).isSheaf).injective
  apply PresheafOfModules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro x
  let z := exteriorSection X.sheaf M.val n V.unop.left x
  change f.val.app V z = g.val.app V z
  apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
  intro y hy
  obtain ⟨W,hWS,hyW,hWV⟩ := Opens.isBasis_iff_nbhd.mp hS hy
  have hWU := hWV.trans V.unop.hom.le
  let k : Over.mk (homOfLE hWU) ⟶ V.unop := Over.homMk (homOfLE hWV)
  refine ⟨W,hWV,hyW,?_⟩
  have hr := exteriorSection_restrict X.sheaf M.val n (homOfLE hWV) x
  have ha := LinearMap.congr_fun (hraw W hWU hWS)
    (exteriorMap (X.presheaf.map (homOfLE hWV).op).hom (M.val.restrictₛₗ (homOfLE hWV).op) n x)
  refine (ConcreteCategory.congr_hom (f.val.naturality k.op) z).symm.trans ?_
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (g.val.naturality k.op) z)
  change f.val.app (op (Over.mk (homOfLE hWU))) ((exteriorSheaf X.sheaf M.val n).val.map (homOfLE hWV).op z) =
    g.val.app (op (Over.mk (homOfLE hWU))) ((exteriorSheaf X.sheaf M.val n).val.map (homOfLE hWV).op z)
  rw [show (exteriorSheaf X.sheaf M.val n).val.map (homOfLE hWV).op z = _ from hr]
  exact ha

/-- Every affine subopen may be tested using arbitrary wedges of its module sections. -/
theorem localLinearHom_ext_affine
    (f g : LocalLinearHom X.sheaf (exteriorSheaf X.sheaf M.val n) N U)
    (hfg : ∀ (W : X.Opens) (h : W ≤ U), IsAffineOpen W → ∀ a : Fin n → M.val.obj (op W),
      f.val.app (op (Over.mk (homOfLE h))) (wedgeSection X.sheaf M.val n W a) =
        g.val.app (op (Over.mk (homOfLE h))) (wedgeSection X.sheaf M.val n W a)) : f = g :=
  localLinearHom_ext_of_basis M N n U _ X.isBasis_affineOpens f g hfg

open CycleQ2GeometricSectionDifferentials CycleQ2AffineOpenOrdinaryDifferentials

private theorem affine_exact_span (c : ℂ →+* Γ(X,⊤)) (W : X.Opens) (hW : IsAffineOpen W) :
    Submodule.span Γ(X,W) (Set.range ((universalDifferential X.sheaf c).d (X := op W))) = ⊤ := by
  let R := SectionRing X.sheaf W
  let : Algebra ℂ R := sectionAlgebra X.sheaf c W
  let F := toSheaf X.sheaf c W
  change Submodule.span R (Set.range (F ∘ (KaehlerDifferential.D ℂ R))) = ⊤
  rw [Set.range_comp]
  refine (Submodule.map_span F (Set.range (KaehlerDifferential.D ℂ R))).symm.trans ?_
  refine (congrArg (Submodule.map F) (KaehlerDifferential.span_range_derivation ℂ R)).trans ?_
  exact (Submodule.map_top F).trans (LinearMap.range_eq_top.mpr
    (toSheaf_bijective_of_isAffineOpen c W hW).surjective)

/-- For differentials it suffices to evaluate wedges of exact forms from
the affine coordinate ring, in any exterior degree. -/
theorem localLinearHom_ext_affine_exact (c : ℂ →+* Γ(X,⊤))
    (f g : LocalLinearHom X.sheaf (exteriorSheaf X.sheaf (differentialSheaf X.sheaf c).val n) N U)
    (hfg : ∀ (W : X.Opens) (h : W ≤ U), IsAffineOpen W → ∀ r : Fin n → Γ(X,W),
      f.val.app (op (Over.mk (homOfLE h)))
        (wedgeSection X.sheaf (differentialSheaf X.sheaf c).val n W
          (fun j => (universalDifferential X.sheaf c).d (X := op W) (r j))) =
      g.val.app (op (Over.mk (homOfLE h)))
        (wedgeSection X.sheaf (differentialSheaf X.sheaf c).val n W
          (fun j => (universalDifferential X.sheaf c).d (X := op W) (r j)))) : f = g := by
  apply localLinearHom_ext_affine (differentialSheaf X.sheaf c) N n U f g
  intro W h hW a
  let M := differentialSheaf X.sheaf c
  have he : evaluateRaw M N n U f (Over.mk (homOfLE h)) =
      evaluateRaw M N n U g (Over.mk (homOfLE h)) := by
    apply LinearMap.ext_on (exteriorPower.ιMulti_span_of_span Γ(X,W) n (M.val.obj (op W))
      (affine_exact_span c W hW))
    rintro _ ⟨b, hb, rfl⟩
    have hex (i : Fin n) : ∃ r : Γ(X,W), (universalDifferential X.sheaf c).d (X := op W) r = b i :=
      hb (Set.mem_range_self i)
    choose r hr using hex
    rw [← funext hr]
    exact hfg W h hW r
  exact LinearMap.congr_fun he (exteriorPower.ιMulti Γ(X,W) n a)

/-- In degree two the tests are exactly the ordered pairs of regular functions. -/
theorem localLinearHom_ext_affine_exact_pair (c : ℂ →+* Γ(X,⊤))
    (f g : LocalLinearHom X.sheaf (exteriorSheaf X.sheaf (differentialSheaf X.sheaf c).val 2) N U)
    (hfg : ∀ (W : X.Opens) (h : W ≤ U), IsAffineOpen W → ∀ a b : Γ(X,W),
      let d := (universalDifferential X.sheaf c).d (X := op W)
      let ω := wedgeSection X.sheaf (differentialSheaf X.sheaf c).val 2 W ![d a, d b]
      f.val.app (op (Over.mk (homOfLE h))) ω = g.val.app (op (Over.mk (homOfLE h))) ω) : f = g := by
  apply localLinearHom_ext_affine_exact N 2 U c f g
  intro W h hW r
  let d := (universalDifferential X.sheaf c).d (X := op W)
  have hr : (fun j => d (r j)) = ![d (r 0),d (r 1)] := by
    funext j
    fin_cases j <;> rfl
  rw [hr]
  exact hfg W h hW (r 0) (r 1)

end CycleQ2LiteralAbelJacobiEvaluationExt

#print axioms CycleQ2LiteralAbelJacobiEvaluationExt.localLinearHom_ext_affine
#print axioms CycleQ2LiteralAbelJacobiEvaluationExt.localLinearHom_ext_affine_exact

#print axioms CycleQ2LiteralAbelJacobiEvaluationExt.localLinearHom_ext_affine_exact_pair
