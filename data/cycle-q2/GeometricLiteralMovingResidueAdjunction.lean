import Proposal.GeometricLiteralMovingResidueExact
import Proposal.GeometricLiteralMovingResidueFaces
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# The moving equation and the curve's Kähler one-forms

The conormal wedge kills the differential of the moving equation and descends
to the actual quotient by that equation. Its target is the canonical
numerator module modulo the same equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingResidueAdjunction

section Quotient

variable {R M : Type*} [CommRing R] [Algebra ℂ R] [AddCommGroup M] [Module R M]
    [Module ℂ M] [IsScalarTower ℂ R M] (e : R)

abbrev eqIdeal := Ideal.span {e}
abbrev eqModule := eqIdeal e • (⊤ : Submodule R M)
abbrev Numerators := M ⧸ (eqModule (M := M) e)

private instance : IsScalarTower ℂ (R ⧸ eqIdeal e) (Numerators (M := M) e) :=
  (Module.isTorsionBySet_quotient_ideal_smul M (eqIdeal e)).isScalarTower

variable (d : Derivation ℂ R M) (he : d e = 0)

include he in
private theorem equation_mem_kernel :
    (eqIdeal e).restrictScalars ℂ ≤ LinearMap.ker
      (((eqModule (M := M) e).mkQ.restrictScalars ℂ).comp d.toLinearMap) := by
  intro x hx
  change x ∈ Ideal.span {e} at hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton.mp hx
  change Submodule.Quotient.mk (p := eqModule (M := M) e) (d (e * a)) = 0
  rw [Derivation.leibniz, he, smul_zero, add_zero, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton e)) Submodule.mem_top

private def coefficientDer : (R ⧸ eqIdeal e) →ₗ[ℂ] Numerators (M := M) e :=
  ((eqIdeal e).restrictScalars ℂ).liftQ
    (((eqModule (M := M) e).mkQ.restrictScalars ℂ).comp d.toLinearMap)
    (equation_mem_kernel e d he) ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv ℂ (eqIdeal e)).symm.toLinearMap

private theorem coefficientDer_mk (x : R) :
    coefficientDer e d he (Ideal.Quotient.mk (eqIdeal e) x) =
      (eqModule (M := M) e).mkQ (d x) := rfl

/-- A derivation which vanishes on a Cartier equation induces a derivation
on its quotient, after reducing its values modulo the equation. -/
def quotientDerivative : Derivation ℂ (R ⧸ eqIdeal e) (Numerators (M := M) e) where
  toLinearMap := coefficientDer e d he
  map_one_eq_zero' := by
    change coefficientDer e d he (Ideal.Quotient.mk (eqIdeal e) 1) = 0
    rw [coefficientDer_mk, d.map_one_eq_zero, map_zero]
  leibniz' := by
    intro x y
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
    change coefficientDer e d he ((Ideal.Quotient.mk (eqIdeal e) a) * _) = _
    rw [← map_mul, coefficientDer_mk, Derivation.leibniz, map_add]
    rfl

/-- The resulting map on ordinary Kähler differentials of the curve ring. -/
def quotientDifferential :
    KaehlerDifferential ℂ (R ⧸ eqIdeal e) →ₗ[R ⧸ eqIdeal e] Numerators (M := M) e :=
  (quotientDerivative e d he).liftKaehlerDifferential

theorem quotientDifferential_D (x : R) :
    quotientDifferential e d he
      (KaehlerDifferential.D ℂ _ (Ideal.Quotient.mk (eqIdeal e) x)) =
      (eqModule (M := M) e).mkQ (d x) := by
  rw [quotientDifferential, Derivation.liftKaehlerDifferential_comp_D]
  exact coefficientDer_mk e d he x

end Quotient

section MovingCokernel

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle (Surface)
open CycleQ2SeedSectionDivisorTransitions (FrameData)
open CycleQ2SeedSectionAffineInjective (ChartRegular)
open CycleQ2CanonicalResidueSheaf (CanonicalForms)
open CycleQ2LiteralMovingResiduePole (poleMap poleOfNumerator regular_eq_poleOfNumerator)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2LiteralMovingResidueExact (regularInclusion residueQuotient)
open CycleQ2LiteralMovingResidueFaces (frameEquation)
open scoped Pointwise

local instance canonicalSectionModule (W : Surface.Opens) :
    Module Γ(Surface,W) (CanonicalForms.val.obj (op W)) := (CanonicalForms.val.obj (op W)).isModule

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) {W : Surface.Opens} (j : FrameData W)

private abbrev numeratorMultiples :=
  (Ideal.span {frameEquation t j} : Ideal Γ(Surface,W)) •
    (⊤ : Submodule Γ(Surface,W) (CanonicalForms.val.obj (op W)))

private def numeratorProjection : CanonicalForms.val.obj (op W) →+ (residueQuotient t).obj.obj (op W) :=
  ((cokernel.π (regularInclusion t)).hom.app (op W)).hom.comp (poleMap t ht j)

private theorem numeratorMultiples_le_ker :
    (numeratorMultiples t j).toAddSubgroup ≤ (numeratorProjection t ht j).ker := by
  intro x hx
  change x ∈ (Ideal.span {frameEquation t j} : Ideal Γ(Surface,W)) •
    (⊤ : Submodule Γ(Surface,W) (CanonicalForms.val.obj (op W))) at hx
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨u, -, rfl⟩ := hx
  change (cokernel.π (regularInclusion t)).hom.app (op W)
    (poleOfNumerator t ht j (frameEquation t j • u)) = 0
  rw [frameEquation, ← regular_eq_poleOfNumerator]
  exact congrArg (fun f : addSheaf CanonicalForms ⟶ residueQuotient t => f.hom.app (op W) u)
    (cokernel.condition (regularInclusion t))

/-- The class of a pole in the actual quotient sheaf only depends on its
numerator modulo the Cartier equation. -/
def numeratorToResidue :
    ((CanonicalForms.val.obj (op W)) ⧸ (numeratorMultiples t j)) →+
      (residueQuotient t).obj.obj (op W) :=
  QuotientAddGroup.lift _ (numeratorProjection t ht j) (numeratorMultiples_le_ker t ht j)

theorem numeratorToResidue_mk (σ : CanonicalForms.val.obj (op W)) :
    numeratorToResidue t ht j ((numeratorMultiples t j).mkQ σ) =
      (cokernel.π (regularInclusion t)).hom.app (op W) (poleMap t ht j σ) := rfl

private theorem evaluateNumerator (σ : CanonicalForms.val.obj (op W)) :
    (poleMap t ht j σ).val.app (op (Over.mk (𝟙 W)))
      (CycleQ2LiteralMovingResiduePole.frame t ht (j.restrict le_rfl) 1) = σ := by
  change (poleOfNumerator t ht j σ).val.app _ _ = _
  exact (CycleQ2LiteralMovingResiduePole.poleOfNumerator_app_frame t ht j σ (Over.mk (𝟙 W)) 1).trans
    ((one_smul Γ(Surface,W) (CanonicalForms.val.map (𝟙 (op W)) σ : CanonicalForms.val.obj (op W))).trans
      (ConcreteCategory.congr_hom (CanonicalForms.val.presheaf.map_id (op W)) σ))

private theorem poleMap_injective : Function.Injective (poleMap t ht j) := by
  intro x y h
  rw [← evaluateNumerator t ht j x, ← evaluateNumerator t ht j y, h]

/-- On any pivot open, including nonaffine subopens, the numerator quotient
embeds in sections of the sheaf quotient. -/
theorem numeratorToResidue_injective : Function.Injective (numeratorToResidue t ht j) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨x, rfl⟩ := (numeratorMultiples t j).mkQ_surjective z
  rw [numeratorToResidue_mk] at hz
  obtain ⟨y, hy⟩ := CycleQ2CechTwoToDerived.sections_exact
    (CycleQ2LiteralMovingResidueExact.residueShortExact t ht) W (poleMap t ht j x) hz
  change CanonicalForms.val.obj (op W) at y
  change (CycleQ2LocalHomFrame.idealRegularInclusion
    (CycleQ2SeedSectionSheafCurveBinding.curveToSurface t) CanonicalForms).val.app (op W) y =
      poleMap t ht j x at hy
  rw [regular_eq_poleOfNumerator t ht j] at hy
  have he : frameEquation t j • y = x := poleMap_injective t ht j hy
  change Submodule.Quotient.mk (p := numeratorMultiples t j) x = 0
  rw [Submodule.Quotient.mk_eq_zero, ← he]
  exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top


end MovingCokernel
section Surface

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricExteriorSheaf
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralMovingResidueFaces
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionAffineInjective
  CycleQ2LiteralMovingResiduePole CycleQ2LiteralMovingResidueExact
open CycleQ2CanonicalResidueSheaf (CanonicalForms)

variable {W : Surface.Opens}

local instance surfaceAlg (V : Surface.Opens) : Algebra ℂ (SectionRing Surface.sheaf V) :=
  sectionAlgebra Surface.sheaf globalCoefficient V
local instance canonicalModule (V : Surface.Opens) :
    Module (SectionRing Surface.sheaf V) (CanonicalForms.val.obj (op V)) := (CanonicalForms.val.obj (op V)).isModule
local instance canonicalComplexModule (V : Surface.Opens) : Module ℂ (CanonicalForms.val.obj (op V)) :=
  Module.compHom _ (algebraMap ℂ (SectionRing Surface.sheaf V))
local instance canonicalComplexTower (V : Surface.Opens) :
    IsScalarTower ℂ (SectionRing Surface.sheaf V) (CanonicalForms.val.obj (op V)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private abbrev equationOn (t : Fin 3 → ℂ) (j : FrameData W) : SectionRing Surface.sheaf W := frameEquation t j

/-- The canonical two-form given by wedging with the actual moving equation's
differential in the first slot. -/
def numeratorLinear (t : Fin 3 → ℂ) (j : FrameData W) :
    OneForms W →ₗ[(SectionRing Surface.sheaf W)] CanonicalForms.val.obj (op W) := by
  let α := equationDifferential W (equationOn t j)
  let F := exteriorPower.ιMulti (SectionRing Surface.sheaf W) 2 (M := OneForms W)
  have upd (b : OneForms W) : Function.update ![α,b] 1 = fun c => ![α,c] := by
    funext c i
    fin_cases i <;> rfl
  exact (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W).comp
    (show OneForms W →ₗ[(SectionRing Surface.sheaf W)] ⋀[(SectionRing Surface.sheaf W)]^2 (OneForms W) from
    { toFun := fun β => F ![α,β]
      map_add' x y := by simpa only [upd x] using F.map_update_add ![α,x] 1 x y
      map_smul' a x := by
        change F ![α,a • x] = a • F ![α,x]
        simpa only [upd x] using F.map_update_smul ![α,x] 1 a x })

theorem numeratorLinear_apply (t : Fin 3 → ℂ) (j : FrameData W) (β : OneForms W) :
    numeratorLinear t j β = poleNumerator t j β := rfl

def nativeDerivation (t : Fin 3 → ℂ) (j : FrameData W) :
    Derivation ℂ (SectionRing Surface.sheaf W) (CanonicalForms.val.obj (op W)) :=
  ((numeratorLinear t j).comp (toSheaf Surface.sheaf globalCoefficient W)).compDer
    (KaehlerDifferential.D ℂ (SectionRing Surface.sheaf W))

theorem nativeDerivation_equation (t : Fin 3 → ℂ) (j : FrameData W) :
    nativeDerivation t j (equationOn t j) = 0 := by
  let α := equationDifferential W (equationOn t j)
  change exteriorSection Surface.sheaf DifferentialSheaf.val 2 W
    (exteriorPower.ιMulti (SectionRing Surface.sheaf W) 2 ![α,α]) = 0
  rw [(exteriorPower.ιMulti (SectionRing Surface.sheaf W) 2).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide),
    map_zero]

/-- The conormal wedge is defined on Kähler one-forms of the quotient by the
actual row equation on the surface pivot. -/
def chartAdjunction (t : Fin 3 → ℂ) (j : FrameData W) :=
  quotientDifferential (equationOn t j) (nativeDerivation t j) (nativeDerivation_equation t j)

theorem chartAdjunction_D (t : Fin 3 → ℂ) (j : FrameData W) (x : (SectionRing Surface.sheaf W)) :
    chartAdjunction t j
      (KaehlerDifferential.D ℂ _ (Ideal.Quotient.mk (eqIdeal (equationOn t j)) x)) =
      (eqModule (M := CanonicalForms.val.obj (op W)) (equationOn t j)).mkQ
        (poleNumerator t j (equationDifferential W x)) :=
  quotientDifferential_D _ _ _ x

/-- This is the same conormal wedge on every one-form, by the universal
spanning property of the ordinary Kähler generators. -/
theorem chartAdjunction_map (t : Fin 3 → ℂ) (j : FrameData W)
    (ω : KaehlerDifferential ℂ (SectionRing Surface.sheaf W)) :
    chartAdjunction t j (KaehlerDifferential.map ℂ ℂ (SectionRing Surface.sheaf W) _ ω) =
      (eqModule (M := CanonicalForms.val.obj (op W)) (equationOn t j)).mkQ
        (poleNumerator t j (toSheaf Surface.sheaf globalCoefficient W ω)) := by
  let I := eqIdeal (equationOn t j)
  let C := chartAdjunction t j
  let Q := (eqModule (M := CanonicalForms.val.obj (op W)) (equationOn t j)).mkQ
  let L := (numeratorLinear t j).comp (toSheaf Surface.sheaf globalCoefficient W)
  change C (KaehlerDifferential.map ℂ ℂ (SectionRing Surface.sheaf W) ((SectionRing Surface.sheaf W) ⧸ I) ω) = Q (L ω)
  have hω : ω ∈ Submodule.span (SectionRing Surface.sheaf W) (Set.range (KaehlerDifferential.D ℂ (SectionRing Surface.sheaf W))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x,rfl⟩ := hx
    rw [KaehlerDifferential.map_D]
    exact chartAdjunction_D t j x
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx =>
    let m := KaehlerDifferential.map ℂ ℂ (SectionRing Surface.sheaf W) ((SectionRing Surface.sheaf W) ⧸ I)
    have hm : m (r • x) = Ideal.Quotient.mk I r • m x := by
      exact m.map_smul r x
    change C (m (r • x)) = Q (L (r • x))
    rw [hm, C.map_smul, hx, L.map_smul, Q.map_smul]
    rfl

end Surface

namespace AffineFrame
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionDivisorFrames
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionSheafKernel
  CycleQ2SeedSectionSheafCurveBinding CycleQ2SeedSectionAffineInjective
  CycleQ2GeometricIntrinsicNormal CycleQ2SeedSectionSheafImage
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSectionDifferentials
  CycleQ2GeometricAffineChartSections
open CycleQ2LiteralNativeDifferentialSections (globalCoefficient)

abbrev equation {W : Surface.Opens} (t : Fin 3 → ℂ) (j : FrameData W) : Γ(Surface,W) :=
  sectionRows t j.chart W j.within j.pivot.1

abbrev Curve (t : Fin 3 → ℂ) := CycleQ2SpecializedProjectiveCurve.specializedCurve CycleQ2SeedSectionCurveRows.seed t
abbrev CurveRing (t : Fin 3 → ℂ) (W : Surface.Opens) := Γ(Curve t, (curveToSurface t) ⁻¹ᵁ W)

theorem curveKer_eq_span {W : Surface.Opens} (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (j : FrameData W) :
    RingHom.ker ((curveToSurface t).app W).hom = Ideal.span {equation t j} := by
  apply le_antisymm
  · intro x hx
    let e := kernelIdealSectionEquiv (curveToSurface t) W
    let v := e.symm ⟨x,hx⟩
    let F := curveIdealFrame t ht j.chart W j.within j.pivot j.pivotUnit j.pivot_eq
    let r := F.symm v
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨r, ?_⟩
    have hr := curveIdealFrame_coordinate t ht j.chart W j.within j.pivot j.pivotUnit j.pivot_eq r
    change (e (F r) : Γ(Surface,W)) = r * equation t j at hr
    rw [show F r = v from F.apply_symm_apply _, show e v = ⟨x,hx⟩ from e.apply_symm_apply _] at hr
    exact hr.symm
  · apply Ideal.span_le.mpr
    intro x hx
    obtain rfl : x = equation t j := hx
    change (curveToSurface t).app W _ = 0
    exact sectionRows_curve_zero t j.chart W j.within j.pivot.1

def curveQuotientEquiv {W : Surface.Opens} (hW : IsAffineOpen W) (t : Fin 3 → ℂ)
    (ht : ∀ i, ChartRegular t i) (j : FrameData W) :
    (Γ(Surface,W) ⧸ Ideal.span {equation t j}) ≃+* CurveRing t W :=
  (Ideal.quotEquivOfEq (curveKer_eq_span t ht j).symm).trans
    (((curveToSurface t).app W).hom.quotientKerEquivOfSurjective ((curveToSurface t).app_surjective W hW))

theorem curveQuotientEquiv_mk {W : Surface.Opens} (hW : IsAffineOpen W) (t : Fin 3 → ℂ)
    (ht : ∀ i, ChartRegular t i) (j : FrameData W) (x : Γ(Surface,W)) :
    curveQuotientEquiv hW t ht j (Ideal.Quotient.mk _ x) = (curveToSurface t).app W x := by
  rw [curveQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

local instance surfaceAlgebra (W : Surface.Opens) : Algebra ℂ Γ(Surface,W) :=
  sectionAlgebra Surface.sheaf globalCoefficient W

abbrev curveCoefficient (t : Fin 3 → ℂ) :=
  schemeCoefficient ((curveToSurface t) ≫ CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1)

local instance curveAlgebra (t : Fin 3 → ℂ) (W : Surface.Opens) : Algebra ℂ (CurveRing t W) :=
  sectionAlgebra (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ W)

theorem curveMap_constants {W : Surface.Opens} (t : Fin 3 → ℂ) (c : ℂ) :
    (curveToSurface t).app W (algebraMap ℂ Γ(Surface,W) c) = algebraMap ℂ (CurveRing t W) c :=
  coefficientOn_app (curveToSurface t) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) W c

def curveQuotientAlgEquiv {W : Surface.Opens} (hW : IsAffineOpen W) (t : Fin 3 → ℂ)
    (ht : ∀ i, ChartRegular t i) (j : FrameData W) :
    (Γ(Surface,W) ⧸ Ideal.span {equation t j}) ≃ₐ[ℂ] CurveRing t W :=
  AlgEquiv.ofRingEquiv (f := curveQuotientEquiv hW t ht j) fun c =>
    (curveQuotientEquiv_mk hW t ht j (algebraMap ℂ Γ(Surface,W) c)).trans (curveMap_constants t c)

end AffineFrame

end CycleQ2LiteralMovingResidueAdjunction
end

#print axioms CycleQ2LiteralMovingResidueAdjunction.quotientDifferential_D
#print axioms CycleQ2LiteralMovingResidueAdjunction.chartAdjunction_map
#print axioms CycleQ2LiteralMovingResidueAdjunction.numeratorToResidue_injective
#print axioms CycleQ2LiteralMovingResidueAdjunction.AffineFrame.curveQuotientAlgEquiv
