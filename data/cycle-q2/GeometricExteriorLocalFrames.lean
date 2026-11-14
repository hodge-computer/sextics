/-
SOURCE-ONLY DRAFT: unverified.
Compilation and independent kernel replay were deferred at the user's request.
The proof terms below have not been accepted as a checked certificate.
-/

import Proposal.GeometricLocalSheafificationFrame
import Proposal.GeometricExteriorSheaf
import Proposal.GeometricProjectiveCanonical

/-!
# Actual local frames of the sheafified surface exterior square

The determinant coordinates of genuine differential sections are natural
under restriction. Their normalized Jacobian coordinates therefore extend
along the canonical exterior-sheafification map to an actual local frame
on every subopen of a surface Jacobian chart. The inverse generator is
proved to be the original residue section, so the resulting decomposition
applies to arbitrary sections of the actual exterior sheaf.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricExteriorLocalFrames

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricExteriorSheaf
open CycleQ2GeometricSurfaceAdjunction CycleQ2LocalSheafificationFrame

section DeterminantRestriction

variable {R S : Type} [CommRing R] [CommRing S]
  {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]

/-- Restricting the actual ordered basis restricts its determinant coordinate. -/
theorem determinant_exteriorMap (φ : R →+* S) (f : M →ₛₗ[φ] N)
    (b : Basis (Fin 2) R M) (c : Basis (Fin 2) S N)
    (hb : ∀ i, f (b i) = c i) (ω : ⋀[R]^2 M) :
    determinantEquiv c (exteriorMap φ f 2 ω) = φ (determinantEquiv b ω) := by
  have hω : determinantEquiv b ω • exteriorPower.ιMulti R 2 b = ω := by
    apply (determinantEquiv b).injective
    rw [map_smul, determinantEquiv_wedge, smul_eq_mul, mul_one]
  calc
    _ = determinantEquiv c (exteriorMap φ f 2
        (determinantEquiv b ω • exteriorPower.ιMulti R 2 b)) :=
      congrArg (fun z => determinantEquiv c (exteriorMap φ f 2 z)) hω.symm
    _ = determinantEquiv c
        (φ (determinantEquiv b ω) • exteriorPower.ιMulti S 2 c) := by
      rw [map_smulₛₗ, exteriorMap_wedge]
      exact congrArg (fun a : Fin 2 → N => determinantEquiv c
        (φ (determinantEquiv b ω) • exteriorPower.ιMulti S 2 a)) (funext hb)
    _ = φ (determinantEquiv b ω) := by
      rw [map_smul, determinantEquiv_wedge, smul_eq_mul, mul_one]

end DeterminantRestriction

section ExteriorPresentation

variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (M : PresheafOfModules.{0} (ringSheaf R).obj) (n : ℕ)

instance exteriorPresentation_locallyInjective :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology T)
      (toExteriorSheaf R M n) := by
  change Presheaf.IsLocallyInjective (Opens.grothendieckTopology T)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology T)
      (exteriorPresheaf R.obj M n).presheaf)
  infer_instance

instance exteriorPresentation_locallySurjective :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology T)
      (toExteriorSheaf R M n) := by
  change Presheaf.IsLocallySurjective (Opens.grothendieckTopology T)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology T)
      (exteriorPresheaf R.obj M n).presheaf)
  infer_instance

variable (U : Opens T)
  (c : ∀ V : Over U,
    (⋀[R.obj.obj (op V.left)]^n (M.obj (op V.left))) ≃ₗ[R.obj.obj (op V.left)]
      R.obj.obj (op V.left))
  (hc : ∀ {V W : Over U} (a : V ⟶ W)
    (ω : ⋀[R.obj.obj (op W.left)]^n (M.obj (op W.left))),
    c V (exteriorMap (R.obj.map a.left.op).hom (M.restrictₛₗ a.left.op) n ω) =
      R.obj.map a.left.op (c W ω))

/-- The prescribed sectionwise exterior coordinates form an actual presheaf iso. -/
def exteriorPresheafOverIso :
    overPresheaf (ringSheaf R) (exteriorPresheaf R.obj M n) U ≅
      (SheafOfModules.unit ((ringSheaf R).over U)).val :=
  PresheafOfModules.isoMk (fun V => (c V.unop).toModuleIso) (by
    intro V W a
    apply ConcreteCategory.hom_ext
    intro ω
    exact hc a.unop ω)

/-- The same coordinates on arbitrary sections of the genuine exterior sheaf. -/
def exteriorSheafOverIso :
    (exteriorSheaf R M n).over U ≅ SheafOfModules.unit ((ringSheaf R).over U) :=
  overIsoOfPresentation U (toExteriorSheaf R M n)
    (exteriorPresheafOverIso R M n U c hc)

theorem exteriorSheafOverIso_exteriorSection (V : Over U)
    (ω : ⋀[R.obj.obj (op V.left)]^n (M.obj (op V.left))) :
    (exteriorSheafOverIso R M n U c hc).hom.val.app (op V)
      (exteriorSection R M n V.left ω) = c V ω :=
  isoOfPresentation_hom (overPresentation U (toExteriorSheaf R M n))
    (exteriorPresheafOverIso R M n U c hc) (op V) ω

theorem exteriorSheafOverIso_inv (V : Over U) (a : R.obj.obj (op V.left)) :
    (exteriorSheafOverIso R M n U c hc).inv.val.app (op V) a =
      exteriorSection R M n V.left ((c V).symm a) := rfl

end ExteriorPresentation

section SurfaceChart

open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
open CycleQ2GeometricFunctionalDifferentials CycleQ2GeometricSurfaceExteriorSections
open CycleQ2GeometricModuleOverFrame CycleQ2GeometricCanonicalGluing

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

theorem chartSectionBasis_restrict (b : Basis (Fin 2) A (KaehlerDifferential ℂ A))
    {V W : Over U} (a : V ⟶ W) (i : Fin 2) :
    (ChartDifferentialModule f).val.map a.op (chartSectionBasis e f h b W i) =
      chartSectionBasis e f h b V i := by
  rw [chartSectionBasis_apply, chartSectionBasis_apply,
    chartRestrictedBasisSection, chartRestrictedBasisSection,
    ← PresheafOfModules.map_comp_apply] <;> rfl

variable (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (eR : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n t)))
  (hR : eR.inv ≫ U.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))))

theorem chartResidueCoordinate_restrict {V W : Over U} (a : V ⟶ W)
    (ω : ⋀[Γ(X,W.left)]^2 ((ChartDifferentialModule f).val.obj (op W))) :
    chartResidueCoordinate f v n t eR hR V
      (exteriorMap (X.presheaf.map a.left.op).hom
        ((differentialSheaf X.sheaf (schemeCoefficient f)).val.restrictₛₗ a.left.op) 2 ω) =
      X.presheaf.map a.left.op (chartResidueCoordinate f v n t eR hR W ω) := by
  rw [chartResidueCoordinate_apply, chartResidueCoordinate_apply,
    determinant_exteriorMap _ _ _ _ (chartSectionBasis_restrict eR f hR
      (localSurfaceKaehlerBasis v n t) a), map_mul, chartSection_naturality]

/-- The actual normalized residue trivializes the sheafified exterior square
on its Jacobian chart, including all non-polynomial sheaf sections. -/
def chartResidueOverIso :
    (exteriorSheaf X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2).over U ≅
      SheafOfModules.unit ((ringSheaf X.sheaf).over U) :=
  exteriorSheafOverIso X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 U
    (chartResidueCoordinate f v n t eR hR)
    (chartResidueCoordinate_restrict f v n t eR hR)

def chartResidueLocalFrame : LocalFrame X.sheaf
    (exteriorSheaf X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2) U :=
  patchIsoOfOverFrame (chartResidueOverIso f v n t eR hR)

theorem chartResidueLocalFrame_exteriorSection (O : X.Opens) (hO : O ≤ U)
    (ω : ⋀[Γ(X,O)]^2 ((differentialSheaf X.sheaf (schemeCoefficient f)).val.obj (op O))) :
    (chartResidueLocalFrame f v n t eR hR).app O hO
      (exteriorSection X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 O ω) =
      chartResidueCoordinate f v n t eR hR (Over.mk (homOfLE hO)) ω :=
  exteriorSheafOverIso_exteriorSection X.sheaf
    (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 U
    (chartResidueCoordinate f v n t eR hR)
    (chartResidueCoordinate_restrict f v n t eR hR) (Over.mk (homOfLE hO)) ω

/-- The inverse generator is exactly the previously defined actual residue section. -/
theorem chartResidueLocalFrame_generator (O : X.Opens) (hO : O ≤ U) :
    frameGenerator (chartResidueLocalFrame f v n t eR hR) O hO =
      chartResidueSheafSection f v n t eR hR (Over.mk (homOfLE hO)) := by
  change exteriorSection X.sheaf
    (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 O
      ((chartResidueCoordinate f v n t eR hR (Over.mk (homOfLE hO))).symm 1) = _
  unfold chartResidueSheafSection
  congr 1
  apply (chartResidueCoordinate f v n t eR hR (Over.mk (homOfLE hO))).injective
  rw [LinearEquiv.apply_symm_apply, chartResidueSection_normalization]

/-- Every genuine exterior-sheaf section on the chart has its unique actual
residue coordinate. This statement is not restricted to polynomial lifts. -/
theorem chartResidueLocalFrame_reconstruction (O : X.Opens) (hO : O ≤ U)
    (s : (exteriorSheaf X.sheaf
      (differentialSheaf X.sheaf (schemeCoefficient f)).val 2).val.obj (op O)) :
    s = (frameCoordinate (chartResidueLocalFrame f v n t eR hR) O hO s) •
      chartResidueSheafSection f v n t eR hR (Over.mk (homOfLE hO)) := by
  rw [← chartResidueLocalFrame_generator]
  apply ((chartResidueLocalFrame f v n t eR hR).app O hO).injective
  rw [map_smul]
  change _ = _ * ((chartResidueLocalFrame f v n t eR hR).app O hO
    (((chartResidueLocalFrame f v n t eR hR).app O hO).symm 1))
  simp only [LinearEquiv.apply_symm_apply, mul_one, frameCoordinate]

end SurfaceChart

#print axioms determinant_exteriorMap
#print axioms exteriorSheafOverIso
#print axioms chartResidueOverIso
#print axioms chartResidueLocalFrame_generator
#print axioms chartResidueLocalFrame_reconstruction

end CycleQ2GeometricExteriorLocalFrames

end
