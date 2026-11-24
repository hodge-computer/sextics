import Proposal.GeometricDifferentialSheaf
import Proposal.GeometricAffineOverlap

/-!
# Mapping actual affine Kähler forms into a sheaf

A ring map into the sections on an open, compatible with the complex
coefficient map, carries affine Kähler forms into any sheaf-valued
derivation. The construction is the ordinary universal Kähler lift.
Its scalar formula, compatibility with restriction, and compatibility with
change of affine ring retain the actual section maps throughout.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSheafKaehlerMap

open CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineOverlap

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤))
  (M : SheafOfModules.{0} (ringSheaf R))
  (d : M.val.Derivation' (coefficientMap R c))
  (O : Opens X) {A : Type} [CommRing A] [Algebra ℂ A]
  (f : A →+* R.obj.obj (op O))
  (hf : ∀ z : ℂ, f (algebraMap ℂ A z) = coefficientOn R c O z)

/-- Pull back the actual sectionwise derivation along the supplied ring map. -/
def sectionDerivation :
    letI : Module A (M.val.obj (op O)) := Module.compHom _ f
    letI : Module ℂ (M.val.obj (op O)) := Module.compHom _ (algebraMap ℂ A)
    Derivation ℂ A (M.val.obj (op O)) := by
  letI : Module A (M.val.obj (op O)) := Module.compHom _ f
  letI : Module ℂ (M.val.obj (op O)) := Module.compHom _ (algebraMap ℂ A)
  exact
    { toFun := fun a => d.d (f a)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun z a => by
        change d.d (f (z • a)) = f (algebraMap ℂ A z) • d.d (f a)
        rw [Algebra.smul_def, map_mul, d.d_mul, hf]
        have hz := d.d_app (X := op O) z
        change d.d (coefficientOn R c O z) = 0 at hz
        rw [hz, smul_zero, add_zero]
      map_one_eq_zero' := by
        change d.d (f 1) = 0
        rw [map_one, d.d_one]
      leibniz' := fun a b => by
        change d.d (f (a * b)) = f a • d.d (f b) + f b • d.d (f a)
        rw [map_mul, d.d_mul] }

/-- The ordinary Kähler lift, with no chosen basis or local freeness input. -/
def sectionLift : KaehlerDifferential ℂ A →+ M.val.obj (op O) := by
  letI : Module A (M.val.obj (op O)) := Module.compHom _ f
  letI : Module ℂ (M.val.obj (op O)) := Module.compHom _ (algebraMap ℂ A)
  letI : IsScalarTower ℂ A (M.val.obj (op O)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (sectionDerivation R c M d O f hf).liftKaehlerDifferential.toAddMonoidHom

theorem sectionLift_D (a : A) :
    sectionLift R c M d O f hf (KaehlerDifferential.D ℂ A a) = d.d (f a) := by
  let : Module A (M.val.obj (op O)) := Module.compHom _ f
  let : Module ℂ (M.val.obj (op O)) := Module.compHom _ (algebraMap ℂ A)
  let : IsScalarTower ℂ A (M.val.obj (op O)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (sectionDerivation R c M d O f hf).liftKaehlerDifferential_comp_D a

theorem sectionLift_smul (a : A) (ω : KaehlerDifferential ℂ A) :
    sectionLift R c M d O f hf (a • ω) = f a • sectionLift R c M d O f hf ω := by
  let : Module A (M.val.obj (op O)) := Module.compHom _ f
  let : Module ℂ (M.val.obj (op O)) := Module.compHom _ (algebraMap ℂ A)
  let : IsScalarTower ℂ A (M.val.obj (op O)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (sectionDerivation R c M d O f hf).liftKaehlerDifferential.map_smul a ω

/-- Values on universal differentials and the actual scalar formula
characterize the lift on every affine Kähler form. -/
theorem sectionLift_unique (l : KaehlerDifferential ℂ A →+ M.val.obj (op O))
    (hl_smul : ∀ a ω, l (a • ω) = f a • l ω)
    (hl_D : ∀ a, l (KaehlerDifferential.D ℂ A a) = d.d (f a)) :
    sectionLift R c M d O f hf = l := by
  ext ω
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact (sectionLift_D R c M d O f hf a).trans (hl_D a).symm
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => rw [sectionLift_smul, hl_smul, hx]

/-- The sectionwise Kähler lift commutes with actual module-sheaf maps. -/
theorem sectionLift_postcomp (N : SheafOfModules.{0} (ringSheaf R))
    (ψ : M ⟶ N) (ω : KaehlerDifferential ℂ A) :
    sectionLift R c N (d.postcomp ψ.val) O f hf ω =
      ψ.val.app (op O) (sectionLift R c M d O f hf ω) := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [sectionLift_D, sectionLift_D]
      rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [sectionLift_smul, sectionLift_smul, (ψ.val.app (op O)).hom.map_smul, hx]

/-- Actual sheaf restriction commutes with the ordinary Kähler lift. -/
theorem sectionLift_restriction (P : Opens X) (hPO : P ≤ O)
    (g : A →+* R.obj.obj (op P))
    (hg : ∀ z : ℂ, g (algebraMap ℂ A z) = coefficientOn R c P z)
    (hfg : ∀ a : A, R.obj.map (homOfLE hPO).op (f a) = g a)
    (ω : KaehlerDifferential ℂ A) :
    M.val.map (homOfLE hPO).op (sectionLift R c M d O f hf ω) =
      sectionLift R c M d P g hg ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [sectionLift_D, sectionLift_D]
      exact (d.d_map (homOfLE hPO).op (f a)).symm.trans (congrArg d.d (hfg a))
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [sectionLift_smul, sectionLift_smul, M.val.map_smul]
      change R.obj.map (homOfLE hPO).op (f a) •
        M.val.map (homOfLE hPO).op (sectionLift R c M d O f hf x) = _
      rw [hfg, hx]

/-- Changing affine coordinates before the lift agrees with composing the
actual ring maps. The equality holds on all Kähler forms. -/
theorem sectionLift_differentialMap {B : Type} [CommRing B] [Algebra ℂ B]
    (g : B →+* R.obj.obj (op O))
    (hg : ∀ z : ℂ, g (algebraMap ℂ B z) = coefficientOn R c O z)
    (φ : A →ₐ[ℂ] B) (hfg : ∀ a : A, g (φ a) = f a)
    (ω : KaehlerDifferential ℂ A) :
    sectionLift R c M d O g hg (differentialMap φ ω) =
      sectionLift R c M d O f hf ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [differentialMap_D, sectionLift_D, sectionLift_D, hfg]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [differentialMap_smul, sectionLift_smul, sectionLift_smul, hfg, hx]

#print axioms sectionLift_D
#print axioms sectionLift_smul
#print axioms sectionLift_unique
#print axioms sectionLift_postcomp
#print axioms sectionLift_restriction
#print axioms sectionLift_differentialMap

end CycleQ2GeometricSheafKaehlerMap
end
