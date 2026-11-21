import Proposal.GeometricSurfaceDifferentialCharts
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricExteriorSheaf

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf

section SemilinearExterior
variable {R S : Type} [CommRing R] [CommRing S]
  {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
  (φ : R →+* S) (f : M →ₛₗ[φ] N) (n : ℕ)

/-- Exterior powers of an actual semilinear restriction map. -/
def exteriorMap : (⋀[R]^n M) →ₛₗ[φ] (⋀[S]^n N) := by
  letI : Algebra R S := φ.toAlgebra
  letI : Module R N := Module.compHom N φ
  letI : Module R (⋀[S]^n N) := Module.compHom (⋀[S]^n N) φ
  letI : IsScalarTower R S N := ⟨fun r s m => mul_smul (φ r) s m⟩
  letI : IsScalarTower R S (⋀[S]^n N) := ⟨fun r s m => mul_smul (φ r) s m⟩
  let l : M →ₗ[R] N :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := f.map_smulₛₗ }
  let w : N [⋀^Fin n]→ₗ[R] (⋀[S]^n N) :=
    { toMultilinearMap := (exteriorPower.ιMulti S n).toMultilinearMap.restrictScalars R
      map_eq_zero_of_eq' := (exteriorPower.ιMulti S n).map_eq_zero_of_eq' }
  let e := exteriorPower.alternatingMapLinearEquiv (w.compLinearMap l)
  exact
    { toFun := e
      map_add' := e.map_add
      map_smul' := e.map_smul }

@[simp] theorem exteriorMap_wedge (m : Fin n → M) :
    exteriorMap φ f n (exteriorPower.ιMulti R n m) =
      exteriorPower.ιMulti S n (fun i => f (m i)) := by
  simp only [exteriorMap,LinearMap.coe_mk,AddHom.coe_mk,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

end SemilinearExterior

section Functoriality
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]
  {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module R M] [Module S N] [Module T P]

theorem exteriorMap_identity (φ : R →+* R) (f : M →ₛₗ[φ] M)
    (hφ : ∀ r, φ r = r) (hf : ∀ m, f m = m) (n : ℕ) (ω : ⋀[R]^n M) :
    exteriorMap φ f n ω = ω := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a,rfl⟩ := hx
      rw [exteriorMap_wedge]
      exact congrArg (exteriorPower.ιMulti R n) (funext fun i => hf (a i))
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add,hx,hy]
  | smul r x _ hx => rw [map_smulₛₗ,hx,hφ]

theorem exteriorMap_composition (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T)
    (f : M →ₛₗ[φ] N) (g : N →ₛₗ[ψ] P) (k : M →ₛₗ[χ] P)
    (hχ : ∀ r, χ r = ψ (φ r)) (hk : ∀ m, k m = g (f m))
    (n : ℕ) (ω : ⋀[R]^n M) :
    exteriorMap χ k n ω = exteriorMap ψ g n (exteriorMap φ f n ω) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a,rfl⟩ := hx
      rw [exteriorMap_wedge,exteriorMap_wedge,exteriorMap_wedge]
      exact congrArg (exteriorPower.ιMulti T n) (funext fun i => hk (a i))
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add,hx,hy]
  | smul r x _ hx => rw [map_smulₛₗ,map_smulₛₗ,map_smulₛₗ,hx,hχ]

end Functoriality

section ExteriorPresheaf
variable {C : Type} [Category C] (R : Cᵒᵖ ⥤ CommRingCat.{0})
  (M : PresheafOfModules.{0} (R ⋙ forget₂ CommRingCat RingCat)) (n : ℕ)

/-- The exterior powers of local sections, with the literal ring and
module restriction maps. Sheafification is performed only after these
maps have been fixed. -/
def exteriorAdditivePresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj U := AddCommGrpCat.of (⋀[R.obj U]^n (M.obj U))
  map h := AddCommGrpCat.ofHom
    (exteriorMap (R.map h).hom (M.restrictₛₗ h) n).toAddMonoidHom
  map_id U := by
    apply ConcreteCategory.hom_ext
    intro ω
    exact exteriorMap_identity (R.map (𝟙 U)).hom (M.restrictₛₗ (𝟙 U))
      (fun r => ConcreteCategory.congr_hom (R.map_id U) r)
      (fun m => ConcreteCategory.congr_hom (M.map_id U) m) n ω
  map_comp {U V W} h k := by
    apply ConcreteCategory.hom_ext
    intro ω
    exact exteriorMap_composition (R.map h).hom (R.map k).hom (R.map (h ≫ k)).hom
      (M.restrictₛₗ h) (M.restrictₛₗ k) (M.restrictₛₗ (h ≫ k))
      (fun r => ConcreteCategory.congr_hom (R.map_comp h k) r)
      (M.map_comp_apply h k) n ω

local instance exteriorObjectModule (U : Cᵒᵖ) :
    Module ((R ⋙ forget₂ CommRingCat RingCat).obj U)
      ((exteriorAdditivePresheaf R M n).obj U) := by
  change Module (R.obj U) (⋀[R.obj U]^n (M.obj U))
  infer_instance

def exteriorPresheaf : PresheafOfModules.{0} (R ⋙ forget₂ CommRingCat RingCat) :=
  PresheafOfModules.ofPresheaf (exteriorAdditivePresheaf R M n)
    (fun {_ _} h r ω => (exteriorMap (R.map h).hom (M.restrictₛₗ h) n).map_smulₛₗ r ω)

end ExteriorPresheaf

section ExteriorSheaf
variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (M : PresheafOfModules.{0} (ringSheaf R).obj) (n : ℕ)

/-- The genuine exterior-power module sheaf, formed from the actual
sectionwise exterior powers and their proved restriction maps. -/
def exteriorSheaf : SheafOfModules.{0} (ringSheaf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).obj
    (exteriorPresheaf R.obj M n)

def toExteriorSheaf : exteriorPresheaf R.obj M n ⟶ (exteriorSheaf R M n).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
    (exteriorPresheaf R.obj M n)

def exteriorSection (U : Opens T) :
    (⋀[R.obj.obj (op U)]^n (M.obj (op U))) →ₗ[R.obj.obj (op U)]
      (exteriorSheaf R M n).val.obj (op U) :=
  ((toExteriorSheaf R M n).app (op U)).hom

theorem exteriorSection_restrict {U V : Opens T} (h : V ⟶ U)
    (ω : ⋀[R.obj.obj (op U)]^n (M.obj (op U))) :
    (exteriorSheaf R M n).val.map h.op (exteriorSection R M n U ω) =
      exteriorSection R M n V
        (exteriorMap (R.obj.map h.op).hom (M.restrictₛₗ h.op) n ω) :=
  (PresheafOfModules.naturality_apply (toExteriorSheaf R M n) h.op ω).symm

/-- A wedge of genuine local sections, as a section of the genuine
exterior-power sheaf. -/
def wedgeSection (U : Opens T) (m : Fin n → M.obj (op U)) :
    (exteriorSheaf R M n).val.obj (op U) :=
  exteriorSection R M n U (exteriorPower.ιMulti (R.obj.obj (op U)) n m)

theorem wedgeSection_restrict {U V : Opens T} (h : V ⟶ U)
    (m : Fin n → M.obj (op U)) :
    (exteriorSheaf R M n).val.map h.op (wedgeSection R M n U m) =
      wedgeSection R M n V (fun i => M.map h.op (m i)) := by
  rw [wedgeSection,exteriorSection_restrict,exteriorMap_wedge]
  rfl

/-- The universal sheafification property retains the actual exterior
presheaf and the canonical unit, so later comparisons cannot select a
different local form by its coordinate alone. -/
def exteriorSheafHomEquiv (N : SheafOfModules.{0} (ringSheaf R)) :
    (exteriorSheaf R M n ⟶ N) ≃ (exteriorPresheaf R.obj M n ⟶ N.val) :=
  PresheafOfModules.sheafificationHomEquiv (𝟙 (ringSheaf R).obj)

end ExteriorSheaf

section ActualResidue
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceExteriorSections
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
variable {X : Scheme.{0}} {U : X.Opens}
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (e : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n t)))
  (h : e.inv ≫ U.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))))

/-- The previously constructed actual local residue, now as a section of
the exterior square of the actual differential module sheaf. -/
def chartResidueSheafSection (V : Over U) :
    (exteriorSheaf X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2).val.obj
      (op V.left) :=
  exteriorSection X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 V.left
    (chartResidueSection f v n t e h V)

theorem chartExteriorSection_wedge_in_sheaf (V : Over U)
    (ω η : KaehlerDifferential ℂ (AdjunctionPatch v n t)) :
    exteriorSection X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 V.left
      (chartExteriorSection e f h (localSurfaceKaehlerBasis v n t) V
        (exteriorPower.ιMulti (AdjunctionPatch v n t) 2 ![ω,η])) =
      wedgeSection X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 V.left
        ![chartKaehlerSection e f h V ω,chartKaehlerSection e f h V η] := by
  rw [chartExteriorSection_wedge]
  rfl

end ActualResidue

#print axioms exteriorMap_wedge
#print axioms exteriorAdditivePresheaf
#print axioms exteriorPresheaf
#print axioms exteriorSection_restrict
#print axioms wedgeSection_restrict
#print axioms exteriorSheafHomEquiv
#print axioms chartResidueSheafSection
#print axioms chartExteriorSection_wedge_in_sheaf

end CycleQ2GeometricExteriorSheaf
end
