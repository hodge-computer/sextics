import Proposal.GeometricDifferentialSheaf
import Proposal.GeometricSheafHZero
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-!
# Complex scalars on actual additive-sheaf cohomology

A global complex coefficient homomorphism acts on an actual sheaf of
structure-ring modules by sectionwise scalar multiplication. Applying the
existing derived cohomology functor gives a complex module structure on
its actual `H'` groups, in every degree and on every open.

The action is induced by those sheaf endomorphisms, rather than chosen
through an abstract coordinate on cohomology. Module-sheaf morphisms and
isomorphisms induce complex-linear maps and equivalences. The actual
degree-zero section comparison and Mayer-Vietoris connecting map commute
with these scalars.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricConeCech.HZero

noncomputable section
namespace CycleQ2GeometricSheafCohomologyScalar

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤))
  (M : SheafOfModules.{0} (ringSheaf R))
local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

local instance (O : (Opens X)ᵒᵖ) : Module (R.obj.obj O) (M.val.presheaf.obj O) :=
  (M.val.obj O).isModule

abbrev additiveSheaf := (SheafOfModules.toSheaf (ringSheaf R)).obj M

local instance (O : (Opens X)ᵒᵖ) :
    Module (R.obj.obj O) ((additiveSheaf R M).obj.obj O) :=
  (M.val.obj O).isModule

def scalarEnd (z : ℂ) :
    additiveSheaf R M ⟶ additiveSheaf R M where
  hom :=
    { app O := AddCommGrpCat.ofHom
        { toFun x := (coefficientOn R c O.unop z) • x
          map_zero' := smul_zero _
          map_add' := smul_add _ }
      naturality {O P} f := by
        ext x
        change (coefficientOn R c P.unop z) • M.val.presheaf.map f x =
          M.val.presheaf.map f ((coefficientOn R c O.unop z) • x)
        have hm := M.val.map_smul f (coefficientOn R c O.unop z) x
        have hc := congrArg (fun k : CommRingCat.of ℂ ⟶ R.obj.obj P => k z)
          ((coefficientMap R c).naturality f)
        exact (hm.trans (congrArg (fun a : R.obj.obj P => a • M.val.presheaf.map f x)
          hc.symm)).symm }

theorem scalarEnd_one : scalarEnd R c M 1 = 𝟙 _ := by
  ext O x
  change coefficientOn R c O.unop 1 • x = x
  rw [map_one, one_smul]

theorem scalarEnd_mul (a b : ℂ) :
    scalarEnd R c M (a * b) = scalarEnd R c M b ≫ scalarEnd R c M a := by
  ext O x
  change coefficientOn R c O.unop (a * b) • x =
    coefficientOn R c O.unop a • (coefficientOn R c O.unop b • x)
  rw [map_mul, mul_smul]

theorem scalarEnd_add (a b : ℂ) :
    scalarEnd R c M (a + b) = scalarEnd R c M a + scalarEnd R c M b := by
  ext O x
  change coefficientOn R c O.unop (a + b) • x =
    coefficientOn R c O.unop a • x + coefficientOn R c O.unop b • x
  rw [map_add, add_smul]

theorem scalarEnd_zero : scalarEnd R c M 0 = 0 := by
  ext O x
  change coefficientOn R c O.unop 0 • x = 0
  rw [map_zero, zero_smul]

def cohomologyScalar (n : ℕ) (O : Opens X) (z : ℂ) :
    (additiveSheaf R M).H' n O →+ (additiveSheaf R M).H' n O :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
    (scalarEnd R c M z)).app (op O)).hom

theorem cohomologyScalar_one (n : ℕ) (O : Opens X)
    (x : (additiveSheaf R M).H' n O) : cohomologyScalar R c M n O 1 x = x := by
  change x.comp (Ext.mk₀ (scalarEnd R c M 1)) (add_zero n) = x
  rw [scalarEnd_one]
  exact Ext.comp_mk₀_id x

theorem cohomologyScalar_mul (n : ℕ) (O : Opens X) (a b : ℂ)
    (x : (additiveSheaf R M).H' n O) :
    cohomologyScalar R c M n O (a * b) x =
      cohomologyScalar R c M n O a (cohomologyScalar R c M n O b x) := by
  change x.comp (Ext.mk₀ (scalarEnd R c M (a * b))) (add_zero n) =
    (x.comp (Ext.mk₀ (scalarEnd R c M b)) (add_zero n)).comp
      (Ext.mk₀ (scalarEnd R c M a)) (add_zero n)
  rw [scalarEnd_mul, ← Ext.mk₀_comp_mk₀]
  symm
  exact Ext.comp_assoc _ _ _ (add_zero n) rfl (by omega)

theorem cohomologyScalar_add (n : ℕ) (O : Opens X) (a b : ℂ)
    (x : (additiveSheaf R M).H' n O) :
    cohomologyScalar R c M n O (a + b) x =
      cohomologyScalar R c M n O a x + cohomologyScalar R c M n O b x := by
  change x.comp (Ext.mk₀ (scalarEnd R c M (a + b))) (add_zero n) =
    x.comp (Ext.mk₀ (scalarEnd R c M a)) (add_zero n) +
      x.comp (Ext.mk₀ (scalarEnd R c M b)) (add_zero n)
  rw [scalarEnd_add, Ext.mk₀_add, Ext.comp_add]

@[instance_reducible] def cohomologyModule (n : ℕ) (O : Opens X) :
    Module ℂ ((additiveSheaf R M).H' n O) := by
  letI : SMul ℂ ((additiveSheaf R M).H' n O) :=
    ⟨fun z x => cohomologyScalar R c M n O z x⟩
  exact
    { smul_add := fun z x y => (cohomologyScalar R c M n O z).map_add x y
      smul_zero := fun z => (cohomologyScalar R c M n O z).map_zero
      add_smul := cohomologyScalar_add R c M n O
      zero_smul := fun x => by
        change x.comp (Ext.mk₀ (scalarEnd R c M 0)) (add_zero n) = 0
        rw [scalarEnd_zero, Ext.mk₀_zero, Ext.comp_zero]
      mul_smul := cohomologyScalar_mul R c M n O
      one_smul := cohomologyScalar_one R c M n O }

theorem scalarEnd_naturality {N : SheafOfModules.{0} (ringSheaf R)}
    (f : M ⟶ N) (z : ℂ) :
    scalarEnd R c M z ≫ (SheafOfModules.toSheaf (ringSheaf R)).map f =
      (SheafOfModules.toSheaf (ringSheaf R)).map f ≫ scalarEnd R c N z := by
  ext O x
  exact (f.val.app O).hom.map_smul (coefficientOn R c O.unop z) x

theorem cohomologyMap_scalar {N : SheafOfModules.{0} (ringSheaf R)}
    (f : M ⟶ N) (n : ℕ) (O : Opens X) (z : ℂ)
    (x : (additiveSheaf R M).H' n O) :
    ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
        ((SheafOfModules.toSheaf (ringSheaf R)).map f)).app (op O)
        (cohomologyScalar R c M n O z x) =
      cohomologyScalar R c N n O z
        (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map
          ((SheafOfModules.toSheaf (ringSheaf R)).map f)).app (op O) x) := by
  let g := (SheafOfModules.toSheaf (ringSheaf R)).map f
  change (x.comp (Ext.mk₀ (scalarEnd R c M z)) (add_zero n)).comp
      (Ext.mk₀ g) (add_zero n) =
    (x.comp (Ext.mk₀ g) (add_zero n)).comp
      (Ext.mk₀ (scalarEnd R c N z)) (add_zero n)
  rw [Ext.comp_assoc _ _ _ (add_zero n) rfl (by omega),
    Ext.comp_assoc _ _ _ (add_zero n) rfl (by omega),
    Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, scalarEnd_naturality]

def cohomologyMapLinear {N : SheafOfModules.{0} (ringSheaf R)}
    (f : M ⟶ N) (n : ℕ) (O : Opens X) :
    letI := cohomologyModule R c M n O
    letI := cohomologyModule R c N n O
    (additiveSheaf R M).H' n O →ₗ[ℂ] (additiveSheaf R N).H' n O := by
  letI := cohomologyModule R c M n O
  letI := cohomologyModule R c N n O
  exact
    { (((Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) n).map
          ((SheafOfModules.toSheaf (ringSheaf R)).map f)).app (op O)).hom with
      map_smul' := cohomologyMap_scalar R c M f n O }

def cohomologyIsoAdd {N : SheafOfModules.{0} (ringSheaf R)}
    (e : M ≅ N) (n : ℕ) (O : Opens X) :
    (additiveSheaf R M).H' n O ≃+ (additiveSheaf R N).H' n O :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).mapIso
    ((SheafOfModules.toSheaf (ringSheaf R)).mapIso e)).app
      (op O)).addCommGroupIsoToAddEquiv

def cohomologyIsoLinear {N : SheafOfModules.{0} (ringSheaf R)}
    (e : M ≅ N) (n : ℕ) (O : Opens X) :
    letI := cohomologyModule R c M n O
    letI := cohomologyModule R c N n O
    (additiveSheaf R M).H' n O ≃ₗ[ℂ] (additiveSheaf R N).H' n O := by
  letI := cohomologyModule R c M n O
  letI := cohomologyModule R c N n O
  exact
    { toAddEquiv := cohomologyIsoAdd R M e n O
      map_smul' := cohomologyMap_scalar R c M e.hom n O }

theorem sectionsEquiv_map {F G : X.Sheaf AddCommGrpCat.{0}}
    (f : F ⟶ G) (O : Opens X) (x : F.H' 0 O) :
    sectionsEquiv G O
        (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) 0).map f).app
          (op O) x) =
      f.hom.app (op O) (sectionsEquiv F O x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  change sectionsEquiv G O ((Ext.mk₀ a).comp (Ext.mk₀ f) (add_zero 0)) = _
  rw [Ext.mk₀_comp_mk₀, sectionsEquiv_mk₀, sectionsEquiv_mk₀,
    (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv_naturality_right]
  rfl

theorem sectionsEquiv_scalar (O : Opens X) (z : ℂ)
    (x : (additiveSheaf R M).H' 0 O) :
    sectionsEquiv (additiveSheaf R M) O (cohomologyScalar R c M 0 O z x) =
      coefficientOn R c O z • sectionsEquiv (additiveSheaf R M) O x :=
  sectionsEquiv_map (scalarEnd R c M z) O x

theorem sectionsEquiv_symm_scalar (O : Opens X) (z : ℂ)
    (x : (additiveSheaf R M).obj.obj (op O)) :
    (sectionsEquiv (additiveSheaf R M) O).symm (coefficientOn R c O z • x) =
      cohomologyScalar R c M 0 O z ((sectionsEquiv (additiveSheaf R M) O).symm x) := by
  apply (sectionsEquiv (additiveSheaf R M) O).injective
  rw [AddEquiv.apply_symm_apply, sectionsEquiv_scalar, AddEquiv.apply_symm_apply]

theorem mayerVietoris_scalar
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (z : ℂ)
    (x : (additiveSheaf R M).H' n₀ S.X₁) :
    S.δ (additiveSheaf R M) n₀ n₁ h
        (cohomologyScalar R c M n₀ S.X₁ z x) =
      cohomologyScalar R c M n₁ S.X₄ z
        (S.δ (additiveSheaf R M) n₀ n₁ h x) := by
  change S.shortComplex_shortExact.extClass.comp
      (x.comp (Ext.mk₀ (scalarEnd R c M z)) (add_zero n₀)) (by omega) =
    (S.shortComplex_shortExact.extClass.comp x (by omega)).comp
      (Ext.mk₀ (scalarEnd R c M z)) (add_zero n₁)
  symm
  exact Ext.comp_assoc _ _ _ (by omega) (add_zero n₀) (by omega)

#print axioms cohomologyModule
#print axioms cohomologyMapLinear
#print axioms cohomologyIsoLinear
#print axioms sectionsEquiv_scalar
#print axioms mayerVietoris_scalar


end CycleQ2GeometricSheafCohomologyScalar
end

