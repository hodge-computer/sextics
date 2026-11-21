import Proposal.GeometricMonicGenericSupport

/-! Exterior powers of finite projective modules commute with scalar extension. On smooth affine schemes this gives normalized localization of relative forms on principal opens, including their restriction maps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

noncomputable section

namespace CycleQ2ProjectiveExteriorBaseChange
open Module TensorProduct
open scoped TensorProduct
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)
open CycleQ2ProductExteriorComponents (extEquiv)
variable {R S M N P : Type} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- Under a scalar extension, the ordinary R-linear map can be viewed as
semilinear for the algebra map. -/
def semi {L : Type} [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
    (f : M →ₗ[R] L) : M →ₛₗ[algebraMap R S] L where
  __ := f.toAddHom
  map_smul' c x := (f.map_smul c x).trans (IsScalarTower.algebraMap_smul S c (f x)).symm

/-- The alternating-power map before tensoring the source. -/
def raw (n : ℕ) {L : Type} [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
    (f : M →ₗ[R] L) : (⋀[R]^n M) →ₗ[R] (⋀[S]^n L) where
  __ := (exteriorMap (algebraMap R S) (semi (S := S) f) n).toAddMonoidHom
  map_smul' c x := ((exteriorMap (algebraMap R S) (semi (S := S) f) n).map_smulₛₗ c x).trans
    (IsScalarTower.algebraMap_smul S c _)

theorem raw_wedge (n : ℕ) {L : Type} [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
    (f : M →ₗ[R] L) (v : Fin n → M) :
    raw (S := S) n f (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti S n (f ∘ v) :=
  exteriorMap_wedge (algebraMap R S) (semi (S := S) f) n v

def canonical (n : ℕ) : S ⊗[R] (⋀[R]^n M) →ₗ[S] (⋀[S]^n (S ⊗[R] M)) :=
  (TensorProduct.isBaseChange R (⋀[R]^n M) S).lift (raw (S := S) n (TensorProduct.mk R S M 1))

theorem canonical_wedge (n : ℕ) (v : Fin n → M) :
    canonical (S := S) n (1 ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i => 1 ⊗ₜ[R] v i) := by
  change (TensorProduct.isBaseChange R _ S).lift _ (TensorProduct.mk R S _ 1 _) = _
  rw [IsBaseChange.lift_eq,raw_wedge]
  rfl

private theorem tensor_wedge_ext (n : ℕ) {L : Type} [AddCommGroup L] [Module S L]
    [Module R L] [IsScalarTower R S L] (f g : S ⊗[R] (⋀[R]^n M) →ₗ[S] L)
    (h : ∀ v : Fin n → M, f (1 ⊗ₜ[R] exteriorPower.ιMulti R n v) = g (1 ⊗ₜ[R] exteriorPower.ιMulti R n v)) :
    f = g := by
  apply (TensorProduct.isBaseChange R (⋀[R]^n M) S).algHom_ext'
  apply exteriorPower.linearMap_ext
  exact AlternatingMap.ext h

private abbrev sourceMap (n : ℕ) (f : M →ₗ[R] N) := (exteriorPower.map n f).baseChange S
private abbrev targetMap (n : ℕ) (f : M →ₗ[R] N) := exteriorPower.map n (f.baseChange S)

theorem canonical_natural (n : ℕ) (f : M →ₗ[R] N) (x : S ⊗[R] (⋀[R]^n M)) :
    canonical n (sourceMap (S := S) n f x) = targetMap (S := S) n f (canonical n x) := by
  have h : (canonical n).comp (sourceMap (S := S) n f) =
      (targetMap (S := S) n f).comp (canonical n) := by
    apply tensor_wedge_ext
    intro v
    simp only [LinearMap.comp_apply,sourceMap,targetMap,LinearMap.baseChange_tmul,
      exteriorPower.map_apply_ιMulti,canonical_wedge]
    rfl
  exact LinearMap.congr_fun h x

private theorem free_bijective (n : ℕ) {m : ℕ} (b : Basis (Fin m) R M) :
    Function.Bijective (canonical (R := R) (M := M) (S := S) n) := by
  have h : canonical (R := R) (S := S) n = (CycleQ2ExteriorBaseChange.comparison (S := S) b n).toLinearMap :=
    tensor_wedge_ext n _ _ (fun v => (canonical_wedge n v).trans (CycleQ2ExteriorBaseChange.comparison_wedge b n v).symm)
  rw [h]
  exact LinearEquiv.bijective _

theorem bijective (n : ℕ) [Module.Finite R M] [Module.Projective R M] :
    Function.Bijective (canonical (R := R) (M := M) (S := S) n) := by
  obtain ⟨m,p,hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨i,hi⟩ := Module.projective_lifting_property p (LinearMap.id (R := R) (M := M)) hp
  have hF := free_bijective (S := S) n (Pi.basisFun R (Fin m))
  have hD : (sourceMap (S := S) n p).comp (sourceMap n i) = LinearMap.id := by
    rw [sourceMap,sourceMap,← LinearMap.baseChange_comp,← exteriorPower.map_comp,hi,exteriorPower.map_id,LinearMap.baseChange_id]
  have hE : (targetMap (S := S) n p).comp (targetMap n i) = LinearMap.id := by
    rw [targetMap,targetMap,← exteriorPower.map_comp,← LinearMap.baseChange_comp,hi,LinearMap.baseChange_id,exteriorPower.map_id]
  constructor
  · intro x y h
    have hx : sourceMap (S := S) n i x = sourceMap n i y := hF.injective
      ((canonical_natural n i x).trans ((congrArg (targetMap n i) h).trans (canonical_natural n i y).symm))
    exact (LinearMap.congr_fun hD x).symm.trans ((congrArg (sourceMap n p) hx).trans (LinearMap.congr_fun hD y))
  · intro y
    obtain ⟨x,hx⟩ := hF.surjective (targetMap n i y)
    exact ⟨sourceMap n p x,(canonical_natural n p x).trans
      ((congrArg (targetMap n p) hx).trans (LinearMap.congr_fun hE y))⟩

theorem isBaseChange (n : ℕ) [Module.Finite R M] [Module.Projective R M]
    {L : Type} [AddCommGroup L] [Module R L] [Module S L] [IsScalarTower R S L]
    {f : M →ₗ[R] L} (h : IsBaseChange S f) : IsBaseChange S (raw (S := S) n f) := by
  let e := (LinearEquiv.ofBijective (canonical (R := R) (M := M) (S := S) n) (bijective n)).trans
    (extEquiv n h.equiv)
  apply IsBaseChange.of_equiv e
  intro w
  have m : ((e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R S _ 1)) = raw (S := S) n f := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change (extEquiv n h.equiv) (canonical n (1 ⊗ₜ[R] exteriorPower.ιMulti R n v)) = _
    rw [canonical_wedge]
    change exteriorPower.map n h.equiv.toLinearMap _ = raw (S := S) n f (exteriorPower.ιMulti R n v)
    rw [exteriorPower.map_apply_ιMulti,raw_wedge]
    apply congrArg (exteriorPower.ιMulti S n)
    funext a
    exact (h.equiv_tmul 1 (v a)).trans (one_smul _ _)
  exact LinearMap.congr_fun m w

theorem projective (n : ℕ) [Module.Finite R M] [Module.Projective R M] :
    Module.Projective R (⋀[R]^n M) := by
  obtain ⟨m,p,hp⟩ := Module.Finite.exists_fin' R M
  obtain ⟨i,hi⟩ := Module.projective_lifting_property p (LinearMap.id (R := R) (M := M)) hp
  let := Module.Free.of_basis ((Pi.basisFun R (Fin m)).exteriorPower n)
  apply Module.Projective.of_split (exteriorPower.map n i) (exteriorPower.map n p)
  rw [← exteriorPower.map_comp,hi,exteriorPower.map_id]

end CycleQ2ProjectiveExteriorBaseChange

namespace CycleQ2ExteriorPrincipal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GenericAffineKahlerLocalization (X p basic B fromAffine fromAffineAdd_restrict)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2ProjectiveExteriorBaseChange (raw raw_wedge)
open scoped KaehlerDifferential
attribute [local instance] CycleQ2GenericAffineKahlerLocalization.sectionsAlgebra
  CycleQ2GenericAffineKahlerLocalization.coefficientsAlgebra
variable (k A : Type) [Field k] [CommRing A] [Algebra k A] (n : ℕ)

abbrev M := ModuleCat.of A (Form k A n)
abbrev sheaf : (X A).Modules := tilde (M k A n)
abbrev localTilde (U : (X A).Opens) := (modulesSpecToSheaf.obj (sheaf k A n)).presheaf.obj (op U)
abbrev localForms (U : (X A).Opens) := Form k (B A U) n

def fromRing (U : (X A).Opens) : Form k A n →ₗ[A] localForms k A n U :=
  raw (S := B A U) n (fromAffine k A U)

private def res {U V : (X A).Opens} (h : V ≤ U) : localForms k A n U →ₗ[A] localForms k A n V where
  __ := (exteriorPullback (restrict (p k A) h) n).toAddMonoidHom
  map_smul' c w := by
    change exteriorPullback (restrict (p k A) h) n (c • w) = c • _
    rw [← IsScalarTower.algebraMap_smul (B A U) c w, map_smulₛₗ]
    have hs : restrict (p k A) h (algebraMap A (B A U) c) = algebraMap A (B A V) c :=
      ConcreteCategory.congr_hom (StructureSheaf.algebraMap_self_map A (op V) (op U) (homOfLE h).op) c
    change restrict (p k A) h (algebraMap A (B A U) c) • _ = _
    exact (congrArg (fun z : B A V => z • exteriorPullback (restrict (p k A) h) n w) hs).trans
      (IsScalarTower.algebraMap_smul (B A V) c _)

private theorem res_fromRing {U V : (X A).Opens} (h : V ≤ U) (w : Form k A n) :
    res k A n h (fromRing k A n U w) = fromRing k A n V w := by
  have e : (res k A n h).comp (fromRing k A n U) = fromRing k A n V := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change exteriorPullback (restrict (p k A) h) n (raw (S := B A U) n _ (exteriorPower.ιMulti A n v)) =
      raw (S := B A V) n _ (exteriorPower.ιMulti A n v)
    rw [raw_wedge,raw_wedge,exteriorPullback,exteriorMap_wedge]
    apply congrArg (exteriorPower.ιMulti (B A V) n)
    funext i
    exact fromAffineAdd_restrict k A h (v i)
  exact LinearMap.congr_fun e w

private instance tildeLocalized (a : A) :
    IsLocalizedModule.Away a (tilde.toOpen (R := CommRingCat.of A) (M k A n) (basic A a)).hom :=
  IsLocalizedModule.of_linearEquiv (Submonoid.powers a)
    (StructureSheaf.toOpenₗ A (M k A n) (PrimeSpectrum.basicOpen a))
    ((tilde.modulesSpecToSheafIso (R := CommRingCat.of A) (M k A n)).app _).toLinearEquiv.symm

variable [Algebra.Smooth k A]

private instance formsLocalized (a : A) : IsLocalizedModule.Away a (fromRing k A n (basic A a)) := by
  let : IsLocalization.Away a (B A (basic A a)) := StructureSheaf.IsLocalization.to_basicOpen A a
  have h : IsLocalizedModule.Away a (fromAffine k A (basic A a)) := by
    change IsLocalizedModule.Away a (KaehlerDifferential.map k k A (B A (basic A a)))
    infer_instance
  apply (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) (B A (basic A a)) _).mpr
  exact CycleQ2ProjectiveExteriorBaseChange.isBaseChange n
    (IsLocalizedModule.isBaseChange (Submonoid.powers a) (B A (basic A a)) (fromAffine k A (basic A a)))

def localIso (a : A) : localForms k A n (basic A a) ≃ₗ[A] localTilde k A n (basic A a) :=
  IsLocalizedModule.linearEquiv (Submonoid.powers a) (fromRing k A n (basic A a))
    (tilde.toOpen (R := CommRingCat.of A) (M k A n) (basic A a)).hom

theorem localIso_fromRing (a : A) (w : Form k A n) :
    localIso k A n a (fromRing k A n (basic A a) w) = tilde.toOpen (R := CommRingCat.of A) (M k A n) (basic A a) w :=
  IsLocalizedModule.linearEquiv_apply _ _ _ _

private def tildeRes {U V : (X A).Opens} (h : V ≤ U) : localTilde k A n U →ₗ[A] localTilde k A n V :=
  ((modulesSpecToSheaf.obj (sheaf k A n)).presheaf.map (homOfLE h).op).hom

def localAddIso (a : A) : localForms k A n (basic A a) ≃+
    (addSheaf (sheaf k A n)).obj.obj (op (basic A a)) := (localIso k A n a).toAddEquiv

theorem localAddIso_natural {a b : A} (h : basic A b ≤ basic A a) (w : localForms k A n (basic A a)) :
    localAddIso k A n b (exteriorPullback (restrict (p k A) h) n w) =
      (addSheaf (sheaf k A n)).obj.map (homOfLE h).op (localAddIso k A n a w) := by
  let l := (localIso k A n b).toLinearMap.comp (res k A n h)
  let r := (tildeRes k A n h).comp (localIso k A n a).toLinearMap
  have e : l = r := by
    apply IsLocalizedModule.ext (Submonoid.powers a) (fromRing k A n (basic A a))
    · intro m
      obtain ⟨t,ht⟩ := m.property
      rw [← ht,map_pow]
      exact ((sheaf k A n).isUnit_algebraMap_end_of_le_basicOpen a h).pow t
    · apply LinearMap.ext
      intro z
      change localIso k A n b (res k A n h (fromRing k A n (basic A a) z)) =
        tildeRes k A n h (localIso k A n a (fromRing k A n (basic A a) z))
      rw [res_fromRing,localIso_fromRing,localIso_fromRing]
      exact (ConcreteCategory.congr_hom
        (tilde.toOpen_res (R := CommRingCat.of A) (M k A n) (basic A a) (basic A b) (homOfLE h)) z).symm
  exact LinearMap.congr_fun e w

end CycleQ2ExteriorPrincipal

end

#print axioms CycleQ2ProjectiveExteriorBaseChange.isBaseChange
#print axioms CycleQ2ExteriorPrincipal.localAddIso_natural
