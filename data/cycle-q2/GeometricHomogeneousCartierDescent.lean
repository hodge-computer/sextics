import Proposal.GeometricCartierCoordinateDescent
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Proposal.GeometricCartierCechNonboundary

section SourceCartierSecondNaturality

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V W : Finset (Fin 4) → Finset (Fin 4) → Type*}
variable [∀ s t, AddCommGroup (V s t)] [∀ s t, Module R (V s t)]
variable [∀ s t, AddCommGroup (W s t)] [∀ s t, Module R (W s t)]

/-- A morphism of actual common-refinement diagrams preserves both
restriction directions. -/
structure BiSystemMorphism (D : BiSystem (R := R) V) (E : BiSystem (R := R) W) where
  app (s t : Finset (Fin 4)) : V s t →ₗ[R] W s t
  naturality_left {s s' t : Finset (Fin 4)} (hs : s ⊆ s') (x : V s t) :
    app s' t ((D.left t).res hs x) = (E.left t).res hs (app s t x)
  naturality_right {s t t' : Finset (Fin 4)} (ht : t ⊆ t') (x : V s t) :
    app s t' ((D.right s).res ht x) = (E.right s).res ht (app s t x)

namespace BiSystemMorphism

variable {D : BiSystem (R := R) V} {E : BiSystem (R := R) W}

def left (f : BiSystemMorphism D E) (t : Finset (Fin 4)) :
    SystemMorphism (D.left t) (E.left t) where
  app s := f.app s t
  naturality hs := LinearMap.ext (f.naturality_left hs)

def right (f : BiSystemMorphism D E) (s : Finset (Fin 4)) :
    SystemMorphism (D.right s) (E.right s) where
  app t := f.app s t
  naturality ht := LinearMap.ext (f.naturality_right ht)

def row0 (f : BiSystemMorphism D E) : SystemMorphism D.row0 E.row0 where
  app s := (f.right s).map0
  naturality hs := by
    apply LinearMap.ext
    intro x
    exact Prod.ext (Prod.ext (f.naturality_left hs x.1.1)
      (f.naturality_left hs x.1.2))
      (Prod.ext (f.naturality_left hs x.2.1) (f.naturality_left hs x.2.2))

def row1 (f : BiSystemMorphism D E) : SystemMorphism D.row1 E.row1 where
  app s := (f.right s).map1
  naturality hs := by
    apply LinearMap.ext
    intro x
    exact Prod.ext (Prod.ext (f.naturality_left hs x.1.1)
      (Prod.ext (f.naturality_left hs x.1.2.1) (f.naturality_left hs x.1.2.2)))
      (Prod.ext (f.naturality_left hs x.2.1)
        (Prod.ext (f.naturality_left hs x.2.2.1) (f.naturality_left hs x.2.2.2)))

def row2 (f : BiSystemMorphism D E) : SystemMorphism D.row2 E.row2 where
  app s := (f.right s).map2
  naturality hs := by
    apply LinearMap.ext
    intro x
    exact Prod.ext (Prod.ext (f.naturality_left hs x.1.1)
      (f.naturality_left hs x.1.2))
      (Prod.ext (f.naturality_left hs x.2.1) (f.naturality_left hs x.2.2))

theorem row0_horizontalAugmentation (f : BiSystemMorphism D E)
    (c : TwoCochain (fun s => V s ∅)) :
    f.row0.map2 (D.horizontalAugmentation.map2 c) =
      E.horizontalAugmentation.map2 ((f.left ∅).map2 c) := by
  exact Prod.ext (Prod.ext ((f.right {0,1,2}).map0_augmentation c.1.1)
    ((f.right {0,1,3}).map0_augmentation c.1.2))
    (Prod.ext ((f.right {0,2,3}).map0_augmentation c.2.1)
      ((f.right {1,2,3}).map0_augmentation c.2.2))

theorem row1_vertical0 (f : BiSystemMorphism D E)
    (x : OneCochain (fun s => ZeroCochain (V s))) :
    f.row1.map1 (D.vertical0.map1 x) = E.vertical0.map1 (f.row0.map1 x) := by
  exact Prod.ext (Prod.ext ((f.right {0,1}).map1_d0 x.1.1)
    (Prod.ext ((f.right {0,2}).map1_d0 x.1.2.1) ((f.right {0,3}).map1_d0 x.1.2.2)))
    (Prod.ext ((f.right {1,2}).map1_d0 x.2.1)
      (Prod.ext ((f.right {1,3}).map1_d0 x.2.2.1) ((f.right {2,3}).map1_d0 x.2.2.2)))

theorem row2_vertical1 (f : BiSystemMorphism D E)
    (y : ZeroCochain (fun s => OneCochain (V s))) :
    f.row2.map0 (D.vertical1.map0 y) = E.vertical1.map0 (f.row1.map0 y) := by
  exact Prod.ext (Prod.ext ((f.right {0}).map2_d1 y.1.1)
    ((f.right {1}).map2_d1 y.1.2))
    (Prod.ext ((f.right {2}).map2_d1 y.2.1) ((f.right {3}).map2_d1 y.2.2))

/-- Transport preserves the precise staircase witnesses, so forgetting
homogeneous degree or changing canonical localizations retains the same
original cocycle and its descendant. -/
theorem mapSecondDescent (f : BiSystemMorphism D E)
    {c : TwoCochain (fun s => V s ∅)} {d : TwoCochain (V ∅)}
    (hcd : D.SecondDescent c d) :
    E.SecondDescent ((f.left ∅).map2 c) ((f.right ∅).map2 d) := by
  obtain ⟨x,y,hx,hy,hd⟩ := hcd
  refine ⟨f.row0.map1 x,f.row1.map0 y,?_,?_,?_⟩
  · rw [← f.row0.map2_d1, hx, f.row0_horizontalAugmentation]
  · rw [← f.row1.map1_d0, hy, f.row1_vertical0]
  · change augmentation E.row2 (f.row2.app ∅ d) = _
    rw [← f.row2.map0_augmentation, hd, f.row2_vertical1]

end BiSystemMorphism

namespace BiSystem

variable (D : BiSystem (R := R) V)

/-- The second-cover representative is also a boundary when the original
one is. This is the reverse chase through the same actual staircase. -/
theorem SecondDescent.preserves_boundary
    (hleft1 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (d0 (D.left t)) (d1 (D.left t)))
    (hleft0 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (augmentation (D.left t)) (d0 (D.left t)))
    (hleftinj : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Injective (augmentation (D.left t)))
    {c : TwoCochain (fun s => V s ∅)} {d : TwoCochain (V ∅)}
    (hcd : D.SecondDescent c d)
    (hc : ∃ a, d1 (D.left ∅) a = c) : ∃ b, d1 (D.right ∅) b = d := by
  obtain ⟨x,y,hx,hy,hd⟩ := hcd
  obtain ⟨a,ha⟩ := hc
  have hxa : d1 D.row0 (x - D.horizontalAugmentation.map1 a) = 0 := by
    rw [map_sub, ← D.horizontalAugmentation.map2_d1, ha, hx, sub_self]
  obtain ⟨z,hz⟩ := (D.row0_first_exact hleft1 _).mp hxa
  have hyz : d0 D.row1 (y - D.vertical0.map0 z) = 0 := by
    rw [(d0 D.row1).map_sub, ← D.vertical0.map1_d0, hz,
      D.vertical0.map1.map_sub, hy]
    have hv : D.vertical0.map1 (D.horizontalAugmentation.map1 a) = 0 := by
      exact Prod.ext (Prod.ext (d0_augmentation (D.right {0,1}) a.1.1)
        (Prod.ext (d0_augmentation (D.right {0,2}) a.1.2.1)
          (d0_augmentation (D.right {0,3}) a.1.2.2)))
        (Prod.ext (d0_augmentation (D.right {1,2}) a.2.1)
          (Prod.ext (d0_augmentation (D.right {1,3}) a.2.2.1)
            (d0_augmentation (D.right {2,3}) a.2.2.2)))
    rw [hv, sub_zero, sub_self]
  obtain ⟨b,hb⟩ := (D.row1_zero_exact hleft0 _).mp hyz
  refine ⟨b,D.row2_augmentation_injective hleftinj ?_⟩
  change augmentation D.row2 (D.vertical1.app ∅ b) = augmentation D.row2 d
  rw [← D.vertical1.map0_augmentation, hb, D.vertical1.map0.map_sub, ← hd]
  have hvv : D.vertical1.map0 (D.vertical0.map0 z) = 0 := by
    exact Prod.ext (Prod.ext (d1_d0 (D.right {0}) z.1.1)
      (d1_d0 (D.right {1}) z.1.2))
      (Prod.ext (d1_d0 (D.right {2}) z.2.1) (d1_d0 (D.right {3}) z.2.2))
  rw [hvv, sub_zero]

theorem SecondDescent.sub
    {c c' : TwoCochain (fun s => V s ∅)} {d d' : TwoCochain (V ∅)}
    (h : D.SecondDescent c d) (h' : D.SecondDescent c' d') :
    D.SecondDescent (c - c') (d - d') := by
  obtain ⟨x,y,hx,hy,hd⟩ := h
  obtain ⟨x',y',hx',hy',hd'⟩ := h'
  refine ⟨x-x',y-y',?_,?_,?_⟩
  · rw [(d1 D.row0).map_sub,D.horizontalAugmentation.map2.map_sub,hx,hx']
  · rw [(d0 D.row1).map_sub,D.vertical0.map1.map_sub,hy,hy']
  · rw [(augmentation D.row2).map_sub,D.vertical1.map0.map_sub,hd,hd']

/-- Different choices of refinement primitives produce the same
cohomology class, expressed by an actual boundary between representatives. -/
theorem SecondDescent.unique_mod_boundary
    (hleft1 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (d0 (D.left t)) (d1 (D.left t)))
    (hleft0 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (augmentation (D.left t)) (d0 (D.left t)))
    (hleftinj : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Injective (augmentation (D.left t)))
    {c : TwoCochain (fun s => V s ∅)} {d d' : TwoCochain (V ∅)}
    (h : D.SecondDescent c d) (h' : D.SecondDescent c d') :
    ∃ b, d1 (D.right ∅) b = d - d' := by
  apply SecondDescent.preserves_boundary D hleft1 hleft0 hleftinj
    (SecondDescent.sub D h h')
  exact ⟨0,by simp⟩

end BiSystem

section RestrictScalars

variable (S : Type*) [CommRing S] [Algebra S R]
variable [∀ s t, Module S (V s t)] [∀ s t, IsScalarTower S R (V s t)]

def BiSystem.restrictScalars (D : BiSystem (R := R) V) : BiSystem (R := S) V where
  left t := (D.left t).restrictScalars S
  right s := (D.right s).restrictScalars S
  interchange hs ht x := D.interchange hs ht x

@[simp] theorem BiSystem.secondDescent_restrictScalars (D : BiSystem (R := R) V)
    (c : TwoCochain (fun s => V s ∅)) (d : TwoCochain (V ∅)) :
    (D.restrictScalars S).SecondDescent c d ↔ D.SecondDescent c d := Iff.rfl

end RestrictScalars

end CycleQ2GeometricFourOpenCech

#print axioms CycleQ2GeometricFourOpenCech.BiSystemMorphism.mapSecondDescent
#print axioms CycleQ2GeometricFourOpenCech.BiSystem.SecondDescent.preserves_boundary
#print axioms CycleQ2GeometricFourOpenCech.BiSystem.SecondDescent.unique_mod_boundary

end
end SourceCartierSecondNaturality

section SourceCartierProductRefinement

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricLocalizedCech

open scoped TensorProduct
open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]

/-- The actual scalar ring on a mixed principal intersection. The order
matches homogeneous localization at the second-cover product times the
first-cover product. -/
abbrev ProductRing (a b : Fin 4 → R) (s t : Finset (Fin 4)) :=
  Localization.Away (coverProduct b t * coverProduct a s)

/-- Canonical restriction induced by the divisibility of the two products. -/
def productRestriction (a b : Fin 4 → R)
    {s s' t t' : Finset (Fin 4)} (hs : s ⊆ s') (ht : t ⊆ t') :
    ProductRing a b s t →ₐ[R] ProductRing a b s' t' where
  __ := IsLocalization.Away.lift (S := ProductRing a b s t)
    (coverProduct b t * coverProduct a s)
    (IsLocalization.Away.isUnit_of_dvd (S := ProductRing a b s' t')
      (coverProduct b t' * coverProduct a s')
      (mul_dvd_mul (Finset.prod_dvd_prod_of_subset t t' b ht)
        (Finset.prod_dvd_prod_of_subset s s' a hs)))
  commutes' x := IsLocalization.Away.lift_eq _ _ x

@[simp] theorem productRestriction_comp (a b : Fin 4 → R)
    {s s' s'' t t' t'' : Finset (Fin 4)}
    (hs : s ⊆ s') (hs' : s' ⊆ s'') (ht : t ⊆ t') (ht' : t' ⊆ t'')
    (x : ProductRing a b s t) :
    productRestriction a b hs' ht' (productRestriction a b hs ht x) =
      productRestriction a b (hs.trans hs') (ht.trans ht') x := by
  have h : (productRestriction a b hs' ht').comp (productRestriction a b hs ht) =
      productRestriction a b (hs.trans hs') (ht.trans ht') := by
    apply IsLocalization.algHom_ext (Submonoid.powers (coverProduct b t * coverProduct a s))
    ext z
  exact AlgHom.congr_fun h x

@[simp] theorem productRestriction_self (a b : Fin 4 → R) (s t : Finset (Fin 4)) :
    productRestriction a b (s := s) (t := t) (by rfl) (by rfl) = AlgHom.id R _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coverProduct b t * coverProduct a s))
  ext z

/-- The two actual localization restriction directions on the ordinary
mixed product rings. -/
def productSystem (a b : Fin 4 → R) : BiSystem (R := R) (ProductRing a b) where
  left t := {
    res hs := (productRestriction a b hs (show t ⊆ t by rfl)).toLinearMap
    res_id s := congrArg AlgHom.toLinearMap (productRestriction_self a b s t)
    res_comp hs hs' := by
      apply LinearMap.ext
      intro x
      exact productRestriction_comp a b hs hs' (by rfl) (by rfl) x }
  right s := {
    res ht := (productRestriction a b (show s ⊆ s by rfl) ht).toLinearMap
    res_id t := congrArg AlgHom.toLinearMap (productRestriction_self a b s t)
    res_comp ht ht' := by
      apply LinearMap.ext
      intro x
      exact productRestriction_comp a b (by rfl) (by rfl) ht ht' x }
  interchange hs ht x := by
    change productRestriction a b hs (by rfl)
        (productRestriction a b (by rfl) ht x) =
      productRestriction a b (by rfl) ht
        (productRestriction a b hs (by rfl) x)
    simp only [productRestriction_comp]

/-- Tensoring the scalar module does not change its actual localization. -/
instance scalarModuleAt_isLocalization (a : Fin 4 → R) (s : Finset (Fin 4)) :
    IsLocalization.Away (coverProduct a s) (ModuleAt R a s) :=
  IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (coverProduct a s))
    (Algebra.TensorProduct.rid R R (RingAt a s)).symm

/-- Successive tensor localizations are the actual localization at the
product of the two denominators. -/
instance mixedScalar_isLocalization (a b : Fin 4 → R) (s t : Finset (Fin 4)) :
    IsLocalization.Away (coverProduct b t * coverProduct a s) (MixedModule R a b s t) :=
  IsLocalization.Away.mul' (RingAt b t) (MixedModule R a b s t)
    (coverProduct b t) (coverProduct a s)

/-- The canonical algebra equivalence, fixed by the original base-ring map. -/
def mixedScalarEquiv (a b : Fin 4 → R) (s t : Finset (Fin 4)) :
    MixedModule R a b s t ≃ₐ[R] ProductRing a b s t :=
  IsLocalization.algEquiv (Submonoid.powers (coverProduct b t * coverProduct a s))
    (MixedModule R a b s t) (ProductRing a b s t)

/-- The existing left tensor restriction is an algebra map. -/
def mixedLeftRingRestriction (a b : Fin 4 → R)
    {s s' : Finset (Fin 4)} (hs : s ⊆ s') (t : Finset (Fin 4)) :
    MixedModule R a b s t →ₐ[R] MixedModule R a b s' t :=
  Algebra.TensorProduct.map (AlgHom.id R (RingAt b t))
    (Algebra.TensorProduct.map (ringRestriction a hs) (AlgHom.id R R))

/-- The existing right tensor restriction is an algebra map. -/
def mixedRightRingRestriction (a b : Fin 4 → R) (s : Finset (Fin 4))
    {t t' : Finset (Fin 4)} (ht : t ⊆ t') :
    MixedModule R a b s t →ₐ[R] MixedModule R a b s t' :=
  Algebra.TensorProduct.map (ringRestriction b ht) (AlgHom.id R (ModuleAt R a s))

@[simp] theorem mixedLeftRingRestriction_toLinearMap (a b : Fin 4 → R)
    {s s' : Finset (Fin 4)} (hs : s ⊆ s') (t : Finset (Fin 4)) :
    (mixedLeftRingRestriction a b hs t).toLinearMap = ((mixedSystem R a b).left t).res hs := by
  ext z y x
  rfl

@[simp] theorem mixedRightRingRestriction_toLinearMap (a b : Fin 4 → R)
    (s : Finset (Fin 4)) {t t' : Finset (Fin 4)} (ht : t ⊆ t') :
    (mixedRightRingRestriction a b s ht).toLinearMap = ((mixedSystem R a b).right s).res ht := by
  ext z x
  rfl

theorem mixedScalarEquiv_left (a b : Fin 4 → R)
    {s s' : Finset (Fin 4)} (hs : s ⊆ s') (t : Finset (Fin 4))
    (x : MixedModule R a b s t) :
    mixedScalarEquiv a b s' t (((mixedSystem R a b).left t).res hs x) =
      ((productSystem a b).left t).res hs (mixedScalarEquiv a b s t x) := by
  have h : (mixedScalarEquiv a b s' t).toAlgHom.comp (mixedLeftRingRestriction a b hs t) =
      (productRestriction a b hs (show t ⊆ t by rfl)).comp
        (mixedScalarEquiv a b s t).toAlgHom := by
    apply IsLocalization.algHom_ext (R := R) (A := R)
      (L := MixedModule R a b s t) (B := ProductRing a b s' t)
      (Submonoid.powers (coverProduct b t * coverProduct a s))
    ext z
  have hx := AlgHom.congr_fun h x
  change mixedScalarEquiv a b s' t ((mixedLeftRingRestriction a b hs t).toLinearMap x) =
    (productRestriction a b hs (show t ⊆ t by rfl)).toLinearMap
      (mixedScalarEquiv a b s t x) at hx
  change mixedScalarEquiv a b s' t (((mixedSystem R a b).left t).res hs x) =
    (productRestriction a b hs (show t ⊆ t by rfl)).toLinearMap
      (mixedScalarEquiv a b s t x)
  simpa only [mixedLeftRingRestriction_toLinearMap] using hx

theorem mixedScalarEquiv_right (a b : Fin 4 → R) (s : Finset (Fin 4))
    {t t' : Finset (Fin 4)} (ht : t ⊆ t') (x : MixedModule R a b s t) :
    mixedScalarEquiv a b s t' (((mixedSystem R a b).right s).res ht x) =
      ((productSystem a b).right s).res ht (mixedScalarEquiv a b s t x) := by
  have h : (mixedScalarEquiv a b s t').toAlgHom.comp (mixedRightRingRestriction a b s ht) =
      (productRestriction a b (show s ⊆ s by rfl) ht).comp
        (mixedScalarEquiv a b s t).toAlgHom := by
    apply IsLocalization.algHom_ext (R := R) (A := R)
      (L := MixedModule R a b s t) (B := ProductRing a b s t')
      (Submonoid.powers (coverProduct b t * coverProduct a s))
    ext z
  have hx := AlgHom.congr_fun h x
  change mixedScalarEquiv a b s t' ((mixedRightRingRestriction a b s ht).toLinearMap x) =
    (productRestriction a b (show s ⊆ s by rfl) ht).toLinearMap
      (mixedScalarEquiv a b s t x) at hx
  change mixedScalarEquiv a b s t' (((mixedSystem R a b).right s).res ht x) =
    (productRestriction a b (show s ⊆ s by rfl) ht).toLinearMap
      (mixedScalarEquiv a b s t x)
  simpa only [mixedRightRingRestriction_toLinearMap] using hx

/-- Both complete ordinary diagrams agree through the canonical
localization equivalences. -/
def mixedToProduct (a b : Fin 4 → R) :
    BiSystemMorphism (mixedSystem R a b) (productSystem a b) where
  app s t := (mixedScalarEquiv a b s t).toLinearMap
  naturality_left hs x := mixedScalarEquiv_left a b hs _ x
  naturality_right ht x := mixedScalarEquiv_right a b _ ht x

def productToMixed (a b : Fin 4 → R) :
    BiSystemMorphism (productSystem a b) (mixedSystem R a b) where
  app s t := (mixedScalarEquiv a b s t).symm.toLinearMap
  naturality_left {s s' t} hs x := by
    apply (mixedScalarEquiv a b s' t).injective
    change mixedScalarEquiv a b s' t ((mixedScalarEquiv a b s' t).symm
      (((productSystem a b).left t).res hs x)) =
      mixedScalarEquiv a b s' t (((mixedSystem R a b).left t).res hs
        ((mixedScalarEquiv a b s t).symm x))
    rw [AlgEquiv.apply_symm_apply, mixedScalarEquiv_left, AlgEquiv.apply_symm_apply]
  naturality_right {s t t'} ht x := by
    apply (mixedScalarEquiv a b s t').injective
    change mixedScalarEquiv a b s t' ((mixedScalarEquiv a b s t').symm
      (((productSystem a b).right s).res ht x)) =
      mixedScalarEquiv a b s t' (((mixedSystem R a b).right s).res ht
        ((mixedScalarEquiv a b s t).symm x))
    rw [AlgEquiv.apply_symm_apply, mixedScalarEquiv_right, AlgEquiv.apply_symm_apply]

/-- Actual ordinary product localizations preserve the same degree-two
comparison after passage to the original tensor refinement. -/
theorem productSecondDescent_to_mixed (a b : Fin 4 → R)
    {c : TwoCochain (fun s => ProductRing a b s ∅)}
    {d : TwoCochain (ProductRing a b ∅)}
    (hcd : (productSystem a b).SecondDescent c d) :
    (mixedSystem R a b).SecondDescent
      ((productToMixed a b).left ∅ |>.map2 c)
      ((productToMixed a b).right ∅ |>.map2 d) :=
  (productToMixed a b).mapSecondDescent hcd

end CycleQ2GeometricLocalizedCech

#print axioms CycleQ2GeometricLocalizedCech.mixedScalarEquiv
#print axioms CycleQ2GeometricLocalizedCech.mixedToProduct
#print axioms CycleQ2GeometricLocalizedCech.productSecondDescent_to_mixed

end
end SourceCartierProductRefinement

section SourceCartierProductEndpoints

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricFourOpenCech

section Composition

variable {R : Type*} [CommRing R]
variable {V W X : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]
variable [∀ s, AddCommGroup (W s)] [∀ s, Module R (W s)]
variable [∀ s, AddCommGroup (X s)] [∀ s, Module R (X s)]
variable {D : RestrictionSystem R V} {E : RestrictionSystem R W}
variable {F : RestrictionSystem R X}

def SystemMorphism.comp (g : SystemMorphism E F) (f : SystemMorphism D E) :
    SystemMorphism D F where
  app s := (g.app s).comp (f.app s)
  naturality hs := by
    apply LinearMap.ext
    intro x
    exact (congrArg (g.app _) (f.app_res hs x)).trans (g.app_res hs _)

@[simp] theorem SystemMorphism.comp_mapCycle (g : SystemMorphism E F)
    (f : SystemMorphism D E) (c : TwoCocycles D) :
    (g.comp f).mapCycle c = g.mapCycle (f.mapCycle c) := by
  apply Subtype.ext
  rfl

end Composition

section BiScalars

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra S R]
variable {V W : Finset (Fin 4) → Finset (Fin 4) → Type*}
variable [∀ s t, AddCommGroup (V s t)] [∀ s t, Module R (V s t)]
variable [∀ s t, AddCommGroup (W s t)] [∀ s t, Module R (W s t)]
variable [∀ s t, Module S (V s t)] [∀ s t, IsScalarTower S R (V s t)]
variable [∀ s t, Module S (W s t)] [∀ s t, IsScalarTower S R (W s t)]
variable {D : BiSystem (R := R) V} {E : BiSystem (R := R) W}

def BiSystemMorphism.restrictScalars (f : BiSystemMorphism D E) :
    BiSystemMorphism (D.restrictScalars S) (E.restrictScalars S) where
  app s t := (f.app s t).restrictScalars S
  naturality_left hs x := f.naturality_left hs x
  naturality_right ht x := f.naturality_right ht x

end BiScalars

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricLocalizedCech

open scoped TensorProduct
open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]

instance productLeftEmpty_isLocalization (a b : Fin 4 → R) (s : Finset (Fin 4)) :
    IsLocalization.Away (coverProduct a s) (ProductRing a b s ∅) := by
  have h : coverProduct b ∅ * coverProduct a s = coverProduct a s := by
    simp [coverProduct]
  exact (congrArg (fun f : R => IsLocalization.Away f (ProductRing a b s ∅)) h).mp
    (inferInstance : IsLocalization.Away (coverProduct b ∅ * coverProduct a s)
      (ProductRing a b s ∅))

instance productRightEmpty_isLocalization (a b : Fin 4 → R) (t : Finset (Fin 4)) :
    IsLocalization.Away (coverProduct b t) (ProductRing a b ∅ t) := by
  have h : coverProduct b t * coverProduct a ∅ = coverProduct b t := by
    simp [coverProduct]
  exact (congrArg (fun f : R => IsLocalization.Away f (ProductRing a b ∅ t)) h).mp
    (inferInstance : IsLocalization.Away (coverProduct b t * coverProduct a ∅)
      (ProductRing a b ∅ t))

def productLeftEmptyEquiv (a b : Fin 4 → R) (s : Finset (Fin 4)) :
    ProductRing a b s ∅ ≃ₐ[R] RingAt a s :=
  IsLocalization.algEquiv (Submonoid.powers (coverProduct a s)) _ _

def productRightEmptyEquiv (a b : Fin 4 → R) (t : Finset (Fin 4)) :
    ProductRing a b ∅ t ≃ₐ[R] RingAt b t :=
  IsLocalization.algEquiv (Submonoid.powers (coverProduct b t)) _ _

/-- The empty second index set gives precisely the original first-cover
scalar rings, through the localization equivalence fixing the base ring. -/
def productLeftEmpty (a b : Fin 4 → R) :
    SystemMorphism ((productSystem a b).left ∅) (scalarSystem a) where
  app s := (productLeftEmptyEquiv a b s).toLinearMap
  naturality {s s'} hs := by
    apply LinearMap.ext
    intro x
    have h : (productLeftEmptyEquiv a b s').toAlgHom.comp
        (productRestriction a b hs (show (∅ : Finset (Fin 4)) ⊆ ∅ by rfl)) =
        (ringRestriction a hs).comp (productLeftEmptyEquiv a b s).toAlgHom := by
      apply IsLocalization.algHom_ext (Submonoid.powers (coverProduct a s))
      ext z
    exact AlgHom.congr_fun h x

/-- The empty first index set similarly gives the original second cover. -/
def productRightEmpty (a b : Fin 4 → R) :
    SystemMorphism ((productSystem a b).right ∅) (scalarSystem b) where
  app t := (productRightEmptyEquiv a b t).toLinearMap
  naturality {t t'} ht := by
    apply LinearMap.ext
    intro x
    have h : (productRightEmptyEquiv a b t').toAlgHom.comp
        (productRestriction a b (show (∅ : Finset (Fin 4)) ⊆ ∅ by rfl) ht) =
        (ringRestriction b ht).comp (productRightEmptyEquiv a b t).toAlgHom := by
      apply IsLocalization.algHom_ext (Submonoid.powers (coverProduct b t))
      ext z
    exact AlgHom.congr_fun h x

private def mixedLeftRingEmpty (a b : Fin 4 → R) (s : Finset (Fin 4)) :
    MixedModule R a b s ∅ ≃ₐ[R] RingAt a s :=
  ((Algebra.TensorProduct.congr (emptyRingEquiv b) (AlgEquiv.refl : ModuleAt R a s ≃ₐ[R] ModuleAt R a s)).trans
    (Algebra.TensorProduct.lid R (ModuleAt R a s))).trans
      (Algebra.TensorProduct.rid R R (RingAt a s))

private def mixedRightRingEmpty (a b : Fin 4 → R) (t : Finset (Fin 4)) :
    MixedModule R a b ∅ t ≃ₐ[R] RingAt b t :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : RingAt b t ≃ₐ[R] RingAt b t)
    ((Algebra.TensorProduct.congr (emptyRingEquiv a) (AlgEquiv.refl : R ≃ₐ[R] R)).trans
      (Algebra.TensorProduct.lid R R))).trans
    (Algebra.TensorProduct.rid R R (RingAt b t))

private theorem mixedLeftRingEmpty_apply (a b : Fin 4 → R) (s : Finset (Fin 4))
    (x : MixedModule R a b s ∅) :
    mixedLeftRingEmpty a b s x =
      (scalarTensorMorphism a).app s ((mixedLeftEmpty R a b).app s x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z m =>
    induction m using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add m n hm hn => simp only [TensorProduct.tmul_add, map_add, hm, hn]
    | tmul y x =>
      simp only [mixedLeftRingEmpty, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
        map_smul, Algebra.TensorProduct.rid_tmul, AlgEquiv.coe_toAlgHom,
        AlgEquiv.coe_refl, id_eq,
        mixedLeftEmpty, LinearEquiv.coe_coe, emptyModuleEquiv_tmul,
        scalarTensorMorphism_tmul]

private theorem mixedRightRingEmpty_apply (a b : Fin 4 → R) (t : Finset (Fin 4))
    (x : MixedModule R a b ∅ t) :
    mixedRightRingEmpty a b t x =
      (scalarTensorMorphism b).app t ((mixedRightEmpty R a b).app t x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul z m =>
    induction m using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add m n hm hn => simp only [TensorProduct.tmul_add, map_add, hm, hn]
    | tmul y x =>
      simp only [mixedRightRingEmpty, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
        Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul,
        Algebra.TensorProduct.rid_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq,
        mixedRightEmpty, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        LinearEquiv.coe_coe, emptyModuleEquiv_tmul, scalarTensorMorphism_tmul]

theorem productLeftEmpty_mixed (a b : Fin 4 → R) (s : Finset (Fin 4))
    (x : MixedModule R a b s ∅) :
    (productLeftEmpty a b).app s (mixedScalarEquiv a b s ∅ x) =
      (scalarTensorMorphism a).app s ((mixedLeftEmpty R a b).app s x) := by
  have h : (productLeftEmptyEquiv a b s).toAlgHom.comp
      (mixedScalarEquiv a b s ∅).toAlgHom = (mixedLeftRingEmpty a b s).toAlgHom := by
    apply IsLocalization.algHom_ext (R := R) (A := R)
      (L := MixedModule R a b s ∅) (B := RingAt a s)
      (Submonoid.powers (coverProduct b ∅ * coverProduct a s))
    ext z
  exact (AlgHom.congr_fun h x).trans (mixedLeftRingEmpty_apply a b s x)

theorem productRightEmpty_mixed (a b : Fin 4 → R) (t : Finset (Fin 4))
    (x : MixedModule R a b ∅ t) :
    (productRightEmpty a b).app t (mixedScalarEquiv a b ∅ t x) =
      (scalarTensorMorphism b).app t ((mixedRightEmpty R a b).app t x) := by
  have h : (productRightEmptyEquiv a b t).toAlgHom.comp
      (mixedScalarEquiv a b ∅ t).toAlgHom = (mixedRightRingEmpty a b t).toAlgHom := by
    apply IsLocalization.algHom_ext (R := R) (A := R)
      (L := MixedModule R a b ∅ t) (B := RingAt b t)
      (Submonoid.powers (coverProduct b t * coverProduct a ∅))
    ext z
  exact (AlgHom.congr_fun h x).trans (mixedRightRingEmpty_apply a b t x)

theorem productLeftEmpty_mapCycle (a b : Fin 4 → R)
    (c : TwoCocycles ((productSystem a b).left ∅)) :
    (scalarTensorMorphism a).mapCycle
      ((mixedLeftEmpty R a b).mapCycle (((productToMixed a b).left ∅).mapCycle c)) =
      (productLeftEmpty a b).mapCycle c := by
  have happ (s : Finset (Fin 4)) (z : ProductRing a b s ∅) :
      (scalarTensorMorphism a).app s
        ((mixedLeftEmpty R a b).app s ((mixedScalarEquiv a b s ∅).symm z)) =
      (productLeftEmpty a b).app s z := by
    have h := productLeftEmpty_mixed a b s ((mixedScalarEquiv a b s ∅).symm z)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  apply Subtype.ext
  dsimp only [SystemMorphism.mapCycle,SystemMorphism.map2,
    BiSystemMorphism.left,productToMixed]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  all_goals exact happ _ _

theorem productRightEmpty_mapCycle (a b : Fin 4 → R)
    (d : TwoCocycles ((productSystem a b).right ∅)) :
    (scalarTensorMorphism b).mapCycle
      ((mixedRightEmpty R a b).mapCycle (((productToMixed a b).right ∅).mapCycle d)) =
      (productRightEmpty a b).mapCycle d := by
  have happ (t : Finset (Fin 4)) (z : ProductRing a b ∅ t) :
      (scalarTensorMorphism b).app t
        ((mixedRightEmpty R a b).app t ((mixedScalarEquiv a b ∅ t).symm z)) =
      (productRightEmpty a b).app t z := by
    have h := productRightEmpty_mixed a b t ((mixedScalarEquiv a b ∅ t).symm z)
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  apply Subtype.ext
  dsimp only [SystemMorphism.mapCycle,SystemMorphism.map2,
    BiSystemMorphism.right,productToMixed]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  all_goals exact happ _ _

/-- Scalar representatives related through the ordinary product rings,
retaining both canonical empty-index identifications. -/
def ScalarProductSecondDescent (a b : Fin 4 → R)
    (c : TwoCocycles (scalarSystem a)) (d : TwoCocycles (scalarSystem b)) : Prop :=
  ∃ c' : TwoCocycles ((productSystem a b).left ∅),
    ∃ d' : TwoCocycles ((productSystem a b).right ∅),
      (productLeftEmpty a b).mapCycle c' = c ∧
      (productRightEmpty a b).mapCycle d' = d ∧
      (productSystem a b).SecondDescent c'.val d'.val

/-- The ordinary scalar-product relation is the same actual principal
comparison already used for the nonvanishing and cubic-multiple proofs. -/
theorem ScalarProductSecondDescent.to_principal (a b : Fin 4 → R)
    {c : TwoCocycles (scalarSystem a)} {d : TwoCocycles (scalarSystem b)}
    (hcd : ScalarProductSecondDescent a b c d) :
    ∃ cT : TwoCocycles (moduleSystem R a), ∃ dT : TwoCocycles (moduleSystem R b),
      (scalarTensorMorphism a).mapCycle cT = c ∧
      PrincipalSecondDescent R a b cT dT ∧ (scalarTensorMorphism b).mapCycle dT = d := by
  obtain ⟨c',d',hc',hd',hcd'⟩ := hcd
  let cm := ((productToMixed a b).left ∅).mapCycle c'
  let dm := ((productToMixed a b).right ∅).mapCycle d'
  refine ⟨(mixedLeftEmpty R a b).mapCycle cm,(mixedRightEmpty R a b).mapCycle dm,
    ?_,⟨cm,dm,rfl,rfl,?_⟩,?_⟩
  · exact (productLeftEmpty_mapCycle a b c').trans hc'
  · exact productSecondDescent_to_mixed a b hcd'
  · exact (productRightEmpty_mapCycle a b d').trans hd'

end CycleQ2GeometricLocalizedCech

#print axioms CycleQ2GeometricLocalizedCech.productLeftEmpty_mapCycle
#print axioms CycleQ2GeometricLocalizedCech.productRightEmpty_mapCycle
#print axioms CycleQ2GeometricLocalizedCech.ScalarProductSecondDescent.to_principal

end
end SourceCartierProductEndpoints

section SourceHomogeneousPrincipalRefinement

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricHomogeneousPrincipal

open AlgebraicGeometry HomogeneousLocalization
open scoped BigOperators

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

def product (a : Fin 4 → A) (s : Finset (Fin 4)) : A := ∏ i ∈ s, a i

def productDegree (da : Fin 4 → ℕ) (s : Finset (Fin 4)) : ℕ := ∑ i ∈ s, da i

theorem product_homogeneous (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (s : Finset (Fin 4)) :
    product a s ∈ 𝒜 (productDegree da s) :=
  SetLike.prod_mem_graded 𝒜 da a (fun i _ => ha i)

theorem productDegree_pos (da : Fin 4 → ℕ) (hda : ∀ i, 0 < da i)
    {s : Finset (Fin 4)} (hs : s.Nonempty) : 0 < productDegree da s := by
  obtain ⟨i, hi⟩ := hs
  exact (hda i).trans_le (Finset.single_le_sum (fun j _ => Nat.zero_le (da j)) hi)

theorem product_factor (a : Fin 4 → A) {s t : Finset (Fin 4)} (h : s ⊆ t) :
    product a t = product a s * product a (t \ s) := by
  unfold product
  rw [mul_comm]
  exact (Finset.prod_sdiff h).symm

/-- The actual degree-zero function cutting out D₊(aᵢ) inside D₊(f). -/
def normalizedCover (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) :
    Fin 4 → Away 𝒜 f := fun i => Away.isLocalizationElem hf (ha i)

/-- Products of the actual normalized functions are the normalization
of the corresponding product. -/
theorem normalizedCover_product (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
    (s : Finset (Fin 4)) :
    product (normalizedCover 𝒜 a da ha hf) s =
      Away.isLocalizationElem hf (product_homogeneous 𝒜 a da ha s) := by
  apply (show Function.Injective (algebraMap (Away 𝒜 f) (Localization.Away f))
    from HomogeneousLocalization.val_injective _)
  simp only [product, map_prod, HomogeneousLocalization.algebraMap_apply,
    normalizedCover, Away.isLocalizationElem, Away.val_mk, Localization.mk_prod]
  congr 1
  · simp only [Finset.prod_pow]
  · apply Subtype.ext
    simp only [SubmonoidClass.coe_finsetProd, productDegree,
      Finset.prod_pow_eq_pow_sum]

/-- The actual mixed homogeneous localization; the fixed chart factor
comes first, matching the chosen common-refinement convention. -/
abbrev RowRing (a : Fin 4 → A) (f : A) (s : Finset (Fin 4)) :=
  Away 𝒜 (f * product a s)

def rowAlgebra (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (f : A) (s : Finset (Fin 4)) :
    Algebra (Away 𝒜 f) (RowRing 𝒜 a f s) :=
  (HomogeneousLocalization.awayMap 𝒜 (product_homogeneous 𝒜 a da ha s) rfl).toAlgebra

/-- Every mixed homogeneous chart is the genuine principal localization
of the fixed degree-zero affine chart at the product of the normalized
cover functions. The algebra map is the actual homogeneous restriction. -/
theorem rowIsLocalization (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) {f : A} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (s : Finset (Fin 4)) :
    letI := rowAlgebra 𝒜 a da ha f s
    IsLocalization.Away (product (normalizedCover 𝒜 a da ha hf) s)
      (RowRing 𝒜 a f s) := by
  letI := rowAlgebra 𝒜 a da ha f s
  rw [normalizedCover_product]
  exact Away.isLocalization_mul hf (product_homogeneous 𝒜 a da ha s) rfl hd.ne'

/-- A proved projective cover induces an actual unit-ideal principal
cover on every positive-degree homogeneous affine chart. -/
theorem normalizedCover_span_top (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (hda : ∀ i, 0 < da i)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i)) = ⊤)
    {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Ideal.span (Set.range (normalizedCover 𝒜 a da ha hf)) = ⊤ := by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
  have hh (i : Fin 4) : (Proj.awayι 𝒜 f hf hd) ⁻¹ᵁ Proj.basicOpen 𝒜 (a i) =
      PrimeSpectrum.basicOpen (normalizedCover 𝒜 a da ha hf i) :=
    Proj.awayι_preimage_basicOpen 𝒜 hf hd (ha i) (hda i)
  have hc := (Proj.awayι 𝒜 f hf hd).iSup_preimage_eq_top hcover
  simp only [hh] at hc
  change (⨆ i, PrimeSpectrum.basicOpen (normalizedCover 𝒜 a da ha hf i)) =
    (⊤ : TopologicalSpace.Opens (PrimeSpectrum (Away 𝒜 f))) at hc
  exact hc

end CycleQ2GeometricHomogeneousPrincipal

#print axioms CycleQ2GeometricHomogeneousPrincipal.normalizedCover_product
#print axioms CycleQ2GeometricHomogeneousPrincipal.rowIsLocalization
#print axioms CycleQ2GeometricHomogeneousPrincipal.normalizedCover_span_top

end
end SourceHomogeneousPrincipalRefinement

section SourceHomogeneousBiSystem

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricHomogeneousPrincipal

open HomogeneousLocalization CycleQ2GeometricFourOpenCech
  CycleQ2GeometricLocalizedCech
open scoped BigOperators

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private theorem awayLift_eq_algHom {T U : Type*} [CommRing T] [CommRing U]
    [Algebra T U] (f : T) (hu : IsUnit (algebraMap T U f))
    (ρ : Localization.Away f →ₐ[T] U) :
    Localization.awayLift (algebraMap T U) f hu = ρ.toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  apply RingHom.ext
  intro x
  change IsLocalization.Away.lift f hu (algebraMap T (Localization.Away f) x) =
    ρ (algebraMap T (Localization.Away f) x)
  rw [IsLocalization.Away.lift_eq, ρ.commutes]

/-- A homogeneous restriction has the unique ordinary localization map
on its underlying fraction. -/
theorem awayMap_val_eq {f g x : A} {d : ℕ} (hg : g ∈ 𝒜 d)
    (hx : x = f * g) (ρ : Localization.Away f →ₐ[A] Localization.Away x)
    (z : Away 𝒜 f) : (HomogeneousLocalization.awayMap 𝒜 hg hx z).val = ρ z.val := by
  rw [HomogeneousLocalization.val_awayMap]
  exact DFunLike.congr_fun (awayLift_eq_algHom f _ ρ) z.val

def mixedProduct (a b : Fin 4 → A) (s t : Finset (Fin 4)) : A :=
  product b t * product a s

abbrev MixedRing (a b : Fin 4 → A) (s t : Finset (Fin 4)) :=
  Away 𝒜 (mixedProduct a b s t)

theorem mixedProduct_factor (a b : Fin 4 → A)
    {s s' t t' : Finset (Fin 4)} (hs : s ⊆ s') (ht : t ⊆ t') :
    mixedProduct a b s' t' =
      mixedProduct a b s t * (product b (t' \ t) * product a (s' \ s)) := by
  unfold mixedProduct
  rw [product_factor a hs, product_factor b ht]
  ring

/-- The canonical homogeneous restriction on the actual product chart.
Both the coordinate order and each complement factor are explicit. -/
def restriction (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i))
    {s s' t t' : Finset (Fin 4)} (hs : s ⊆ s') (ht : t ⊆ t') :
    MixedRing 𝒜 a b s t →+* MixedRing 𝒜 a b s' t' :=
  HomogeneousLocalization.awayMap 𝒜
    (SetLike.mul_mem_graded (product_homogeneous 𝒜 b db hb (t' \ t))
      (product_homogeneous 𝒜 a da ha (s' \ s)))
    (mixedProduct_factor a b hs ht)

/-- Forgetting the homogeneous fraction gives precisely the ordinary
canonical product-localization map used by the checked Cartier descent. -/
theorem restriction_val (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i))
    {s s' t t' : Finset (Fin 4)} (hs : s ⊆ s') (ht : t ⊆ t')
    (z : MixedRing 𝒜 a b s t) :
    (restriction 𝒜 a da ha b db hb hs ht z).val =
      productRestriction a b hs ht z.val := by
  exact awayMap_val_eq 𝒜 _ _ (productRestriction a b hs ht) z

theorem restriction_self (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i)) (s t : Finset (Fin 4))
    (z : MixedRing 𝒜 a b s t) :
    restriction 𝒜 a da ha b db hb (s := s) (t := t) (by rfl) (by rfl) z = z := by
  apply HomogeneousLocalization.val_injective
  rw [restriction_val, productRestriction_self]
  rfl

theorem restriction_comp (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i))
    {s s' s'' t t' t'' : Finset (Fin 4)}
    (hs : s ⊆ s') (hs' : s' ⊆ s'') (ht : t ⊆ t') (ht' : t' ⊆ t'')
    (z : MixedRing 𝒜 a b s t) :
    restriction 𝒜 a da ha b db hb hs' ht'
        (restriction 𝒜 a da ha b db hb hs ht z) =
      restriction 𝒜 a da ha b db hb (hs.trans hs') (ht.trans ht') z := by
  apply HomogeneousLocalization.val_injective
  simp only [restriction_val]
  exact productRestriction_comp a b hs hs' ht ht' z.val

/-- The actual homogeneous common refinement, with positive-degree
chart coordinates retained and the ordinary second-cover factor first. -/
def homogeneousBiSystem (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i)) :
    BiSystem (R := ℤ) (MixedRing 𝒜 a b) where
  left t := {
    res hs := (restriction 𝒜 a da ha b db hb hs (show t ⊆ t by rfl)).toAddMonoidHom.toIntLinearMap
    res_id s := LinearMap.ext (restriction_self 𝒜 a da ha b db hb s t)
    res_comp hs hs' := by
      apply LinearMap.ext
      intro z
      exact restriction_comp 𝒜 a da ha b db hb hs hs' (by rfl) (by rfl) z }
  right s := {
    res ht := (restriction 𝒜 a da ha b db hb (show s ⊆ s by rfl) ht).toAddMonoidHom.toIntLinearMap
    res_id t := LinearMap.ext (restriction_self 𝒜 a da ha b db hb s t)
    res_comp ht ht' := by
      apply LinearMap.ext
      intro z
      exact restriction_comp 𝒜 a da ha b db hb (by rfl) (by rfl) ht ht' z }
  interchange hs ht z := by
    change restriction 𝒜 a da ha b db hb hs (by rfl)
        (restriction 𝒜 a da ha b db hb (by rfl) ht z) =
      restriction 𝒜 a da ha b db hb (by rfl) ht
        (restriction 𝒜 a da ha b db hb hs (by rfl) z)
    simp only [restriction_comp]

/-- The literal homogeneous-to-ordinary forgetful maps commute with both
complete restriction directions. They retain every cocycle and every
common-refinement witness before any cohomology quotient is taken. -/
def forgetBiSystem (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i)) :
    BiSystemMorphism (homogeneousBiSystem 𝒜 a da ha b db hb)
      ((productSystem a b).restrictScalars ℤ) where
  app s t := (algebraMap (MixedRing 𝒜 a b s t)
    (Localization.Away (mixedProduct a b s t))).toAddMonoidHom.toIntLinearMap
  naturality_left hs z := restriction_val 𝒜 a da ha b db hb hs (by rfl) z
  naturality_right ht z := restriction_val 𝒜 a da ha b db hb (by rfl) ht z

end CycleQ2GeometricHomogeneousPrincipal

#print axioms CycleQ2GeometricHomogeneousPrincipal.homogeneousBiSystem
#print axioms CycleQ2GeometricHomogeneousPrincipal.forgetBiSystem

end
end SourceHomogeneousBiSystem

section SourceHomogeneousRowExact

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricFourOpenCech.SystemMorphism

variable {R : Type*} [CommRing R]
variable {V W : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]
variable [∀ s, AddCommGroup (W s)] [∀ s, Module R (W s)]
variable {D : RestrictionSystem R V} {E : RestrictionSystem R W}

theorem second_exact_iff_of_bijective (f : SystemMorphism D E)
    (hf : ∀ s, Function.Bijective (f.app s)) :
    Function.Exact (d1 D) (d2 D) ↔ Function.Exact (d1 E) (d2 E) := by
  let e1 := LinearEquiv.ofBijective f.map1 (f.map1_bijective hf)
  let e2 := LinearEquiv.ofBijective f.map2 (f.map2_bijective hf)
  let e3 := LinearEquiv.ofBijective (f.app Finset.univ) (hf Finset.univ)
  have h1 : (d1 E).comp e1.toLinearMap = e2.toLinearMap.comp (d1 D) :=
    LinearMap.ext (fun x => (f.map2_d1 x).symm)
  have h2 : (d2 E).comp e2.toLinearMap = e3.toLinearMap.comp (d2 D) :=
    LinearMap.ext (fun x => (f.app_d2 x).symm)
  exact (Function.Exact.iff_of_ladder_linearEquiv h1 h2).symm

end CycleQ2GeometricFourOpenCech.SystemMorphism

namespace CycleQ2GeometricLocalizedCech

open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]

/-- Actual scalar sections of an affine principal cover are exact through
degree two, with unique gluing in degree zero. -/
theorem scalar_affine_exact (a : Fin 4 → R)
    (ha : Ideal.span (Set.range a) = ⊤) :
    Function.Exact (augmentation (scalarSystem a)) (d0 (scalarSystem a)) ∧
      Function.Injective (augmentation (scalarSystem a)) ∧
      Function.Exact (d0 (scalarSystem a)) (d1 (scalarSystem a)) ∧
      Function.Exact (d1 (scalarSystem a)) (d2 (scalarSystem a)) := by
  letI (i : Fin 4) (s : Finset (Fin 4)) :
      IsLocalizedModule (Submonoid.powers (a i)) ((localizationMorphism R a i).app s) :=
    moduleRestriction_insert_isLocalized R a i s
  have h0 := zero_exact_of_unit_span (moduleSystem R a) a ha
    (fun i s => ModuleAt R a (insert i s)) (localizedSystem R a)
    (localizationMorphism R a) (localizedSystem_pivot R a)
  have hi := augmentation_injective_of_unit_span (moduleSystem R a) a ha
    (fun i s => ModuleAt R a (insert i s)) (localizedSystem R a)
    (localizationMorphism R a) (localizedSystem_pivot R a)
  let f := scalarTensorMorphism a
  have hf (s : Finset (Fin 4)) : Function.Bijective (f.app s) :=
    scalarTensorMorphism_bijective a s
  exact ⟨(f.zero_exact_iff_of_bijective hf).mp h0,
    (f.augmentation_injective_iff_of_bijective hf).mp hi,
    (f.first_exact_iff_of_bijective hf).mp (affine_firstCech_exact R a ha),
    (f.second_exact_iff_of_bijective hf).mp (affine_secondCech_exact R a ha)⟩

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricHomogeneousPrincipal

open AlgebraicGeometry HomogeneousLocalization CycleQ2GeometricFourOpenCech
  CycleQ2GeometricLocalizedCech

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The ordinary map underlying restriction from one fixed homogeneous
chart to a mixed chart. -/
def rowBaseOrdinary (a : Fin 4 → A) (f : A) (s : Finset (Fin 4)) :
    Localization.Away f →ₐ[A] Localization.Away (f * product a s) where
  __ := IsLocalization.Away.lift (S := Localization.Away f) f
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (f * product a s))
      (f * product a s) (dvd_mul_right f (product a s)))
  commutes' x := IsLocalization.Away.lift_eq _ _ x

/-- The actual homogeneous restriction commutes with the actual fixed-chart
algebra maps. The equality is proved in the ordinary localization, where
all three maps are canonically fixed by the original polynomial ring. -/
theorem leftRestriction_commutes (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i)) (t : Finset (Fin 4))
    {s s' : Finset (Fin 4)} (hs : s ⊆ s') (z : Away 𝒜 (product b t)) :
    restriction 𝒜 a da ha b db hb hs (show t ⊆ t by rfl)
        (HomogeneousLocalization.awayMap 𝒜 (product_homogeneous 𝒜 a da ha s) rfl z) =
      HomogeneousLocalization.awayMap 𝒜 (product_homogeneous 𝒜 a da ha s') rfl z := by
  have hm : (productRestriction a b hs (show t ⊆ t by rfl)).comp
        (rowBaseOrdinary a (product b t) s) = rowBaseOrdinary a (product b t) s' := by
    apply IsLocalization.algHom_ext (Submonoid.powers (product b t))
    ext
  let y : MixedRing 𝒜 a b s t :=
    HomogeneousLocalization.awayMap 𝒜 (product_homogeneous 𝒜 a da ha s) rfl z
  have hy : y.val = rowBaseOrdinary a (product b t) s z.val :=
    awayMap_val_eq 𝒜 _ _ (rowBaseOrdinary a (product b t) s) z
  have hz : (HomogeneousLocalization.awayMap 𝒜
      (product_homogeneous 𝒜 a da ha s') rfl z).val =
      rowBaseOrdinary a (product b t) s' z.val :=
    awayMap_val_eq 𝒜 _ _ (rowBaseOrdinary a (product b t) s') z
  apply HomogeneousLocalization.val_injective
  exact (restriction_val 𝒜 a da ha b db hb hs (show t ⊆ t by rfl) y).trans
    ((congrArg (productRestriction a b hs (show t ⊆ t by rfl)) hy).trans
      ((AlgHom.congr_fun hm z.val).trans hz.symm))

/-- Pointwise canonical algebra equivalences from the ordinary principal
cover on the fixed affine chart to its actual homogeneous intersections. -/
def leftRowEquiv (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i)) (t : Finset (Fin 4))
    (ht : 0 < productDegree db t) (s : Finset (Fin 4)) :
    letI : Algebra (Away 𝒜 (product b t)) (MixedRing 𝒜 a b s t) :=
      rowAlgebra 𝒜 a da ha (product b t) s
    RingAt (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s
      ≃ₐ[Away 𝒜 (product b t)] MixedRing 𝒜 a b s t := by
  letI : Algebra (Away 𝒜 (product b t)) (MixedRing 𝒜 a b s t) :=
    rowAlgebra 𝒜 a da ha (product b t) s
  letI : IsLocalization.Away
      (product (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s)
      (MixedRing 𝒜 a b s t) :=
    rowIsLocalization 𝒜 a da ha (product_homogeneous 𝒜 b db hb t) ht s
  letI : IsLocalization.Away
      (product (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s)
      (RingAt (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s) := by
    change IsLocalization.Away
      (product (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s)
      (Localization.Away
        (product (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s))
    infer_instance
  exact IsLocalization.algEquiv
    (Submonoid.powers
      (product (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s)) _ _

/-- The pointwise localization equivalences commute with every actual
homogeneous restriction. The base is ℤ only to give both cover directions
one common scalar ring. -/
def leftRowMorphism (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i)) (t : Finset (Fin 4))
    (ht : 0 < productDegree db t) :
    SystemMorphism
      ((scalarSystem (normalizedCover 𝒜 a da ha
        (product_homogeneous 𝒜 b db hb t))).restrictScalars ℤ)
      ((homogeneousBiSystem 𝒜 a da ha b db hb).left t) := by
  letI (s : Finset (Fin 4)) : Algebra (Away 𝒜 (product b t)) (MixedRing 𝒜 a b s t) :=
    rowAlgebra 𝒜 a da ha (product b t) s
  letI (s : Finset (Fin 4)) : IsLocalization.Away
      (product (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s)
      (MixedRing 𝒜 a b s t) :=
    rowIsLocalization 𝒜 a da ha (product_homogeneous 𝒜 b db hb t) ht s
  letI (s : Finset (Fin 4)) : IsLocalization.Away
      (product (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s)
      (RingAt (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s) := by
    change IsLocalization.Away
      (product (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s)
      (Localization.Away
        (product (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s))
    infer_instance
  refine {
    app s := ((leftRowEquiv 𝒜 a da ha b db hb t ht s).toLinearMap).restrictScalars ℤ
    naturality := ?_ }
  intro s s' hs
  let ρ : MixedRing 𝒜 a b s t →ₐ[Away 𝒜 (product b t)] MixedRing 𝒜 a b s' t := {
    __ := restriction 𝒜 a da ha b db hb hs (show t ⊆ t by rfl)
    commutes' z := leftRestriction_commutes 𝒜 a da ha b db hb t hs z }
  have hm : (leftRowEquiv 𝒜 a da ha b db hb t ht s').toAlgHom.comp
        (ringRestriction (normalizedCover 𝒜 a da ha
          (product_homogeneous 𝒜 b db hb t)) hs) =
      ρ.comp (leftRowEquiv 𝒜 a da ha b db hb t ht s).toAlgHom := by
    apply IsLocalization.algHom_ext
      (Submonoid.powers
        (product (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t)) s))
    ext
  exact LinearMap.ext (AlgHom.congr_fun hm)

theorem leftRowMorphism_bijective (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i)) (t : Finset (Fin 4))
    (ht : 0 < productDegree db t) (s : Finset (Fin 4)) :
    Function.Bijective ((leftRowMorphism 𝒜 a da ha b db hb t ht).app s) := by
  letI : Algebra (Away 𝒜 (product b t)) (MixedRing 𝒜 a b s t) :=
    rowAlgebra 𝒜 a da ha (product b t) s
  exact (leftRowEquiv 𝒜 a da ha b db hb t ht s).bijective

/-- On every nonempty chart of the second cover, the first homogeneous
cover is an actual affine principal cover and is exact in degrees zero,
one, and two. There is no cohomological vanishing assumption. -/
theorem leftRow_exact (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (hda : ∀ i, 0 < da i)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i)) = ⊤)
    (b : Fin 4 → A) (db : Fin 4 → ℕ) (hb : ∀ i, b i ∈ 𝒜 (db i))
    (hdb : ∀ i, 0 < db i) (t : Finset (Fin 4)) (ht : t.Nonempty) :
    let D := (homogeneousBiSystem 𝒜 a da ha b db hb).left t
    Function.Exact (augmentation D) (d0 D) ∧
      Function.Injective (augmentation D) ∧
      Function.Exact (d0 D) (d1 D) ∧ Function.Exact (d1 D) (d2 D) := by
  have ht' := productDegree_pos db hdb ht
  let f := leftRowMorphism 𝒜 a da ha b db hb t ht'
  have hf := leftRowMorphism_bijective 𝒜 a da ha b db hb t ht'
  have h := scalar_affine_exact
    (normalizedCover 𝒜 a da ha (product_homogeneous 𝒜 b db hb t))
    (normalizedCover_span_top 𝒜 a da ha hda hcover
      (product_homogeneous 𝒜 b db hb t) ht')
  exact ⟨(f.zero_exact_iff_of_bijective hf).mp h.1,
    (f.augmentation_injective_iff_of_bijective hf).mp h.2.1,
    (f.first_exact_iff_of_bijective hf).mp h.2.2.1,
    (f.second_exact_iff_of_bijective hf).mp h.2.2.2⟩

end CycleQ2GeometricHomogeneousPrincipal

#print axioms CycleQ2GeometricFourOpenCech.SystemMorphism.second_exact_iff_of_bijective
#print axioms CycleQ2GeometricLocalizedCech.scalar_affine_exact
#print axioms CycleQ2GeometricHomogeneousPrincipal.leftRestriction_commutes
#print axioms CycleQ2GeometricHomogeneousPrincipal.leftRowMorphism
#print axioms CycleQ2GeometricHomogeneousPrincipal.leftRow_exact

end
end SourceHomogeneousRowExact

section SourceHomogeneousEndpoints

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricHomogeneousPrincipal

open AlgebraicGeometry HomogeneousLocalization CycleQ2GeometricFourOpenCech
  CycleQ2GeometricLocalizedCech

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

abbrev HomogeneousRing (a : Fin 4 → A) (s : Finset (Fin 4)) :=
  Away 𝒜 (product a s)

def singleRestriction (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) {s t : Finset (Fin 4)} (hs : s ⊆ t) :
    HomogeneousRing 𝒜 a s →+* HomogeneousRing 𝒜 a t :=
  HomogeneousLocalization.awayMap 𝒜 (product_homogeneous 𝒜 a da ha (t \ s))
    (product_factor a hs)

theorem singleRestriction_val (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) {s t : Finset (Fin 4)} (hs : s ⊆ t)
    (z : HomogeneousRing 𝒜 a s) :
    (singleRestriction 𝒜 a da ha hs z).val = ringRestriction a hs z.val :=
  awayMap_val_eq 𝒜 _ _ (ringRestriction a hs) z

theorem singleRestriction_self (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (s : Finset (Fin 4))
    (z : HomogeneousRing 𝒜 a s) :
    singleRestriction 𝒜 a da ha (s := s) (t := s) (by rfl) z = z := by
  apply HomogeneousLocalization.val_injective
  rw [singleRestriction_val, ringRestriction_self]
  rfl

theorem singleRestriction_comp (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) {s t u : Finset (Fin 4)}
    (hs : s ⊆ t) (ht : t ⊆ u) (z : HomogeneousRing 𝒜 a s) :
    singleRestriction 𝒜 a da ha ht (singleRestriction 𝒜 a da ha hs z) =
      singleRestriction 𝒜 a da ha (hs.trans ht) z := by
  apply HomogeneousLocalization.val_injective
  simp only [singleRestriction_val]
  exact ringRestriction_comp a hs ht z.val

def homogeneousSystem (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) : RestrictionSystem ℤ (HomogeneousRing 𝒜 a) where
  res hs := (singleRestriction 𝒜 a da ha hs).toAddMonoidHom.toIntLinearMap
  res_id s := LinearMap.ext (singleRestriction_self 𝒜 a da ha s)
  res_comp hs ht := LinearMap.ext (singleRestriction_comp 𝒜 a da ha hs ht)

def homogeneousForget (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) :
    SystemMorphism (homogeneousSystem 𝒜 a da ha) ((scalarSystem a).restrictScalars ℤ) where
  app s := (algebraMap (HomogeneousRing 𝒜 a s)
    (Localization.Away (product a s))).toAddMonoidHom.toIntLinearMap
  naturality hs := LinearMap.ext (singleRestriction_val 𝒜 a da ha hs)

def awayCongr {f g : A} (h : f = g) : Away 𝒜 f ≃+* Away 𝒜 g :=
  RingEquiv.cast (R := fun f : A => Away 𝒜 f) h

def ordinaryAwayCongr {f g : A} (h : f = g) :
    Localization.Away f ≃ₐ[A] Localization.Away g := by
  subst g
  exact AlgEquiv.refl

theorem awayCongr_val {f g : A} (h : f = g) (z : Away 𝒜 f) :
    (awayCongr 𝒜 h z).val = ordinaryAwayCongr h z.val := by
  subst g
  rfl

def leftEmptyEquiv (a b : Fin 4 → A) (s : Finset (Fin 4)) :
    MixedRing 𝒜 a b s ∅ ≃+* HomogeneousRing 𝒜 a s :=
  awayCongr 𝒜 (by simp only [mixedProduct, product, Finset.prod_empty, one_mul])

def rightEmptyEquiv (a b : Fin 4 → A) (t : Finset (Fin 4)) :
    MixedRing 𝒜 a b ∅ t ≃+* HomogeneousRing 𝒜 b t :=
  awayCongr 𝒜 (by simp only [mixedProduct, product, Finset.prod_empty, mul_one])

theorem leftEmptyEquiv_val (a b : Fin 4 → A) (s : Finset (Fin 4))
    (z : MixedRing 𝒜 a b s ∅) :
    (leftEmptyEquiv 𝒜 a b s z).val = productLeftEmptyEquiv a b s z.val := by
  let h : mixedProduct a b s ∅ = product a s := by
    simp only [mixedProduct, product, Finset.prod_empty, one_mul]
  change (awayCongr 𝒜 h z).val = _
  rw [awayCongr_val]
  letI : IsLocalization.Away (product a s)
      (Localization.Away (mixedProduct a b s ∅)) :=
    (congrArg (fun f : A => IsLocalization.Away f
      (Localization.Away (mixedProduct a b s ∅))) h).mp
        (inferInstance : IsLocalization.Away (mixedProduct a b s ∅)
          (Localization.Away (mixedProduct a b s ∅)))
  have hm : (ordinaryAwayCongr h).toAlgHom = (productLeftEmptyEquiv a b s).toAlgHom := by
    apply IsLocalization.algHom_ext (Submonoid.powers (product a s))
    ext
  exact AlgHom.congr_fun hm z.val

theorem rightEmptyEquiv_val (a b : Fin 4 → A) (t : Finset (Fin 4))
    (z : MixedRing 𝒜 a b ∅ t) :
    (rightEmptyEquiv 𝒜 a b t z).val = productRightEmptyEquiv a b t z.val := by
  let h : mixedProduct a b ∅ t = product b t := by
    simp only [mixedProduct, product, Finset.prod_empty, mul_one]
  change (awayCongr 𝒜 h z).val = _
  rw [awayCongr_val]
  letI : IsLocalization.Away (product b t)
      (Localization.Away (mixedProduct a b ∅ t)) :=
    (congrArg (fun f : A => IsLocalization.Away f
      (Localization.Away (mixedProduct a b ∅ t))) h).mp
        (inferInstance : IsLocalization.Away (mixedProduct a b ∅ t)
          (Localization.Away (mixedProduct a b ∅ t)))
  have hm : (ordinaryAwayCongr h).toAlgHom = (productRightEmptyEquiv a b t).toAlgHom := by
    apply IsLocalization.algHom_ext (Submonoid.powers (product b t))
    ext
  exact AlgHom.congr_fun hm z.val

def homogeneousLeftEmpty (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i)) :
    SystemMorphism ((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅)
      (homogeneousSystem 𝒜 a da ha) where
  app s := (leftEmptyEquiv 𝒜 a b s).toAddEquiv.toIntLinearEquiv.toLinearMap
  naturality {s s'} hs := by
    apply LinearMap.ext
    intro z
    apply HomogeneousLocalization.val_injective
    change (leftEmptyEquiv 𝒜 a b s' (restriction 𝒜 a da ha b db hb hs (by rfl) z)).val =
      (singleRestriction 𝒜 a da ha hs (leftEmptyEquiv 𝒜 a b s z)).val
    rw [leftEmptyEquiv_val, restriction_val, singleRestriction_val, leftEmptyEquiv_val]
    exact (productLeftEmpty a b).app_res hs z.val

def homogeneousRightEmpty (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i)) :
    SystemMorphism ((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅)
      (homogeneousSystem 𝒜 b db hb) where
  app t := (rightEmptyEquiv 𝒜 a b t).toAddEquiv.toIntLinearEquiv.toLinearMap
  naturality {t t'} ht := by
    apply LinearMap.ext
    intro z
    apply HomogeneousLocalization.val_injective
    change (rightEmptyEquiv 𝒜 a b t' (restriction 𝒜 a da ha b db hb (by rfl) ht z)).val =
      (singleRestriction 𝒜 b db hb ht (rightEmptyEquiv 𝒜 a b t z)).val
    rw [rightEmptyEquiv_val, restriction_val, singleRestriction_val, rightEmptyEquiv_val]
    exact (productRightEmpty a b).app_res ht z.val

theorem leftEmpty_forget_cycle (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i))
    (c : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅)) :
    (productLeftEmpty a b).mapCycle (((forgetBiSystem 𝒜 a da ha b db hb).left ∅).mapCycle c) =
      (homogeneousForget 𝒜 a da ha).mapCycle
        ((homogeneousLeftEmpty 𝒜 a da ha b db hb).mapCycle c) := by
  apply Subtype.ext
  exact Prod.ext (Prod.ext (leftEmptyEquiv_val 𝒜 a b _ c.val.1.1).symm
    (leftEmptyEquiv_val 𝒜 a b _ c.val.1.2).symm)
    (Prod.ext (leftEmptyEquiv_val 𝒜 a b _ c.val.2.1).symm
      (leftEmptyEquiv_val 𝒜 a b _ c.val.2.2).symm)

theorem rightEmpty_forget_cycle (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i))
    (d : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅)) :
    (productRightEmpty a b).mapCycle (((forgetBiSystem 𝒜 a da ha b db hb).right ∅).mapCycle d) =
      (homogeneousForget 𝒜 b db hb).mapCycle
        ((homogeneousRightEmpty 𝒜 a da ha b db hb).mapCycle d) := by
  apply Subtype.ext
  exact Prod.ext (Prod.ext (rightEmptyEquiv_val 𝒜 a b _ d.val.1.1).symm
    (rightEmptyEquiv_val 𝒜 a b _ d.val.1.2).symm)
    (Prod.ext (rightEmptyEquiv_val 𝒜 a b _ d.val.2.1).symm
      (rightEmptyEquiv_val 𝒜 a b _ d.val.2.2).symm)

/-- The homogeneous descendant is related to the original cocycle through
the actual mixed charts and their canonical empty-index identifications. -/
def HomogeneousSecondDescent (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i))
    (c : TwoCocycles (homogeneousSystem 𝒜 a da ha))
    (d : TwoCocycles (homogeneousSystem 𝒜 b db hb)) : Prop :=
  ∃ c' : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅),
    ∃ d' : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅),
      (homogeneousLeftEmpty 𝒜 a da ha b db hb).mapCycle c' = c ∧
      (homogeneousRightEmpty 𝒜 a da ha b db hb).mapCycle d' = d ∧
      (homogeneousBiSystem 𝒜 a da ha b db hb).SecondDescent c'.val d'.val

/-- Forgetting degree preserves the same two cocycles and the same
refinement witnesses in the ordinary product-localization comparison. -/
theorem HomogeneousSecondDescent.to_scalar (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (b : Fin 4 → A) (db : Fin 4 → ℕ)
    (hb : ∀ i, b i ∈ 𝒜 (db i))
    {c : TwoCocycles (homogeneousSystem 𝒜 a da ha)}
    {d : TwoCocycles (homogeneousSystem 𝒜 b db hb)}
    (hcd : HomogeneousSecondDescent 𝒜 a da ha b db hb c d) :
    ScalarProductSecondDescent a b ((homogeneousForget 𝒜 a da ha).mapCycle c)
      ((homogeneousForget 𝒜 b db hb).mapCycle d) := by
  obtain ⟨c',d',hc',hd',hcd'⟩ := hcd
  refine ⟨((forgetBiSystem 𝒜 a da ha b db hb).left ∅).mapCycle c',
    ((forgetBiSystem 𝒜 a da ha b db hb).right ∅).mapCycle d', ?_, ?_, ?_⟩
  · rw [leftEmpty_forget_cycle, hc']
  · rw [rightEmpty_forget_cycle, hd']
  · exact (forgetBiSystem 𝒜 a da ha b db hb).mapSecondDescent hcd'

/-- Actual homogeneous degree-zero descent, constructed only from the
proved projective cover and actual affine localization exactness. -/
theorem exists_homogeneous_second_descent (a : Fin 4 → A) (da : Fin 4 → ℕ)
    (ha : ∀ i, a i ∈ 𝒜 (da i)) (hda : ∀ i, 0 < da i)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i)) = ⊤)
    (b : Fin 4 → A) (db : Fin 4 → ℕ) (hb : ∀ i, b i ∈ 𝒜 (db i))
    (hdb : ∀ i, 0 < db i) (c : TwoCocycles (homogeneousSystem 𝒜 a da ha)) :
    ∃ d : TwoCocycles (homogeneousSystem 𝒜 b db hb),
      HomogeneousSecondDescent 𝒜 a da ha b db hb c d := by
  let D := homogeneousBiSystem 𝒜 a da ha b db hb
  have hleft (t : Finset (Fin 4)) (ht : t.Nonempty) :=
    leftRow_exact 𝒜 a da ha hda hcover b db hb hdb t ht
  have hbij (s : Finset (Fin 4)) :
      Function.Bijective ((homogeneousLeftEmpty 𝒜 a da ha b db hb).app s) :=
    (leftEmptyEquiv 𝒜 a b s).bijective
  obtain ⟨c',hc'⟩ :=
    ((homogeneousLeftEmpty 𝒜 a da ha b db hb).mapCycle_bijective hbij).2 c
  obtain ⟨d',hd',hcd'⟩ := D.exists_second_descent
    (fun t ht => (hleft t ht).2.2.2) (fun t ht => (hleft t ht).2.2.1)
    (fun t ht => (hleft t ht).1) (fun t ht => (hleft t ht).2.1) c'.val c'.property
  exact ⟨(homogeneousRightEmpty 𝒜 a da ha b db hb).mapCycle ⟨d',hd'⟩,
    c',⟨d',hd'⟩,hc',rfl,hcd'⟩

end CycleQ2GeometricHomogeneousPrincipal

#print axioms CycleQ2GeometricHomogeneousPrincipal.HomogeneousSecondDescent.to_scalar
#print axioms CycleQ2GeometricHomogeneousPrincipal.exists_homogeneous_second_descent

end
end SourceHomogeneousEndpoints

section SourceCartierHomogeneousDescent

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricCartierCech

open MvPolynomial HomogeneousLocalization
  CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricFourOpenCech CycleQ2GeometricLocalizedCech
  CycleQ2GeometricHomogeneousPrincipal CycleQ2CartierSurfaceGrading
  CycleQ2CartierHomogeneousCech CycleQ2CartierProjectiveCover CycleQ2NormalConnecting

/-- The stable coordinate family has weight one; its zero fourth member
is homogeneous of that same positive degree. -/
theorem coordinateCover_mem_grade (r : ℂ) (i : Fin 4) :
    coordinateCover r i ∈ surfaceGrade r 1 1 := by
  have hx1 : (X (1 : Fin 5) : CycleQ2SeedTrace.WeightedPoly).IsWeightedHomogeneous weight 1 := by
    simpa [weight] using isWeightedHomogeneous_X ℂ weight (1 : Fin 5)
  have hx2 : (X (2 : Fin 5) : CycleQ2SeedTrace.WeightedPoly).IsWeightedHomogeneous weight 1 := by
    simpa [weight] using isWeightedHomogeneous_X ℂ weight (2 : Fin 5)
  have hx3 : (X (3 : Fin 5) : CycleQ2SeedTrace.WeightedPoly).IsWeightedHomogeneous weight 1 := by
    simpa [weight] using isWeightedHomogeneous_X ℂ weight (3 : Fin 5)
  fin_cases i
  · exact surfaceQuotient_mem_grade r 1 hx1
  · exact surfaceQuotient_mem_grade r 1 hx2
  · exact surfaceQuotient_mem_grade r 1 hx3
  · exact zero_mem _

abbrev homogeneousCartierSystem (r θ : ℂ) :=
  homogeneousSystem (surfaceGrade r θ) (coverElement r θ) coverDegree
    (coverElement_mem_grade r θ)

abbrev homogeneousCoordinateSystem (r : ℂ) :=
  homogeneousSystem (surfaceGrade r 1) (coordinateCover r) (fun _ => 1)
    (coordinateCover_mem_grade r)

/-- The fixed original Cartier boundary with its actual homogeneous
fraction representatives; no class is selected from nonvanishing alone. -/
def literalHomogeneousCartierCycle : TwoCocycles (homogeneousCartierSystem 57 1) :=
  ⟨((literalHomogeneousBoundary012,literalHomogeneousBoundary013),(0,0)), by
    change homogeneousTwoDifferential 57 1 literalHomogeneousCartierCochain = 0
    exact literalHomogeneousCartierCochain_cocycle⟩

theorem literalHomogeneousCartierCycle_forget :
    (homogeneousForget (surfaceGrade 57 1) (coverElement 57 1) coverDegree
      (coverElement_mem_grade 57 1)).map2 literalHomogeneousCartierCycle.val =
        (cartierCycle 57 1 derivativeA 0).val := by
  exact Prod.ext (Prod.ext literalHomogeneousBoundary012_val literalHomogeneousBoundary013_val)
    (Prod.ext HomogeneousLocalization.val_zero HomogeneousLocalization.val_zero)

def homogeneousCoordinateForget (r : ℂ) :
    SystemMorphism (homogeneousCoordinateSystem r)
      ((coordinateScalarSystem r).restrictScalars ℤ) :=
  homogeneousForget (surfaceGrade r 1) (coordinateCover r) (fun _ => 1)
    (coordinateCover_mem_grade r)

/-- Forgetting only homogeneous degree retains the same actual coordinate
fractions and their ordinary scalar Čech cocycle. -/
def forgetCoordinateCycle (r : ℂ)
    (d : TwoCocycles (homogeneousCoordinateSystem r)) :
    TwoCocycles (coordinateScalarSystem r) :=
  (homogeneousCoordinateForget r).mapCycle d

/-- The literal degree-zero coordinate descendant is connected to the
original Cartier cocycle by the already checked ordinary comparison. -/
theorem literal_homogeneous_coordinate_descent :
    ∃ d : TwoCocycles (homogeneousCoordinateSystem 57),
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0)
        (forgetCoordinateCycle 57 d) := by
  obtain ⟨d,hd⟩ := exists_homogeneous_second_descent (surfaceGrade 57 1)
    (coverElement 57 1) coverDegree (coverElement_mem_grade 57 1) coverDegree_pos
    (projective_four_cover 57 1 (by norm_num))
    (coordinateCover 57) (fun _ => 1) (coordinateCover_mem_grade 57)
    (fun _ => by decide) literalHomogeneousCartierCycle
  have ho := HomogeneousSecondDescent.to_scalar (surfaceGrade 57 1)
    (coverElement 57 1) coverDegree (coverElement_mem_grade 57 1)
    (coordinateCover 57) (fun _ => 1) (coordinateCover_mem_grade 57) hd
  obtain ⟨cT,dT,hcT,hmid,hdT⟩ :=
    ScalarProductSecondDescent.to_principal (coverElement 57 1) (coordinateCover 57) ho
  refine ⟨d,cT,dT,?_,hmid,hdT⟩
  apply Subtype.ext
  have hc := congrArg Subtype.val hcT
  change (scalarTensorMorphism (coverElement 57 1)).map2 cT.val = _ at hc
  change (scalarTensorMorphism (coverElement 57 1)).map2 cT.val =
    (cartierCycle 57 1 derivativeA 0).val
  exact hc.trans literalHomogeneousCartierCycle_forget

/-- The actual first triple section in its original degree-zero
homogeneous localization at x₁x₂x₃. -/
def homogeneousCoordinateRepresentative (r : ℂ)
    (d : TwoCocycles (homogeneousCoordinateSystem r)) :
    Away (surfaceGrade r 1) (coordinateProduct r 1 Finset.univ) := d.val.1.1

@[simp] theorem homogeneousCoordinateRepresentative_val (r : ℂ)
    (d : TwoCocycles (homogeneousCoordinateSystem r)) :
    (homogeneousCoordinateRepresentative r d).val =
      coordinateTopRepresentative r (forgetCoordinateCycle r d) := rfl

/-- One actual homogeneous coordinate representative carries the original
literal Cartier class and its nonzero cubic multiple. The same first
triple is supplied explicitly for the Laurent weight/character calculation. -/
theorem literal_homogeneous_coordinate_cubic_nonzero :
    ∃ d : TwoCocycles (coordinateScalarSystem 57),
    ∃ q : Away (surfaceGrade 57 1) (coordinateProduct 57 1 Finset.univ),
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d ∧
      q.val = coordinateTopRepresentative 57 d ∧
      classOf (coordinateScalarSystem 57) d ≠ 0 ∧
      surfaceQuotient 57 1 detectorCubic • classOf (coordinateScalarSystem 57) d ≠ 0 := by
  obtain ⟨d,hd⟩ := literal_homogeneous_coordinate_descent
  refine ⟨forgetCoordinateCycle 57 d,homogeneousCoordinateRepresentative 57 d,
    hd,rfl,?_,literal_descent_cubic_ne_zero _ hd⟩
  intro hz
  have hc := CartierCoordinateDescent.reflects_class_zero 57 (by norm_num) hd hz
  apply literal_cartierClass_ne_zero
  change classOf (surfaceSystem 57 1) (cartierCycle 57 1 derivativeA 0) = 0
  exact hc

end CycleQ2GeometricCartierCech

#print axioms CycleQ2GeometricCartierCech.literalHomogeneousCartierCycle_forget
#print axioms CycleQ2GeometricCartierCech.literal_homogeneous_coordinate_descent
#print axioms CycleQ2GeometricCartierCech.literal_homogeneous_coordinate_cubic_nonzero

end
end SourceCartierHomogeneousDescent
