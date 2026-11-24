import Proposal.GeometricCartierCech

/-!
# The actual Cartier class on the coordinate cover

This continuation constructs the degree-two common-refinement staircase,
retains its actual cochains, and reflects boundaries back to the original
Cartier cover. The literal class and its original cubic multiple descend
to nonzero classes on the three coordinate opens. Their nonvanishing is
detected by the actual rank-nine Laurent coordinates, at arbitrary pole
orders. No character or global de Rham comparison is assumed here.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]

/-- The actual four-open Čech complex contracts in degree two when adjoining
one pivot does not change any section module. -/
theorem second_exact_of_pivot (D : RestrictionSystem R V) (k : Fin 4)
    (h : ∀ s : Finset (Fin 4),
      Function.Bijective (D.res (s := s) (t := insert k s) (by simp))) :
    Function.Exact (d1 D) (d2 D) := by
  intro p
  constructor
  · intro hp
    have bij {s t : Finset (Fin 4)} (hst : s ⊆ t) (ht : t = insert k s) :
        Function.Bijective (D.res hst) := by
      subst t
      exact h s
    change D.res (s := {1,2,3}) (t := Finset.univ) (by decide) p.2.2 -
      D.res (s := {0,2,3}) (t := Finset.univ) (by decide) p.2.1 +
      D.res (s := {0,1,3}) (t := Finset.univ) (by decide) p.1.2 -
      D.res (s := {0,1,2}) (t := Finset.univ) (by decide) p.1.1 = 0 at hp
    fin_cases k
    · obtain ⟨q12, h12⟩ := (bij (s := {1,2}) (t := {0,1,2}) (by decide) (by decide)).2 p.1.1
      obtain ⟨q13, h13⟩ := (bij (s := {1,3}) (t := {0,1,3}) (by decide) (by decide)).2 p.1.2
      obtain ⟨q23, h23⟩ := (bij (s := {2,3}) (t := {0,2,3}) (by decide) (by decide)).2 p.2.1
      refine ⟨((0, 0, 0), (q12, q13, q23)), ?_⟩
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · change D.res (s := {1,2}) (t := {0,1,2}) (by decide) q12 - D.res (s := {0,2}) (t := {0,1,2}) (by decide) 0 + D.res (s := {0,1}) (t := {0,1,2}) (by decide) 0 = p.1.1
        simp only [map_zero, h12, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
      · change D.res (s := {1,3}) (t := {0,1,3}) (by decide) q13 - D.res (s := {0,3}) (t := {0,1,3}) (by decide) 0 + D.res (s := {0,1}) (t := {0,1,3}) (by decide) 0 = p.1.2
        simp only [map_zero, h13, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
      · change D.res (s := {2,3}) (t := {0,2,3}) (by decide) q23 - D.res (s := {0,3}) (t := {0,2,3}) (by decide) 0 + D.res (s := {0,2}) (t := {0,2,3}) (by decide) 0 = p.2.1
        simp only [map_zero, h23, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
      · apply (bij (s := {1,2,3}) (t := Finset.univ) (by decide) (by decide)).1
        change D.res (s := {1,2,3}) (t := Finset.univ) (by decide) (D.res (s := {2,3}) (t := {1,2,3}) (by decide) q23 - D.res (s := {1,3}) (t := {1,2,3}) (by decide) q13 + D.res (s := {1,2}) (t := {1,2,3}) (by decide) q12) = D.res (s := {1,2,3}) (t := Finset.univ) (by decide) p.2.2
        simp only [map_sub, map_add, map_zero, RestrictionSystem.res_res]
        have h12' := congrArg (D.res (s := {0,1,2}) (t := Finset.univ) (by decide)) h12
        have h13' := congrArg (D.res (s := {0,1,3}) (t := Finset.univ) (by decide)) h13
        have h23' := congrArg (D.res (s := {0,2,3}) (t := Finset.univ) (by decide)) h23
        simp only [RestrictionSystem.res_res, map_neg] at h12' h13' h23'
        rw [h12', h13', h23']
        calc
          _ = D.res (s := {1,2,3}) (t := Finset.univ) (by decide) p.2.2 -
            (D.res (s := {1,2,3}) (t := Finset.univ) (by decide) p.2.2 - D.res (s := {0,2,3}) (t := Finset.univ) (by decide) p.2.1 + D.res (s := {0,1,3}) (t := Finset.univ) (by decide) p.1.2 - D.res (s := {0,1,2}) (t := Finset.univ) (by decide) p.1.1) := by abel
          _ = _ := by rw [hp, sub_zero]
    · obtain ⟨q02, h02⟩ := (bij (s := {0,2}) (t := {0,1,2}) (by decide) (by decide)).2 (-p.1.1)
      obtain ⟨q03, h03⟩ := (bij (s := {0,3}) (t := {0,1,3}) (by decide) (by decide)).2 (-p.1.2)
      obtain ⟨q23, h23⟩ := (bij (s := {2,3}) (t := {1,2,3}) (by decide) (by decide)).2 p.2.2
      refine ⟨((0, q02, q03), (0, 0, q23)), ?_⟩
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · change D.res (s := {1,2}) (t := {0,1,2}) (by decide) 0 - D.res (s := {0,2}) (t := {0,1,2}) (by decide) q02 + D.res (s := {0,1}) (t := {0,1,2}) (by decide) 0 = p.1.1
        simp only [map_zero, h02, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
      · change D.res (s := {1,3}) (t := {0,1,3}) (by decide) 0 - D.res (s := {0,3}) (t := {0,1,3}) (by decide) q03 + D.res (s := {0,1}) (t := {0,1,3}) (by decide) 0 = p.1.2
        simp only [map_zero, h03, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
      · apply (bij (s := {0,2,3}) (t := Finset.univ) (by decide) (by decide)).1
        change D.res (s := {0,2,3}) (t := Finset.univ) (by decide) (D.res (s := {2,3}) (t := {0,2,3}) (by decide) q23 - D.res (s := {0,3}) (t := {0,2,3}) (by decide) q03 + D.res (s := {0,2}) (t := {0,2,3}) (by decide) q02) = D.res (s := {0,2,3}) (t := Finset.univ) (by decide) p.2.1
        simp only [map_sub, map_add, map_zero, RestrictionSystem.res_res]
        have h02' := congrArg (D.res (s := {0,1,2}) (t := Finset.univ) (by decide)) h02
        have h03' := congrArg (D.res (s := {0,1,3}) (t := Finset.univ) (by decide)) h03
        have h23' := congrArg (D.res (s := {1,2,3}) (t := Finset.univ) (by decide)) h23
        simp only [RestrictionSystem.res_res, map_neg] at h02' h03' h23'
        rw [h02', h03', h23']
        calc
          _ = D.res (s := {0,2,3}) (t := Finset.univ) (by decide) p.2.1 +
            (D.res (s := {1,2,3}) (t := Finset.univ) (by decide) p.2.2 - D.res (s := {0,2,3}) (t := Finset.univ) (by decide) p.2.1 + D.res (s := {0,1,3}) (t := Finset.univ) (by decide) p.1.2 - D.res (s := {0,1,2}) (t := Finset.univ) (by decide) p.1.1) := by abel
          _ = _ := by rw [hp, add_zero]
      · change D.res (s := {2,3}) (t := {1,2,3}) (by decide) q23 - D.res (s := {1,3}) (t := {1,2,3}) (by decide) 0 + D.res (s := {1,2}) (t := {1,2,3}) (by decide) 0 = p.2.2
        simp only [map_zero, h23, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
    · obtain ⟨q01, h01⟩ := (bij (s := {0,1}) (t := {0,1,2}) (by decide) (by decide)).2 p.1.1
      obtain ⟨q03, h03⟩ := (bij (s := {0,3}) (t := {0,2,3}) (by decide) (by decide)).2 (-p.2.1)
      obtain ⟨q13, h13⟩ := (bij (s := {1,3}) (t := {1,2,3}) (by decide) (by decide)).2 (-p.2.2)
      refine ⟨((q01, 0, q03), (0, q13, 0)), ?_⟩
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · change D.res (s := {1,2}) (t := {0,1,2}) (by decide) 0 - D.res (s := {0,2}) (t := {0,1,2}) (by decide) 0 + D.res (s := {0,1}) (t := {0,1,2}) (by decide) q01 = p.1.1
        simp only [map_zero, h01, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
      · apply (bij (s := {0,1,3}) (t := Finset.univ) (by decide) (by decide)).1
        change D.res (s := {0,1,3}) (t := Finset.univ) (by decide) (D.res (s := {1,3}) (t := {0,1,3}) (by decide) q13 - D.res (s := {0,3}) (t := {0,1,3}) (by decide) q03 + D.res (s := {0,1}) (t := {0,1,3}) (by decide) q01) = D.res (s := {0,1,3}) (t := Finset.univ) (by decide) p.1.2
        simp only [map_sub, map_add, map_zero, RestrictionSystem.res_res]
        have h01' := congrArg (D.res (s := {0,1,2}) (t := Finset.univ) (by decide)) h01
        have h03' := congrArg (D.res (s := {0,2,3}) (t := Finset.univ) (by decide)) h03
        have h13' := congrArg (D.res (s := {1,2,3}) (t := Finset.univ) (by decide)) h13
        simp only [RestrictionSystem.res_res, map_neg] at h01' h03' h13'
        rw [h01', h03', h13']
        calc
          _ = D.res (s := {0,1,3}) (t := Finset.univ) (by decide) p.1.2 -
            (D.res (s := {1,2,3}) (t := Finset.univ) (by decide) p.2.2 - D.res (s := {0,2,3}) (t := Finset.univ) (by decide) p.2.1 + D.res (s := {0,1,3}) (t := Finset.univ) (by decide) p.1.2 - D.res (s := {0,1,2}) (t := Finset.univ) (by decide) p.1.1) := by abel
          _ = _ := by rw [hp, sub_zero]
      · change D.res (s := {2,3}) (t := {0,2,3}) (by decide) 0 - D.res (s := {0,3}) (t := {0,2,3}) (by decide) q03 + D.res (s := {0,2}) (t := {0,2,3}) (by decide) 0 = p.2.1
        simp only [map_zero, h03, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
      · change D.res (s := {2,3}) (t := {1,2,3}) (by decide) 0 - D.res (s := {1,3}) (t := {1,2,3}) (by decide) q13 + D.res (s := {1,2}) (t := {1,2,3}) (by decide) 0 = p.2.2
        simp only [map_zero, h13, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
    · obtain ⟨q01, h01⟩ := (bij (s := {0,1}) (t := {0,1,3}) (by decide) (by decide)).2 p.1.2
      obtain ⟨q02, h02⟩ := (bij (s := {0,2}) (t := {0,2,3}) (by decide) (by decide)).2 p.2.1
      obtain ⟨q12, h12⟩ := (bij (s := {1,2}) (t := {1,2,3}) (by decide) (by decide)).2 p.2.2
      refine ⟨((q01, q02, 0), (q12, 0, 0)), ?_⟩
      refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
      · apply (bij (s := {0,1,2}) (t := Finset.univ) (by decide) (by decide)).1
        change D.res (s := {0,1,2}) (t := Finset.univ) (by decide) (D.res (s := {1,2}) (t := {0,1,2}) (by decide) q12 - D.res (s := {0,2}) (t := {0,1,2}) (by decide) q02 + D.res (s := {0,1}) (t := {0,1,2}) (by decide) q01) = D.res (s := {0,1,2}) (t := Finset.univ) (by decide) p.1.1
        simp only [map_sub, map_add, map_zero, RestrictionSystem.res_res]
        have h01' := congrArg (D.res (s := {0,1,3}) (t := Finset.univ) (by decide)) h01
        have h02' := congrArg (D.res (s := {0,2,3}) (t := Finset.univ) (by decide)) h02
        have h12' := congrArg (D.res (s := {1,2,3}) (t := Finset.univ) (by decide)) h12
        simp only [RestrictionSystem.res_res, map_neg] at h01' h02' h12'
        rw [h01', h02', h12']
        calc
          _ = D.res (s := {0,1,2}) (t := Finset.univ) (by decide) p.1.1 +
            (D.res (s := {1,2,3}) (t := Finset.univ) (by decide) p.2.2 - D.res (s := {0,2,3}) (t := Finset.univ) (by decide) p.2.1 + D.res (s := {0,1,3}) (t := Finset.univ) (by decide) p.1.2 - D.res (s := {0,1,2}) (t := Finset.univ) (by decide) p.1.1) := by abel
          _ = _ := by rw [hp, add_zero]
      · change D.res (s := {1,3}) (t := {0,1,3}) (by decide) 0 - D.res (s := {0,3}) (t := {0,1,3}) (by decide) 0 + D.res (s := {0,1}) (t := {0,1,3}) (by decide) q01 = p.1.2
        simp only [map_zero, h01, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
      · change D.res (s := {2,3}) (t := {0,2,3}) (by decide) 0 - D.res (s := {0,3}) (t := {0,2,3}) (by decide) 0 + D.res (s := {0,2}) (t := {0,2,3}) (by decide) q02 = p.2.1
        simp only [map_zero, h02, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
      · change D.res (s := {2,3}) (t := {1,2,3}) (by decide) 0 - D.res (s := {1,3}) (t := {1,2,3}) (by decide) 0 + D.res (s := {1,2}) (t := {1,2,3}) (by decide) q12 = p.2.2
        simp only [map_zero, h12, sub_zero, zero_sub, zero_add, add_zero, neg_neg]
  · rintro ⟨q, rfl⟩
    exact d2_d1 D q

variable {W : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (W s)] [∀ s, Module R (W s)]

namespace SystemMorphism

variable {D : RestrictionSystem R V} {E : RestrictionSystem R W}
variable (S : Submonoid R) (f : SystemMorphism D E)
variable [∀ s, IsLocalizedModule S (f.app s)]

theorem localized_d2 :
    IsLocalizedModule.map S f.map2 (f.app Finset.univ) (d2 D) = d2 E := by
  letI := f.map2_isLocalized S
  apply IsLocalizedModule.linearMap_ext S f.map2 (f.app Finset.univ)
  rw [IsLocalizedModule.map_comp]
  exact LinearMap.ext f.app_d2

include f in
theorem localized_second_exact_iff :
    Function.Exact
      (LocalizedModule.map S (d1 D)) (LocalizedModule.map S (d2 D)) ↔
      Function.Exact (d1 E) (d2 E) := by
  rw [← f.localized_d1 S, ← f.localized_d2 S]
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (IsLocalizedModule.map_iso_commute S f.map1 f.map2 (d1 D))
    (IsLocalizedModule.map_iso_commute S f.map2 (f.app Finset.univ) (d2 D))).symm

end SystemMorphism

/-- Localizing at the actual members of an affine cover detects and solves
all degree-two cocycles via the proved unit-pivot contraction. -/
theorem second_exact_of_unit_span
    (D : RestrictionSystem R V) (a : Fin 4 → R)
    (ha : Ideal.span (Set.range a) = ⊤)
    (W : Fin 4 → Finset (Fin 4) → Type*)
    [∀ i s, AddCommGroup (W i s)] [∀ i s, Module R (W i s)]
    (E : ∀ i, RestrictionSystem R (W i))
    (f : ∀ i, SystemMorphism D (E i))
    [∀ i s, IsLocalizedModule (Submonoid.powers (a i)) ((f i).app s)]
    (hpivot : ∀ (i : Fin 4) (s : Finset (Fin 4)),
      Function.Bijective ((E i).res (s := s) (t := insert i s) (by simp))) :
    Function.Exact (d1 D) (d2 D) := by
  apply CycleQ2GeometricLocalizedCech.exact_of_unit_span a ha (d1 D) (d2 D)
  intro i
  apply ((f i).localized_second_exact_iff (Submonoid.powers (a i))).mpr
  exact second_exact_of_pivot (E i) i (hpivot i)

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricLocalizedCech

open scoped TensorProduct
open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Every actual degree-two module-localization cocycle on an affine
four-element distinguished-open cover has actual degree-one primitives. -/
theorem affine_secondCech_exact (a : Fin 4 → R)
    (ha : Ideal.span (Set.range a) = ⊤) :
    Function.Exact (d1 (moduleSystem M a)) (d2 (moduleSystem M a)) := by
  letI (i : Fin 4) (s : Finset (Fin 4)) :
      IsLocalizedModule (Submonoid.powers (a i)) ((localizationMorphism M a i).app s) :=
    moduleRestriction_insert_isLocalized M a i s
  exact second_exact_of_unit_span (moduleSystem M a) a ha
    (fun i s => ModuleAt M a (insert i s)) (localizedSystem M a)
    (localizationMorphism M a) (localizedSystem_pivot M a)

/-- The same genuine degree-two contraction after arbitrary scalar extension.
The actual cover functions need only generate one on the extended base. -/
theorem baseChanged_affine_second_exact (T : Type*) [CommRing T] [Algebra R T]
    (a : Fin 4 → R)
    (ha : Ideal.span (Set.range (fun i => algebraMap R T (a i))) = ⊤) :
    Function.Exact (d1 (baseChangedSystem T (moduleSystem M a)))
      (d2 (baseChangedSystem T (moduleSystem M a))) := by
  letI (i : Fin 4) (s : Finset (Fin 4)) :
      IsLocalizedModule (Submonoid.powers (a i)) ((localizationMorphism M a i).app s) :=
    moduleRestriction_insert_isLocalized M a i s
  letI (i : Fin 4) (s : Finset (Fin 4)) :
      IsLocalizedModule (Submonoid.powers (algebraMap R T (a i)))
        (((localizationMorphism M a i).baseChange T).app s) :=
    isLocalizedModule_baseChange_away (a i) T ((localizationMorphism M a i).app s)
  have hpivot (i : Fin 4) (s : Finset (Fin 4)) :
      Function.Bijective ((baseChangedSystem T (localizedSystem M a i)).res
        (s := s) (t := insert i s) (by simp)) :=
    baseChange_bijective T _ (localizedSystem_pivot M a i s)
  exact second_exact_of_unit_span (baseChangedSystem T (moduleSystem M a))
    (fun i => algebraMap R T (a i)) ha
    (fun i s => T ⊗[R] ModuleAt M a (insert i s))
    (fun i => baseChangedSystem T (localizedSystem M a i))
    (fun i => (localizationMorphism M a i).baseChange T) hpivot

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricFourOpenCech

section SecondCoverDescent

variable {R : Type*} [CommRing R]
variable {A2 A3 C2 C3 B10 B20 B30 B01 B11 B21 B02 B12 B03 : Type*}
variable [AddCommGroup A2] [AddCommGroup A3] [AddCommGroup C2] [AddCommGroup C3]
variable [AddCommGroup B10] [AddCommGroup B20] [AddCommGroup B30]
variable [AddCommGroup B01] [AddCommGroup B11] [AddCommGroup B21]
variable [AddCommGroup B02] [AddCommGroup B12] [AddCommGroup B03]
variable [Module R A2] [Module R A3] [Module R C2] [Module R C3]
variable [Module R B10] [Module R B20] [Module R B30]
variable [Module R B01] [Module R B11] [Module R B21]
variable [Module R B02] [Module R B12] [Module R B03]

/-- The actual double-complex staircase in degree two. Its witnesses record
the restrictions and primitives connecting the two original cocycles. -/
theorem second_descent_exists
    (dA2 : A2 →ₗ[R] A3) (dC2 : C2 →ₗ[R] C3)
    (u2 : A2 →ₗ[R] B20) (u3 : A3 →ₗ[R] B30)
    (i2 : C2 →ₗ[R] B02) (i3 : C3 →ₗ[R] B03)
    (h10 : B10 →ₗ[R] B20) (h20 : B20 →ₗ[R] B30)
    (h01 : B01 →ₗ[R] B11) (h11 : B11 →ₗ[R] B21)
    (h02 : B02 →ₗ[R] B12)
    (v10 : B10 →ₗ[R] B11) (v20 : B20 →ₗ[R] B21)
    (v01 : B01 →ₗ[R] B02) (v11 : B11 →ₗ[R] B12)
    (v02 : B02 →ₗ[R] B03)
    (hu : ∀ c, h20 (u2 c) = u3 (dA2 c))
    (hi : ∀ c, v02 (i2 c) = i3 (dC2 c))
    (hcomm1 : ∀ x, h11 (v10 x) = v20 (h10 x))
    (hcomm2 : ∀ y, h02 (v01 y) = v11 (h01 y))
    (huv : ∀ c, v20 (u2 c) = 0)
    (hvv1 : ∀ x, v11 (v10 x) = 0)
    (hvv0 : ∀ y, v02 (v01 y) = 0)
    (hrow2 : Function.Exact h10 h20)
    (hrow1 : Function.Exact h01 h11)
    (hglue : Function.Exact i2 h02)
    (hinj : Function.Injective i3)
    (c : A2) (hc : dA2 c = 0) :
    ∃ d : C2, dC2 d = 0 ∧ ∃ x : B10, ∃ y : B01,
      h10 x = u2 c ∧ h01 y = v10 x ∧ i2 d = v01 y := by
  have huc : h20 (u2 c) = 0 := by rw [hu, hc, map_zero]
  obtain ⟨x,hx⟩ := (hrow2 (u2 c)).mp huc
  have hvx : h11 (v10 x) = 0 := by rw [hcomm1, hx, huv]
  obtain ⟨y,hy⟩ := (hrow1 (v10 x)).mp hvx
  have hvy : h02 (v01 y) = 0 := by rw [hcomm2, hy, hvv1]
  obtain ⟨d,hd⟩ := (hglue (v01 y)).mp hvy
  refine ⟨d, ?_, x, y, hx, hy, hd⟩
  apply hinj
  rw [map_zero, ← hi, hd, hvv0]

end SecondCoverDescent

section SecondCoverDescentReflection

variable {R : Type*} [CommRing R]
variable {A1 A2 C1 C2 B00 B10 B20 B01 B11 B02 : Type*}
variable [AddCommGroup A1] [AddCommGroup A2] [AddCommGroup C1] [AddCommGroup C2]
variable [AddCommGroup B00] [AddCommGroup B10] [AddCommGroup B20]
variable [AddCommGroup B01] [AddCommGroup B11] [AddCommGroup B02]
variable [Module R A1] [Module R A2] [Module R C1] [Module R C2]
variable [Module R B00] [Module R B10] [Module R B20]
variable [Module R B01] [Module R B11] [Module R B02]

/-- A degree-two cocycle carried through the actual staircase can become a
boundary only if the original cocycle was already a boundary. -/
theorem second_descent_reflects_boundary
    (dA1 : A1 →ₗ[R] A2) (dC1 : C1 →ₗ[R] C2)
    (u1 : A1 →ₗ[R] B10) (u2 : A2 →ₗ[R] B20)
    (i1 : C1 →ₗ[R] B01) (i2 : C2 →ₗ[R] B02)
    (h00 : B00 →ₗ[R] B10) (h10 : B10 →ₗ[R] B20)
    (h01 : B01 →ₗ[R] B11)
    (v00 : B00 →ₗ[R] B01) (v10 : B10 →ₗ[R] B11) (v01 : B01 →ₗ[R] B02)
    (hu : ∀ a, h10 (u1 a) = u2 (dA1 a))
    (hi : ∀ b, v01 (i1 b) = i2 (dC1 b))
    (hcomm : ∀ z, v10 (h00 z) = h01 (v00 z))
    (hih : ∀ b, h01 (i1 b) = 0)
    (hhh : ∀ z, h10 (h00 z) = 0)
    (hcol1 : Function.Exact v00 v01)
    (hglue : Function.Exact u1 v10)
    (hinj : Function.Injective u2)
    (c : A2) (d : C2) (x : B10) (y : B01)
    (hx : h10 x = u2 c) (hy : h01 y = v10 x) (hd : i2 d = v01 y)
    (hboundary : ∃ b : C1, dC1 b = d) : ∃ a : A1, dA1 a = c := by
  obtain ⟨b,hb⟩ := hboundary
  have hyb : v01 (y - i1 b) = 0 := by rw [map_sub, hi, hb, hd, sub_self]
  obtain ⟨z,hz⟩ := (hcol1 (y - i1 b)).mp hyb
  have hxz : v10 (x - h00 z) = 0 := by
    rw [map_sub, hcomm, hz, map_sub, hih, sub_zero, hy, sub_self]
  obtain ⟨a,ha⟩ := (hglue (x - h00 z)).mp hxz
  refine ⟨a, hinj ?_⟩
  rw [← hu, ha, map_sub, hhh, sub_zero, hx]

end SecondCoverDescentReflection

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricFourOpenCech.BiSystem

variable {R : Type*} [CommRing R]
variable {V : Finset (Fin 4) → Finset (Fin 4) → Type*}
variable [∀ s t, AddCommGroup (V s t)] [∀ s t, Module R (V s t)]
variable (D : CycleQ2GeometricFourOpenCech.BiSystem (R := R) V)

/-- The last vertical differential retains the same actual restrictions. -/
def vertical2 : SystemMorphism D.row2 (D.left Finset.univ) where
  app s := d2 (D.right s)
  naturality hs := by
    apply LinearMap.ext
    intro x
    exact ((D.horizontalMorphism hs).app_d2 x).symm

/-- Exactness of this common-refinement row is the finite product of
actual exactness on its nonempty second-cover overlaps. -/
theorem row0_second_exact
    (h : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (d1 (D.left t)) (d2 (D.left t))) :
    Function.Exact (d1 D.row0) (d2 D.row0) := by
  intro p
  constructor
  · intro hp
    have h0 : d2 (D.left {0}) ((p.1.1.1.1, p.1.2.1.1), (p.2.1.1.1, p.2.2.1.1)) = 0 :=
      congrArg (fun z : ThreeCochain (fun s => ZeroCochain (V s)) => z.1.1) hp
    obtain ⟨q0,hq0⟩ := (h {0} (by simp) ((p.1.1.1.1, p.1.2.1.1), (p.2.1.1.1, p.2.2.1.1))).mp h0
    have h1 : d2 (D.left {1}) ((p.1.1.1.2, p.1.2.1.2), (p.2.1.1.2, p.2.2.1.2)) = 0 :=
      congrArg (fun z : ThreeCochain (fun s => ZeroCochain (V s)) => z.1.2) hp
    obtain ⟨q1,hq1⟩ := (h {1} (by simp) ((p.1.1.1.2, p.1.2.1.2), (p.2.1.1.2, p.2.2.1.2))).mp h1
    have h2 : d2 (D.left {2}) ((p.1.1.2.1, p.1.2.2.1), (p.2.1.2.1, p.2.2.2.1)) = 0 :=
      congrArg (fun z : ThreeCochain (fun s => ZeroCochain (V s)) => z.2.1) hp
    obtain ⟨q2,hq2⟩ := (h {2} (by simp) ((p.1.1.2.1, p.1.2.2.1), (p.2.1.2.1, p.2.2.2.1))).mp h2
    have h3 : d2 (D.left {3}) ((p.1.1.2.2, p.1.2.2.2), (p.2.1.2.2, p.2.2.2.2)) = 0 :=
      congrArg (fun z : ThreeCochain (fun s => ZeroCochain (V s)) => z.2.2) hp
    obtain ⟨q3,hq3⟩ := (h {3} (by simp) ((p.1.1.2.2, p.1.2.2.2), (p.2.1.2.2, p.2.2.2.2))).mp h3
    refine ⟨((((q0.1.1, q1.1.1), (q2.1.1, q3.1.1)), (((q0.1.2.1, q1.1.2.1), (q2.1.2.1, q3.1.2.1)), ((q0.1.2.2, q1.1.2.2), (q2.1.2.2, q3.1.2.2)))), (((q0.2.1, q1.2.1), (q2.2.1, q3.2.1)), (((q0.2.2.1, q1.2.2.1), (q2.2.2.1, q3.2.2.1)), ((q0.2.2.2, q1.2.2.2), (q2.2.2.2, q3.2.2.2))))), ?_⟩
    exact (Prod.ext (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : TwoCochain (fun s => V s {0}) => z.1.1) hq0) (congrArg (fun z : TwoCochain (fun s => V s {1}) => z.1.1) hq1)) (Prod.ext (congrArg (fun z : TwoCochain (fun s => V s {2}) => z.1.1) hq2) (congrArg (fun z : TwoCochain (fun s => V s {3}) => z.1.1) hq3))) (Prod.ext (Prod.ext (congrArg (fun z : TwoCochain (fun s => V s {0}) => z.1.2) hq0) (congrArg (fun z : TwoCochain (fun s => V s {1}) => z.1.2) hq1)) (Prod.ext (congrArg (fun z : TwoCochain (fun s => V s {2}) => z.1.2) hq2) (congrArg (fun z : TwoCochain (fun s => V s {3}) => z.1.2) hq3)))) (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : TwoCochain (fun s => V s {0}) => z.2.1) hq0) (congrArg (fun z : TwoCochain (fun s => V s {1}) => z.2.1) hq1)) (Prod.ext (congrArg (fun z : TwoCochain (fun s => V s {2}) => z.2.1) hq2) (congrArg (fun z : TwoCochain (fun s => V s {3}) => z.2.1) hq3))) (Prod.ext (Prod.ext (congrArg (fun z : TwoCochain (fun s => V s {0}) => z.2.2) hq0) (congrArg (fun z : TwoCochain (fun s => V s {1}) => z.2.2) hq1)) (Prod.ext (congrArg (fun z : TwoCochain (fun s => V s {2}) => z.2.2) hq2) (congrArg (fun z : TwoCochain (fun s => V s {3}) => z.2.2) hq3)))))
  · rintro ⟨q,rfl⟩
    exact d2_d1 D.row0 q

/-- Exactness of this common-refinement row is the finite product of
actual exactness on its nonempty second-cover overlaps. -/
theorem row1_first_exact
    (h : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (d0 (D.left t)) (d1 (D.left t))) :
    Function.Exact (d0 D.row1) (d1 D.row1) := by
  intro p
  constructor
  · intro hp
    have h0 : d1 (D.left {0,1}) ((p.1.1.1.1, (p.1.2.1.1.1, p.1.2.2.1.1)), (p.2.1.1.1, (p.2.2.1.1.1, p.2.2.2.1.1))) = 0 :=
      congrArg (fun z : TwoCochain (fun s => OneCochain (V s)) => ((z.1.1.1.1, z.1.2.1.1), (z.2.1.1.1, z.2.2.1.1))) hp
    obtain ⟨q0,hq0⟩ := (h {0,1} (by simp) ((p.1.1.1.1, (p.1.2.1.1.1, p.1.2.2.1.1)), (p.2.1.1.1, (p.2.2.1.1.1, p.2.2.2.1.1)))).mp h0
    have h1 : d1 (D.left {0,2}) ((p.1.1.1.2.1, (p.1.2.1.1.2.1, p.1.2.2.1.2.1)), (p.2.1.1.2.1, (p.2.2.1.1.2.1, p.2.2.2.1.2.1))) = 0 :=
      congrArg (fun z : TwoCochain (fun s => OneCochain (V s)) => ((z.1.1.1.2.1, z.1.2.1.2.1), (z.2.1.1.2.1, z.2.2.1.2.1))) hp
    obtain ⟨q1,hq1⟩ := (h {0,2} (by simp) ((p.1.1.1.2.1, (p.1.2.1.1.2.1, p.1.2.2.1.2.1)), (p.2.1.1.2.1, (p.2.2.1.1.2.1, p.2.2.2.1.2.1)))).mp h1
    have h2 : d1 (D.left {0,3}) ((p.1.1.1.2.2, (p.1.2.1.1.2.2, p.1.2.2.1.2.2)), (p.2.1.1.2.2, (p.2.2.1.1.2.2, p.2.2.2.1.2.2))) = 0 :=
      congrArg (fun z : TwoCochain (fun s => OneCochain (V s)) => ((z.1.1.1.2.2, z.1.2.1.2.2), (z.2.1.1.2.2, z.2.2.1.2.2))) hp
    obtain ⟨q2,hq2⟩ := (h {0,3} (by simp) ((p.1.1.1.2.2, (p.1.2.1.1.2.2, p.1.2.2.1.2.2)), (p.2.1.1.2.2, (p.2.2.1.1.2.2, p.2.2.2.1.2.2)))).mp h2
    have h3 : d1 (D.left {1,2}) ((p.1.1.2.1, (p.1.2.1.2.1, p.1.2.2.2.1)), (p.2.1.2.1, (p.2.2.1.2.1, p.2.2.2.2.1))) = 0 :=
      congrArg (fun z : TwoCochain (fun s => OneCochain (V s)) => ((z.1.1.2.1, z.1.2.2.1), (z.2.1.2.1, z.2.2.2.1))) hp
    obtain ⟨q3,hq3⟩ := (h {1,2} (by simp) ((p.1.1.2.1, (p.1.2.1.2.1, p.1.2.2.2.1)), (p.2.1.2.1, (p.2.2.1.2.1, p.2.2.2.2.1)))).mp h3
    have h4 : d1 (D.left {1,3}) ((p.1.1.2.2.1, (p.1.2.1.2.2.1, p.1.2.2.2.2.1)), (p.2.1.2.2.1, (p.2.2.1.2.2.1, p.2.2.2.2.2.1))) = 0 :=
      congrArg (fun z : TwoCochain (fun s => OneCochain (V s)) => ((z.1.1.2.2.1, z.1.2.2.2.1), (z.2.1.2.2.1, z.2.2.2.2.1))) hp
    obtain ⟨q4,hq4⟩ := (h {1,3} (by simp) ((p.1.1.2.2.1, (p.1.2.1.2.2.1, p.1.2.2.2.2.1)), (p.2.1.2.2.1, (p.2.2.1.2.2.1, p.2.2.2.2.2.1)))).mp h4
    have h5 : d1 (D.left {2,3}) ((p.1.1.2.2.2, (p.1.2.1.2.2.2, p.1.2.2.2.2.2)), (p.2.1.2.2.2, (p.2.2.1.2.2.2, p.2.2.2.2.2.2))) = 0 :=
      congrArg (fun z : TwoCochain (fun s => OneCochain (V s)) => ((z.1.1.2.2.2, z.1.2.2.2.2), (z.2.1.2.2.2, z.2.2.2.2.2))) hp
    obtain ⟨q5,hq5⟩ := (h {2,3} (by simp) ((p.1.1.2.2.2, (p.1.2.1.2.2.2, p.1.2.2.2.2.2)), (p.2.1.2.2.2, (p.2.2.1.2.2.2, p.2.2.2.2.2.2)))).mp h5
    refine ⟨((((q0.1.1, (q1.1.1, q2.1.1)), (q3.1.1, (q4.1.1, q5.1.1))), ((q0.1.2, (q1.1.2, q2.1.2)), (q3.1.2, (q4.1.2, q5.1.2)))), (((q0.2.1, (q1.2.1, q2.2.1)), (q3.2.1, (q4.2.1, q5.2.1))), ((q0.2.2, (q1.2.2, q2.2.2)), (q3.2.2, (q4.2.2, q5.2.2))))), ?_⟩
    exact (Prod.ext (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,1}) => z.1.1) hq0) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,2}) => z.1.1) hq1) (congrArg (fun z : OneCochain (fun s => V s {0,3}) => z.1.1) hq2))) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,2}) => z.1.1) hq3) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,3}) => z.1.1) hq4) (congrArg (fun z : OneCochain (fun s => V s {2,3}) => z.1.1) hq5)))) (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,1}) => z.1.2.1) hq0) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,2}) => z.1.2.1) hq1) (congrArg (fun z : OneCochain (fun s => V s {0,3}) => z.1.2.1) hq2))) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,2}) => z.1.2.1) hq3) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,3}) => z.1.2.1) hq4) (congrArg (fun z : OneCochain (fun s => V s {2,3}) => z.1.2.1) hq5)))) (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,1}) => z.1.2.2) hq0) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,2}) => z.1.2.2) hq1) (congrArg (fun z : OneCochain (fun s => V s {0,3}) => z.1.2.2) hq2))) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,2}) => z.1.2.2) hq3) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,3}) => z.1.2.2) hq4) (congrArg (fun z : OneCochain (fun s => V s {2,3}) => z.1.2.2) hq5)))))) (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,1}) => z.2.1) hq0) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,2}) => z.2.1) hq1) (congrArg (fun z : OneCochain (fun s => V s {0,3}) => z.2.1) hq2))) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,2}) => z.2.1) hq3) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,3}) => z.2.1) hq4) (congrArg (fun z : OneCochain (fun s => V s {2,3}) => z.2.1) hq5)))) (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,1}) => z.2.2.1) hq0) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,2}) => z.2.2.1) hq1) (congrArg (fun z : OneCochain (fun s => V s {0,3}) => z.2.2.1) hq2))) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,2}) => z.2.2.1) hq3) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,3}) => z.2.2.1) hq4) (congrArg (fun z : OneCochain (fun s => V s {2,3}) => z.2.2.1) hq5)))) (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,1}) => z.2.2.2) hq0) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0,2}) => z.2.2.2) hq1) (congrArg (fun z : OneCochain (fun s => V s {0,3}) => z.2.2.2) hq2))) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,2}) => z.2.2.2) hq3) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {1,3}) => z.2.2.2) hq4) (congrArg (fun z : OneCochain (fun s => V s {2,3}) => z.2.2.2) hq5)))))))
  · rintro ⟨q,rfl⟩
    exact d1_d0 D.row1 q

/-- Exactness of this common-refinement row is the finite product of
actual exactness on its nonempty second-cover overlaps. -/
theorem row2_zero_exact
    (h : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (augmentation (D.left t)) (d0 (D.left t))) :
    Function.Exact (augmentation D.row2) (d0 D.row2) := by
  intro p
  constructor
  · intro hp
    have h0 : d0 (D.left {0,1,2}) ((p.1.1.1.1, p.1.2.1.1), (p.2.1.1.1, p.2.2.1.1)) = 0 :=
      congrArg (fun z : OneCochain (fun s => TwoCochain (V s)) => ((z.1.1.1.1, (z.1.2.1.1.1, z.1.2.2.1.1)), (z.2.1.1.1, (z.2.2.1.1.1, z.2.2.2.1.1)))) hp
    obtain ⟨q0,hq0⟩ := (h {0,1,2} (by simp) ((p.1.1.1.1, p.1.2.1.1), (p.2.1.1.1, p.2.2.1.1))).mp h0
    have h1 : d0 (D.left {0,1,3}) ((p.1.1.1.2, p.1.2.1.2), (p.2.1.1.2, p.2.2.1.2)) = 0 :=
      congrArg (fun z : OneCochain (fun s => TwoCochain (V s)) => ((z.1.1.1.2, (z.1.2.1.1.2, z.1.2.2.1.2)), (z.2.1.1.2, (z.2.2.1.1.2, z.2.2.2.1.2)))) hp
    obtain ⟨q1,hq1⟩ := (h {0,1,3} (by simp) ((p.1.1.1.2, p.1.2.1.2), (p.2.1.1.2, p.2.2.1.2))).mp h1
    have h2 : d0 (D.left {0,2,3}) ((p.1.1.2.1, p.1.2.2.1), (p.2.1.2.1, p.2.2.2.1)) = 0 :=
      congrArg (fun z : OneCochain (fun s => TwoCochain (V s)) => ((z.1.1.2.1, (z.1.2.1.2.1, z.1.2.2.2.1)), (z.2.1.2.1, (z.2.2.1.2.1, z.2.2.2.2.1)))) hp
    obtain ⟨q2,hq2⟩ := (h {0,2,3} (by simp) ((p.1.1.2.1, p.1.2.2.1), (p.2.1.2.1, p.2.2.2.1))).mp h2
    have h3 : d0 (D.left {1,2,3}) ((p.1.1.2.2, p.1.2.2.2), (p.2.1.2.2, p.2.2.2.2)) = 0 :=
      congrArg (fun z : OneCochain (fun s => TwoCochain (V s)) => ((z.1.1.2.2, (z.1.2.1.2.2, z.1.2.2.2.2)), (z.2.1.2.2, (z.2.2.1.2.2, z.2.2.2.2.2)))) hp
    obtain ⟨q3,hq3⟩ := (h {1,2,3} (by simp) ((p.1.1.2.2, p.1.2.2.2), (p.2.1.2.2, p.2.2.2.2))).mp h3
    refine ⟨((q0, q1), (q2, q3)), ?_⟩
    exact (Prod.ext (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,1,2}) => z.1.1) hq0) (congrArg (fun z : ZeroCochain (fun s => V s {0,1,3}) => z.1.1) hq1)) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,2,3}) => z.1.1) hq2) (congrArg (fun z : ZeroCochain (fun s => V s {1,2,3}) => z.1.1) hq3))) (Prod.ext (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,1,2}) => z.1.2) hq0) (congrArg (fun z : ZeroCochain (fun s => V s {0,1,3}) => z.1.2) hq1)) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,2,3}) => z.1.2) hq2) (congrArg (fun z : ZeroCochain (fun s => V s {1,2,3}) => z.1.2) hq3)))) (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,1,2}) => z.2.1) hq0) (congrArg (fun z : ZeroCochain (fun s => V s {0,1,3}) => z.2.1) hq1)) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,2,3}) => z.2.1) hq2) (congrArg (fun z : ZeroCochain (fun s => V s {1,2,3}) => z.2.1) hq3))) (Prod.ext (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,1,2}) => z.2.2) hq0) (congrArg (fun z : ZeroCochain (fun s => V s {0,1,3}) => z.2.2) hq1)) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,2,3}) => z.2.2) hq2) (congrArg (fun z : ZeroCochain (fun s => V s {1,2,3}) => z.2.2) hq3)))))
  · rintro ⟨q,rfl⟩
    exact d0_augmentation D.row2 q

theorem horizontal_augmentation_one_exact
    (h : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Exact (augmentation (D.right s)) (d0 (D.right s))) :
    Function.Exact D.horizontalAugmentation.map1 D.vertical0.map1 := by
  exact exact_prod
    (exact_prod (h {0,1} (by simp))
      (exact_prod (h {0,2} (by simp)) (h {0,3} (by simp))))
    (exact_prod (h {1,2} (by simp))
      (exact_prod (h {1,3} (by simp)) (h {2,3} (by simp))))

theorem vertical_first_exact
    (h : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Exact (d0 (D.right s)) (d1 (D.right s))) :
    Function.Exact D.vertical0.map0 D.vertical1.map0 := by
  exact exact_prod (exact_prod (h {0} (by simp)) (h {1} (by simp)))
    (exact_prod (h {2} (by simp)) (h {3} (by simp)))

theorem horizontal_augmentation_two_injective
    (h : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Injective (augmentation (D.right s))) :
    Function.Injective D.horizontalAugmentation.map2 := by
  exact injective_prod
    (injective_prod (h {0,1,2} (by simp)) (h {0,1,3} (by simp)))
    (injective_prod (h {0,2,3} (by simp)) (h {1,2,3} (by simp)))

/-- A comparison records both actual common-refinement primitives. This
relation ties the second-cover cocycle to the original first-cover one. -/
def SecondDescent
    (c : TwoCochain (fun s => V s ∅)) (d : TwoCochain (V ∅)) : Prop :=
  ∃ x : OneCochain (fun s => ZeroCochain (V s)),
    ∃ y : ZeroCochain (fun s => OneCochain (V s)),
      d1 D.row0 x = D.horizontalAugmentation.map2 c ∧
      d0 D.row1 y = D.vertical0.map1 x ∧
      augmentation D.row2 d = D.vertical1.map0 y

/-- The actual degree-two comparison is constructed from affine
exactness and gluing on the common refinement. -/
theorem exists_second_descent
    (hleft2 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (d1 (D.left t)) (d2 (D.left t)))
    (hleft1 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (d0 (D.left t)) (d1 (D.left t)))
    (hleft0 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (augmentation (D.left t)) (d0 (D.left t)))
    (hleftinj : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Injective (augmentation (D.left t)))
    (c : TwoCochain (fun s => V s ∅)) (hc : d2 (D.left ∅) c = 0) :
    ∃ d : TwoCochain (V ∅), d2 (D.right ∅) d = 0 ∧ D.SecondDescent c d := by
  refine second_descent_exists
    (d2 (D.left ∅)) (d2 (D.right ∅))
    D.horizontalAugmentation.map2 (D.horizontalAugmentation.app Finset.univ)
    (augmentation D.row2) (augmentation (D.left Finset.univ))
    (d1 D.row0) (d2 D.row0) (d0 D.row1) (d1 D.row1) (d0 D.row2)
    D.vertical0.map1 D.vertical0.map2 D.vertical1.map0 D.vertical1.map1
    D.vertical2.map0
    (fun x => (D.horizontalAugmentation.app_d2 x).symm)
    D.vertical2.map0_augmentation
    (fun x => (D.vertical0.map2_d1 x).symm)
    (fun x => (D.vertical1.map1_d0 x).symm)
    ?_ ?_ ?_
    (D.row0_second_exact hleft2) (D.row1_first_exact hleft1)
    (D.row2_zero_exact hleft0) (hleftinj Finset.univ (by simp)) c hc
  · intro x
    exact (Prod.ext (Prod.ext (d0_augmentation (D.right {0,1,2}) x.1.1) (d0_augmentation (D.right {0,1,3}) x.1.2)) (Prod.ext (d0_augmentation (D.right {0,2,3}) x.2.1) (d0_augmentation (D.right {1,2,3}) x.2.2)))
  · intro x
    exact (Prod.ext (Prod.ext (d1_d0 (D.right {0,1}) x.1.1) (Prod.ext (d1_d0 (D.right {0,2}) x.1.2.1) (d1_d0 (D.right {0,3}) x.1.2.2))) (Prod.ext (d1_d0 (D.right {1,2}) x.2.1) (Prod.ext (d1_d0 (D.right {1,3}) x.2.2.1) (d1_d0 (D.right {2,3}) x.2.2.2))))
  · intro x
    exact (Prod.ext (Prod.ext (d2_d1 (D.right {0}) x.1.1) (d2_d1 (D.right {1}) x.1.2)) (Prod.ext (d2_d1 (D.right {2}) x.2.1) (d2_d1 (D.right {3}) x.2.2)))

/-- Vanishing after actual common-refinement descent reflects vanishing
of the original cocycle. No global second-cohomology comparison is a premise. -/
theorem SecondDescent.reflects_boundary
    (hright1 : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Exact (d0 (D.right s)) (d1 (D.right s)))
    (hright0 : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Exact (augmentation (D.right s)) (d0 (D.right s)))
    (hrightinj : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Injective (augmentation (D.right s)))
    {c : TwoCochain (fun s => V s ∅)} {d : TwoCochain (V ∅)}
    (hcd : D.SecondDescent c d)
    (hd : ∃ b, d1 (D.right ∅) b = d) : ∃ a, d1 (D.left ∅) a = c := by
  obtain ⟨x,y,hx,hy,hd'⟩ := hcd
  exact second_descent_reflects_boundary
    (d1 (D.left ∅)) (d1 (D.right ∅))
    D.horizontalAugmentation.map1 D.horizontalAugmentation.map2
    (augmentation D.row1) (augmentation D.row2)
    (d0 D.row0) (d1 D.row0) (d0 D.row1)
    D.vertical0.map0 D.vertical0.map1 D.vertical1.map0
    (fun a => (D.horizontalAugmentation.map2_d1 a).symm)
    D.vertical1.map0_augmentation D.vertical0.map1_d0
    (d0_augmentation D.row1) (d1_d0 D.row0)
    (D.vertical_first_exact hright1) (D.horizontal_augmentation_one_exact hright0)
    (D.horizontal_augmentation_two_injective hrightinj) c d x y hx hy hd' hd

/-- A nonzero actual cocycle remains nonzero in the second-cover quotient,
with explicit primitive equations connecting its representative to the original. -/
theorem exists_nonzero_second_descent
    (hleft2 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (d1 (D.left t)) (d2 (D.left t)))
    (hleft1 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (d0 (D.left t)) (d1 (D.left t)))
    (hleft0 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (augmentation (D.left t)) (d0 (D.left t)))
    (hleftinj : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Injective (augmentation (D.left t)))
    (hright1 : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Exact (d0 (D.right s)) (d1 (D.right s)))
    (hright0 : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Exact (augmentation (D.right s)) (d0 (D.right s)))
    (hrightinj : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Injective (augmentation (D.right s)))
    (c : TwoCocycles (D.left ∅)) (hc : classOf (D.left ∅) c ≠ 0) :
    ∃ d : TwoCocycles (D.right ∅), D.SecondDescent c.val d.val ∧
      classOf (D.right ∅) d ≠ 0 := by
  obtain ⟨d,hd,hcd⟩ := D.exists_second_descent hleft2 hleft1 hleft0 hleftinj c.val c.property
  refine ⟨⟨d,hd⟩,hcd,?_⟩
  intro hz
  apply hc
  apply (classOf_eq_zero_iff (D.left ∅) c).mpr
  exact SecondDescent.reflects_boundary D hright1 hright0 hrightinj hcd
    ((classOf_eq_zero_iff (D.right ∅) ⟨d,hd⟩).mp hz)

end CycleQ2GeometricFourOpenCech.BiSystem

namespace CycleQ2GeometricFourOpenCech.SystemMorphism

variable {R : Type*} [CommRing R]
variable {V W : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]
variable [∀ s, AddCommGroup (W s)] [∀ s, Module R (W s)]
variable {D : RestrictionSystem R V} {E : RestrictionSystem R W}

/-- The actual cochain morphism induces the corresponding map on cocycles. -/
def mapCycle (f : SystemMorphism D E) : TwoCocycles D →ₗ[R] TwoCocycles E where
  toFun c := ⟨f.map2 c.val, by
    change d2 E (f.map2 c.val) = 0
    rw [← f.app_d2, c.property, map_zero]⟩
  map_add' c d := Subtype.ext (map_add f.map2 c.val d.val)
  map_smul' a c := Subtype.ext (map_smul f.map2 a c.val)

theorem mapCycle_bijective (f : SystemMorphism D E)
    (hf : ∀ s, Function.Bijective (f.app s)) : Function.Bijective f.mapCycle := by
  constructor
  · intro c d h
    apply Subtype.ext
    exact (f.map2_bijective hf).1 (congrArg Subtype.val h)
  · intro c
    obtain ⟨p,hp⟩ := (f.map2_bijective hf).2 c.val
    have hz : d2 D p = 0 := by
      apply (hf Finset.univ).1
      rw [map_zero, f.app_d2, hp]
      exact c.property
    exact ⟨⟨p,hz⟩,Subtype.ext hp⟩

/-- Pointwise bijective actual restrictions preserve and reflect the
zero cohomology class, by their explicit maps on one-cochain primitives. -/
theorem classOf_mapCycle_eq_zero_iff (f : SystemMorphism D E)
    (hf : ∀ s, Function.Bijective (f.app s)) (c : TwoCocycles D) :
    classOf E (f.mapCycle c) = 0 ↔ classOf D c = 0 := by
  rw [classOf_eq_zero_iff, classOf_eq_zero_iff]
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨p,rfl⟩ := (f.map1_bijective hf).2 q
    refine ⟨p,(f.map2_bijective hf).1 ?_⟩
    rw [f.map2_d1]
    exact hq
  · rintro ⟨p,hp⟩
    refine ⟨f.map1 p, ?_⟩
    rw [← f.map2_d1, hp]
    rfl

end CycleQ2GeometricFourOpenCech.SystemMorphism

namespace CycleQ2GeometricFourOpenCech.BiSystem

variable {R : Type*} [CommRing R]
variable {V : Finset (Fin 4) → Finset (Fin 4) → Type*}
variable [∀ s t, AddCommGroup (V s t)] [∀ s t, Module R (V s t)]
variable (D : CycleQ2GeometricFourOpenCech.BiSystem (R := R) V)

theorem SecondDescent.smul (a : R)
    {c : TwoCochain (fun s => V s ∅)} {d : TwoCochain (V ∅)}
    (hcd : D.SecondDescent c d) : D.SecondDescent (a • c) (a • d) := by
  obtain ⟨x,y,hx,hy,hd⟩ := hcd
  refine ⟨a • x,a • y,?_,?_,?_⟩
  · simp only [map_smul, hx]
  · simp only [map_smul, hy]
  · simp only [map_smul, hd]

end CycleQ2GeometricFourOpenCech.BiSystem

namespace CycleQ2GeometricLocalizedCech

open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

theorem mixedLeft_second_exact (a b : Fin 4 → R)
    (hab : (Ideal.span (Set.range b)).radical ≤ (Ideal.span (Set.range a)).radical)
    (t : Finset (Fin 4)) (ht : t.Nonempty) :
    Function.Exact (d1 ((mixedSystem M a b).left t))
      (d2 ((mixedSystem M a b).left t)) :=
  baseChanged_affine_second_exact M (RingAt b t) a
    (localized_cover_span_top a b hab t ht)

theorem mixedRight_first_exact (a b : Fin 4 → R)
    (hab : (Ideal.span (Set.range a)).radical ≤ (Ideal.span (Set.range b)).radical)
    (s : Finset (Fin 4)) (hs : s.Nonempty) :
    Function.Exact (d0 ((mixedSystem M a b).right s))
      (d1 ((mixedSystem M a b).right s)) := by
  let f := mixedRightSwap M a b s
  have hf (t : Finset (Fin 4)) : Function.Bijective (f.app t) :=
    (TensorProduct.leftComm R (RingAt b t) (RingAt a s) M).bijective
  have h := baseChanged_affine_exact M (RingAt a s) b
    (localized_cover_span_top b a hab s hs)
  exact (f.first_exact_iff_of_bijective hf).mpr h.2.2

/-- The original two cocycles are related through the actual principal
common refinement and its canonical empty-localization comparisons. -/
def PrincipalSecondDescent (a b : Fin 4 → R)
    (c : TwoCocycles (moduleSystem M a)) (d : TwoCocycles (moduleSystem M b)) : Prop :=
  ∃ c' : TwoCocycles ((mixedSystem M a b).left ∅),
    ∃ d' : TwoCocycles ((mixedSystem M a b).right ∅),
      (mixedLeftEmpty M a b).mapCycle c' = c ∧
      (mixedRightEmpty M a b).mapCycle d' = d ∧
      (mixedSystem M a b).SecondDescent c'.val d'.val

theorem PrincipalSecondDescent.smul (a b : Fin 4 → R) (z : R)
    {c : TwoCocycles (moduleSystem M a)} {d : TwoCocycles (moduleSystem M b)}
    (hcd : PrincipalSecondDescent M a b c d) :
    PrincipalSecondDescent M a b (z • c) (z • d) := by
  obtain ⟨c',d',hc',hd',hcd'⟩ := hcd
  refine ⟨z • c',z • d',?_,?_,?_⟩
  · simp only [map_smul, hc']
  · simp only [map_smul, hd']
  · exact BiSystem.SecondDescent.smul (mixedSystem M a b) z hcd'

/-- Every actual representative related by the common-refinement
equations detects the original zero class, including after multiplication. -/
theorem PrincipalSecondDescent.reflects_class_zero (a b : Fin 4 → R)
    (hab : (Ideal.span (Set.range a)).radical = (Ideal.span (Set.range b)).radical)
    {c : TwoCocycles (moduleSystem M a)} {d : TwoCocycles (moduleSystem M b)}
    (hcd : PrincipalSecondDescent M a b c d) (hd : classOf (moduleSystem M b) d = 0) :
    classOf (moduleSystem M a) c = 0 := by
  obtain ⟨c',d',hc',hd',hcd'⟩ := hcd
  let D := mixedSystem M a b
  let fL := mixedLeftEmpty M a b
  let fR := mixedRightEmpty M a b
  have hL (s : Finset (Fin 4)) : Function.Bijective (fL.app s) :=
    (emptyModuleEquiv (ModuleAt M a s) b).bijective
  have hR (t : Finset (Fin 4)) : Function.Bijective (fR.app t) :=
    (TensorProduct.congr (LinearEquiv.refl R (RingAt b t))
      (emptyModuleEquiv M a)).bijective
  have hzR : classOf (D.right ∅) d' = 0 := by
    apply (fR.classOf_mapCycle_eq_zero_iff hR d').mp
    change classOf (moduleSystem M b) (fR.mapCycle d') = 0
    rw [hd']
    exact hd
  have hbound := BiSystem.SecondDescent.reflects_boundary D
    (fun s hs => mixedRight_first_exact M a b hab.le s hs)
    (fun s hs => (mixedRight_gluing M a b hab.le s hs).1)
    (fun s hs => (mixedRight_gluing M a b hab.le s hs).2) hcd'
    ((classOf_eq_zero_iff (D.right ∅) d').mp hzR)
  rw [← hc']
  apply (fL.classOf_mapCycle_eq_zero_iff hL c').mpr
  exact (classOf_eq_zero_iff (D.left ∅) c').mpr hbound

/-- An actual nonzero degree-two class transfers to the other principal
cover of the same open scheme. The conclusion retains the precise
common-refinement equations connecting the original representatives. -/
theorem exists_nonzero_second_descent_of_radical_eq (a b : Fin 4 → R)
    (hab : (Ideal.span (Set.range a)).radical = (Ideal.span (Set.range b)).radical)
    (c : TwoCocycles (moduleSystem M a)) (hc : classOf (moduleSystem M a) c ≠ 0) :
    ∃ d : TwoCocycles (moduleSystem M b), PrincipalSecondDescent M a b c d ∧
      classOf (moduleSystem M b) d ≠ 0 := by
  let D := mixedSystem M a b
  let fL := mixedLeftEmpty M a b
  let fR := mixedRightEmpty M a b
  have hL (s : Finset (Fin 4)) : Function.Bijective (fL.app s) :=
    (emptyModuleEquiv (ModuleAt M a s) b).bijective
  have hR (t : Finset (Fin 4)) : Function.Bijective (fR.app t) :=
    (TensorProduct.congr (LinearEquiv.refl R (RingAt b t))
      (emptyModuleEquiv M a)).bijective
  obtain ⟨c',hc'⟩ := (fL.mapCycle_bijective hL).2 c
  have hn : classOf (D.left ∅) c' ≠ 0 := by
    intro hz
    apply hc
    rw [← hc']
    exact (fL.classOf_mapCycle_eq_zero_iff hL c').mpr hz
  obtain ⟨d',hcd,hd'⟩ := D.exists_nonzero_second_descent
    (fun t ht => mixedLeft_second_exact M a b hab.ge t ht)
    (fun t ht => (mixedLeft_exact M a b hab.ge t ht).2.2)
    (fun t ht => (mixedLeft_exact M a b hab.ge t ht).1)
    (fun t ht => (mixedLeft_exact M a b hab.ge t ht).2.1)
    (fun s hs => mixedRight_first_exact M a b hab.le s hs)
    (fun s hs => (mixedRight_gluing M a b hab.le s hs).1)
    (fun s hs => (mixedRight_gluing M a b hab.le s hs).2) c' hn
  refine ⟨fR.mapCycle d', ⟨c',d',hc',rfl,hcd⟩, ?_⟩
  intro hz
  exact hd' ((fR.classOf_mapCycle_eq_zero_iff hR d').mp hz)

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricLocalizedCech

open scoped TensorProduct
open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]

/-- The actual scalar localization rings with their actual restriction maps. -/
def scalarSystem (a : Fin 4 → R) : RestrictionSystem R (RingAt a) where
  res h := (ringRestriction a h).toLinearMap
  res_id s := congrArg AlgHom.toLinearMap (ringRestriction_self a s)
  res_comp hs ht := by
    apply LinearMap.ext
    intro z
    exact ringRestriction_comp a hs ht z

/-- Tensoring the scalar module with a localization is identified with that
same localization by multiplication, on every overlap and every restriction. -/
def scalarTensorMorphism (a : Fin 4 → R) :
    SystemMorphism (moduleSystem R a) (scalarSystem a) where
  app s := ((TensorProduct.AlgebraTensorModule.rid R (RingAt a s) (RingAt a s)).restrictScalars R).toLinearMap
  naturality {s t} h := by
    apply LinearMap.ext
    intro p
    induction p using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add p q hp hq => simp only [map_add, hp, hq]
    | tmul z x =>
      change x • ringRestriction a h z = ringRestriction a h (x • z)
      exact ((ringRestriction a h).toLinearMap.map_smul x z).symm

@[simp] theorem scalarTensorMorphism_tmul (a : Fin 4 → R) (s : Finset (Fin 4))
    (z : RingAt a s) (x : R) :
    (scalarTensorMorphism a).app s (z ⊗ₜ[R] x) = x • z := rfl

theorem scalarTensorMorphism_bijective (a : Fin 4 → R) (s : Finset (Fin 4)) :
    Function.Bijective ((scalarTensorMorphism a).app s) :=
  (TensorProduct.AlgebraTensorModule.rid R (RingAt a s) (RingAt a s)).bijective

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricCartierCech

open scoped TensorProduct
open CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricFourOpenCech
  CycleQ2GeometricLocalizedCech

/-- Both named surface restrictions are the unique map between the same
actual localizations extending the identity on the original surface ring. -/
theorem scalar_ringRestriction_eq_coverRestriction (r θ : ℂ)
    {s t : Finset (Fin 4)} (h : s ⊆ t) :
    ringRestriction (coverElement r θ) h = coverRestriction r θ h := by
  apply IsLocalization.algHom_ext
    (Submonoid.powers
      (CycleQ2GeometricLocalizedCech.coverProduct (coverElement r θ) s))
  ext

/-- The tensor localization comparison lands in the original scalar surface
system used to define the fixed Cartier cocycle. -/
def surfaceTensorMorphism (r θ : ℂ) :
    SystemMorphism (moduleSystem (SurfaceRing r θ) (coverElement r θ))
      (surfaceSystem r θ) where
  app s := (scalarTensorMorphism (coverElement r θ)).app s
  naturality {s t} h := by
    apply LinearMap.ext
    intro p
    change (scalarTensorMorphism (coverElement r θ)).app t
        (moduleRestriction (SurfaceRing r θ) (coverElement r θ) h p) =
      coverRestriction r θ h ((scalarTensorMorphism (coverElement r θ)).app s p)
    rw [← scalar_ringRestriction_eq_coverRestriction r θ h]
    exact (scalarTensorMorphism (coverElement r θ)).app_res h p

@[simp] theorem surfaceTensorMorphism_tmul (r θ : ℂ) (s : Finset (Fin 4))
    (z : CoverLocal r θ s) (x : SurfaceRing r θ) :
    (surfaceTensorMorphism r θ).app s (z ⊗ₜ[SurfaceRing r θ] x) = x • z := rfl

theorem surfaceTensorMorphism_bijective (r θ : ℂ) (s : Finset (Fin 4)) :
    Function.Bijective ((surfaceTensorMorphism r θ).app s) :=
  scalarTensorMorphism_bijective (coverElement r θ) s

/-- The genuine scalar rings on the three coordinate opens, with an empty
fourth open to retain the same four-open Čech complex. -/
abbrev coordinateScalarSystem (r : ℂ) := scalarSystem (coordinateCover r)

abbrev ActualCoordinateSecondCech (r : ℂ) := SecondCech (coordinateScalarSystem r)

/-- Exact cochain data relating an original surface cocycle to a coordinate
cocycle. Both scalar-to-tensor identifications are canonical multiplication
maps, and the middle witness is the actual principal common refinement. -/
def CartierCoordinateDescent (r : ℂ) (c : TwoCocycles (surfaceSystem r 1))
    (d : TwoCocycles (coordinateScalarSystem r)) : Prop :=
  ∃ c' : TwoCocycles (moduleSystem (SurfaceRing r 1) (coverElement r 1)),
    ∃ d' : TwoCocycles (moduleSystem (SurfaceRing r 1) (coordinateCover r)),
      (surfaceTensorMorphism r 1).mapCycle c' = c ∧
      PrincipalSecondDescent (SurfaceRing r 1) (coverElement r 1) (coordinateCover r) c' d' ∧
      (scalarTensorMorphism (coordinateCover r)).mapCycle d' = d

/-- The exact same common-refinement equations remain valid after
multiplication by an element of the original surface ring. -/
theorem CartierCoordinateDescent.smul (r : ℂ) (z : SurfaceRing r 1)
    {c : TwoCocycles (surfaceSystem r 1)} {d : TwoCocycles (coordinateScalarSystem r)}
    (hcd : CartierCoordinateDescent r c d) :
    CartierCoordinateDescent r (z • c) (z • d) := by
  obtain ⟨c', d', hc', hmiddle, hd'⟩ := hcd
  refine ⟨z • c', z • d', ?_, ?_, ?_⟩
  · simp only [map_smul, hc']
  · exact PrincipalSecondDescent.smul (SurfaceRing r 1)
      (coverElement r 1) (coordinateCover r) z hmiddle
  · simp only [map_smul, hd']

/-- Every coordinate cocycle related by the actual descent equations
detects the zero class of the original scalar surface cocycle. -/
theorem CartierCoordinateDescent.reflects_class_zero (r : ℂ) (hr : r ≠ 0)
    {c : TwoCocycles (surfaceSystem r 1)} {d : TwoCocycles (coordinateScalarSystem r)}
    (hcd : CartierCoordinateDescent r c d)
    (hd : classOf (coordinateScalarSystem r) d = 0) :
    classOf (surfaceSystem r 1) c = 0 := by
  obtain ⟨c', d', hc', hmiddle, hd'⟩ := hcd
  have hz : classOf (moduleSystem (SurfaceRing r 1) (coordinateCover r)) d' = 0 := by
    apply ((scalarTensorMorphism (coordinateCover r)).classOf_mapCycle_eq_zero_iff
      (scalarTensorMorphism_bijective (coordinateCover r)) d').mp
    rw [hd']
    exact hd
  have hab : (Ideal.span (Set.range (coverElement r 1))).radical =
      (Ideal.span (Set.range (coordinateCover r))).radical := by
    rw [coordinateCover_span]
    exact cover_radical_eq_coordinate_radical r 1 hr one_ne_zero
  have hc := PrincipalSecondDescent.reflects_class_zero (SurfaceRing r 1)
    (coverElement r 1) (coordinateCover r) hab hmiddle hz
  rw [← hc']
  exact ((surfaceTensorMorphism r 1).classOf_mapCycle_eq_zero_iff
    (surfaceTensorMorphism_bijective r 1) c').mpr hc

/-- The proved actual coordinate cover carries the same nonzero class as an
original nonzero scalar surface cocycle, with its representative relation
retained in the conclusion. -/
theorem exists_nonzero_coordinate_descent (r : ℂ) (hr : r ≠ 0)
    (c : TwoCocycles (surfaceSystem r 1)) (hc : classOf (surfaceSystem r 1) c ≠ 0) :
    ∃ d : TwoCocycles (coordinateScalarSystem r), CartierCoordinateDescent r c d ∧
      classOf (coordinateScalarSystem r) d ≠ 0 := by
  let f := surfaceTensorMorphism r 1
  have hf (s : Finset (Fin 4)) : Function.Bijective (f.app s) :=
    surfaceTensorMorphism_bijective r 1 s
  obtain ⟨c', hc'⟩ := (f.mapCycle_bijective hf).2 c
  have hn : classOf (moduleSystem (SurfaceRing r 1) (coverElement r 1)) c' ≠ 0 := by
    intro hz
    apply hc
    rw [← hc']
    exact (f.classOf_mapCycle_eq_zero_iff hf c').mpr hz
  have hab : (Ideal.span (Set.range (coverElement r 1))).radical =
      (Ideal.span (Set.range (coordinateCover r))).radical := by
    rw [coordinateCover_span]
    exact cover_radical_eq_coordinate_radical r 1 hr one_ne_zero
  obtain ⟨d', hdesc, hnd⟩ := exists_nonzero_second_descent_of_radical_eq (SurfaceRing r 1)
    (coverElement r 1) (coordinateCover r) hab c' hn
  refine ⟨(scalarTensorMorphism (coordinateCover r)).mapCycle d',
    ⟨c', d', hc', hdesc, rfl⟩, ?_⟩
  intro hz
  exact hnd (((scalarTensorMorphism (coordinateCover r)).classOf_mapCycle_eq_zero_iff
    (scalarTensorMorphism_bijective (coordinateCover r)) d').mp hz)

/-- The fixed literal ambient Cartier cocycle gives a nonzero actual scalar
coordinate-cover class. No nonzero vector or comparison premise is supplied:
the conclusion records the exact descent from that original cocycle. -/
theorem literal_cartier_coordinate_descent_nonzero :
    ∃ d : TwoCocycles (coordinateScalarSystem 57),
      CartierCoordinateDescent 57 (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0) d ∧
      classOf (coordinateScalarSystem 57) d ≠ 0 :=
  exists_nonzero_coordinate_descent 57 (by norm_num)
    (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0) literal_cartierClass_ne_zero

end CycleQ2GeometricCartierCech

namespace CycleQ2GeometricCartierCech

open MvPolynomial CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricFourOpenCech
  CycleQ2ActualNormalCech CycleQ2NormalConnecting CycleQ2SeedTrace
  CycleQ2GeometricCanonicalCechBoundary

theorem boundary012_mul_inputs (r θ : ℂ) (σ A L : P) :
    boundary012 r θ (σ * A) (σ * L) =
      surfaceQuotient r θ σ • boundary012 r θ A L := by
  calc
    _ = algebraMap (SurfaceRing r θ) (CoverLocal r θ {0,1,2})
        (surfaceQuotient r θ σ) * boundary012 r θ A L := by
      rw [boundary012_formula, boundary012_formula]
      change coverPolyMap r θ {0,1,2} (thetaK θ * (σ * L) - σ * A) * _ * _ =
        coverPolyMap r θ {0,1,2} σ *
          (coverPolyMap r θ {0,1,2} (thetaK θ * L - A) * _ * _)
      simp only [map_mul, map_sub]
      ring
    _ = _ := (Algebra.smul_def (surfaceQuotient r θ σ) (boundary012 r θ A L)).symm

theorem boundary013_mul_inputs (r θ : ℂ) (σ A L : P) :
    boundary013 r θ (σ * A) (σ * L) =
      surfaceQuotient r θ σ • boundary013 r θ A L := by
  calc
    _ = algebraMap (SurfaceRing r θ) (CoverLocal r θ {0,1,3})
        (surfaceQuotient r θ σ) * boundary013 r θ A L := by
      rw [boundary013_formula, boundary013_formula]
      change -coverPolyMap r θ {0,1,3} (thetaK θ * (σ * L) - σ * A) * _ * _ =
        coverPolyMap r θ {0,1,3} σ *
          (-coverPolyMap r θ {0,1,3} (thetaK θ * L - A) * _ * _)
      simp only [map_mul, map_sub]
      ring
    _ = _ := (Algebra.smul_def (surfaceQuotient r θ σ) (boundary013 r θ A L)).symm

/-- Multiplication of the original polynomial inputs is multiplication of
the same actual Cartier cocycle in every scalar localization. -/
theorem cartierCycle_mul_inputs (r θ : ℂ) (σ A L : P) :
    cartierCycle r θ (σ * A) (σ * L) =
      surfaceQuotient r θ σ • cartierCycle r θ A L := by
  apply Subtype.ext
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · exact boundary012_mul_inputs r θ σ A L
  · exact boundary013_mul_inputs r θ σ A L
  · exact (smul_zero _).symm
  · exact (smul_zero _).symm

theorem cartierClass_mul_inputs (r θ : ℂ) (σ A L : P) :
    cartierClass r θ (σ * A) (σ * L) =
      surfaceQuotient r θ σ • cartierClass r θ A L := by
  change classOf (surfaceSystem r θ) (cartierCycle r θ (σ * A) (σ * L)) =
    surfaceQuotient r θ σ • classOf (surfaceSystem r θ) (cartierCycle r θ A L)
  rw [cartierCycle_mul_inputs, map_smul]

/-- Multiplying the actual ambient inputs and pairing with one gives
exactly the original relative-normal coefficient paired with σ. -/
theorem pairedRelativeNormalCoefficient_mul_inputs (r θ : ℂ) (σ A L : P) :
    pairedRelativeNormalCoefficient r θ (σ * A) (σ * L) 1 =
      pairedRelativeNormalCoefficient r θ A L (substitute σ) := by
  rw [pairedRelativeNormalCoefficient_eq, pairedRelativeNormalCoefficient_eq]
  simp only [map_one, mul_one]
  change normalOverlapCoefficient r θ (σ * A) (σ * L) =
    normalOverlapCoefficient r θ A L * overlapAmbient r θ σ
  simp only [normalOverlapCoefficient, overlapCoefficient, map_mul]
  ring

theorem scalarRelativeNormalCechClass_mul_inputs (r θ : ℂ) (σ A L : P) :
    scalarRelativeNormalCechClass r θ (σ * A) (σ * L) 1 =
      scalarRelativeNormalCechClass r θ A L (substitute σ) := by
  unfold scalarRelativeNormalCechClass
  rw [pairedRelativeNormalCoefficient_mul_inputs]

/-- The cubic used in the actual nonzero paired-normal calculation. -/
def detectorCubic : P := X 0 ^ 3

theorem substitute_detectorCubic : substitute detectorCubic = X 0 ^ 3 := by
  simp [detectorCubic, substitute]

theorem literal_cubic_normalClass_ne_zero :
    connectingClass 57 1 (detectorCubic * derivativeA) 0 ≠ 0 := by
  intro hz
  have h := scalarPair_zero_of_normalClass_zero 57 1 (detectorCubic * derivativeA) 0 1 hz
  have he : scalarRelativeNormalCechClass 57 1 (detectorCubic * derivativeA) 0 1 =
      scalarRelativeNormalCechClass 57 1 derivativeA 0 (X 0 ^ 3) := by
    simpa only [mul_zero, substitute_detectorCubic] using
      scalarRelativeNormalCechClass_mul_inputs 57 1 detectorCubic derivativeA 0
  rw [he] at h
  exact incidenceScalarAmbientNormalCechClass_ne_zero
    (by simpa only [incidenceAmbientCubic] using h)

/-- The exact cubic multiple of the fixed actual Cartier surface class is
nonzero. No character projection or graded identification is asserted here. -/
theorem literal_cubic_cartierClass_ne_zero :
    surfaceQuotient 57 1 detectorCubic • cartierClass 57 1 derivativeA 0 ≠ 0 := by
  intro hz
  have hz' : cartierClass 57 1 (detectorCubic * derivativeA) 0 = 0 := by
    have hm := cartierClass_mul_inputs 57 1 detectorCubic derivativeA 0
    simpa only [mul_zero, hz] using hm
  exact literal_cubic_normalClass_ne_zero
    (normalClass_zero_of_cartierClass_zero 57 (by norm_num)
      (detectorCubic * derivativeA) 0 hz')

/-- Every coordinate representative of the original Cartier cocycle has
the same nonzero cubic multiple, using the same scaled descent equations. -/
theorem literal_descent_cubic_ne_zero (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d) :
    surfaceQuotient 57 1 detectorCubic • classOf (coordinateScalarSystem 57) d ≠ 0 := by
  intro hz
  have hd : classOf (coordinateScalarSystem 57)
      (surfaceQuotient 57 1 detectorCubic • d) = 0 := by
    rw [map_smul]
    exact hz
  have hc := CartierCoordinateDescent.reflects_class_zero 57 (by norm_num)
    (CartierCoordinateDescent.smul 57 (surfaceQuotient 57 1 detectorCubic) hcd) hd
  apply literal_cubic_cartierClass_ne_zero
  change surfaceQuotient 57 1 detectorCubic •
    classOf (surfaceSystem 57 1) (cartierCycle 57 1 derivativeA 0) = 0
  simpa only [map_smul] using hc

/-- One actual coordinate descendant of the fixed Cartier cocycle, whose
class and cubic multiple are both nonzero. The descendant is not replaced
when the cubic test is applied. -/
theorem literal_cartier_coordinate_cubic_nonzero :
    ∃ d : TwoCocycles (coordinateScalarSystem 57),
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d ∧
      classOf (coordinateScalarSystem 57) d ≠ 0 ∧
      surfaceQuotient 57 1 detectorCubic • classOf (coordinateScalarSystem 57) d ≠ 0 := by
  obtain ⟨d, hcd, hd⟩ := literal_cartier_coordinate_descent_nonzero
  exact ⟨d, hcd, hd, literal_descent_cubic_ne_zero d hcd⟩

end CycleQ2GeometricCartierCech

namespace CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]

/-- With an empty fourth open, the original degree-two class vanishes
exactly when its actual first triple component is a three-open boundary. -/
theorem classOf_eq_zero_iff_three_boundary (D : RestrictionSystem R V)
    (h3 : ∀ s : Finset (Fin 4), 3 ∈ s → Subsingleton (V s))
    (c : TwoCocycles D) :
    classOf D c = 0 ↔ ∃ (p01 : V {0,1}) (p02 : V {0,2}) (p12 : V {1,2}),
      D.res (show ({1,2} : Finset (Fin 4)) ⊆ {0,1,2} by decide) p12 -
        D.res (show ({0,2} : Finset (Fin 4)) ⊆ {0,1,2} by decide) p02 +
        D.res (show ({0,1} : Finset (Fin 4)) ⊆ {0,1,2} by decide) p01 = c.val.1.1 := by
  rw [classOf_eq_zero_iff]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p.1.1,p.1.2.1,p.2.1,
      congrArg (fun z : TwoCochain V => z.1.1) hp⟩
  · rintro ⟨p01,p02,p12,hp⟩
    refine ⟨((p01,p02,0),(p12,0,0)),Prod.ext (Prod.ext hp ?_) (Prod.ext ?_ ?_)⟩
    · letI := h3 {0,1,3} (by decide)
      exact Subsingleton.elim _ _
    · letI := h3 {0,2,3} (by decide)
      exact Subsingleton.elim _ _
    · letI := h3 {1,2,3} (by decide)
      exact Subsingleton.elim _ _

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricLaurentTop

open CycleQ2SeedCechThreeOpen

variable {R : Type*} [CommRing R]

/-- The three disjoint groups of terms that can be removed by pair-open
boundaries. The remaining terms have all three exponents negative. -/
def pairPart01 (p : Laurent (R := R)) : Laurent (R := R) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.filter (fun e => 0 ≤ e 2))

def pairPart02 (p : Laurent (R := R)) : Laurent (R := R) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.filter (fun e => e 2 < 0 ∧ 0 ≤ e 1))

def pairPart12 (p : Laurent (R := R)) : Laurent (R := R) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.filter (fun e => e 2 < 0 ∧ e 1 < 0))

@[simp] theorem pairPart01_coeff (p : Laurent (R := R)) (e : LaurentExponent) :
    (pairPart01 p).coeff e = if 0 ≤ e 2 then p.coeff e else 0 := rfl

@[simp] theorem pairPart02_coeff (p : Laurent (R := R)) (e : LaurentExponent) :
    (pairPart02 p).coeff e = if e 2 < 0 ∧ 0 ≤ e 1 then p.coeff e else 0 := rfl

@[simp] theorem pairPart12_coeff (p : Laurent (R := R)) (e : LaurentExponent) :
    (pairPart12 p).coeff e = if e 2 < 0 ∧ e 1 < 0 then p.coeff e else 0 := rfl

theorem pairPart01_hasPoles (p : Laurent (R := R)) : HasPoles {0,1} (pairPart01 p) := by
  intro e i hi hneg
  fin_cases i
  · simp at hi
  · simp at hi
  · change e 2 < 0 at hneg
    simp [not_le.mpr hneg]

theorem pairPart02_hasPoles (p : Laurent (R := R)) : HasPoles {0,2} (pairPart02 p) := by
  intro e i hi hneg
  fin_cases i
  · simp at hi
  · change e 1 < 0 at hneg
    simp [not_le.mpr hneg]
  · simp at hi

theorem pairPart12_hasPoles (p : Laurent (R := R))
    (hp : ∀ e, (∀ i, e i < 0) → p.coeff e = 0) : HasPoles {1,2} (pairPart12 p) := by
  intro e i hi hneg
  fin_cases i
  · simp only [pairPart12_coeff]
    split
    next h =>
      apply hp e
      intro j
      fin_cases j
      · exact hneg
      · exact h.2
      · exact h.1
    next h => rfl
  · simp at hi
  · simp at hi

theorem pairParts_sum (p : Laurent (R := R)) :
    pairPart01 p + pairPart02 p + pairPart12 p = p := by
  ext e
  by_cases h2 : 0 ≤ e 2 <;> by_cases h1 : 0 ≤ e 1 <;>
    simp [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h2, h1,
      lt_of_not_ge, not_lt_of_ge]

/-- The ungraded Laurent top quotient is detected precisely by the
all-negative coefficients. Both directions retain arbitrary pole orders. -/
theorem all_negative_zero_iff_pair_boundary (p : Laurent (R := R)) :
    (∀ e, (∀ i, e i < 0) → p.coeff e = 0) ↔
      ∃ p01 p02 p12 : Laurent (R := R),
        HasPoles {0,1} p01 ∧ HasPoles {0,2} p02 ∧ HasPoles {1,2} p12 ∧
        p12 - p02 + p01 = p := by
  constructor
  · intro hp
    refine ⟨pairPart01 p,-pairPart02 p,pairPart12 p,
      pairPart01_hasPoles p,?_,pairPart12_hasPoles p hp,?_⟩
    · intro e i hi hneg
      simpa only [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, neg_eq_zero] using
        pairPart02_hasPoles p e i hi hneg
    · calc
        _ = pairPart01 p + pairPart02 p + pairPart12 p := by abel
        _ = p := pairParts_sum p
  · rintro ⟨p01,p02,p12,h01,h02,h12,rfl⟩ e he
    simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
      Finsupp.add_apply, Finsupp.sub_apply,
      h12 e 0 (by decide) (he 0), h02 e 1 (by decide) (he 1),
      h01 e 2 (by decide) (he 2), sub_self, add_zero]

end CycleQ2GeometricLaurentTop

namespace CycleQ2GeometricLaurentTop

open CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2GeometricSurfaceCoordinates

theorem seed_coordinates_mul_base (r : ℂ) (s : Finset (Fin 3))
    (p : SeedLocal ℂ r Complex.I s) (c : Base ℂ) (ab : ShiftIndex) :
    localizedCoordinates ℂ r Complex.I s
      (p * algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I s)
        (algebraMap (Base ℂ) (SeedRing r Complex.I) c)) ab =
      baseToLaurent ℂ c * localizedCoordinates ℂ r Complex.I s p ab := by
  rw [← IsScalarTower.algebraMap_apply (Base ℂ) (SeedRing r Complex.I)
      (SeedLocal ℂ r Complex.I s) c,
    IsScalarTower.algebraMap_apply (Base ℂ) (coordinateLocalization ℂ s)
      (SeedLocal ℂ r Complex.I s) c,
    mul_comm p, ← Algebra.smul_def]
  rw [localizedCoordinates_smul, localizationToLaurent_algebraMap]

/-- The original surface quotient restriction is literal inclusion in
the already constructed common Laurent coordinates. -/
theorem seed_coordinates_restriction (r : ℂ)
    {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (z : SeedLocal ℂ r Complex.I s) (ab : ShiftIndex) :
    localizedCoordinates ℂ r Complex.I t (seedRestriction r hst z) ab =
      localizedCoordinates ℂ r Complex.I s z ab := by
  obtain ⟨n,p,hp⟩ := IsLocalization.Away.surj
    (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ s)) z
  have hp' : z * algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I s)
      (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ s ^ n)) =
      algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I s) p := by
    simpa only [map_pow] using hp
  have hs := congrArg (fun z => localizedCoordinates ℂ r Complex.I s z ab) hp'
  simp only [seed_coordinates_mul_base, localizedCoordinates_algebraMap] at hs
  have ht := congrArg (seedRestriction r hst) hp'
  simp only [map_mul, seedRestriction_base] at ht
  have ht' := congrArg (fun z => localizedCoordinates ℂ r Complex.I t z ab) ht
  simp only [seed_coordinates_mul_base, localizedCoordinates_algebraMap] at ht'
  have hu : IsUnit (baseToLaurent ℂ (baseProduct ℂ s ^ n)) := by
    rw [map_pow, baseToLaurent_baseProduct]
    exact (T_isUnit ℂ _).pow n
  exact hu.mul_right_injective (ht'.trans hs.symm)

/-- Coordinates of actual localized surface elements, preserving the
fixed quotient-ring isomorphism and the actual nine monomials. -/
def coordinateLaurent (r : ℂ) (s : Finset (Fin 3)) :
    CoordinateLocal r 1 s →+ (ShiftIndex → Laurent (R := ℂ)) :=
  (localizedCoordinates ℂ r Complex.I s).comp (seedCoordinateEquiv r s).toAddMonoidHom

theorem coordinateLaurent_injective (r : ℂ) (s : Finset (Fin 3)) :
    Function.Injective (coordinateLaurent r s) :=
  (localizedCoordinates_injective ℂ r Complex.I s).comp (seedCoordinateEquiv r s).injective

theorem coordinateLaurent_hasPoles (r : ℂ) (s : Finset (Fin 3))
    (p : CoordinateLocal r 1 s) (ab : ShiftIndex) :
    HasPoles s (coordinateLaurent r s p ab) :=
  localizedCoordinates_hasPoles ℂ r Complex.I s (seedCoordinateEquiv r s p) ab

theorem coordinateLaurent_range (r : ℂ) (s : Finset (Fin 3))
    (p : ShiftIndex → Laurent (R := ℂ)) :
    p ∈ Set.range (coordinateLaurent r s) ↔ ∀ ab, HasPoles s (p ab) := by
  constructor
  · rintro ⟨p,rfl⟩ ab
    exact coordinateLaurent_hasPoles r s p ab
  · intro hp
    obtain ⟨q,hq⟩ := (mem_range_localizedCoordinates ℂ r Complex.I s p).mpr hp
    refine ⟨(seedCoordinateEquiv r s).symm q, ?_⟩
    change localizedCoordinates ℂ r Complex.I s
      (seedCoordinateEquiv r s ((seedCoordinateEquiv r s).symm q)) = p
    rw [RingEquiv.apply_symm_apply]
    exact hq

@[simp] theorem coordinateLaurent_restriction (r : ℂ)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (p : CoordinateLocal r 1 s) :
    coordinateLaurent r t (coordinateRestriction r 1 hst p) = coordinateLaurent r s p := by
  funext ab
  change localizedCoordinates ℂ r Complex.I t
    (seedCoordinateEquiv r t (coordinateRestriction r 1 hst p)) ab = _
  rw [seedCoordinateEquiv_restriction, seed_coordinates_restriction]
  rfl

/-- Every all-negative Laurent coefficient vanishes exactly when the
original surface fraction is a boundary of actual pair-open fractions.
This identifies the original, ungraded coordinate top obstruction. -/
theorem coordinate_all_negative_zero_iff (r : ℂ)
    (p : CoordinateLocal r 1 Finset.univ) :
    (∀ ab e, (∀ i, e i < 0) → (coordinateLaurent r Finset.univ p ab).coeff e = 0) ↔
      ∃ (p01 : CoordinateLocal r 1 {0,1}) (p02 : CoordinateLocal r 1 {0,2})
        (p12 : CoordinateLocal r 1 {1,2}),
        coordinateRestriction r 1 (show ({1,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p12 -
          coordinateRestriction r 1 (show ({0,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p02 +
          coordinateRestriction r 1 (show ({0,1} : Finset (Fin 3)) ⊆ Finset.univ by simp) p01 = p := by
  constructor
  · intro hp
    choose a01 a02 a12 h01 h02 h12 he using fun ab =>
      (all_negative_zero_iff_pair_boundary (coordinateLaurent r Finset.univ p ab)).mp (hp ab)
    obtain ⟨q01,hq01⟩ := (coordinateLaurent_range r {0,1} a01).mpr h01
    obtain ⟨q02,hq02⟩ := (coordinateLaurent_range r {0,2} a02).mpr h02
    obtain ⟨q12,hq12⟩ := (coordinateLaurent_range r {1,2} a12).mpr h12
    refine ⟨q01,q02,q12,?_⟩
    apply coordinateLaurent_injective r Finset.univ
    simp only [map_add, map_sub, coordinateLaurent_restriction, hq01, hq02, hq12]
    funext ab
    exact he ab
  · rintro ⟨p01,p02,p12,hp⟩ ab
    apply (all_negative_zero_iff_pair_boundary (coordinateLaurent r Finset.univ p ab)).mpr
    refine ⟨coordinateLaurent r {0,1} p01 ab, coordinateLaurent r {0,2} p02 ab,
      coordinateLaurent r {1,2} p12 ab, coordinateLaurent_hasPoles r _ p01 ab,
      coordinateLaurent_hasPoles r _ p02 ab, coordinateLaurent_hasPoles r _ p12 ab,?_⟩
    have he := congrArg (fun z => coordinateLaurent r Finset.univ z ab) hp
    simpa only [map_add, map_sub, coordinateLaurent_restriction,
      Pi.add_apply, Pi.sub_apply] using he

end CycleQ2GeometricLaurentTop

namespace CycleQ2GeometricCartierCech

open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricFourOpenCech
  CycleQ2GeometricLocalizedCech CycleQ2GeometricLaurentTop
  CycleQ2SeedCechThreeOpen CycleQ2NormalConnecting

/-- The first actual triple component on the three coordinate opens.
The fourth open is empty; no representative is chosen or changed here. -/
def coordinateTopRepresentative (r : ℂ) (d : TwoCocycles (coordinateScalarSystem r)) :
    CoordinateLocal r 1 Finset.univ := d.val.1.1

@[simp] theorem coordinateTopRepresentative_smul (r : ℂ) (z : SurfaceRing r 1)
    (d : TwoCocycles (coordinateScalarSystem r)) :
    coordinateTopRepresentative r (z • d) = z • coordinateTopRepresentative r d := rfl

private theorem coordinateScalar_empty (r : ℂ) (s : Finset (Fin 4)) (hs : 3 ∈ s) :
    Subsingleton (RingAt (coordinateCover r) s) := by
  have hz : coordinateCover r 3 = 0 := rfl
  have hp : CycleQ2GeometricLocalizedCech.coverProduct (coordinateCover r) s = 0 :=
    Finset.prod_eq_zero hs hz
  exact IsLocalization.subsingleton (S := RingAt (coordinateCover r) s)
    (M := Submonoid.powers (CycleQ2GeometricLocalizedCech.coverProduct (coordinateCover r) s))
    ⟨1, by simp [hp]⟩

/-- The original scalar coordinate class vanishes precisely when all
strictly negative Laurent coefficients of its own first triple vanish.
This uses the fixed rank-nine surface basis and actual restriction maps. -/
theorem coordinate_class_zero_iff_all_negative (r : ℂ)
    (d : TwoCocycles (coordinateScalarSystem r)) :
    classOf (coordinateScalarSystem r) d = 0 ↔
      ∀ ab e, (∀ i, e i < 0) →
        (coordinateLaurent r Finset.univ (coordinateTopRepresentative r d) ab).coeff e = 0 := by
  rw [classOf_eq_zero_iff_three_boundary (coordinateScalarSystem r)
    (coordinateScalar_empty r)]
  change (∃ (p01 : CoordinateLocal r 1 {0,1}) (p02 : CoordinateLocal r 1 {0,2})
      (p12 : CoordinateLocal r 1 {1,2}),
      coordinateRestriction r 1 (show ({1,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p12 -
        coordinateRestriction r 1 (show ({0,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p02 +
        coordinateRestriction r 1 (show ({0,1} : Finset (Fin 3)) ⊆ Finset.univ by simp) p01 =
          coordinateTopRepresentative r d) ↔ _
  exact (coordinate_all_negative_zero_iff r (coordinateTopRepresentative r d)).symm

theorem coordinate_class_ne_zero_iff_negative_coefficient (r : ℂ)
    (d : TwoCocycles (coordinateScalarSystem r)) :
    classOf (coordinateScalarSystem r) d ≠ 0 ↔
      ∃ ab e, (∀ i, e i < 0) ∧
        (coordinateLaurent r Finset.univ (coordinateTopRepresentative r d) ab).coeff e ≠ 0 := by
  classical
  constructor
  · intro hd
    by_contra hn
    apply hd
    apply (coordinate_class_zero_iff_all_negative r d).mpr
    intro ab e he
    by_contra hc
    exact hn ⟨ab, e, he, hc⟩
  · rintro ⟨ab, e, he, hc⟩ hd
    exact hc ((coordinate_class_zero_iff_all_negative r d).mp hd ab e he)

/-- A negative Laurent coefficient belongs to the very same coordinate
descendant of the fixed literal Cartier cocycle. -/
theorem literal_cartier_negative_coordinate_coefficient :
    ∃ d : TwoCocycles (coordinateScalarSystem 57),
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d ∧
      ∃ ab e, (∀ i, e i < 0) ∧
        (coordinateLaurent 57 Finset.univ (coordinateTopRepresentative 57 d) ab).coeff e ≠ 0 := by
  obtain ⟨d, hcd, hd⟩ := literal_cartier_coordinate_descent_nonzero
  exact ⟨d, hcd, (coordinate_class_ne_zero_iff_negative_coefficient 57 d).mp hd⟩

/-- The same descended representative also has a nonzero negative Laurent
coefficient after multiplication by the fixed cubic. No degree projection
or character identification is assumed in this conclusion. -/
theorem literal_cartier_cubic_negative_coordinate_coefficient :
    ∃ d : TwoCocycles (coordinateScalarSystem 57),
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d ∧
      classOf (coordinateScalarSystem 57) d ≠ 0 ∧
      ∃ ab e, (∀ i, e i < 0) ∧
        (coordinateLaurent 57 Finset.univ
          (surfaceQuotient 57 1 detectorCubic • coordinateTopRepresentative 57 d) ab).coeff e ≠ 0 := by
  obtain ⟨d, hcd, hd, hσ⟩ := literal_cartier_coordinate_cubic_nonzero
  have hσ' : classOf (coordinateScalarSystem 57)
      (surfaceQuotient 57 1 detectorCubic • d) ≠ 0 := by
    simpa only [map_smul] using hσ
  obtain ⟨ab, e, he, hc⟩ :=
    (coordinate_class_ne_zero_iff_negative_coefficient 57
      (surfaceQuotient 57 1 detectorCubic • d)).mp hσ'
  refine ⟨d, hcd, hd, ab, e, he, ?_⟩
  simpa only [coordinateTopRepresentative_smul] using hc

end CycleQ2GeometricCartierCech

namespace CycleQ2SeedCechThreeOpen

/-- Among the actual nine surface-basis shifts and strictly negative base
Laurent exponents, weight three has exactly one possible monomial. -/
theorem strictlyNegative_weight_three_unique (ab : ShiftIndex) (e : LaurentExponent)
    (he : ∀ i, e i < 0) (hw : (shiftedGrade ab e).1 = 3) :
    ab = (2, 2) ∧ e = fun _ => -1 := by
  rcases ab with ⟨a, b⟩
  have ha := a.isLt
  have hb := b.isLt
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  simp only [shiftedGrade, Fin.sum_univ_three] at hw
  have ha' : a.val = 2 := by omega
  have hb' : b.val = 2 := by omega
  have h0' : e 0 = -1 := by omega
  have h1' : e 1 = -1 := by omega
  have h2' : e 2 = -1 := by omega
  refine ⟨Prod.ext (Fin.ext ha') (Fin.ext hb'), ?_⟩
  funext i
  fin_cases i
  · exact h0'
  · exact h1'
  · exact h2'

/-- The unique weight-three top coordinate monomial has character one
for the actual action encoded by `shiftedGrade`. This statement concerns
the coordinate cover; it assumes no character for a Cartier denominator. -/
theorem strictlyNegative_weight_three_character (ab : ShiftIndex) (e : LaurentExponent)
    (he : ∀ i, e i < 0) (hw : (shiftedGrade ab e).1 = 3) :
    (shiftedGrade ab e).2 = 1 := by
  obtain ⟨rfl, rfl⟩ := strictlyNegative_weight_three_unique ab e he hw
  norm_num [shiftedGrade]

end CycleQ2SeedCechThreeOpen

#print axioms CycleQ2GeometricFourOpenCech.second_descent_exists
#print axioms CycleQ2GeometricFourOpenCech.second_descent_reflects_boundary
#print axioms CycleQ2GeometricFourOpenCech.BiSystem.exists_second_descent
#print axioms CycleQ2GeometricFourOpenCech.BiSystem.exists_nonzero_second_descent
#print axioms CycleQ2GeometricLocalizedCech.exists_nonzero_second_descent_of_radical_eq
#print axioms CycleQ2GeometricLocalizedCech.PrincipalSecondDescent.reflects_class_zero
#print axioms CycleQ2GeometricFourOpenCech.classOf_eq_zero_iff_three_boundary
#print axioms CycleQ2GeometricLaurentTop.all_negative_zero_iff_pair_boundary
#print axioms CycleQ2GeometricLaurentTop.coordinate_all_negative_zero_iff
#print axioms CycleQ2GeometricCartierCech.coordinate_class_zero_iff_all_negative
#print axioms CycleQ2GeometricCartierCech.literal_cartier_cubic_negative_coordinate_coefficient
#print axioms CycleQ2SeedCechThreeOpen.strictlyNegative_weight_three_unique
#print axioms CycleQ2SeedCechThreeOpen.strictlyNegative_weight_three_character
