import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Algebra.Bilinear
import Proposal.GeometricCechRefinement

/-!
# Canonical weight-zero projection of the actual Cartier staircase

The degree-zero projection on ordinary homogeneous principal localizations
is constructed by projecting each numerator to the denominator's degree.
Clearing denominators proves independence of every fraction presentation,
including in rings with zero divisors. It commutes with the actual
localization maps and fixes genuine homogeneous degree-zero fractions.

Canonical tensor-localization equivalences then project the original
Cartier-to-coordinate staircase, retaining its actual maps and primitives.
The fixed literal Cartier cocycle is unchanged. The projected coordinate
cocycle and its unchanged detector-cubic multiple are both nonzero.
The signed diagonal primitive compares the first cocycle with the negative
of the second, in the ordinary alternating Cech convention.

This module does not yet identify the projected coordinate cochain with
actual projective coordinate sections and their derived class. Nor does
it yet prove the weight support of its actual rank-nine Laurent coordinates.
Those are separate comparisons, not premises of the results proved here.
-/


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2GradedLocalizationProjection

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

def powerDenominator (f : A) (n : ℕ) : Submonoid.powers f := ⟨f ^ n, ⟨n, rfl⟩⟩

def fraction (f : A) (n : ℕ) (a : A) : Localization.Away f :=
  IsLocalization.mk' (Localization.Away f) a (powerDenominator f n)

theorem exists_fraction (f : A) (z : Localization.Away f) :
    ∃ n a, fraction f n a = z := by
  obtain ⟨a, ⟨_, n, rfl⟩, ha⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) z
  exact ⟨n, a, ha⟩

theorem fraction_add (f : A) (n m : ℕ) (a b : A) :
    fraction f (n + m) (a * f ^ m + b * f ^ n) = fraction f n a + fraction f m b := by
  unfold fraction
  rw [show powerDenominator f (n + m) =
    powerDenominator f n * powerDenominator f m from Subtype.ext (pow_add f n m)]
  exact IsLocalization.mk'_add a b (powerDenominator f n) (powerDenominator f m)

variable {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)

include hf in
theorem proj_mul_pow (n m : ℕ) (a : A) :
    GradedRing.proj 𝒜 ((n + m) * d) (a * f ^ m) =
      GradedRing.proj 𝒜 (n * d) a * f ^ m := by
  rw [Nat.add_mul]
  exact DirectSum.coe_decompose_mul_add_of_right_mem 𝒜
    (show f ^ m ∈ 𝒜 (m * d) by simpa using SetLike.pow_mem_graded m hf)

/-- Extract the numerator of exactly the denominator's degree. -/
def projectedFraction (n : ℕ) (a : A) : HomogeneousLocalization.Away 𝒜 f :=
  HomogeneousLocalization.Away.mk 𝒜 hf n (GradedRing.proj 𝒜 (n * d) a)
    (by
      change (DirectSum.decompose 𝒜 a (n * d) : A) ∈ 𝒜 (n * d)
      exact (DirectSum.decompose 𝒜 a (n * d)).property)

@[simp] theorem projectedFraction_val (n : ℕ) (a : A) :
    (projectedFraction 𝒜 hf n a).val = fraction f n (GradedRing.proj 𝒜 (n * d) a) := by
  simp only [projectedFraction, HomogeneousLocalization.Away.val_mk,
    fraction, Localization.mk_eq_mk', powerDenominator]

/-- This construction is independent of the numerator and pole order. It
does not assume the homogeneous denominator is a nonzerodivisor. -/
theorem projectedFraction_eq {n m : ℕ} {a b : A}
    (h : fraction f n a = fraction f m b) :
    projectedFraction 𝒜 hf n a = projectedFraction 𝒜 hf m b := by
  apply HomogeneousLocalization.val_injective
  simp only [projectedFraction_val]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.eq.mp h
  have hk' : a * f ^ (m + k) = b * f ^ (n + k) := by
    simpa only [powerDenominator, pow_add, mul_assoc, mul_comm, mul_left_comm] using hk
  have hdegrees : m + (n + k) = n + (m + k) := by omega
  have hx := proj_mul_pow 𝒜 hf n (m + k) a
  have hy := proj_mul_pow 𝒜 hf m (n + k) b
  rw [hdegrees] at hy
  have hp : GradedRing.proj 𝒜 (n * d) a * f ^ (m + k) =
      GradedRing.proj 𝒜 (m * d) b * f ^ (n + k) :=
    hx.symm.trans ((congrArg (GradedRing.proj 𝒜 ((n + (m + k)) * d)) hk').trans hy)
  apply IsLocalization.eq.mpr
  refine ⟨powerDenominator f k, ?_⟩
  simpa only [powerDenominator, pow_add, mul_assoc, mul_comm, mul_left_comm] using hp

/-- The actual weight-zero part of an ordinary principal localization,
valued in its genuine homogeneous localization. -/
def degreeZero (z : Localization.Away f) : HomogeneousLocalization.Away 𝒜 f :=
  projectedFraction 𝒜 hf (IsLocalization.Away.sec f z).2 (IsLocalization.Away.sec f z).1

theorem sec_fraction (z : Localization.Away f) :
    fraction f (IsLocalization.Away.sec f z).2 (IsLocalization.Away.sec f z).1 = z := by
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  exact (IsLocalization.Away.sec_spec f z).symm

theorem degreeZero_fraction (n : ℕ) (a : A) :
    degreeZero 𝒜 hf (fraction f n a) = projectedFraction 𝒜 hf n a :=
  projectedFraction_eq 𝒜 hf (sec_fraction (fraction f n a))

theorem degreeZero_add (z w : Localization.Away f) :
    degreeZero 𝒜 hf (z + w) = degreeZero 𝒜 hf z + degreeZero 𝒜 hf w := by
  obtain ⟨n, a, rfl⟩ := exists_fraction f z
  obtain ⟨m, b, rfl⟩ := exists_fraction f w
  rw [← fraction_add, degreeZero_fraction, degreeZero_fraction, degreeZero_fraction]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_add, projectedFraction_val]
  rw [map_add, proj_mul_pow 𝒜 hf n m a]
  have hb := proj_mul_pow 𝒜 hf m n b
  rw [Nat.add_comm m n] at hb
  rw [hb]
  exact fraction_add f n m _ _

theorem degreeZero_zero : degreeZero 𝒜 hf 0 = 0 := by
  have h := degreeZero_add 𝒜 hf (0 : Localization.Away f) 0
  apply add_left_cancel (a := degreeZero 𝒜 hf 0)
  simpa only [zero_add, add_zero] using h.symm

def degreeZeroAddHom : Localization.Away f →+ HomogeneousLocalization.Away 𝒜 f where
  toFun := degreeZero 𝒜 hf
  map_zero' := degreeZero_zero 𝒜 hf
  map_add' := degreeZero_add 𝒜 hf

/-- Every already homogeneous degree-zero fraction is fixed by projection. -/
theorem degreeZero_val (z : HomogeneousLocalization.Away 𝒜 f) :
    degreeZero 𝒜 hf z.val = z := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf z
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  change degreeZero 𝒜 hf (fraction f n a) = _
  rw [degreeZero_fraction]
  apply HomogeneousLocalization.val_injective
  simp only [projectedFraction_val, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', fraction]
  congr 1
  exact DirectSum.decompose_of_mem_same 𝒜 ha

end CycleQ2GradedLocalizationProjection

#print axioms CycleQ2GradedLocalizationProjection.projectedFraction_eq
#print axioms CycleQ2GradedLocalizationProjection.degreeZero_val

namespace CycleQ2GradedLocalizationProjection

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {f g x : A} {d e : ℕ}

theorem fraction_map (ρ : Localization.Away f →ₐ[A] Localization.Away x)
    (hx : x = f * g) (n : ℕ) (a : A) :
    ρ (fraction f n a) = fraction x n (a * g ^ n) := by
  subst x
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  change ρ (fraction f n a) * algebraMap A (Localization.Away (f * g)) ((f * g) ^ n) =
    algebraMap A (Localization.Away (f * g)) (a * g ^ n)
  rw [mul_pow, map_mul, ← mul_assoc]
  have h := congrArg ρ (IsLocalization.mk'_spec (Localization.Away f) a (powerDenominator f n))
  have h' : ρ (fraction f n a) * algebraMap A (Localization.Away (f * g)) (f ^ n) =
      algebraMap A (Localization.Away (f * g)) a := by
    simpa only [fraction, powerDenominator, map_mul, AlgHom.commutes] using h
  rw [h', map_mul]

theorem degreeZero_eq_of_mem (hf : f ∈ 𝒜 d) (hf' : f ∈ 𝒜 e)
    (z : Localization.Away f) : degreeZero 𝒜 hf z = degreeZero 𝒜 hf' z := by
  by_cases hz : f = 0
  · exact @Subsingleton.elim (HomogeneousLocalization.Away 𝒜 f)
      (HomogeneousLocalization.subsingleton 𝒜 (x := Submonoid.powers f)
        ⟨1, by simpa using hz⟩) _ _
  · have hd := DirectSum.degree_eq_of_mem_mem 𝒜 hf hf' hz
    subst e
    rfl

/-- Projection commutes with the actual localization map, and its codomain
map is the genuine degree-zero homogeneous restriction. -/
theorem degreeZero_naturality (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hx : x = f * g) {dx : ℕ} (hxhom : x ∈ 𝒜 dx)
    (ρ : Localization.Away f →ₐ[A] Localization.Away x) (z : Localization.Away f) :
    degreeZero 𝒜 hxhom (ρ z) =
      HomogeneousLocalization.awayMap 𝒜 hg hx (degreeZero 𝒜 hf z) := by
  rw [degreeZero_eq_of_mem 𝒜 hxhom (hx ▸ SetLike.mul_mem_graded hf hg)]
  obtain ⟨n, a, rfl⟩ := exists_fraction f z
  rw [fraction_map ρ hx, degreeZero_fraction, degreeZero_fraction]
  simp only [projectedFraction, HomogeneousLocalization.awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk]
  congr 1
  change GradedRing.proj 𝒜 (n * (d + e)) (a * g ^ n) =
    GradedRing.proj 𝒜 (n * d) a * g ^ n
  rw [Nat.mul_add]
  exact DirectSum.coe_decompose_mul_add_of_right_mem 𝒜
    (show g ^ n ∈ 𝒜 (n * e) by simpa using SetLike.pow_mem_graded n hg)

theorem homogeneousRestriction_val (hg : g ∈ 𝒜 e) (hx : x = f * g)
    (ρ : Localization.Away f →ₐ[A] Localization.Away x)
    (z : HomogeneousLocalization.Away 𝒜 f) :
    (HomogeneousLocalization.awayMap 𝒜 hg hx z).val = ρ z.val := by
  rw [HomogeneousLocalization.val_awayMap]
  let hu : IsUnit (algebraMap A (Localization.Away x) f) :=
    isUnit_of_dvd_unit (map_dvd _ ⟨g, hx⟩) (IsLocalization.Away.algebraMap_isUnit x)
  have hρ : Localization.awayLift (algebraMap A (Localization.Away x)) f
      (isUnit_of_dvd_unit (map_dvd _ ⟨g, hx⟩)
        (IsLocalization.Away.algebraMap_isUnit x)) = ρ.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro a
    change IsLocalization.Away.lift f hu (algebraMap A (Localization.Away f) a) =
      ρ (algebraMap A (Localization.Away f) a)
    rw [IsLocalization.Away.lift_eq, ρ.commutes]
  exact DFunLike.congr_fun hρ z.val

/-- The projection as an additive endomorphism of the original localization.
Its range is realized by genuine homogeneous fractions. -/
def degreeZeroEnd (hf : f ∈ 𝒜 d) : Localization.Away f →+ Localization.Away f where
  toFun z := (degreeZero 𝒜 hf z).val
  map_zero' := by rw [degreeZero_zero, HomogeneousLocalization.val_zero]
  map_add' z w := by rw [degreeZero_add, HomogeneousLocalization.val_add]

theorem degreeZeroEnd_val (hf : f ∈ 𝒜 d) (z : HomogeneousLocalization.Away 𝒜 f) :
    degreeZeroEnd 𝒜 hf z.val = z.val := by
  change (degreeZero 𝒜 hf z.val).val = z.val
  rw [degreeZero_val]

theorem degreeZeroEnd_idempotent (hf : f ∈ 𝒜 d) (z : Localization.Away f) :
    degreeZeroEnd 𝒜 hf (degreeZeroEnd 𝒜 hf z) = degreeZeroEnd 𝒜 hf z :=
  degreeZeroEnd_val 𝒜 hf (degreeZero 𝒜 hf z)

theorem degreeZeroEnd_naturality (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hx : x = f * g) {dx : ℕ} (hxhom : x ∈ 𝒜 dx)
    (ρ : Localization.Away f →ₐ[A] Localization.Away x) (z : Localization.Away f) :
    degreeZeroEnd 𝒜 hxhom (ρ z) = ρ (degreeZeroEnd 𝒜 hf z) := by
  change (degreeZero 𝒜 hxhom (ρ z)).val = ρ (degreeZero 𝒜 hf z).val
  rw [degreeZero_naturality 𝒜 hf hg hx hxhom ρ, homogeneousRestriction_val]

end CycleQ2GradedLocalizationProjection


set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2MixedScalarLocalization

open scoped TensorProduct

variable {A : Type*} [CommRing A]

abbrev TensorRing (a b : A) := Localization.Away b ⊗[A] Localization.Away a
abbrev ScalarModule (a b : A) :=
  Localization.Away b ⊗[A] (Localization.Away a ⊗[A] A)

instance tensorIsLocalization (a b : A) :
    IsLocalization.Away (a * b) (TensorRing a b) :=
  IsLocalization.Away.mul (Localization.Away b) (TensorRing a b) b a

/-- The two successive scalar localizations are the actual localization at
the product, with the original base-ring map. -/
def tensorEquiv (a b : A) : TensorRing a b ≃ₐ[A] Localization.Away (a * b) :=
  IsLocalization.algEquiv (Submonoid.powers (a * b)) _ _

def scalarEquiv (a b : A) : ScalarModule a b ≃ₗ[A] Localization.Away (a * b) :=
  (TensorProduct.congr (LinearEquiv.refl A (Localization.Away b))
    (TensorProduct.rid A (Localization.Away a))).trans (tensorEquiv a b).toLinearEquiv

def firstFactor (a b : A) : Localization.Away a →ₐ[A] Localization.Away (a * b) :=
  (tensorEquiv a b).toAlgHom.comp Algebra.TensorProduct.includeRight

def secondFactor (a b : A) : Localization.Away b →ₐ[A] Localization.Away (a * b) :=
  (tensorEquiv a b).toAlgHom.comp Algebra.TensorProduct.includeLeft

theorem tensorEquiv_tmul (a b : A) (z : Localization.Away b) (w : Localization.Away a) :
    tensorEquiv a b (z ⊗ₜ[A] w) = secondFactor a b z * firstFactor a b w := by
  change tensorEquiv a b (z ⊗ₜ[A] w) =
    tensorEquiv a b (z ⊗ₜ[A] 1) * tensorEquiv a b (1 ⊗ₜ[A] w)
  rw [← map_mul]
  simp

theorem scalarEquiv_tmul (a b : A) (z : Localization.Away b)
    (w : Localization.Away a) (r : A) :
    scalarEquiv a b (z ⊗ₜ[A] (w ⊗ₜ[A] r)) =
      r • (secondFactor a b z * firstFactor a b w) := by
  change tensorEquiv a b (z ⊗ₜ[A] (r • w)) = _
  rw [TensorProduct.tmul_smul, map_smul, tensorEquiv_tmul]

theorem firstFactor_natural {a b a' b' : A}
    (ρ : Localization.Away (a * b) →ₐ[A] Localization.Away (a' * b'))
    (ρa : Localization.Away a →ₐ[A] Localization.Away a') (z : Localization.Away a) :
    ρ (firstFactor a b z) = firstFactor a' b' (ρa z) := by
  exact DFunLike.congr_fun (Subsingleton.elim
    (h := IsLocalization.algHom_subsingleton (Submonoid.powers a))
    (ρ.comp (firstFactor a b)) ((firstFactor a' b').comp ρa)) z

theorem secondFactor_natural {a b a' b' : A}
    (ρ : Localization.Away (a * b) →ₐ[A] Localization.Away (a' * b'))
    (ρb : Localization.Away b →ₐ[A] Localization.Away b') (z : Localization.Away b) :
    ρ (secondFactor a b z) = secondFactor a' b' (ρb z) := by
  exact DFunLike.congr_fun (Subsingleton.elim
    (h := IsLocalization.algHom_subsingleton (Submonoid.powers b))
    (ρ.comp (secondFactor a b)) ((secondFactor a' b').comp ρb)) z

/-- Naturality is proved for the original tensor maps and any actual
base-preserving localization maps; no separate comparison premise occurs. -/
theorem scalarEquiv_natural {a b a' b' : A}
    (ρ : Localization.Away (a * b) →ₐ[A] Localization.Away (a' * b'))
    (ρa : Localization.Away a →ₐ[A] Localization.Away a')
    (ρb : Localization.Away b →ₐ[A] Localization.Away b') (p : ScalarModule a b) :
    ρ (scalarEquiv a b p) = scalarEquiv a' b'
      (TensorProduct.map ρb.toLinearMap
        (TensorProduct.map ρa.toLinearMap (LinearMap.id : A →ₗ[A] A)) p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul z m =>
    induction m using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
    | tmul w r =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply,
        scalarEquiv_tmul, map_smul, map_mul]
      rw [firstFactor_natural ρ ρa, secondFactor_natural ρ ρb]

end CycleQ2MixedScalarLocalization

#print axioms CycleQ2MixedScalarLocalization.scalarEquiv_natural


set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GradedCechProjection

open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V W : Finset (Fin 4) → Finset (Fin 4) → Type*}
variable [∀ s t, AddCommGroup (V s t)] [∀ s t, Module R (V s t)]
variable [∀ s t, AddCommGroup (W s t)] [∀ s t, Module R (W s t)]

/-- A map of the actual common-refinement modules, natural in both
restriction directions. -/
structure BiMorphism (D : BiSystem (R := R) V) (E : BiSystem (R := R) W) where
  app (s t : Finset (Fin 4)) : V s t →ₗ[R] W s t
  left_naturality {s s' : Finset (Fin 4)} (hs : s ⊆ s') (t : Finset (Fin 4)) :
    (app s' t).comp ((D.left t).res hs) = ((E.left t).res hs).comp (app s t)
  right_naturality (s : Finset (Fin 4)) {t t' : Finset (Fin 4)} (ht : t ⊆ t') :
    (app s t').comp ((D.right s).res ht) = ((E.right s).res ht).comp (app s t)

namespace BiMorphism

variable {D : BiSystem (R := R) V} {E : BiSystem (R := R) W} (φ : BiMorphism D E)

def left (t : Finset (Fin 4)) : SystemMorphism (D.left t) (E.left t) where
  app s := φ.app s t
  naturality hs := φ.left_naturality hs t

def right (s : Finset (Fin 4)) : SystemMorphism (D.right s) (E.right s) where
  app t := φ.app s t
  naturality ht := φ.right_naturality s ht

def row0 : SystemMorphism D.row0 E.row0 where
  app s := (φ.right s).map0
  naturality hs := by
    ext p <;> exact LinearMap.congr_fun (φ.left_naturality hs _) _

def row1 : SystemMorphism D.row1 E.row1 where
  app s := (φ.right s).map1
  naturality hs := by
    ext p <;> exact LinearMap.congr_fun (φ.left_naturality hs _) _

def row2 : SystemMorphism D.row2 E.row2 where
  app s := (φ.right s).map2
  naturality hs := by
    ext p <;> exact LinearMap.congr_fun (φ.left_naturality hs _) _

theorem horizontal_augmentation (c : TwoCochain (fun s => V s ∅)) :
    φ.row0.map2 (D.horizontalAugmentation.map2 c) =
      E.horizontalAugmentation.map2 ((φ.left ∅).map2 c) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals exact (φ.right _).map0_augmentation _

theorem vertical0 (x : OneCochain (fun s => ZeroCochain (V s))) :
    φ.row1.map1 (D.vertical0.map1 x) = E.vertical0.map1 (φ.row0.map1 x) := by
  apply Prod.ext
  · apply Prod.ext
    · exact (φ.right _).map1_d0 _
    · apply Prod.ext <;> exact (φ.right _).map1_d0 _
  · apply Prod.ext
    · exact (φ.right _).map1_d0 _
    · apply Prod.ext <;> exact (φ.right _).map1_d0 _

theorem vertical1 (y : ZeroCochain (fun s => OneCochain (V s))) :
    φ.row2.map0 (D.vertical1.map0 y) = E.vertical1.map0 (φ.row1.map0 y) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals exact (φ.right _).map2_d1 _

/-- Both projected primitives are the images of the original primitives,
and satisfy the same three staircase equations. -/
theorem secondDescent_data
    (c : TwoCochain (fun s => V s ∅)) (d : TwoCochain (V ∅))
    (x : OneCochain (fun s => ZeroCochain (V s)))
    (y : ZeroCochain (fun s => OneCochain (V s)))
    (hx : d1 D.row0 x = D.horizontalAugmentation.map2 c)
    (hy : d0 D.row1 y = D.vertical0.map1 x)
    (hd : augmentation D.row2 d = D.vertical1.map0 y) :
    d1 E.row0 (φ.row0.map1 x) =
        E.horizontalAugmentation.map2 ((φ.left ∅).map2 c) ∧
      d0 E.row1 (φ.row1.map0 y) = E.vertical0.map1 (φ.row0.map1 x) ∧
      augmentation E.row2 ((φ.right ∅).map2 d) = E.vertical1.map0 (φ.row1.map0 y) := by
  constructor
  · rw [← φ.row0.map2_d1, hx, φ.horizontal_augmentation]
  constructor
  · rw [← φ.row1.map1_d0, hy, φ.vertical0]
  · change augmentation E.row2 (φ.row2.app ∅ d) = _
    rw [← φ.row2.map0_augmentation, hd, φ.vertical1]

theorem map_secondDescent
    {c : TwoCochain (fun s => V s ∅)} {d : TwoCochain (V ∅)}
    (h : D.SecondDescent c d) :
    E.SecondDescent ((φ.left ∅).map2 c) ((φ.right ∅).map2 d) := by
  obtain ⟨x, y, hx, hy, hd⟩ := h
  exact ⟨φ.row0.map1 x, φ.row1.map0 y, φ.secondDescent_data c d x y hx hy hd⟩

end BiMorphism

end CycleQ2GradedCechProjection

#print axioms CycleQ2GradedCechProjection.BiMorphism.secondDescent_data

namespace CycleQ2GradedCechProjection

open scoped BigOperators
open CycleQ2GeometricFourOpenCech CycleQ2GeometricLocalizedCech
  CycleQ2GradedLocalizationProjection

section PrincipalFamilies

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (a : Fin 4 → A) (w : Fin 4 → ℕ) (ha : ∀ i, a i ∈ 𝒜 (w i))

def productWeight (s : Finset (Fin 4)) : ℕ := ∑ i ∈ s, w i

include ha in
theorem principalProduct_homogeneous (s : Finset (Fin 4)) :
    coverProduct a s ∈ 𝒜 (productWeight w s) :=
  SetLike.prod_mem_graded 𝒜 w a (fun i _ => ha i)

theorem principalProduct_factor {s t : Finset (Fin 4)} (h : s ⊆ t) :
    coverProduct a t = coverProduct a s * coverProduct a (t \ s) := by
  unfold coverProduct
  rw [mul_comm]
  exact (Finset.prod_sdiff h).symm

/-- Project every original principal-localization section to its actual
weight-zero fraction. -/
def principalProjection (s : Finset (Fin 4)) : RingAt a s →+ RingAt a s :=
  degreeZeroEnd 𝒜 (principalProduct_homogeneous 𝒜 a w ha s)

theorem principalProjection_restriction {s t : Finset (Fin 4)} (h : s ⊆ t)
    (z : RingAt a s) :
    principalProjection 𝒜 a w ha t (ringRestriction a h z) =
      ringRestriction a h (principalProjection 𝒜 a w ha s z) :=
  degreeZeroEnd_naturality 𝒜 (principalProduct_homogeneous 𝒜 a w ha s)
    (principalProduct_homogeneous 𝒜 a w ha (t \ s)) (principalProduct_factor a h)
    (principalProduct_homogeneous 𝒜 a w ha t) (ringRestriction a h) z

def principalProjectionMorphism :
    SystemMorphism ((scalarSystem a).restrictScalars ℤ) ((scalarSystem a).restrictScalars ℤ) where
  app s := (principalProjection 𝒜 a w ha s).toIntLinearMap
  naturality h := by
    apply LinearMap.ext
    intro z
    exact principalProjection_restriction 𝒜 a w ha h z

/-- The cocycle is obtained by applying the canonical projection to each
of the original four components. -/
def principalProjectedCocycle (c : TwoCocycles (scalarSystem a)) :
    TwoCocycles (scalarSystem a) :=
  ⟨(principalProjectionMorphism 𝒜 a w ha).map2 c.val, by
    change d2 ((scalarSystem a).restrictScalars ℤ)
      ((principalProjectionMorphism 𝒜 a w ha).map2 c.val) = 0
    rw [← (principalProjectionMorphism 𝒜 a w ha).app_d2]
    change (principalProjection 𝒜 a w ha Finset.univ) (d2 (scalarSystem a) c.val) = 0
    rw [c.property, map_zero]⟩

end PrincipalFamilies

section ActualSurface

open MvPolynomial CycleQ2ConormalJacobian CycleQ2SeedQuotientFiniteFree
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricCartierCech
  CycleQ2CartierSurfaceGrading CycleQ2CartierHomogeneousCech

theorem coordinateElement_homogeneous (r θ : ℂ) (i : Fin 3) :
    coordinateElement r θ i ∈ surfaceGrade r θ 1 := by
  apply surfaceQuotient_mem_grade
  change (X (remainingIndex i) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous weight 1
  have hi : weight (remainingIndex i) = 1 := by fin_cases i <;> rfl
  simpa only [hi] using MvPolynomial.isWeightedHomogeneous_X ℂ weight (remainingIndex i)

theorem coordinateCover_homogeneous (r : ℂ) (i : Fin 4) :
    coordinateCover r i ∈ surfaceGrade r 1 1 := by
  fin_cases i
  · exact coordinateElement_homogeneous r 1 0
  · exact coordinateElement_homogeneous r 1 1
  · exact coordinateElement_homogeneous r 1 2
  · exact (surfaceGrade r 1 1).zero_mem

def coordinateProjection (r : ℂ) (s : Finset (Fin 4)) :
    RingAt (coordinateCover r) s →+ RingAt (coordinateCover r) s :=
  principalProjection (surfaceGrade r 1) (coordinateCover r) (fun _ => 1)
    (coordinateCover_homogeneous r) s

theorem coordinateProjection_restriction (r : ℂ)
    {s t : Finset (Fin 4)} (h : s ⊆ t) (z : RingAt (coordinateCover r) s) :
    coordinateProjection r t (ringRestriction (coordinateCover r) h z) =
      ringRestriction (coordinateCover r) h (coordinateProjection r s z) :=
  principalProjection_restriction (surfaceGrade r 1) (coordinateCover r) (fun _ => 1)
    (coordinateCover_homogeneous r) h z

def coordinateProjectedCocycle (r : ℂ) (d : TwoCocycles (coordinateScalarSystem r)) :
    TwoCocycles (coordinateScalarSystem r) :=
  principalProjectedCocycle (surfaceGrade r 1) (coordinateCover r) (fun _ => 1)
    (coordinateCover_homogeneous r) d

def cartierProjectionMorphism (r θ : ℂ) :
    SystemMorphism ((surfaceSystem r θ).restrictScalars ℤ)
      ((surfaceSystem r θ).restrictScalars ℤ) where
  app s := (degreeZeroEnd (surfaceGrade r θ) (coverProduct_mem_grade r θ s)).toIntLinearMap
  naturality h := by
    apply LinearMap.ext
    intro z
    exact degreeZeroEnd_naturality (surfaceGrade r θ) (coverProduct_mem_grade r θ _)
      (coverProduct_mem_grade r θ _) (coverProduct_factor r θ h)
      (coverProduct_mem_grade r θ _) (coverRestriction r θ h) z

/-- The projection fixes the original literal Cartier cocycle, because its
two nonzero faces are the previously proved genuine homogeneous fractions. -/
theorem literalCartier_projection_fixed :
    (cartierProjectionMorphism 57 1).map2
        (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0).val =
      (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0).val := by
  apply Prod.ext <;> apply Prod.ext
  · change degreeZeroEnd (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1,2})
      (boundary012 57 1 CycleQ2NormalConnecting.derivativeA 0) =
        boundary012 57 1 CycleQ2NormalConnecting.derivativeA 0
    rw [← literalHomogeneousBoundary012_val]
    exact degreeZeroEnd_val (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1,2})
      literalHomogeneousBoundary012
  · change degreeZeroEnd (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1,3})
      (boundary013 57 1 CycleQ2NormalConnecting.derivativeA 0) =
        boundary013 57 1 CycleQ2NormalConnecting.derivativeA 0
    rw [← literalHomogeneousBoundary013_val]
    exact degreeZeroEnd_val (surfaceGrade 57 1) (coverProduct_mem_grade 57 1 {0,1,3})
      literalHomogeneousBoundary013
  · exact map_zero _
  · exact map_zero _

end ActualSurface

end CycleQ2GradedCechProjection
#print axioms CycleQ2GradedLocalizationProjection.degreeZeroEnd_naturality
#print axioms CycleQ2GradedCechProjection.literalCartier_projection_fixed


set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2GradedCechProjection

open scoped TensorProduct
open CycleQ2GradedLocalizationProjection CycleQ2MixedScalarLocalization
  CycleQ2GeometricFourOpenCech CycleQ2GeometricLocalizedCech

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

section ScalarModules

variable {a b a' b' k : A} {da db da' db' dk : ℕ}

def mixedProjection (ha : a ∈ 𝒜 da) (hb : b ∈ 𝒜 db) :
    ScalarModule a b →+ ScalarModule a b :=
  (scalarEquiv a b).symm.toLinearMap.toAddMonoidHom.comp
    ((degreeZeroEnd 𝒜 (SetLike.mul_mem_graded ha hb)).comp
      (scalarEquiv a b).toLinearMap.toAddMonoidHom)

theorem scalarEquiv_mixedProjection (ha : a ∈ 𝒜 da) (hb : b ∈ 𝒜 db)
    (p : ScalarModule a b) :
    scalarEquiv a b (mixedProjection 𝒜 ha hb p) =
      degreeZeroEnd 𝒜 (SetLike.mul_mem_graded ha hb) (scalarEquiv a b p) :=
  (scalarEquiv a b).apply_symm_apply _

/-- Conjugation by the canonical scalar-localization equivalence retains
the original mixed module and commutes with its actual tensor maps. -/
theorem mixedProjection_natural
    (ha : a ∈ 𝒜 da) (hb : b ∈ 𝒜 db) (ha' : a' ∈ 𝒜 da') (hb' : b' ∈ 𝒜 db')
    (hk : k ∈ 𝒜 dk) (hfactor : a' * b' = (a * b) * k)
    (ρ : Localization.Away (a * b) →ₐ[A] Localization.Away (a' * b'))
    (ρa : Localization.Away a →ₐ[A] Localization.Away a')
    (ρb : Localization.Away b →ₐ[A] Localization.Away b') (p : ScalarModule a b) :
    mixedProjection 𝒜 ha' hb'
        (TensorProduct.map ρb.toLinearMap
          (TensorProduct.map ρa.toLinearMap (LinearMap.id : A →ₗ[A] A)) p) =
      TensorProduct.map ρb.toLinearMap
        (TensorProduct.map ρa.toLinearMap (LinearMap.id : A →ₗ[A] A))
          (mixedProjection 𝒜 ha hb p) := by
  apply (scalarEquiv a' b').injective
  rw [scalarEquiv_mixedProjection]
  rw [← scalarEquiv_natural ρ ρa ρb p]
  rw [degreeZeroEnd_naturality 𝒜 (SetLike.mul_mem_graded ha hb) hk hfactor
    (SetLike.mul_mem_graded ha' hb') ρ]
  rw [← scalarEquiv_mixedProjection]
  exact scalarEquiv_natural ρ ρa ρb _

def moduleProjection (ha : a ∈ 𝒜 da) :
    (Localization.Away a ⊗[A] A) →+ (Localization.Away a ⊗[A] A) :=
  (TensorProduct.rid A (Localization.Away a)).symm.toLinearMap.toAddMonoidHom.comp
    ((degreeZeroEnd 𝒜 ha).comp
      (TensorProduct.rid A (Localization.Away a)).toLinearMap.toAddMonoidHom)

theorem rid_moduleProjection (ha : a ∈ 𝒜 da) (p : Localization.Away a ⊗[A] A) :
    TensorProduct.rid A (Localization.Away a) (moduleProjection 𝒜 ha p) =
      degreeZeroEnd 𝒜 ha (TensorProduct.rid A (Localization.Away a) p) :=
  (TensorProduct.rid A (Localization.Away a)).apply_symm_apply _

theorem rid_natural (ρ : Localization.Away a →ₐ[A] Localization.Away a')
    (p : Localization.Away a ⊗[A] A) :
    TensorProduct.rid A (Localization.Away a')
        (TensorProduct.map ρ.toLinearMap (LinearMap.id : A →ₗ[A] A) p) =
      ρ (TensorProduct.rid A (Localization.Away a) p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul z r => simp only [TensorProduct.map_tmul, TensorProduct.rid_tmul,
      LinearMap.id_apply, AlgHom.toLinearMap_apply, map_smul]

theorem moduleProjection_natural
    (ha : a ∈ 𝒜 da) (ha' : a' ∈ 𝒜 da') (hk : k ∈ 𝒜 dk)
    (hfactor : a' = a * k) (ρ : Localization.Away a →ₐ[A] Localization.Away a')
    (p : Localization.Away a ⊗[A] A) :
    moduleProjection 𝒜 ha'
        (TensorProduct.map ρ.toLinearMap (LinearMap.id : A →ₗ[A] A) p) =
      TensorProduct.map ρ.toLinearMap (LinearMap.id : A →ₗ[A] A)
        (moduleProjection 𝒜 ha p) := by
  apply (TensorProduct.rid A (Localization.Away a')).injective
  rw [rid_moduleProjection, rid_natural, rid_natural, rid_moduleProjection]
  exact degreeZeroEnd_naturality 𝒜 ha hk hfactor ha' ρ _

end ScalarModules

end CycleQ2GradedCechProjection


namespace CycleQ2GradedCechProjection

open scoped TensorProduct
open CycleQ2GradedLocalizationProjection CycleQ2MixedScalarLocalization
  CycleQ2GeometricFourOpenCech CycleQ2GeometricLocalizedCech

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

def principalTransition (f g : A) (h : f ∣ g) :
    Localization.Away f →ₐ[A] Localization.Away g where
  __ := IsLocalization.Away.lift f
    (isUnit_of_dvd_unit (map_dvd (algebraMap A (Localization.Away g)) h)
      (IsLocalization.Away.algebraMap_isUnit g))
  commutes' z := IsLocalization.Away.lift_eq _ _ z

def integerBiSystem {V : Finset (Fin 4) → Finset (Fin 4) → Type*}
    [∀ s t, AddCommGroup (V s t)] [∀ s t, Module A (V s t)]
    (D : BiSystem (R := A) V) : BiSystem (R := ℤ) V where
  left t := (D.left t).restrictScalars ℤ
  right s := (D.right s).restrictScalars ℤ
  interchange hs ht p := D.interchange hs ht p

theorem secondDescent_integer_iff {V : Finset (Fin 4) → Finset (Fin 4) → Type*}
    [∀ s t, AddCommGroup (V s t)] [∀ s t, Module A (V s t)]
    (D : BiSystem (R := A) V)
    (c : TwoCochain (fun s => V s ∅)) (d : TwoCochain (V ∅)) :
    (integerBiSystem D).SecondDescent c d ↔ D.SecondDescent c d := Iff.rfl

variable (a b : Fin 4 → A) (wa wb : Fin 4 → ℕ)
variable (ha : ∀ i, a i ∈ 𝒜 (wa i)) (hb : ∀ i, b i ∈ 𝒜 (wb i))

def moduleProjectionMorphism :
    SystemMorphism ((moduleSystem A a).restrictScalars ℤ)
      ((moduleSystem A a).restrictScalars ℤ) where
  app s := (moduleProjection 𝒜 (principalProduct_homogeneous 𝒜 a wa ha s)).toIntLinearMap
  naturality h := by
    apply LinearMap.ext
    intro z
    exact moduleProjection_natural 𝒜 (principalProduct_homogeneous 𝒜 a wa ha _)
      (principalProduct_homogeneous 𝒜 a wa ha _) (principalProduct_homogeneous 𝒜 a wa ha _)
      (principalProduct_factor a h) (ringRestriction a h) z

/-- The weight-zero endomorphism of the unchanged actual tensor-localized
common refinement. -/
def mixedProjectionMorphism :
    BiMorphism (integerBiSystem (mixedSystem A a b))
      (integerBiSystem (mixedSystem A a b)) where
  app s t := (mixedProjection 𝒜 (principalProduct_homogeneous 𝒜 a wa ha s)
    (principalProduct_homogeneous 𝒜 b wb hb t)).toIntLinearMap
  left_naturality {s s'} hs t := by
    apply LinearMap.ext
    intro z
    have hfactor : coverProduct a s' * coverProduct b t =
        (coverProduct a s * coverProduct b t) * coverProduct a (s' \ s) := by
      rw [principalProduct_factor a hs]
      ring
    let ρ := principalTransition (coverProduct a s * coverProduct b t)
      (coverProduct a s' * coverProduct b t) ⟨coverProduct a (s' \ s), hfactor⟩
    exact mixedProjection_natural 𝒜
      (principalProduct_homogeneous 𝒜 a wa ha s) (principalProduct_homogeneous 𝒜 b wb hb t)
      (principalProduct_homogeneous 𝒜 a wa ha s') (principalProduct_homogeneous 𝒜 b wb hb t)
      (principalProduct_homogeneous 𝒜 a wa ha (s' \ s)) hfactor ρ
      (ringRestriction a hs) (AlgHom.id A (RingAt b t)) z
  right_naturality s {t t'} ht := by
    apply LinearMap.ext
    intro z
    have hfactor : coverProduct a s * coverProduct b t' =
        (coverProduct a s * coverProduct b t) * coverProduct b (t' \ t) := by
      rw [principalProduct_factor b ht]
      ring
    let ρ := principalTransition (coverProduct a s * coverProduct b t)
      (coverProduct a s * coverProduct b t') ⟨coverProduct b (t' \ t), hfactor⟩
    have h := mixedProjection_natural 𝒜
      (principalProduct_homogeneous 𝒜 a wa ha s) (principalProduct_homogeneous 𝒜 b wb hb t)
      (principalProduct_homogeneous 𝒜 a wa ha s) (principalProduct_homogeneous 𝒜 b wb hb t')
      (principalProduct_homogeneous 𝒜 b wb hb (t' \ t)) hfactor ρ
      (AlgHom.id A (RingAt a s)) (ringRestriction b ht) z
    change mixedProjection 𝒜 (principalProduct_homogeneous 𝒜 a wa ha s)
        (principalProduct_homogeneous 𝒜 b wb hb t')
        (TensorProduct.map (ringRestriction b ht).toLinearMap
          (TensorProduct.map LinearMap.id LinearMap.id) z) =
      TensorProduct.map (ringRestriction b ht).toLinearMap
        (TensorProduct.map LinearMap.id LinearMap.id)
          (mixedProjection 𝒜 (principalProduct_homogeneous 𝒜 a wa ha s)
            (principalProduct_homogeneous 𝒜 b wb hb t) z) at h
    change mixedProjection 𝒜 (principalProduct_homogeneous 𝒜 a wa ha s)
        (principalProduct_homogeneous 𝒜 b wb hb t')
        (TensorProduct.map (ringRestriction b ht).toLinearMap
          (LinearMap.id : ModuleAt A a s →ₗ[A] ModuleAt A a s) z) =
      TensorProduct.map (ringRestriction b ht).toLinearMap
        (LinearMap.id : ModuleAt A a s →ₗ[A] ModuleAt A a s)
          (mixedProjection 𝒜 (principalProduct_homogeneous 𝒜 a wa ha s)
            (principalProduct_homogeneous 𝒜 b wb hb t) z)
    simpa only [TensorProduct.map_id] using h

theorem scalarTensorMorphism_eq_rid (s : Finset (Fin 4)) :
    (scalarTensorMorphism a).app s = (TensorProduct.rid A (RingAt a s)).toLinearMap := by
  ext z
  rfl

theorem scalarTensorMorphism_projection (s : Finset (Fin 4)) (z : ModuleAt A a s) :
    (scalarTensorMorphism a).app s ((moduleProjectionMorphism 𝒜 a wa ha).app s z) =
      principalProjection 𝒜 a wa ha s ((scalarTensorMorphism a).app s z) := by
  simp only [scalarTensorMorphism_eq_rid]
  exact rid_moduleProjection 𝒜 (principalProduct_homogeneous 𝒜 a wa ha s) z

end CycleQ2GradedCechProjection


namespace CycleQ2GradedCechProjection

open scoped TensorProduct
open CycleQ2GradedLocalizationProjection CycleQ2MixedScalarLocalization
  CycleQ2GeometricFourOpenCech CycleQ2GeometricLocalizedCech

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

def oneLocalizationEquiv : Localization.Away (1 : A) ≃ₐ[A] A :=
  (IsLocalization.atOne A (Localization.Away (1 : A))).symm

def removeLeftEmpty (a : A) :
    ScalarModule a 1 ≃ₗ[A] (Localization.Away a ⊗[A] A) :=
  (TensorProduct.congr oneLocalizationEquiv.toLinearEquiv
    (LinearEquiv.refl A (Localization.Away a ⊗[A] A))).trans
      (TensorProduct.lid A (Localization.Away a ⊗[A] A))

def removeRightEmpty (b : A) :
    ScalarModule 1 b ≃ₗ[A] (Localization.Away b ⊗[A] A) :=
  TensorProduct.congr (LinearEquiv.refl A (Localization.Away b))
    ((TensorProduct.congr oneLocalizationEquiv.toLinearEquiv (LinearEquiv.refl A A)).trans
      (TensorProduct.lid A A))

theorem removeLeftEmpty_toScalar (a : A) (p : ScalarModule a 1) :
    TensorProduct.rid A (Localization.Away a) (removeLeftEmpty a p) =
      principalTransition (a * 1) a (by simp) (scalarEquiv a 1 p) := by
  let ρ := principalTransition (a * 1) a (by simp)
  have hfirst (z : Localization.Away a) : ρ (firstFactor a 1 z) = z := by
    exact DFunLike.congr_fun (Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton (Submonoid.powers a))
      (ρ.comp (firstFactor a 1)) (AlgHom.id A (Localization.Away a))) z
  have hsecond (z : Localization.Away (1 : A)) :
      ρ (secondFactor a 1 z) = algebraMap A (Localization.Away a) (oneLocalizationEquiv z) := by
    exact DFunLike.congr_fun (Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton (Submonoid.powers (1 : A)))
      (ρ.comp (secondFactor a 1))
      ((Algebra.ofId A (Localization.Away a)).comp oneLocalizationEquiv.toAlgHom)) z
  change TensorProduct.rid A (Localization.Away a) (removeLeftEmpty a p) = ρ (scalarEquiv a 1 p)
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul z m =>
    induction m using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
    | tmul w r =>
      rw [scalarEquiv_tmul, map_smul, map_mul, hfirst, hsecond]
      change TensorProduct.rid A (Localization.Away a)
          (oneLocalizationEquiv z • (w ⊗ₜ[A] r)) =
        r • (algebraMap A (Localization.Away a) (oneLocalizationEquiv z) * w)
      rw [map_smul, TensorProduct.rid_tmul]
      simp only [Algebra.smul_def]
      ring

theorem removeRightEmpty_toScalar (b : A) (p : ScalarModule 1 b) :
    TensorProduct.rid A (Localization.Away b) (removeRightEmpty b p) =
      principalTransition (1 * b) b (by simp) (scalarEquiv 1 b p) := by
  let ρ := principalTransition (1 * b) b (by simp)
  have hsecond (z : Localization.Away b) : ρ (secondFactor 1 b z) = z := by
    exact DFunLike.congr_fun (Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton (Submonoid.powers b))
      (ρ.comp (secondFactor 1 b)) (AlgHom.id A (Localization.Away b))) z
  have hfirst (z : Localization.Away (1 : A)) :
      ρ (firstFactor 1 b z) = algebraMap A (Localization.Away b) (oneLocalizationEquiv z) := by
    exact DFunLike.congr_fun (Subsingleton.elim
      (h := IsLocalization.algHom_subsingleton (Submonoid.powers (1 : A)))
      (ρ.comp (firstFactor 1 b))
      ((Algebra.ofId A (Localization.Away b)).comp oneLocalizationEquiv.toAlgHom)) z
  change TensorProduct.rid A (Localization.Away b) (removeRightEmpty b p) = ρ (scalarEquiv 1 b p)
  induction p using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | tmul z m =>
    induction m using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.tmul_zero, map_zero]
    | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
    | tmul w r =>
      rw [scalarEquiv_tmul, map_smul, map_mul, hfirst, hsecond]
      change (oneLocalizationEquiv w * r) • z =
        r • (z * algebraMap A (Localization.Away b) (oneLocalizationEquiv w))
      simp only [Algebra.smul_def, map_mul]
      ring

theorem removeLeftEmpty_projection {a : A} {da : ℕ} (ha : a ∈ 𝒜 da)
    (p : ScalarModule a 1) :
    removeLeftEmpty a (mixedProjection 𝒜 ha (SetLike.one_mem_graded 𝒜) p) =
      moduleProjection 𝒜 ha (removeLeftEmpty a p) := by
  apply (TensorProduct.rid A (Localization.Away a)).injective
  rw [removeLeftEmpty_toScalar, scalarEquiv_mixedProjection, rid_moduleProjection,
    removeLeftEmpty_toScalar]
  exact (degreeZeroEnd_naturality 𝒜 (SetLike.mul_mem_graded ha (SetLike.one_mem_graded 𝒜))
    (SetLike.one_mem_graded 𝒜) (by simp) ha
    (principalTransition (a * 1) a (by simp)) (scalarEquiv a 1 p)).symm

theorem removeRightEmpty_projection {b : A} {db : ℕ} (hb : b ∈ 𝒜 db)
    (p : ScalarModule 1 b) :
    removeRightEmpty b (mixedProjection 𝒜 (SetLike.one_mem_graded 𝒜) hb p) =
      moduleProjection 𝒜 hb (removeRightEmpty b p) := by
  apply (TensorProduct.rid A (Localization.Away b)).injective
  rw [removeRightEmpty_toScalar, scalarEquiv_mixedProjection, rid_moduleProjection,
    removeRightEmpty_toScalar]
  exact (degreeZeroEnd_naturality 𝒜 (SetLike.mul_mem_graded (SetLike.one_mem_graded 𝒜) hb)
    (SetLike.one_mem_graded 𝒜) (by simp) hb
    (principalTransition (1 * b) b (by simp)) (scalarEquiv 1 b p)).symm

end CycleQ2GradedCechProjection


namespace CycleQ2GradedCechProjection

open scoped TensorProduct
open CycleQ2GradedLocalizationProjection CycleQ2MixedScalarLocalization
  CycleQ2GeometricFourOpenCech CycleQ2GeometricLocalizedCech

section IntegralCocycleMaps

variable {A : Type*} [CommRing A]
variable {V W : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module A (V s)]
variable [∀ s, AddCommGroup (W s)] [∀ s, Module A (W s)]

def integerMapCycle (D : RestrictionSystem A V)
    (f : SystemMorphism (D.restrictScalars ℤ) (D.restrictScalars ℤ))
    (c : TwoCocycles D) : TwoCocycles D :=
  ⟨f.map2 c.val, by
    change d2 (D.restrictScalars ℤ) (f.map2 c.val) = 0
    rw [← f.app_d2]
    change f.app Finset.univ (d2 D c.val) = 0
    rw [c.property, map_zero]⟩

theorem mapCycle_integerMapCycle {D : RestrictionSystem A V} {E : RestrictionSystem A W}
    (f : SystemMorphism (D.restrictScalars ℤ) (D.restrictScalars ℤ))
    (g : SystemMorphism (E.restrictScalars ℤ) (E.restrictScalars ℤ))
    (u : SystemMorphism D E)
    (h : ∀ s z, u.app s (f.app s z) = g.app s (u.app s z)) (c : TwoCocycles D) :
    u.mapCycle (integerMapCycle D f c) = integerMapCycle E g (u.mapCycle c) := by
  apply Subtype.ext
  apply Prod.ext <;> apply Prod.ext
  all_goals exact h _ _

end IntegralCocycleMaps

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (a b : Fin 4 → A) (wa wb : Fin 4 → ℕ)
variable (ha : ∀ i, a i ∈ 𝒜 (wa i)) (hb : ∀ i, b i ∈ 𝒜 (wb i))

def moduleProjectedCocycle (c : TwoCocycles (moduleSystem A a)) :
    TwoCocycles (moduleSystem A a) :=
  integerMapCycle (moduleSystem A a) (moduleProjectionMorphism 𝒜 a wa ha) c

theorem mixedLeftEmpty_projection (s : Finset (Fin 4))
    (z : MixedModule A a b s ∅) :
    (mixedLeftEmpty A a b).app s
        ((mixedProjectionMorphism 𝒜 a b wa wb ha hb).app s ∅ z) =
      (moduleProjectionMorphism 𝒜 a wa ha).app s ((mixedLeftEmpty A a b).app s z) := by
  change removeLeftEmpty (coverProduct a s)
      (mixedProjection 𝒜 (principalProduct_homogeneous 𝒜 a wa ha s)
        (SetLike.one_mem_graded 𝒜) z) =
    moduleProjection 𝒜 (principalProduct_homogeneous 𝒜 a wa ha s)
      (removeLeftEmpty (coverProduct a s) z)
  exact removeLeftEmpty_projection 𝒜 _ z

theorem mixedRightEmpty_projection (t : Finset (Fin 4))
    (z : MixedModule A a b ∅ t) :
    (mixedRightEmpty A a b).app t
        ((mixedProjectionMorphism 𝒜 a b wa wb ha hb).app ∅ t z) =
      (moduleProjectionMorphism 𝒜 b wb hb).app t ((mixedRightEmpty A a b).app t z) := by
  change removeRightEmpty (coverProduct b t)
      (mixedProjection 𝒜 (SetLike.one_mem_graded 𝒜)
        (principalProduct_homogeneous 𝒜 b wb hb t) z) =
    moduleProjection 𝒜 (principalProduct_homogeneous 𝒜 b wb hb t)
      (removeRightEmpty (coverProduct b t) z)
  exact removeRightEmpty_projection 𝒜 _ z

/-- The same principal common-refinement staircase survives the canonical
weight-zero projection. The new primitives are the actual images of the
old ones under `mixedProjectionMorphism`. -/
theorem principalSecondDescent_project
    {c : TwoCocycles (moduleSystem A a)} {d : TwoCocycles (moduleSystem A b)}
    (hcd : PrincipalSecondDescent A a b c d) :
    PrincipalSecondDescent A a b
      (moduleProjectedCocycle 𝒜 a wa ha c) (moduleProjectedCocycle 𝒜 b wb hb d) := by
  obtain ⟨c', d', hc', hd', hmiddle⟩ := hcd
  let D := mixedSystem A a b
  let φ := mixedProjectionMorphism 𝒜 a b wa wb ha hb
  refine ⟨integerMapCycle (D.left ∅) (φ.left ∅) c',
    integerMapCycle (D.right ∅) (φ.right ∅) d', ?_, ?_, ?_⟩
  · rw [mapCycle_integerMapCycle (φ.left ∅) (moduleProjectionMorphism 𝒜 a wa ha)
      (mixedLeftEmpty A a b) (mixedLeftEmpty_projection 𝒜 a b wa wb ha hb), hc']
    rfl
  · rw [mapCycle_integerMapCycle (φ.right ∅) (moduleProjectionMorphism 𝒜 b wb hb)
      (mixedRightEmpty A a b) (mixedRightEmpty_projection 𝒜 a b wa wb ha hb), hd']
    rfl
  · change (integerBiSystem D).SecondDescent ((φ.left ∅).map2 c'.val)
      ((φ.right ∅).map2 d'.val)
    exact φ.map_secondDescent hmiddle

end CycleQ2GradedCechProjection


namespace CycleQ2GradedCechProjection

open CycleQ2GeometricFourOpenCech CycleQ2GeometricLocalizedCech
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricCartierCech CycleQ2CartierSurfaceGrading

def cartierProjectedCocycle (r θ : ℂ) (c : TwoCocycles (surfaceSystem r θ)) :
    TwoCocycles (surfaceSystem r θ) :=
  integerMapCycle (surfaceSystem r θ) (cartierProjectionMorphism r θ) c

theorem surfaceTensor_projection (r : ℂ) (s : Finset (Fin 4))
    (z : ModuleAt (SurfaceRing r 1) (coverElement r 1) s) :
    (surfaceTensorMorphism r 1).app s
        ((moduleProjectionMorphism (surfaceGrade r 1) (coverElement r 1) coverDegree
          (coverElement_mem_grade r 1)).app s z) =
      (cartierProjectionMorphism r 1).app s ((surfaceTensorMorphism r 1).app s z) :=
  scalarTensorMorphism_projection (surfaceGrade r 1) (coverElement r 1) coverDegree
    (coverElement_mem_grade r 1) s z

/-- The canonical projection preserves the original `CartierCoordinateDescent`
relation, through its unchanged tensor and empty-localization comparisons. -/
theorem cartierCoordinateDescent_project (r : ℂ)
    {c : TwoCocycles (surfaceSystem r 1)} {d : TwoCocycles (coordinateScalarSystem r)}
    (hcd : CartierCoordinateDescent r c d) :
    CartierCoordinateDescent r (cartierProjectedCocycle r 1 c) (coordinateProjectedCocycle r d) := by
  obtain ⟨c', d', hc', hmiddle, hd'⟩ := hcd
  refine ⟨moduleProjectedCocycle (surfaceGrade r 1) (coverElement r 1) coverDegree
      (coverElement_mem_grade r 1) c',
    moduleProjectedCocycle (surfaceGrade r 1) (coordinateCover r) (fun _ => 1)
      (coordinateCover_homogeneous r) d', ?_, ?_, ?_⟩
  · change (surfaceTensorMorphism r 1).mapCycle
      (integerMapCycle _ (moduleProjectionMorphism (surfaceGrade r 1)
        (coverElement r 1) coverDegree (coverElement_mem_grade r 1)) c') = _
    rw [mapCycle_integerMapCycle _ (cartierProjectionMorphism r 1)
      (surfaceTensorMorphism r 1) (surfaceTensor_projection r), hc']
    rfl
  · exact principalSecondDescent_project (surfaceGrade r 1) (coverElement r 1)
      (coordinateCover r) coverDegree (fun _ => 1)
      (coverElement_mem_grade r 1) (coordinateCover_homogeneous r) hmiddle
  · change (scalarTensorMorphism (coordinateCover r)).mapCycle
      (integerMapCycle _ (moduleProjectionMorphism (surfaceGrade r 1)
        (coordinateCover r) (fun _ => 1) (coordinateCover_homogeneous r)) d') = _
    rw [mapCycle_integerMapCycle _
      (principalProjectionMorphism (surfaceGrade r 1) (coordinateCover r) (fun _ => 1)
        (coordinateCover_homogeneous r))
      (scalarTensorMorphism (coordinateCover r))
      (scalarTensorMorphism_projection (surfaceGrade r 1) (coordinateCover r) (fun _ => 1)
        (coordinateCover_homogeneous r)), hd']
    rfl

theorem literalCartier_projectedCocycle_eq :
    cartierProjectedCocycle 57 1
        (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0) =
      cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0 :=
  Subtype.ext literalCartier_projection_fixed

theorem literal_projected_descent (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57
      (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0) d) :
    CartierCoordinateDescent 57
      (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0) (coordinateProjectedCocycle 57 d) := by
  have h := cartierCoordinateDescent_project 57 hcd
  rw [literalCartier_projectedCocycle_eq] at h
  exact h

theorem literal_projected_class_ne_zero (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57
      (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0) d) :
    classOf (coordinateScalarSystem 57) (coordinateProjectedCocycle 57 d) ≠ 0 := by
  intro hz
  exact literal_cartierClass_ne_zero
    ((literal_projected_descent d hcd).reflects_class_zero 57 (by norm_num) hz)

theorem literal_projected_cubic_ne_zero (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57
      (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0) d) :
    surfaceQuotient 57 1 detectorCubic •
      classOf (coordinateScalarSystem 57) (coordinateProjectedCocycle 57 d) ≠ 0 :=
  literal_descent_cubic_ne_zero (coordinateProjectedCocycle 57 d) (literal_projected_descent d hcd)

/-- An original coordinate descendant and its canonical weight-zero part.
The latter retains the exact original descent, is nonzero, and remains
nonzero after multiplication by the unchanged detector cubic. -/
theorem literal_weightZero_coordinate_descent :
    ∃ d : TwoCocycles (coordinateScalarSystem 57),
      CartierCoordinateDescent 57 (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0) d ∧
      CartierCoordinateDescent 57 (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0)
        (coordinateProjectedCocycle 57 d) ∧
      classOf (coordinateScalarSystem 57) (coordinateProjectedCocycle 57 d) ≠ 0 ∧
      surfaceQuotient 57 1 detectorCubic •
        classOf (coordinateScalarSystem 57) (coordinateProjectedCocycle 57 d) ≠ 0 := by
  obtain ⟨d, hcd, _⟩ := literal_cartier_coordinate_descent_nonzero
  exact ⟨d, hcd, literal_projected_descent d hcd, literal_projected_class_ne_zero d hcd,
    literal_projected_cubic_ne_zero d hcd⟩

end CycleQ2GradedCechProjection

#print axioms CycleQ2GradedCechProjection.principalSecondDescent_project
#print axioms CycleQ2GradedCechProjection.literal_weightZero_coordinate_descent

namespace CycleQ2GradedCechProjection

open CycleQ2GeometricFourOpenCech CycleQ2CechStaircaseSign

variable {R : Type*} [CommRing R]
variable {V : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]

theorem evalTwo_neg (D : RestrictionSystem R V) (s : Finset (Fin 4))
    (i j k : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) (q : TwoCochain V) :
    evalTwo D s i j k hi hj hk (-q) = -evalTwo D s i j k hi hj hk q := by
  let f : SystemMorphism D D := {
    app := fun _ => -LinearMap.id
    naturality := fun _ => by ext z; simp }
  exact evalTwo_map2 f s i j k hi hj hk q

variable {B C : Finset (Fin 4) → Finset (Fin 4) → Type*}
variable [∀ s t, AddCommGroup (B s t)] [∀ s t, Module R (B s t)]
variable [∀ s t, AddCommGroup (C s t)] [∀ s t, Module R (C s t)]

theorem verticalValue_neg (D : BiSystem (R := R) B)
    (d : TwoCochain (B ∅)) (s t : Finset (Fin 4))
    (i j k : Fin 4) (hi : i ∈ t) (hj : j ∈ t) (hk : k ∈ t) :
    verticalValue D (-d) s t i j k hi hj hk = -verticalValue D d s t i j k hi hj hk := by
  simp only [verticalValue, evalTwo_neg, map_neg]

private theorem pair_subset {s : Finset (Fin 4)} {i j : Fin 4}
    (hi : i ∈ s) (hj : j ∈ s) : {i,j} ⊆ s := by
  simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hi hj

/-- The transformed diagonal primitive is built from the images of the
original `x` and `y`. Its boundary compares the first projected cocycle
with the **negative** of the second, in the ordinary Čech convention. -/
theorem BiMorphism.projected_signed_diagonal
    {D : BiSystem (R := R) B} {E : BiSystem (R := R) C} (φ : BiMorphism D E)
    (c : TwoCochain (fun s => B s ∅)) (d : TwoCochain (B ∅))
    (x : OneCochain (fun s => ZeroCochain (B s)))
    (y : ZeroCochain (fun s => OneCochain (B s)))
    (hx : d1 D.row0 x = D.horizontalAugmentation.map2 c)
    (hy : d0 D.row1 y = D.vertical0.map1 x)
    (hd : augmentation D.row2 d = D.vertical1.map0 y)
    (s t : Finset (Fin 4)) (u v w : Fin 4 × Fin 4)
    (hu : u.1 ∈ s) (hv : v.1 ∈ s) (hw : w.1 ∈ s)
    (hu' : u.2 ∈ t) (hv' : v.2 ∈ t) (hw' : w.2 ∈ t) :
    biRes E (pair_subset hv hw) (pair_subset hv' hw')
        (diagonalEdge E (φ.row0.map1 x) (φ.row1.map0 y) v w) -
      biRes E (pair_subset hu hw) (pair_subset hu' hw')
        (diagonalEdge E (φ.row0.map1 x) (φ.row1.map0 y) u w) +
      biRes E (pair_subset hu hv) (pair_subset hu' hv')
        (diagonalEdge E (φ.row0.map1 x) (φ.row1.map0 y) u v) =
      horizontalValue E ((φ.left ∅).map2 c) s t u.1 v.1 w.1 hu hv hw -
        verticalValue E (-((φ.right ∅).map2 d)) s t u.2 v.2 w.2 hu' hv' hw' := by
  obtain ⟨hx', hy', hd'⟩ := φ.secondDescent_data c d x y hx hy hd
  rw [verticalValue_neg, sub_neg_eq_add]
  exact diagonal_boundary E (φ.row0.map1 x) (φ.row1.map0 y)
    ((φ.left ∅).map2 c) ((φ.right ∅).map2 d) hx' hy' hd'
    s t u v w hu hv hw hu' hv' hw'

end CycleQ2GradedCechProjection

#print axioms CycleQ2GradedCechProjection.BiMorphism.projected_signed_diagonal
#print axioms CycleQ2GradedCechProjection.cartierCoordinateDescent_project
#print axioms CycleQ2GradedCechProjection.literal_weightZero_coordinate_descent
