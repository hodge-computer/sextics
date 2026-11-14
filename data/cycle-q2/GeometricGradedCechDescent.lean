import Proposal.GeometricLiteralSurface
import Proposal.GeometricCoordinateH2
import Proposal.GeometricCartierNormalLift
import Proposal.GeometricIntrinsicNormal
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Abelian.ShortExact

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

end -- original noncomputable section

/-!
## Actual regular Cartier ideals and the intrinsic short exact sequence

The continuation identifies the original curve ideal on twelve actual
projective affine charts, proves its displayed generator regular, and
retains the original structure-map reduction. The actual intrinsic
inverse-ideal short complex is exact on affine schemes with this regular
principal kernel. The cartesian chart squares transport the three actual
maps to every principal subopen. These opens form a basis of the literal
surface, giving short exactness of both the module-sheaf complex and its
underlying additive complex. Evaluation of the genuine connecting morphism
on the original normal class remains a separate obligation.
-/

section RegularPrincipalHomSequence

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2RegularPrincipalHomSequence

open CycleQ2GeometricCartierNormalLift

variable {R : Type*} [CommRing R] (I : Ideal R)

def scalarInclusion : R →ₗ[R] (I →ₗ[R] R) where
  toFun a := a • I.subtype
  map_add' a b := add_smul a b I.subtype
  map_smul' a b := mul_smul a b I.subtype

def quotientReduction : (I →ₗ[R] R) →ₗ[R] (I →ₗ[R] R ⧸ I) where
  toFun f := (Ideal.Quotient.mkₐ R I).toLinearMap.comp f
  map_add' f g := by ext x; exact map_add (Ideal.Quotient.mk I) (f x) (g x)
  map_smul' a f := by ext x; exact (Ideal.Quotient.mkₐ R I).toLinearMap.map_smul a (f x)

theorem scalarInclusion_apply (a : R) (x : I) : scalarInclusion I a x = a * (x : R) := rfl

theorem quotientReduction_apply (f : I →ₗ[R] R) (x : I) :
    quotientReduction I f x = Ideal.Quotient.mk I (f x) := rfl

theorem quotientReduction_scalarInclusion (a : R) :
    quotientReduction I (scalarInclusion I a) = 0 := by
  ext x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact I.mul_mem_left a x.property

variable (b : R) (hb : IsSMulRegular R b) (hI : I = Ideal.span ({b} : Set R))

theorem principalIdealEquiv_one_coe :
    (principalIdealEquiv I b hb hI 1 : R) = b := one_mul b

/-- Equality of homomorphisms from the actual regular principal ideal
is detected on its original generator. -/
theorem principalHom_ext {Q : Type*} [AddCommGroup Q] [Module R Q]
    {f g : I →ₗ[R] Q}
    (h : f (principalIdealEquiv I b hb hI 1) =
      g (principalIdealEquiv I b hb hI 1)) : f = g := by
  ext x
  obtain ⟨a,rfl⟩ := (principalIdealEquiv I b hb hI).surjective x
  have ha : principalIdealEquiv I b hb hI a =
      a • principalIdealEquiv I b hb hI 1 := by
    simpa only [smul_eq_mul, mul_one] using
      (principalIdealEquiv I b hb hI).map_smul a (1 : R)
  rw [ha, map_smul, map_smul, h]

include b hb hI

theorem scalarInclusion_injective : Function.Injective (scalarInclusion I) := by
  intro a c hac
  have h := congrArg (fun f : I →ₗ[R] R => f (principalIdealEquiv I b hb hI 1)) hac
  rw [scalarInclusion_apply, scalarInclusion_apply, principalIdealEquiv_one_coe] at h
  apply hb
  simpa only [smul_eq_mul, mul_comm] using h

/-- Every normal functional lifts through the actual quotient map. -/
theorem quotientReduction_surjective : Function.Surjective (quotientReduction I) := by
  intro f
  obtain ⟨a,ha⟩ := Ideal.Quotient.mk_surjective (f (principalIdealEquiv I b hb hI 1))
  refine ⟨a • inverseIdealGenerator I b hb hI, ?_⟩
  apply principalHom_ext I b hb hI
  change Ideal.Quotient.mk I
    (a * (principalIdealEquiv I b hb hI).symm (principalIdealEquiv I b hb hI 1)) = _
  rw [LinearEquiv.symm_apply_apply, mul_one]
  exact ha

/-- The scalar kernel and quotient reduction are exact for the genuine
Hom modules of a regular principal ideal. -/
theorem scalar_quotient_exact : Function.Exact (scalarInclusion I) (quotientReduction I) := by
  intro f
  constructor
  · intro hf
    have hz : Ideal.Quotient.mk I (f (principalIdealEquiv I b hb hI 1)) = 0 :=
      congrArg (fun g : I →ₗ[R] R ⧸ I => g (principalIdealEquiv I b hb hI 1)) hf
    have hm := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hm' : f (principalIdealEquiv I b hb hI 1) ∈ Ideal.span ({b} : Set R) :=
      (le_of_eq hI) hm
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hm'
    refine ⟨a, principalHom_ext I b hb hI ?_⟩
    rw [scalarInclusion_apply, principalIdealEquiv_one_coe]
    exact ha
  · rintro ⟨a,rfl⟩
    exact quotientReduction_scalarInclusion I a

end CycleQ2RegularPrincipalHomSequence

#print axioms CycleQ2RegularPrincipalHomSequence.scalarInclusion_injective
#print axioms CycleQ2RegularPrincipalHomSequence.quotientReduction_surjective
#print axioms CycleQ2RegularPrincipalHomSequence.scalar_quotient_exact

end -- component noncomputable section
end RegularPrincipalHomSequence

section RegularPrincipalAlgebraSequence

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2RegularPrincipalHomSequence

open CycleQ2GeometricCartierNormalLift

variable {R : Type*} [CommRing R] (I : Ideal R)
  (B : Type*) [CommRing B] [Algebra R B]

/-- Reduction along the actual algebra map, with its existing scalar
action. This version does not replace the target ring by a quotient. -/
def algebraReduction : (I →ₗ[R] R) →ₗ[R] (I →ₗ[R] B) where
  toFun f := (Algebra.linearMap R B).comp f
  map_add' f g := by ext x; exact map_add (algebraMap R B) (f x) (g x)
  map_smul' a f := by ext x; exact (Algebra.linearMap R B).map_smul a (f x)

theorem algebraReduction_apply (f : I →ₗ[R] R) (x : I) :
    algebraReduction I B f x = algebraMap R B (f x) := rfl

theorem algebraReduction_scalarInclusion (hker : I = RingHom.ker (algebraMap R B)) (a : R) :
    algebraReduction I B (scalarInclusion I a) = 0 := by
  ext x
  change algebraMap R B (a * (x : R)) = 0
  have hx : algebraMap R B (x : R) = 0 := (le_of_eq hker) x.property
  rw [map_mul, hx, mul_zero]

theorem algebraReduction_surjective (b : R) (hb : IsSMulRegular R b)
    (hp : I = Ideal.span ({b} : Set R)) (hs : Function.Surjective (algebraMap R B)) :
    Function.Surjective (algebraReduction I B) := by
  intro f
  obtain ⟨a,ha⟩ := hs (f (principalIdealEquiv I b hb hp 1))
  refine ⟨a • inverseIdealGenerator I b hb hp, ?_⟩
  apply principalHom_ext I b hb hp
  change algebraMap R B
    (a * (principalIdealEquiv I b hb hp).symm (principalIdealEquiv I b hb hp 1)) = _
  rw [LinearEquiv.symm_apply_apply, mul_one]
  exact ha

theorem scalar_algebra_exact (b : R) (hb : IsSMulRegular R b)
    (hp : I = Ideal.span ({b} : Set R))
    (hker : I = RingHom.ker (algebraMap R B)) :
    Function.Exact (scalarInclusion I) (algebraReduction I B) := by
  intro f
  constructor
  · intro hf
    have hz : algebraMap R B (f (principalIdealEquiv I b hb hp 1)) = 0 :=
      congrArg (fun g : I →ₗ[R] B => g (principalIdealEquiv I b hb hp 1)) hf
    have hm : f (principalIdealEquiv I b hb hp 1) ∈ I := (le_of_eq hker.symm) hz
    have hm' : f (principalIdealEquiv I b hb hp 1) ∈ Ideal.span ({b} : Set R) :=
      (le_of_eq hp) hm
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hm'
    refine ⟨a, principalHom_ext I b hb hp ?_⟩
    rw [scalarInclusion_apply, principalIdealEquiv_one_coe]
    exact ha
  · rintro ⟨a,rfl⟩
    exact algebraReduction_scalarInclusion I B hker a

end CycleQ2RegularPrincipalHomSequence

#print axioms CycleQ2RegularPrincipalHomSequence.algebraReduction_surjective
#print axioms CycleQ2RegularPrincipalHomSequence.scalar_algebra_exact

end -- component noncomputable section
end RegularPrincipalAlgebraSequence

section ActualProjectiveCartierIdeal

/-!
# Actual regular principal ideal charts for the literal projective curve

The canonical degree-zero projection is linear over genuine homogeneous
fractions. Consequently it contracts a principal ideal generated by such
a fraction to the same principal ideal in the homogeneous localization.

On the actual Cartier-by-coordinate refinement, this proves that the
literal curve ideal is generated by f2/x_j^2 or f1/x_j^2 on the two
cofactor opens, and by one on the two opens disjoint from the curve.
The generators are regular by the original monic regular-sequence proof.
For r and theta nonzero the twelve actual opens cover the whole surface.

The kernel and the surjective quotient map are transported to the actual
scheme section rings. Their scalar/inverse-ideal/normal Hom sequence is
exact on each displayed affine chart, with reduction by the actual
structure-map component. Passing this algebra to the global intrinsic
Hom sheaves and identifying its derived connecting map are further steps.
-/


section DegreeZeroIdealCore

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2GradedLocalizationProjection

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

theorem fraction_mul (f : A) (n m : ℕ) (a b : A) :
    fraction f (n + m) (a * b) = fraction f n a * fraction f m b := by
  unfold fraction
  rw [show powerDenominator f (n + m) =
    powerDenominator f n * powerDenominator f m from Subtype.ext (pow_add f n m)]
  exact IsLocalization.mk'_mul (Localization.Away f) a b
    (powerDenominator f n) (powerDenominator f m)

variable {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)

/-- The genuine weight-zero projection is linear over the degree-zero
homogeneous localization, including when the original ring has zero divisors. -/
theorem degreeZero_mul_homogeneous (h : HomogeneousLocalization.Away 𝒜 f)
    (z : Localization.Away f) :
    degreeZero 𝒜 hf (h.val * z) = h * degreeZero 𝒜 hf z := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf h
  obtain ⟨m, b, rfl⟩ := exists_fraction f z
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  change degreeZero 𝒜 hf (fraction f n a * fraction f m b) = _
  rw [← fraction_mul, degreeZero_fraction, degreeZero_fraction]
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, projectedFraction_val,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  change fraction f (n + m) (GradedRing.proj 𝒜 ((n + m) * d) (a * b)) =
    fraction f n a * fraction f m (GradedRing.proj 𝒜 (m * d) b)
  rw [← fraction_mul]
  congr 1
  change (DirectSum.decompose 𝒜 (a * b) ((n + m) * d) : A) =
    a * DirectSum.decompose 𝒜 b (m * d)
  rw [Nat.add_mul]
  exact DirectSum.coe_decompose_mul_add_of_left_mem 𝒜 ha

theorem degreeZero_homogeneous_mul (z : Localization.Away f)
    (h : HomogeneousLocalization.Away 𝒜 f) :
    degreeZero 𝒜 hf (z * h.val) = degreeZero 𝒜 hf z * h := by
  rw [mul_comm z, degreeZero_mul_homogeneous, mul_comm h]

include hf in
/-- Contracting the ordinary principal ideal of an actual degree-zero
element gives its principal ideal in the genuine projective chart ring. -/
theorem principalIdeal_comap_val (h : HomogeneousLocalization.Away 𝒜 f) :
    (Ideal.span ({h.val} : Set (Localization.Away f))).comap
      (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)) =
        Ideal.span ({h} : Set (HomogeneousLocalization.Away 𝒜 f)) := by
  ext x
  constructor
  · intro hx
    change x.val ∈ Ideal.span ({h.val} : Set (Localization.Away f)) at hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨degreeZero 𝒜 hf a, ?_⟩
    have he := congrArg (degreeZero 𝒜 hf) ha
    rw [degreeZero_homogeneous_mul, degreeZero_val] at he
    exact he
  · intro hx
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hx
    change x.val ∈ Ideal.span ({h.val} : Set (Localization.Away f))
    apply Ideal.mem_span_singleton'.mpr
    exact ⟨a.val, (HomogeneousLocalization.val_mul a h).symm.trans
      (congrArg HomogeneousLocalization.val ha)⟩

/-- Regularity of the same element in the ordinary localization descends
along the injective homogeneous-localization inclusion. -/
theorem isSMulRegular_of_val (h : HomogeneousLocalization.Away 𝒜 f)
    (hh : IsSMulRegular (Localization.Away f) h.val) :
    IsSMulRegular (HomogeneousLocalization.Away 𝒜 f) h := by
  intro x y hxy
  change h * x = h * y at hxy
  apply HomogeneousLocalization.val_injective
  apply hh
  change h.val * x.val = h.val * y.val
  simpa only [HomogeneousLocalization.val_mul] using
    congrArg HomogeneousLocalization.val hxy

section NormalizedElement

variable {a z b : A} {e k : ℕ}
variable (ha : a ∈ 𝒜 e) (hz : z ∈ 𝒜 1) (hb : b ∈ 𝒜 k)

/-- The actual degree-zero fraction `b / z^k` on `D₊(a) ∩ D₊(z)`.
Its presentation uses only powers of the homogeneous product denominator. -/
def normalizedElement : HomogeneousLocalization.Away 𝒜 (a * z) :=
  HomogeneousLocalization.Away.mk 𝒜 (SetLike.mul_mem_graded ha hz) k
    (b * a ^ k) (by
      simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_add, Nat.mul_one, Nat.add_comm] using
        SetLike.mul_mem_graded hb (SetLike.pow_mem_graded k ha))

theorem normalizedElement_val_mul :
    (normalizedElement 𝒜 ha hz hb).val *
      (algebraMap A (Localization.Away (a * z)) z) ^ k =
        algebraMap A (Localization.Away (a * z)) b := by
  have hua : IsUnit (algebraMap A (Localization.Away (a * z)) a) :=
    IsLocalization.Away.isUnit_of_dvd (a * z) ⟨z, rfl⟩
  apply (hua.pow k).mul_right_cancel
  have hspec := IsLocalization.mk'_spec (Localization.Away (a * z))
    (b * a ^ k) (powerDenominator (a * z) k)
  change fraction (a * z) k (b * a ^ k) *
    algebraMap A (Localization.Away (a * z)) ((a * z) ^ k) = _ at hspec
  simp only [normalizedElement, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk']
  change (fraction (a * z) k (b * a ^ k) *
    algebraMap A (Localization.Away (a * z)) z ^ k) *
      algebraMap A (Localization.Away (a * z)) a ^ k = _
  simpa only [map_mul, map_pow, mul_pow, mul_assoc, mul_comm, mul_left_comm] using hspec

theorem normalizedElement_span_val :
    Ideal.span ({(normalizedElement 𝒜 ha hz hb).val} :
      Set (Localization.Away (a * z))) =
        Ideal.span ({algebraMap A (Localization.Away (a * z)) b} :
          Set (Localization.Away (a * z))) := by
  have huz : IsUnit (algebraMap A (Localization.Away (a * z)) z) :=
    IsLocalization.Away.isUnit_of_dvd (a * z) ⟨a, mul_comm a z⟩
  rw [← normalizedElement_val_mul 𝒜 ha hz hb,
    Ideal.span_singleton_mul_right_unit (huz.pow k)]

theorem normalizedElement_regular
    (hbreg : IsSMulRegular (Localization.Away (a * z))
      (algebraMap A (Localization.Away (a * z)) b)) :
    IsSMulRegular (HomogeneousLocalization.Away 𝒜 (a * z))
      (normalizedElement 𝒜 ha hz hb) := by
  apply isSMulRegular_of_val
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro x hx
  apply hbreg.right_eq_zero_of_smul
  change algebraMap A (Localization.Away (a * z)) b * x = 0
  change (normalizedElement 𝒜 ha hz hb).val * x = 0 at hx
  rw [← normalizedElement_val_mul 𝒜 ha hz hb]
  calc
    ((normalizedElement 𝒜 ha hz hb).val *
        algebraMap A (Localization.Away (a * z)) z ^ k) * x =
      algebraMap A (Localization.Away (a * z)) z ^ k *
        ((normalizedElement 𝒜 ha hz hb).val * x) := by ring
    _ = 0 := by rw [hx, mul_zero]

end NormalizedElement

end CycleQ2GradedLocalizationProjection

#print axioms CycleQ2GradedLocalizationProjection.degreeZero_mul_homogeneous
#print axioms CycleQ2GradedLocalizationProjection.principalIdeal_comap_val
#print axioms CycleQ2GradedLocalizationProjection.isSMulRegular_of_val

namespace CycleQ2ProjectiveCartierIdeal

open MvPolynomial HomogeneousLocalization
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricSurfaceCoordinates CycleQ2CartierSurfaceGrading
  CycleQ2GradedLocalizationProjection CycleQ2GradedCechProjection
open CycleQ2GeometricLiteralSurface (curveGradedMap curveChartMap_mk_eq_zero_iff
  curveToSurface curveToSurface_chart_ker projChartSectionsEquiv)

/-- This is the actual homogeneous-localization kernel of the literal
surface-to-curve map, not an independently chosen homogeneous ideal. -/
theorem curveChartKernel_eq_comap (r θ : ℂ) (s : SurfaceRing r θ) {d : ℕ}
    (hs : s ∈ surfaceGrade r θ d) :
    RingHom.ker (Away.map (curveGradedMap r θ) s) =
      ((curveIdealOnSurface r θ).map
        (algebraMap (SurfaceRing r θ) (Localization.Away s))).comap
        (algebraMap (Away (surfaceGrade r θ) s) (Localization.Away s)) := by
  ext x
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (surfaceGrade r θ) hs x
  change Away.map (curveGradedMap r θ) s
    (Away.mk (surfaceGrade r θ) hs n p hp) = 0 ↔ _
  rw [curveChartMap_mk_eq_zero_iff]
  change (∃ k : ℕ, s ^ k * p ∈ curveIdealOnSurface r θ) ↔
    (Away.mk (surfaceGrade r θ) hs n p hp).val ∈
      (curveIdealOnSurface r θ).map
        (algebraMap (SurfaceRing r θ) (Localization.Away s))
  rw [Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_mem_map_algebraMap_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨s ^ k, ⟨k, rfl⟩, hk⟩
  · rintro ⟨t, ⟨k, rfl⟩, hk⟩
    exact ⟨k, hk⟩

end CycleQ2ProjectiveCartierIdeal

#print axioms CycleQ2GradedLocalizationProjection.normalizedElement_val_mul
#print axioms CycleQ2GradedLocalizationProjection.normalizedElement_regular
#print axioms CycleQ2ProjectiveCartierIdeal.curveChartKernel_eq_comap


end
end DegreeZeroIdealCore


section ActualProjectiveIdealCharts

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ProjectiveCartierIdeal

open MvPolynomial HomogeneousLocalization
  CycleQ2ConormalJacobian CycleQ2NormalConnecting CycleQ2SeedTrace
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricSurfaceCoordinates CycleQ2CartierSurfaceGrading
  CycleQ2GradedLocalizationProjection CycleQ2GradedCechProjection
open CycleQ2GeometricLiteralSurface (curveGradedMap curveChartMap_mk_eq_zero_iff
  curveToSurface curveToSurface_chart_ker projChartSectionsEquiv
  gradedAwayMap_surjective curveGradedMap_homogeneous_surjective
  projMap_app_basicOpen curve_irrelevant_le)

def refinedDenominator (r θ : ℂ) (i : Fin 4) (j : Fin 3) : SurfaceRing r θ :=
  coverElement r θ i * coordinateElement r θ j

theorem refinedDenominator_homogeneous (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    refinedDenominator r θ i j ∈ surfaceGrade r θ (coverDegree i + 1) :=
  SetLike.mul_mem_graded (coverElement_mem_grade r θ i)
    (coordinateElement_homogeneous r θ j)

abbrev RefinedRing (r θ : ℂ) (i : Fin 4) (j : Fin 3) :=
  Away (surfaceGrade r θ) (refinedDenominator r θ i j)

def refinedIdeal (r θ : ℂ) (i : Fin 4) (j : Fin 3) : Ideal (RefinedRing r θ i j) :=
  RingHom.ker (Away.map (curveGradedMap r θ) (refinedDenominator r θ i j))

/-- The actual generator is `f₂/x_j²` or `f₁/x_j²` on the two cofactor
opens. On the complementary opens the curve is empty and its ideal is the unit ideal. -/
def refinedGenerator (r θ : ℂ) (i : Fin 4) (j : Fin 3) : RefinedRing r θ i j := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact normalizedElement (surfaceGrade r θ) (coverElement_mem_grade r θ 0)
      (coordinateElement_homogeneous r θ j)
      (surfaceQuotient_mem_grade r θ originalF2_homogeneous)
  · refine Fin.cases ?_ (fun _ => 1) i
    exact normalizedElement (surfaceGrade r θ) (coverElement_mem_grade r θ 1)
      (coordinateElement_homogeneous r θ j)
      (surfaceQuotient_mem_grade r θ (originalF1_homogeneous r))

theorem localizedIdeal_principal_first (r θ : ℂ) (z : SurfaceRing r θ) :
    (curveIdealOnSurface r θ).map (algebraMap (SurfaceRing r θ)
      (Localization.Away (surfaceQuotient r θ (originalG1 r) * z))) =
        Ideal.span ({algebraMap (SurfaceRing r θ)
          (Localization.Away (surfaceQuotient r θ (originalG1 r) * z))
          (surfaceQuotient r θ originalF2)} : Set _) := by
  let L := Localization.Away (surfaceQuotient r θ (originalG1 r) * z)
  let φ : WeightedPoly →+* L := (algebraMap (SurfaceRing r θ) L).comp (surfaceQuotient r θ)
  have hu : IsUnit (φ (originalG1 r)) :=
    IsLocalization.Away.isUnit_of_dvd (surfaceQuotient r θ (originalG1 r) * z) ⟨z, rfl⟩
  rw [curveIdealOnSurface, CycleQ2GeometricRelativeConormal.relativeIdeal, Ideal.map_map]
  exact mapped_curveIdeal_principal_first r θ φ
    (by simp [φ]) (by simp [φ]) hu.unit (IsUnit.unit_spec hu)

theorem localizedIdeal_principal_second (r θ : ℂ) (z : SurfaceRing r θ) :
    (curveIdealOnSurface r θ).map (algebraMap (SurfaceRing r θ)
      (Localization.Away (surfaceQuotient r θ originalG2 * z))) =
        Ideal.span ({algebraMap (SurfaceRing r θ)
          (Localization.Away (surfaceQuotient r θ originalG2 * z))
          (surfaceQuotient r θ (originalF1 r))} : Set _) := by
  let L := Localization.Away (surfaceQuotient r θ originalG2 * z)
  let φ : WeightedPoly →+* L := (algebraMap (SurfaceRing r θ) L).comp (surfaceQuotient r θ)
  have hu : IsUnit (φ originalG2) :=
    IsLocalization.Away.isUnit_of_dvd (surfaceQuotient r θ originalG2 * z) ⟨z, rfl⟩
  rw [curveIdealOnSurface, CycleQ2GeometricRelativeConormal.relativeIdeal, Ideal.map_map]
  exact mapped_curveIdeal_principal_second r θ φ
    (by simp [φ]) (by simp [φ]) hu.unit (IsUnit.unit_spec hu)

theorem localizedGenerator_regular_first (r θ : ℂ) (z : SurfaceRing r θ) :
    IsSMulRegular (Localization.Away (surfaceQuotient r θ (originalG1 r) * z))
      (algebraMap (SurfaceRing r θ)
        (Localization.Away (surfaceQuotient r θ (originalG1 r) * z))
        (surfaceQuotient r θ originalF2)) := by
  apply regular_after_localizing
  intro x hx
  calc
    (surfaceQuotient r θ (originalG1 r) * z) * x =
      z * (surfaceQuotient r θ (originalG1 r) * x) := by ring
    _ = 0 := by rw [first_generator_torsion r θ x hx, mul_zero]

theorem localizedGenerator_regular_second (r θ : ℂ) (z : SurfaceRing r θ) :
    IsSMulRegular (Localization.Away (surfaceQuotient r θ originalG2 * z))
      (algebraMap (SurfaceRing r θ)
        (Localization.Away (surfaceQuotient r θ originalG2 * z))
        (surfaceQuotient r θ (originalF1 r))) := by
  apply regular_after_localizing
  intro x hx
  calc
    (surfaceQuotient r θ originalG2 * z) * x =
      z * (surfaceQuotient r θ originalG2 * x) := by ring
    _ = 0 := by rw [second_generator_torsion r θ x hx, mul_zero]

theorem curveChartKernel_principal_of_localized (r θ : ℂ)
    {s : SurfaceRing r θ} {d : ℕ} (hs : s ∈ surfaceGrade r θ d)
    (b : Away (surfaceGrade r θ) s)
    (hI : (curveIdealOnSurface r θ).map
      (algebraMap (SurfaceRing r θ) (Localization.Away s)) = Ideal.span ({b.val} : Set _)) :
    RingHom.ker (Away.map (curveGradedMap r θ) s) = Ideal.span ({b} : Set _) := by
  rw [curveChartKernel_eq_comap r θ s hs, hI]
  exact principalIdeal_comap_val (surfaceGrade r θ) hs b

theorem refinedIdeal_principal_first (r θ : ℂ) (j : Fin 3) :
    refinedIdeal r θ 0 j = Ideal.span ({refinedGenerator r θ 0 j} : Set _) := by
  apply curveChartKernel_principal_of_localized r θ
    (refinedDenominator_homogeneous r θ 0 j)
  exact (localizedIdeal_principal_first r θ (coordinateElement r θ j)).trans
    (normalizedElement_span_val (surfaceGrade r θ) (coverElement_mem_grade r θ 0)
      (coordinateElement_homogeneous r θ j)
      (surfaceQuotient_mem_grade r θ originalF2_homogeneous)).symm

theorem refinedIdeal_principal_second (r θ : ℂ) (j : Fin 3) :
    refinedIdeal r θ 1 j = Ideal.span ({refinedGenerator r θ 1 j} : Set _) := by
  apply curveChartKernel_principal_of_localized r θ
    (refinedDenominator_homogeneous r θ 1 j)
  exact (localizedIdeal_principal_second r θ (coordinateElement r θ j)).trans
    (normalizedElement_span_val (surfaceGrade r θ) (coverElement_mem_grade r θ 1)
      (coordinateElement_homogeneous r θ j)
      (surfaceQuotient_mem_grade r θ (originalF1_homogeneous r))).symm

theorem curveChartKernel_eq_top_of_mem (r θ : ℂ) (s : SurfaceRing r θ) {d : ℕ}
    (hs : s ∈ surfaceGrade r θ d) (hI : s ∈ curveIdealOnSurface r θ) :
    RingHom.ker (Away.map (curveGradedMap r θ) s) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (surfaceGrade r θ) hs x
  apply (curveChartMap_mk_eq_zero_iff r θ s hs n p hp).mpr
  refine ⟨1, ?_⟩
  simpa only [pow_one] using (curveIdealOnSurface r θ).mul_mem_right p hI

theorem refinedIdeal_eq_top_third (r θ : ℂ) (j : Fin 3) : refinedIdeal r θ 2 j = ⊤ := by
  apply curveChartKernel_eq_top_of_mem r θ _ (refinedDenominator_homogeneous r θ 2 j)
  apply (curveIdealOnSurface r θ).mul_mem_right
  exact Ideal.mem_map_of_mem _ (curveEquation_mem r θ 0)

theorem refinedIdeal_eq_top_fourth (r θ : ℂ) (j : Fin 3) : refinedIdeal r θ 3 j = ⊤ := by
  apply curveChartKernel_eq_top_of_mem r θ _ (refinedDenominator_homogeneous r θ 3 j)
  apply (curveIdealOnSurface r θ).mul_mem_right
  exact Ideal.mem_map_of_mem _ (curveEquation_mem r θ 1)

/-- On every member of the actual Cartier-by-coordinate refinement,
the genuine homogeneous localization kernel is generated by the displayed section. -/
theorem refinedIdeal_principal (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    refinedIdeal r θ i j = Ideal.span ({refinedGenerator r θ i j} : Set _) := by
  fin_cases i
  · exact refinedIdeal_principal_first r θ j
  · exact refinedIdeal_principal_second r θ j
  · change refinedIdeal r θ 2 j = Ideal.span ({(1 : RefinedRing r θ 2 j)} : Set _)
    rw [Ideal.span_singleton_one]
    exact refinedIdeal_eq_top_third r θ j
  · change refinedIdeal r θ 3 j = Ideal.span ({(1 : RefinedRing r θ 3 j)} : Set _)
    rw [Ideal.span_singleton_one]
    exact refinedIdeal_eq_top_fourth r θ j

/-- These are genuine nonzerodivisors in the projective chart rings.
The proof uses the original monic regular sequence, without a smoothness premise. -/
theorem refinedGenerator_regular (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    IsSMulRegular (RefinedRing r θ i j) (refinedGenerator r θ i j) := by
  fin_cases i
  · exact normalizedElement_regular (surfaceGrade r θ) (coverElement_mem_grade r θ 0)
      (coordinateElement_homogeneous r θ j)
      (surfaceQuotient_mem_grade r θ originalF2_homogeneous)
      (localizedGenerator_regular_first r θ (coordinateElement r θ j))
  · exact normalizedElement_regular (surfaceGrade r θ) (coverElement_mem_grade r θ 1)
      (coordinateElement_homogeneous r θ j)
      (surfaceQuotient_mem_grade r θ (originalF1_homogeneous r))
      (localizedGenerator_regular_second r θ (coordinateElement r θ j))
  · exact IsSMulRegular.one _
  · exact IsSMulRegular.one _

theorem refinedGenerator_first_val_mul (r θ : ℂ) (j : Fin 3) :
    (refinedGenerator r θ 0 j).val *
      algebraMap (SurfaceRing r θ) (Localization.Away (refinedDenominator r θ 0 j))
        (coordinateElement r θ j) ^ 2 =
      algebraMap (SurfaceRing r θ) (Localization.Away (refinedDenominator r θ 0 j))
        (surfaceQuotient r θ originalF2) :=
  normalizedElement_val_mul (surfaceGrade r θ) (coverElement_mem_grade r θ 0)
    (coordinateElement_homogeneous r θ j)
    (surfaceQuotient_mem_grade r θ originalF2_homogeneous)

theorem refinedGenerator_second_val_mul (r θ : ℂ) (j : Fin 3) :
    (refinedGenerator r θ 1 j).val *
      algebraMap (SurfaceRing r θ) (Localization.Away (refinedDenominator r θ 1 j))
        (coordinateElement r θ j) ^ 2 =
      algebraMap (SurfaceRing r θ) (Localization.Away (refinedDenominator r θ 1 j))
        (surfaceQuotient r θ (originalF1 r)) :=
  normalizedElement_val_mul (surfaceGrade r θ) (coverElement_mem_grade r θ 1)
    (coordinateElement_homogeneous r θ j)
    (surfaceQuotient_mem_grade r θ (originalF1_homogeneous r))

section ActualProjectiveSections

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2CartierProjectiveCover (projectiveSurface coverFamily projective_four_cover)
open CycleQ2ProjectiveCoordinateCohomology (coordinateOpen coordinate_cover)

def refinedOpen (r θ : ℂ) (i : Fin 4) (j : Fin 3) : (projectiveSurface r θ).Opens :=
  Proj.basicOpen (surfaceGrade r θ) (refinedDenominator r θ i j)

theorem refinedOpen_eq (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    refinedOpen r θ i j = coverFamily r θ i ⊓ coordinateOpen r θ j :=
  Proj.basicOpen_mul (surfaceGrade r θ) _ _

/-- The twelve displayed actual affine opens cover the literal projective surface. -/
theorem refinedOpen_cover (r θ : ℂ) (hr : r ≠ 0) (hθ : θ ≠ 0) :
    (⨆ i : Fin 4, ⨆ j : Fin 3, refinedOpen r θ i j) = ⊤ := by
  calc
    (⨆ i : Fin 4, ⨆ j : Fin 3, refinedOpen r θ i j) =
        (⨆ i : Fin 4, coverFamily r θ i) ⊓
          (⨆ j : Fin 3, coordinateOpen r θ j) := by
      simp only [refinedOpen_eq, iSup_inf_eq, inf_iSup_eq]
      exact iSup_comm
    _ = ⊤ := by rw [projective_four_cover r θ hr, coordinate_cover r θ hθ]; simp

theorem literal_refinedOpen_cover :
    (⨆ i : Fin 4, ⨆ j : Fin 3, refinedOpen 57 1 i j) = ⊤ :=
  refinedOpen_cover 57 1 (by norm_num) one_ne_zero

def refinedSectionsEquiv (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    RefinedRing r θ i j ≃+* Γ(projectiveSurface r θ, refinedOpen r θ i j) :=
  projChartSectionsEquiv (surfaceGrade r θ) (refinedDenominator r θ i j)
    (refinedDenominator_homogeneous r θ i j) (by omega)

def refinedSectionGenerator (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    Γ(projectiveSurface r θ, refinedOpen r θ i j) :=
  refinedSectionsEquiv r θ i j (refinedGenerator r θ i j)

/-- The displayed section generates the kernel of the actual scheme
structure map on the actual open, with the canonical chart equivalence. -/
theorem refinedSectionKernel_principal (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    RingHom.ker ((curveToSurface r θ).app (refinedOpen r θ i j)).hom =
      Ideal.span ({refinedSectionGenerator r θ i j} : Set _) := by
  have hk :
      (RingHom.ker ((curveToSurface r θ).app (refinedOpen r θ i j)).hom).comap
        (refinedSectionsEquiv r θ i j).toRingHom = refinedIdeal r θ i j :=
    curveToSurface_chart_ker r θ (refinedDenominator r θ i j)
      (refinedDenominator_homogeneous r θ i j) (by omega)
  calc
    RingHom.ker ((curveToSurface r θ).app (refinedOpen r θ i j)).hom =
        ((RingHom.ker ((curveToSurface r θ).app (refinedOpen r θ i j)).hom).comap
          (refinedSectionsEquiv r θ i j).toRingHom).map
            (refinedSectionsEquiv r θ i j).toRingHom :=
      (Ideal.map_comap_of_surjective _ (refinedSectionsEquiv r θ i j).surjective _).symm
    _ = (refinedIdeal r θ i j).map (refinedSectionsEquiv r θ i j).toRingHom := by rw [hk]
    _ = Ideal.span ({refinedSectionGenerator r θ i j} : Set _) := by
      rw [refinedIdeal_principal, Ideal.map_span]
      simp only [Set.image_singleton]
      rfl

theorem refinedSectionGenerator_regular (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    IsSMulRegular Γ(projectiveSurface r θ, refinedOpen r θ i j)
      (refinedSectionGenerator r θ i j) := by
  intro x y hxy
  apply (refinedSectionsEquiv r θ i j).symm.injective
  apply refinedGenerator_regular r θ i j
  change refinedGenerator r θ i j * (refinedSectionsEquiv r θ i j).symm x =
    refinedGenerator r θ i j * (refinedSectionsEquiv r θ i j).symm y
  change refinedSectionGenerator r θ i j * x = refinedSectionGenerator r θ i j * y at hxy
  have h := congrArg (refinedSectionsEquiv r θ i j).symm hxy
  simpa only [map_mul, refinedSectionGenerator, RingEquiv.symm_apply_apply] using h

open CycleQ2GeometricProjectiveCurve (curveGrade projectiveCurve)

/-- The actual structure-map target on each refined chart is the genuine
curve section ring, and every such section lifts from this surface chart. -/
theorem refinedStructureMap_surjective (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    Function.Surjective ((curveToSurface r θ).app (refinedOpen r θ i j)).hom := by
  intro q
  let s := refinedDenominator r θ i j
  have hs : s ∈ surfaceGrade r θ (coverDegree i + 1) :=
    refinedDenominator_homogeneous r θ i j
  have hd : 0 < coverDegree i + 1 := by omega
  let eB := projChartSectionsEquiv (curveGrade r θ) (curveGradedMap r θ s)
    ((curveGradedMap r θ).2 hs) hd
  obtain ⟨a, ha⟩ := gradedAwayMap_surjective (surfaceGrade r θ) (curveGrade r θ)
    (curveGradedMap r θ) (curveGradedMap_homogeneous_surjective r θ) s hs (eB.symm q)
  refine ⟨refinedSectionsEquiv r θ i j a, ?_⟩
  change (Proj.map (curveGradedMap r θ) (curve_irrelevant_le r θ)).app
    (Proj.basicOpen (surfaceGrade r θ) s)
      (projChartSectionsEquiv (surfaceGrade r θ) s hs hd a) = q
  rw [projMap_app_basicOpen (surfaceGrade r θ) (curveGrade r θ)
    (curveGradedMap r θ) (curve_irrelevant_le r θ) s hs hd, ha]
  exact eB.apply_symm_apply q

abbrev RefinedSections (r θ : ℂ) (i : Fin 4) (j : Fin 3) :=
  Γ(projectiveSurface r θ, refinedOpen r θ i j)

abbrev RefinedCurveSections (r θ : ℂ) (i : Fin 4) (j : Fin 3) :=
  Γ(projectiveCurve r θ, (curveToSurface r θ) ⁻¹ᵁ refinedOpen r θ i j)

def refinedSectionMap (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    RefinedSections r θ i j →+* RefinedCurveSections r θ i j :=
  ((curveToSurface r θ).app (refinedOpen r θ i j)).hom

open CycleQ2RegularPrincipalHomSequence

theorem refinedScalarInclusion_injective (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    Function.Injective (scalarInclusion (RingHom.ker (refinedSectionMap r θ i j))) :=
  scalarInclusion_injective _ (refinedSectionGenerator r θ i j)
    (refinedSectionGenerator_regular r θ i j) (refinedSectionKernel_principal r θ i j)

/-- Reduction is literally postcomposition by the curve-to-surface
structure-map component. The curve section ring is not replaced by a chosen quotient. -/
theorem refinedHomReduction_apply (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    letI : Algebra (RefinedSections r θ i j) (RefinedCurveSections r θ i j) :=
      (refinedSectionMap r θ i j).toAlgebra
    ∀ (f : RingHom.ker (refinedSectionMap r θ i j) →ₗ[RefinedSections r θ i j]
        RefinedSections r θ i j) (x : RingHom.ker (refinedSectionMap r θ i j)),
      algebraReduction (RingHom.ker (refinedSectionMap r θ i j))
        (RefinedCurveSections r θ i j) f x =
          (curveToSurface r θ).app (refinedOpen r θ i j) (f x) := by
  intros
  rfl

theorem refinedHomReduction_surjective (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    letI : Algebra (RefinedSections r θ i j) (RefinedCurveSections r θ i j) :=
      (refinedSectionMap r θ i j).toAlgebra
    Function.Surjective (algebraReduction (RingHom.ker (refinedSectionMap r θ i j))
      (RefinedCurveSections r θ i j)) := by
  letI : Algebra (RefinedSections r θ i j) (RefinedCurveSections r θ i j) :=
    (refinedSectionMap r θ i j).toAlgebra
  exact algebraReduction_surjective _ _ (refinedSectionGenerator r θ i j)
    (refinedSectionGenerator_regular r θ i j) (refinedSectionKernel_principal r θ i j)
    (refinedStructureMap_surjective r θ i j)

/-- Exactness on the actual refined affine chart, with the actual ideal,
the actual scalar inclusion, and reduction to the actual curve section ring. -/
theorem refinedHomSequence_exact (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    letI : Algebra (RefinedSections r θ i j) (RefinedCurveSections r θ i j) :=
      (refinedSectionMap r θ i j).toAlgebra
    Function.Exact (scalarInclusion (RingHom.ker (refinedSectionMap r θ i j)))
      (algebraReduction (RingHom.ker (refinedSectionMap r θ i j))
        (RefinedCurveSections r θ i j)) := by
  letI : Algebra (RefinedSections r θ i j) (RefinedCurveSections r θ i j) :=
    (refinedSectionMap r θ i j).toAlgebra
  exact scalar_algebra_exact _ _ (refinedSectionGenerator r θ i j)
    (refinedSectionGenerator_regular r θ i j) (refinedSectionKernel_principal r θ i j) rfl

end ActualProjectiveSections

end CycleQ2ProjectiveCartierIdeal

#print axioms CycleQ2ProjectiveCartierIdeal.refinedIdeal_principal
#print axioms CycleQ2ProjectiveCartierIdeal.refinedGenerator_regular
#print axioms CycleQ2ProjectiveCartierIdeal.literal_refinedOpen_cover
#print axioms CycleQ2ProjectiveCartierIdeal.refinedSectionKernel_principal
#print axioms CycleQ2ProjectiveCartierIdeal.refinedSectionGenerator_regular
#print axioms CycleQ2ProjectiveCartierIdeal.refinedStructureMap_surjective
#print axioms CycleQ2ProjectiveCartierIdeal.refinedScalarInclusion_injective
#print axioms CycleQ2ProjectiveCartierIdeal.refinedHomReduction_surjective
#print axioms CycleQ2ProjectiveCartierIdeal.refinedHomSequence_exact

end
end ActualProjectiveIdealCharts

end ActualProjectiveCartierIdeal

section ActualProjectiveCartierSquares

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ProjectiveCartierIdeal

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  HomogeneousLocalization
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading
open CycleQ2GeometricProjectiveCurve (curveGrade projectiveCurve)
open CycleQ2CartierProjectiveCover (projectiveSurface)
open CycleQ2GeometricLiteralSurface (curveGradedMap curveToSurface curve_irrelevant_le
  gradedAwayMap_surjective curveGradedMap_homogeneous_surjective)

abbrev RefinedCurveRing (r θ : ℂ) (i : Fin 4) (j : Fin 3) :=
  Away (curveGrade r θ) (curveGradedMap r θ (refinedDenominator r θ i j))

def refinedCurveRingMap (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    RefinedRing r θ i j →+* RefinedCurveRing r θ i j :=
  Away.map (curveGradedMap r θ) (refinedDenominator r θ i j)

def refinedSurfaceChart (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    Spec (CommRingCat.of (RefinedRing r θ i j)) ⟶ projectiveSurface r θ :=
  Proj.awayι (surfaceGrade r θ) (refinedDenominator r θ i j)
    (refinedDenominator_homogeneous r θ i j) (by omega)

def refinedCurveChart (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    Spec (CommRingCat.of (RefinedCurveRing r θ i j)) ⟶ projectiveCurve r θ :=
  Proj.awayι (curveGrade r θ) (curveGradedMap r θ (refinedDenominator r θ i j))
    ((curveGradedMap r θ).2 (refinedDenominator_homogeneous r θ i j)) (by omega)

instance (r θ : ℂ) (i : Fin 4) (j : Fin 3) : IsOpenImmersion (refinedSurfaceChart r θ i j) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (surfaceGrade r θ)
    (refinedDenominator r θ i j) (refinedDenominator_homogeneous r θ i j) (by omega)))

instance (r θ : ℂ) (i : Fin 4) (j : Fin 3) : IsOpenImmersion (refinedCurveChart r θ i j) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (curveGrade r θ)
    (curveGradedMap r θ (refinedDenominator r θ i j))
    ((curveGradedMap r θ).2 (refinedDenominator_homogeneous r θ i j)) (by omega)))

theorem refinedSurfaceChart_range (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    (refinedSurfaceChart r θ i j).opensRange = refinedOpen r θ i j :=
  Proj.opensRange_awayι (surfaceGrade r θ) (refinedDenominator r θ i j)
    (refinedDenominator_homogeneous r θ i j) (by omega)

theorem refinedCurveChart_range (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    (refinedCurveChart r θ i j).opensRange =
      (curveToSurface r θ) ⁻¹ᵁ refinedOpen r θ i j :=
  Proj.opensRange_awayι (curveGrade r θ)
    (curveGradedMap r θ (refinedDenominator r θ i j))
    ((curveGradedMap r θ).2 (refinedDenominator_homogeneous r θ i j)) (by omega)

theorem refinedChart_square (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    refinedCurveChart r θ i j ≫ curveToSurface r θ =
      Spec.map (CommRingCat.ofHom (refinedCurveRingMap r θ i j)) ≫
        refinedSurfaceChart r θ i j :=
  Proj.awayι_comp_map (curveGradedMap r θ) (curve_irrelevant_le r θ)
    (by omega) (refinedDenominator r θ i j) (refinedDenominator_homogeneous r θ i j)

/-- The two actual homogeneous-localization charts form the cartesian
square of the original projective closed immersion. -/
theorem refinedChart_isPullback (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    IsPullback (Spec.map (CommRingCat.ofHom (refinedCurveRingMap r θ i j)))
      (refinedCurveChart r θ i j) (refinedSurfaceChart r θ i j)
      (curveToSurface r θ) := by
  apply IsOpenImmersion.isPullback
  · exact refinedChart_square r θ i j
  · rw [refinedSurfaceChart_range, refinedCurveChart_range]

theorem refinedCurveRingMap_surjective (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    Function.Surjective (refinedCurveRingMap r θ i j) :=
  gradedAwayMap_surjective (surfaceGrade r θ) (curveGrade r θ) (curveGradedMap r θ)
    (curveGradedMap_homogeneous_surjective r θ) (refinedDenominator r θ i j)
    (refinedDenominator_homogeneous r θ i j)

theorem refinedCurveRingMap_kernel (r θ : ℂ) (i : Fin 4) (j : Fin 3) :
    RingHom.ker (refinedCurveRingMap r θ i j) =
      Ideal.span ({refinedGenerator r θ i j} : Set _) :=
  refinedIdeal_principal r θ i j

end CycleQ2ProjectiveCartierIdeal

#print axioms CycleQ2ProjectiveCartierIdeal.refinedChart_isPullback
#print axioms CycleQ2ProjectiveCartierIdeal.refinedCurveRingMap_surjective
#print axioms CycleQ2ProjectiveCartierIdeal.refinedCurveRingMap_kernel

end -- component noncomputable section
end ActualProjectiveCartierSquares

section IntrinsicAffineCartierExactness

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIntrinsicCartierSequence

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricCartierNormalLift
  CycleQ2RegularPrincipalHomSequence

variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

theorem affineInverseIdealScalar_injective (b : Γ(Spec A, ⊤))
    (hb : IsSMulRegular Γ(Spec A, ⊤) b)
    (hp : RingHom.ker ((Spec.map φ).app ⊤).hom = Ideal.span ({b} : Set Γ(Spec A, ⊤))) :
    Function.Injective ((inverseIdealScalar (Spec.map φ)).val.app (op ⊤)) := by
  intro a c hac
  apply scalarInclusion_injective (RingHom.ker ((Spec.map φ).app ⊤).hom) b hb hp
  apply LinearMap.ext
  intro x
  have h := congrArg (fun f => inverseIdealSectionEvaluate (Spec.map φ) ⊤ f x) hac
  exact (inverseIdealScalar_evaluate (Spec.map φ) ⊤ a x).symm.trans
    (h.trans (inverseIdealScalar_evaluate (Spec.map φ) ⊤ c x))

theorem affineInverseIdealReduction_surjective (b : Γ(Spec A, ⊤))
    (hb : IsSMulRegular Γ(Spec A, ⊤) b)
    (hp : RingHom.ker ((Spec.map φ).app ⊤).hom = Ideal.span ({b} : Set Γ(Spec A, ⊤)))
    (hs : Function.Surjective ((Spec.map φ).app ⊤)) :
    Function.Surjective ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤)) := by
  intro n
  let I := RingHom.ker ((Spec.map φ).app ⊤).hom
  let e := principalIdealEquiv I b hb hp
  obtain ⟨a,ha⟩ := hs (normalSectionEvaluate (Spec.map φ) ⊤ n (e 1))
  let l : I →ₗ[Γ(Spec A, ⊤)] Γ(Spec A, ⊤) := a • e.symm.toLinearMap
  let f := (affineInverseIdealSectionEquiv φ).symm l
  refine ⟨f, ?_⟩
  apply (affineNormalSectionEquiv φ).injective
  apply principalHom_ext I b hb hp
  calc
    _ = (Spec.map φ).app ⊤ (inverseIdealSectionEvaluate (Spec.map φ) ⊤ f (e 1)) :=
      inverseIdealReduction_evaluate (Spec.map φ) ⊤ f (e 1)
    _ = (Spec.map φ).app ⊤ (l (e 1)) :=
      congrArg (fun h : I →ₗ[Γ(Spec A, ⊤)] Γ(Spec A, ⊤) => (Spec.map φ).app ⊤ (h (e 1)))
        ((affineInverseIdealSectionEquiv φ).apply_symm_apply l)
    _ = (Spec.map φ).app ⊤ a := by
      apply congrArg ((Spec.map φ).app ⊤)
      change a * e.symm (e 1) = a
      rw [LinearEquiv.symm_apply_apply, mul_one]
    _ = _ := ha

theorem affineInverseIdealSequence_exact (b : Γ(Spec A, ⊤))
    (hb : IsSMulRegular Γ(Spec A, ⊤) b)
    (hp : RingHom.ker ((Spec.map φ).app ⊤).hom = Ideal.span ({b} : Set Γ(Spec A, ⊤))) :
    Function.Exact ((inverseIdealScalar (Spec.map φ)).val.app (op ⊤))
      ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤)) := by
  intro f
  constructor
  · intro hf
    let I := RingHom.ker ((Spec.map φ).app ⊤).hom
    let e := principalIdealEquiv I b hb hp
    have hz : (Spec.map φ).app ⊤ (inverseIdealSectionEvaluate (Spec.map φ) ⊤ f (e 1)) = 0 :=
      (inverseIdealReduction_evaluate (Spec.map φ) ⊤ f (e 1)).symm.trans
        (congrArg (fun n => normalSectionEvaluate (Spec.map φ) ⊤ n (e 1)) hf)
    have hm : inverseIdealSectionEvaluate (Spec.map φ) ⊤ f (e 1) ∈ Ideal.span ({b} : Set Γ(Spec A, ⊤)) :=
      (le_of_eq hp) hz
    obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hm
    refine ⟨a, ?_⟩
    apply (affineInverseIdealSectionEquiv φ).injective
    apply principalHom_ext I b hb hp
    exact (inverseIdealScalar_evaluate (Spec.map φ) ⊤ a (e 1)).trans
      ((congrArg (fun z : Γ(Spec A, ⊤) => a * z) (principalIdealEquiv_one_coe I b hb hp)).trans ha)
  · rintro ⟨a,rfl⟩
    exact congrArg (fun h => h.val.app (op ⊤) a)
      (inverseIdealScalar_comp_reduction (Spec.map φ))

end CycleQ2GeometricIntrinsicCartierSequence

#print axioms CycleQ2GeometricIntrinsicCartierSequence.affineInverseIdealScalar_injective
#print axioms CycleQ2GeometricIntrinsicCartierSequence.affineInverseIdealReduction_surjective
#print axioms CycleQ2GeometricIntrinsicCartierSequence.affineInverseIdealSequence_exact

end -- component noncomputable section
end IntrinsicAffineCartierExactness

section IntrinsicCartierOpenTransport

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2IntrinsicCartierOpenTransport

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricIntrinsicCartierSequence

variable {X Y : Scheme.{0}} {A B : CommRingCat.{0}}
variable (j : X ⟶ Y) (φ : A ⟶ B)
  (i : Spec A ⟶ Y) (k : Spec B ⟶ X)
  [IsOpenImmersion i] [IsOpenImmersion k]
  (H : IsPullback (Spec.map φ) k i j)

def ambientSectionsEquiv : Γ(Y, i.opensRange) ≃+* Γ(Spec A, ⊤) :=
  (IsOpenImmersion.ΓIsoTop i).symm.commRingCatIsoToRingEquiv

theorem ambientSectionsEquiv_apply (a : Γ(Y, i.opensRange)) :
    ambientSectionsEquiv i a = (i.appIso ⊤).hom
      (Y.presheaf.map (homOfLE (i.image_le_opensRange ⊤)).op a) := rfl

/-- The actual open-base-change equivalence intertwines multiplication
of the original ideal inclusion with multiplication on the affine chart. -/
theorem inverseIdealScalar_openBaseChange (a : Γ(Y, i.opensRange)) :
    inverseIdealSectionOpenBaseChangeEquiv j i k (Spec.map φ) H
      ((inverseIdealScalar j).val.app (op i.opensRange) a) =
        (inverseIdealScalar (Spec.map φ)).val.app (op ⊤) (ambientSectionsEquiv i a) := by
  apply (affineInverseIdealSectionEquiv φ).injective
  apply LinearMap.ext
  intro x
  change inverseIdealSectionEvaluate (Spec.map φ) ⊤
      (inverseIdealSectionOpenBaseChangeEquiv j i k (Spec.map φ) H
        ((inverseIdealScalar j).val.app (op i.opensRange) a)) x =
    inverseIdealSectionEvaluate (Spec.map φ) ⊤
      ((inverseIdealScalar (Spec.map φ)).val.app (op ⊤) (ambientSectionsEquiv i a)) x
  rw [inverseIdealSectionOpenBaseChangeEquiv_evaluate]
  rw [← PresheafOfModules.naturality_apply (inverseIdealScalar j).val]
  rw [inverseIdealScalar_evaluate, inverseIdealScalar_evaluate]
  rw [map_mul, normalOpenIdealPullback_coe]
  have hx := ConcreteCategory.congr_hom (i.appIso ⊤).inv_hom_id (x : Γ(Spec A, ⊤))
  change (i.appIso ⊤).hom ((i.appIso ⊤).inv (x : Γ(Spec A, ⊤))) = x at hx
  rw [hx]
  rfl

theorem baseChangeStructureSectionIso_app_forward (V : (Spec A).Opens)
    (a : Γ(Y, i ''ᵁ V)) :
    (baseChangeStructureSectionIso j i k (Spec.map φ) H V).hom
      (j.app (i ''ᵁ V) a) = (Spec.map φ).app V ((i.appIso V).hom a) := by
  have h := ConcreteCategory.congr_hom
    (baseChangeStructureSectionIso_app j i k (Spec.map φ) H V) ((i.appIso V).hom a)
  have ha := ConcreteCategory.congr_hom (i.appIso V).hom_inv_id a
  change (i.appIso V).inv ((i.appIso V).hom a) = a at ha
  simpa only [CommRingCat.comp_apply, ha] using h

/-- Reduction commutes with the two genuine local-Hom comparisons because
it is postcomposition with the same cartesian structure-map square. -/
theorem inverseIdealReduction_openBaseChange
    (f : (inverseIdealSheaf j).val.obj (op i.opensRange)) :
    normalSectionOpenBaseChangeEquiv j i k (Spec.map φ) H
      ((inverseIdealReduction j).val.app (op i.opensRange) f) =
        (inverseIdealReduction (Spec.map φ)).val.app (op ⊤)
          (inverseIdealSectionOpenBaseChangeEquiv j i k (Spec.map φ) H f) := by
  apply (affineNormalSectionEquiv φ).injective
  apply LinearMap.ext
  intro x
  change normalSectionEvaluate (Spec.map φ) ⊤
      (normalSectionOpenBaseChangeEquiv j i k (Spec.map φ) H
        ((inverseIdealReduction j).val.app (op i.opensRange) f)) x =
    normalSectionEvaluate (Spec.map φ) ⊤
      ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤)
        (inverseIdealSectionOpenBaseChangeEquiv j i k (Spec.map φ) H f)) x
  rw [normalSectionOpenBaseChangeEquiv_evaluate]
  rw [← PresheafOfModules.naturality_apply (inverseIdealReduction j).val]
  rw [inverseIdealReduction_evaluate, inverseIdealReduction_evaluate]
  rw [inverseIdealSectionOpenBaseChangeEquiv_evaluate]
  exact baseChangeStructureSectionIso_app_forward j φ i k H ⊤ _

theorem normalOpenBaseChange_zero :
    normalSectionOpenBaseChangeEquiv j i k (Spec.map φ) H 0 = 0 := by
  apply (affineNormalSectionEquiv φ).injective
  apply LinearMap.ext
  intro x
  change normalSectionEvaluate (Spec.map φ) ⊤
    (normalSectionOpenBaseChangeEquiv j i k (Spec.map φ) H 0) x = 0
  rw [normalSectionOpenBaseChangeEquiv_evaluate, map_zero]
  change (baseChangeStructureSectionIso j i k (Spec.map φ) H ⊤).hom 0 = 0
  exact map_zero _

include H

/-- Injectivity transports along the actual cartesian affine chart. -/
theorem inverseIdealScalar_injective_of_affine
    (hf : Function.Injective ((inverseIdealScalar (Spec.map φ)).val.app (op ⊤))) :
    Function.Injective ((inverseIdealScalar j).val.app (op i.opensRange)) := by
  intro a b hab
  apply (ambientSectionsEquiv i).injective
  apply hf
  rw [← inverseIdealScalar_openBaseChange j φ i k H,
    ← inverseIdealScalar_openBaseChange j φ i k H, hab]

/-- Surjectivity transports with the original normal-sheaf comparison. -/
theorem inverseIdealReduction_surjective_of_affine
    (hg : Function.Surjective ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤))) :
    Function.Surjective ((inverseIdealReduction j).val.app (op i.opensRange)) := by
  intro n
  obtain ⟨f, hf⟩ := hg (normalSectionOpenBaseChangeEquiv j i k (Spec.map φ) H n)
  refine ⟨(inverseIdealSectionOpenBaseChangeEquiv j i k (Spec.map φ) H).symm f, ?_⟩
  apply (normalSectionOpenBaseChangeEquiv j i k (Spec.map φ) H).injective
  rw [inverseIdealReduction_openBaseChange, Equiv.apply_symm_apply, hf]

/-- Exactness transports with both actual sheaf morphisms and their
canonical local-Hom equivalences. -/
theorem inverseIdealSequence_exact_of_affine
    (he : Function.Exact ((inverseIdealScalar (Spec.map φ)).val.app (op ⊤))
      ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤))) :
    Function.Exact ((inverseIdealScalar j).val.app (op i.opensRange))
      ((inverseIdealReduction j).val.app (op i.opensRange)) := by
  intro f
  constructor
  · intro hf
    have hz : (inverseIdealReduction (Spec.map φ)).val.app (op ⊤)
        (inverseIdealSectionOpenBaseChangeEquiv j i k (Spec.map φ) H f) = 0 := by
      rw [← inverseIdealReduction_openBaseChange, hf, normalOpenBaseChange_zero]
    obtain ⟨a, ha⟩ := (he _).mp hz
    refine ⟨(ambientSectionsEquiv i).symm a, ?_⟩
    apply (inverseIdealSectionOpenBaseChangeEquiv j i k (Spec.map φ) H).injective
    rw [inverseIdealScalar_openBaseChange, RingEquiv.apply_symm_apply, ha]
  · rintro ⟨a, rfl⟩
    exact congrArg (fun h => h.val.app (op i.opensRange) a)
      (inverseIdealScalar_comp_reduction j)

end CycleQ2IntrinsicCartierOpenTransport

#print axioms CycleQ2IntrinsicCartierOpenTransport.inverseIdealScalar_openBaseChange
#print axioms CycleQ2IntrinsicCartierOpenTransport.inverseIdealReduction_openBaseChange
#print axioms CycleQ2IntrinsicCartierOpenTransport.inverseIdealSequence_exact_of_affine

end -- component noncomputable section
end IntrinsicCartierOpenTransport

section IntrinsicCartierPrincipalBasis

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2IntrinsicCartierPrincipalBasis

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2GeometricCartierNormalLift

section AffineSections
variable {A B : CommRingCat.{0}} (φ : A ⟶ B)

theorem sectionGenerator_regular (b : A) (hb : IsSMulRegular A b) :
    IsSMulRegular Γ(Spec A, ⊤) ((specTopRingEquiv A).symm b) := by
  intro x y hxy
  apply (specTopRingEquiv A).injective
  apply hb
  have h := congrArg (specTopRingEquiv A) hxy
  simpa only [smul_eq_mul, map_mul, RingEquiv.apply_symm_apply] using h

theorem sectionKernel_principal (b : A)
    (hp : RingHom.ker φ.hom = Ideal.span ({b} : Set A)) :
    RingHom.ker ((Spec.map φ).app ⊤).hom =
      Ideal.span ({(specTopRingEquiv A).symm b} : Set Γ(Spec A, ⊤)) := by
  ext z
  constructor
  · intro hz
    have hz' : specTopRingEquiv A z ∈ Ideal.span ({b} : Set A) := by
      rw [← hp]
      change φ (specTopRingEquiv A z) = 0
      rw [← affineSectionMap_normalization]
      exact (congrArg (specTopRingEquiv B) hz).trans (map_zero _)
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hz'
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨(specTopRingEquiv A).symm a, ?_⟩
    apply (specTopRingEquiv A).injective
    simpa only [map_mul, RingEquiv.apply_symm_apply] using ha
  · intro hz
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    change (Spec.map φ).app ⊤ (a * (specTopRingEquiv A).symm b) = 0
    apply (specTopRingEquiv B).injective
    rw [affineSectionMap_normalization, map_zero, map_mul,
      RingEquiv.apply_symm_apply, map_mul]
    have hb : φ b = 0 := (le_of_eq hp.symm) (Ideal.subset_span (Set.mem_singleton b))
    rw [hb, mul_zero]

theorem affineSectionMap_surjective (hs : Function.Surjective φ) :
    Function.Surjective ((Spec.map φ).app ⊤) := by
  intro y
  obtain ⟨x, hx⟩ := hs (specTopRingEquiv B y)
  refine ⟨(specTopRingEquiv A).symm x, (specTopRingEquiv B).injective ?_⟩
  rw [affineSectionMap_normalization, RingEquiv.apply_symm_apply, hx]

theorem affineIntrinsic_exactness (b : A) (hb : IsSMulRegular A b)
    (hp : RingHom.ker φ.hom = Ideal.span ({b} : Set A))
    (hs : Function.Surjective φ) :
    Function.Injective ((inverseIdealScalar (Spec.map φ)).val.app (op ⊤)) ∧
      Function.Exact ((inverseIdealScalar (Spec.map φ)).val.app (op ⊤))
        ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤)) ∧
      Function.Surjective ((inverseIdealReduction (Spec.map φ)).val.app (op ⊤)) := by
  exact ⟨affineInverseIdealScalar_injective φ _
      (sectionGenerator_regular b hb) (sectionKernel_principal φ b hp),
    affineInverseIdealSequence_exact φ _
      (sectionGenerator_regular b hb) (sectionKernel_principal φ b hp),
    affineInverseIdealReduction_surjective φ _
      (sectionGenerator_regular b hb) (sectionKernel_principal φ b hp)
      (affineSectionMap_surjective φ hs)⟩

end AffineSections

section PrincipalLocalization
variable {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (a : A)

def principalMap : Localization.Away a →+* Localization.Away (φ a) :=
  IsLocalization.Away.map _ _ φ a

theorem principalMap_base (b : A) :
    principalMap φ a (algebraMap A (Localization.Away a) b) =
      algebraMap B (Localization.Away (φ a)) (φ b) := by
  simp only [principalMap, IsLocalization.Away.map, IsLocalization.map_eq]

theorem principalMap_surjective (hs : Function.Surjective φ) :
    Function.Surjective (principalMap φ a) := by
  let : IsLocalization ((Submonoid.powers a).map φ) (Localization.Away (φ a)) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact IsLocalization.map_surjective_of_surjective (Submonoid.powers a)
    (Localization.Away a) (Localization.Away (φ a)) (g := φ) hs

theorem principalMap_kernel :
    RingHom.ker (principalMap φ a) =
      (RingHom.ker φ).map (algebraMap A (Localization.Away a)) := by
  exact IsLocalization.ker_map (S := Localization.Away a)
    (Localization.Away (φ a)) φ (Submonoid.map_powers φ a)

theorem principalMap_kernel_principal (b : A)
    (hp : RingHom.ker φ = Ideal.span ({b} : Set A)) :
    RingHom.ker (principalMap φ a) =
      Ideal.span ({algebraMap A (Localization.Away a) b} : Set (Localization.Away a)) := by
  rw [principalMap_kernel, hp, Ideal.map_span, Set.image_singleton]

theorem principalGenerator_regular (b : A) (hb : IsSMulRegular A b) :
    IsSMulRegular (Localization.Away a) (algebraMap A (Localization.Away a) b) := by
  apply regular_after_localizing b a
  intro x hx
  have hx0 : x = 0 := hb (show b • x = b • (0 : A) by simpa only [smul_eq_mul, mul_zero] using hx)
  rw [hx0, mul_zero]

theorem principal_square :
    Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ a)))) ≫
      Spec.map (CommRingCat.ofHom φ) =
    Spec.map (CommRingCat.ofHom (principalMap φ a)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  ext b
  exact (principalMap_base φ a b).symm

theorem principal_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (principalMap φ a)))
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ a)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))))
      (Spec.map (CommRingCat.ofHom φ)) := by
  apply IsOpenImmersion.isPullback
  · exact principal_square φ a
  · rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of A) a,
      Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) (φ a)]
    rfl

end PrincipalLocalization

section ActualRefinedCharts

open CycleQ2ProjectiveCartierIdeal CycleQ2GeometricLiteralSurface
  CycleQ2IntrinsicCartierOpenTransport
open CycleQ2GeometricProjectiveCurve (projectiveCurve)
open CycleQ2CartierProjectiveCover (projectiveSurface)

variable (r θ : ℂ) (u : Fin 4) (v : Fin 3) (a : RefinedRing r θ u v)

/-- A principal subopen of an actual Cartier--coordinate affine surface chart. -/
def principalSurfaceChart :
    Spec (CommRingCat.of (Localization.Away a)) ⟶ projectiveSurface r θ :=
  Spec.map (CommRingCat.ofHom (algebraMap (RefinedRing r θ u v) (Localization.Away a))) ≫
    refinedSurfaceChart r θ u v

/-- The matching principal subopen of the original curve chart. -/
def principalCurveChart :
    Spec (CommRingCat.of (Localization.Away (refinedCurveRingMap r θ u v a))) ⟶
      projectiveCurve r θ :=
  Spec.map (CommRingCat.ofHom (algebraMap (RefinedCurveRing r θ u v)
    (Localization.Away (refinedCurveRingMap r θ u v a)))) ≫
      refinedCurveChart r θ u v

instance : IsOpenImmersion (principalSurfaceChart r θ u v a) := by
  dsimp [principalSurfaceChart]
  infer_instance

instance : IsOpenImmersion (principalCurveChart r θ u v a) := by
  dsimp [principalCurveChart]
  infer_instance

theorem principalSurfaceChart_range :
    (principalSurfaceChart r θ u v a).opensRange =
      (refinedSurfaceChart r θ u v) ''ᵁ PrimeSpectrum.basicOpen a := by
  dsimp only [principalSurfaceChart]
  rw [Scheme.Hom.opensRange_comp]
  exact congrArg (fun W : (Spec (CommRingCat.of (RefinedRing r θ u v))).Opens =>
    (refinedSurfaceChart r θ u v) ''ᵁ W)
      (Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of (RefinedRing r θ u v)) a)

theorem principalChart_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (principalMap (refinedCurveRingMap r θ u v) a)))
      (principalCurveChart r θ u v a) (principalSurfaceChart r θ u v a)
      (curveToSurface r θ) :=
  (principal_isPullback (refinedCurveRingMap r θ u v) a).paste_vert
    (refinedChart_isPullback r θ u v)

/-- The literal intrinsic Cartier sequence is short exact on every principal
subopen of each actual homogeneous Cartier--coordinate chart. This uses the
original kernel ideal sheaf, its internal Hom, and the original reduction map. -/
theorem refinedPrincipal_inverseIdeal_exactness :
    let W := (refinedSurfaceChart r θ u v) ''ᵁ PrimeSpectrum.basicOpen a
    Function.Injective ((inverseIdealScalar (curveToSurface r θ)).val.app (op W)) ∧
      Function.Exact ((inverseIdealScalar (curveToSurface r θ)).val.app (op W))
        ((inverseIdealReduction (curveToSurface r θ)).val.app (op W)) ∧
      Function.Surjective ((inverseIdealReduction (curveToSurface r θ)).val.app (op W)) := by
  let φ := CommRingCat.ofHom (principalMap (refinedCurveRingMap r θ u v) a)
  have hlocal := affineIntrinsic_exactness φ
    (algebraMap (RefinedRing r θ u v) (Localization.Away a) (refinedGenerator r θ u v))
    (principalGenerator_regular a (refinedGenerator r θ u v) (refinedGenerator_regular r θ u v))
    (principalMap_kernel_principal (refinedCurveRingMap r θ u v) a
      (refinedGenerator r θ u v) (refinedCurveRingMap_kernel r θ u v))
    (principalMap_surjective (refinedCurveRingMap r θ u v) a
      (refinedCurveRingMap_surjective r θ u v))
  have hcart := principalChart_isPullback r θ u v a
  have hi := inverseIdealScalar_injective_of_affine (curveToSurface r θ) φ
    (principalSurfaceChart r θ u v a) (principalCurveChart r θ u v a) hcart hlocal.1
  have he := inverseIdealSequence_exact_of_affine (curveToSurface r θ) φ
    (principalSurfaceChart r θ u v a) (principalCurveChart r θ u v a) hcart hlocal.2.1
  have hs := inverseIdealReduction_surjective_of_affine (curveToSurface r θ) φ
    (principalSurfaceChart r θ u v a) (principalCurveChart r θ u v a) hcart hlocal.2.2
  rw [principalSurfaceChart_range] at hi he hs
  exact ⟨hi, he, hs⟩

end ActualRefinedCharts

end CycleQ2IntrinsicCartierPrincipalBasis

#print axioms CycleQ2IntrinsicCartierPrincipalBasis.affineIntrinsic_exactness
#print axioms CycleQ2IntrinsicCartierPrincipalBasis.principalMap_kernel_principal
#print axioms CycleQ2IntrinsicCartierPrincipalBasis.principalGenerator_regular
#print axioms CycleQ2IntrinsicCartierPrincipalBasis.refinedPrincipal_inverseIdeal_exactness

end -- component noncomputable section
end IntrinsicCartierPrincipalBasis

section ActualSheafLocalExactness

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSheafLocalExactness

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf

variable {X : TopCat.{0}}

/-- Component exactness on a basis implies exactness of the genuine sheaf
complex. A germ in the kernel is first represented on a basis open where its
image already vanishes, so no global section-surjectivity is assumed. -/
theorem additiveSheaf_exact_of_basis
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (he : ∀ U ∈ B, Function.Exact (S.f.hom.app (op U)) (S.g.hom.app (op U))) :
    S.Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mpr
  intro x
  apply (ShortComplex.ab_exact_iff _).mpr
  intro t ht
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq S.X₂.obj t
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.g.hom
      (TopCat.Presheaf.germ S.X₂.obj U x hxU s) = 0 at ht
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply] at ht
  have hz : TopCat.Presheaf.germ S.X₃.obj U x hxU (S.g.hom.app (op U) s) =
      TopCat.Presheaf.germ S.X₃.obj U x hxU 0 := ht.trans (map_zero _).symm
  obtain ⟨V, hxV, hVB, hVU, hVU', hv⟩ :=
    TopCat.Presheaf.germ_eq_of_isBasis hB S.X₃.obj x hxU hxU hz
  have hk : S.g.hom.app (op V) (S.X₂.obj.map (homOfLE hVU).op s) = 0 := by
    simpa only [← S.g.hom.naturality_apply, map_zero] using hv
  obtain ⟨a, ha⟩ := (he V hVB _).mp hk
  refine ⟨TopCat.Presheaf.germ S.X₁.obj V x hxV a, ?_⟩
  change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map S.f.hom
      (TopCat.Presheaf.germ S.X₁.obj V x hxV a) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, ha,
    TopCat.Presheaf.germ_res_apply]

/-- A componentwise short exact complex on a basis is short exact as a
complex of additive sheaves. -/
theorem additiveSheaf_shortExact_of_basis
    (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X))
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hi : ∀ U ∈ B, Function.Injective (S.f.hom.app (op U)))
    (he : ∀ U ∈ B, Function.Exact (S.f.hom.app (op U)) (S.g.hom.app (op U)))
    (hs : ∀ U ∈ B, Function.Surjective (S.g.hom.app (op U))) :
    S.ShortExact where
  exact := additiveSheaf_exact_of_basis S B hB he
  mono_f := by
    apply (TopCat.Presheaf.mono_iff_stalk_mono S.f).mpr
    intro x
    exact (AddCommGrpCat.mono_iff_injective _).mpr
      (TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB hi x)
  epi_g := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mp
    apply (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mpr
    intro U t x hx
    obtain ⟨V, hVB, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB hx
    obtain ⟨s, hs⟩ := hs V hVB (S.X₃.obj.map (homOfLE hVU).op t)
    exact ⟨V, hVU, ⟨s, hs⟩, hxV⟩

/-- The actual additive forgetful functor sends the zero module-sheaf
morphism to the zero additive-sheaf morphism. -/
instance moduleSheaf_toSheaf_preservesZeroMorphisms
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{0}) :
    (SheafOfModules.toSheaf.{0} R).PreservesZeroMorphisms where
  map_zero M N := by
    ext U s
    rfl

/-- A basis-local component criterion for the actual category of modules
over a ring sheaf. The faithful additive forgetful functor reflects the
resulting short exact sequence. -/
theorem moduleSheaf_shortExact_of_basis
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{0})
    (S : ShortComplex (SheafOfModules.{0} R))
    (B : Set (Opens X)) (hB : Opens.IsBasis B)
    (hi : ∀ U ∈ B, Function.Injective (S.f.val.app (op U)))
    (he : ∀ U ∈ B, Function.Exact (S.f.val.app (op U)) (S.g.val.app (op U)))
    (hs : ∀ U ∈ B, Function.Surjective (S.g.val.app (op U))) :
    S.ShortExact := by
  haveI : (SheafOfModules.toSheaf.{0} R).PreservesZeroMorphisms :=
    moduleSheaf_toSheaf_preservesZeroMorphisms (X := X) R
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful (SheafOfModules.toSheaf.{0} R)
  exact additiveSheaf_shortExact_of_basis (S.map (SheafOfModules.toSheaf.{0} R)) B hB hi he hs

/-- Neighborhood form of the basis criterion. Every neighborhood must
contain a smaller neighborhood with the three displayed component facts. -/
theorem moduleSheaf_shortExact_of_neighborhoods
    (R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{0})
    (S : ShortComplex (SheafOfModules.{0} R))
    (h : ∀ (U : Opens X) (x : X), x ∈ U →
      ∃ (V : Opens X), V ≤ U ∧ x ∈ V ∧
        Function.Injective (S.f.val.app (op V)) ∧
        Function.Exact (S.f.val.app (op V)) (S.g.val.app (op V)) ∧
        Function.Surjective (S.g.val.app (op V))) :
    S.ShortExact := by
  let B : Set (Opens X) := {V |
    Function.Injective (S.f.val.app (op V)) ∧
      Function.Exact (S.f.val.app (op V)) (S.g.val.app (op V)) ∧
      Function.Surjective (S.g.val.app (op V))}
  have hB : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨V, hVU, hxV, hi, he, hs⟩ := h U x hx
    exact ⟨V, ⟨hi, he, hs⟩, hxV, hVU⟩
  exact moduleSheaf_shortExact_of_basis R S B hB
    (fun _ hV => hV.1) (fun _ hV => hV.2.1) (fun _ hV => hV.2.2)

section AffineCover

open AlgebraicGeometry CycleQ2GeometricDifferentialSheaf

/-- Principal affine subopens of an open affine cover form a basis of the
actual ambient scheme. -/
theorem affineOpenImages_isBasis
    (Y : Scheme.{0}) {ι : Type} (A : ι → CommRingCat.{0})
    (j : ∀ i, Spec (A i) ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hcover : (⨆ i, (j i).opensRange) = ⊤) :
    Opens.IsBasis {V : Y.Opens | ∃ i, ∃ a : A i, V = j i ''ᵁ PrimeSpectrum.basicOpen a} := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  have hxc : x ∈ ⨆ i, (j i).opensRange := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxc
  obtain ⟨y, rfl⟩ := (Scheme.Hom.mem_opensRange).mp hi
  obtain ⟨V, ⟨a, rfl⟩, hya, haU⟩ :=
    Opens.isBasis_iff_nbhd.mp (PrimeSpectrum.isBasis_basic_opens (R := A i))
      (show y ∈ (j i) ⁻¹ᵁ U from hx)
  refine ⟨j i ''ᵁ PrimeSpectrum.basicOpen a, ⟨i, a, rfl⟩, ⟨y, hya, rfl⟩, ?_⟩
  exact ((j i).image_mono haU).trans ((j i).image_preimage_le U)

/-- The sheaf short-exactness criterion in the form used by the literal
Cartier charts: the three component properties are required on every
principal subopen of every affine chart in the actual cover. -/
theorem moduleSheaf_shortExact_of_affine_cover
    (Y : Scheme.{0}) (S : ShortComplex (SheafOfModules.{0} (ringSheaf Y.sheaf)))
    {ι : Type} (A : ι → CommRingCat.{0})
    (j : ∀ i, Spec (A i) ⟶ Y) [∀ i, IsOpenImmersion (j i)]
    (hcover : (⨆ i, (j i).opensRange) = ⊤)
    (hi : ∀ i (a : A i), Function.Injective
      (S.f.val.app (op (j i ''ᵁ PrimeSpectrum.basicOpen a))))
    (he : ∀ i (a : A i), Function.Exact
      (S.f.val.app (op (j i ''ᵁ PrimeSpectrum.basicOpen a)))
      (S.g.val.app (op (j i ''ᵁ PrimeSpectrum.basicOpen a))))
    (hs : ∀ i (a : A i), Function.Surjective
      (S.g.val.app (op (j i ''ᵁ PrimeSpectrum.basicOpen a)))) :
    S.ShortExact := by
  apply moduleSheaf_shortExact_of_basis (ringSheaf Y.sheaf) S
    {V | ∃ i, ∃ a : A i, V = j i ''ᵁ PrimeSpectrum.basicOpen a}
    (affineOpenImages_isBasis Y A j hcover)
  · rintro V ⟨i, a, rfl⟩
    exact hi i a
  · rintro V ⟨i, a, rfl⟩
    exact he i a
  · rintro V ⟨i, a, rfl⟩
    exact hs i a

end AffineCover

end CycleQ2GeometricSheafLocalExactness

#print axioms CycleQ2GeometricSheafLocalExactness.additiveSheaf_exact_of_basis
#print axioms CycleQ2GeometricSheafLocalExactness.moduleSheaf_shortExact_of_basis
#print axioms CycleQ2GeometricSheafLocalExactness.moduleSheaf_shortExact_of_neighborhoods

#print axioms CycleQ2GeometricSheafLocalExactness.moduleSheaf_shortExact_of_affine_cover

end -- component noncomputable section
end ActualSheafLocalExactness

section LiteralCartierShortExactness

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricIntrinsicCartierSequence

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafLocalExactness
open CycleQ2CartierProjectiveCover CycleQ2ProjectiveCartierIdeal
open CycleQ2IntrinsicCartierPrincipalBasis

/-- The genuine affine principal subopens of the twelve Cartier charts. -/
def cartierPrincipalBasis (r θ : ℂ) : Set (projectiveSurface r θ).Opens :=
  {V | ∃ (i : Fin 4) (j : Fin 3) (a : RefinedRing r θ i j),
    V = refinedSurfaceChart r θ i j ''ᵁ PrimeSpectrum.basicOpen a}

/-- These principal subopens form a basis of the entire projective surface. -/
theorem cartierPrincipalBasis_isBasis (r θ : ℂ) (hr : r ≠ 0) (hθ : θ ≠ 0) :
    Opens.IsBasis (cartierPrincipalBasis r θ) := by
  have hcover :
      (⨆ ij : Fin 4 × Fin 3, (refinedSurfaceChart r θ ij.1 ij.2).opensRange) = ⊤ := by
    simpa only [iSup_prod, refinedSurfaceChart_range] using refinedOpen_cover r θ hr hθ
  have h := affineOpenImages_isBasis (projectiveSurface r θ)
    (fun ij : Fin 4 × Fin 3 => CommRingCat.of (RefinedRing r θ ij.1 ij.2))
    (fun ij => refinedSurfaceChart r θ ij.1 ij.2) hcover
  convert h using 1
  ext V
  constructor
  · rintro ⟨i, j, a, ha⟩
    exact ⟨(i, j), a, ha⟩
  · rintro ⟨⟨i, j⟩, a, ha⟩
    exact ⟨i, j, a, ha⟩

/-- The original scalar/reduction complex is short exact as a genuine
module-sheaf complex. The proof uses every principal subopen of the actual
Cartier chart cover, together with the checked localized regular generators. -/
theorem literalInverseIdealComplex_shortExact_of_parameters
    (r θ : ℂ) (hr : r ≠ 0) (hθ : θ ≠ 0) :
    (literalInverseIdealComplex r θ).ShortExact := by
  apply moduleSheaf_shortExact_of_basis _ (literalInverseIdealComplex r θ)
    (cartierPrincipalBasis r θ) (cartierPrincipalBasis_isBasis r θ hr hθ)
  · rintro V ⟨i, j, a, rfl⟩
    exact (refinedPrincipal_inverseIdeal_exactness r θ i j a).1
  · rintro V ⟨i, j, a, rfl⟩
    exact (refinedPrincipal_inverseIdeal_exactness r θ i j a).2.1
  · rintro V ⟨i, j, a, rfl⟩
    exact (refinedPrincipal_inverseIdeal_exactness r θ i j a).2.2

/-- The exact original inverse-ideal short exact sequence at the literal
incidence parameters. No geometric comparison or exactness premise remains. -/
theorem literalInverseIdealComplex_shortExact :
    (literalInverseIdealComplex 57 1).ShortExact :=
  literalInverseIdealComplex_shortExact_of_parameters 57 1 (by norm_num) one_ne_zero

/-- The underlying additive sheaf complex, retaining the literal scalar
and reduction maps, for constructing its actual derived connecting map. -/
def literalInverseIdealAdditiveComplex (r θ : ℂ) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (projectiveSurface r θ)) := by
  have : (SheafOfModules.toSheaf.{0}
      (ringSheaf (projectiveSurface r θ).sheaf)).PreservesZeroMorphisms :=
    moduleSheaf_toSheaf_preservesZeroMorphisms (X := (projectiveSurface r θ : TopCat))
      (ringSheaf (projectiveSurface r θ).sheaf)
  exact (literalInverseIdealComplex r θ).map
    (SheafOfModules.toSheaf.{0} (ringSheaf (projectiveSurface r θ).sheaf))

/-- The underlying additive complex is short exact by the same actual
component calculations. This does not rely on a cokernel-preservation
assumption for the additive forgetful functor. -/
theorem literalInverseIdealAdditiveComplex_shortExact_of_parameters
    (r θ : ℂ) (hr : r ≠ 0) (hθ : θ ≠ 0) :
    (literalInverseIdealAdditiveComplex r θ).ShortExact := by
  apply additiveSheaf_shortExact_of_basis _ (cartierPrincipalBasis r θ)
    (cartierPrincipalBasis_isBasis r θ hr hθ)
  · rintro V ⟨i, j, a, rfl⟩
    exact (refinedPrincipal_inverseIdeal_exactness r θ i j a).1
  · rintro V ⟨i, j, a, rfl⟩
    exact (refinedPrincipal_inverseIdeal_exactness r θ i j a).2.1
  · rintro V ⟨i, j, a, rfl⟩
    exact (refinedPrincipal_inverseIdeal_exactness r θ i j a).2.2

/-- Short exactness of the literal incidence additive sheaf sequence. -/
theorem literalInverseIdealAdditiveComplex_shortExact :
    (literalInverseIdealAdditiveComplex 57 1).ShortExact :=
  literalInverseIdealAdditiveComplex_shortExact_of_parameters 57 1 (by norm_num) one_ne_zero

end CycleQ2GeometricIntrinsicCartierSequence

#print axioms CycleQ2GeometricIntrinsicCartierSequence.cartierPrincipalBasis_isBasis
#print axioms CycleQ2GeometricIntrinsicCartierSequence.literalInverseIdealComplex_shortExact_of_parameters
#print axioms CycleQ2GeometricIntrinsicCartierSequence.literalInverseIdealComplex_shortExact
#print axioms CycleQ2GeometricIntrinsicCartierSequence.literalInverseIdealAdditiveComplex_shortExact_of_parameters
#print axioms CycleQ2GeometricIntrinsicCartierSequence.literalInverseIdealAdditiveComplex_shortExact

end -- component noncomputable section
end LiteralCartierShortExactness
