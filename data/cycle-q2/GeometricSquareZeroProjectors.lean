import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Idempotents
import Mathlib.Tactic.NoncommRing
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Abel

section SourceSurfaceFirstOrder

/-! The actual first-order hypersurface deformation f - εa, after
quotienting by the fixed second equation.  Its square-zero ideal is
canonically the original hypersurface ring when f is regular. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricSurfaceFirstOrder

variable {R : Type*} [CommRing R]

abbrev Dual (R : Type*) := TrivSqZeroExt R R

private theorem dual_snd_mul (x y : Dual R) :
    (x * y).snd = x.fst * y.snd + x.snd * y.fst := rfl

/-- The sign is fixed: the defining relation is f - εa. -/
def relation (f a : R) : Dual R := (f, -a)

theorem relation_eq (f a : R) :
    relation f a = TrivSqZeroExt.inl f - TrivSqZeroExt.inr a := by
  apply TrivSqZeroExt.ext
  · change f = f - 0
    exact (sub_zero f).symm
  · change -a = 0 - a
    exact (zero_sub a).symm

def deformationIdeal (f a : R) : Ideal (Dual R) :=
  Ideal.span {relation f a}

abbrev Deformation (f a : R) := Dual R ⧸ deformationIdeal f a
abbrev Closed (f : R) := R ⧸ Ideal.span ({f} : Set R)

def rawReduction (f : R) : Dual R →ₐ[R] Closed f :=
  (Ideal.Quotient.mkₐ R (Ideal.span ({f} : Set R))).comp
    (TrivSqZeroExt.fstHom R R R)

@[simp] theorem rawReduction_apply (f : R) (z : Dual R) :
    rawReduction f z = Ideal.Quotient.mk (Ideal.span ({f} : Set R)) z.fst := rfl

theorem relation_mem_kernel (f a : R) :
    deformationIdeal f a ≤ RingHom.ker (rawReduction f).toRingHom := by
  apply Ideal.span_le.mpr
  rintro x (rfl : x = relation f a)
  change Ideal.Quotient.mk (Ideal.span ({f} : Set R)) f = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)

/-- Reduction modulo ε in the actual quotient by f - εa. -/
def reduction (f a : R) : Deformation f a →ₐ[R] Closed f :=
  Ideal.Quotient.liftₐ (deformationIdeal f a) (rawReduction f)
    (fun x hx => relation_mem_kernel f a hx)

@[simp] theorem reduction_mk (f a : R) (z : Dual R) :
    reduction f a (Ideal.Quotient.mk (deformationIdeal f a) z) =
      Ideal.Quotient.mk (Ideal.span ({f} : Set R)) z.fst := rfl

theorem reduction_surjective (f a : R) : Function.Surjective (reduction f a) := by
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (deformationIdeal f a) (TrivSqZeroExt.inl b), rfl⟩

def rawEpsilon (f a : R) : R →ₗ[R] Deformation f a :=
  (Ideal.Quotient.mkₐ R (deformationIdeal f a)).toLinearMap.comp
    (TrivSqZeroExt.inrHom R R)

@[simp] theorem rawEpsilon_apply (f a b : R) :
    rawEpsilon f a b =
      Ideal.Quotient.mk (deformationIdeal f a) (TrivSqZeroExt.inr b) := rfl

theorem rawEpsilon_f (f a : R) : rawEpsilon f a f = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨(TrivSqZeroExt.inr (1 : R) : Dual R), ?_⟩
  apply TrivSqZeroExt.ext
  · change (0 : R) * f = 0
    exact zero_mul f
  · change (0 : R) * (-a) + 1 * f = f
    rw [zero_mul, one_mul, zero_add]

/-- The canonical map [b] ↦ εb. It is defined without choosing a section
of the deformed ring onto the original ring. -/
def epsilon (f a : R) : Closed f →ₗ[R] Deformation f a :=
  (Ideal.span ({f} : Set R)).liftQ (rawEpsilon f a) (by
    apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = f := hx
    change rawEpsilon f a x = 0
    rw [hx']
    exact rawEpsilon_f f a)

@[simp] theorem epsilon_mk (f a b : R) :
    epsilon f a (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) b) =
      Ideal.Quotient.mk (deformationIdeal f a) (TrivSqZeroExt.inr b) := rfl

@[simp] theorem reduction_epsilon (f a : R) (x : Closed f) :
    reduction f a (epsilon f a x) = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [epsilon_mk, reduction_mk, TrivSqZeroExt.fst_inr, map_zero]

/-- This is the regularity argument making the coefficient of ε faithful.
It works over rings with zero divisors; only f is required to be regular. -/
theorem inr_mem_deformationIdeal_iff (f a : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) (b : R) :
    TrivSqZeroExt.inr b ∈ deformationIdeal f a ↔
      b ∈ Ideal.span ({f} : Set R) := by
  constructor
  · intro hb
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hb
    have hfst : f * z.fst = 0 := by
      have h := congrArg TrivSqZeroExt.fst hz
      change z.fst * f = 0 at h
      simpa only [mul_comm] using h
    have hz0 := hf z.fst hfst
    have hsnd : z.snd * f = b := by
      have h := congrArg TrivSqZeroExt.snd hz
      change z.fst * (-a) + z.snd * f = b at h
      simpa only [hz0, zero_mul, zero_add] using h
    exact Ideal.mem_span_singleton'.mpr ⟨z.snd, hsnd⟩
  · intro hb
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hb
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨(TrivSqZeroExt.inr u : Dual R), ?_⟩
    apply TrivSqZeroExt.ext
    · change (0 : R) * f = 0
      exact zero_mul f
    · change (0 : R) * (-a) + u * f = b
      simpa only [zero_mul, zero_add] using hu

theorem epsilon_eq_zero_iff (f a : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) (x : Closed f) :
    epsilon f a x = 0 ↔ x = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [epsilon_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
  exact inr_mem_deformationIdeal_iff f a hf b

theorem epsilon_injective (f a : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) : Function.Injective (epsilon f a) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (epsilon_eq_zero_iff f a hf (x - y)).mp
  rw [map_sub, hxy, sub_self]

/-- Every element killed by reduction is an actual ε-multiple. -/
theorem reduction_eq_zero_iff (f a : R) (z : Deformation f a) :
    reduction f a z = 0 ↔ ∃ x : Closed f, epsilon f a x = z := by
  constructor
  · obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    intro hw
    have hw' : w.fst ∈ Ideal.span ({f} : Set R) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hw
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hw'
    refine ⟨Ideal.Quotient.mk (Ideal.span ({f} : Set R)) (w.snd + u * a), ?_⟩
    rw [epsilon_mk]
    apply Eq.symm
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨(TrivSqZeroExt.inl u : Dual R), ?_⟩
    apply TrivSqZeroExt.ext
    · change u * f = w.fst - 0
      simpa only [sub_zero] using hu
    · change u * (-a) + 0 * f = w.snd - (w.snd + u * a)
      ring
  · rintro ⟨x, rfl⟩
    exact reduction_epsilon f a x

/-- The actual kernel, rather than a chosen vector space of the same rank,
is canonically identified with the original hypersurface quotient. -/
def kernelEquiv (f a : R) (hf : ∀ x : R, f * x = 0 → x = 0) :
    Closed f ≃ₗ[R] LinearMap.ker (reduction f a).toLinearMap :=
  LinearEquiv.ofBijective
    ((epsilon f a).codRestrict _ (fun x => reduction_epsilon f a x)) (by
      constructor
      · intro x y hxy
        exact epsilon_injective f a hf (congrArg Subtype.val hxy)
      · rintro ⟨z, hz⟩
        obtain ⟨x, hx⟩ := (reduction_eq_zero_iff f a z).mp hz
        exact ⟨x, Subtype.ext hx⟩)

@[simp] theorem kernelEquiv_val (f a : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) (x : Closed f) :
    (kernelEquiv f a hf x).val = epsilon f a x := rfl

theorem epsilon_mul_epsilon (f a : R) (x y : Closed f) :
    epsilon f a x * epsilon f a y = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [epsilon_mk, epsilon_mk, ← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero]

theorem kernel_mul_zero (f a : R) (x y : Deformation f a)
    (hx : reduction f a x = 0) (hy : reduction f a y = 0) : x * y = 0 := by
  obtain ⟨b, rfl⟩ := (reduction_eq_zero_iff f a x).mp hx
  obtain ⟨c, rfl⟩ := (reduction_eq_zero_iff f a y).mp hy
  exact epsilon_mul_epsilon f a b c

/-- Multiplication on the square-zero kernel uses precisely the reduced
surface function, the action needed for actual overlap endomorphisms. -/
theorem mul_epsilon (f a : R) (z : Deformation f a) (x : Closed f) :
    z * epsilon f a x = epsilon f a (reduction f a z * x) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [epsilon_mk, reduction_mk,
    ← map_mul (Ideal.Quotient.mk (Ideal.span ({f} : Set R))), epsilon_mk,
    ← map_mul (Ideal.Quotient.mk (deformationIdeal f a))]
  congr 1
  apply TrivSqZeroExt.ext
  · simp
  · simp [dual_snd_mul]

end CycleQ2GeometricSurfaceFirstOrder

#print axioms CycleQ2GeometricSurfaceFirstOrder.epsilon_injective
#print axioms CycleQ2GeometricSurfaceFirstOrder.reduction_eq_zero_iff
#print axioms CycleQ2GeometricSurfaceFirstOrder.kernelEquiv
#print axioms CycleQ2GeometricSurfaceFirstOrder.kernel_mul_zero
#print axioms CycleQ2GeometricSurfaceFirstOrder.mul_epsilon

end
end SourceSurfaceFirstOrder

section SourceRankOneImageEnd

/-! A rank-one matrix with a proved unit-ideal entry certificate has its
actual image as a projective module, and every endomorphism of that image
is multiplication by a unique scalar. No local freeness premise is used. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricRankOneImage

open Matrix
open scoped BigOperators

variable {R m n : Type*} [CommRing R] [Fintype m] [Fintype n] [DecidableEq n]

abbrev Image (M : Matrix m n R) := LinearMap.range M.mulVecLin

def column (M : Matrix m n R) (j : n) : Image M :=
  ⟨M.col j, ⟨Pi.single j 1, Matrix.mulVec_single_one M j⟩⟩

@[simp] theorem column_val (M : Matrix m n R) (j : n) (i : m) :
    (column M j).val i = M i j := rfl

/-- All two by two minors vanish on any two actual image vectors. -/
theorem image_minors (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (u v : Image M) (i k : m) : u.val i * v.val k = u.val k * v.val i := by
  obtain ⟨x, hx⟩ := u.property
  obtain ⟨y, hy⟩ := v.property
  change u.val i * v.val k = u.val k * v.val i
  rw [← hx, ← hy]
  change (∑ j, M i j * x j) * (∑ l, M k l * y l) =
    (∑ j, M k j * x j) * (∑ l, M i l * y l)
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  calc
    (M i j * x j) * (M k l * y l) = (M i j * M k l) * (x j * y l) := by ring
    _ = (M k j * M i l) * (x j * y l) := by rw [hM]
    _ = (M k j * x j) * (M i l * y l) := by ring

/-- The unit-ideal certificate reconstructs every actual image vector. -/
theorem reconstruction (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1) (x : Image M) :
    (∑ q, (w q * x.val q.1) • column M q.2) = x := by
  apply Subtype.ext
  funext k
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, column_val]
  calc
    ∑ q, (w q * x.val q.1) * M k q.2 =
        ∑ q, (w q * M q.1 q.2) * x.val k := by
      apply Finset.sum_congr rfl
      intro q _
      have h := image_minors M hM (column M q.2) x q.1 k
      change M q.1 q.2 * x.val k = M k q.2 * x.val q.1 at h
      calc
        (w q * x.val q.1) * M k q.2 = w q * (M k q.2 * x.val q.1) := by ring
        _ = w q * (M q.1 q.2 * x.val k) := by rw [h]
        _ = (w q * M q.1 q.2) * x.val k := by ring
    _ = (∑ q, w q * M q.1 q.2) * x.val k := (Finset.sum_mul ..).symm
    _ = x.val k := by rw [hw, one_mul]

/-- An explicit retraction onto the actual matrix image. -/
def projection (M : Matrix m n R) (w : m × n → R) :
    (m → R) →ₗ[R] Image M where
  toFun x := ∑ q, (w q * x q.1) • column M q.2
  map_add' x y := by
    simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
      smul_smul]
    apply Finset.sum_congr rfl
    intro q _
    congr 1
    ring

theorem projection_retract (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1) (x : Image M) :
    projection M w x.val = x := reconstruction M hM w hw x

def ambientProjection (M : Matrix m n R) (w : m × n → R) :
    Module.End R (m → R) := (LinearMap.range M.mulVecLin).subtype.comp (projection M w)

theorem ambientProjection_idempotent (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1) :
    (ambientProjection M w).comp (ambientProjection M w) = ambientProjection M w := by
  ext x i
  exact congrArg (fun z : Image M => z.val i)
    (projection_retract M hM w hw (projection M w x))

/-- Scalar extraction from an endomorphism of the actual image, using
the same finite unit-ideal certificate as the image projector. -/
def scalar (M : Matrix m n R) (w : m × n → R) :
    Module.End R (Image M) →ₗ[R] R where
  toFun φ := ∑ q, w q * (φ (column M q.2)).val q.1
  map_add' φ ψ := by
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
      mul_add, Finset.sum_add_distrib]
  map_smul' c φ := by
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring

def scalarMap (M : Matrix m n R) : R →ₗ[R] Module.End R (Image M) where
  toFun c := c • LinearMap.id
  map_add' c d := add_smul c d _
  map_smul' c d := by simp only [smul_eq_mul, RingHom.id_apply, smul_smul]

@[simp] theorem scalarMap_apply (M : Matrix m n R) (c : R) (x : Image M) :
    scalarMap M c x = c • x := rfl

theorem scalar_scalarMap (M : Matrix m n R) (w : m × n → R)
    (hw : ∑ q, w q * M q.1 q.2 = 1) (c : R) : scalar M w (scalarMap M c) = c := by
  change (∑ q, w q * (c • column M q.2).val q.1) = c
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, column_val]
  calc
    ∑ q, w q * (c * M q.1 q.2) = c * (∑ q, w q * M q.1 q.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = c := by rw [hw, mul_one]

theorem scalar_reconstruction (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1)
    (φ : Module.End R (Image M)) (x : Image M) :
    scalar M w φ • x = φ x := by
  apply Subtype.ext
  funext k
  change (∑ q, w q * (φ (column M q.2)).val q.1) * x.val k = (φ x).val k
  calc
    (∑ q, w q * (φ (column M q.2)).val q.1) * x.val k =
        ∑ q, (w q * (φ (column M q.2)).val q.1) * x.val k := Finset.sum_mul ..
    _ = ∑ q, (w q * x.val q.1) * (φ (column M q.2)).val k := by
      apply Finset.sum_congr rfl
      intro q _
      have h := image_minors M hM (φ (column M q.2)) x q.1 k
      calc
        (w q * (φ (column M q.2)).val q.1) * x.val k =
            w q * ((φ (column M q.2)).val q.1 * x.val k) := by ring
        _ = w q * ((φ (column M q.2)).val k * x.val q.1) := by rw [h]
        _ = (w q * x.val q.1) * (φ (column M q.2)).val k := by ring
    _ = (φ (∑ q, (w q * x.val q.1) • column M q.2)).val k := by
      simp only [map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply,
        Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    _ = (φ x).val k := by rw [reconstruction M hM w hw x]

/-- The identification is faithful in the original ring, including
nilpotents and zero divisors, and is inverse to actual scalar multiplication. -/
def endEquiv (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1) :
    Module.End R (Image M) ≃ₗ[R] R where
  __ := scalar M w
  invFun := scalarMap M
  left_inv φ := LinearMap.ext (scalar_reconstruction M hM w hw φ)
  right_inv c := scalar_scalarMap M w hw c

@[simp] theorem endEquiv_symm_apply (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1) (c : R) (x : Image M) :
    (endEquiv M hM w hw).symm c x = c • x := rfl

end CycleQ2GeometricRankOneImage

#print axioms CycleQ2GeometricRankOneImage.projection_retract
#print axioms CycleQ2GeometricRankOneImage.ambientProjection_idempotent
#print axioms CycleQ2GeometricRankOneImage.scalar_reconstruction
#print axioms CycleQ2GeometricRankOneImage.endEquiv

end
end SourceRankOneImageEnd

section SourceSurfaceProjectorLift

/-! Actual projectors onto the actual matrix image lift through any
surjective square-zero ring map.  The nilpotent-idempotent theorem is
applied to the genuine matrix reduction map, not an abstract deformation
space. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricRankOneImage

open Matrix
open scoped BigOperators

variable {R E m n : Type*} [CommRing R] [CommRing E]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- All projectors constructed from entry certificates have the same
actual image; the left one acts as the identity on the right one's image. -/
theorem ambientProjection_comp (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1)
    (v : m × n → R) :
    (ambientProjection M w).comp (ambientProjection M v) = ambientProjection M v := by
  apply LinearMap.ext
  intro x
  exact congrArg Subtype.val
    (projection_retract M hM w hw (projection M v x))

def projectorMatrix (M : Matrix m n R) (w : m × n → R) : Matrix m m R :=
  LinearMap.toMatrix' (ambientProjection M w)

theorem projectorMatrix_mul (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1)
    (v : m × n → R) :
    projectorMatrix M w * projectorMatrix M v = projectorMatrix M v := by
  rw [projectorMatrix, projectorMatrix, ← LinearMap.toMatrix'_comp,
    ambientProjection_comp M hM w hw v]

theorem projectorMatrix_idempotent (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1) :
    IsIdempotentElem (projectorMatrix M w) :=
  projectorMatrix_mul M hM w hw w

/-- A square-zero coefficient kernel gives a square-zero matrix kernel,
without a domain or reducedness assumption. -/
theorem matrix_kernel_square_zero (ρ : E →+* R)
    (hρ : ∀ x y : E, ρ x = 0 → ρ y = 0 → x * y = 0)
    (X Y : Matrix m m E) (hX : ρ.mapMatrix X = 0) (hY : ρ.mapMatrix Y = 0) :
    X * Y = 0 := by
  ext i j
  change (∑ k, X i k * Y k j) = 0
  apply Finset.sum_eq_zero
  intro k _
  apply hρ
  · exact congrArg (fun Z : Matrix m m R => Z i k) hX
  · exact congrArg (fun Z : Matrix m m R => Z k j) hY

theorem exists_idempotent_matrix_lift (ρ : E →+* R)
    (hρsurj : Function.Surjective ρ)
    (hρsq : ∀ x y : E, ρ x = 0 → ρ y = 0 → x * y = 0)
    (P : Matrix m m R) (hP : IsIdempotentElem P) :
    ∃ Q : Matrix m m E, IsIdempotentElem Q ∧ ρ.mapMatrix Q = P := by
  let ρM : Matrix m m E →+* Matrix m m R := ρ.mapMatrix
  refine exists_isIdempotentElem_eq_of_ker_isNilpotent ρM ?_ P ?_ hP
  · intro X hX
    refine ⟨2, ?_⟩
    rw [pow_two]
    exact matrix_kernel_square_zero ρ hρsq X X hX hX
  · refine ⟨fun i j => (hρsurj (P i j)).choose, ?_⟩
    ext i j
    exact (hρsurj (P i j)).choose_spec

/-- The supplied projector is the one onto the genuine image of M.
In the family application ρ is reduction of the actual F - εA quotient. -/
theorem exists_image_projector_lift (ρ : E →+* R)
    (hρsurj : Function.Surjective ρ)
    (hρsq : ∀ x y : E, ρ x = 0 → ρ y = 0 → x * y = 0)
    (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1) :
    ∃ Q : Matrix m m E, IsIdempotentElem Q ∧
      ρ.mapMatrix Q = projectorMatrix M w :=
  exists_idempotent_matrix_lift ρ hρsurj hρsq _
    (projectorMatrix_idempotent M hM w hw)

end CycleQ2GeometricRankOneImage

#print axioms CycleQ2GeometricRankOneImage.projectorMatrix_mul
#print axioms CycleQ2GeometricRankOneImage.matrix_kernel_square_zero
#print axioms CycleQ2GeometricRankOneImage.exists_image_projector_lift

end
end SourceSurfaceProjectorLift

section SourceProjectorDefect

/-! The associative algebra of the actual projector obstruction.  The
coefficient interface below records a faithful square-zero kernel; the
first-order surface extension supplies it without a flatness hypothesis.
The sign convention is product minus direct transition throughout. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricProjectorDefect

variable {E R : Type*} [Ring E] [Ring R]

def defect (x y z : E) : E := x * y * z - x * z

/-- Associativity gives the obstruction identity before any extraction
of an epsilon coefficient or identification of an image module. -/
theorem defect_identity (x y z w : E) :
    x * defect y z w - defect x z w + defect x y w - defect x y z * w = 0 := by
  unfold defect
  noncomm_ring

theorem defect_left (x y z : E) (hx : x * x = x) :
    x * defect x y z = defect x y z := by
  simp only [defect, mul_sub, ← mul_assoc, hx]

theorem defect_right (x y z : E) (hz : z * z = z) :
    defect x y z * z = defect x y z := by
  simp only [defect, sub_mul, mul_assoc, hz]

/-- The reduced projectors act identically on their common actual image. -/
theorem reduction_defect (ρ : E →+* R) (x y z : E)
    (hxy : ρ x * ρ y = ρ y) (hyz : ρ y * ρ z = ρ z)
    (hxz : ρ x * ρ z = ρ z) : ρ (defect x y z) = 0 := by
  simp only [defect, map_sub, map_mul, hxy, hyz, hxz, sub_self]

/-- A coefficient map for a faithful square-zero kernel.  Both module
actions are explicit so this also applies to matrices over the deformed
surface ring, which form a noncommutative ring. -/
structure Coefficients (ρ : E →+* R) where
  epsilon : R →+ E
  injective : Function.Injective epsilon
  reduction_epsilon : ∀ x, ρ (epsilon x) = 0
  exact_kernel : ∀ z, ρ z = 0 → ∃ x, epsilon x = z
  mul_epsilon : ∀ z x, z * epsilon x = epsilon (ρ z * x)
  epsilon_mul : ∀ x z, epsilon x * z = epsilon (x * ρ z)

namespace Coefficients

variable {ρ : E →+* R} (K : Coefficients ρ)

def coefficient (z : E) (hz : ρ z = 0) : R :=
  Classical.choose (K.exact_kernel z hz)

@[simp] theorem epsilon_coefficient (z : E) (hz : ρ z = 0) :
    K.epsilon (K.coefficient z hz) = z := Classical.choose_spec (K.exact_kernel z hz)

theorem epsilon_mul_epsilon (x y : R) : K.epsilon x * K.epsilon y = 0 := by
  rw [K.epsilon_mul, K.reduction_epsilon, mul_zero, map_zero]

theorem coefficient_epsilon (x : R) :
    K.coefficient (K.epsilon x) (K.reduction_epsilon x) = x := by
  apply K.injective
  exact K.epsilon_coefficient _ _

def triple (x y z : E) (hxy : ρ x * ρ y = ρ y)
    (hyz : ρ y * ρ z = ρ z) (hxz : ρ x * ρ z = ρ z) : R :=
  K.coefficient (defect x y z) (reduction_defect ρ x y z hxy hyz hxz)

@[simp] theorem epsilon_triple (x y z : E) (hxy : ρ x * ρ y = ρ y)
    (hyz : ρ y * ρ z = ρ z) (hxz : ρ x * ρ z = ρ z) :
    K.epsilon (K.triple x y z hxy hyz hxz) = defect x y z :=
  K.epsilon_coefficient _ _

section Family

variable {I : Type*} (e : I → E)
  (hP : ∀ i j, ρ (e i) * ρ (e j) = ρ (e j))

def cochain (i j k : I) : R :=
  K.triple (e i) (e j) (e k) (hP i j) (hP j k) (hP i k)

@[simp] theorem epsilon_cochain (i j k : I) :
    K.epsilon (K.cochain e hP i j k) = defect (e i) (e j) (e k) :=
  K.epsilon_triple _ _ _ _ _ _

/-- This weighted identity is valid as a matrix identity.  On the actual
common image, its outer projectors act as identities and it is the Cech
two-cocycle identity. -/
theorem cochain_identity (i j k l : I) :
    ρ (e i) * K.cochain e hP j k l - K.cochain e hP i k l +
      K.cochain e hP i j l - K.cochain e hP i j k * ρ (e l) = 0 := by
  apply K.injective
  rw [map_sub, map_add, map_sub, ← K.mul_epsilon, ← K.epsilon_mul,
    K.epsilon_cochain, K.epsilon_cochain, K.epsilon_cochain, K.epsilon_cochain, map_zero]
  exact defect_identity _ _ _ _

theorem cochain_left (he : ∀ i, e i * e i = e i) (i j k : I) :
    ρ (e i) * K.cochain e hP i j k = K.cochain e hP i j k := by
  apply K.injective
  rw [← K.mul_epsilon, K.epsilon_cochain]
  exact defect_left _ _ _ (he i)

theorem cochain_right (he : ∀ i, e i * e i = e i) (i j k : I) :
    K.cochain e hP i j k * ρ (e k) = K.cochain e hP i j k := by
  apply K.injective
  rw [← K.epsilon_mul, K.epsilon_cochain]
  exact defect_right _ _ _ (he k)

/-- Restricting to the common image removes both outer transports. -/
theorem cochain_cocycle_on_image (he : ∀ i, e i * e i = e i)
    (i j k l : I) (v : R) (hv : ∀ a, ρ (e a) * v = v) :
    (K.cochain e hP j k l - K.cochain e hP i k l +
      K.cochain e hP i j l - K.cochain e hP i j k) * v = 0 := by
  have hij : ρ (e i) * K.cochain e hP j k l = K.cochain e hP j k l := by
    calc
      ρ (e i) * K.cochain e hP j k l =
          ρ (e i) * (ρ (e j) * K.cochain e hP j k l) := by rw [K.cochain_left e hP he]
      _ = K.cochain e hP j k l := by rw [← mul_assoc, hP, K.cochain_left e hP he]
  have h := congrArg (fun z : R => z * v) (K.cochain_identity e hP i j k l)
  simpa only [sub_mul, add_mul, hij, mul_assoc, hv, zero_mul] using h

end Family

/-- Expansion contains only one epsilon factor: every product of two
kernel elements vanishes.  No commutativity of matrices is used. -/
theorem defect_perturbation (x y z : E) (s t u : R) :
    defect (x + K.epsilon s) (y + K.epsilon t) (z + K.epsilon u) =
      defect x y z + K.epsilon
        (s * ρ y * ρ z + ρ x * t * ρ z + ρ x * ρ y * u - s * ρ z - ρ x * u) := by
  simp only [defect, add_mul, mul_add, K.reduction_epsilon,
    zero_mul, mul_zero, add_zero, zero_add, K.mul_epsilon, K.epsilon_mul,
    map_mul, map_add, map_sub, map_zero]
  noncomm_ring

/-- Changing the lifted projectors changes the actual coefficient by an
explicit coboundary after restriction to their common image. -/
theorem defect_perturbation_common_image (x y z : E) (s t u : R)
    (hxy : ρ x * ρ y = ρ y) (hyz : ρ y * ρ z = ρ z) :
    defect (x + K.epsilon s) (y + K.epsilon t) (z + K.epsilon u) =
      defect x y z + K.epsilon
        (ρ y * u - ρ x * u + ρ x * t * ρ z) := by
  rw [K.defect_perturbation]
  congr 1
  congr 1
  rw [mul_assoc s, hyz, hxy]
  noncomm_ring

section Naturality

variable {E' R' : Type*} [Ring E'] [Ring R'] {ρ' : E' →+* R'}
  (K' : Coefficients ρ') (f : E →+* E') (g : R →+* R')
  (hρ : ∀ z, ρ' (f z) = g (ρ z))

/-- The coefficient is compatible with the actual map of extensions,
including specialization and principal restriction. -/
theorem coefficient_natural
    (hε : ∀ x, f (K.epsilon x) = K'.epsilon (g x)) (z : E) (hz : ρ z = 0) :
    g (K.coefficient z hz) =
      K'.coefficient (f z) (by rw [hρ, hz, map_zero]) := by
  apply K'.injective
  rw [← hε, K.epsilon_coefficient, K'.epsilon_coefficient]

end Naturality

/-- The actual ambient-test character scales epsilon.  This variant
retains that scalar rather than assuming the parameter is fixed. -/
theorem coefficient_natural_scaled
    {E' R' : Type*} [Ring E'] [Ring R'] {ρ' : E' →+* R'}
    (K' : Coefficients ρ') (f : E →+* E') (g : R →+* R') (c : R')
    (hρ : ∀ z, ρ' (f z) = g (ρ z))
    (hε : ∀ x, f (K.epsilon x) = K'.epsilon (c * g x))
    (z : E) (hz : ρ z = 0) :
    c * g (K.coefficient z hz) =
      K'.coefficient (f z) (by rw [hρ, hz, map_zero]) := by
  apply K'.injective
  rw [← hε, K.epsilon_coefficient, K'.epsilon_coefficient]

end Coefficients
end CycleQ2GeometricProjectorDefect

#print axioms CycleQ2GeometricProjectorDefect.defect_identity
#print axioms CycleQ2GeometricProjectorDefect.Coefficients.cochain_cocycle_on_image
#print axioms CycleQ2GeometricProjectorDefect.Coefficients.defect_perturbation_common_image
#print axioms CycleQ2GeometricProjectorDefect.Coefficients.coefficient_natural
#print axioms CycleQ2GeometricProjectorDefect.Coefficients.coefficient_natural_scaled

end
end SourceProjectorDefect

section SourceMatrixProjectorDefect

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricProjectorDefect.Coefficients

open scoped BigOperators

variable {E R : Type*} [Ring E] [Ring R] {ρ : E →+* R}
  (K : CycleQ2GeometricProjectorDefect.Coefficients ρ)

/-- Applying the actual epsilon map to every matrix entry supplies the
faithful square-zero coefficients for the lifted image projectors. -/
def matrixCoefficients (n : Type*) [Fintype n] [DecidableEq n] :
    CycleQ2GeometricProjectorDefect.Coefficients
      (ρ.mapMatrix : Matrix n n E →+* Matrix n n R) where
  epsilon := K.epsilon.mapMatrix
  injective := by
    intro A B h
    ext i j
    apply K.injective
    exact congrArg (fun M : Matrix n n E => M i j) h
  reduction_epsilon := by
    intro A
    ext i j
    exact K.reduction_epsilon (A i j)
  exact_kernel := by
    intro Z hZ
    have hentry : ∀ i j, ρ (Z i j) = 0 := fun i j =>
      congrArg (fun M : Matrix n n R => M i j) hZ
    refine ⟨fun i j => K.coefficient (Z i j) (hentry i j), ?_⟩
    ext i j
    exact K.epsilon_coefficient _ _
  mul_epsilon := by
    intro Z A
    ext i j
    change (∑ k, Z i k * K.epsilon (A k j)) =
      K.epsilon (∑ k, ρ (Z i k) * A k j)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact K.mul_epsilon _ _
  epsilon_mul := by
    intro A Z
    ext i j
    change (∑ k, K.epsilon (A i k) * Z k j) =
      K.epsilon (∑ k, A i k * ρ (Z k j))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact K.epsilon_mul _ _

@[simp] theorem matrixCoefficients_epsilon_apply
    (n : Type*) [Fintype n] [DecidableEq n] (A : Matrix n n R) (i j : n) :
    (K.matrixCoefficients n).epsilon A i j = K.epsilon (A i j) := rfl

/-- Matrix coefficient extraction is exactly entrywise scalar extraction. -/
theorem matrixCoefficients_coefficient_apply
    (n : Type*) [Fintype n] [DecidableEq n] (Z : Matrix n n E)
    (hZ : (ρ.mapMatrix : Matrix n n E →+* Matrix n n R) Z = 0) (i j : n) :
    (K.matrixCoefficients n).coefficient Z hZ i j =
      K.coefficient (Z i j) (congrArg (fun M : Matrix n n R => M i j) hZ) := by
  apply K.injective
  have h := congrArg (fun M : Matrix n n E => M i j)
    ((K.matrixCoefficients n).epsilon_coefficient Z hZ)
  change K.epsilon ((K.matrixCoefficients n).coefficient Z hZ i j) = Z i j at h
  exact h.trans (K.epsilon_coefficient _ _).symm

end CycleQ2GeometricProjectorDefect.Coefficients

#print axioms CycleQ2GeometricProjectorDefect.Coefficients.matrixCoefficients
#print axioms CycleQ2GeometricProjectorDefect.Coefficients.matrixCoefficients_coefficient_apply

end
end SourceMatrixProjectorDefect

section SourceProjectorChoiceIndependence

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricProjectorDefect.Coefficients

variable {E R I : Type*} [Ring E] [Ring R] {ρ : E →+* R}
  (K : CycleQ2GeometricProjectorDefect.Coefficients ρ)
  (e : I → E) (hP : ∀ i j, ρ (e i) * ρ (e j) = ρ (e j))

def perturbed (s : I → R) (i : I) : E := e i + K.epsilon (s i)

@[simp] theorem reduction_perturbed (s : I → R) (i : I) :
    ρ (K.perturbed e s i) = ρ (e i) := by
  rw [perturbed, map_add, K.reduction_epsilon, add_zero]

theorem perturbed_common_image
    (hP : ∀ i j, ρ (e i) * ρ (e j) = ρ (e j)) (s : I → R) (i j : I) :
    ρ (K.perturbed e s i) * ρ (K.perturbed e s j) =
      ρ (K.perturbed e s j) := by
  simpa only [K.reduction_perturbed] using hP i j

def perturbedCochain (s : I → R) (i j k : I) : R :=
  K.cochain (K.perturbed e s) (K.perturbed_common_image e hP s) i j k

@[simp] theorem epsilon_perturbedCochain (s : I → R) (i j k : I) :
    K.epsilon (K.perturbedCochain e hP s i j k) =
      defect (K.perturbed e s i) (K.perturbed e s j) (K.perturbed e s k) :=
  K.epsilon_cochain _ _ _ _ _

/-- The actual change of the extracted coefficient.  The expression
keeps the right projector until it is restricted to the common image. -/
theorem cochain_difference (s : I → R) (i j k : I) :
    K.perturbedCochain e hP s i j k - K.cochain e hP i j k =
      ρ (e j) * s k - ρ (e i) * s k + ρ (e i) * s j * ρ (e k) := by
  apply K.injective
  rw [map_sub, K.epsilon_perturbedCochain, K.epsilon_cochain]
  change defect (e i + K.epsilon (s i)) (e j + K.epsilon (s j))
      (e k + K.epsilon (s k)) - defect (e i) (e j) (e k) = _
  rw [K.defect_perturbation_common_image _ _ _ _ _ _ (hP i j) (hP j k)]
  exact add_sub_cancel_left _ _

/-- Pairwise correction whose Cech boundary is the change of obstruction. -/
def pairCorrection (s : I → R) (i j : I) : R := ρ (e i) * s j

theorem cochain_difference_on_image (s : I → R) (i j k : I)
    (v : R) (hv : ρ (e k) * v = v) :
    (K.perturbedCochain e hP s i j k - K.cochain e hP i j k) * v =
      (pairCorrection (ρ := ρ) e s j k - pairCorrection (ρ := ρ) e s i k +
        pairCorrection (ρ := ρ) e s i j) * v := by
  rw [K.cochain_difference e hP s i j k]
  simp only [pairCorrection, add_mul, sub_mul, mul_assoc, hv]

/-- Every second choice of lifts of the same reduced projectors has
exactly this perturbation form; no section of the extension is chosen. -/
theorem exists_perturbation (e' : I → E) (h : ∀ i, ρ (e' i) = ρ (e i)) :
    ∃ s : I → R, e' = K.perturbed e s := by
  have hz : ∀ i, ρ (e' i - e i) = 0 := by
    intro i
    rw [map_sub, h, sub_self]
  refine ⟨fun i => K.coefficient (e' i - e i) (hz i), ?_⟩
  funext i
  rw [perturbed, K.epsilon_coefficient]
  noncomm_ring

end CycleQ2GeometricProjectorDefect.Coefficients

#print axioms CycleQ2GeometricProjectorDefect.Coefficients.cochain_difference
#print axioms CycleQ2GeometricProjectorDefect.Coefficients.cochain_difference_on_image
#print axioms CycleQ2GeometricProjectorDefect.Coefficients.exists_perturbation

end
end SourceProjectorChoiceIndependence

section SourceProjectorPrism

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricProjectorDefect

section Additive

variable {I J A : Type*} [AddCommGroup A]

def prismCorrection (c : J → J → J → A) (f g : I → J) (i j : I) : A :=
  c (f i) (g i) (g j) - c (f i) (f j) (g j)

/-- The mixed-cover prism gives an explicit boundary between two
restrictions of the same two-cocycle. Alternation is not assumed. -/
theorem prism_boundary (c : J → J → J → A)
    (hc : ∀ i j k l, c j k l - c i k l + c i j l - c i j k = 0)
    (f g : I → J) (i j k : I) :
    c (g i) (g j) (g k) - c (f i) (f j) (f k) =
      prismCorrection c f g j k - prismCorrection c f g i k +
        prismCorrection c f g i j := by
  apply sub_eq_zero.mp
  calc
    c (g i) (g j) (g k) - c (f i) (f j) (f k) -
        (prismCorrection c f g j k - prismCorrection c f g i k +
          prismCorrection c f g i j) =
      (c (g i) (g j) (g k) - c (f i) (g j) (g k) +
        c (f i) (g i) (g k) - c (f i) (g i) (g j)) -
      (c (f j) (g j) (g k) - c (f i) (g j) (g k) +
        c (f i) (f j) (g k) - c (f i) (f j) (g j)) +
      (c (f j) (f k) (g k) - c (f i) (f k) (g k) +
        c (f i) (f j) (g k) - c (f i) (f j) (f k)) := by
          unfold prismCorrection
          abel
    _ = 0 := by rw [hc, hc, hc, sub_self, add_zero]

end Additive

namespace Coefficients

variable {E R I J : Type*} [Ring E] [Ring R] {ρ : E →+* R}
  (K : CycleQ2GeometricProjectorDefect.Coefficients ρ)
  (e : J → E) (hP : ∀ i j, ρ (e i) * ρ (e j) = ρ (e j))

/-- Independence holds even when the two reduced projectors differ:
they need only project onto the same actual image.  One applies this
to the union of the two projector families. -/
theorem cochain_prism_on_image (he : ∀ i, e i * e i = e i)
    (f g : I → J) (i j k : I) (v : R) (hv : ∀ a, ρ (e a) * v = v) :
    (K.cochain e hP (g i) (g j) (g k) -
      K.cochain e hP (f i) (f j) (f k)) * v =
      (prismCorrection (K.cochain e hP) f g j k -
        prismCorrection (K.cochain e hP) f g i k +
        prismCorrection (K.cochain e hP) f g i j) * v := by
  have hc : ∀ a b c d,
      K.cochain e hP b c d * v - K.cochain e hP a c d * v +
        K.cochain e hP a b d * v - K.cochain e hP a b c * v = 0 := by
    intro a b c d
    simpa only [sub_mul, add_mul] using
      K.cochain_cocycle_on_image e hP he a b c d v hv
  simpa only [prismCorrection, sub_mul, add_mul] using
    prism_boundary (fun a b c => K.cochain e hP a b c * v) hc f g i j k

end Coefficients
end CycleQ2GeometricProjectorDefect

#print axioms CycleQ2GeometricProjectorDefect.prism_boundary
#print axioms CycleQ2GeometricProjectorDefect.Coefficients.cochain_prism_on_image

end
end SourceProjectorPrism
