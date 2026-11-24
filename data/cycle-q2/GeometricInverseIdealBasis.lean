import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Dual.Basis
import Proposal.GeometricSeedNormalIdeals
import Proposal.GeometricSurfaceCoordinates
import Mathlib.RingTheory.AlgebraTower
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Localization.Algebra


/-!
A basis for the actual ideal (f, x) in a cubic algebra with constant
coefficient divisible by f. This is a preparatory algebraic lemma for the
surface inverse ideal; no freeness of that inverse ideal is assumed here.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricCubicIdealBasis

open Module

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

def curveIdeal (f : R) (x : A) : Ideal A :=
  Ideal.span {algebraMap R A f, x}

def coefficientMap (f : R) (x : A) : (Fin 3 → R) →ₗ[R] A where
  toFun c := algebraMap R A (c 0 * f) +
    algebraMap R A (c 1) * x + algebraMap R A (c 2) * x ^ 2
  map_add' c d := by
    simp only [Pi.add_apply, add_mul, map_add]
    ring
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def, RingHom.id_apply]
    ring

theorem coefficientMap_mem (f : R) (x : A) (c : Fin 3 → R) :
    coefficientMap f x c ∈ curveIdeal f x := by
  have hf : algebraMap R A f ∈ curveIdeal f x :=
    Ideal.subset_span (by simp)
  have hx : x ∈ curveIdeal f x := Ideal.subset_span (by simp)
  apply (curveIdeal f x).add_mem
  · apply (curveIdeal f x).add_mem
    · simpa only [map_mul] using (curveIdeal f x).mul_mem_left (algebraMap R A (c 0)) hf
    · exact (curveIdeal f x).mul_mem_left _ hx
  · exact (curveIdeal f x).mul_mem_left _
      (by simpa only [pow_two] using (curveIdeal f x).mul_mem_left x hx)

def idealMap (f : R) (x : A) :
    (Fin 3 → R) →ₗ[R] (curveIdeal f x) :=
  (coefficientMap f x).codRestrict ((curveIdeal f x).restrictScalars R)
    (coefficientMap_mem f x)

variable (b : Basis (Fin 3) R A) (x : A)
variable (h0 : b 0 = 1) (h1 : b 1 = x) (h2 : b 2 = x ^ 2)

include b x h0 h1 h2

theorem basis_expansion (z : A) :
    z = algebraMap R A (b.equivFun z 0) +
      algebraMap R A (b.equivFun z 1) * x +
      algebraMap R A (b.equivFun z 2) * x ^ 2 := by
  simpa only [Fin.sum_univ_three, h0, h1, h2, Algebra.smul_def, mul_one] using
    (b.sum_equivFun z).symm

theorem coefficientMap_eq_coordinates (f : R) (c : Fin 3 → R) :
    coefficientMap f x c = b.equivFun.symm ![c 0 * f, c 1, c 2] := by
  rw [b.equivFun_symm_apply, Fin.sum_univ_three]
  simp [h0, h1, h2, Algebra.smul_def, coefficientMap]

theorem idealMap_injective (f : R)
    (hf : ∀ z : R, f * z = 0 → z = 0) :
    Function.Injective (idealMap f x) := by
  intro c d h
  have he : coefficientMap f x c = coefficientMap f x d :=
    congrArg Subtype.val h
  rw [coefficientMap_eq_coordinates b x h0 h1 h2,
    coefficientMap_eq_coordinates b x h0 h1 h2] at he
  have he' := b.equivFun.symm.injective he
  have he0 : c 0 * f = d 0 * f := congrFun he' 0
  have hz : f * (c 0 - d 0) = 0 := by
    calc
      f * (c 0 - d 0) = c 0 * f - d 0 * f := by ring
      _ = 0 := sub_eq_zero.mpr he0
  have hc0 : c 0 = d 0 := sub_eq_zero.mp (hf _ hz)
  funext i
  fin_cases i
  · exact hc0
  · exact congrFun he' 1
  · exact congrFun he' 2

theorem idealMap_surjective (f g a e : R)
    (hx : x ^ 3 + algebraMap R A a * x + algebraMap R A e * x ^ 2 +
      algebraMap R A f * algebraMap R A g = 0) :
    Function.Surjective (idealMap f x) := by
  intro z
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp z.property
  let U := b.equivFun u
  let V := b.equivFun v
  refine ⟨![U 0 - V 2 * g, U 1 * f + V 0 - V 2 * a,
    U 2 * f + V 1 - V 2 * e], ?_⟩
  apply Subtype.ext
  change coefficientMap f x _ = z.val
  rw [← huv, basis_expansion b x h0 h1 h2 u, basis_expansion b x h0 h1 h2 v]
  simp only [coefficientMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    map_sub, map_add, map_mul]
  dsimp only [U, V]
  linear_combination -(algebraMap R A (b.equivFun v 2)) * hx

/-- The actual ideal has three free coordinates, without assuming that
the ambient algebra is a domain or that the ideal is already free. -/
def idealCoordinateEquiv (f g a e : R)
    (hf : ∀ z : R, f * z = 0 → z = 0)
    (hx : x ^ 3 + algebraMap R A a * x + algebraMap R A e * x ^ 2 +
      algebraMap R A f * algebraMap R A g = 0) :
    (Fin 3 → R) ≃ₗ[R] (curveIdeal f x) :=
  LinearEquiv.ofBijective (idealMap f x)
    ⟨idealMap_injective b x h0 h1 h2 f hf,
      idealMap_surjective b x h0 h1 h2 f g a e hx⟩

def idealBasis (f g a e : R)
    (hf : ∀ z : R, f * z = 0 → z = 0)
    (hx : x ^ 3 + algebraMap R A a * x + algebraMap R A e * x ^ 2 +
      algebraMap R A f * algebraMap R A g = 0) :
    Basis (Fin 3) R (curveIdeal f x) :=
  Basis.ofEquivFun (idealCoordinateEquiv b x h0 h1 h2 f g a e hf hx).symm

#print axioms idealCoordinateEquiv
#print axioms idealBasis

end CycleQ2GeometricCubicIdealBasis
end



/-!
The coefficient pairing of a monic cubic is perfect even at ramification.
This is the coefficient functional, not the ordinary algebra trace.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricCubicInverseIdeal

open Module CycleQ2GeometricCubicIdealBasis

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (b : Basis (Fin 3) R A) (x : A)
variable (h0 : b 0 = 1) (h1 : b 1 = x) (h2 : b 2 = x ^ 2)

def topCoefficient : A →ₗ[R] R := b.coord 2

theorem topCoefficient_eq (z : A) : topCoefficient b z = b.equivFun z 2 := rfl

include x h0 h1 h2

omit x h1 h2 in
theorem topCoefficient_one : topCoefficient b (1 : A) = 0 := by
  rw [← h0]
  simp [topCoefficient]

omit h0 h2 in
theorem topCoefficient_x : topCoefficient b x = 0 := by
  rw [← h1]
  simp [topCoefficient]

omit h0 h1 in
theorem topCoefficient_square : topCoefficient b (x ^ 2) = 1 := by
  rw [← h2]
  simp [topCoefficient]

omit x h0 h1 h2 in
theorem topCoefficient_scalar_mul (c : R) (z : A) :
    topCoefficient b (algebraMap R A c * z) = c * topCoefficient b z := by
  rw [← Algebra.smul_def]
  exact (topCoefficient b).map_smul c z

omit x h1 h2 in
theorem topCoefficient_scalar (c : R) :
    topCoefficient b (algebraMap R A c) = 0 := by
  simpa only [mul_one, topCoefficient_one b h0, mul_zero] using
    topCoefficient_scalar_mul b c (1 : A)

variable (f g a e : R)
variable (hx : x ^ 3 + algebraMap R A a * x + algebraMap R A e * x ^ 2 +
  algebraMap R A f * algebraMap R A g = 0)

include f g a e hx

theorem topCoefficient_cube : topCoefficient b (x ^ 3) = -e := by
  have h := congrArg (topCoefficient b) hx
  simp only [map_add, map_zero, topCoefficient_scalar_mul,
    topCoefficient_x b x h1, topCoefficient_square b x h2,
    topCoefficient_scalar b h0, mul_zero, mul_one, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

theorem topCoefficient_fourth : topCoefficient b (x ^ 4) = e ^ 2 - a := by
  have hx4 : x ^ 4 + algebraMap R A a * x ^ 2 + algebraMap R A e * x ^ 3 +
      algebraMap R A (f * g) * x = 0 := by
    rw [map_mul]
    linear_combination x * hx
  have h := congrArg (topCoefficient b) hx4
  simp only [map_add, map_zero, topCoefficient_scalar_mul,
    topCoefficient_x b x h1, topCoefficient_square b x h2,
    topCoefficient_cube b x h0 h1 h2 f g a e hx, mul_one, mul_zero, add_zero] at h
  linear_combination h

theorem topCoefficient_mul_x (z : A) :
    topCoefficient b (x * z) = b.equivFun z 1 - e * b.equivFun z 2 := by
  have hz : x * z =
      algebraMap R A (b.equivFun z 0) * x +
      algebraMap R A (b.equivFun z 1) * x ^ 2 +
      algebraMap R A (b.equivFun z 2) * x ^ 3 :=
    (congrArg (fun y : A => x * y) (basis_expansion b x h0 h1 h2 z)).trans (by ring)
  rw [hz]
  simp only [map_add, topCoefficient_scalar_mul,
    topCoefficient_x b x h1, topCoefficient_square b x h2,
    topCoefficient_cube b x h0 h1 h2 f g a e hx, mul_zero, mul_one, zero_add]
  ring

theorem topCoefficient_mul_square (z : A) :
    topCoefficient b (x ^ 2 * z) =
      b.equivFun z 0 - e * b.equivFun z 1 + (e ^ 2 - a) * b.equivFun z 2 := by
  have hz : x ^ 2 * z =
      algebraMap R A (b.equivFun z 0) * x ^ 2 +
      algebraMap R A (b.equivFun z 1) * x ^ 3 +
      algebraMap R A (b.equivFun z 2) * x ^ 4 :=
    (congrArg (fun y : A => x ^ 2 * y) (basis_expansion b x h0 h1 h2 z)).trans (by ring)
  rw [hz]
  simp only [map_add, topCoefficient_scalar_mul,
    topCoefficient_square b x h2,
    topCoefficient_cube b x h0 h1 h2 f g a e hx,
    topCoefficient_fourth b x h0 h1 h2 f g a e hx, mul_one]
  ring

/-- The top-coefficient pairing is faithful without separability or
unramifiedness assumptions. -/
theorem coefficient_pairing_faithful (z : A)
    (hz : topCoefficient b z = 0)
    (hxz : topCoefficient b (x * z) = 0)
    (hx2z : topCoefficient b (x ^ 2 * z) = 0) : z = 0 := by
  have h2z : b.equivFun z 2 = 0 := hz
  have h1z : b.equivFun z 1 = 0 := by
    simpa only [topCoefficient_mul_x b x h0 h1 h2 f g a e hx, h2z,
      mul_zero, sub_zero] using hxz
  have h0z : b.equivFun z 0 = 0 := by
    simpa only [topCoefficient_mul_square b x h0 h1 h2 f g a e hx, h1z, h2z,
      mul_zero, sub_zero, add_zero] using hx2z
  apply b.equivFun.injective
  rw [map_zero]
  ext i
  fin_cases i
  · exact h0z
  · exact h1z
  · exact h2z

/-- Multiplication followed by the top coefficient, as a linear pairing. -/
def coefficientPairing : A →ₗ[R] (A →ₗ[R] R) where
  toFun z :=
    { toFun := fun y => topCoefficient b (y * z)
      map_add' y w := by rw [add_mul, map_add]
      map_smul' c y := by rw [smul_mul_assoc, map_smul, RingHom.id_apply] }
  map_add' z w := by
    ext y
    change topCoefficient b (y * (z + w)) =
      topCoefficient b (y * z) + topCoefficient b (y * w)
    rw [mul_add, map_add]
  map_smul' c z := by
    ext y
    change topCoefficient b (y * (c • z)) = c • topCoefficient b (y * z)
    rw [mul_smul_comm, map_smul]

theorem coefficientPairing_injective : Function.Injective (coefficientPairing b) := by
  intro z w h
  apply sub_eq_zero.mp
  have hz (y : A) : topCoefficient b (y * (z - w)) = 0 := by
    rw [mul_sub, map_sub]
    exact sub_eq_zero.mpr (congrArg (fun φ : A →ₗ[R] R => φ y) h)
  exact coefficient_pairing_faithful b x h0 h1 h2 f g a e hx (z - w)
    (by simpa only [one_mul] using hz 1) (hz x) (hz (x ^ 2))

theorem coefficientPairing_surjective : Function.Surjective (coefficientPairing b) := by
  intro φ
  let z := b.equivFun.symm
    ![φ (x ^ 2) + e * φ x + a * φ 1, φ x + e * φ 1, φ 1]
  have hc : b.equivFun z =
      ![φ (x ^ 2) + e * φ x + a * φ 1, φ x + e * φ 1, φ 1] :=
    b.equivFun.apply_symm_apply _
  refine ⟨z, b.ext (fun i => ?_)⟩
  fin_cases i
  · change topCoefficient b (b 0 * z) = φ (b 0)
    rw [h0, one_mul]
    change b.equivFun z 2 = φ 1
    rw [hc]
    rfl
  · change topCoefficient b (b 1 * z) = φ (b 1)
    rw [h1, topCoefficient_mul_x b x h0 h1 h2 f g a e hx, hc]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  · change topCoefficient b (b 2 * z) = φ (b 2)
    rw [h2, topCoefficient_mul_square b x h0 h1 h2 f g a e hx, hc]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring

/-- The monic-cubic coefficient pairing is perfect over the base ring,
including at ramified fibers. -/
def coefficientPairingEquiv : A ≃ₗ[R] (A →ₗ[R] R) :=
  LinearEquiv.ofBijective (coefficientPairing b)
    ⟨coefficientPairing_injective b x h0 h1 h2 f g a e hx,
      coefficientPairing_surjective b x h0 h1 h2 f g a e hx⟩

section Modules

variable {M : Type*} [AddCommGroup M] [Module A M] [Module R M]
variable [IsScalarTower R A M]

def testFunctional (φ : M →ₗ[R] R) (m : M) : A →ₗ[R] R where
  toFun z := φ (z • m)
  map_add' z w := by rw [add_smul, map_add]
  map_smul' c z := by rw [smul_assoc, map_smul, RingHom.id_apply]

def dualLiftValue (φ : M →ₗ[R] R) (m : M) : A :=
  (coefficientPairingEquiv b x h0 h1 h2 f g a e hx).symm (testFunctional φ m)

theorem dualLiftValue_pair (φ : M →ₗ[R] R) (m : M) (z : A) :
    topCoefficient b (z * dualLiftValue b x h0 h1 h2 f g a e hx φ m) = φ (z • m) :=
  congrArg (fun ψ : A →ₗ[R] R => ψ z)
    ((coefficientPairingEquiv b x h0 h1 h2 f g a e hx).apply_symm_apply (testFunctional φ m))

/-- The inverse to composition with the cubic coefficient functional. -/
def dualLift (φ : M →ₗ[R] R) : M →ₗ[A] A where
  toFun m := dualLiftValue b x h0 h1 h2 f g a e hx φ m
  map_add' m n := by
    apply (coefficientPairingEquiv b x h0 h1 h2 f g a e hx).injective
    ext z
    change topCoefficient b (z * dualLiftValue b x h0 h1 h2 f g a e hx φ (m + n)) =
      topCoefficient b (z * (dualLiftValue b x h0 h1 h2 f g a e hx φ m +
        dualLiftValue b x h0 h1 h2 f g a e hx φ n))
    rw [mul_add, map_add, dualLiftValue_pair, dualLiftValue_pair, dualLiftValue_pair,
      smul_add, map_add]
  map_smul' c m := by
    apply (coefficientPairingEquiv b x h0 h1 h2 f g a e hx).injective
    ext z
    change topCoefficient b (z * dualLiftValue b x h0 h1 h2 f g a e hx φ (c • m)) =
      topCoefficient b (z * (c * dualLiftValue b x h0 h1 h2 f g a e hx φ m))
    rw [← mul_assoc, dualLiftValue_pair, dualLiftValue_pair, mul_smul]

/-- Composition with the coefficient functional on an actual A-linear map. -/
def coefficientOnHom : (M →ₗ[A] A) →ₗ[R] (M →ₗ[R] R) where
  toFun ν := (topCoefficient b).comp (ν.restrictScalars R)
  map_add' ν μ := by
    ext m
    exact (topCoefficient b).map_add (ν m) (μ m)
  map_smul' c ν := by
    ext m
    exact (topCoefficient b).map_smul c (ν m)

theorem coefficientOnHom_dualLift (φ : M →ₗ[R] R) :
    coefficientOnHom b (dualLift b x h0 h1 h2 f g a e hx φ) = φ := by
  ext m
  change topCoefficient b (dualLiftValue b x h0 h1 h2 f g a e hx φ m) = φ m
  simpa only [one_mul, one_smul] using
    dualLiftValue_pair b x h0 h1 h2 f g a e hx φ m 1

theorem coefficientOnHom_injective :
    Function.Injective (coefficientOnHom b (M := M)) := by
  intro ν μ h
  ext m
  apply (coefficientPairingEquiv b x h0 h1 h2 f g a e hx).injective
  ext z
  change topCoefficient b (z * ν m) = topCoefficient b (z * μ m)
  have hm := congrArg (fun φ : M →ₗ[R] R => φ (z • m)) h
  change topCoefficient b (ν (z • m)) = topCoefficient b (μ (z • m)) at hm
  simpa only [map_smul, smul_eq_mul] using hm

/-- Frobenius adjunction for the actual cubic algebra and any module. -/
def coefficientHomEquiv : (M →ₗ[A] A) ≃ₗ[R] (M →ₗ[R] R) :=
  LinearEquiv.ofBijective (coefficientOnHom b)
    ⟨coefficientOnHom_injective b x h0 h1 h2 f g a e hx,
      fun φ => ⟨dualLift b x h0 h1 h2 f g a e hx φ,
        coefficientOnHom_dualLift b x h0 h1 h2 f g a e hx φ⟩⟩

end Modules

/-- A genuine base-ring basis of the inverse ideal, obtained from its
proved ideal basis and the monic-cubic Frobenius pairing. -/
def inverseIdealBasis
    (hf : ∀ z : R, f * z = 0 → z = 0) :
    Basis (Fin 3) R ((curveIdeal f x) →ₗ[A] A) :=
  ((idealBasis b x h0 h1 h2 f g a e hf hx).dualBasis).map
    (coefficientHomEquiv b x h0 h1 h2 f g a e hx).symm

#print axioms coefficient_pairing_faithful
#print axioms coefficientPairingEquiv
#print axioms coefficientHomEquiv
#print axioms inverseIdealBasis

end CycleQ2GeometricCubicInverseIdeal
end



/-!
# Actual theta=1 surface and inverse-ideal coordinates

The literal surface quotient is identified with two monic cubic extensions.
The quadratic curve equation is regular in the coefficient algebra, so the
actual curve ideal has three coefficient coordinates. The cubic Frobenius
pairing then gives a nine-element polynomial-base basis of the actual
surface-linear inverse ideal. The final theorem specializes ungraded
coordinate Cech exactness; it does not assert projective sheaf vanishing.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ActualSurfaceTower

section Cubic
variable {R : Type*} [CommRing R]
open Polynomial

def cubic (a e c : R) : R[X] := X ^ 3 + (C e * X ^ 2 + C a * X + C c)

private theorem cubic_tail_degree (a e c : R) :
    (C e * X ^ 2 + C a * X + C c).degree < (3 : WithBot ℕ) := by
  apply lt_of_le_of_lt (degree_add_le _ _) (max_lt _ _)
  · apply lt_of_le_of_lt (degree_add_le _ _) (max_lt _ _)
    · apply lt_of_le_of_lt (degree_mul_le _ _)
      calc
        _ ≤ 0 + 2 := add_le_add degree_C_le (degree_X_pow_le 2)
        _ < (3 : WithBot ℕ) := by norm_num
    · apply lt_of_le_of_lt (degree_mul_le _ _)
      calc
        _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
        _ < (3 : WithBot ℕ) := by norm_num
  · exact lt_of_le_of_lt degree_C_le (by norm_num)

theorem cubic_monic (a e c : R) : (cubic a e c).Monic :=
  monic_X_pow_add (cubic_tail_degree a e c)

theorem cubic_degree [Nontrivial R] (a e c : R) :
    (cubic a e c).degree = 3 := by
  unfold cubic
  rw [degree_add_eq_left_of_degree_lt]
  · simp
  · simpa using cubic_tail_degree a e c

theorem cubic_natDegree [Nontrivial R] (a e c : R) :
    (cubic a e c).natDegree = 3 := natDegree_eq_of_degree_eq_some (cubic_degree a e c)

def cubicBasis [Nontrivial R] (a e c : R) :
    Module.Basis (Fin 3) R (AdjoinRoot (cubic a e c)) :=
  (AdjoinRoot.powerBasis' (cubic_monic a e c)).basis.reindex
    (finCongr (cubic_natDegree a e c))

theorem cubicBasis_apply [Nontrivial R] (a e c : R) (i : Fin 3) :
    cubicBasis a e c i = AdjoinRoot.root (cubic a e c) ^ (i : ℕ) := by
  rw [cubicBasis, Module.Basis.reindex_apply]
  rw [(AdjoinRoot.powerBasis' (cubic_monic a e c)).basis_eq_pow]
  rfl

theorem cubic_root_relation (a e c : R) :
    let S := AdjoinRoot (cubic a e c)
    let x := AdjoinRoot.root (cubic a e c)
    x ^ 3 + algebraMap R S e * x ^ 2 + algebraMap R S a * x +
      algebraMap R S c = 0 := by
  have h := AdjoinRoot.mk_self (f := cubic a e c)
  change AdjoinRoot.mk _ (X ^ 3 + (C e * X ^ 2 + C a * X + C c)) = 0 at h
  simpa only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    ← AdjoinRoot.algebraMap_eq, add_assoc] using h

private theorem regular_map_adjoinRoot {p : R[X]} (hp : p.Monic) {z : R}
    (hz : IsSMulRegular R z) :
    IsSMulRegular (AdjoinRoot p) (algebraMap R (AdjoinRoot p) z) := by
  intro u v huv
  apply (AdjoinRoot.powerBasisAux' hp).repr.injective
  ext k
  apply hz
  have huv' : z • u = z • v := by
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply] using huv
  have hh := congrArg (fun w => (AdjoinRoot.powerBasisAux' hp).repr w k) huv'
  simpa only [map_smul, Finsupp.smul_apply, RingHom.id_apply] using hh

end Cubic

abbrev Base := MvPolynomial (Fin 3) ℂ

def alpha : Base := MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 * MvPolynomial.X 2
def beta : Base := MvPolynomial.X 2 ^ 3 + MvPolynomial.X 1 ^ 3 +
  MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2 -
  MvPolynomial.C Complex.I * (MvPolynomial.X 0 ^ 3 + MvPolynomial.X 2 ^ 3)

abbrev hPolynomial : Polynomial Base := cubic alpha 0 beta
abbrev C0 := AdjoinRoot hPolynomial
def u : C0 := AdjoinRoot.root hPolynomial

instance : Nontrivial C0 :=
  AdjoinRoot.nontrivial hPolynomial (by rw [hPolynomial, cubic_degree]; norm_num)

def coefficientBasis : Module.Basis (Fin 3) Base C0 := cubicBasis alpha 0 beta

theorem u_relation : u ^ 3 + algebraMap Base C0 alpha * u + algebraMap Base C0 beta = 0 := by
  change AdjoinRoot.root (cubic alpha 0 beta) ^ 3 +
    algebraMap Base (AdjoinRoot (cubic alpha 0 beta)) alpha *
      AdjoinRoot.root (cubic alpha 0 beta) +
    algebraMap Base (AdjoinRoot (cubic alpha 0 beta)) beta = 0
  simpa only [map_zero, zero_mul, add_zero] using cubic_root_relation alpha 0 beta

def d (r : ℂ) : Base := MvPolynomial.C r * MvPolynomial.X 0 * MvPolynomial.X 2
def f (r : ℂ) : C0 := u ^ 2 - algebraMap Base C0 (d r)
def g (r : ℂ) : C0 := u ^ 4 + algebraMap Base C0 (d r) * u ^ 2 +
  algebraMap Base C0 (d r) ^ 2
def q : C0 := algebraMap Base C0 (MvPolynomial.X 1 ^ 2)
def norm (r : ℂ) : Base := beta ^ 2 - d r * (alpha + d r) ^ 2
def normMultiplier (r : ℂ) : C0 :=
  algebraMap Base C0 (alpha + d r) * u ^ 2 - algebraMap Base C0 beta * u +
    algebraMap Base C0 (alpha + d r) ^ 2

theorem norm_certificate (r : ℂ) : normMultiplier r * f r = algebraMap Base C0 (norm r) := by
  dsimp only [normMultiplier, f, norm]
  simp only [map_sub, map_pow, map_mul, map_add]
  linear_combination (algebraMap Base C0 alpha + algebraMap Base C0 (d r)) * u * u_relation -
    algebraMap Base C0 beta * u_relation

theorem norm_ne_zero (r : ℂ) : norm r ≠ 0 := by
  intro hz
  have hv := congrArg (MvPolynomial.eval (![0, 0, 1] : Fin 3 → ℂ)) hz
  norm_num [norm, d, alpha, beta, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Matrix.cons_val_two, Complex.ext_iff] at hv

theorem f_regular (r : ℂ) : IsSMulRegular C0 (f r) := by
  have hn : IsSMulRegular C0 (algebraMap Base C0 (norm r)) :=
    regular_map_adjoinRoot (cubic_monic alpha 0 beta)
      (by
        intro x y hxy
        exact mul_left_cancel₀ (norm_ne_zero r) (by simpa only [smul_eq_mul] using hxy))
  intro x y hxy
  change f r * x = f r * y at hxy
  apply hn
  change algebraMap Base C0 (norm r) * x = algebraMap Base C0 (norm r) * y
  rw [← norm_certificate r]
  simpa only [mul_assoc] using congrArg (fun z => normMultiplier r * z) hxy

abbrev vPolynomial (r : ℂ) : Polynomial C0 := cubic (3 * q ^ 2) (-3 * q) (f r * g r)
abbrev Tower (r : ℂ) := AdjoinRoot (vPolynomial r)
def v (r : ℂ) : Tower r := AdjoinRoot.root (vPolynomial r)
def ambientBasis (r : ℂ) : Module.Basis (Fin 3) C0 (Tower r) :=
  cubicBasis (3 * q ^ 2) (-3 * q) (f r * g r)

theorem v_relation (r : ℂ) :
    v r ^ 3 + algebraMap C0 (Tower r) (-3 * q) * v r ^ 2 +
      algebraMap C0 (Tower r) (3 * q ^ 2) * v r +
      algebraMap C0 (Tower r) (f r * g r) = 0 :=
  cubic_root_relation (3 * q ^ 2) (-3 * q) (f r * g r)

section ActualComparison
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals
variable {S : Type*} [CommRing S]

def baseInclusion : Base →+* WeightedPoly :=
  (MvPolynomial.rename ![(1 : Fin 5), 2, 3]).toRingHom

@[simp] theorem baseInclusion_C (z : ℂ) : baseInclusion (C z) = C z := by
  simp [baseInclusion]
@[simp] theorem baseInclusion_X0 : baseInclusion (X 0) = X 1 := by simp [baseInclusion]
@[simp] theorem baseInclusion_X1 : baseInclusion (X 1) = X 2 := by simp [baseInclusion]
@[simp] theorem baseInclusion_X2 : baseInclusion (X 2) = X 3 := by simp [baseInclusion]

def liftCoefficient (p : WeightedPoly →+* S) (hh : p (thetaH 1) = 0) : C0 →+* S :=
  AdjoinRoot.lift (p.comp baseInclusion) (p (X 0)) (by
    simp only [thetaH, originalH, originalB, map_add, map_sub, map_mul, map_pow,
      map_one, one_mul] at hh
    simp only [hPolynomial, cubic, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_sub,
      map_zero,
      zero_mul, zero_add, RingHom.comp_apply, alpha, beta,
      map_add, map_sub, map_mul, map_pow, baseInclusion_C, baseInclusion_X0,
      baseInclusion_X1, baseInclusion_X2]
    linear_combination hh)

@[simp] theorem liftCoefficient_base (p : WeightedPoly →+* S)
    (hh : p (thetaH 1) = 0) (z : Base) :
    liftCoefficient p hh (algebraMap Base C0 z) = p (baseInclusion z) := by
  exact AdjoinRoot.lift_of _

@[simp] theorem liftCoefficient_of (p : WeightedPoly →+* S)
    (hh : p (thetaH 1) = 0) (z : Base) :
    liftCoefficient p hh (AdjoinRoot.of hPolynomial z) = p (baseInclusion z) :=
  AdjoinRoot.lift_of _

@[simp] theorem liftCoefficient_u (p : WeightedPoly →+* S)
    (hh : p (thetaH 1) = 0) : liftCoefficient p hh u = p (X 0) :=
  AdjoinRoot.lift_root _

@[simp] theorem liftCoefficient_f (r : ℂ) (p : WeightedPoly →+* S)
    (hh : p (thetaH 1) = 0) : liftCoefficient p hh (f r) = p (originalF1 r) := by
  simp [f, d, originalF1]

@[simp] theorem liftCoefficient_g (r : ℂ) (p : WeightedPoly →+* S)
    (hh : p (thetaH 1) = 0) : liftCoefficient p hh (g r) = p (originalG1 r) := by
  simp only [g, d, map_add, map_mul, map_pow, liftCoefficient_u,
    liftCoefficient_base, baseInclusion_C, baseInclusion_X0, baseInclusion_X2,
    originalG1]
  ring

@[simp] theorem liftCoefficient_q (p : WeightedPoly →+* S)
    (hh : p (thetaH 1) = 0) : liftCoefficient p hh q = p (X 2) ^ 2 := by
  simp [q]

def liftTower (r : ℂ) (p : WeightedPoly →+* S)
    (hF : p (actualSeedEquation r 1) = 0) (hh : p (thetaH 1) = 0) : Tower r →+* S :=
  AdjoinRoot.lift (liftCoefficient p hh) (p originalF2) (by
    have hF' := hF
    rw [actualSeedEquation, map_add, map_add, map_mul, map_mul, map_mul,
      hh, zero_mul, add_zero] at hF'
    simp only [vPolynomial, cubic, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
      Polynomial.eval₂_neg, Polynomial.eval₂_ofNat,
      map_mul, map_neg, map_ofNat, map_pow, liftCoefficient_f,
      liftCoefficient_g, liftCoefficient_q]
    simp only [originalF2, originalG2, map_add, map_sub, map_mul, map_pow] at hF' ⊢
    linear_combination hF')

@[simp] theorem liftTower_coefficient (r : ℂ) (p : WeightedPoly →+* S)
    (hF : p (actualSeedEquation r 1) = 0) (hh : p (thetaH 1) = 0) (z : C0) :
    liftTower r p hF hh (algebraMap C0 (Tower r) z) = liftCoefficient p hh z :=
  AdjoinRoot.lift_of _

@[simp] theorem liftTower_of (r : ℂ) (p : WeightedPoly →+* S)
    (hF : p (actualSeedEquation r 1) = 0) (hh : p (thetaH 1) = 0) (z : C0) :
    liftTower r p hF hh (AdjoinRoot.of (vPolynomial r) z) = liftCoefficient p hh z :=
  AdjoinRoot.lift_of _

@[simp] theorem liftTower_v (r : ℂ) (p : WeightedPoly →+* S)
    (hF : p (actualSeedEquation r 1) = 0) (hh : p (thetaH 1) = 0) :
    liftTower r p hF hh (v r) = p originalF2 := AdjoinRoot.lift_root _

def towerBase (r : ℂ) : Base →+* Tower r :=
  (algebraMap C0 (Tower r)).comp (algebraMap Base C0)

def towerEval (r : ℂ) : WeightedPoly →+* Tower r :=
  eval₂Hom ((towerBase r).comp C)
    ![algebraMap C0 (Tower r) u, towerBase r (X 0), towerBase r (X 1),
      towerBase r (X 2), v r - algebraMap C0 (Tower r) q]

@[simp] theorem towerEval_C (r z : ℂ) : towerEval r (C z) = towerBase r (C z) := by
  simp [towerEval]
@[simp] theorem towerEval_X0 (r : ℂ) :
    towerEval r (X 0) = algebraMap C0 (Tower r) u := by simp [towerEval]
@[simp] theorem towerEval_X1 (r : ℂ) : towerEval r (X 1) = towerBase r (X 0) := by
  simp [towerEval]
@[simp] theorem towerEval_X2 (r : ℂ) : towerEval r (X 2) = towerBase r (X 1) := by
  simp [towerEval]
@[simp] theorem towerEval_X3 (r : ℂ) : towerEval r (X 3) = towerBase r (X 2) := by
  simp [towerEval]
@[simp] theorem towerEval_X4 (r : ℂ) :
    towerEval r (X 4) = v r - algebraMap C0 (Tower r) q := by simp [towerEval]

@[simp] theorem towerEval_base (r : ℂ) (z : Base) :
    towerEval r (baseInclusion z) = towerBase r z := by
  have he : (towerEval r).comp baseInclusion = towerBase r := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro j
      fin_cases j <;> simp
  exact RingHom.congr_fun he z

@[simp] theorem towerEval_h (r : ℂ) : towerEval r (thetaH 1) = 0 := by
  have hh := congrArg (algebraMap C0 (Tower r)) u_relation
  simp only [map_add, map_mul, map_pow, map_zero, alpha, beta] at hh
  simp only [thetaH, originalH, originalB, map_add, map_sub, map_mul, map_pow,
    towerEval_C, towerEval_X0, towerEval_X1, towerEval_X2, towerEval_X3,
    map_one, one_mul]
  dsimp only [towerBase, RingHom.comp_apply]
  simp only [map_add, map_sub, map_mul, map_pow] at hh
  linear_combination hh

@[simp] theorem towerEval_f (r : ℂ) :
    towerEval r (originalF1 r) = algebraMap C0 (Tower r) (f r) := by
  simp [originalF1, f, d, towerBase]

@[simp] theorem towerEval_g (r : ℂ) :
    towerEval r (originalG1 r) = algebraMap C0 (Tower r) (g r) := by
  simp only [originalG1, g, d, map_add, map_mul, map_pow, towerEval_C,
    towerEval_X0, towerEval_X1, towerEval_X3]
  dsimp only [towerBase, RingHom.comp_apply]
  ring

@[simp] theorem towerEval_f2 (r : ℂ) : towerEval r originalF2 = v r := by
  simp [originalF2, q, towerBase]

@[simp] theorem towerEval_F (r : ℂ) : towerEval r (actualSeedEquation r 1) = 0 := by
  rw [actualSeedEquation, map_add, map_add, map_mul, map_mul, map_mul,
    towerEval_h, zero_mul, add_zero, towerEval_f, towerEval_g, towerEval_f2]
  have hv := v_relation r
  simp only [map_mul, map_neg, map_ofNat, map_pow] at hv
  simp only [originalG2, map_add, map_sub, map_mul, map_pow, towerEval_X4, towerEval_X2]
  have hq : towerBase r (X 1) ^ 2 = algebraMap C0 (Tower r) q := by
    simp [towerBase, q]
  rw [show towerBase r (X 1) ^ 4 = (towerBase r (X 1) ^ 2) ^ 2 by ring, hq]
  linear_combination hv

def surfaceQuotient (r : ℂ) : WeightedPoly →+* SurfaceRing r 1 :=
  Ideal.Quotient.mk (surfaceIdeal r 1)

@[simp] theorem surfaceQuotient_equation (r : ℂ) (i : Fin 2) :
    surfaceQuotient r (surfaceEquations r 1 i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

@[simp] theorem surfaceQuotient_h (r : ℂ) : surfaceQuotient r (thetaH 1) = 0 :=
  surfaceQuotient_equation r 1
@[simp] theorem surfaceQuotient_F (r : ℂ) : surfaceQuotient r (actualSeedEquation r 1) = 0 :=
  surfaceQuotient_equation r 0

def surfaceToTower (r : ℂ) : SurfaceRing r 1 →+* Tower r :=
  Ideal.Quotient.lift _ (towerEval r) (by
    intro p hp
    have hm : surfaceIdeal r 1 ≤ RingHom.ker (towerEval r) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [surfaceEquations]
    exact hm hp)

def towerToSurface (r : ℂ) : Tower r →+* SurfaceRing r 1 :=
  liftTower r (surfaceQuotient r) (surfaceQuotient_F r) (surfaceQuotient_h r)

@[simp] theorem surfaceToTower_quotient (r : ℂ) (p : WeightedPoly) :
    surfaceToTower r (surfaceQuotient r p) = towerEval r p := rfl

end ActualComparison

section ActualInverse
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals
variable {S : Type*} [CommRing S]

theorem liftTower_comp_eval (r : ℂ) (p : WeightedPoly →+* S)
    (hF : p (actualSeedEquation r 1) = 0) (hh : p (thetaH 1) = 0) :
    (liftTower r p hF hh).comp (towerEval r) = p := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [towerBase]
  · intro j
    fin_cases j <;> simp [towerBase, q, originalF2]

theorem towerToSurface_leftInverse (r : ℂ) :
    Function.LeftInverse (towerToSurface r) (surfaceToTower r) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact RingHom.congr_fun
    (liftTower_comp_eval r (surfaceQuotient r) (surfaceQuotient_F r) (surfaceQuotient_h r)) p

def surfaceCoefficient (r : ℂ) : C0 →+* SurfaceRing r 1 :=
  liftCoefficient (surfaceQuotient r) (surfaceQuotient_h r)

theorem surfaceToTower_coefficient (r : ℂ) (z : C0) :
    surfaceToTower r (surfaceCoefficient r z) = algebraMap C0 (Tower r) z := by
  have he : (surfaceToTower r).comp (surfaceCoefficient r) = algebraMap C0 (Tower r) := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro x
      change surfaceToTower r (surfaceCoefficient r (algebraMap Base C0 x)) =
        algebraMap C0 (Tower r) (algebraMap Base C0 x)
      rw [surfaceCoefficient, liftCoefficient_base, surfaceToTower_quotient, towerEval_base]
      rfl
    · change surfaceToTower r (surfaceCoefficient r u) = algebraMap C0 (Tower r) u
      rw [surfaceCoefficient, liftCoefficient_u, surfaceToTower_quotient, towerEval_X0]
  exact RingHom.congr_fun he z

theorem towerToSurface_rightInverse (r : ℂ) :
    Function.RightInverse (towerToSurface r) (surfaceToTower r) := by
  have he : (surfaceToTower r).comp (towerToSurface r) = RingHom.id (Tower r) := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro z
      change surfaceToTower r (towerToSurface r (algebraMap C0 (Tower r) z)) =
        algebraMap C0 (Tower r) z
      rw [towerToSurface, liftTower_coefficient]
      exact surfaceToTower_coefficient r z
    · change surfaceToTower r (towerToSurface r (v r)) = v r
      rw [towerToSurface, liftTower_v, surfaceToTower_quotient, towerEval_f2]
  exact RingHom.congr_fun he

def surfaceRingEquiv (r : ℂ) : SurfaceRing r 1 ≃+* Tower r where
  toFun := surfaceToTower r
  invFun := towerToSurface r
  left_inv := towerToSurface_leftInverse r
  right_inv := towerToSurface_rightInverse r
  map_add' := (surfaceToTower r).map_add
  map_mul' := (surfaceToTower r).map_mul

local instance surfaceAlgebra (r : ℂ) : Algebra C0 (SurfaceRing r 1) :=
  (surfaceCoefficient r).toAlgebra

def surfaceAlgEquiv (r : ℂ) : SurfaceRing r 1 ≃ₐ[C0] Tower r where
  __ := surfaceRingEquiv r
  commutes' := surfaceToTower_coefficient r

def surfaceCubicBasis (r : ℂ) : Module.Basis (Fin 3) C0 (SurfaceRing r 1) :=
  (ambientBasis r).map (surfaceAlgEquiv r).symm.toLinearEquiv

theorem surfaceCubicBasis_apply (r : ℂ) (i : Fin 3) :
    surfaceCubicBasis r i = surfaceQuotient r originalF2 ^ (i : ℕ) := by
  rw [surfaceCubicBasis, Module.Basis.map_apply]
  change (surfaceAlgEquiv r).symm (cubicBasis _ _ _ i) = _
  rw [cubicBasis_apply, map_pow]
  congr 1
  exact liftTower_v r (surfaceQuotient r) (surfaceQuotient_F r) (surfaceQuotient_h r)

end ActualInverse

section ActualIdeal
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals

local instance surfaceAlgebra' (r : ℂ) : Algebra C0 (SurfaceRing r 1) := surfaceAlgebra r

theorem coefficientBasis_apply (i : Fin 3) : coefficientBasis i = u ^ (i : ℕ) :=
  cubicBasis_apply alpha 0 beta i

theorem surfaceCoefficient_f (r : ℂ) :
    algebraMap C0 (SurfaceRing r 1) (f r) = surfaceQuotient r (originalF1 r) :=
  liftCoefficient_f r (surfaceQuotient r) (surfaceQuotient_h r)

theorem surfaceCoefficient_g (r : ℂ) :
    algebraMap C0 (SurfaceRing r 1) (g r) = surfaceQuotient r (originalG1 r) :=
  liftCoefficient_g r (surfaceQuotient r) (surfaceQuotient_h r)

theorem actual_curveIdeal_eq (r : ℂ) :
    curveIdealOnSurface r 1 =
      Ideal.span {algebraMap C0 (SurfaceRing r 1) (f r), surfaceQuotient r originalF2} := by
  rw [surfaceCoefficient_f]
  change (ambientCurveIdeal r 1).map (surfaceQuotient r) = _
  rw [ambientCurveIdeal, Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact Ideal.subset_span (by simp [curveEquations])
    · exact Ideal.subset_span (by simp [curveEquations])
    · change surfaceQuotient r (thetaH 1) ∈
        Ideal.span {surfaceQuotient r (originalF1 r), surfaceQuotient r originalF2}
      rw [surfaceQuotient_h]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · subst x
      exact Ideal.subset_span ⟨0, rfl⟩
    · have h' : x = surfaceQuotient r originalF2 := Set.mem_singleton_iff.mp h
      subst x
      exact Ideal.subset_span ⟨1, rfl⟩

theorem actual_cubic_relation (r : ℂ) :
    let x := surfaceQuotient r originalF2
    x ^ 3 + algebraMap C0 (SurfaceRing r 1) (3 * q ^ 2) * x +
      algebraMap C0 (SurfaceRing r 1) (-3 * q) * x ^ 2 +
      algebraMap C0 (SurfaceRing r 1) (f r) * algebraMap C0 (SurfaceRing r 1) (g r) = 0 := by
  have hh := congrArg (towerToSurface r) (v_relation r)
  simp only [map_add, map_mul, map_pow, map_zero] at hh
  change _ = 0
  simp only [towerToSurface, liftTower_coefficient, liftTower_v] at hh
  change surfaceQuotient r originalF2 ^ 3 +
    surfaceCoefficient r (3 * q ^ 2) * surfaceQuotient r originalF2 +
    surfaceCoefficient r (-3 * q) * surfaceQuotient r originalF2 ^ 2 +
    surfaceCoefficient r (f r) * surfaceCoefficient r (g r) = 0
  simp only [surfaceCoefficient, map_mul, map_neg, map_ofNat, map_pow] at hh ⊢
  linear_combination hh

end ActualIdeal

section ActualIdealBasis
open CycleQ2SeedTrace CycleQ2GeometricSeedNormalIdeals

local instance surfaceAlgebra'' (r : ℂ) : Algebra C0 (SurfaceRing r 1) := surfaceAlgebra r

/-- A basis of the actual curve ideal on the literal theta=1 surface. -/
def actualCurveIdealBasis (r : ℂ) :
    Module.Basis (Fin 3) C0 (curveIdealOnSurface r 1) := by
  rw [actual_curveIdeal_eq]
  exact CycleQ2GeometricCubicIdealBasis.idealBasis
    (surfaceCubicBasis r) (surfaceQuotient r originalF2)
    (by simp [surfaceCubicBasis_apply]) (by simp [surfaceCubicBasis_apply])
    (by simp [surfaceCubicBasis_apply])
    (f r) (g r) (3 * q ^ 2) (-3 * q)
    (by
      intro z hz
      apply f_regular r
      change f r * z = f r * 0
      simpa only [mul_zero] using hz)
    (actual_cubic_relation r)

/-- The inherited quotient scalar action is the literal polynomial-base
coordinate action. This fixes the scalar diamond after importing the
existing surface-coordinate presentation. -/
theorem surfaceBase_smul (r : ℂ) (b : Base) (z : SurfaceRing r 1) :
    b • z = surfaceQuotient r (baseInclusion b) * z :=
  Algebra.smul_def b z

local instance surfaceBaseAlgebra (r : ℂ) : Algebra Base (SurfaceRing r 1) :=
  ((surfaceCoefficient r).comp (algebraMap Base C0)).toAlgebra

local instance surfaceScalarTower (r : ℂ) : IsScalarTower Base C0 (SurfaceRing r 1) where
  smul_assoc b c z := by
    rw [Algebra.smul_def b c]
    change surfaceCoefficient r (algebraMap Base C0 b * c) * z =
      b • (surfaceCoefficient r c * z)
    rw [surfaceBase_smul, map_mul]
    have hb : surfaceCoefficient r (algebraMap Base C0 b) =
        surfaceQuotient r (baseInclusion b) :=
      liftCoefficient_base (surfaceQuotient r) (surfaceQuotient_h r) b
    rw [hb, mul_assoc]

theorem surfaceBaseAlgebraMap (r : ℂ) (p : Base) :
    algebraMap Base (SurfaceRing r 1) p = surfaceQuotient r (baseInclusion p) :=
  liftCoefficient_base (surfaceQuotient r) (surfaceQuotient_h r) p

/-- The actual curve ideal has nine coordinates over the literal polynomial
base generated by x1,x2,x3. This is a module basis, not an assertion that
the ideal is free over the surface coordinate ring. -/
def actualCurveIdealBaseBasis (r : ℂ) :
    Module.Basis (Fin 3 × Fin 3) Base (curveIdealOnSurface r 1) :=
  coefficientBasis.smulTower (actualCurveIdealBasis r)

end ActualIdealBasis

#print axioms f_regular
#print axioms surfaceAlgEquiv
#print axioms surfaceCubicBasis
#print axioms actual_curveIdeal_eq
#print axioms actualCurveIdealBasis
#print axioms actualCurveIdealBaseBasis

section ActualInverseIdeal
open CycleQ2SeedTrace CycleQ2GeometricSeedNormalIdeals

local instance inverseSurfaceAlgebra (r : ℂ) : Algebra C0 (SurfaceRing r 1) :=
  surfaceAlgebra r
local instance inverseSurfaceBaseAlgebra (r : ℂ) : Algebra Base (SurfaceRing r 1) :=
  surfaceBaseAlgebra r
local instance inverseSurfaceScalarTower (r : ℂ) : IsScalarTower Base C0 (SurfaceRing r 1) :=
  surfaceScalarTower r

abbrev ActualInverseIdeal (r : ℂ) :=
  (curveIdealOnSurface r 1) →ₗ[SurfaceRing r 1] SurfaceRing r 1

/-- The cubic top-coefficient pairing identifies the actual surface-linear
inverse ideal with the C0-linear dual of the actual curve ideal. -/
def actualInverseIdealDualEquiv (r : ℂ) :
    ActualInverseIdeal r ≃ₗ[C0] ((curveIdealOnSurface r 1) →ₗ[C0] C0) :=
  CycleQ2GeometricCubicInverseIdeal.coefficientHomEquiv
    (surfaceCubicBasis r) (surfaceQuotient r originalF2)
    (by simp [surfaceCubicBasis_apply]) (by simp [surfaceCubicBasis_apply])
    (by simp [surfaceCubicBasis_apply])
    (f r) (g r) (3 * q ^ 2) (-3 * q) (actual_cubic_relation r)

/-- A free basis over C0 for the actual inverse ideal Hom_A(I,A). -/
def actualInverseIdealBasis (r : ℂ) :
    Module.Basis (Fin 3) C0 (ActualInverseIdeal r) :=
  ((actualCurveIdealBasis r).dualBasis).map (actualInverseIdealDualEquiv r).symm

/-- Nine coordinates over the literal polynomial base x1,x2,x3 for the
actual inverse ideal. This does not assert freeness over A or sheaf cohomology vanishing. -/
def actualInverseIdealBaseBasis (r : ℂ) :
    Module.Basis (Fin 3 × Fin 3) Base (ActualInverseIdeal r) :=
  coefficientBasis.smulTower (actualInverseIdealBasis r)

end ActualInverseIdeal

#print axioms actualInverseIdealDualEquiv
#print axioms actualInverseIdealBasis
#print axioms actualInverseIdealBaseBasis

section ActualInverseIdealCech
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricFreeCoordinateCech

local instance cechSurfaceAlgebra (r : ℂ) : Algebra C0 (SurfaceRing r 1) := surfaceAlgebra r
local instance cechSurfaceBaseAlgebra (r : ℂ) : Algebra Base (SurfaceRing r 1) :=
  surfaceBaseAlgebra r
local instance cechSurfaceScalarTower (r : ℂ) : IsScalarTower Base C0 (SurfaceRing r 1) :=
  surfaceScalarTower r

/-- The ungraded three-coordinate Cech complex of the actual inverse ideal
is exact in degree one, with actual localized-module primitives supplied. -/
theorem actualInverseIdeal_firstCech_exact (r : ℂ)
    (p01 : LocalModule ℂ (ActualInverseIdeal r) {0, 1})
    (p02 : LocalModule ℂ (ActualInverseIdeal r) {0, 2})
    (p12 : LocalModule ℂ (ActualInverseIdeal r) {1, 2})
    (hc : restriction ℂ (ActualInverseIdeal r)
        (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by simp) p01 -
      restriction ℂ (ActualInverseIdeal r)
        (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p02 +
      restriction ℂ (ActualInverseIdeal r)
        (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p12 = 0) :
    ∃ (q0 : LocalModule ℂ (ActualInverseIdeal r) {0})
      (q1 : LocalModule ℂ (ActualInverseIdeal r) {1})
      (q2 : LocalModule ℂ (ActualInverseIdeal r) {2}),
      p01 = restriction ℂ (ActualInverseIdeal r)
          (show ({1} : Finset (Fin 3)) ⊆ {0, 1} by decide) q1 -
        restriction ℂ (ActualInverseIdeal r)
          (show ({0} : Finset (Fin 3)) ⊆ {0, 1} by decide) q0 ∧
      p02 = restriction ℂ (ActualInverseIdeal r)
          (show ({2} : Finset (Fin 3)) ⊆ {0, 2} by decide) q2 -
        restriction ℂ (ActualInverseIdeal r)
          (show ({0} : Finset (Fin 3)) ⊆ {0, 2} by decide) q0 ∧
      p12 = restriction ℂ (ActualInverseIdeal r)
          (show ({2} : Finset (Fin 3)) ⊆ {1, 2} by decide) q2 -
        restriction ℂ (ActualInverseIdeal r)
          (show ({1} : Finset (Fin 3)) ⊆ {1, 2} by decide) q1 :=
  firstCech_exact (actualInverseIdealBaseBasis r) p01 p02 p12 hc

end ActualInverseIdealCech

#print axioms actualInverseIdeal_firstCech_exact

end CycleQ2ActualSurfaceTower



/-!
Localization of the actual inverse-ideal Hom module, with its canonical
map and evaluation compatibility. No freeness of the ideal or inverse
ideal is assumed; finite presentation is used for the Hom comparison.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricLocalizedInverseIdeal

variable {A : Type*} [CommRing A]
variable (S : Submonoid A) (U : Type*) [CommRing U] [Algebra A U] [IsLocalization S U]
variable (I : Ideal A)

abbrev LocalInverseIdeal := I.map (algebraMap A U) →ₗ[U] U

/-- Localizing an actual inverse-ideal homomorphism. -/
def localizedInverseIdealMap : (I →ₗ[A] A) →ₗ[A] LocalInverseIdeal U I :=
  IsLocalizedModule.mapExtendScalars S (Algebra.idealMap U I) (Algebra.linearMap A U) U

/-- The canonical localization retains evaluation on every original ideal element. -/
theorem localizedInverseIdealMap_eval (ν : I →ₗ[A] A) (x : I) :
    localizedInverseIdealMap S U I ν (Algebra.idealMap U I x) = algebraMap A U (ν x) := by
  change IsLocalizedModule.map S (Algebra.idealMap U I) (Algebra.linearMap A U)
    ν (Algebra.idealMap U I x) = _
  exact IsLocalizedModule.map_apply S (Algebra.idealMap U I) (Algebra.linearMap A U) ν x

include S

/-- Local homomorphisms are determined by the original ideal elements. -/
theorem localInverseIdeal_ext (ν μ : LocalInverseIdeal U I)
    (h : ∀ x : I, ν (Algebra.idealMap U I x) = μ (Algebra.idealMap U I x)) : ν = μ := by
  apply LinearMap.restrictScalars_injective A
  apply IsLocalizedModule.ext S (Algebra.idealMap U I)
    (IsLocalizedModule.map_units (Algebra.linearMap A U))
  ext x
  exact h x

variable [Module.FinitePresentation A I]

instance localizedInverseIdealMap_isLocalization :
    IsLocalizedModule S (localizedInverseIdealMap S U I) :=
  Module.FinitePresentation.isLocalizedModule_mapExtendScalars S
    (Algebra.idealMap U I) (Algebra.linearMap A U) U

/-- The actual local inverse ideal is the localization of the global one. -/
def localizedInverseIdealEquiv :
    LocalizedModule S (I →ₗ[A] A) ≃ₗ[A] LocalInverseIdeal U I :=
  IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (I →ₗ[A] A))
    (localizedInverseIdealMap S U I)

@[simp] theorem localizedInverseIdealEquiv_original (ν : I →ₗ[A] A) :
    localizedInverseIdealEquiv S U I (LocalizedModule.mkLinearMap S (I →ₗ[A] A) ν) =
      localizedInverseIdealMap S U I ν :=
  IsLocalizedModule.linearEquiv_apply S _ _ ν

theorem localizedInverseIdealEquiv_eval (ν : I →ₗ[A] A) (x : I) :
    localizedInverseIdealEquiv S U I (LocalizedModule.mkLinearMap S (I →ₗ[A] A) ν)
      (Algebra.idealMap U I x) = algebraMap A U (ν x) := by
  rw [localizedInverseIdealEquiv_original, localizedInverseIdealMap_eval]

variable (T : Submonoid A) (V : Type*) [CommRing V] [Algebra A V] [IsLocalization T V]

/-- Canonical restriction when more elements are inverted. -/
def inverseIdealRestriction (hST : S ≤ T) :
    LocalInverseIdeal U I →ₗ[A] LocalInverseIdeal V I :=
  IsLocalizedModule.lift S (localizedInverseIdealMap S U I) (localizedInverseIdealMap T V I)
    (fun s => IsLocalizedModule.map_units (localizedInverseIdealMap T V I) ⟨s, hST s.property⟩)

@[simp] theorem inverseIdealRestriction_original (hST : S ≤ T) (ν : I →ₗ[A] A) :
    inverseIdealRestriction S U I T V hST (localizedInverseIdealMap S U I ν) =
      localizedInverseIdealMap T V I ν := by
  apply IsLocalizedModule.lift_apply

variable (W : Submonoid A) (Z : Type*) [CommRing Z] [Algebra A Z] [IsLocalization W Z]

theorem inverseIdealRestriction_comp (hST : S ≤ T) (hTW : T ≤ W) :
    (inverseIdealRestriction T V I W Z hTW).comp (inverseIdealRestriction S U I T V hST) =
      inverseIdealRestriction S U I W Z (hST.trans hTW) := by
  apply IsLocalizedModule.ext S (localizedInverseIdealMap S U I)
    (fun s => IsLocalizedModule.map_units (localizedInverseIdealMap W Z I)
      ⟨s, hTW (hST s.property)⟩)
  ext ν
  simp only [LinearMap.comp_apply, inverseIdealRestriction_original]

#print axioms localizedInverseIdealEquiv
#print axioms localizedInverseIdealMap_eval
#print axioms inverseIdealRestriction_comp

end CycleQ2GeometricLocalizedInverseIdeal
end

noncomputable section
namespace CycleQ2ActualInverseIdealLocalization

open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricLocalizedInverseIdeal

instance actualCurveIdeal_finitePresentation (r θ : ℂ) :
    Module.FinitePresentation (SurfaceRing r θ) (curveIdealOnSurface r θ) :=
  Module.finitePresentation_of_finite (SurfaceRing r θ) (curveIdealOnSurface r θ)

/-- The genuine inverse ideal on every actual surface localization. -/
def actualLocalizedInverseIdealEquiv (r θ : ℂ) (s : SurfaceRing r θ) :
    LocalizedModule (Submonoid.powers s)
      ((curveIdealOnSurface r θ) →ₗ[SurfaceRing r θ] SurfaceRing r θ) ≃ₗ[SurfaceRing r θ]
        ((curveIdealOnSurface r θ).map (algebraMap (SurfaceRing r θ) (Localization.Away s))
          →ₗ[Localization.Away s] Localization.Away s) :=
  localizedInverseIdealEquiv (Submonoid.powers s) (Localization.Away s) (curveIdealOnSurface r θ)

theorem actualLocalizedInverseIdealEquiv_eval (r θ : ℂ) (s : SurfaceRing r θ)
    (ν : (curveIdealOnSurface r θ) →ₗ[SurfaceRing r θ] SurfaceRing r θ)
    (x : curveIdealOnSurface r θ) :
    actualLocalizedInverseIdealEquiv r θ s
      (LocalizedModule.mkLinearMap (Submonoid.powers s) _ ν)
      (Algebra.idealMap (Localization.Away s) (curveIdealOnSurface r θ) x) =
        algebraMap (SurfaceRing r θ) (Localization.Away s) (ν x) :=
  localizedInverseIdealEquiv_eval (Submonoid.powers s) (Localization.Away s)
    (curveIdealOnSurface r θ) ν x

#print axioms actualCurveIdeal_finitePresentation
#print axioms actualLocalizedInverseIdealEquiv
#print axioms actualLocalizedInverseIdealEquiv_eval

end CycleQ2ActualInverseIdealLocalization
end
