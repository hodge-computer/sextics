import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Cofactor residue trivializations of an actual conormal cokernel

For two rows a,b in R^3, this file uses the actual module R^3/(Ra+Rb).
The signed Jacobian-minor functional descends to this quotient. If one
minor is a unit, explicit Cramer identities prove that the descended map
is a linear equivalence, with inverse c |-> c dx_k/minor_k.

This strengthens agreement of normalized residue representatives: it
proves their generation and uniqueness without assuming that the module
already has rank one. All statements allow arbitrary commutative rings,
including rings with zero divisors. No passage to a function field is used.

In the cycle-q2 application a,b are the two equation-gradient rows on a
Jacobian localization. Identifying this conormal cokernel with the actual
Kaehler module, and assembling the local equivalences into the global
canonical-sheaf comparison, are distinct application steps. Neither that
global comparison nor the final protected certificate is asserted here.

Validation: compiled with the repository's pinned Lean 4.33.1 and independently
kernel-replayed. This check establishes the local cokernel statements in this
file; the Kähler and global canonical-sheaf comparisons remain separate.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

universe u

namespace CycleQ2GeometricCofactorResidue

variable {R : Type u} [CommRing R]

abbrev Coordinates (R : Type u) := Fin 3 → R

/-- Signed maximal minors, in the orientation (0,1,2). -/
def cofactor (a b : Coordinates R) : Coordinates R := ![
  a 1 * b 2 - a 2 * b 1,
  a 2 * b 0 - a 0 * b 2,
  a 0 * b 1 - a 1 * b 0]

/-- The actual coordinate vector, rather than an assumed differential basis. -/
def coordinateVector (k : Fin 3) : Coordinates R :=
  fun i => if i = k then 1 else 0

/-- The Jacobian-minor functional on the free differential module. -/
def coefficient (a b : Coordinates R) : Coordinates R →ₗ[R] R where
  toFun v := cofactor a b 0 * v 0 + cofactor a b 1 * v 1 +
    cofactor a b 2 * v 2
  map_add' v w := by
    simp only [Pi.add_apply]
    ring
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem coefficient_apply (a b v : Coordinates R) :
    coefficient a b v = cofactor a b 0 * v 0 + cofactor a b 1 * v 1 +
      cofactor a b 2 * v 2 := rfl

@[simp] theorem coefficient_first_relation (a b : Coordinates R) :
    coefficient a b a = 0 := by
  simp [coefficient, cofactor]
  ring

@[simp] theorem coefficient_second_relation (a b : Coordinates R) :
    coefficient a b b = 0 := by
  simp [coefficient, cofactor]
  ring

@[simp] theorem coefficient_coordinateVector (a b : Coordinates R) (k : Fin 3) :
    coefficient a b (coordinateVector k) = cofactor a b k := by
  fin_cases k <;> simp [coefficient, coordinateVector]

/-- The two coefficients of the explicit relation for each pivot. -/
def cramerA (b v : Coordinates R) : Coordinates R := ![
  b 2 * v 1 - b 1 * v 2,
  b 0 * v 2 - b 2 * v 0,
  b 1 * v 0 - b 0 * v 1]

def cramerB (a v : Coordinates R) : Coordinates R := ![
  a 1 * v 2 - a 2 * v 1,
  a 2 * v 0 - a 0 * v 2,
  a 0 * v 1 - a 1 * v 0]

/-- Polynomial Cramer identity. No inverse, regularity, or rank hypothesis. -/
theorem cramer_identity (a b v : Coordinates R) (k : Fin 3) :
    cofactor a b k • v - coefficient a b v • coordinateVector k =
      cramerA b v k • a + cramerB a v k • b := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [cofactor, coefficient, coordinateVector, cramerA, cramerB,
      Pi.smul_apply, smul_eq_mul] <;> ring

/-- Precisely the two equation relations, with all their module multiples. -/
def relations (a b : Coordinates R) : Submodule R (Coordinates R) :=
  Submodule.span R ({a, b} : Set (Coordinates R))

abbrev ResidueModule (a b : Coordinates R) := Coordinates R ⧸ relations a b

def toResidue (a b : Coordinates R) : Coordinates R →ₗ[R] ResidueModule a b :=
  (relations a b).mkQ

theorem first_relation_mem (a b : Coordinates R) : a ∈ relations a b :=
  Submodule.subset_span (by simp)

theorem second_relation_mem (a b : Coordinates R) : b ∈ relations a b :=
  Submodule.subset_span (by simp)

theorem relations_le_kernel (a b : Coordinates R) :
    relations a b ≤ LinearMap.ker (coefficient a b) := by
  apply Submodule.span_le.mpr
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with hv | hv <;> subst v
  · change coefficient a b a = 0
    exact coefficient_first_relation a b
  · change coefficient a b b = 0
    exact coefficient_second_relation a b

/-- A constructed functional on the actual cokernel. -/
def residueFunctional (a b : Coordinates R) : ResidueModule a b →ₗ[R] R :=
  (relations a b).liftQ (coefficient a b) (relations_le_kernel a b)

@[simp] theorem residueFunctional_toResidue (a b v : Coordinates R) :
    residueFunctional a b (toResidue a b v) = coefficient a b v := rfl

/-- The decisive quotient identity before inverting a minor. -/
theorem scaled_reconstruction (a b v : Coordinates R) (k : Fin 3) :
    cofactor a b k • toResidue a b v =
      coefficient a b v • toResidue a b (coordinateVector k) := by
  have hmem : cofactor a b k • v - coefficient a b v • coordinateVector k ∈
      relations a b := by
    rw [cramer_identity]
    exact (relations a b).add_mem
      ((relations a b).smul_mem _ (first_relation_mem a b))
      ((relations a b).smul_mem _ (second_relation_mem a b))
  have hz : toResidue a b
      (cofactor a b k • v - coefficient a b v • coordinateVector k) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hmem
  simpa only [map_sub, map_smul, sub_eq_zero] using hz

/-- The normalized residue generator for a specified unit minor. -/
def normalizedResidue (a b : Coordinates R) (k : Fin 3) (v : Rˣ) :
    ResidueModule a b :=
  (↑(v⁻¹) : R) • toResidue a b (coordinateVector k)

@[simp] theorem residueFunctional_normalized (a b : Coordinates R)
    (k : Fin 3) (v : Rˣ) (hv : cofactor a b k = (v : R)) :
    residueFunctional a b (normalizedResidue a b k v) = 1 := by
  rw [normalizedResidue, map_smul, residueFunctional_toResidue,
    coefficient_coordinateVector, hv]
  change (↑(v⁻¹) : R) * (v : R) = 1
  exact v.inv_mul

/-- Every element has the explicit coefficient times the normalized residue.
This proves generation without assuming freeness or a dimension statement. -/
theorem reconstruction (a b : Coordinates R) (k : Fin 3) (v : Rˣ)
    (hv : cofactor a b k = (v : R)) (η : ResidueModule a b) :
    η = residueFunctional a b η • normalizedResidue a b k v := by
  refine Quotient.inductionOn' η (fun x => ?_)
  change toResidue a b x =
    residueFunctional a b (toResidue a b x) • normalizedResidue a b k v
  rw [residueFunctional_toResidue]
  calc
    toResidue a b x =
        (↑(v⁻¹) : R) • ((v : R) • toResidue a b x) := by
          rw [smul_smul, v.inv_mul, one_smul]
    _ = (↑(v⁻¹) : R) •
        (coefficient a b x • toResidue a b (coordinateVector k)) := by
          rw [← hv, scaled_reconstruction]
    _ = coefficient a b x • normalizedResidue a b k v := by
          simp only [normalizedResidue, smul_smul]
          rw [mul_comm (↑(v⁻¹) : R) (coefficient a b x)]

theorem residueFunctional_injective (a b : Coordinates R) (k : Fin 3)
    (v : Rˣ) (hv : cofactor a b k = (v : R)) :
    Function.Injective (residueFunctional a b) := by
  intro η ζ h
  calc
    η = residueFunctional a b η • normalizedResidue a b k v :=
      reconstruction a b k v hv η
    _ = residueFunctional a b ζ • normalizedResidue a b k v := by rw [h]
    _ = ζ := (reconstruction a b k v hv ζ).symm

theorem residueFunctional_surjective (a b : Coordinates R) (k : Fin 3)
    (v : Rˣ) (hv : cofactor a b k = (v : R)) :
    Function.Surjective (residueFunctional a b) := by
  intro c
  refine ⟨c • normalizedResidue a b k v, ?_⟩
  rw [map_smul, residueFunctional_normalized a b k v hv, smul_eq_mul, mul_one]

/-- The local residue map is an actual linear equivalence. Its existence
is proved by the explicit preceding formulas, not assumed as geometric data. -/
def residueLinearEquiv (a b : Coordinates R) (k : Fin 3) (v : Rˣ)
    (hv : cofactor a b k = (v : R)) : ResidueModule a b ≃ₗ[R] R :=
  LinearEquiv.ofBijective (residueFunctional a b)
    ⟨residueFunctional_injective a b k v hv,
      residueFunctional_surjective a b k v hv⟩

/-- All unit-minor normalizations give the same section of this cokernel. -/
theorem normalizedResidues_agree (a b : Coordinates R)
    (k l : Fin 3) (v w : Rˣ)
    (hv : cofactor a b k = (v : R)) (hw : cofactor a b l = (w : R)) :
    normalizedResidue a b k v = normalizedResidue a b l w := by
  apply residueFunctional_injective a b k v hv
  rw [residueFunctional_normalized a b k v hv,
    residueFunctional_normalized a b l w hw]

/-- Changing the two equation generators scales the cofactor by the
actual 2-by-2 determinant, including every off-diagonal term. -/
theorem cofactor_row_change (a b : Coordinates R) (α β γ δ : R) :
    cofactor (α • a + β • b) (γ • a + δ • b) =
      (α * δ - β * γ) • cofactor a b := by
  funext k
  fin_cases k <;> simp [cofactor, Pi.smul_apply, smul_eq_mul] <;> ring

theorem coefficient_row_change (a b x : Coordinates R) (α β γ δ : R) :
    coefficient (α • a + β • b) (γ • a + δ • b) x =
      (α * δ - β * γ) * coefficient a b x := by
  simp only [coefficient_apply, cofactor_row_change, Pi.smul_apply, smul_eq_mul]
  ring

theorem row_inverse_first (a b : Coordinates R) (α β γ δ : R) :
    δ • (α • a + β • b) - β • (γ • a + δ • b) =
      (α * δ - β * γ) • a := by
  funext k
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring

theorem row_inverse_second (a b : Coordinates R) (α β γ δ : R) :
    α • (γ • a + δ • b) - γ • (α • a + β • b) =
      (α * δ - β * γ) • b := by
  funext k
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- An invertible equation change preserves the actual relation submodule. -/
theorem relations_row_change (a b : Coordinates R) (α β γ δ : R)
    (v : Rˣ) (hv : α * δ - β * γ = (v : R)) :
    relations (α • a + β • b) (γ • a + δ • b) = relations a b := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx <;> subst x
    · exact (relations a b).add_mem
        ((relations a b).smul_mem _ (first_relation_mem a b))
        ((relations a b).smul_mem _ (second_relation_mem a b))
    · exact (relations a b).add_mem
        ((relations a b).smul_mem _ (first_relation_mem a b))
        ((relations a b).smul_mem _ (second_relation_mem a b))
  · apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx <;> subst x
    · have h : (α * δ - β * γ) • a ∈
          relations (α • a + β • b) (γ • a + δ • b) := by
        rw [← row_inverse_first a b α β γ δ]
        exact (relations (α • a + β • b) (γ • a + δ • b)).sub_mem
          ((relations (α • a + β • b) (γ • a + δ • b)).smul_mem δ
            (first_relation_mem (α • a + β • b) (γ • a + δ • b)))
          ((relations (α • a + β • b) (γ • a + δ • b)).smul_mem β
            (second_relation_mem (α • a + β • b) (γ • a + δ • b)))
      have h' := (relations (α • a + β • b) (γ • a + δ • b)).smul_mem
        (↑(v⁻¹) : R) h
      simpa only [hv, smul_smul, v.inv_mul, one_smul, SetLike.mem_coe] using h'
    · have h : (α * δ - β * γ) • b ∈
          relations (α • a + β • b) (γ • a + δ • b) := by
        rw [← row_inverse_second a b α β γ δ]
        exact (relations (α • a + β • b) (γ • a + δ • b)).sub_mem
          ((relations (α • a + β • b) (γ • a + δ • b)).smul_mem α
            (second_relation_mem (α • a + β • b) (γ • a + δ • b)))
          ((relations (α • a + β • b) (γ • a + δ • b)).smul_mem γ
            (first_relation_mem (α • a + β • b) (γ • a + δ • b)))
      have h' := (relations (α • a + β • b) (γ • a + δ • b)).smul_mem
        (↑(v⁻¹) : R) h
      simpa only [hv, smul_smul, v.inv_mul, one_smul, SetLike.mem_coe] using h'


/-- The cofactor construction commutes with every ring restriction map. -/
theorem cofactor_map {S : Type*} [CommRing S] (φ : R →+* S)
    (a b : Coordinates R) :
    cofactor (fun i => φ (a i)) (fun i => φ (b i)) =
      fun i => φ (cofactor a b i) := by
  funext k
  fin_cases k <;> simp [cofactor, map_sub, map_mul]

/-- The coefficient formula retains naturality before passing to cokernels. -/
theorem coefficient_map {S : Type*} [CommRing S] (φ : R →+* S)
    (a b x : Coordinates R) :
    coefficient (fun i => φ (a i)) (fun i => φ (b i)) (fun i => φ (x i)) =
      φ (coefficient a b x) := by
  simp only [coefficient_apply, cofactor_map, map_add, map_mul]

/-- Once an actual chart map has its coefficient transformation proved,
the corresponding normalized residue transformation follows in the module
itself. This is a transport lemma, not an assumed geometric chart map. -/
theorem normalizedResidue_transport (a b a' b' : Coordinates R)
    (k l : Fin 3) (v w : Rˣ)
    (hv : cofactor a b k = (v : R)) (hw : cofactor a' b' l = (w : R))
    (φ : ResidueModule a b →ₗ[R] ResidueModule a' b') (c : R)
    (hφ : ∀ ξ, residueFunctional a' b' (φ ξ) = c * residueFunctional a b ξ) :
    φ (normalizedResidue a b k v) = c • normalizedResidue a' b' l w := by
  calc
    φ (normalizedResidue a b k v) =
        residueFunctional a' b' (φ (normalizedResidue a b k v)) •
          normalizedResidue a' b' l w :=
      reconstruction a' b' l w hw _
    _ = c • normalizedResidue a' b' l w := by
      rw [hφ, residueFunctional_normalized a b k v hv, mul_one]

end CycleQ2GeometricCofactorResidue

end
