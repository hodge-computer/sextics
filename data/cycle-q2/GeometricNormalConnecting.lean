import Proposal.GeometricSeedConormalBases
import Mathlib.Tactic.Abel

/-!
# The actual normal connecting cochain, inside the surface-relative normal module

The first sections extract the existing actual equation lifts, tensor-Hom
restriction maps, normal-kernel trivializations, and two-open connecting
cochain.  Their definitions and names are unchanged.  The last section
transports this specific cochain through the canonical comparison with
the normal module of the actual curve ideal on the actual surface quotient.
Its equation values and scalar coefficient are proved, rather than assumed.

These are normal-module and affine-cone Cech statements.  Projective degree
extraction, the effective-Cartier boundary to surface cohomology, and its
compatibility with the global geometric trace are separate constructions.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open scoped BigOperators TensorProduct

section
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace CycleQ2NormalConnecting

section EquationMap

variable {R : Type*} [CommRing R]

def equationMap (g₁ g₂ k : R) : (Fin 3 → R) →ₗ[R] (Fin 2 → R) where
  toFun u := ![g₁*u 0+g₂*u 1+k*u 2, u 2]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c u := by ext i; fin_cases i <;> simp [smul_eq_mul] <;> ring

def kernelVector (g₁ g₂ : R) : Fin 3 → R := ![g₂,-g₁,0]

theorem equationMap_kernelVector (g₁ g₂ k : R) :
    equationMap g₁ g₂ k (kernelVector g₁ g₂) = 0 := by
  ext i
  fin_cases i <;> simp [equationMap, kernelVector] <;> ring

def firstLift (g₁ : Rˣ) (k A L : R) : Fin 3 → R :=
  ![(k*L-A)*(↑(g₁⁻¹) : R),0,-L]

def secondLift (g₂ : Rˣ) (k A L : R) : Fin 3 → R :=
  ![0,(k*L-A)*(↑(g₂⁻¹) : R),-L]

theorem equationMap_firstLift (g₁ : Rˣ) (g₂ k A L : R) :
    equationMap (g₁ : R) g₂ k (firstLift g₁ k A L) = ![-A,-L] := by
  ext i
  fin_cases i
  · change (g₁ : R)*((k*L-A)*(↑(g₁⁻¹) : R))+g₂*0+k*(-L)= -A
    linear_combination (k*L-A)*g₁.mul_inv
  · rfl

theorem equationMap_secondLift (g₂ : Rˣ) (g₁ k A L : R) :
    equationMap g₁ (g₂ : R) k (secondLift g₂ k A L) = ![-A,-L] := by
  ext i
  fin_cases i
  · change g₁*0+(g₂ : R)*((k*L-A)*(↑(g₂⁻¹) : R))+k*(-L)= -A
    linear_combination (k*L-A)*g₂.mul_inv
  · rfl

/-- Exactness on a first-denominator chart, without a field hypothesis. -/
theorem equationMap_kernel_first (g₁ : Rˣ) (g₂ k : R) (u : Fin 3 → R) :
    equationMap (g₁ : R) g₂ k u = 0 ↔
      ∃ c : R, u = c • kernelVector (g₁ : R) g₂ := by
  constructor
  · intro hu
    have h₀ := congrFun hu 0
    have h₂ := congrFun hu 1
    change g₁*u 0+g₂*u 1+k*u 2=0 at h₀
    change u 2=0 at h₂
    refine ⟨-(u 1*(↑(g₁⁻¹) : R)), ?_⟩
    ext i
    fin_cases i
    · change u 0 = -(u 1*(↑(g₁⁻¹) : R))*g₂
      rw [h₂] at h₀
      linear_combination (↑(g₁⁻¹) : R)*h₀-u 0*g₁.inv_mul
    · simp [kernelVector, smul_eq_mul, mul_assoc]
    · simpa [kernelVector] using h₂
  · rintro ⟨c,rfl⟩
    rw [map_smul, equationMap_kernelVector, smul_zero]

def overlapCoefficient (g₁ g₂ : Rˣ) (k A L : R) : R :=
  (k*L-A)*(↑(g₁⁻¹) : R)*(↑(g₂⁻¹) : R)

/-- The two actual lift formulas differ by the kernel generator with this
literal scalar.  This is the equation-normal Čech connecting expression. -/
theorem local_lift_difference (g₁ g₂ : Rˣ) (k A L : R) :
    firstLift g₁ k A L-secondLift g₂ k A L =
      overlapCoefficient g₁ g₂ k A L • kernelVector (g₁ : R) (g₂ : R) := by
  ext i
  fin_cases i
  · simp only [Pi.sub_apply, firstLift, secondLift, Pi.smul_apply, kernelVector,
      overlapCoefficient, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, sub_zero, smul_eq_mul]
    rw [mul_assoc _ _ (g₂ : R), g₂.inv_mul, mul_one]
  · simp only [Pi.sub_apply, firstLift, secondLift, Pi.smul_apply, kernelVector,
      overlapCoefficient, Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons, zero_sub, smul_eq_mul]
    calc
      _ = -((k*L-A)*(↑(g₂⁻¹) : R)*
          ((↑(g₁⁻¹) : R)*(g₁ : R))) := by rw [g₁.inv_mul]; ring
      _ = _ := by ring
  · simp [firstLift, secondLift, kernelVector]

end EquationMap

section Seed
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta
open CycleQ2SeedCech (curveA curveB)

def firstOpenUnit (r θ : ℂ) : (FirstOpen r θ)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := FirstOpen r θ) (curveG1 r θ)).unit
def secondOpenUnit (r θ : ℂ) : (SecondOpen r θ)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := SecondOpen r θ) (curveG2 r θ)).unit


def firstOverlapUnit (r θ : ℂ) : (Overlap r θ)ˣ :=
  Units.map (firstRestriction r θ).toMonoidHom (firstOpenUnit r θ)
def secondOverlapUnit (r θ : ℂ) : (Overlap r θ)ˣ :=
  Units.map (secondRestriction r θ).toMonoidHom (secondOpenUnit r θ)

@[simp] theorem coe_firstOverlapUnit (r θ : ℂ) :
    (firstOverlapUnit r θ : Overlap r θ)=algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ) := by
  change firstRestriction r θ (firstOpenUnit r θ : FirstOpen r θ)=_
  rw [show (firstOpenUnit r θ : FirstOpen r θ)=
    algebraMap (CurveRing r θ) (FirstOpen r θ) (curveG1 r θ) from IsUnit.unit_spec _]
  exact IsLocalization.Away.awayToAwayRight_eq _ _ _

@[simp] theorem coe_secondOverlapUnit (r θ : ℂ) :
    (secondOverlapUnit r θ : Overlap r θ)=algebraMap (CurveRing r θ) (Overlap r θ) (curveG2 r θ) := by
  change secondRestriction r θ (secondOpenUnit r θ : SecondOpen r θ)=_
  rw [show (secondOpenUnit r θ : SecondOpen r θ)=
    algebraMap (CurveRing r θ) (SecondOpen r θ) (curveG2 r θ) from IsUnit.unit_spec _]
  exact IsLocalization.Away.awayToAwayLeft_eq _ _ _

def firstNormalLift (r θ : ℂ) (A L : WeightedPoly) : Fin 3 → FirstOpen r θ :=
  firstLift (firstOpenUnit r θ) (firstOpenAmbient r θ (thetaK θ))
    (firstOpenAmbient r θ A) (firstOpenAmbient r θ L)
def secondNormalLift (r θ : ℂ) (A L : WeightedPoly) : Fin 3 → SecondOpen r θ :=
  secondLift (secondOpenUnit r θ) (secondOpenAmbient r θ (thetaK θ))
    (secondOpenAmbient r θ A) (secondOpenAmbient r θ L)

theorem firstNormalLift_equations (r θ : ℂ) (A L : WeightedPoly) :
    equationMap (firstOpenAmbient r θ (originalG1 r)) (firstOpenAmbient r θ originalG2)
      (firstOpenAmbient r θ (thetaK θ)) (firstNormalLift r θ A L)=
        ![-firstOpenAmbient r θ A,-firstOpenAmbient r θ L] := by
  have hu : (firstOpenUnit r θ : FirstOpen r θ)=firstOpenAmbient r θ (originalG1 r) :=
    IsUnit.unit_spec _
  rw [← hu]
  exact equationMap_firstLift _ _ _ _ _

theorem secondNormalLift_equations (r θ : ℂ) (A L : WeightedPoly) :
    equationMap (secondOpenAmbient r θ (originalG1 r)) (secondOpenAmbient r θ originalG2)
      (secondOpenAmbient r θ (thetaK θ)) (secondNormalLift r θ A L)=
        ![-secondOpenAmbient r θ A,-secondOpenAmbient r θ L] := by
  have hu : (secondOpenUnit r θ : SecondOpen r θ)=secondOpenAmbient r θ originalG2 :=
    IsUnit.unit_spec _
  rw [← hu]
  exact equationMap_secondLift _ _ _ _ _

theorem firstNormalLift_restriction (r θ : ℂ) (A L : WeightedPoly) :
    (fun i => firstRestriction r θ (firstNormalLift r θ A L i))=
      firstLift (firstOverlapUnit r θ) (overlapAmbient r θ (thetaK θ))
        (overlapAmbient r θ A) (overlapAmbient r θ L) := by
  ext i
  fin_cases i <;>
    simp [firstNormalLift, firstLift, firstOpenAmbient, overlapAmbient, firstOverlapUnit,
      firstRestriction, IsLocalization.Away.awayToAwayRight_eq, Units.coe_map_inv]

theorem secondNormalLift_restriction (r θ : ℂ) (A L : WeightedPoly) :
    (fun i => secondRestriction r θ (secondNormalLift r θ A L i))=
      secondLift (secondOverlapUnit r θ) (overlapAmbient r θ (thetaK θ))
        (overlapAmbient r θ A) (overlapAmbient r θ L) := by
  ext i
  fin_cases i <;>
    simp [secondNormalLift, secondLift, secondOpenAmbient, overlapAmbient, secondOverlapUnit,
      secondRestriction, IsLocalization.Away.awayToAwayLeft_eq, Units.coe_map_inv]

/-- The connecting coefficient is now an element of the actual overlap
localization, with both inverses constructed from the two chart restrictions. -/
def normalOverlapCoefficient (r θ : ℂ) (A L : WeightedPoly) : Overlap r θ :=
  overlapCoefficient (firstOverlapUnit r θ) (secondOverlapUnit r θ)
    (overlapAmbient r θ (thetaK θ)) (overlapAmbient r θ A) (overlapAmbient r θ L)

theorem actual_overlap_lift_difference (r θ : ℂ) (A L : WeightedPoly) :
    firstLift (firstOverlapUnit r θ) (overlapAmbient r θ (thetaK θ))
        (overlapAmbient r θ A) (overlapAmbient r θ L)-
      secondLift (secondOverlapUnit r θ) (overlapAmbient r θ (thetaK θ))
        (overlapAmbient r θ A) (overlapAmbient r θ L)=
      normalOverlapCoefficient r θ A L •
        kernelVector (overlapAmbient r θ (originalG1 r)) (overlapAmbient r θ originalG2) := by
  rw [local_lift_difference]
  simp only [normalOverlapCoefficient, coe_firstOverlapUnit, coe_secondOverlapUnit,
    curveG1, curveG2, overlapAmbient, RingHom.comp_apply]

theorem restricted_local_lifts_difference (r θ : ℂ) (A L : WeightedPoly) :
    (fun i => firstRestriction r θ (firstNormalLift r θ A L i))-
      (fun i => secondRestriction r θ (secondNormalLift r θ A L i))=
      normalOverlapCoefficient r θ A L •
        kernelVector (overlapAmbient r θ (originalG1 r)) (overlapAmbient r θ originalG2) := by
  rw [firstNormalLift_restriction, secondNormalLift_restriction, actual_overlap_lift_difference]

end Seed
end CycleQ2NormalConnecting
end

section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace CycleQ2ConormalJacobian
open CycleQ2SeedTrace CycleQ2NormalConnecting
variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

/-- The actual conormal relation after any scalar extension, with no
independent equation-normal presentation supplied as a hypothesis. -/
theorem baseChangedConormal_relation (r θ : ℂ) :
    (1:S) ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent
        ⟨actualSeedEquation r θ,actualSeedEquation_mem r θ⟩ =
      algebraMap P S (originalG1 r) • ((1:S) ⊗ₜ[P] conormalGenerator r θ 0)+
      algebraMap P S originalG2 • ((1:S) ⊗ₜ[P] conormalGenerator r θ 1)+
      algebraMap P S (thetaK θ) • ((1:S) ⊗ₜ[P] conormalGenerator r θ 2) := by
  rw [actual_conormal_relation]
  simp only [TensorProduct.tmul_add,TensorProduct.tmul_smul,algebraMap_smul]

/-- Literal evaluation of the actual two conormal equation classes is the
checked equationMap, on every scalar extension including all prime charts. -/
theorem baseChangedNormalMap_eq (r θ : ℂ)
    (φ : S ⊗[P] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S) :
    ![φ ((1:S) ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent
          ⟨actualSeedEquation r θ,actualSeedEquation_mem r θ⟩),
      φ ((1:S) ⊗ₜ[P] conormalGenerator r θ 2)] =
      equationMap (algebraMap P S (originalG1 r))
        (algebraMap P S originalG2) (algebraMap P S (thetaK θ))
        (fun i => φ ((1:S) ⊗ₜ[P] conormalGenerator r θ i)) := by
  ext i
  fin_cases i
  · simp only [Matrix.cons_val_zero,baseChangedConormal_relation,
      map_add,map_smul,smul_eq_mul]
    rfl
  · rfl

end CycleQ2ConormalJacobian

namespace CycleQ2NaturalNormalMap
open CycleQ2ConormalJacobian CycleQ2NormalConnecting CycleQ2SeedTrace
variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

/-- On every scalar extension, the equation values of the actual dual
natural map are exactly the previously proved normal matrix. This theorem
does not require either equation family to have been proved a basis. -/
theorem naturalNormalMap_equation_coordinates (r θ : ℂ)
    (φ : S ⊗[P] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S) :
    (fun j : Fin 2 => naturalNormalMap r θ φ
        (generator (S := S) (surfaceIdeal r θ) (surfaceEquations r θ) rfl j)) =
      equationMap (algebraMap P S (originalG1 r))
        (algebraMap P S originalG2) (algebraMap P S (thetaK θ))
        (fun i => φ ((1 : S) ⊗ₜ[P] conormalGenerator r θ i)) := by
  calc
    (fun j : Fin 2 => naturalNormalMap r θ φ
        (generator (S := S) (surfaceIdeal r θ) (surfaceEquations r θ) rfl j)) =
        ![φ ((1 : S) ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent
              ⟨actualSeedEquation r θ, actualSeedEquation_mem r θ⟩),
          φ ((1 : S) ⊗ₜ[P] conormalGenerator r θ 2)] := by
      funext j
      fin_cases j <;> rfl
    _ = _ := baseChangedNormalMap_eq r θ φ

end CycleQ2NaturalNormalMap
end

section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace CycleQ2GenuineNormalConnecting
open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap
  CycleQ2NormalConnecting CycleQ2SeedTrace
variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

abbrev CurveConormal (r θ : ℂ) := S ⊗[P] (ambientCurveIdeal r θ).Cotangent
abbrev SurfaceConormal (r θ : ℂ) := S ⊗[P] (surfaceIdeal r θ).Cotangent
abbrev CurveNormal (r θ : ℂ) := CurveConormal (S := S) r θ →ₗ[S] S
abbrev SurfaceNormal (r θ : ℂ) := SurfaceConormal (S := S) r θ →ₗ[S] S

def curveClass (r θ : ℂ) (i : Fin 3) : CurveConormal (S := S) r θ :=
  (1 : S) ⊗ₜ[P] conormalGenerator r θ i

def surfaceClass (r θ : ℂ) (j : Fin 2) : SurfaceConormal (S := S) r θ :=
  generator (S := S) (surfaceIdeal r θ) (surfaceEquations r θ) rfl j

theorem curveNormal_ext (r θ : ℂ) {φ ψ : CurveNormal (S := S) r θ}
    (h : ∀ i, φ (curveClass r θ i) = ψ (curveClass r θ i)) : φ = ψ := by
  apply LinearMap.ext_on_range
    (generators_span (S := S) (ambientCurveIdeal r θ) (curveEquations r θ) rfl)
  exact h

theorem surfaceNormal_ext (r θ : ℂ) {φ ψ : SurfaceNormal (S := S) r θ}
    (h : ∀ j, φ (surfaceClass r θ j) = ψ (surfaceClass r θ j)) : φ = ψ := by
  apply LinearMap.ext_on_range
    (generators_span (S := S) (surfaceIdeal r θ) (surfaceEquations r θ) rfl)
  exact h

section ActualLifts

variable (r θ : ℂ)
variable (b : Module.Basis (Fin 3) S (CurveConormal (S := S) r θ))
variable (hb : ∀ i, b i = curveClass r θ i)

def fromCoordinates : (Fin 3 → S) ≃ₗ[S] CurveNormal (S := S) r θ := b.constr S

include hb in
@[simp] theorem fromCoordinates_class (v : Fin 3 → S) (i : Fin 3) :
    fromCoordinates r θ b v (curveClass r θ i) = v i := by
  rw [← hb i]
  exact b.constr_basis S v i

include hb in
@[simp] theorem fromCoordinates_symm_class (φ : CurveNormal (S := S) r θ) (i : Fin 3) :
    (fromCoordinates r θ b).symm φ i = φ (curveClass r θ i) := by
  change φ (b i) = _
  rw [hb i]

include hb in
/-- The coordinate constructor does not depend on a choice of derivative
duals or of a basis construction once its equation values are fixed. -/
theorem fromCoordinates_unique
    (b' : Module.Basis (Fin 3) S (CurveConormal (S := S) r θ))
    (hb' : ∀ i, b' i = curveClass r θ i) (v : Fin 3 → S) :
    fromCoordinates r θ b v = fromCoordinates r θ b' v := by
  apply curveNormal_ext r θ
  intro i
  rw [fromCoordinates_class r θ b hb, fromCoordinates_class r θ b' hb']

include hb in
theorem naturalNormalMap_fromCoordinates (v : Fin 3 → S) :
    (fun j => naturalNormalMap r θ (fromCoordinates r θ b v) (surfaceClass r θ j)) =
      equationMap (algebraMap P S (originalG1 r)) (algebraMap P S originalG2)
        (algebraMap P S (thetaK θ)) v := by
  calc
    _ = equationMap (algebraMap P S (originalG1 r)) (algebraMap P S originalG2)
        (algebraMap P S (thetaK θ))
        (fun i => fromCoordinates r θ b v (curveClass r θ i)) :=
      naturalNormalMap_equation_coordinates r θ (fromCoordinates r θ b v)
    _ = _ := by
      congr 1
      funext i
      exact fromCoordinates_class r θ b hb v i

def firstGenuineLift (u : Sˣ) (A L : S) : CurveNormal (S := S) r θ :=
  fromCoordinates r θ b (firstLift u (algebraMap P S (thetaK θ)) A L)

def secondGenuineLift (u : Sˣ) (A L : S) : CurveNormal (S := S) r θ :=
  fromCoordinates r θ b (secondLift u (algebraMap P S (thetaK θ)) A L)

def genuineKernelGenerator : CurveNormal (S := S) r θ :=
  fromCoordinates r θ b
    (kernelVector (algebraMap P S (originalG1 r)) (algebraMap P S originalG2))

include hb in
theorem firstGenuineLift_equations (u : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r)) (A L : S) :
    (fun j => naturalNormalMap r θ (firstGenuineLift r θ b u A L) (surfaceClass r θ j)) =
      ![-A, -L] := by
  rw [firstGenuineLift, naturalNormalMap_fromCoordinates r θ b hb, ← hu]
  exact equationMap_firstLift u _ _ A L

include hb in
theorem secondGenuineLift_equations (u : Sˣ)
    (hu : (u : S) = algebraMap P S originalG2) (A L : S) :
    (fun j => naturalNormalMap r θ (secondGenuineLift r θ b u A L) (surfaceClass r θ j)) =
      ![-A, -L] := by
  rw [secondGenuineLift, naturalNormalMap_fromCoordinates r θ b hb, ← hu]
  exact equationMap_secondLift u _ _ A L

include hb in
/-- These are two lifts of the same genuine target normal homomorphism,
not merely solutions of an independently specified coordinate matrix. -/
theorem genuineLifts_same_image (u v : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r))
    (hv : (v : S) = algebraMap P S originalG2) (A L : S) :
    naturalNormalMap r θ (firstGenuineLift r θ b u A L) =
      naturalNormalMap r θ (secondGenuineLift r θ b v A L) := by
  apply surfaceNormal_ext r θ
  intro j
  exact congrFun ((firstGenuineLift_equations r θ b hb u hu A L).trans
    (secondGenuineLift_equations r θ b hb v hv A L).symm) j

include hb in
theorem genuineKernelGenerator_mem :
    naturalNormalMap r θ (genuineKernelGenerator r θ b) = 0 := by
  apply surfaceNormal_ext r θ
  intro j
  have h := congrFun (naturalNormalMap_fromCoordinates r θ b hb
    (kernelVector (algebraMap P S (originalG1 r)) (algebraMap P S originalG2))) j
  simpa only [equationMap_kernelVector, Pi.zero_apply, LinearMap.zero_apply,
    genuineKernelGenerator] using h

/-- The literal scalar in the genuine kernel is the existing normal
connecting coefficient, with first-chart-minus-second-chart sign. -/
theorem genuineLift_difference (u v : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r))
    (hv : (v : S) = algebraMap P S originalG2) (A L : S) :
    firstGenuineLift r θ b u A L - secondGenuineLift r θ b v A L =
      overlapCoefficient u v (algebraMap P S (thetaK θ)) A L •
        genuineKernelGenerator r θ b := by
  rw [firstGenuineLift, secondGenuineLift, ← map_sub, local_lift_difference, map_smul]
  rw [hu, hv]
  rfl

/-- The first-chart scalar coordinate of a genuine normal homomorphism.
On the kernel it is inverse to c |-> c * genuineKernelGenerator. -/
def kernelCoefficient (u : Sˣ) : CurveNormal (S := S) r θ →ₗ[S] S where
  toFun φ := -(φ (curveClass r θ 1) * (↑(u⁻¹) : S))
  map_add' φ ψ := by simp [add_mul, add_comm]
  map_smul' c φ := by simp [smul_eq_mul, mul_assoc]

include hb in
theorem kernelCoefficient_generator (u : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r)) (c : S) :
    kernelCoefficient r θ u (c • genuineKernelGenerator r θ b) = c := by
  change -((c * fromCoordinates r θ b
    (kernelVector (algebraMap P S (originalG1 r)) (algebraMap P S originalG2))
      (curveClass r θ 1)) * (↑(u⁻¹) : S)) = c
  rw [fromCoordinates_class r θ b hb]
  change -(c * (-algebraMap P S (originalG1 r)) * (↑(u⁻¹) : S)) = c
  rw [← hu]
  simp [mul_assoc]

include hb in
theorem genuineLift_difference_coefficient (u v : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r))
    (hv : (v : S) = algebraMap P S originalG2) (A L : S) :
    kernelCoefficient r θ u
        (firstGenuineLift r θ b u A L - secondGenuineLift r θ b v A L) =
      overlapCoefficient u v (algebraMap P S (thetaK θ)) A L := by
  rw [genuineLift_difference r θ b u v hu hv,
    kernelCoefficient_generator r θ b hb u hu]

include hb in
/-- Changing the two local lifts changes the connecting coordinate by
the difference of their kernel coordinates, the Cech coboundary formula. -/
theorem changed_lifts_coefficient (u v : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r))
    (hv : (v : S) = algebraMap P S originalG2) (A L : S)
    (a b' : CurveNormal (S := S) r θ) :
    kernelCoefficient r θ u
      ((firstGenuineLift r θ b u A L + a) - (secondGenuineLift r θ b v A L + b')) =
      overlapCoefficient u v (algebraMap P S (thetaK θ)) A L +
        kernelCoefficient r θ u a - kernelCoefficient r θ u b' := by
  have h := genuineLift_difference_coefficient r θ b hb u v hu hv A L
  rw [map_sub] at h
  simp only [map_sub, map_add]
  rw [show kernelCoefficient r θ u (firstGenuineLift r θ b u A L) +
      kernelCoefficient r θ u a -
      (kernelCoefficient r θ u (secondGenuineLift r θ b v A L) + kernelCoefficient r θ u b') =
      (kernelCoefficient r θ u (firstGenuineLift r θ b u A L) -
        kernelCoefficient r θ u (secondGenuineLift r θ b v A L)) +
        kernelCoefficient r θ u a - kernelCoefficient r θ u b' by abel]
  rw [h]

end ActualLifts

end CycleQ2GenuineNormalConnecting
end

section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2NormalRestriction

open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap
  CycleQ2NormalConnecting CycleQ2SeedTrace CycleQ2GenuineNormalConnecting

section Restriction

variable {S T : Type*} [CommRing S] [CommRing T]
  [Algebra P S] [Algebra P T]

/-- Canonical restriction of genuine normal homomorphisms. -/
def normalRestriction (I : Ideal P) (f : S →ₐ[P] T) :
    (S ⊗[P] I.Cotangent →ₗ[S] S) →ₗ[P]
      (T ⊗[P] I.Cotangent →ₗ[T] T) :=
  (((LinearMap.liftBaseChangeEquiv T).restrictScalars P).toLinearMap).comp
    ((LinearMap.compRight P f.toLinearMap).comp
      (((LinearMap.liftBaseChangeEquiv S).symm.restrictScalars P).toLinearMap))

@[simp] theorem normalRestriction_tmul (I : Ideal P) (f : S →ₐ[P] T)
    (φ : S ⊗[P] I.Cotangent →ₗ[S] S) (t : T) (x : I.Cotangent) :
    normalRestriction I f φ (t ⊗ₜ[P] x) = t * f (φ ((1 : S) ⊗ₜ[P] x)) := by
  simp [normalRestriction, LinearMap.comp_apply, smul_eq_mul]

abbrev curveRestriction (r θ : ℂ) (f : S →ₐ[P] T) :
    CurveNormal (S := S) r θ →ₗ[P] CurveNormal (S := T) r θ :=
  normalRestriction (ambientCurveIdeal r θ) f

abbrev surfaceRestriction (r θ : ℂ) (f : S →ₐ[P] T) :
    SurfaceNormal (S := S) r θ →ₗ[P] SurfaceNormal (S := T) r θ :=
  normalRestriction (surfaceIdeal r θ) f

@[simp] theorem curveRestriction_class (r θ : ℂ) (f : S →ₐ[P] T)
    (φ : CurveNormal (S := S) r θ) (i : Fin 3) :
    curveRestriction r θ f φ (curveClass r θ i) = f (φ (curveClass r θ i)) := by
  simp [curveClass]

@[simp] theorem surfaceRestriction_class (r θ : ℂ) (f : S →ₐ[P] T)
    (φ : SurfaceNormal (S := S) r θ) (i : Fin 2) :
    surfaceRestriction r θ f φ (surfaceClass r θ i) = f (φ (surfaceClass r θ i)) := by
  simp [surfaceClass, generator]

/-- The square of actual natural dual maps and canonical Hom restrictions
commutes before any equation coordinates are chosen. -/
theorem naturalNormalMap_restriction (r θ : ℂ) (f : S →ₐ[P] T)
    (φ : CurveNormal (S := S) r θ) :
    naturalNormalMap r θ (curveRestriction r θ f φ) =
      surfaceRestriction r θ f (naturalNormalMap r θ φ) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro t x
  simp only [naturalNormalMap, LinearMap.dualMap_apply,
    baseChangedNaturalCotangentMap, LinearMap.baseChange_tmul,
    curveRestriction, surfaceRestriction, normalRestriction_tmul]

end Restriction

section Kernel

variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

abbrev NormalKernel (r θ : ℂ) :=
  LinearMap.ker (naturalNormalMap (S := S) r θ)

variable (r θ : ℂ)
variable (b : Module.Basis (Fin 3) S (CurveConormal (S := S) r θ))
variable (hb : ∀ i, b i = curveClass r θ i)

include hb in
/-- Vanishing under the genuine normal map is exactly vanishing of the
checked equation matrix in the genuine equation-class basis. -/
theorem naturalNormalMap_eq_zero_iff (φ : CurveNormal (S := S) r θ) :
    naturalNormalMap r θ φ = 0 ↔
      equationMap (algebraMap P S (originalG1 r)) (algebraMap P S originalG2)
        (algebraMap P S (thetaK θ)) ((fromCoordinates r θ b).symm φ) = 0 := by
  have h := naturalNormalMap_fromCoordinates r θ b hb ((fromCoordinates r θ b).symm φ)
  simp only [LinearEquiv.apply_symm_apply] at h
  constructor
  · intro hz
    rw [hz] at h
    funext j
    simpa only [LinearMap.zero_apply, Pi.zero_apply] using congrFun h.symm j
  · intro hz
    apply surfaceNormal_ext r θ
    intro j
    rw [hz] at h
    exact congrFun h j

include hb in
theorem genuine_kernel_first (u : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r)) (φ : CurveNormal (S := S) r θ) :
    naturalNormalMap r θ φ = 0 ↔
      ∃ c : S, φ = c • genuineKernelGenerator r θ b := by
  rw [naturalNormalMap_eq_zero_iff r θ b hb, ← hu, equationMap_kernel_first]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hh := congrArg (fromCoordinates r θ b) hc
    simpa [genuineKernelGenerator, hu] using hh
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    simp [genuineKernelGenerator, hu]

/-- The complementary local matrix calculation needed on the g2 chart. -/
theorem equationMap_kernel_second (u : Sˣ) (g1 k : S) (v : Fin 3 → S) :
    equationMap g1 (u : S) k v = 0 ↔
      ∃ c : S, v = c • kernelVector g1 (u : S) := by
  constructor
  · intro hv
    have h0 := congrFun hv 0
    have h2 := congrFun hv 1
    change g1 * v 0 + (u : S) * v 1 + k * v 2 = 0 at h0
    change v 2 = 0 at h2
    refine ⟨v 0 * (↑(u⁻¹) : S), ?_⟩
    funext i
    fin_cases i
    · simp [kernelVector, smul_eq_mul, mul_assoc]
    · change v 1 = v 0 * (↑(u⁻¹) : S) * (-g1)
      rw [h2] at h0
      linear_combination (↑(u⁻¹) : S) * h0 - v 1 * u.inv_mul
    · simpa [kernelVector] using h2
  · rintro ⟨c, rfl⟩
    rw [map_smul, equationMap_kernelVector, smul_zero]

include hb in
theorem genuine_kernel_second (u : Sˣ)
    (hu : (u : S) = algebraMap P S originalG2) (φ : CurveNormal (S := S) r θ) :
    naturalNormalMap r θ φ = 0 ↔
      ∃ c : S, φ = c • genuineKernelGenerator r θ b := by
  rw [naturalNormalMap_eq_zero_iff r θ b hb, ← hu, equationMap_kernel_second]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hh := congrArg (fromCoordinates r θ b) hc
    simpa [genuineKernelGenerator, hu] using hh
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    simp [genuineKernelGenerator, hu]

/-- The same intrinsic kernel generator is used on both opens. -/
def kernelParam : S →ₗ[S] NormalKernel (S := S) r θ where
  toFun c := ⟨c • genuineKernelGenerator r θ b, by
    change naturalNormalMap r θ (c • genuineKernelGenerator r θ b) = 0
    rw [map_smul, genuineKernelGenerator_mem r θ b hb, smul_zero]⟩
  map_add' c d := by apply Subtype.ext; simp [add_smul]
  map_smul' c d := by apply Subtype.ext; simp [smul_smul]

@[simp] theorem kernelParam_val (c : S) :
    (kernelParam r θ b hb c).val = c • genuineKernelGenerator r θ b := rfl

include hb in
theorem kernelParam_bijective_first (u : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r)) :
    Function.Bijective (kernelParam r θ b hb) := by
  constructor
  · intro c d h
    have hh := congrArg (fun z : NormalKernel (S := S) r θ =>
      kernelCoefficient r θ u z.val) h
    simpa only [kernelParam_val, kernelCoefficient_generator r θ b hb u hu] using hh
  · intro φ
    obtain ⟨c, hc⟩ := (genuine_kernel_first r θ b hb u hu φ.val).mp φ.property
    exact ⟨c, Subtype.ext hc.symm⟩

include hb in
theorem kernelParam_bijective_second (u : Sˣ)
    (hu : (u : S) = algebraMap P S originalG2) :
    Function.Bijective (kernelParam r θ b hb) := by
  constructor
  · intro c d h
    have hh := congrArg (fun z : NormalKernel (S := S) r θ =>
      z.val (curveClass r θ 0) * (↑(u⁻¹) : S)) h
    simp only [kernelParam_val, LinearMap.smul_apply, smul_eq_mul,
      genuineKernelGenerator, fromCoordinates_class r θ b hb] at hh
    change c * algebraMap P S originalG2 * (↑(u⁻¹) : S) =
      d * algebraMap P S originalG2 * (↑(u⁻¹) : S) at hh
    simpa [← hu, mul_assoc] using hh
  · intro φ
    obtain ⟨c, hc⟩ := (genuine_kernel_second r θ b hb u hu φ.val).mp φ.property
    exact ⟨c, Subtype.ext hc.symm⟩

/-- Genuine rank-one trivialization on the first denominator chart. -/
def firstKernelEquiv (u : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r)) :
    S ≃ₗ[S] NormalKernel (S := S) r θ :=
  LinearEquiv.ofBijective (kernelParam r θ b hb)
    (kernelParam_bijective_first r θ b hb u hu)

/-- The same generator gives the complementary chart trivialization. -/
def secondKernelEquiv (u : Sˣ)
    (hu : (u : S) = algebraMap P S originalG2) :
    S ≃ₗ[S] NormalKernel (S := S) r θ :=
  LinearEquiv.ofBijective (kernelParam r θ b hb)
    (kernelParam_bijective_second r θ b hb u hu)

@[simp] theorem firstKernelEquiv_apply (u : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r)) (c : S) :
    firstKernelEquiv r θ b hb u hu c = kernelParam r θ b hb c := rfl

@[simp] theorem secondKernelEquiv_apply (u : Sˣ)
    (hu : (u : S) = algebraMap P S originalG2) (c : S) :
    secondKernelEquiv r θ b hb u hu c = kernelParam r θ b hb c := rfl

end Kernel

section KernelRestriction

variable {S T : Type*} [CommRing S] [CommRing T]
  [Algebra P S] [Algebra P T]
  [Algebra ℂ S] [Algebra ℂ T] [IsScalarTower ℂ P S] [IsScalarTower ℂ P T]

/-- Canonical restriction on the kernel of the actual natural normal map. -/
def kernelRestriction (r θ : ℂ) (f : S →ₐ[P] T) :
    NormalKernel (S := S) r θ →ₗ[P] NormalKernel (S := T) r θ where
  toFun φ := ⟨curveRestriction r θ f φ.val, by
    change naturalNormalMap r θ (curveRestriction r θ f φ.val) = 0
    rw [naturalNormalMap_restriction, φ.property, map_zero]⟩
  map_add' φ ψ := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c φ := by apply Subtype.ext; exact map_smul _ _ _

@[simp] theorem kernelRestriction_val (r θ : ℂ) (f : S →ₐ[P] T)
    (φ : NormalKernel (S := S) r θ) :
    (kernelRestriction r θ f φ).val = curveRestriction r θ f φ.val := rfl

/-- The coordinate constructor respects the canonical tensor-Hom restriction. -/
theorem fromCoordinates_restriction (r θ : ℂ) (f : S →ₐ[P] T)
    (bS : Module.Basis (Fin 3) S (CurveConormal (S := S) r θ))
    (hS : ∀ i, bS i = curveClass r θ i)
    (bT : Module.Basis (Fin 3) T (CurveConormal (S := T) r θ))
    (hT : ∀ i, bT i = curveClass r θ i) (v : Fin 3 → S) :
    curveRestriction r θ f (fromCoordinates r θ bS v) =
      fromCoordinates r θ bT (fun i => f (v i)) := by
  apply curveNormal_ext r θ
  intro i
  rw [curveRestriction_class, fromCoordinates_class r θ bS hS,
    fromCoordinates_class r θ bT hT]

/-- The scalar kernel trivializations commute with every actual algebra
restriction. This is the compatibility needed for the two-open Cech quotient. -/
theorem kernelParam_restriction (r θ : ℂ) (f : S →ₐ[P] T)
    (bS : Module.Basis (Fin 3) S (CurveConormal (S := S) r θ))
    (hS : ∀ i, bS i = curveClass r θ i)
    (bT : Module.Basis (Fin 3) T (CurveConormal (S := T) r θ))
    (hT : ∀ i, bT i = curveClass r θ i) (c : S) :
    kernelRestriction r θ f (kernelParam r θ bS hS c) =
      kernelParam r θ bT hT (f c) := by
  apply Subtype.ext
  apply curveNormal_ext r θ
  intro i
  simp only [kernelRestriction_val, kernelParam_val, curveRestriction_class,
    LinearMap.smul_apply, genuineKernelGenerator, fromCoordinates_class r θ bS hS,
    fromCoordinates_class r θ bT hT, smul_eq_mul]
  fin_cases i <;>
    simp [kernelVector, map_mul, AlgHom.commutes]

end KernelRestriction
end CycleQ2NormalRestriction

end

section
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
namespace CycleQ2ActualNormalCech
open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap CycleQ2NormalConnecting
  CycleQ2SeedTrace CycleQ2GenuineNormalConnecting CycleQ2NormalRestriction
  CycleQ2SeedGlobalConormal CycleQ2SeedCechTheta

def firstBasis (r θ : ℂ) :
    Module.Basis (Fin 3) (FirstOpen r θ) (CurveConormal (S := FirstOpen r θ) r θ) :=
  seedConormalBasis (S := FirstOpen r θ) r θ (first_annihilates r θ)
def secondBasis (r θ : ℂ) :
    Module.Basis (Fin 3) (SecondOpen r θ) (CurveConormal (S := SecondOpen r θ) r θ) :=
  seedConormalBasis (S := SecondOpen r θ) r θ (second_annihilates r θ)
def overlapBasis (r θ : ℂ) :
    Module.Basis (Fin 3) (Overlap r θ) (CurveConormal (S := Overlap r θ) r θ) :=
  seedConormalBasis (S := Overlap r θ) r θ (overlap_annihilates r θ)

@[simp] theorem firstBasis_apply (r θ : ℂ) (i : Fin 3) :
    firstBasis r θ i = curveClass r θ i :=
  seedConormalBasis_apply (S := FirstOpen r θ) r θ (first_annihilates r θ) i
@[simp] theorem secondBasis_apply (r θ : ℂ) (i : Fin 3) :
    secondBasis r θ i = curveClass r θ i :=
  seedConormalBasis_apply (S := SecondOpen r θ) r θ (second_annihilates r θ) i
@[simp] theorem overlapBasis_apply (r θ : ℂ) (i : Fin 3) :
    overlapBasis r θ i = curveClass r θ i :=
  seedConormalBasis_apply (S := Overlap r θ) r θ (overlap_annihilates r θ) i

theorem firstUnit_value (r θ : ℂ) :
    (firstOpenUnit r θ : FirstOpen r θ) = algebraMap P (FirstOpen r θ) (originalG1 r) :=
  IsUnit.unit_spec _
theorem secondUnit_value (r θ : ℂ) :
    (secondOpenUnit r θ : SecondOpen r θ) = algebraMap P (SecondOpen r θ) originalG2 :=
  IsUnit.unit_spec _
theorem firstOverlapUnit_value (r θ : ℂ) :
    (firstOverlapUnit r θ : Overlap r θ) = algebraMap P (Overlap r θ) (originalG1 r) :=
  coe_firstOverlapUnit r θ
theorem secondOverlapUnit_value (r θ : ℂ) :
    (secondOverlapUnit r θ : Overlap r θ) = algebraMap P (Overlap r θ) originalG2 :=
  coe_secondOverlapUnit r θ

/-- The actual normal map is surjective on the first open: every genuine
target homomorphism is lifted by its two actual equation values. -/
theorem first_normal_surjective (r θ : ℂ) :
    Function.Surjective (naturalNormalMap (S := FirstOpen r θ) r θ) := by
  intro ψ
  refine ⟨firstGenuineLift r θ (firstBasis r θ) (firstOpenUnit r θ)
    (-ψ (surfaceClass r θ 0)) (-ψ (surfaceClass r θ 1)), ?_⟩
  apply surfaceNormal_ext r θ
  intro j
  have hh := congrFun (firstGenuineLift_equations r θ (firstBasis r θ)
    (firstBasis_apply r θ) (firstOpenUnit r θ) (firstUnit_value r θ)
    (-ψ (surfaceClass r θ 0)) (-ψ (surfaceClass r θ 1))) j
  fin_cases j <;> simpa using hh

/-- Surjectivity on the complementary actual open. -/
theorem second_normal_surjective (r θ : ℂ) :
    Function.Surjective (naturalNormalMap (S := SecondOpen r θ) r θ) := by
  intro ψ
  refine ⟨secondGenuineLift r θ (secondBasis r θ) (secondOpenUnit r θ)
    (-ψ (surfaceClass r θ 0)) (-ψ (surfaceClass r θ 1)), ?_⟩
  apply surfaceNormal_ext r θ
  intro j
  have hh := congrFun (secondGenuineLift_equations r θ (secondBasis r θ)
    (secondBasis_apply r θ) (secondOpenUnit r θ) (secondUnit_value r θ)
    (-ψ (surfaceClass r θ 0)) (-ψ (surfaceClass r θ 1))) j
  fin_cases j <;> simpa using hh

abbrev FirstKernel (r θ : ℂ) := NormalKernel (S := FirstOpen r θ) r θ
abbrev SecondKernel (r θ : ℂ) := NormalKernel (S := SecondOpen r θ) r θ
abbrev OverlapKernel (r θ : ℂ) := NormalKernel (S := Overlap r θ) r θ

/-- Cache the inherited additive groups and scalar modules of the genuine
kernel subtypes, keeping the same subtype operations and polynomial action. -/
instance (priority := 2000) firstKernelAddCommGroup (r θ : ℂ) :
    AddCommGroup (FirstKernel r θ) :=
  Submodule.addCommGroup (LinearMap.ker (naturalNormalMap (S := FirstOpen r θ) r θ))
instance (priority := 2000) firstKernelAddCommMonoid (r θ : ℂ) :
    AddCommMonoid (FirstKernel r θ) := (firstKernelAddCommGroup r θ).toAddCommMonoid
instance (priority := 2000) firstKernelPolynomialModule (r θ : ℂ) :
    Module P (FirstKernel r θ) := inferInstance

instance (priority := 2000) secondKernelAddCommGroup (r θ : ℂ) :
    AddCommGroup (SecondKernel r θ) :=
  Submodule.addCommGroup (LinearMap.ker (naturalNormalMap (S := SecondOpen r θ) r θ))
instance (priority := 2000) secondKernelAddCommMonoid (r θ : ℂ) :
    AddCommMonoid (SecondKernel r θ) := (secondKernelAddCommGroup r θ).toAddCommMonoid
instance (priority := 2000) secondKernelPolynomialModule (r θ : ℂ) :
    Module P (SecondKernel r θ) := inferInstance

instance (priority := 2000) overlapKernelAddCommGroup (r θ : ℂ) :
    AddCommGroup (OverlapKernel r θ) :=
  Submodule.addCommGroup (LinearMap.ker (naturalNormalMap (S := Overlap r θ) r θ))
instance (priority := 2000) overlapKernelAddCommMonoid (r θ : ℂ) :
    AddCommMonoid (OverlapKernel r θ) := (overlapKernelAddCommGroup r θ).toAddCommMonoid
instance (priority := 2000) overlapKernelPolynomialModule (r θ : ℂ) :
    Module P (OverlapKernel r θ) := inferInstance

def firstKernelEquivalence (r θ : ℂ) : FirstOpen r θ ≃ₗ[P] FirstKernel r θ :=
  (firstKernelEquiv r θ (firstBasis r θ) (firstBasis_apply r θ)
    (firstOpenUnit r θ) (firstUnit_value r θ)).restrictScalars P

def secondKernelEquivalence (r θ : ℂ) : SecondOpen r θ ≃ₗ[P] SecondKernel r θ :=
  (secondKernelEquiv r θ (secondBasis r θ) (secondBasis_apply r θ)
    (secondOpenUnit r θ) (secondUnit_value r θ)).restrictScalars P

def overlapKernelEquivalence (r θ : ℂ) : Overlap r θ ≃ₗ[P] OverlapKernel r θ :=
  (firstKernelEquiv r θ (overlapBasis r θ) (overlapBasis_apply r θ)
    (firstOverlapUnit r θ) (firstOverlapUnit_value r θ)).restrictScalars P

def firstKernelRestriction (r θ : ℂ) : FirstKernel r θ →ₗ[P] OverlapKernel r θ :=
  kernelRestriction r θ (firstRestrictionAlg r θ)
def secondKernelRestriction (r θ : ℂ) : SecondKernel r θ →ₗ[P] OverlapKernel r θ :=
  kernelRestriction r θ (secondRestrictionAlg r θ)

theorem firstKernelRestriction_trivialization (r θ : ℂ) (c : FirstOpen r θ) :
    firstKernelRestriction r θ (firstKernelEquivalence r θ c) =
      overlapKernelEquivalence r θ (firstRestriction r θ c) :=
  kernelParam_restriction r θ (firstRestrictionAlg r θ)
    (firstBasis r θ) (firstBasis_apply r θ)
    (overlapBasis r θ) (overlapBasis_apply r θ) c

theorem secondKernelRestriction_trivialization (r θ : ℂ) (c : SecondOpen r θ) :
    secondKernelRestriction r θ (secondKernelEquivalence r θ c) =
      overlapKernelEquivalence r θ (secondRestriction r θ c) :=
  kernelParam_restriction r θ (secondRestrictionAlg r θ)
    (secondBasis r θ) (secondBasis_apply r θ)
    (overlapBasis r θ) (overlapBasis_apply r θ) c

/-- Degree-unrestricted scalar Cech coboundaries on the two actual opens. -/
def scalarBoundaries (r θ : ℂ) : Submodule P (Overlap r θ) :=
  LinearMap.range (firstRestrictionAlg r θ).toLinearMap ⊔
    LinearMap.range (secondRestrictionAlg r θ).toLinearMap

/-- Genuine normal-kernel coboundaries using the canonical Hom restrictions. -/
def normalBoundaries (r θ : ℂ) : Submodule P (OverlapKernel r θ) :=
  LinearMap.range (firstKernelRestriction r θ) ⊔
    LinearMap.range (secondKernelRestriction r θ)

abbrev ScalarCech (r θ : ℂ) := (Overlap r θ) ⧸ scalarBoundaries r θ
abbrev NormalCech (r θ : ℂ) := (OverlapKernel r θ) ⧸ normalBoundaries r θ

private theorem map_first_range (r θ : ℂ) :
    (LinearMap.range (firstKernelRestriction r θ)).map
        (overlapKernelEquivalence r θ).symm.toLinearMap =
      LinearMap.range (firstRestrictionAlg r θ).toLinearMap := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (firstKernelEquivalence r θ).surjective y
    refine ⟨c, ?_⟩
    rw [firstKernelRestriction_trivialization]
    exact ((overlapKernelEquivalence r θ).symm_apply_apply (firstRestriction r θ c)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨firstKernelRestriction r θ (firstKernelEquivalence r θ c),
      ⟨firstKernelEquivalence r θ c, rfl⟩, ?_⟩
    rw [firstKernelRestriction_trivialization]
    exact (overlapKernelEquivalence r θ).symm_apply_apply (firstRestriction r θ c)

private theorem map_second_range (r θ : ℂ) :
    (LinearMap.range (secondKernelRestriction r θ)).map
        (overlapKernelEquivalence r θ).symm.toLinearMap =
      LinearMap.range (secondRestrictionAlg r θ).toLinearMap := by
  ext z
  constructor
  · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (secondKernelEquivalence r θ).surjective y
    refine ⟨c, ?_⟩
    rw [secondKernelRestriction_trivialization]
    exact ((overlapKernelEquivalence r θ).symm_apply_apply (secondRestriction r θ c)).symm
  · rintro ⟨c, rfl⟩
    refine ⟨secondKernelRestriction r θ (secondKernelEquivalence r θ c),
      ⟨secondKernelEquivalence r θ c, rfl⟩, ?_⟩
    rw [secondKernelRestriction_trivialization]
    exact (overlapKernelEquivalence r θ).symm_apply_apply (secondRestriction r θ c)

theorem normalBoundaries_map (r θ : ℂ) :
    (normalBoundaries r θ).map (overlapKernelEquivalence r θ).symm.toLinearMap =
      scalarBoundaries r θ := by
  rw [normalBoundaries, Submodule.map_sup, map_first_range, map_second_range]
  rfl

/-- The actual kernel Cech module is canonically identified with the scalar
Cech module by its equation generator, compatibly on both opens. -/
def normalCechEquivalence (r θ : ℂ) : NormalCech r θ ≃ₗ[P] ScalarCech r θ :=
  Submodule.Quotient.equiv (normalBoundaries r θ) (scalarBoundaries r θ)
    (overlapKernelEquivalence r θ).symm (normalBoundaries_map r θ)

def actualFirstLift (r θ : ℂ) (A L : P) : CurveNormal (S := FirstOpen r θ) r θ :=
  fromCoordinates r θ (firstBasis r θ) (firstNormalLift r θ A L)
def actualSecondLift (r θ : ℂ) (A L : P) : CurveNormal (S := SecondOpen r θ) r θ :=
  fromCoordinates r θ (secondBasis r θ) (secondNormalLift r θ A L)

theorem actualFirstLift_restriction (r θ : ℂ) (A L : P) :
    curveRestriction r θ (firstRestrictionAlg r θ) (actualFirstLift r θ A L) =
      firstGenuineLift r θ (overlapBasis r θ) (firstOverlapUnit r θ)
        (overlapAmbient r θ A) (overlapAmbient r θ L) := by
  rw [actualFirstLift, fromCoordinates_restriction r θ (firstRestrictionAlg r θ)
    (firstBasis r θ) (firstBasis_apply r θ) (overlapBasis r θ) (overlapBasis_apply r θ)]
  change fromCoordinates r θ (overlapBasis r θ)
      (fun i => firstRestriction r θ (firstNormalLift r θ A L i)) = _
  rw [firstNormalLift_restriction]
  rfl

theorem actualSecondLift_restriction (r θ : ℂ) (A L : P) :
    curveRestriction r θ (secondRestrictionAlg r θ) (actualSecondLift r θ A L) =
      secondGenuineLift r θ (overlapBasis r θ) (secondOverlapUnit r θ)
        (overlapAmbient r θ A) (overlapAmbient r θ L) := by
  rw [actualSecondLift, fromCoordinates_restriction r θ (secondRestrictionAlg r θ)
    (secondBasis r θ) (secondBasis_apply r θ) (overlapBasis r θ) (overlapBasis_apply r θ)]
  change fromCoordinates r θ (overlapBasis r θ)
      (fun i => secondRestriction r θ (secondNormalLift r θ A L i)) = _
  rw [secondNormalLift_restriction]
  rfl

/-- Difference of restrictions of actual normal lifts, in the actual kernel. -/
def connectingRepresentative (r θ : ℂ) (A L : P) : OverlapKernel r θ :=
  ⟨curveRestriction r θ (firstRestrictionAlg r θ) (actualFirstLift r θ A L) -
    curveRestriction r θ (secondRestrictionAlg r θ) (actualSecondLift r θ A L), by
    change naturalNormalMap r θ (_ - _) = 0
    rw [map_sub, actualFirstLift_restriction, actualSecondLift_restriction,
      genuineLifts_same_image r θ (overlapBasis r θ) (overlapBasis_apply r θ)
        (firstOverlapUnit r θ) (secondOverlapUnit r θ)
        (firstOverlapUnit_value r θ) (secondOverlapUnit_value r θ), sub_self]⟩

/-- The genuine kernel representative is the old scalar coefficient times
the actual intrinsic generator, with no assumed connecting-class identity. -/
theorem connectingRepresentative_eq (r θ : ℂ) (A L : P) :
    connectingRepresentative r θ A L =
      overlapKernelEquivalence r θ (normalOverlapCoefficient r θ A L) := by
  apply Subtype.ext
  change curveRestriction r θ (firstRestrictionAlg r θ) (actualFirstLift r θ A L) -
      curveRestriction r θ (secondRestrictionAlg r θ) (actualSecondLift r θ A L) = _
  rw [actualFirstLift_restriction, actualSecondLift_restriction,
    genuineLift_difference r θ (overlapBasis r θ)
      (firstOverlapUnit r θ) (secondOverlapUnit r θ)
      (firstOverlapUnit_value r θ) (secondOverlapUnit_value r θ)]
  rfl

def connectingClass (r θ : ℂ) (A L : P) : NormalCech r θ :=
  Submodule.Quotient.mk (connectingRepresentative r θ A L)

/-- The actual two-open connecting class has exactly the previously
computed scalar Cech class. -/
theorem connectingClass_eq_scalar (r θ : ℂ) (A L : P) :
    normalCechEquivalence r θ (connectingClass r θ A L) =
      (Submodule.Quotient.mk (normalOverlapCoefficient r θ A L) : ScalarCech r θ) := by
  change (Submodule.Quotient.mk ((overlapKernelEquivalence r θ).symm
    (connectingRepresentative r θ A L)) : ScalarCech r θ) = _
  rw [connectingRepresentative_eq, LinearEquiv.symm_apply_apply]

end CycleQ2ActualNormalCech
end

namespace CycleQ2GeometricRelativeNormalConnecting

open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap CycleQ2NormalConnecting
  CycleQ2SeedTrace CycleQ2GenuineNormalConnecting CycleQ2NormalRestriction
  CycleQ2ActualNormalCech CycleQ2GeometricSeedNormalIdeals

/-- The already constructed difference of actual local normal lifts, regarded as a
homomorphism on the actual curve ideal modulo its square inside the actual surface. -/
def relativeConnectingRepresentative (r θ : ℂ) (A L : P) :
    RelativeNormal r θ (Overlap r θ) :=
  (overlapNormalModuleEquiv r θ).symm (connectingRepresentative r θ A L)

/-- The canonical comparison recovers the original connecting cochain exactly. -/
theorem relativeConnectingRepresentative_comparison (r θ : ℂ) (A L : P) :
    overlapNormalModuleEquiv r θ (relativeConnectingRepresentative r θ A L) =
      connectingRepresentative r θ A L :=
  (overlapNormalModuleEquiv r θ).apply_symm_apply _

/-- The surface-relative representative has the same values on the literal equations. -/
theorem relativeConnectingRepresentative_equation_value (r θ : ℂ) (A L : P) (i : Fin 3) :
    relativeConnectingRepresentative r θ A L (relativeEquationClass r θ (Overlap r θ) i) =
      (connectingRepresentative r θ A L).val
        ((1 : Overlap r θ) ⊗ₜ[P] conormalGenerator r θ i) :=
  normalModuleEquiv_symm_equation r θ (Overlap r θ) (connectingRepresentative r θ A L) i

/-- The actual relative normal homomorphism has the computed coefficient
`(k L - A)/(g1 g2)` multiplying the equation vector `(g2,-g1,0)`. -/
theorem relativeConnectingRepresentative_equation (r θ : ℂ) (A L : P) (i : Fin 3) :
    relativeConnectingRepresentative r θ A L (relativeEquationClass r θ (Overlap r θ) i) =
      normalOverlapCoefficient r θ A L *
        kernelVector (overlapAmbient r θ (originalG1 r)) (overlapAmbient r θ originalG2) i := by
  rw [relativeConnectingRepresentative_equation_value, connectingRepresentative_eq]
  change (normalOverlapCoefficient r θ A L •
      genuineKernelGenerator r θ (overlapBasis r θ)) (curveClass r θ i) = _
  rw [LinearMap.smul_apply, genuineKernelGenerator,
    fromCoordinates_class r θ (overlapBasis r θ) (overlapBasis_apply r θ)]
  rfl

/-- For the literal ambient test with fixed cubic, the sign is negative and the
coefficient is the actual overlap element `-A/(g1 g2)`. Both units are the
ones constructed from the existing localization restriction maps. -/
theorem fixed_h_equation_vector (r θ : ℂ) :
    (fun i : Fin 3 => relativeConnectingRepresentative r θ derivativeA 0
      (relativeEquationClass r θ (Overlap r θ) i)) =
      (-(overlapAmbient r θ derivativeA) *
        (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) *
        (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ)) •
        kernelVector (overlapAmbient r θ (originalG1 r)) (overlapAmbient r θ originalG2) := by
  funext i
  rw [relativeConnectingRepresentative_equation]
  simp only [normalOverlapCoefficient, overlapCoefficient, map_zero, mul_zero,
    zero_sub, Pi.smul_apply, smul_eq_mul]

/-- The relative-normal comparison for the ambient test at the exact `(57,1)`
incidence seed. No cube-root or sparse-theta specialization is substituted. -/
theorem literal_ambient_test_comparison :
    overlapNormalModuleEquiv 57 1 (relativeConnectingRepresentative 57 1 derivativeA 0) =
      connectingRepresentative 57 1 derivativeA 0 :=
  relativeConnectingRepresentative_comparison 57 1 derivativeA 0

end CycleQ2GeometricRelativeNormalConnecting
