import Proposal.Workspace

/-!
Target-side algebra for the nonconstructive route in Chapter 3D.

These lemmas concern the protected F and A, not a replacement instance.
They establish the two diagonal actions and the determinant-weighted source.
They do not assert divisor support, a rational primitive, or certificate existence.
-/

noncomputable section
namespace CycleQ2GeometricTarget
open MvPolynomial

abbrev Poly := HodgeComputer.AmbientPoly 5
abbrev F : Poly := HodgeSubmission.F
abbrev A : Poly := HodgeSubmission.A

/-- The protected equation evaluated on an affine representative. -/
def equationValue (z : Fin 6 → ℂ) : ℂ :=
  z 0 ^ 6 + z 1 ^ 6 + z 2 ^ 6 + z 3 ^ 6 + z 4 ^ 6 + z 5 ^ 6 +
    (z 0 ^ 3 * z 1 * z 3 * z 4 +
     z 1 ^ 3 * z 2 * z 4 * z 5 +
     z 2 ^ 3 * z 0 * z 5 * z 3) / 2

def sourceValue (z : Fin 6 → ℂ) : ℂ :=
  z 0 ^ 2 * z 1 ^ 2 * z 2 ^ 3 * z 3 ^ 2 * z 4 ^ 2 * z 5

theorem eval_F (z : Fin 6 → ℂ) : eval z F = equationValue z := by
  norm_num [F, HodgeSubmission.F, equationValue] <;> ring

theorem eval_A (z : Fin 6 → ℂ) : eval z A = sourceValue z := by
  norm_num [A, HodgeSubmission.A, sourceValue] <;> ring

/-- The paired sign on (X2,Y2). -/
def beta (z : Fin 6 → ℂ) : Fin 6 → ℂ :=
  ![z 0, z 1, -z 2, z 3, z 4, -z 5]

/-- The order-three action in the ORIGINAL coordinate order. -/
def gamma (ω : ℂ) (z : Fin 6 → ℂ) : Fin 6 → ℂ :=
  ![ω ^ 2 * z 0, ω ^ 2 * z 1, z 2, ω * z 3, z 4, z 5]

def betaDet : ℂ := 1 * 1 * (-1) * 1 * 1 * (-1)
def gammaDet (ω : ℂ) : ℂ := ω ^ 2 * ω ^ 2 * 1 * ω * 1 * 1

theorem beta_involution (z : Fin 6 → ℂ) : beta (beta z) = z := by
  funext i
  fin_cases i <;> simp [beta]

theorem gamma_order_three (ω : ℂ) (hω : ω ^ 3 = 1) (z : Fin 6 → ℂ) :
    gamma ω (gamma ω (gamma ω z)) = z := by
  have h6 : ω ^ 6 = 1 := by
    calc
      ω ^ 6 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω]; norm_num
  funext i
  fin_cases i <;> dsimp [gamma] <;> ring_nf <;> simp [hω, h6]

theorem beta_gamma_commute (ω : ℂ) (z : Fin 6 → ℂ) :
    beta (gamma ω z) = gamma ω (beta z) := by
  funext i
  fin_cases i <;> simp [beta, gamma]

theorem equationValue_beta (z : Fin 6 → ℂ) :
    equationValue (beta z) = equationValue z := by
  norm_num [equationValue, beta] <;> ring

theorem sourceValue_beta (z : Fin 6 → ℂ) :
    sourceValue (beta z) = sourceValue z := by
  norm_num [sourceValue, beta] <;> ring

theorem equationValue_gamma (ω : ℂ) (hω : ω ^ 3 = 1) (z : Fin 6 → ℂ) :
    equationValue (gamma ω z) = equationValue z := by
  have h6 : ω ^ 6 = 1 := by
    calc
      ω ^ 6 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω]; norm_num
  have h9 : ω ^ 9 = 1 := by
    calc
      ω ^ 9 = (ω ^ 3) ^ 3 := by ring
      _ = 1 := by rw [hω]; norm_num
  have h12 : ω ^ 12 = 1 := by
    calc
      ω ^ 12 = (ω ^ 3) ^ 4 := by ring
      _ = 1 := by rw [hω]; norm_num
  dsimp [equationValue, gamma]
  ring_nf
  simp [hω, h6, h9, h12]

theorem sourceValue_gamma (ω : ℂ) (hω : ω ^ 3 = 1) (z : Fin 6 → ℂ) :
    sourceValue (gamma ω z) = ω * sourceValue z := by
  have h10 : ω ^ 10 = ω := by
    calc
      ω ^ 10 = (ω ^ 3) ^ 3 * ω := by ring
      _ = ω := by rw [hω]; ring
  dsimp [sourceValue, gamma]
  ring_nf
  simp [h10]

theorem beta_F (z : Fin 6 → ℂ) : eval (beta z) F = eval z F := by
  rw [eval_F, eval_F]
  exact equationValue_beta z

theorem gamma_F (ω : ℂ) (hω : ω ^ 3 = 1) (z : Fin 6 → ℂ) :
    eval (gamma ω z) F = eval z F := by
  rw [eval_F, eval_F]
  exact equationValue_gamma ω hω z

/-- Invariance of the source times the determinant, not invariance of A alone. -/
theorem beta_source_with_volume (z : Fin 6 → ℂ) :
    betaDet * eval (beta z) A = eval z A := by
  rw [eval_A, eval_A, sourceValue_beta]
  norm_num [betaDet]

theorem gamma_source_with_volume (ω : ℂ) (hω : ω ^ 3 = 1)
    (z : Fin 6 → ℂ) : gammaDet ω * eval (gamma ω z) A = eval z A := by
  rw [eval_A, eval_A, sourceValue_gamma ω hω]
  calc
    gammaDet ω * (ω * sourceValue z) = (ω ^ 3) ^ 2 * sourceValue z := by
      dsimp [gammaDet]
      ring
    _ = sourceValue z := by rw [hω]; simp

/-- Algebraic application data only. Smoothness, geometric support and the
support-to-certificate theorem are NOT encoded as fields of this structure. -/
structure AlgebraicInputs : Prop where
  pole_parameter : HodgeSubmission.q = 2
  hypersurface_ne_zero : F ≠ 0
  hypersurface_homogeneous : F.IsHomogeneous 6
  source_homogeneous : A.IsHomogeneous 12
  paired_sign_equation : ∀ z, eval (beta z) F = eval z F
  paired_sign_source : ∀ z, betaDet * eval (beta z) A = eval z A
  order_three_equation : ∀ ω : ℂ, ω ^ 3 = 1 →
    ∀ z, eval (gamma ω z) F = eval z F
  order_three_source : ∀ ω : ℂ, ω ^ 3 = 1 →
    ∀ z, gammaDet ω * eval (gamma ω z) A = eval z A

theorem algebraicInputs : AlgebraicInputs where
  pole_parameter := rfl
  hypersurface_ne_zero := CycleQ2Workspace.originalF_ne_zero
  hypersurface_homogeneous := CycleQ2Workspace.originalF_homogeneous
  source_homogeneous := CycleQ2Workspace.originalA_homogeneous
  paired_sign_equation := beta_F
  paired_sign_source := beta_source_with_volume
  order_three_equation := gamma_F
  order_three_source := gamma_source_with_volume

#print axioms beta_F
#print axioms gamma_F
#print axioms gamma_source_with_volume
#print axioms algebraicInputs
end CycleQ2GeometricTarget
