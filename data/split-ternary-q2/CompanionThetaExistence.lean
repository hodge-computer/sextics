import Proposal.CompanionThetaScalar
import Proposal.CompanionPoleTwoFamily

/-! Actual existence of the protected first-companion theta primitive,
including the finite polynomial conic family and the second normal residue.
Prepared with OpenAI Codex assistance for fqlx. -/
noncomputable section
open scoped BigOperators

namespace SplitFCompanion
open HoldoutConstruction SplitCompanionPoleTwo
local instance : Algebra ℤ (FunctionField true) := Ring.toIntAlgebra _

theorem cone_density_primitive : ConeDensityPrimitive := by
  obtain ⟨w,hw⟩ := rational_source_residue_solution true
  refine ⟨w,?_⟩
  rw [hw,rationalNumerator_partial,rationalDenominator_partial,hypersurfaceT_second,SplitCompanionPoleTwo.normal_polynomial]
  simp only [rationalNumerator,rationalDenominator,map_mul,map_pow,map_neg,map_zero,map_ofNat]
  field_simp [T_ne_zero true]
  ring
end SplitFCompanion

namespace SplitFElliptic
open HoldoutConstruction CrossedElliptic SplitFCompanion
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

/-- The actual first companion supplies the theta source needed in the
product, with no geometric existence inputs left outstanding. -/
theorem theta_scalar_primitive_complete (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ p)
    (Dx Dy : Derivation ℤ K K)
    (hcx : ∀ c,Dx (φ (MvPolynomial.C c))=0)
    (hcy : ∀ c,Dy (φ (MvPolynomial.C c))=0)
    (hxx : ∀ i : Fin 2,Dx (φ (MvPolynomial.X i))=if i=0 then 1 else 0)
    (hyy : ∀ i : Fin 2,Dy (φ (MvPolynomial.X i))=if i=1 then 1 else 0) :
    ∃ bf cx cy : E K,
      (delta bf+coefficient Dx cx+coefficient Dy cy=
        algebraMap K (E K) (φ h/u^5)*thetaRatio) ∧
      ∀ Z : Derivation ℤ K K,(∀ P : P2,Z (φ P)=0) → Z u=0 →
        coefficient Z bf=0 ∧ coefficient Z cx=0 ∧ coefficient Z cy=0 := by
  exact theta_scalar_primitive φ hφ u hu0 hu Dx Dy hcx hcy hxx hyy cone_density_primitive
end SplitFElliptic

#print axioms SplitFCompanion.cone_density_primitive
#print axioms SplitFElliptic.theta_scalar_primitive_complete
