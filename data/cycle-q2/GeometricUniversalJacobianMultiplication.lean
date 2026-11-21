import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Proposal.GeometricUniversalJacobianFrames
import Proposal.GeometricUniversalJacobianTrace

set_option autoImplicit false

/-!
# Common Jacobian frames for the full sextic family

Three monomial frames and their trace-duality determinants cut out a single
principal open containing Fermat. On every field-valued fiber of this open
the upper and lower graded pieces of the actual Jacobian quotient each have
dimension 33, and its invariant degree-six tangent piece has dimension 35.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

noncomputable section
namespace CycleQ2HiggsFamilyGrading

open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation)
open CycleQ2HiggsJacobianFrames
open CycleQ2GeometricHiggsGradedIndices (upperIndex lowerIndex tangentIndex)
open CycleQ2FermatJacobian (Exp exponent)
open CycleQ2FermatHiggs (basisMonomial tangentMonomial basis_properties socle)
open CycleQ2HiggsGram (gram gram_det_seed)
open MvPolynomial

def upperExp (i : Fin 33) : Exp := exponent (basisMonomial i)

theorem upperExp_injective : Function.Injective upperExp := by
  intro i j h
  apply CycleQ2FermatHiggs.basis_injective
  funext k
  exact congrArg (fun x : Exp => x k) h

theorem upperExp_le (i : Fin 33) : upperExp i ≤ exponent socle := (basis_properties i).2.2

def frameParameter (n : ℕ) (χ : ZMod 3) : CoeffRing := frameDet n χ * gramDet n χ

def parameter : CoeffRing :=
  frameParameter 6 1 * (frameParameter 6 0 * (frameParameter 12 1 * (gram upperExp).det))

theorem parameter_seed : seedEvaluation parameter = 1 := by
  simp only [parameter, frameParameter, map_mul, seed_frameDet, gramDet_seed,
    gram_det_seed upperExp upperExp_injective upperExp_le, one_mul]

variable {K : Type} [Field K] (φ : CoeffRing →+* K)

theorem factor_conditions (h : φ parameter ≠ 0) :
    (φ (frameDet 6 1) ≠ 0 ∧ φ (gramDet 6 1) ≠ 0) ∧
    (φ (frameDet 6 0) ≠ 0 ∧ φ (gramDet 6 0) ≠ 0) ∧
    (φ (frameDet 12 1) ≠ 0 ∧ φ (gramDet 12 1) ≠ 0) ∧
    φ (gram upperExp).det ≠ 0 := by
  simpa only [parameter, frameParameter, map_mul, mul_ne_zero_iff] using h

abbrev Upper := gradedPiece φ 6 1
abbrev Lower := gradedPiece φ 12 1
abbrev Tangent := gradedPiece φ 6 0

def upperBasis (h : φ parameter ≠ 0) : Module.Basis (Fin 33) K (Upper φ) :=
  (basis φ 6 1 (isUnit_iff_ne_zero.mpr (factor_conditions φ h).1.1)
    (factor_conditions φ h).1.2).reindex upperIndex.symm

def tangentBasis (h : φ parameter ≠ 0) : Module.Basis (Fin 35) K (Tangent φ) :=
  (basis φ 6 0 (isUnit_iff_ne_zero.mpr (factor_conditions φ h).2.1.1)
    (factor_conditions φ h).2.1.2).reindex tangentIndex.symm

def lowerBasis (h : φ parameter ≠ 0) : Module.Basis (Fin 33) K (Lower φ) :=
  (basis φ 12 1 (isUnit_iff_ne_zero.mpr (factor_conditions φ h).2.2.1.1)
    (factor_conditions φ h).2.2.1.2).reindex lowerIndex.symm

theorem upperBasis_coe (h : φ parameter ≠ 0) (i : Fin 33) :
    (upperBasis φ h i : QuotientRing φ) = quotientMap φ (monomial (upperExp i) 1) := by
  simp [upperBasis, Module.Basis.reindex_apply, basis_coe, boundedClass, upperExp]

theorem tangentBasis_coe (h : φ parameter ≠ 0) (m : Fin 35) :
    (tangentBasis φ h m : QuotientRing φ) = quotientMap φ (monomial (exponent (tangentMonomial m)) 1) := by
  simp [tangentBasis, Module.Basis.reindex_apply, basis_coe, boundedClass]

theorem lowerBasis_coe (h : φ parameter ≠ 0) (i : Fin 33) :
    (lowerBasis φ h i : QuotientRing φ) = quotientMap φ
      (monomial (CycleQ2HiggsGram.complementExp (upperExp i)) 1) := by
  simp only [lowerBasis, Module.Basis.reindex_apply, Equiv.symm_symm, basis_coe,
    boundedClass, CycleQ2GeometricHiggsGradedIndices.exp_lowerIndex_eq_sub]
  rfl

theorem dimensions (h : φ parameter ≠ 0) :
    Module.finrank K (Upper φ × Lower φ) = 66 ∧ Module.finrank K (Tangent φ) = 35 := by
  let u := upperBasis φ h
  let l := lowerBasis φ h
  let t := tangentBasis φ h
  let := Module.Finite.of_basis u
  let := Module.Finite.of_basis l
  simp only [Module.finrank_prod, Module.finrank_eq_card_basis u, Module.finrank_eq_card_basis l,
    Module.finrank_eq_card_basis t, Fintype.card_fin, Nat.reduceAdd, and_self]

end CycleQ2HiggsFamilyGrading
end

#print axioms CycleQ2HiggsFamilyGrading.parameter_seed
#print axioms CycleQ2HiggsFamilyGrading.dimensions

/-!
# Trace duality and multiplication in the moving Jacobian quotient

The pairings use multiplication in the quotient by the five actual
weighted partial derivatives. The trace descends from the universal
degree-eighteen Macaulay row. The lower piece is separated by its pairing
with the upper piece on the common principal open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

noncomputable section
namespace CycleQ2HiggsFamilyGrading

open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation)
open CycleQ2IncidenceEquations (HG)
open CycleQ2HiggsJacobianFrames
open CycleQ2FermatJacobian (Exp exponent)
open CycleQ2FermatHiggs (basisMonomial tangentMonomial)
open CycleQ2HiggsSocle (H quotientTrace)
open CycleQ2HiggsGram (gram)
open MvPolynomial

variable {K : Type} [Field K] (φ : CoeffRing →+* K)

def pairing : Upper φ →ₗ[K] Lower φ →ₗ[K] K :=
  let tr : QuotientRing φ →ₗ[K] K := quotientTrace φ
  LinearMap.mk₂ K (fun x y => tr ((x : QuotientRing φ) * (y : QuotientRing φ)))
    (fun x y z => by simp [add_mul])
    (fun c x y => by simp [smul_mul_assoc])
    (fun x y z => by simp [mul_add])
    (fun c x y => by simp [mul_smul_comm])

theorem product_mem (x : Upper φ) (t : Tangent φ) :
    (x : QuotientRing φ) * (t : QuotientRing φ) ∈ Lower φ := by
  obtain ⟨p, hp, he₁⟩ := x.property
  obtain ⟨q, hq, he₂⟩ := t.property
  refine ⟨p * q, ?_, ?_⟩
  · have h := (show HG p (6,1) from hp).mul (show HG q (6,0) from hq)
    change HG (p * q) (12,1)
    exact (show ((6,1) + (6,0) : ℕ × ZMod 3) = (12,1) by decide) ▸ h
  · change (quotientMap φ) (p * q) = _
    rw [map_mul]
    exact congrArg₂ (· * ·) he₁ he₂

def higgs (t : Tangent φ) : Upper φ →ₗ[K] Lower φ where
  toFun x := ⟨(x : QuotientRing φ) * (t : QuotientRing φ), product_mem φ x t⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (smul_mul_assoc _ _ _)

theorem pairing_matrix (h : φ parameter ≠ 0) :
    LinearMap.toMatrix₂ (upperBasis φ h) (lowerBasis φ h) (pairing φ) =
      ((gram upperExp).map φ).transpose := by
  ext i j
  rw [LinearMap.toMatrix₂_apply]
  change quotientTrace φ
      ((upperBasis φ h i : QuotientRing φ) * (lowerBasis φ h j : QuotientRing φ)) =
    φ (gram upperExp j i)
  rw [upperBasis_coe, lowerBasis_coe, mul_comm, ← map_mul]
  exact (CycleQ2HiggsGram.gram_map_entry φ upperExp j i).symm

theorem pairing_flip_injective (h : φ parameter ≠ 0) : Function.Injective (pairing φ).flip := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.separatingRight_iff_flip_ker_eq_bot.mp
  apply (LinearMap.separatingRight_toMatrix₂_iff (upperBasis φ h) (lowerBasis φ h)).mp
  apply Matrix.separatingRight_iff_det_ne_zero.mpr
  rw [pairing_matrix φ h, Matrix.det_transpose]
  exact (φ.map_det (gram upperExp)) ▸ (factor_conditions φ h).2.2.2

theorem higgs_basis_entry (h : φ parameter ≠ 0) (m : Fin 35) (i j : Fin 33) :
    pairing φ (upperBasis φ h i) (higgs φ (tangentBasis φ h m) (upperBasis φ h j)) =
      φ (H m i j) := by
  change quotientTrace φ ((upperBasis φ h i : QuotientRing φ) *
    ((upperBasis φ h j : QuotientRing φ) * (tangentBasis φ h m : QuotientRing φ))) = _
  rw [upperBasis_coe, upperBasis_coe, tangentBasis_coe, ← mul_assoc, ← map_mul, ← map_mul]
  exact (CycleQ2HiggsSocle.H_quotientTrace φ m i j).symm

end CycleQ2HiggsFamilyGrading
end

#print axioms CycleQ2HiggsFamilyGrading.pairing_flip_injective
#print axioms CycleQ2HiggsFamilyGrading.higgs_basis_entry
