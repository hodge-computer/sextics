import Proposal.GeometricLiteralResidueSheaf
import Proposal.GeometricLiteralResidueBasicChart

/-!
# Recovering regular three-forms from sections on the Jacobian chart

On a principal open of the Jacobian chart the four coefficients of a section
of the sheaf of three-forms give a three-form over the corresponding localized
ring. The signed tangent derivative agrees with the regular exterior
differential in both directions. In particular the prescribed boundary
equation over the localized ring is equivalent to the sheaf boundary equation
for the literal protected residue.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralResidueSheaf

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricRegularDeRham CycleQ2GeometricAffineDerivations
open CycleQ2LiteralResidueBasicChart CycleQ2AffineClearing

/-- The regular three-form specified by the coefficients of a sheaf section. -/
def readLocal (s : OpenRing) (w : additiveForms.obj.obj (op (PrimeSpectrum.basicOpen s))) :
    Form s 3 :=
  (thirdBasis s).equivFun.symm (fun i =>
    (basicSectionsEquiv s).symm ((coordinate i).val.app (op (PrimeSpectrum.basicOpen s)) w))

theorem readLocal_coord (s : OpenRing)
    (w : additiveForms.obj.obj (op (PrimeSpectrum.basicOpen s))) (i : Fin 4) :
    (thirdBasis s).repr (readLocal s w) i =
      (basicSectionsEquiv s).symm ((coordinate i).val.app (op (PrimeSpectrum.basicOpen s)) w) :=
  (thirdBasis s).coord_equivFun_symm i _

/-- A regular exterior three-form determines an actual section on its principal chart. -/
def writeLocal (s : OpenRing) (η : Form s 3) :
    additiveForms.obj.obj (op (PrimeSpectrum.basicOpen s)) :=
  sectionOfCoordinates _ (fun i => basicSectionsEquiv s ((thirdBasis s).repr η i))

theorem readLocal_writeLocal (s : OpenRing) (η : Form s 3) :
    readLocal s (writeLocal s η) = η := by
  apply (thirdBasis s).repr.injective
  ext i
  rw [readLocal_coord]
  exact (congrArg (basicSectionsEquiv s).symm
    (coordinate_sectionOfCoordinates (PrimeSpectrum.basicOpen s)
      (fun j => basicSectionsEquiv s ((thirdBasis s).repr η j)) i)).trans
    ((basicSectionsEquiv s).symm_apply_apply _)

theorem readLocal_differential (s : OpenRing) (hs : s ≠ 0)
    (w : additiveForms.obj.obj (op (PrimeSpectrum.basicOpen s))) :
    exteriorD3 s (readLocal s w) =
      (basicSectionsEquiv s).symm (topDifferential.hom.app (op (PrimeSpectrum.basicOpen s)) w) •
        volume s := by
  rw [exteriorD3_apply]
  apply congrArg (fun a : LocalRing s => a • volume s)
  let U := PrimeSpectrum.basicOpen s
  let x (i : Fin 4) : AffineSections (A := OpenRing) U := (coordinate i).val.app (op U) w
  let E := (basicSectionsEquiv s).symm
  calc
    _ = ∑ i : Fin 4, E ((-1 : ℤ) ^ i.val • sectionDerivative (tangent i) U (x i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [readLocal_coord, map_zsmul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
      exact congrArg ((-1 : LocalRing s) ^ i.val * ·)
        (basicSectionsEquiv_symm_derivative s hs i (x i)).symm
    _ = E (∑ i : Fin 4, (-1 : ℤ) ^ i.val • sectionDerivative (tangent i) U (x i)) :=
      (map_sum E _ _).symm
    _ = _ := congrArg E (topDifferential_apply U w).symm

theorem protectedSection_principal (s : OpenRing) :
    (basicSectionsEquiv s).symm (protectedSection (PrimeSpectrum.basicOpen s)) =
      residueCoefficient s affineA := by
  rw [← protectedCoefficient_local]
  exact (basicSectionsEquiv s).symm_apply_eq.mpr
    (basicSectionsEquiv_algebraMap s protectedCoefficient).symm

/-- The volume basis vector detects its scalar coefficient, over every localization. -/
theorem volume_smul_injective (s : OpenRing) :
    Function.Injective (fun a : LocalRing s => a • volume s) := by
  intro a b h
  let B := (coordinateBasis s).exteriorPower 4
  have hc := congrArg (B.coord CycleQ2AffineExterior.topIndex) h
  simpa [B, volume, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.smul_apply] using hc

/-- For the protected numerator the actual sheaf and regular boundary
equations on a principal open are equivalent. -/
theorem principal_exact_iff (s : OpenRing) (hs : s ≠ 0) :
    (∃ w : additiveForms.obj.obj (op (PrimeSpectrum.basicOpen s)),
      topDifferential.hom.app _ w = protectedSection _) ↔
      ∃ η : Form s 3, exteriorD3 s η = residueSourceForm s affineA := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨readLocal s w, by rw [readLocal_differential s hs, hw,
      protectedSection_principal, residueSourceForm]⟩
  · rintro ⟨η, hη⟩
    refine ⟨writeLocal s η, (basicSectionsEquiv s).symm.injective ?_⟩
    apply volume_smul_injective s
    calc
      _ = exteriorD3 s (readLocal s (writeLocal s η)) :=
        (readLocal_differential s hs (writeLocal s η)).symm
      _ = exteriorD3 s η := congrArg (exteriorD3 s) (readLocal_writeLocal s η)
      _ = residueSourceForm s affineA := hη
      _ = _ := congrArg (fun a : LocalRing s => a • volume s) (protectedSection_principal s).symm

end CycleQ2LiteralResidueSheaf
end

#print axioms CycleQ2LiteralResidueSheaf.readLocal_differential
#print axioms CycleQ2LiteralResidueSheaf.principal_exact_iff
