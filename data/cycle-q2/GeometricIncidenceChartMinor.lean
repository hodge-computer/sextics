import Proposal.GeometricIncidenceDehomogenizedChart
import Proposal.GeometricIncidenceRelativeJacobian
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finsupp.Weight

/-!
# Normalizing the original Jacobian minors on the actual projective charts

Status: source-only proof draft. No elaboration or kernel replay was run.

The original F,h Jacobian determinant is weighted homogeneous of degree
9 - weight(j) - weight(k). The actual shifted chart is an S-algebra
retract of its coordinate localization. Under its section, the
dehomogenized determinant is the original cone determinant multiplied
by the corresponding inverse power of the weight-one coordinate.

These are identities of the existing rings and coefficient maps. No
smoothness, finite presentation, flatness, or shrinking theorem is
assumed or asserted in this component.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2IncidenceChartMinor

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceDehomogenizedChart

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- A derivative lowers weighted degree by the weight of its geometric
coordinate. Zero derivatives satisfy the same homogeneous statement. -/
theorem pderiv_homogeneous {p : MvPolynomial (Fin 5) S} {n : ℕ}
    (hp : p.IsWeightedHomogeneous geometricWeight n) (j : Fin 5) :
    (pderiv j p).IsWeightedHomogeneous geometricWeight (n - geometricWeight j) := by
  intro e he
  rw [MvPolynomial.coeff_pderiv] at he
  have hc : coeff (e + Finsupp.single j 1) p ≠ 0 := by
    intro hz
    exact he (by rw [hz, zero_mul])
  have hd := hp hc
  simp only [map_add, Finsupp.weight_single, one_smul] at hd
  omega

theorem geometricWeight_le_two (j : Fin 5) : geometricWeight j ≤ 2 := by
  fin_cases j <;> decide

def minorDegree (j k : Fin 5) : ℕ :=
  9 - geometricWeight j - geometricWeight k

/-- The same ordered F,h determinant used by the relative Jacobian
presentation, at arbitrary coefficients y. -/
def surfaceMinor (y : ParameterIndex → S) (j k : Fin 5) : MvPolynomial (Fin 5) S :=
  CycleQ2RelativeJacobianPatch.equationMinor
    (CycleQ2IncidenceDehomogenizedChart.equations y) ![j, k]

theorem surfaceMinor_eq (y : ParameterIndex → S) (j k : Fin 5) :
    surfaceMinor y j k =
      pderiv j (pointEquationF y) * pderiv k (pointEquationH y) -
        pderiv k (pointEquationF y) * pderiv j (pointEquationH y) := rfl

theorem surfaceMinor_homogeneous (y : ParameterIndex → S) (j k : Fin 5) :
    (surfaceMinor y j k).IsWeightedHomogeneous geometricWeight (minorDegree j k) := by
  have hF : (pointEquationF y).IsWeightedHomogeneous geometricWeight 6 :=
    pointEquationF_homogeneous y
  have hH : (pointEquationH y).IsWeightedHomogeneous geometricWeight 3 :=
    pointEquationH_homogeneous y
  have hj := geometricWeight_le_two j
  have hk := geometricWeight_le_two k
  have hleftDegree :
      (6 - geometricWeight j) + (3 - geometricWeight k) = minorDegree j k := by
    unfold minorDegree
    omega
  have hrightDegree :
      (6 - geometricWeight k) + (3 - geometricWeight j) = minorDegree j k := by
    unfold minorDegree
    omega
  have hleft := (pderiv_homogeneous hF j).mul (pderiv_homogeneous hH k)
  have hright := (pderiv_homogeneous hF k).mul (pderiv_homogeneous hH j)
  rw [hleftDegree] at hleft
  rw [hrightDegree] at hright
  rw [surfaceMinor_eq]
  exact hleft.sub hright

/-! ## The actual chart as a split algebra retract -/

def coordinateInclusionAlgHom (y : ParameterIndex → S) (i : Fin 4) :
    CoordinateRing y i →ₐ[S] CoordinateLocalization y i where
  toRingHom := algebraMap (CoordinateRing y i) (CoordinateLocalization y i)
  commutes' c := by
    rw [coordinate_algebraMap]
    change (constants y i c).val = algebraMap S (CoordinateLocalization y i) c
    rw [constants_val,
      IsScalarTower.algebraMap_apply S (PointSurface y) (CoordinateLocalization y i)]
    rfl

def surfaceToDehomogenizedAlgHom (y : ParameterIndex → S) (i : Fin 4) :
    PointSurface y →ₐ[S] DehomogenizedRing y i where
  toRingHom := surfaceToDehomogenized y i
  commutes' c := by
    change surfaceToDehomogenized y i (surfaceQuotient y (C c)) =
      dehomogenizedMap y i (C c)
    rw [surfaceToDehomogenized_surfaceQuotient]
    exact congrArg (dehomogenizedMap y i) ((dehomogenize i).commutes c)

/-- The existing dehomogenization sets the inverted coordinate to one,
so it extends to the actual coordinate localization. -/
def dehomogenizedRetraction (y : ParameterIndex → S) (i : Fin 4) :
    CoordinateLocalization y i →ₐ[S] DehomogenizedRing y i :=
  IsLocalization.Away.liftAlgHom
    (S := CoordinateLocalization y i)
    (f := surfaceToDehomogenizedAlgHom y i)
    (surfaceQuotient y (X i.castSucc)) (by
      change IsUnit (surfaceToDehomogenized y i (surfaceQuotient y (X i.castSucc)))
      rw [surfaceToDehomogenized_self]
      exact isUnit_one)

/-- The section uses the already constructed inverse of the actual
degree-zero chart equivalence and its inclusion in the cone localization. -/
def dehomogenizedSection (y : ParameterIndex → S) (i : Fin 4) :
    DehomogenizedRing y i →ₐ[S] CoordinateLocalization y i :=
  (coordinateInclusionAlgHom y i).comp (familyCoordinateChartEquiv y i).symm.toAlgHom

theorem dehomogenizedRetraction_section (y : ParameterIndex → S) (i : Fin 4)
    (x : DehomogenizedRing y i) :
    dehomogenizedRetraction y i (dehomogenizedSection y i x) = x := by
  exact toDehomogenized_fromDehomogenized y i x

/-- Homogeneous numerators are divided by exactly the corresponding
power of Xi under the actual S-algebra section. -/
theorem dehomogenizedSection_homogeneous (y : ParameterIndex → S) (i : Fin 4)
    (n : ℕ) (p : MvPolynomial (Fin 5) S)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    dehomogenizedSection y i (dehomogenizedMap y i (dehomogenize i p)) =
      algebraMap (PointSurface y) (CoordinateLocalization y i) (surfaceQuotient y p) *
        IsLocalization.Away.invSelf (surfaceQuotient y (X i.castSucc)) ^ n := by
  change ((familyCoordinateChartEquiv y i).symm
    (dehomogenizedMap y i (dehomogenize i p))).val = _
  rw [← familyCoordinateChartEquiv_homogeneousFraction y i n p hp,
    AlgEquiv.symm_apply_apply]
  exact homogeneousFraction_val y i n p hp

def normalizedMinor (y : ParameterIndex → S) (i : Fin 4) (j k : Fin 5) :
    DehomogenizedRing y i :=
  dehomogenizedMap y i (dehomogenize i (surfaceMinor y j k))

/-- The normalization factor is an inverse power of the chosen
weight-one coordinate. No derivative of a moving coefficient occurs. -/
theorem dehomogenizedSection_normalizedMinor (y : ParameterIndex → S)
    (i : Fin 4) (j k : Fin 5) :
    dehomogenizedSection y i (normalizedMinor y i j k) =
      algebraMap (PointSurface y) (CoordinateLocalization y i)
          (surfaceQuotient y (surfaceMinor y j k)) *
        IsLocalization.Away.invSelf (surfaceQuotient y (X i.castSucc)) ^ minorDegree j k :=
  dehomogenizedSection_homogeneous y i (minorDegree j k)
    (surfaceMinor y j k) (surfaceMinor_homogeneous y j k)

end CycleQ2IncidenceChartMinor

end

#print axioms CycleQ2IncidenceChartMinor.surfaceMinor_homogeneous
#print axioms CycleQ2IncidenceChartMinor.dehomogenizedRetraction_section
#print axioms CycleQ2IncidenceChartMinor.dehomogenizedSection_normalizedMinor

