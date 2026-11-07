import HodgeComputer.Constructions.RationalFields.CommonDenominatorSubstitution
import Proposal.SymmetricAffineField

/-!
# Legal homogeneous clearing of the reflection chart

The inverse chart has one common homogeneous denominator `B = U*S`, with
`U = X0+X1` and `S = X0-X1`. The five numerators have degree two.
Pullback to the affine chart sends `B` to `4*v` and its numerators to
`4*v` times the five coordinates. This proves legality for an arbitrary
affine denominator relatively prime to the actual equation.
-/

noncomputable section

namespace SymmetricChartClearing

open MvPolynomial WeightedPrimitiveTransport

abbrev PhysicalPoly := MvPolynomial (Fin 6) ℂ

def U : PhysicalPoly := X 0 + X 1
def S : PhysicalPoly := X 0 - X 1
def T : PhysicalPoly := X 3 - X 4
def B : PhysicalPoly := U * S

/-- Common numerators in the order `(lambda,b,c,d,v)`. -/
def G : Fin 5 → PhysicalPoly :=
  ![U*T, 2*X 2*S, (X 3+X 4)*S, 2*X 5*S, S^2]

def affinePullback : PhysicalPoly →+* Poly :=
  eval₂Hom C ![1+X 4, 1-X 4, X 1,
    X 2+X 0*X 4, X 2-X 0*X 4, X 3]

@[simp] theorem affinePullback_C (r : ℂ) : affinePullback (C r) = C r := by
  simp [affinePullback]

theorem affinePullback_coefficients :
    affinePullback.comp (C : ℂ →+* PhysicalPoly) = (C : ℂ →+* Poly) := by
  ext r
  simp

@[simp] theorem affinePullback_U : affinePullback U = 2 := by
  simp [affinePullback, U]
  ring

@[simp] theorem affinePullback_S : affinePullback S = 2 * X 4 := by
  simp [affinePullback, S]
  ring

@[simp] theorem affinePullback_B : affinePullback B = 4 * X 4 := by
  simp [B]
  ring

@[simp] theorem affinePullback_G (i : Fin 5) :
    affinePullback (G i) = (4 * X 4) * X i := by
  fin_cases i <;> simp [G, T, affinePullback, U, S, map_ofNat] <;> ring

theorem affinePullback_equation : affinePullback HodgeSubmission.F = chartEquation := by
  rw [SymmetricReflections.exactF_compact]
  simp [affinePullback, SymmetricReflections.compactF,
    SymmetricReflections.QX, SymmetricReflections.QY, chartEquation,
    squareLift, rawWeighted, leftQuadric, rightQuadric, Fin.ext_iff,
    map_ofNat, div_eq_mul_inv]
  ring

theorem U_homogeneous : U.IsHomogeneous 1 :=
  (isHomogeneous_X ℂ 0).add (isHomogeneous_X ℂ 1)

theorem S_homogeneous : S.IsHomogeneous 1 :=
  (isHomogeneous_X ℂ 0).sub (isHomogeneous_X ℂ 1)

theorem T_homogeneous : T.IsHomogeneous 1 :=
  (isHomogeneous_X ℂ 3).sub (isHomogeneous_X ℂ 4)

theorem B_homogeneous : B.IsHomogeneous 2 := U_homogeneous.mul S_homogeneous

theorem G_homogeneous (i : Fin 5) : (G i).IsHomogeneous 2 := by
  fin_cases i
  · exact U_homogeneous.mul T_homogeneous
  · exact ((isHomogeneous_X ℂ 2).C_mul 2).mul S_homogeneous
  · exact ((isHomogeneous_X ℂ 3).add (isHomogeneous_X ℂ 4)).mul S_homogeneous
  · exact ((isHomogeneous_X ℂ 5).C_mul 2).mul S_homogeneous
  · exact S_homogeneous.pow 2

def liftPolynomial (p : Poly) (L : ℕ) : PhysicalPoly :=
  CommonDenominatorSubstitution.cleared p B G L

theorem liftPolynomial_homogeneous (p : Poly) (L : ℕ) (hp : p.totalDegree ≤ L) :
    (liftPolynomial p L).IsHomogeneous (2*L) :=
  CommonDenominatorSubstitution.cleared_homogeneous p B G L 2 hp
    B_homogeneous G_homogeneous

theorem affinePullback_liftPolynomial (p : Poly) (L : ℕ) (hp : p.totalDegree ≤ L) :
    affinePullback (liftPolynomial p L) = (4*X 4)^L * p := by
  have h := CommonDenominatorSubstitution.map_cleared p B G L hp
    affinePullback (4*X 4) X affinePullback_B affinePullback_G
  simpa only [liftPolynomial, affinePullback_coefficients, eval₂_eta] using h

theorem equation_not_dvd_four_v : ¬ chartEquation ∣ (4*X 4 : Poly) := by
  intro h
  have hmap := map_dvd (eval SymmetricAffineField.normalPoint) h
  rw [SymmetricAffineField.normalPoint_equation, zero_dvd_iff] at hmap
  have hz : (4 : ℂ)*Complex.I = 0 := by
    simpa [SymmetricAffineField.normalPoint] using hmap
  exact (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) Complex.I_ne_zero) hz

theorem not_dvd_liftPolynomial (p : Poly) (L : ℕ) (hp : p.totalDegree ≤ L)
    (hlegal : IsRelPrime chartEquation p) :
    ¬ HodgeSubmission.F ∣ liftPolynomial p L := by
  apply CommonDenominatorSubstitution.not_dvd_cleared p B G L hp
    affinePullback (4*X 4) X affinePullback_B affinePullback_G
    HodgeSubmission.F chartEquation SymmetricAffinePrime.chart_prime
  · rw [affinePullback_equation]
  · exact equation_not_dvd_four_v
  · rw [affinePullback_coefficients, eval₂_eta]
    exact SymmetricAffinePrime.chart_irreducible.isRelPrime_iff_not_dvd.mp hlegal

theorem liftPolynomial_legal (p : Poly) (L : ℕ) (hp : p.totalDegree ≤ L)
    (hlegal : IsRelPrime chartEquation p) :
    IsRelPrime HodgeSubmission.F (liftPolynomial p L) :=
  SymmetricPrime.target_irreducible.isRelPrime_iff_not_dvd.mpr
    (not_dvd_liftPolynomial p L hp hlegal)

theorem not_dvd_of_affine_point (p : PhysicalPoly)
    (hp : eval SymmetricAffineField.normalPoint (affinePullback p) ≠ 0) :
    ¬ HodgeSubmission.F ∣ p := by
  intro h
  have hmap := map_dvd ((eval SymmetricAffineField.normalPoint).comp affinePullback) h
  simp only [RingHom.comp_apply, affinePullback_equation,
    SymmetricAffineField.normalPoint_equation, zero_dvd_iff] at hmap
  exact hp hmap

theorem not_dvd_S : ¬ HodgeSubmission.F ∣ S := by
  apply not_dvd_of_affine_point
  simp [SymmetricAffineField.normalPoint, Complex.I_ne_zero]

theorem not_dvd_eight : ¬ HodgeSubmission.F ∣ (8 : PhysicalPoly) := by
  apply not_dvd_of_affine_point
  norm_num [map_ofNat]

/-- The denominator of the explicit six-component transported current. -/
def certificateDenominator (p : Poly) (L : ℕ) : PhysicalPoly :=
  8*S^2*liftPolynomial p L

theorem certificateDenominator_not_dvd (p : Poly) (L : ℕ)
    (hp : p.totalDegree ≤ L) (hlegal : IsRelPrime chartEquation p) :
    ¬ HodgeSubmission.F ∣ certificateDenominator p L := by
  apply SymmetricPrime.target_prime.not_dvd_mul
  · exact SymmetricPrime.target_prime.not_dvd_mul not_dvd_eight
      (fun h => not_dvd_S (SymmetricPrime.target_prime.dvd_of_dvd_pow h))
  · exact not_dvd_liftPolynomial p L hp hlegal

theorem certificateDenominator_legal (p : Poly) (L : ℕ)
    (hp : p.totalDegree ≤ L) (hlegal : IsRelPrime chartEquation p) :
    IsRelPrime HodgeSubmission.F (certificateDenominator p L) :=
  SymmetricPrime.target_irreducible.isRelPrime_iff_not_dvd.mpr
    (certificateDenominator_not_dvd p L hp hlegal)

theorem certificateDenominator_ne_zero (p : Poly) (L : ℕ)
    (hp : p.totalDegree ≤ L) (hlegal : IsRelPrime chartEquation p) :
    certificateDenominator p L ≠ 0 := by
  intro h
  exact certificateDenominator_not_dvd p L hp hlegal (by rw [h]; exact dvd_zero _)

theorem certificateDenominator_homogeneous (p : Poly) (L : ℕ)
    (hp : p.totalDegree ≤ L) :
    (certificateDenominator p L).IsHomogeneous (2*L+2) := by
  have h := ((S_homogeneous.pow 2).C_mul (8 : ℂ)).mul
    (liftPolynomial_homogeneous p L hp)
  simpa only [map_ofNat, Nat.mul_one, Nat.one_mul, Nat.add_comm,
    certificateDenominator] using h

#print axioms affinePullback_equation
#print axioms liftPolynomial_legal
#print axioms certificateDenominator_legal
#print axioms certificateDenominator_homogeneous

end SymmetricChartClearing
