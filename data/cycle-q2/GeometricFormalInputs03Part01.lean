import Proposal.Workspace
import HodgeTarget
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Equiv
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import HodgeComputer.CertificateOperations
import HodgeComputer.Verify
import HodgeComputer.Constructions.RationalFields.Calculus
import HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Isomorphisms
import Proposal.GeometricSeed
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import HodgeComputer.Constructions.HigherResidues.HigherResidue
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.RationalFields.Homogenization
import HodgeComputer.Constructions.RationalFields.CommonDenominatorSubstitution
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FreeModule.Basic
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting
import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import Mathlib.RingTheory.Smooth.AdicCompletion
import Proposal.GeometricFormalInputs02Part04

/-! Source partition of GeometricFormalInputs.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: euler_lift/AffineChart.lean -/
section
/-!
# The actual projective chart over the complex rational-function fields

This adapts the injective chart and chain-rule proofs in benediamond's
accepted two-ternary dense Hessian construction, retaining their mathematical
credit. The protected coordinates are unchanged; the chart sets X0=1.
Its fraction-field map is constructed and proved injective, not assumed.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2AffineChart

open MvPolynomial HodgeComputer CycleQ2Bridge HodgeTestbed.Conic
open scoped BigOperators

local instance (n : ℕ) : Algebra ℚ (RationalFunction n) := DivisionRing.toRatAlgebra
local instance (n : ℕ) : Module ℚ (RationalFunction n) := Algebra.toModule

def embed {n : ℕ} : AmbientPoly n →ₐ[ℂ] RationalFunction n :=
  IsScalarTower.toAlgHom ℂ (AmbientPoly n) (RationalFunction n)

abbrev coord {n : ℕ} (i : Fin (n + 1)) : RationalFunction n := polynomialMap n (X i)

theorem coord_ne_zero {n : ℕ} (i : Fin (n + 1)) : coord i ≠ 0 :=
  polynomialMap_ne_zero (X_ne_zero i)

@[simp] theorem partial_coord {n : ℕ} (i j : Fin (n + 1)) :
    rationalPartial n i (coord j) = if i = j then 1 else 0 := by
  simp [coord, rationalPartial_map, pderiv_X, Pi.single_apply, eq_comm]

def dehomogenize : AmbientPoly 5 →ₐ[ℂ] AmbientPoly 4 := aeval (Fin.cases 1 X)

abbrev ChartRing := Localization.Away (X (0 : Fin 6) : AmbientPoly 5)

def awayEmbed : AmbientPoly 5 →ₐ[ℂ] ChartRing :=
  IsScalarTower.toAlgHom ℂ (AmbientPoly 5) ChartRing

def awayEval : ChartRing →ₐ[ℂ] AmbientPoly 4 :=
  IsLocalization.Away.liftAlgHom (X (0 : Fin 6)) (f := dehomogenize) (by
    have hx : dehomogenize (X (0 : Fin 6)) = 1 := aeval_X _ _
    rw [hx]
    exact isUnit_one)

def awayFrac : ChartRing →ₐ[ℂ] RationalFunction 5 :=
  IsLocalization.Away.liftAlgHom (X (0 : Fin 6)) (f := embed)
    (isUnit_iff_ne_zero.mpr (coord_ne_zero 0))

@[simp] theorem awayEval_embed (P : AmbientPoly 5) :
    awayEval (awayEmbed P) = dehomogenize P := IsLocalization.lift_eq _ P

@[simp] theorem awayFrac_embed (P : AmbientPoly 5) :
    awayFrac (awayEmbed P) = polynomialMap 5 P := IsLocalization.lift_eq _ P

def inverseScale : ChartRing :=
  IsLocalization.Away.invSelf (S := ChartRing) (X (0 : Fin 6) : AmbientPoly 5)

theorem scale_mul_inverseScale : awayEmbed (X (0 : Fin 6)) * inverseScale = 1 :=
  IsLocalization.Away.mul_invSelf (S := ChartRing) (X (0 : Fin 6) : AmbientPoly 5)

@[simp] theorem awayEval_inverseScale : awayEval inverseScale = 1 := by
  have h := congrArg awayEval scale_mul_inverseScale
  have hx : dehomogenize (X (0 : Fin 6)) = 1 := aeval_X _ _
  simpa only [map_mul, awayEval_embed, hx, one_mul, map_one] using h

@[simp] theorem awayFrac_inverseScale : awayFrac inverseScale = (coord (0 : Fin 6))⁻¹ := by
  have h := congrArg awayFrac scale_mul_inverseScale
  apply mul_left_cancel₀ (coord_ne_zero (0 : Fin 6))
  rw [mul_inv_cancel₀ (coord_ne_zero (0 : Fin 6))]
  simpa only [coord, map_mul, awayFrac_embed, map_one] using h

theorem awayFrac_injective : Function.Injective awayFrac := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers (X (0 : Fin 6) : AmbientPoly 5)) ChartRing awayFrac.toRingHom
  intro P hP
  change awayFrac (awayEmbed P) = 0 at hP
  rw [awayFrac_embed] at hP
  have hz : P = 0 := polynomialMap_injective (by simpa only [map_zero] using hP)
  simp [hz]

def awayChart : AmbientPoly 4 →ₐ[ℂ] ChartRing :=
  aeval (fun i : Fin 5 => awayEmbed (X i.succ) * inverseScale)

theorem awayChart_leftInverse : awayEval.comp awayChart = AlgHom.id ℂ (AmbientPoly 4) := by
  ext1 i
  change awayEval (awayChart (X i)) = X i
  have hc : awayChart (X i) = awayEmbed (X i.succ) * inverseScale := aeval_X _ _
  have hd : dehomogenize (X i.succ) = X i := aeval_X _ _
  rw [hc, map_mul, awayEval_embed, hd, awayEval_inverseScale, mul_one]

def chartPoly : AmbientPoly 4 →ₐ[ℂ] RationalFunction 5 := awayFrac.comp awayChart

theorem chartPoly_injective : Function.Injective chartPoly := by
  apply awayFrac_injective.comp
  intro P Q h
  have hh := congrArg awayEval h
  have hp := AlgHom.congr_fun awayChart_leftInverse P
  have hq := AlgHom.congr_fun awayChart_leftInverse Q
  exact hp.symm.trans (hh.trans hq)

def chart : RationalFunction 4 →ₐ[ℂ] RationalFunction 5 :=
  IsFractionRing.liftAlgHom (g := chartPoly) chartPoly_injective

@[simp] theorem chart_embed (P : AmbientPoly 4) :
    chart (polynomialMap 4 P) = chartPoly P := IsLocalization.lift_eq _ P

@[simp] theorem chart_coord (i : Fin 5) :
    chart (coord i) = coord i.succ / coord (0 : Fin 6) := by
  rw [coord, chart_embed]
  change awayFrac (awayChart (X i)) = _
  have hc : awayChart (X i) = awayEmbed (X i.succ) * inverseScale := aeval_X _ _
  rw [hc, map_mul, awayFrac_embed, awayFrac_inverseScale]
  rfl

@[simp] theorem chart_constant (c : ℂ) :
    chart (polynomialMap 4 (C c)) = polynomialMap 5 (C c) := by
  exact chart.commutes c

theorem compatibility_of_coordinates
    (D : Derivation ℚ (RationalFunction 5) (RationalFunction 5))
    (E : Derivation ℚ (RationalFunction 4) (RationalFunction 4))
    (c : RationalFunction 5)
    (hD : ∀ a : ℂ, D (polynomialMap 5 (C a)) = 0)
    (hE : ∀ a : ℂ, E (polynomialMap 4 (C a)) = 0)
    (hcoord : ∀ j : Fin 5, D (chart (coord j)) = c * chart (E (coord j)))
    (z : RationalFunction 4) : D (chart z) = c * chart (E z) := by
  have hp (P : AmbientPoly 4) :
      D (chart (polynomialMap 4 P)) = c * chart (E (polynomialMap 4 P)) := by
    induction P using MvPolynomial.induction_on with
    | C a => simp only [chart_constant, hD, hE, map_zero, mul_zero]
    | add P Q hP hQ => simp only [map_add, hP, hQ]; ring
    | mul_X P j hP =>
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add]
      rw [hP, show D (chart (polynomialMap 4 (X j))) =
        c * chart (E (polynomialMap 4 (X j))) from hcoord j]
      ring
  obtain ⟨P, Q, _, rfl⟩ := IsFractionRing.div_surjective (AmbientPoly 4) z
  change D (chart (polynomialMap 4 P / polynomialMap 4 Q)) =
    c * chart (E (polynomialMap 4 P / polynomialMap 4 Q))
  simp only [div_eq_mul_inv, map_mul, map_inv₀, Derivation.leibniz,
    Derivation.leibniz_inv, smul_eq_mul, hp, map_neg, map_add, map_pow]
  ring

theorem affineEuler_coord (j : Fin 5) :
    fieldAction (rationalPartial 4) coord (coord j) = coord j := by
  simp [fieldAction_apply, Pi.single_apply]

theorem chart_zero (z : RationalFunction 4) :
    rationalPartial 5 0 (chart z) = -(coord (0 : Fin 6))⁻¹ *
      chart (fieldAction (rationalPartial 4) coord z) := by
  apply compatibility_of_coordinates (rationalPartial 5 0)
    (fieldAction (rationalPartial 4) coord) (-(coord (0 : Fin 6))⁻¹)
  · intro a
    simp only [rationalPartial_map, pderiv_C, map_zero]
  · intro a
    simp only [fieldAction_apply, rationalPartial_map, pderiv_C, map_zero,
      mul_zero, Finset.sum_const_zero]
  · intro j
    rw [affineEuler_coord, chart_coord]
    have hj0 : (0 : Fin 6) ≠ j.succ := Ne.symm (Fin.succ_ne_zero j)
    simp [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      partial_coord, smul_eq_mul, hj0]
    ring

theorem chart_succ (i : Fin 5) (z : RationalFunction 4) :
    rationalPartial 5 i.succ (chart z) =
      (coord (0 : Fin 6))⁻¹ * chart (rationalPartial 4 i z) := by
  apply compatibility_of_coordinates (rationalPartial 5 i.succ)
    (rationalPartial 4 i) ((coord (0 : Fin 6))⁻¹)
  · intro a
    simp only [rationalPartial_map, pderiv_C, map_zero]
  · intro a
    simp only [rationalPartial_map, pderiv_C, map_zero]
  · intro j
    rw [chart_coord, partial_coord]
    simp only [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      partial_coord, smul_eq_mul]
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij, Fin.succ_inj]

theorem actual_homogeneousChart :
    HomogeneousChart (rationalPartial 4) (rationalPartial 5)
      chart.toRingHom (coord 0) coord where
  a_ne_zero := coord_ne_zero 0
  a_zero := by simp
  a_succ := by intro i; simp
  map_zero := chart_zero
  map_succ := chart_succ
  coordinate_diagonal := by intro i; simp

end CycleQ2AffineChart

#print axioms CycleQ2AffineChart.actual_homogeneousChart
end
end


/- Component: euler_lift/AffineHomogeneousClearing.lean -/
section
/-!
# Homogeneous clearing on the actual X0 affine chart

The clearing polynomial is the repository's proved bounded substitution.
Applying dehomogenization proves legality before taking fractions. Every
finite family of F-regular affine coefficients has a legal homogeneous
common denominator, with the exact numerator degree obtained by X0^7.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2AffineClearing

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity CycleQ2AffineChart
open scoped BigOperators

local instance (n : ℕ) : Algebra ℚ (RationalFunction n) := DivisionRing.toRatAlgebra
local instance (n : ℕ) : Module ℚ (RationalFunction n) := Algebra.toModule

def homogenize (P : AmbientPoly 4) (d : ℕ) : AmbientPoly 5 :=
  CommonDenominatorSubstitution.cleared P (X 0) (fun i : Fin 5 => X i.succ) d

theorem homogenize_homogeneous (P : AmbientPoly 4) (d : ℕ) (hP : P.totalDegree ≤ d) :
    (homogenize P d).IsHomogeneous d := by
  simpa only [homogenize, one_mul] using CommonDenominatorSubstitution.cleared_homogeneous
    P (X 0) (fun i : Fin 5 => X i.succ) d 1 hP
    (isHomogeneous_X ℂ 0) (fun i => isHomogeneous_X ℂ i.succ)

theorem dehomogenize_homogenize (P : AmbientPoly 4) (d : ℕ) (hP : P.totalDegree ≤ d) :
    dehomogenize (homogenize P d) = P := by
  have h := CommonDenominatorSubstitution.map_cleared P (X 0)
    (fun i : Fin 5 => X i.succ) d hP dehomogenize.toRingHom 1 X
    (aeval_X _ _) (fun i => by simp [dehomogenize])
  have hc : dehomogenize.toRingHom.comp C = C := by ext c; simp [dehomogenize]
  simp only [AlgHom.toRingHom_eq_coe] at hc
  simpa only [homogenize, hc, one_pow, one_mul, eval₂_eta,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

theorem homogenize_ne_zero {P : AmbientPoly 4} {d : ℕ}
    (hP : P.totalDegree ≤ d) (hP0 : P ≠ 0) : homogenize P d ≠ 0 := by
  intro h
  have hh := congrArg dehomogenize h
  rw [dehomogenize_homogenize P d hP, map_zero] at hh
  exact hP0 hh

theorem homogenize_chart (P : AmbientPoly 4) (d : ℕ) (hP : P.totalDegree ≤ d) :
    polynomialMap 5 (homogenize P d) =
      (coord (0 : Fin 6))^d * chart (polynomialMap 4 P) := by
  have h := CommonDenominatorSubstitution.map_cleared_fraction P (X 0)
    (fun i : Fin 5 => X i.succ) d hP (polynomialMap 5) (coord_ne_zero 0)
  have hm : eval₂Hom ((polynomialMap 5).comp C)
      (fun i : Fin 5 => coord i.succ / coord (0 : Fin 6)) =
      chart.toRingHom.comp (polynomialMap 4) := by
    ext c
    · simpa only [eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom] using (chart_constant c).symm
    · simpa only [eval₂Hom_X', RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom] using (chart_coord c).symm
  simpa only [homogenize, coord, ← coe_eval₂Hom, hm, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

theorem cleared_self_of_homogeneous {P : AmbientPoly 5} {d : ℕ}
    (hP : P.IsHomogeneous d) (B : AmbientPoly 5) :
    CommonDenominatorSubstitution.cleared P B X d = P := by
  classical
  conv_rhs => rw [P.as_sum]
  rw [CommonDenominatorSubstitution.cleared]
  apply Finset.sum_congr rfl
  intro a ha
  have hdegree : a.sum (fun _ e => e) = d := by
    change a.degree = d
    exact_mod_cast Homogeneous.of_isHomogeneous hP (mem_support_iff.mp ha)
  rw [hdegree, Nat.sub_self, pow_zero, mul_one, monomial_eq]
  rfl

/-- A homogeneous polynomial is recovered from its chart with its exact
degree; the proof uses actual bounded polynomial substitution. -/
theorem homogeneous_chart {P : AmbientPoly 5} {d : ℕ} (hP : P.IsHomogeneous d) :
    polynomialMap 5 P = (coord (0 : Fin 6))^d * chart
      (polynomialMap 4 (dehomogenize P)) := by
  have h := CommonDenominatorSubstitution.map_cleared_fraction P (X 0) X
    d hP.totalDegree_le (polynomialMap 5) (coord_ne_zero 0)
  rw [cleared_self_of_homogeneous hP (X 0)] at h
  have hm : eval₂Hom ((polynomialMap 5).comp C)
      (fun i : Fin 6 => coord i / coord (0 : Fin 6)) =
      (chart.toRingHom.comp (polynomialMap 4)).comp dehomogenize.toRingHom := by
    ext c
    · simpa [dehomogenize] using (chart_constant c).symm
    · refine Fin.cases ?_ (fun j => ?_) c
      · simp [dehomogenize, coord_ne_zero 0]
      · simp only [eval₂Hom_X', RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
          AlgHom.coe_toRingHom]
        have hj : dehomogenize (X j.succ) = X j := aeval_X _ _
        rw [hj]
        exact (chart_coord j).symm
  simpa only [coord, ← coe_eval₂Hom, hm, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h

def affineF : AmbientPoly 4 := dehomogenize HodgeSubmission.F
def affineA : AmbientPoly 4 := dehomogenize HodgeSubmission.A

theorem protected_F_chart : polynomialMap 5 HodgeSubmission.F =
    (coord (0 : Fin 6))^6 * chart (polynomialMap 4 affineF) :=
  homogeneous_chart CycleQ2Workspace.originalF_homogeneous

theorem protected_A_chart : polynomialMap 5 HodgeSubmission.A =
    (coord (0 : Fin 6))^12 * chart (polynomialMap 4 affineA) :=
  homogeneous_chart CycleQ2Workspace.originalA_homogeneous

theorem affineF_ne_zero : affineF ≠ 0 := by
  intro h
  have hf := protected_F_chart
  rw [h, map_zero, map_zero, mul_zero] at hf
  exact polynomialMap_ne_zero CycleQ2Workspace.originalF_ne_zero hf

theorem affineF_not_isUnit : ¬ IsUnit affineF := by
  intro h
  let ev : AmbientPoly 4 →+* ℂ := eval₂Hom (RingHom.id ℂ)
    ![0, 0, Complex.I, 0, 0]
  have he : ev affineF = 0 := by
    have h1 : Fin.cases (1 : AmbientPoly 4) X (1 : Fin 6) = X (0 : Fin 5) := rfl
    have h2 : Fin.cases (1 : AmbientPoly 4) X (2 : Fin 6) = X (1 : Fin 5) := rfl
    have h3 : Fin.cases (1 : AmbientPoly 4) X (3 : Fin 6) = X (2 : Fin 5) := rfl
    have h4 : Fin.cases (1 : AmbientPoly 4) X (4 : Fin 6) = X (3 : Fin 5) := rfl
    have h5 : Fin.cases (1 : AmbientPoly 4) X (5 : Fin 6) = X (4 : Fin 5) := rfl
    norm_num [ev, affineF, dehomogenize, HodgeSubmission.F,
      Complex.I_sq, h1, h2, h3, h4, h5]
    dsimp
    norm_num [pow_succ, Complex.I_sq]
  have hu := h.map ev
  rw [he] at hu
  exact not_isUnit_zero hu

theorem homogenize_legal {P : AmbientPoly 4} {d : ℕ}
    (hP : P.totalDegree ≤ d) (hlegal : IsRelPrime affineF P) :
    IsRelPrime HodgeSubmission.F (homogenize P d) := by
  apply CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
  intro h
  have hd := map_dvd dehomogenize.toRingHom h
  change affineF ∣ dehomogenize (homogenize P d) at hd
  rw [dehomogenize_homogenize P d hP] at hd
  exact affineF_not_isUnit (hlegal.isUnit_of_dvd hd)

theorem regular_chart {z : RationalFunction 4} (hz : RegularAlong affineF z) :
    RegularAlong HodgeSubmission.F (chart z) := by
  obtain ⟨P, T, hT, hFT, rfl⟩ := hz
  let d := max P.totalDegree T.totalDegree
  have hp : P.totalDegree ≤ d := le_max_left _ _
  have ht : T.totalDegree ≤ d := le_max_right _ _
  refine ⟨homogenize P d, homogenize T d, homogenize_ne_zero ht hT,
    homogenize_legal ht hFT, ?_⟩
  rw [map_div₀, homogenize_chart P d hp, homogenize_chart T d ht]
  have hscale : coord (0 : Fin 6) ≠ 0 := coord_ne_zero 0
  field_simp

end CycleQ2AffineClearing

#print axioms CycleQ2AffineClearing.regular_chart
end
end


/- Component: euler_lift/AffineHypersurfaceGeometry.lean -/
section
/-! Exact algebraic geometry of the protected X0=1 chart. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2AffineGeometry

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2AffineChart CycleQ2AffineClearing
open scoped BigOperators

theorem protected_coordinate_legal : IsRelPrime HodgeSubmission.F (X (0 : Fin 6)) :=
  CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
    (CycleQ2SupportEquation.not_dvd_coordinate_of_degree_gt_one HodgeSubmission.F
      (by rw [CycleQ2Workspace.originalF_totalDegree]; norm_num) 0)

theorem homogenize_dvd_iff (P : AmbientPoly 4) (d : ℕ) (hP : P.totalDegree ≤ d) :
    HodgeSubmission.F ∣ homogenize P d ↔ affineF ∣ P := by
  constructor
  · intro h
    have hd := map_dvd dehomogenize.toRingHom h
    change affineF ∣ dehomogenize (homogenize P d) at hd
    simpa only [dehomogenize_homogenize P d hP] using hd
  · rintro ⟨R, hR⟩
    have heq : X (0 : Fin 6)^(6 + R.totalDegree) * homogenize P d =
        HodgeSubmission.F * (X (0 : Fin 6)^d * homogenize R R.totalDegree) := by
      apply polynomialMap_injective (n := 5)
      simp only [map_mul, map_pow]
      rw [homogenize_chart P d hP, homogenize_chart R R.totalDegree le_rfl,
        protected_F_chart, hR, map_mul, map_mul, pow_add]
      ring
    have hd : HodgeSubmission.F ∣ X (0 : Fin 6)^(6 + R.totalDegree) * homogenize P d :=
      ⟨X (0 : Fin 6)^d * homogenize R R.totalDegree, heq⟩
    exact protected_coordinate_legal.pow_right.dvd_of_dvd_mul_left hd

theorem homogenize_mul (P Q : AmbientPoly 4) (d e : ℕ)
    (hP : P.totalDegree ≤ d) (hQ : Q.totalDegree ≤ e) :
    homogenize (P * Q) (d + e) = homogenize P d * homogenize Q e := by
  have hpq : (P * Q).totalDegree ≤ d + e :=
    (totalDegree_mul P Q).trans (Nat.add_le_add hP hQ)
  apply polynomialMap_injective (n := 5)
  rw [map_mul, homogenize_chart (P * Q) (d + e) hpq,
    homogenize_chart P d hP, homogenize_chart Q e hQ, map_mul, map_mul, pow_add]
  ring

theorem affineF_prime : Prime affineF := by
  refine ⟨affineF_ne_zero, affineF_not_isUnit, ?_⟩
  intro P Q h
  have hdegree : (P * Q).totalDegree ≤ P.totalDegree + Q.totalDegree := totalDegree_mul P Q
  have hh := (homogenize_dvd_iff (P * Q) (P.totalDegree + Q.totalDegree) hdegree).mpr h
  rw [homogenize_mul P Q P.totalDegree Q.totalDegree le_rfl le_rfl] at hh
  rcases CycleQ2ExactIrreducible.protected_F_irreducible.prime.dvd_or_dvd hh with hp | hq
  · exact Or.inl ((homogenize_dvd_iff P P.totalDegree le_rfl).mp hp)
  · exact Or.inr ((homogenize_dvd_iff Q Q.totalDegree le_rfl).mp hq)

theorem affineF_irreducible : Irreducible affineF := affineF_prime.irreducible

theorem affineF_formula : affineF =
    1 + X 0^6 + X 1^6 + X 2^6 + X 3^6 + X 4^6 +
      C (1 / 2 : ℂ) * (X 0 * X 2 * X 3 + X 0^3 * X 1 * X 3 * X 4 +
        X 1^3 * X 4 * X 2) := by
  have h1 : Fin.cases (1 : AmbientPoly 4) X (1 : Fin 6) = X (0 : Fin 5) := rfl
  have h2 : Fin.cases (1 : AmbientPoly 4) X (2 : Fin 6) = X (1 : Fin 5) := rfl
  have h3 : Fin.cases (1 : AmbientPoly 4) X (3 : Fin 6) = X (2 : Fin 5) := rfl
  have h4 : Fin.cases (1 : AmbientPoly 4) X (4 : Fin 6) = X (3 : Fin 5) := rfl
  have h5 : Fin.cases (1 : AmbientPoly 4) X (5 : Fin 6) = X (4 : Fin 5) := rfl
  norm_num [affineF, dehomogenize, HodgeSubmission.F, h1, h2, h3, h4, h5]
  ring

def testPoint : AmbientPoly 4 →+* ℂ :=
  eval₂Hom (RingHom.id ℂ) ![Complex.I, 0, 0, 0, 0]

theorem testPoint_F : testPoint affineF = 0 := by
  rw [affineF_formula]
  norm_num [testPoint, pow_succ, Complex.I_sq]
  dsimp
  ring

theorem testPoint_normal : testPoint (pderiv (0 : Fin 5) affineF) = 6 * Complex.I := by
  rw [affineF_formula]
  norm_num [testPoint, Pi.single_apply, Fin.ext_iff, pow_succ, Complex.I_sq]
  dsimp
  ring_nf
  norm_num [Complex.I_sq]
  have hI5 : Complex.I^5 = Complex.I := by
    calc
      Complex.I^5 = (Complex.I^2)^2 * Complex.I := by ring
      _ = Complex.I := by norm_num [Complex.I_sq]
  rw [hI5]
  ring

theorem affineF_not_dvd_normal : ¬ affineF ∣ pderiv (0 : Fin 5) affineF := by
  intro h
  have hh := map_dvd testPoint h
  rw [testPoint_F, testPoint_normal] at hh
  exact (mul_ne_zero (by norm_num : (6 : ℂ) ≠ 0) Complex.I_ne_zero)
    (zero_dvd_iff.mp hh)

theorem affine_normal_ne_zero : pderiv (0 : Fin 5) affineF ≠ 0 := by
  intro h
  apply affineF_not_dvd_normal
  rw [h]
  exact dvd_zero _

theorem affine_normal_legal : IsRelPrime affineF (pderiv (0 : Fin 5) affineF) :=
  affineF_irreducible.isRelPrime_iff_not_dvd.mpr affineF_not_dvd_normal

end CycleQ2AffineGeometry

#print axioms CycleQ2AffineGeometry.affineF_irreducible
#print axioms CycleQ2AffineGeometry.affine_normal_legal
end
end


/- Component: euler_lift/AffineCertificate.lean -/
section
/-!
# A regular affine primitive gives the exact protected certificate

This completes homogeneous clearing and the projective chart transfer with
actual fraction-field maps and proved chain rules. Numerators have degree
degree(D)+7, and the complete quotient is retained. The input is an actual
affine rational vector satisfying the residue equation; its existence is
not postulated or inferred merely from homogeneity or Hodge type.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2AffineCertificate

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open CycleQ2AffineChart CycleQ2AffineClearing HodgeTestbed.Conic
open scoped BigOperators

local instance (n : ℕ) : Algebra ℚ (RationalFunction n) := DivisionRing.toRatAlgebra
local instance (n : ℕ) : Module ℚ (RationalFunction n) := Algebra.toModule

theorem regular_common_denominator {n : ℕ} {ι : Type*} [Fintype ι]
    (F : AmbientPoly n) (v : ι → RationalFunction n)
    (hv : ∀ i, RegularAlong F (v i)) :
    ∃ (T : AmbientPoly n) (P : ι → AmbientPoly n),
      T ≠ 0 ∧ IsRelPrime F T ∧ ∀ i,
        v i = polynomialMap n (P i) / polynomialMap n T := by
  classical
  choose P T hT hFT heq using hv
  let D := ∏ i, T i
  refine ⟨D, fun i => P i * ∏ j ∈ Finset.univ.erase i, T j,
    Finset.prod_ne_zero_iff.mpr (fun i _ => hT i),
    IsRelPrime.prod_right (fun i _ => hFT i), ?_⟩
  intro i
  have hp : D = T i * ∏ j ∈ Finset.univ.erase i, T j :=
    (Finset.mul_prod_erase Finset.univ T (Finset.mem_univ i)).symm
  have ht := polynomialMap_ne_zero (hT i)
  have hr := polynomialMap_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun j _ => hT j) :
      (∏ j ∈ Finset.univ.erase i, T j) ≠ 0)
  rw [heq i, hp]
  simp only [map_mul]
  field_simp

def liftedField (v : Fin 5 → RationalFunction 4) : Fin 6 → RationalFunction 5 :=
  Fin.cases 0 (fun i => (coord (0 : Fin 6))^7 * chart (v i))

theorem liftedField_eq_scale (v : Fin 5 → RationalFunction 4) :
    liftedField v = fun i => (coord (0 : Fin 6))^6 *
      homogenizedField chart.toRingHom (coord 0) v i := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [liftedField, homogenizedField]
  · simp only [liftedField, homogenizedField, Fin.cases_succ,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
    ring

theorem liftedField_action (v : Fin 5 → RationalFunction 4) (P : RationalFunction 4) :
    fieldAction (rationalPartial 5) (liftedField v)
        ((coord (0 : Fin 6))^6 * chart P) =
      (coord (0 : Fin 6))^12 * chart (fieldAction (rationalPartial 4) v P) := by
  rw [liftedField_eq_scale, fieldAction_scale]
  have he := homogenizedField_contraction (rationalPartial 4) (rationalPartial 5)
      chart.toRingHom (coord 0) coord v actual_homogeneousChart P
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at he ⊢
  rw [he]
  ring

theorem liftedField_divergence (v : Fin 5 → RationalFunction 4) :
    fieldDivergence (rationalPartial 5) (liftedField v) =
      (coord (0 : Fin 6))^6 * chart (fieldDivergence (rationalPartial 4) v) := by
  have hs : fieldAction (rationalPartial 5)
      (homogenizedField chart.toRingHom (coord 0) v) ((coord (0 : Fin 6))^6) = 0 := by
    rw [fieldAction_apply, Fin.sum_univ_succ]
    simp only [homogenizedField, Fin.cases_zero, zero_mul, Fin.cases_succ,
      Derivation.leibniz_pow, partial_coord, Fin.succ_ne_zero, if_false,
      smul_zero, mul_zero, Finset.sum_const_zero, add_zero]
  rw [liftedField_eq_scale, fieldDivergence_scale, hs, zero_add,
    homogenizedField_divergence (rationalPartial 4) (rationalPartial 5)
      chart.toRingHom (coord 0) coord v actual_homogeneousChart]
  rfl

def affineDefect (v : Fin 5 → RationalFunction 4) : RationalFunction 4 :=
  rationalDefect affineF affineA 2 v

theorem liftedField_defect (v : Fin 5 → RationalFunction 4) :
    rationalDefect HodgeSubmission.F HodgeSubmission.A 2 (liftedField v) =
      (coord (0 : Fin 6))^12 * chart (affineDefect v) := by
  unfold rationalDefect affineDefect
  rw [protected_F_chart, protected_A_chart, liftedField_action, liftedField_divergence]
  simp only [rationalDefect, map_add, map_sub, map_mul, map_natCast]
  ring

theorem exists_homogeneous_liftedField
    (v : Fin 5 → RationalFunction 4) (hv : ∀ i, RegularAlong affineF (v i)) :
    ∃ (d : ℕ) (D : AmbientPoly 5) (N : Fin 6 → AmbientPoly 5),
      D ≠ 0 ∧ D.IsHomogeneous d ∧ IsRelPrime HodgeSubmission.F D ∧
      (∀ i, (N i).IsHomogeneous (d + 7)) ∧
      rationalField D N = liftedField v := by
  classical
  obtain ⟨T, P, hT0, hFT, hv⟩ := regular_common_denominator affineF v hv
  let polys : Option (Fin 5) → AmbientPoly 4 := fun i => i.elim T P
  let d := ∑ i, (polys i).totalDegree
  have hb : ∀ i, (polys i).totalDegree ≤ d := fun i =>
    Finset.single_le_sum (fun j _ => Nat.zero_le (polys j).totalDegree) (Finset.mem_univ i)
  have ht : T.totalDegree ≤ d := hb none
  have hp : ∀ i, (P i).totalDegree ≤ d := fun i => hb (some i)
  let D := homogenize T d
  let N : Fin 6 → AmbientPoly 5 := Fin.cases 0
    (fun i => X (0 : Fin 6)^7 * homogenize (P i) d)
  refine ⟨d, D, N, homogenize_ne_zero ht hT0, homogenize_homogeneous T d ht,
    homogenize_legal ht hFT, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact isHomogeneous_zero _ _ _
    · simpa only [N, Fin.cases_succ, Nat.one_mul, Nat.add_comm] using
        ((isHomogeneous_X ℂ (0 : Fin 6)).pow 7).mul
          (homogenize_homogeneous (P j) d (hp j))
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [rationalField, N, liftedField]
    · change polynomialMap 5 (X (0 : Fin 6)^7 * homogenize (P j) d) /
        polynomialMap 5 (homogenize T d) =
        (coord (0 : Fin 6))^7 * chart (v j)
      rw [map_mul, map_pow, homogenize_chart (P j) d (hp j),
        homogenize_chart T d ht, hv j, map_div₀]
      have hscale := coord_ne_zero (0 : Fin 6)
      have hden : chart (polynomialMap 4 T) ≠ 0 :=
        (map_ne_zero chart).mpr (polynomialMap_ne_zero hT0)
      field_simp

theorem lifted_regular_residual
    (v : Fin 5 → RationalFunction 4)
    (h : RegularAlong affineF (affineDefect v / (polynomialMap 4 affineF)^3)) :
    RegularAlong HodgeSubmission.F
      (rationalDefect HodgeSubmission.F HodgeSubmission.A 2 (liftedField v) /
        (polynomialMap 5 HodgeSubmission.F)^3) := by
  have hX : IsRelPrime HodgeSubmission.F (X (0 : Fin 6)) :=
    CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
      (CycleQ2SupportEquation.not_dvd_coordinate_of_degree_gt_one HodgeSubmission.F
        (by rw [CycleQ2Workspace.originalF_totalDegree]; norm_num) 0)
  have hr := (regular_inv_polynomial HodgeSubmission.F (X (0 : Fin 6))
    (X_ne_zero 0) hX).pow 6
  have hc := hr.mul (regular_chart h)
  convert hc using 1
  rw [liftedField_defect, protected_F_chart, map_div₀, map_pow]
  have hs := coord_ne_zero (0 : Fin 6)
  have hf : chart (polynomialMap 4 affineF) ≠ 0 :=
    (map_ne_zero chart).mpr (polynomialMap_ne_zero affineF_ne_zero)
  simp only [coord]
  field_simp

/-- The complete algebraic implication from a genuine regular affine
primitive to the unchanged protected certificate. -/
theorem protected_certificate_of_affine_primitive
    (v : Fin 5 → RationalFunction 4)
    (hv : ∀ i, RegularAlong affineF (v i))
    (hres : RegularAlong affineF (affineDefect v / (polynomialMap 4 affineF)^3)) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  obtain ⟨d, D, N, hD0, hDhom, hFD, hN, hfield⟩ :=
    exists_homogeneous_liftedField v hv
  have hr := lifted_regular_residual v hres
  rw [← hfield] at hr
  obtain ⟨P, T, hT0, hFT, hr⟩ := hr
  have hlocal : LocalizedEquation HodgeSubmission.F HodgeSubmission.A 2 D N := by
    refine ⟨P, T, hT0, hFT, ?_⟩
    have hf := polynomialMap_ne_zero CycleQ2Workspace.originalF_ne_zero
    have ht := polynomialMap_ne_zero hT0
    field_simp at hr ⊢
    linear_combination hr
  have hdegree : D.totalDegree = d := hDhom.totalDegree hD0
  obtain ⟨Q, hQ⟩ := (exists_verify_iff_localizedEquation
    HodgeSubmission.F HodgeSubmission.A D 6 2 N
    CycleQ2Workspace.originalF_ne_zero CycleQ2Workspace.originalF_homogeneous
    (by simpa using Homogeneous.of_isHomogeneous CycleQ2Workspace.originalA_homogeneous)
    hD0 (by simpa only [hdegree] using hDhom)
    (fun i => by
      convert Homogeneous.of_isHomogeneous (hN i) using 1
      simp only [hdegree, Nat.cast_add, Nat.cast_ofNat]
      ring)
    hFD).mpr hlocal
  unfold HasCertificate
  rw [CycleQ2Workspace.originalF_totalDegree]
  exact ⟨D, N, Q, hQ⟩

end CycleQ2AffineCertificate

#print axioms CycleQ2AffineCertificate.protected_certificate_of_affine_primitive
end
end


/- Component: pole_reduction/AffineHypersurfaceDerivations.lean -/
section
/-!
# Actual tangent derivations on the protected projective affine chart

The coordinate ring is the actual quotient C[x0,...,x4]/(affineF), where
`affineF` is obtained from the protected sextic by setting homogeneous Z0=1.
Its fraction field is the function field of this affine hypersurface chart.
The four tangent derivations are constructed by quotient descent and
fraction-field extension, with all hypotheses proved for this exact equation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2AffineHypersurface

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineGeometry

abbrev AffineCoordinateRing := AmbientPoly 4 ⧸ Ideal.span {affineF}

instance affineCoordinateRing_isDomain : IsDomain AffineCoordinateRing :=
  (Ideal.Quotient.isDomain_iff_prime _).mpr
    ((Ideal.span_singleton_prime affineF_irreducible.ne_zero).mpr affineF_prime)

abbrev AffineFunctionField := FractionRing AffineCoordinateRing

local instance affineFunctionFieldIntAlgebra : Algebra ℤ AffineFunctionField :=
  Ring.toIntAlgebra _

/-- Actual projection to the protected affine chart's coordinate ring. -/
def affineProjection : AmbientPoly 4 →+* AffineCoordinateRing := Ideal.Quotient.mk _

theorem affineProjection_surjective : Function.Surjective affineProjection :=
  Ideal.Quotient.mk_surjective

theorem affineProjection_kernel (P : AmbientPoly 4) :
    affineProjection P = 0 ↔ affineF ∣ P := by
  simp only [affineProjection, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]

/-- Actual polynomial class in the protected affine chart's function field. -/
def affineMap : AmbientPoly 4 →+* AffineFunctionField :=
  (algebraMap AffineCoordinateRing AffineFunctionField).comp affineProjection

theorem affineMap_kernel (P : AmbientPoly 4) :
    affineMap P = 0 ↔ affineF ∣ P := by
  constructor
  · intro h
    apply (affineProjection_kernel P).mp
    apply IsFractionRing.injective AffineCoordinateRing AffineFunctionField
    simpa only [affineMap, RingHom.comp_apply, map_zero] using h
  · intro h
    change algebraMap AffineCoordinateRing AffineFunctionField (affineProjection P) = 0
    rw [(affineProjection_kernel P).mpr h, map_zero]

@[simp] theorem affineMap_F : affineMap affineF = 0 :=
  (affineMap_kernel _).mpr (dvd_refl _)

/-- The normal derivative is nonzero in the actual affine function field. -/
theorem normal_ne_zero : affineMap (pderiv 0 affineF) ≠ 0 := by
  intro h
  exact affineF_not_dvd_normal ((affineMap_kernel _).mp h)

/-- Polynomial coordinate partials in the integer-linear interface used by
the trusted residue derivation construction. -/
def polynomialPartial (i : Fin 5) : Derivation ℤ (AmbientPoly 4) (AmbientPoly 4) :=
  (MvPolynomial.pderiv i).restrictScalars ℤ

@[simp] theorem polynomialPartial_apply (i : Fin 5) (P : AmbientPoly 4) :
    polynomialPartial i P = pderiv i P := rfl

theorem polynomialPartials_commute (i j : Fin 5) (P : AmbientPoly 4) :
    polynomialPartial i (polynomialPartial j P) =
      polynomialPartial j (polynomialPartial i P) :=
  CycleQ2Regularity.polynomial_partials_commute i j P

/-- The four actual tangent derivations, obtained by descent through (F)
followed by fraction-field extension. Coordinate zero is the eliminated normal. -/
def affineTangent (j : Fin 4) : Derivation ℤ AffineFunctionField AffineFunctionField :=
  HoldoutConstruction.residueTangent (K := AffineFunctionField)
    affineProjection affineProjection_surjective (polynomialPartial 0)
    (polynomialPartial j.succ) affineF affineProjection_kernel normal_ne_zero

/-- The actual tangent derivative has the implicit-coordinate formula on
every polynomial class. -/
theorem affineTangent_apply (j : Fin 4) (P : AmbientPoly 4) :
    affineTangent j (affineMap P) = affineMap (pderiv j.succ P) -
      affineMap (pderiv j.succ affineF) /
        affineMap (pderiv 0 affineF) * affineMap (pderiv 0 P) :=
  HoldoutConstruction.residueTangent_apply (K := AffineFunctionField)
    affineProjection affineProjection_surjective (polynomialPartial 0)
    (polynomialPartial j.succ) affineF affineProjection_kernel normal_ne_zero P

@[simp] theorem affineTangent_F (j : Fin 4) :
    affineTangent j (affineMap affineF) = 0 := by
  rw [affineMap_F, map_zero]

/-- All four constructed tangent derivations commute on the entire actual
affine chart function field; no derivative-compatibility assumption remains. -/
theorem affineTangents_commute (i j : Fin 4) :
    Function.Commute (affineTangent i) (affineTangent j) :=
  HoldoutConstruction.residueTangent_commute (K := AffineFunctionField)
    affineProjection affineProjection_surjective (polynomialPartial 0)
    (polynomialPartial i.succ) (polynomialPartial j.succ) affineF
    affineProjection_kernel normal_ne_zero (polynomialPartials_commute i.succ 0)
    (polynomialPartials_commute j.succ 0) (polynomialPartials_commute i.succ j.succ)

@[simp] theorem affineTangent_constant (j : Fin 4) (c : ℂ) :
    affineTangent j (affineMap (C c)) = 0 := by
  rw [affineTangent_apply]
  simp

/-- The independent coordinate classes have the expected Kronecker derivatives. -/
theorem affineTangent_coordinate (i j : Fin 4) :
    affineTangent i (affineMap (X j.succ)) = if j = i then 1 else 0 := by
  rw [affineTangent_apply]
  simp [pderiv_X, Pi.single_apply, Fin.succ_ne_zero]

/-- The eliminated coordinate differentiates by the implicit equation. -/
theorem affineTangent_normalCoordinate (i : Fin 4) :
    affineTangent i (affineMap (X 0)) =
      -affineMap (pderiv i.succ affineF) /
        affineMap (pderiv 0 affineF) := by
  rw [affineTangent_apply]
  simp [pderiv_X, Pi.single_apply, Fin.succ_ne_zero, div_eq_mul_inv]

end CycleQ2AffineHypersurface

#print axioms CycleQ2AffineHypersurface.normal_ne_zero
#print axioms CycleQ2AffineHypersurface.affineTangent_apply
#print axioms CycleQ2AffineHypersurface.affineTangents_commute
end
end


/- Component: pole_reduction/AffineRegularResidue.lean -/
section
/-!
# Actual residue homomorphism on the protected projective affine chart

The domain is the actual subring of five-variable ambient fractions admitting
a denominator relatively prime to affineF. The target is the actual fraction
field of the protected hypersurface chart Z0=1.
The representative-choice map is proved independent by cross multiplication.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2AffineResidue

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity CycleQ2AffineHypersurface
  CycleQ2AffineClearing CycleQ2AffineGeometry

abbrev Poly := AmbientPoly 4
abbrev RatFun := RationalFunction 4

/-- The actual ring of ambient rational functions regular along F. -/
def RegularAtF : Subring RatFun where
  carrier := {z | RegularAlong affineF z}
  zero_mem' := regular_zero _
  one_mem' := regular_one _
  add_mem' := fun hx hy => hx.add hy
  mul_mem' := fun hx hy => hx.mul hy
  neg_mem' := fun hx => hx.neg

private def presentationNumerator (z : RegularAtF) : Poly :=
  Classical.choose z.property

private def presentationDenominator (z : RegularAtF) : Poly :=
  Classical.choose (Classical.choose_spec z.property)

private theorem presentation_spec (z : RegularAtF) :
    presentationDenominator z ≠ 0 ∧
    IsRelPrime affineF (presentationDenominator z) ∧
    (z : RatFun) = polynomialMap 4 (presentationNumerator z) /
      polynomialMap 4 (presentationDenominator z) :=
  Classical.choose_spec (Classical.choose_spec z.property)

/-- Every legal ambient denominator maps to a nonzero affine-chart-function-field element. -/
theorem legal_affineMap_ne_zero (T : Poly) (hT : IsRelPrime affineF T) :
    affineMap T ≠ 0 := by
  intro h
  exact (affineF_irreducible.isRelPrime_iff_not_dvd.mp hT)
    ((affineMap_kernel T).mp h)

private def residueValue (z : RegularAtF) : AffineFunctionField :=
  affineMap (presentationNumerator z) / affineMap (presentationDenominator z)

/-- Representative independence uses the injective ambient fraction map and
polynomial cross multiplication, not a chosen representative axiom. -/
private theorem residueValue_eq (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime affineF T)
    (hz : (z : RatFun) = polynomialMap 4 P / polynomialMap 4 T) :
    residueValue z = affineMap P / affineMap T := by
  have hs := presentation_spec z
  have hcross : presentationNumerator z * T = P * presentationDenominator z := by
    apply polynomialMap_injective
    simpa only [map_mul] using
      (div_eq_div_iff (polynomialMap_ne_zero hs.1) (polynomialMap_ne_zero hT)).mp
        (hs.2.2.symm.trans hz)
  apply (div_eq_div_iff
    (legal_affineMap_ne_zero _ hs.2.1) (legal_affineMap_ne_zero T hFT)).mpr
  simpa only [map_mul] using congrArg affineMap hcross

private theorem residueValue_zero : residueValue 0 = 0 := by
  simpa using residueValue_eq 0 0 1 one_ne_zero isRelPrime_one_right (by simp)

private theorem residueValue_one : residueValue 1 = 1 := by
  simpa using residueValue_eq 1 1 1 one_ne_zero isRelPrime_one_right (by simp)

private theorem residueValue_add (x y : RegularAtF) :
    residueValue (x + y) = residueValue x + residueValue y := by
  obtain ⟨P, T, hT, hFT, hx⟩ := x.property
  obtain ⟨Q, U, hU, hFU, hy⟩ := y.property
  have hxy : ((x + y : RegularAtF) : RatFun) =
      polynomialMap 4 (P * U + Q * T) / polynomialMap 4 (T * U) := by
    change (x : RatFun) + (y : RatFun) = _
    rw [hx, hy]
    have hT' := polynomialMap_ne_zero hT
    have hU' := polynomialMap_ne_zero hU
    simp only [map_add, map_mul]
    field_simp
  rw [residueValue_eq _ _ _ (mul_ne_zero hT hU) (hFT.mul_right hFU) hxy,
    residueValue_eq x P T hT hFT hx, residueValue_eq y Q U hU hFU hy]
  have hT' := legal_affineMap_ne_zero T hFT
  have hU' := legal_affineMap_ne_zero U hFU
  simp only [map_add, map_mul]
  field_simp

private theorem residueValue_mul (x y : RegularAtF) :
    residueValue (x * y) = residueValue x * residueValue y := by
  obtain ⟨P, T, hT, hFT, hx⟩ := x.property
  obtain ⟨Q, U, hU, hFU, hy⟩ := y.property
  have hxy : ((x * y : RegularAtF) : RatFun) =
      polynomialMap 4 (P * Q) / polynomialMap 4 (T * U) := by
    change (x : RatFun) * (y : RatFun) = _
    rw [hx, hy]
    simp only [map_mul, mul_div_mul_comm]
  rw [residueValue_eq _ _ _ (mul_ne_zero hT hU) (hFT.mul_right hFU) hxy,
    residueValue_eq x P T hT hFT hx, residueValue_eq y Q U hU hFU hy]
  simp only [map_mul, mul_div_mul_comm]

/-- The actual residue homomorphism from the regular subring to the protected
affine chart function field. All ring-homomorphism laws are proved above. -/
def residue : RegularAtF →+* AffineFunctionField where
  toFun := residueValue
  map_zero' := residueValue_zero
  map_one' := residueValue_one
  map_add' := residueValue_add
  map_mul' := residueValue_mul

theorem residue_fraction (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime affineF T)
    (hz : (z : RatFun) = polynomialMap 4 P / polynomialMap 4 T) :
    residue z = affineMap P / affineMap T :=
  residueValue_eq z P T hT hFT hz

/-- A polynomial viewed in the regular ambient subring. -/
def polynomialRegular (P : Poly) : RegularAtF :=
  ⟨polynomialMap 4 P, regular_polynomial affineF P⟩

@[simp] theorem residue_polynomial (P : Poly) :
    residue (polynomialRegular P) = affineMap P := by
  simpa using residue_fraction (polynomialRegular P) P 1
    one_ne_zero isRelPrime_one_right (by simp [polynomialRegular])

theorem residue_fraction_eq_zero_iff (z : RegularAtF) (P T : Poly)
    (hT : T ≠ 0) (hFT : IsRelPrime affineF T)
    (hz : (z : RatFun) = polynomialMap 4 P / polynomialMap 4 T) :
    residue z = 0 ↔ affineF ∣ P := by
  rw [residue_fraction z P T hT hFT hz]
  have hT' := legal_affineMap_ne_zero T hFT
  rw [div_eq_zero_iff]
  simp only [hT', or_false]
  exact affineMap_kernel P

/-- The actual residue kernel is exactly multiplication by F inside the
regular subring. The quotient coefficient is still regular along F. -/
theorem residue_eq_zero_iff_exists_F_mul (z : RegularAtF) :
    residue z = 0 ↔ ∃ t : RegularAtF,
      (z : RatFun) = polynomialMap 4 affineF * (t : RatFun) := by
  constructor
  · intro hz
    obtain ⟨P, T, hT, hFT, hrepr⟩ := z.property
    obtain ⟨Q, hQ⟩ := (residue_fraction_eq_zero_iff z P T hT hFT hrepr).mp hz
    let t : RegularAtF := ⟨polynomialMap 4 Q / polynomialMap 4 T,
      ⟨Q, T, hT, hFT, rfl⟩⟩
    refine ⟨t, ?_⟩
    change (z : RatFun) = polynomialMap 4 affineF *
      (polynomialMap 4 Q / polynomialMap 4 T)
    rw [hrepr, hQ, map_mul]
    ring
  · rintro ⟨t, ht⟩
    have he : z = polynomialRegular affineF * t := Subtype.ext ht
    rw [he, map_mul, residue_polynomial, affineMap_F, zero_mul]

/-- Equivalent form convenient for pole reduction: vanishing residue means
one can divide by F while remaining in the actual regular subring. -/
theorem residue_eq_zero_iff_regular_div_F (z : RegularAtF) :
    residue z = 0 ↔ RegularAlong affineF
      ((z : RatFun) / polynomialMap 4 affineF) := by
  have hF := polynomialMap_ne_zero affineF_irreducible.ne_zero
  constructor
  · intro hz
    obtain ⟨t, ht⟩ := (residue_eq_zero_iff_exists_F_mul z).mp hz
    have he : (z : RatFun) / polynomialMap 4 affineF = (t : RatFun) := by
      rw [ht]
      field_simp
    rw [he]
    exact t.property
  · intro hz
    apply (residue_eq_zero_iff_exists_F_mul z).mpr
    refine ⟨⟨(z : RatFun) / polynomialMap 4 affineF, hz⟩, ?_⟩
    change (z : RatFun) = polynomialMap 4 affineF *
      ((z : RatFun) / polynomialMap 4 affineF)
    field_simp


open CycleQ2ActualResidueClosure

local instance rationalFunctionIntAlgebra : Algebra ℤ RatFun := Ring.toIntAlgebra _
local instance affineFunctionFieldIntAlgebra : Algebra ℤ AffineFunctionField := Ring.toIntAlgebra _
local instance regularAtFIntAlgebra : Algebra ℤ RegularAtF := Ring.toIntAlgebra _

/-- The exact normal polynomial is nonzero before quotienting as well. -/
theorem normal_polynomial_ne_zero : pderiv 0 affineF ≠ 0 := by
  intro h
  apply normal_ne_zero
  rw [h, map_zero]

theorem normal_polynomial_relPrime :
    IsRelPrime affineF (pderiv 0 affineF) :=
  affineF_irreducible.isRelPrime_iff_not_dvd.mpr
    affineF_not_dvd_normal

/-- Restriction of the actual ambient tangent derivation to the actual regular
subring. Closure is proved from the quotient rule and normal-denominator legality. -/
def regularTangent (j : Fin 4) : Derivation ℤ RegularAtF RegularAtF :=
  Derivation.mk'
    ({ toFun := fun z => ⟨actualTangent affineF j (z : RatFun),
         regular_actualTangent z.property normal_polynomial_ne_zero
           normal_polynomial_relPrime j⟩
       map_zero' := Subtype.ext (map_zero _)
       map_add' := fun x y => Subtype.ext (map_add _ _ _)
     } : RegularAtF →+ RegularAtF).toIntLinearMap
    (by
      intro x y
      apply Subtype.ext
      change actualTangent affineF j ((x : RatFun) * (y : RatFun)) =
        (x : RatFun) * actualTangent affineF j (y : RatFun) +
          (y : RatFun) * actualTangent affineF j (x : RatFun)
      simpa only [smul_eq_mul] using
        (actualTangent affineF j).leibniz (x : RatFun) (y : RatFun))

@[simp] theorem regularTangent_apply (j : Fin 4) (z : RegularAtF) :
    ((regularTangent j z : RegularAtF) : RatFun) =
      actualTangent affineF j (z : RatFun) := rfl

@[simp] theorem residue_regularTangent_polynomial (j : Fin 4) (P : Poly) :
    residue (regularTangent j (polynomialRegular P)) =
      affineTangent j (affineMap P) := by
  let Q : Poly := pderiv 0 affineF * pderiv j.succ P -
    pderiv j.succ affineF * pderiv 0 P
  have hrepr : ((regularTangent j (polynomialRegular P) : RegularAtF) : RatFun) =
      polynomialMap 4 Q / polynomialMap 4 (pderiv 0 affineF) := by
    change actualTangent affineF j (polynomialMap 4 P) = _
    rw [actualTangent_apply]
    simp only [Q, rationalPartial_map, map_sub, map_mul]
    have hg := polynomialMap_ne_zero normal_polynomial_ne_zero
    field_simp <;> ring
  rw [residue_fraction _ Q _ normal_polynomial_ne_zero normal_polynomial_relPrime hrepr,
    affineTangent_apply]
  simp only [Q, map_sub, map_mul]
  have hg := normal_ne_zero
  field_simp <;> ring

/-- Exact compatibility of the actual regular-subring residue homomorphism
with the actual constructed tangent derivations on the affine chart function field. -/
theorem residue_regularTangent (j : Fin 4) (z : RegularAtF) :
    residue (regularTangent j z) = affineTangent j (residue z) := by
  obtain ⟨P, T, hT, hFT, hz⟩ := z.property
  have hprod : z * polynomialRegular T = polynomialRegular P := by
    apply Subtype.ext
    change (z : RatFun) * polynomialMap 4 T = polynomialMap 4 P
    rw [hz, div_mul_cancel₀ _ (polynomialMap_ne_zero hT)]
  have h₁ := congrArg (fun u : RegularAtF => residue (regularTangent j u)) hprod
  rw [Derivation.leibniz] at h₁
  simp only [smul_eq_mul, map_add, map_mul, residue_polynomial,
    residue_regularTangent_polynomial] at h₁
  have h₂ := congrArg (fun u : RegularAtF => affineTangent j (residue u)) hprod
  simp only [map_mul, residue_polynomial, Derivation.leibniz, smul_eq_mul] at h₂
  apply mul_left_cancel₀ (legal_affineMap_ne_zero T hFT)
  linear_combination h₁ - h₂


/-- Every element of the actual affine chart function field lifts to an actual
ambient fraction regular along affineF. The chart construction supplies
the projective interpretation independently of any grading of this lift. -/
theorem residue_surjective : Function.Surjective residue := by
  intro w
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective AffineCoordinateRing w
  obtain ⟨P, rfl⟩ := affineProjection_surjective a
  obtain ⟨T, rfl⟩ := affineProjection_surjective b
  have hden : affineMap T ≠ 0 := by
    change algebraMap AffineCoordinateRing AffineFunctionField (affineProjection T) ≠ 0
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hT : T ≠ 0 := by
    intro h
    apply hden
    rw [h, map_zero]
  have hFT : IsRelPrime affineF T :=
    affineF_irreducible.isRelPrime_iff_not_dvd.mpr
      (fun h => hden ((affineMap_kernel T).mpr h))
  let z : RegularAtF := ⟨polynomialMap 4 P / polynomialMap 4 T,
    ⟨P, T, hT, hFT, rfl⟩⟩
  refine ⟨z, ?_⟩
  exact residue_fraction z P T hT hFT rfl

/-- A nonconstructive lift, justified by the proved residue surjectivity. -/
def liftResidue (w : AffineFunctionField) : RegularAtF :=
  Function.surjInv residue_surjective w

@[simp] theorem residue_liftResidue (w : AffineFunctionField) :
    residue (liftResidue w) = w := Function.surjInv_eq residue_surjective w

end CycleQ2AffineResidue

#print axioms CycleQ2AffineResidue.residue_fraction
#print axioms CycleQ2AffineResidue.residue_eq_zero_iff_exists_F_mul
#print axioms CycleQ2AffineResidue.residue_eq_zero_iff_regular_div_F

#print axioms CycleQ2AffineResidue.residue_regularTangent

#print axioms CycleQ2AffineResidue.residue_surjective
#print axioms CycleQ2AffineResidue.residue_liftResidue
end
end


/- Component: pole_reduction/AffineResidueClosure.lean -/
section
/-!
Concrete closure of an actual residue primitive on the protected X0=1 chart.

The source, quotient function field, derivations, regular lifts, homogeneous
clearing, and final certificate are all bound to the actual protected instance.
The final theorem still explicitly requires existence of the affine residue
primitive; that geometric existence statement is not asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineResidueClosure

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open CycleQ2AffineHypersurface CycleQ2AffineResidue CycleQ2ActualResidueClosure
open CycleQ2AffineClearing CycleQ2AffineCertificate
open HoldoutConstruction SplitHigherResidue
open scoped BigOperators

local instance rationalFunctionIntAlgebra : Algebra ℤ RatFun := Ring.toIntAlgebra _
local instance affineFunctionFieldIntAlgebra : Algebra ℤ AffineFunctionField := Ring.toIntAlgebra _
local instance regularAtFIntAlgebra : Algebra ℤ RegularAtF := Ring.toIntAlgebra _

private theorem two_polynomial_relPrime : IsRelPrime affineF (2 : Poly) := by
  have hu : IsUnit (2 : Poly) := by
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (2 : ℂ) ≠ 0)).map (C : ℂ →+* Poly)
  exact hu.isRelPrime_right

/-- The genuine inverse of the normal polynomial in the regular subring. -/
def normalInverse : RegularAtF :=
  ⟨(polynomialMap 4 (pderiv 0 affineF))⁻¹,
    regular_inv_polynomial _ _ normal_polynomial_ne_zero normal_polynomial_relPrime⟩

@[simp] theorem normalInverse_val :
    (normalInverse : RatFun) = (polynomialMap 4 (pderiv 0 affineF))⁻¹ := rfl

@[simp] theorem residue_normalInverse :
    residue normalInverse = (affineMap (pderiv 0 affineF))⁻¹ := by
  simpa using residue_fraction normalInverse 1 (pderiv 0 affineF)
    normal_polynomial_ne_zero normal_polynomial_relPrime (by simp [normalInverse])

private def halfRegular : RegularAtF :=
  ⟨(1 / 2 : RatFun), by
    change RegularAlong affineF (1 / 2 : RatFun)
    simpa only [map_ofNat, one_div] using regular_inv_polynomial affineF (2 : Poly)
      (by norm_num) two_polynomial_relPrime⟩

private theorem halfRegular_val : (halfRegular : RatFun) = (1 / 2 : RatFun) := rfl

private theorem residue_halfRegular : residue halfRegular = (1 / 2 : AffineFunctionField) := by
  simpa only [map_one, map_ofNat] using residue_fraction halfRegular 1 (2 : Poly)
    (by norm_num) two_polynomial_relPrime (by
      change (1 / 2 : RatFun) = polynomialMap 4 1 / polynomialMap 4 2
      simp only [map_one, map_ofNat])

/-- The exact normal source, now evaluated in the actual affine function field. -/
def affineNormalSource (A : Poly) : AffineFunctionField :=
  normalSourceTwo (affineMap A) (affineMap (pderiv 0 A))
    (affineMap (pderiv 0 (pderiv 0 A)))
    (affineMap (pderiv 0 affineF))
    (affineMap (pderiv 0 (pderiv 0 affineF)))
    (affineMap (pderiv 0 (pderiv 0 (pderiv 0 affineF))))

/-- The concrete function-field residue equation whose solution is required. -/
def affineResidueExpression (A : Poly) (w : Fin 4 → AffineFunctionField) : AffineFunctionField :=
  affineNormalSource A +
    residueDivergence affineTangent (affineMap (pderiv 0 affineF)) w

private def normalSourceRegular (A : Poly) : RegularAtF :=
  halfRegular *
    (polynomialRegular (pderiv 0 (pderiv 0 A)) * normalInverse ^ 2 -
      (3 * polynomialRegular (pderiv 0 A) *
          polynomialRegular (pderiv 0 (pderiv 0 affineF)) +
        polynomialRegular A * polynomialRegular (pderiv 0 (pderiv 0 (pderiv 0 affineF)))) *
        normalInverse ^ 3 +
      3 * polynomialRegular A * polynomialRegular (pderiv 0 (pderiv 0 affineF)) ^ 2 *
        normalInverse ^ 4)

private theorem normalSourceRegular_val (A : Poly) :
    ((normalSourceRegular A : RegularAtF) : RatFun) =
      actualNormalSource affineF A := by
  change RegularAtF.subtype (normalSourceRegular A) = _
  simp only [normalSourceRegular, actualNormalSource, normalSourceTwo,
    map_mul, map_add, map_sub, map_pow, map_ofNat, Subring.subtype_apply,
    halfRegular_val, normalInverse_val, polynomialRegular,
    div_eq_mul_inv, inv_pow]

private theorem residue_normalSourceRegular (A : Poly) :
    residue (normalSourceRegular A) = affineNormalSource A := by
  simp only [normalSourceRegular, map_mul, map_add, map_sub, map_pow, map_ofNat,
    residue_halfRegular, residue_normalInverse, residue_polynomial,
    affineNormalSource, normalSourceTwo, div_eq_mul_inv, inv_pow]

/-- The actual regular-subring lift of the entire residue equation. -/
def residueExpressionRegular (A : Poly) (w : Fin 4 → RegularAtF) : RegularAtF :=
  normalSourceRegular A +
    (∑ j, regularTangent j (w j)) -
    (∑ j, w j * regularTangent j (polynomialRegular (pderiv 0 affineF))) *
      normalInverse

theorem residueExpressionRegular_val (A : Poly) (w : Fin 4 → RegularAtF) :
    ((residueExpressionRegular A w : RegularAtF) : RatFun) =
      actualResidueExpression affineF A (fun j => (w j : RatFun)) := by
  change RegularAtF.subtype (residueExpressionRegular A w) = _
  simp only [residueExpressionRegular, map_add, map_sub, map_mul,
    map_sum, Subring.subtype_apply, regularTangent_apply, normalSourceRegular_val, normalInverse_val,
    polynomialRegular, actualResidueExpression, residueDivergence,
    HoldoutConstruction.fieldDivergence, div_eq_mul_inv]
  ring

/-- The ambient source and tangent divergence transport to the actual quotient
equation through the proved residue homomorphism. -/
theorem residue_residueExpressionRegular (A : Poly) (w : Fin 4 → RegularAtF) :
    residue (residueExpressionRegular A w) =
      affineResidueExpression A (fun j => residue (w j)) := by
  simp only [residueExpressionRegular, map_add, map_sub, map_mul, map_sum,
    residue_normalSourceRegular, residue_regularTangent, residue_polynomial,
    residue_normalInverse, affineResidueExpression, residueDivergence,
    HoldoutConstruction.fieldDivergence, div_eq_mul_inv]
  ring

/-- A solved affine residue equation for actual regular lifts gives an actual
regular ambient vector with third-order defect. Homogeneity is not asserted. -/
theorem regular_affine_primitive_closure (A : Poly) (w : Fin 4 → RegularAtF)
    (hres : affineResidueExpression A (fun j => residue (w j)) = 0) :
    ∃ (v : Fin 5 → RatFun) (t : RatFun),
      (∀ i, RegularAlong affineF (v i)) ∧
      RegularAlong affineF t ∧
      rationalDefect affineF A 2 v =
        polynomialMap 4 affineF ^ 3 * t := by
  have hz : residue (residueExpressionRegular A w) = 0 := by
    rw [residue_residueExpressionRegular]
    exact hres
  obtain ⟨t, ht⟩ := (residue_eq_zero_iff_exists_F_mul (residueExpressionRegular A w)).mp hz
  refine ⟨actualClosureVector affineF A (fun j => (w j : RatFun)), t,
    ?_, t.property, ?_⟩
  · exact regular_actualClosureVector affineF A _ normal_polynomial_ne_zero
      normal_polynomial_relPrime (fun j => (w j).property)
  · apply actualClosure_defect_of_residue affineF A _ _ normal_polynomial_ne_zero
    rw [← residueExpressionRegular_val]
    exact ht

/-- Every actual affine primitive has regular ambient lifts. This conclusion
is the rational defect equation; no homogeneous-degree conclusion is hidden. -/
theorem affine_primitive_closure (A : Poly) (w : Fin 4 → AffineFunctionField)
    (hres : affineResidueExpression A w = 0) :
    ∃ (v : Fin 5 → RatFun) (t : RatFun),
      (∀ i, RegularAlong affineF (v i)) ∧
      RegularAlong affineF t ∧
      rationalDefect affineF A 2 v =
        polynomialMap 4 affineF ^ 3 * t := by
  apply regular_affine_primitive_closure A (fun j => liftResidue (w j))
  simpa only [residue_liftResidue] using hres

/-- The exact chart numerator is bound here to the concrete affine equation.
Its remaining primitive-existence hypothesis is stated explicitly. -/
theorem protected_regular_ambient_of_affine_primitive
    (h : ∃ w : Fin 4 → AffineFunctionField,
      affineResidueExpression affineA w = 0) :
    ∃ (v : Fin 5 → RatFun) (t : RatFun),
      (∀ i, RegularAlong affineF (v i)) ∧
      RegularAlong affineF t ∧
      rationalDefect affineF affineA 2 v =
        polynomialMap 4 affineF ^ 3 * t := by
  obtain ⟨w, hw⟩ := h
  exact affine_primitive_closure affineA w hw

/-- A primitive for the exact affine function-field residue implies the
unchanged protected certificate. All field, derivative, regularity,
homogeneity, and denominator-legality steps are proved by this point. -/
theorem protected_certificate_of_affine_residue_primitive
    (h : ∃ w : Fin 4 → AffineFunctionField,
      affineResidueExpression affineA w = 0) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  obtain ⟨v, t, hv, ht, heq⟩ := protected_regular_ambient_of_affine_primitive h
  apply CycleQ2AffineCertificate.protected_certificate_of_affine_primitive v hv
  change RegularAlong affineF
    (rationalDefect affineF affineA 2 v / (polynomialMap 4 affineF) ^ 3)
  rw [heq]
  have hf := polynomialMap_ne_zero affineF_ne_zero
  have hquotient : polynomialMap 4 affineF ^ 3 * t / polynomialMap 4 affineF ^ 3 = t := by
    field_simp
  rw [hquotient]
  exact ht

end CycleQ2AffineResidueClosure

#print axioms CycleQ2AffineResidueClosure.residue_residueExpressionRegular
#print axioms CycleQ2AffineResidueClosure.regular_affine_primitive_closure
#print axioms CycleQ2AffineResidueClosure.protected_regular_ambient_of_affine_primitive
#print axioms CycleQ2AffineResidueClosure.protected_certificate_of_affine_residue_primitive
end
end


/- Component: continuation_2/AffineKaehler.lean -/
section
/-!
# Actual relative Kähler differentials of the protected affine chart

The four independent coordinate differentials form a basis of the genuine
mathlib module Ω[K⁄ℂ], where K is the already constructed function field of
the exact chart F(1,x)=0. The universal differential is computed by the
already constructed tangent derivations. No cohomological vanishing or
primitive-existence hypothesis is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineDifferentials

open MvPolynomial HodgeComputer CycleQ2AffineHypersurface CycleQ2AffineClearing
open scoped BigOperators

abbrev K := AffineFunctionField
abbrev Omega := Ω[K⁄ℂ]

local instance intAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

theorem affineMap_eq_algebraMap (P : AmbientPoly 4) :
    affineMap P = algebraMap (AmbientPoly 4) K P := rfl

theorem affineMap_constant (c : ℂ) :
    affineMap (C c) = algebraMap ℂ K c := rfl

theorem tangent_complex_constant (j : Fin 4) (c : ℂ) :
    affineTangent j (algebraMap ℂ K c) = 0 := by
  rw [← affineMap_constant]
  exact affineTangent_constant j c

theorem tangent_complex_smul (j : Fin 4) (c : ℂ) (z : K) :
    affineTangent j (c • z) = c • affineTangent j z := by
  simp only [Algebra.smul_def, Derivation.leibniz, smul_eq_mul,
    tangent_complex_constant, mul_zero, add_zero]
  simp

/-- The actual tangent operator, with its complex scalar linearity included
in the type. Its underlying function is unchanged. -/
def complexTangent (j : Fin 4) : Derivation ℂ K K where
  toFun := affineTangent j
  map_add' := (affineTangent j).map_add
  map_smul' := tangent_complex_smul j
  map_one_eq_zero' := (affineTangent j).map_one_eq_zero
  leibniz' := (affineTangent j).leibniz

@[simp] theorem complexTangent_apply (j : Fin 4) (z : K) :
    complexTangent j z = affineTangent j z := rfl

abbrev d : Derivation ℂ K Omega := KaehlerDifferential.D ℂ K

/-- The four independent coordinate differentials in the actual universal
module of relative differentials. -/
def coordinateDifferential (j : Fin 4) : Omega := d (affineMap (X j.succ))

private theorem sum_derivations_apply
    (q : Fin 5 → Derivation ℂ (AmbientPoly 4) Omega) (P : AmbientPoly 4) :
    (∑ i, q i) P = ∑ i, q i P := by
  simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using
    congrFun (map_sum Derivation.coeFnAddMonoidHom q Finset.univ) P

theorem differential_polynomial (P : AmbientPoly 4) :
    d (affineMap P) = ∑ i : Fin 5, affineMap (pderiv i P) • d (affineMap (X i)) := by
  let dp : Derivation ℂ (AmbientPoly 4) Omega := d.compAlgebraMap (AmbientPoly 4)
  have he : dp = ∑ i : Fin 5,
      (LinearMap.toSpanSingleton (AmbientPoly 4) Omega (dp (X i))).compDer (pderiv i) := by
    apply MvPolynomial.derivation_ext
    intro i
    rw [sum_derivations_apply]
    simp [Derivation.coe_comp, pderiv_X, Pi.single_apply]
  have hh := Derivation.congr_fun he P
  rw [sum_derivations_apply] at hh
  simpa only [dp, Derivation.compAlgebraMap_apply,
    Derivation.coe_comp, LinearMap.comp_apply, LinearMap.coe_restrictScalars,
    Derivation.coeFn_coe, LinearMap.toSpanSingleton_apply,
    affineMap_eq_algebraMap, IsScalarTower.algebraMap_smul] using hh

theorem differential_normal :
    d (affineMap (X (0 : Fin 5))) =
      ∑ j : Fin 4, (-affineMap (pderiv j.succ affineF) /
        affineMap (pderiv 0 affineF)) • coordinateDifferential j := by
  have hf := differential_polynomial affineF
  rw [affineMap_F, map_zero, Fin.sum_univ_succ] at hf
  have he : affineMap (pderiv 0 affineF) • d (affineMap (X (0 : Fin 5))) =
      -(∑ j : Fin 4, affineMap (pderiv j.succ affineF) • coordinateDifferential j) :=
    eq_neg_of_add_eq_zero_left hf.symm
  calc
    _ = (affineMap (pderiv 0 affineF))⁻¹ •
        (affineMap (pderiv 0 affineF) • d (affineMap (X (0 : Fin 5)))) := by
      rw [smul_smul, inv_mul_cancel₀ normal_ne_zero, one_smul]
    _ = _ := by
      rw [he]
      simp only [smul_neg, Finset.smul_sum, smul_smul]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← neg_smul]
      congr 1
      simp [div_eq_mul_inv, mul_comm]

theorem differential_polynomial_coordinates (P : AmbientPoly 4) :
    d (affineMap P) =
      ∑ j : Fin 4, affineTangent j (affineMap P) • coordinateDifferential j := by
  rw [differential_polynomial, Fin.sum_univ_succ, differential_normal, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [affineTangent_apply, smul_smul]
  simp only [coordinateDifferential]
  rw [← add_smul]
  congr 1
  ring

/-- The universal differential on every element of the actual chart field
is exactly its four actual implicit-coordinate partial derivatives. -/
theorem differential_coordinates (z : K) :
    d z = ∑ j : Fin 4, affineTangent j z • coordinateDifferential j := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective AffineCoordinateRing z
  obtain ⟨P, rfl⟩ := affineProjection_surjective a
  obtain ⟨T, rfl⟩ := affineProjection_surjective b
  change d (affineMap P / affineMap T) =
    ∑ j : Fin 4, affineTangent j (affineMap P / affineMap T) • coordinateDifferential j
  rw [Derivation.leibniz_div, differential_polynomial_coordinates,
    differential_polynomial_coordinates]
  simp only [Derivation.leibniz_div, Finset.smul_sum, smul_sub,
    ← Finset.sum_sub_distrib, smul_smul, smul_eq_mul, sub_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_sub, sub_smul]

/-- Evaluation of a universal differential against the four actual
complex tangent derivations. -/
def coordinateMap : Omega →ₗ[K] (Fin 4 → K) :=
  LinearMap.pi fun j => (complexTangent j).liftKaehlerDifferential

@[simp] theorem coordinateMap_d (z : K) (j : Fin 4) :
    coordinateMap (d z) j = affineTangent j z :=
  Derivation.liftKaehlerDifferential_comp_D (complexTangent j) z

@[simp] theorem coordinateMap_coordinateDifferential (i j : Fin 4) :
    coordinateMap (coordinateDifferential i) j = if i = j then 1 else 0 := by
  change coordinateMap (d (affineMap (X i.succ))) j = _
  rw [coordinateMap_d]
  exact affineTangent_coordinate j i

def coordinateExpansion : (Fin 4 → K) →ₗ[K] Omega :=
  Fintype.linearCombination K coordinateDifferential

@[simp] theorem coordinateExpansion_apply (v : Fin 4 → K) :
    coordinateExpansion v = ∑ j, v j • coordinateDifferential j := rfl

theorem coordinateExpansion_coordinateMap :
    coordinateExpansion.comp coordinateMap = LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  ext z
  change coordinateExpansion (coordinateMap (d z)) = d z
  rw [coordinateExpansion_apply]
  simp only [coordinateMap_d]
  exact (differential_coordinates z).symm

theorem coordinateMap_coordinateExpansion :
    coordinateMap.comp coordinateExpansion = LinearMap.id := by
  ext v j
  simp [coordinateExpansion_apply, coordinateMap_coordinateDifferential,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, eq_comm]

/-- Concrete coordinates on the actual relative Kähler module. -/
def differentialCoordinates : Omega ≃ₗ[K] (Fin 4 → K) where
  toLinearMap := coordinateMap
  invFun := coordinateExpansion
  left_inv z := LinearMap.congr_fun coordinateExpansion_coordinateMap z
  right_inv v := LinearMap.congr_fun coordinateMap_coordinateExpansion v

/-- The four independent coordinate differentials are a basis. -/
def coordinateBasis : Module.Basis (Fin 4) K Omega :=
  Module.Basis.ofEquivFun differentialCoordinates

@[simp] theorem coordinateBasis_apply (j : Fin 4) :
    coordinateBasis j = coordinateDifferential j := by
  rw [coordinateBasis, Module.Basis.coe_ofEquivFun]
  change coordinateExpansion (Pi.single j 1) = coordinateDifferential j
  simp [coordinateExpansion]

@[simp] theorem coordinateBasis_repr_d (z : K) (j : Fin 4) :
    coordinateBasis.repr (d z) j = affineTangent j z := by
  rw [coordinateBasis, Module.Basis.ofEquivFun_repr_apply]
  exact coordinateMap_d z j

end CycleQ2AffineDifferentials

#print axioms CycleQ2AffineDifferentials.differential_coordinates
#print axioms CycleQ2AffineDifferentials.coordinateBasis_apply
#print axioms CycleQ2AffineDifferentials.coordinateBasis_repr_d
end
end


/- Component: continuation_2/AffineExterior.lean -/
section
/-!
# Genuine exterior forms on the protected hypersurface function field

This file works with exterior powers of the actual relative Kähler module.
The coordinate exterior derivative is characterized on the exact coordinate
generators, and its top-degree exactness criterion is compared with the
already defined residue equation. It asserts no geometric vanishing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineExterior

open CycleQ2AffineDifferentials CycleQ2AffineHypersurface
open scoped BigOperators

abbrev Form (p : ℕ) := ⋀[K]^p Omega

def omitIndex (i : Fin 4) : Set.powersetCard (Fin 4) 3 :=
  ⟨{i}ᶜ, by simp [Finset.card_compl]⟩

theorem omitIndex_bijective : Function.Bijective omitIndex := by
  constructor
  · intro i j hij
    have he := congrArg (fun s : Set.powersetCard (Fin 4) 3 => (s : Finset (Fin 4))ᶜ) hij
    simpa only [omitIndex, compl_compl, Finset.singleton_inj] using he
  · intro s
    have hc : ((s : Finset (Fin 4))ᶜ).card = 1 := by
      simp [Finset.card_compl, s.property]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    refine ⟨i, Subtype.ext ?_⟩
    change {i}ᶜ = (s : Finset (Fin 4))
    rw [← hi, compl_compl]

def omitEquiv : Fin 4 ≃ Set.powersetCard (Fin 4) 3 :=
  Equiv.ofBijective omitIndex omitIndex_bijective

/-- The increasing three-fold coordinate wedges, indexed by the omitted
coordinate. This is a basis of the genuine third exterior power. -/
def thirdBasis : Module.Basis (Fin 4) K (Form 3) :=
  (coordinateBasis.exteriorPower 3).reindex omitEquiv.symm

theorem thirdBasis_apply (i : Fin 4) :
    thirdBasis i = exteriorPower.ιMulti K 3 (i.removeNth coordinateDifferential) := by
  rw [thirdBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change coordinateBasis.exteriorPower 3 (omitIndex i) = _
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  simp only [Function.comp_apply, coordinateBasis_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, omitIndex,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb, Fin.removeNth]
  rfl

/-- Canonical exterior multiplication of a one-form and a three-form. -/
def wedgeOneThree : Omega →ₗ[K] (Form 3 →ₗ[K] Form 4) :=
  exteriorPower.alternatingMapLinearEquiv.toLinearMap.comp
    (exteriorPower.ιMulti K 4).curryLeft

@[simp] theorem wedgeOneThree_wedge (a : Omega) (v : Fin 3 → Omega) :
    wedgeOneThree a (exteriorPower.ιMulti K 3 v) =
      exteriorPower.ιMulti K 4 (Matrix.vecCons a v) := by
  simp [wedgeOneThree]

@[simp] theorem wedgeOneThree_basis (a : Omega) (i : Fin 4) :
    wedgeOneThree a (thirdBasis i) =
      exteriorPower.ιMulti K 4 (Matrix.vecCons a (i.removeNth coordinateDifferential)) := by
  rw [thirdBasis_apply, wedgeOneThree_wedge]

def volume : Form 4 := exteriorPower.ιMulti K 4 coordinateDifferential

def topIndex : Set.powersetCard (Fin 4) 4 := ⟨Finset.univ, by simp⟩

theorem topIndex_unique (s : Set.powersetCard (Fin 4) 4) : s = topIndex := by
  apply Subtype.ext
  exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [s.property])

theorem topBasis_apply : coordinateBasis.exteriorPower 4 topIndex = volume := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family volume
  congr 1
  funext j
  rw [Function.comp_apply, coordinateBasis_apply]
  have ho : (fun i : Fin 4 => i) =
      (Finset.univ : Finset (Fin 4)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique _ (fun _ => Finset.mem_univ _) strictMono_id
  exact congrArg coordinateDifferential (congrFun ho j).symm

def volumeCoefficient : Form 4 →ₗ[K] K :=
  (coordinateBasis.exteriorPower 4).coord topIndex

@[simp] theorem volumeCoefficient_volume : volumeCoefficient volume = 1 := by
  rw [← topBasis_apply]
  simp [volumeCoefficient]

theorem topForm_eq_coefficient (η : Form 4) :
    η = volumeCoefficient η • volume := by
  calc
    η = ∑ s, (coordinateBasis.exteriorPower 4).repr η s •
        coordinateBasis.exteriorPower 4 s :=
      ((coordinateBasis.exteriorPower 4).sum_repr η).symm
    _ = _ := by
      rw [Finset.sum_eq_single topIndex]
      · rw [topBasis_apply]
        rfl
      · intro i hi hne
        exact (hne (topIndex_unique i)).elim
      · simp

theorem volume_ne_zero : volume ≠ 0 := by
  intro h
  have hh := volumeCoefficient_volume
  rw [h, map_zero] at hh
  exact zero_ne_one hh

/-- The exact Koszul sign of a coordinate wedge. -/
theorem wedge_coordinate_basis (j i : Fin 4) :
    wedgeOneThree (coordinateDifferential j) (thirdBasis i) =
      (if j = i then (-1 : K) ^ i.val else 0) • volume := by
  rw [wedgeOneThree_basis]
  by_cases h : j = i
  · subst j
    rw [if_pos rfl]
    have hh := (exteriorPower.ιMulti K 4).neg_one_pow_smul_map_insertNth i
      (coordinateDifferential i) (i.removeNth coordinateDifferential)
    rw [Fin.insertNth_self_removeNth] at hh
    simpa only [volume, ← Int.cast_smul_eq_zsmul K, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using hh.symm
  · rw [if_neg h, zero_smul]
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
    apply (exteriorPower.ιMulti K 4).map_eq_zero_of_eq (i := 0) (j := k.succ)
    · simp [Fin.removeNth, hk]
    · exact (Fin.succ_ne_zero k).symm

/-- The universal-property wedge agrees with multiplication in the actual
exterior algebra. -/
theorem wedgeOneThree_coe (a : Omega) (η : Form 3) :
    (wedgeOneThree a η : ExteriorAlgebra K Omega) =
      ExteriorAlgebra.ι K a * (η : ExteriorAlgebra K Omega) := by
  have he : (Form 4).subtype.comp (wedgeOneThree a) =
      (LinearMap.mulLeft K (ExteriorAlgebra.ι K a)).comp (Form 3).subtype := by
    apply thirdBasis.ext
    intro i
    change (wedgeOneThree a (thirdBasis i) : ExteriorAlgebra K Omega) =
      ExteriorAlgebra.ι K a * (thirdBasis i : ExteriorAlgebra K Omega)
    rw [wedgeOneThree_basis, thirdBasis_apply]
    change ExteriorAlgebra.ιMulti K 4
        (Matrix.vecCons a (i.removeNth coordinateDifferential)) =
      ExteriorAlgebra.ι K a * ExteriorAlgebra.ιMulti K 3 (i.removeNth coordinateDifferential)
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    rfl
  exact LinearMap.congr_fun he η

theorem wedge_d_basis (a : K) (i : Fin 4) :
    wedgeOneThree (d a) (thirdBasis i) =
      ((-1 : K) ^ i.val * affineTangent i a) • volume := by
  rw [differential_coordinates, map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    wedge_coordinate_basis, smul_smul]
  simp [mul_comm]

/-- The algebraic exterior differential in degree three, written in the
basis of exact coordinate wedges. It is complex-linear, not K-linear. -/
def exteriorD3 : Form 3 →ₗ[ℂ] Form 4 :=
  ∑ i : Fin 4,
    ((LinearMap.toSpanSingleton K (Form 4) ((-1 : K) ^ i.val • volume)).restrictScalars ℂ).comp
      ((complexTangent i).toLinearMap.comp ((thirdBasis.coord i).restrictScalars ℂ))

theorem exteriorD3_apply (η : Form 3) :
    exteriorD3 η =
      (∑ i : Fin 4, (-1 : K) ^ i.val * affineTangent i (thirdBasis.repr η i)) • volume := by
  simp only [exteriorD3, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply,
    Module.Basis.coord_apply, Derivation.coeFn_coe, complexTangent_apply,
    smul_smul, ← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The coordinate definition is the usual differential of a scalar times
a wedge of exact coordinate differentials. -/
theorem exteriorD3_smul_basis (a : K) (i : Fin 4) :
    exteriorD3 (a • thirdBasis i) = wedgeOneThree (d a) (thirdBasis i) := by
  rw [exteriorD3_apply, wedge_d_basis]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, hji, Ne.symm hji]
  · simp

@[simp] theorem exteriorD3_basis (i : Fin 4) : exteriorD3 (thirdBasis i) = 0 := by
  simpa only [one_smul, Derivation.map_one_eq_zero, map_zero, LinearMap.zero_apply] using
    exteriorD3_smul_basis 1 i

theorem exteriorD3_eq_sum_wedge (η : Form 3) :
    exteriorD3 η =
      ∑ i : Fin 4, wedgeOneThree (d (thirdBasis.repr η i)) (thirdBasis i) := by
  rw [exteriorD3_apply]
  simp only [wedge_d_basis, Finset.sum_smul]

/-- The actual scalar Leibniz rule for this exterior differential. -/
theorem exteriorD3_leibniz (a : K) (η : Form 3) :
    exteriorD3 (a • η) = wedgeOneThree (d a) η + a • exteriorD3 η := by
  have hh := congrArg (wedgeOneThree (d a)) (thirdBasis.sum_repr η)
  simp only [map_sum, map_smul] at hh
  rw [exteriorD3_eq_sum_wedge]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Derivation.leibniz,
    map_add, LinearMap.add_apply, LinearMap.smul_apply, Finset.sum_add_distrib]
  rw [← Finset.smul_sum, ← exteriorD3_eq_sum_wedge, hh]
  exact add_comm _ _

/-- The scalar-times-generator formula uniquely determines the exterior
differential on the genuine third exterior power. -/
theorem exteriorD3_unique (δ : Form 3 →ₗ[ℂ] Form 4)
    (hδ : ∀ (a : K) (i : Fin 4),
      δ (a • thirdBasis i) = wedgeOneThree (d a) (thirdBasis i)) :
    δ = exteriorD3 := by
  apply LinearMap.ext
  intro η
  calc
    δ η = δ (∑ i, thirdBasis.repr η i • thirdBasis i) :=
      congrArg δ (thirdBasis.sum_repr η).symm
    _ = ∑ i, wedgeOneThree (d (thirdBasis.repr η i)) (thirdBasis i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact hδ _ i
    _ = exteriorD3 η := (exteriorD3_eq_sum_wedge η).symm

end CycleQ2AffineExterior

#print axioms CycleQ2AffineExterior.thirdBasis_apply
#print axioms CycleQ2AffineExterior.topForm_eq_coefficient
#print axioms CycleQ2AffineExterior.wedge_coordinate_basis
#print axioms CycleQ2AffineExterior.exteriorD3_smul_basis
#print axioms CycleQ2AffineExterior.exteriorD3_leibniz
#print axioms CycleQ2AffineExterior.exteriorD3_unique
end
end


