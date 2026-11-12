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
import Proposal.GeometricFormalInputs02

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


/- Component: continuation_2/AffineExactnessCriterion.lean -/
section
/-!
# Actual top-form exactness is equivalent to the protected residue PDE

Write g for the nonzero normal derivative and c for the actual second normal
source. The residue source is the genuine top exterior form (c/g) dx1∧⋯∧dx4.
The three-form with coefficients (-1)^i w_i/g has derivative
(residueDivergence w/g) dx1∧⋯∧dx4. Thus a solved PDE c+div_g(w)=0 makes its
negative a primitive of the positive source form. No exactness is assumed
without appearing explicitly as a hypothesis in the final implication.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2AffineExactness

open MvPolynomial HodgeComputer CycleQ2AffineDifferentials CycleQ2AffineExterior
open CycleQ2AffineHypersurface CycleQ2AffineClearing CycleQ2AffineResidueClosure
open HoldoutConstruction
open scoped BigOperators

local instance intAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

def normalDensity : K := affineMap (pderiv 0 affineF)

theorem normalDensity_ne_zero : normalDensity ≠ 0 := normal_ne_zero

def coordinateSign (i : Fin 4) : K := (-1 : K) ^ i.val

theorem coordinateSign_mul_self (i : Fin 4) :
    coordinateSign i * coordinateSign i = 1 := by
  unfold coordinateSign
  rw [← pow_add, show i.val + i.val = 2 * i.val by omega, pow_mul]
  simp

@[simp] theorem tangent_coordinateSign (j i : Fin 4) :
    affineTangent j (coordinateSign i) = 0 := by
  simp only [coordinateSign, Derivation.leibniz_pow, map_neg,
    Derivation.map_one_eq_zero, neg_zero, smul_zero]

def signedCoefficients (η : Form 3) (i : Fin 4) : K :=
  coordinateSign i * thirdBasis.repr η i

def densityVector (η : Form 3) (i : Fin 4) : K :=
  normalDensity * signedCoefficients η i

theorem exteriorD3_as_divergence (η : Form 3) :
    exteriorD3 η = fieldDivergence affineTangent (signedCoefficients η) • volume := by
  rw [exteriorD3_apply]
  congr 1
  unfold fieldDivergence signedCoefficients
  apply Finset.sum_congr rfl
  intro i hi
  rw [Derivation.leibniz, tangent_coordinateSign]
  simp only [smul_eq_mul, mul_zero, add_zero, coordinateSign]

theorem densityVector_residueDivergence (η : Form 3) :
    residueDivergence affineTangent normalDensity (densityVector η) =
      normalDensity * fieldDivergence affineTangent (signedCoefficients η) :=
  residueDivergence_cancel_density affineTangent normalDensity normalDensity_ne_zero _

theorem volumeCoefficient_exteriorD3 (η : Form 3) :
    volumeCoefficient (exteriorD3 η) = fieldDivergence affineTangent (signedCoefficients η) := by
  rw [exteriorD3_as_divergence, map_smul, volumeCoefficient_volume, smul_eq_mul, mul_one]

/-- The actual source top-form, with the positive residue sign. -/
def residueSourceForm (A : AmbientPoly 4) : Form 4 :=
  (affineNormalSource A / normalDensity) • volume

@[simp] theorem volumeCoefficient_residueSourceForm (A : AmbientPoly 4) :
    volumeCoefficient (residueSourceForm A) = affineNormalSource A / normalDensity := by
  simp [residueSourceForm]

/-- The explicit three-form whose coordinate coefficients are (-1)^i w_i/g. -/
def residuePrimitiveForm (w : Fin 4 → K) : Form 3 :=
  thirdBasis.equivFun.symm (fun i => coordinateSign i * (w i / normalDensity))

@[simp] theorem residuePrimitiveForm_repr (w : Fin 4 → K) (i : Fin 4) :
    thirdBasis.repr (residuePrimitiveForm w) i =
      coordinateSign i * (w i / normalDensity) := by
  change thirdBasis.coord i (thirdBasis.equivFun.symm _) = _
  exact Module.Basis.coord_equivFun_symm thirdBasis i _

theorem densityVector_residuePrimitiveForm (w : Fin 4 → K) :
    densityVector (residuePrimitiveForm w) = w := by
  funext i
  simp only [densityVector, signedCoefficients, residuePrimitiveForm_repr]
  rw [← mul_assoc (coordinateSign i), coordinateSign_mul_self, one_mul]
  field_simp [normalDensity_ne_zero]

theorem residuePrimitiveForm_densityVector (η : Form 3) :
    residuePrimitiveForm (densityVector η) = η := by
  apply thirdBasis.repr.injective
  ext i
  rw [residuePrimitiveForm_repr]
  simp only [densityVector, signedCoefficients]
  rw [mul_div_cancel_left₀ _ normalDensity_ne_zero,
    ← mul_assoc, coordinateSign_mul_self, one_mul]

/-- Exact identity between the genuine exterior derivative and the existing
weighted residue divergence. -/
theorem exteriorD3_residuePrimitiveForm (w : Fin 4 → K) :
    exteriorD3 (residuePrimitiveForm w) =
      (residueDivergence affineTangent normalDensity w / normalDensity) • volume := by
  have hd := densityVector_residueDivergence (residuePrimitiveForm w)
  rw [densityVector_residuePrimitiveForm] at hd
  rw [exteriorD3_as_divergence]
  congr 1
  apply (eq_div_iff normalDensity_ne_zero).mpr
  simpa only [mul_comm] using hd.symm

theorem affineResidueExpression_densityVector (A : AmbientPoly 4) (η : Form 3) :
    affineResidueExpression A (densityVector η) =
      affineNormalSource A + normalDensity * volumeCoefficient (exteriorD3 η) := by
  change affineNormalSource A +
    residueDivergence affineTangent normalDensity (densityVector η) = _
  rw [densityVector_residueDivergence, volumeCoefficient_exteriorD3]

/-- The sign convention is explicit: a zero residue PDE gives the negative
of the positive source form as the derivative of `residuePrimitiveForm w`. -/
theorem exteriorD3_residuePrimitiveForm_add_source (A : AmbientPoly 4) (w : Fin 4 → K) :
    exteriorD3 (residuePrimitiveForm w) + residueSourceForm A =
      (affineResidueExpression A w / normalDensity) • volume := by
  rw [exteriorD3_residuePrimitiveForm, residueSourceForm, ← add_smul]
  change (residueDivergence affineTangent normalDensity w / normalDensity +
    affineNormalSource A / normalDensity) • volume =
      ((affineNormalSource A + residueDivergence affineTangent normalDensity w) /
        normalDensity) • volume
  congr 1
  ring

/-- Genuine exactness of the actual top exterior source is equivalent to
the already defined concrete residue PDE. Neither side is asserted here. -/
theorem exact_residueSourceForm_iff (A : AmbientPoly 4) :
    (∃ η : Form 3, exteriorD3 η = residueSourceForm A) ↔
      ∃ w : Fin 4 → K, affineResidueExpression A w = 0 := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨densityVector (-η), ?_⟩
    rw [affineResidueExpression_densityVector, map_neg, hη, map_neg,
      volumeCoefficient_residueSourceForm]
    field_simp [normalDensity_ne_zero]
    ring
  · rintro ⟨w, hw⟩
    have hh := exteriorD3_residuePrimitiveForm_add_source A w
    rw [hw, zero_div, zero_smul] at hh
    refine ⟨-residuePrimitiveForm w, ?_⟩
    rw [map_neg, eq_neg_of_add_eq_zero_left hh, neg_neg]

/-- Actual exterior-form exactness now implies the unchanged protected
certificate through the proved residue, chart, and denominator constructions. -/
theorem protected_certificate_of_exact_residueSourceForm
    (h : ∃ η : Form 3, exteriorD3 η = residueSourceForm affineA) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  protected_certificate_of_affine_residue_primitive ((exact_residueSourceForm_iff affineA).mp h)

end CycleQ2AffineExactness

#print axioms CycleQ2AffineExactness.exteriorD3_residuePrimitiveForm_add_source
#print axioms CycleQ2AffineExactness.exact_residueSourceForm_iff
#print axioms CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
end
end


/- Component: continuation_2/VeryGeneralPoint.lean -/
section
/-!
Actual very-general-point selection in affine coefficient spaces.

The countable-proper-image specialization argument requires a complex point
outside countably many proper algebraic conditions. This module proves that
selection statement for genuine polynomial equations. It does not assert
that any moving cycle, supported projector, or primitive exists.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2VeryGeneral

open MvPolynomial

variable {K : Type*} [Field K] [Uncountable K]

theorem exists_avoiding_univariate {ι : Type*} [Countable ι]
    (p : ι → Polynomial K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : K, ∀ i, (p i).eval x ≠ 0 := by
  classical
  let roots : ι → Set K := fun i => {x | (p i).eval x = 0}
  have hroots (i : ι) : (roots i).Finite := by
    simpa only [roots, Polynomial.IsRoot] using
      (Polynomial.finite_setOfPred_isRoot (hp i))
  have hcount : (⋃ i, roots i).Countable :=
    Set.countable_iUnion (fun i => (hroots i).countable)
  have hout : ∃ x : K, x ∉ ⋃ i, roots i := by
    by_contra h
    push Not at h
    have heq : (⋃ i, roots i) = Set.univ := Set.eq_univ_of_forall h
    exact Set.not_countable_univ (heq ▸ hcount)
  obtain ⟨x, hx⟩ := hout
  refine ⟨x, fun i hi => hx ?_⟩
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Countably many genuine nonzero multivariate polynomials have a common
nonvanishing point over an uncountable field. -/
theorem exists_avoiding_polynomials (n : ℕ) {ι : Type*} [Countable ι]
    (p : ι → MvPolynomial (Fin n) K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : Fin n → K, ∀ i, eval x (p i) ≠ 0 := by
  classical
  induction n with
  | zero =>
      refine ⟨Fin.elim0, ?_⟩
      intro i hi
      obtain ⟨c, hc⟩ := (isEmptyAlgEquiv K (Fin 0)).symm.surjective (p i)
      have hpi : p i = C c := by simpa using hc.symm
      rw [hpi, eval_C] at hi
      exact hp i (by simp [hpi, hi])
  | succ n ih =>
      let q : ι → Polynomial (MvPolynomial (Fin n) K) :=
        fun i => finSuccEquiv K n (p i)
      have hq (i : ι) : q i ≠ 0 := by
        intro hz
        apply hp i
        apply (finSuccEquiv K n).injective
        simpa only [q, map_zero] using hz
      have hlc (i : ι) : (q i).leadingCoeff ≠ 0 := by
        simpa only [ne_eq, Polynomial.leadingCoeff_eq_zero] using hq i
      obtain ⟨y, hy⟩ := ih (fun i => (q i).leadingCoeff) hlc
      let s : ι → Polynomial K := fun i => (q i).map (eval y)
      have hs (i : ι) : s i ≠ 0 := by
        intro hz
        have hc := congrArg (fun z : Polynomial K => z.coeff (q i).natDegree) hz
        simp only [s, Polynomial.coeff_map, Polynomial.coeff_zero] at hc
        exact hy i hc
      obtain ⟨x, hx⟩ := exists_avoiding_univariate s hs
      refine ⟨Fin.cons x y, ?_⟩
      intro i
      simpa only [eval_eq_eval_mv_eval', q, s] using hx i

/-- A very general complex coefficient point can also be required to lie in
any prescribed nonempty principal open, without a coefficient bound. -/
theorem complex_point_in_principal_open_avoiding (n : ℕ)
    {ι : Type*} [Countable ι] (g : MvPolynomial (Fin n) ℂ) (hg : g ≠ 0)
    (p : ι → MvPolynomial (Fin n) ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ x : Fin n → ℂ, eval x g ≠ 0 ∧ ∀ i, eval x (p i) ≠ 0 := by
  letI : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  let family : Option ι → MvPolynomial (Fin n) ℂ := fun i => Option.elim i g p
  have hn (i : Option ι) : family i ≠ 0 := by
    cases i with
    | none => exact hg
    | some i => exact hp i
  obtain ⟨x, hx⟩ := exists_avoiding_polynomials n family hn
  exact ⟨x, hx none, fun i => hx (some i)⟩

/-- A countable family of genuine affine algebraic zero loci covering a
nonempty principal open has a member equal to the whole affine space.
This is the countability step in proper-image specialization, without any
assumed existence of projectors or cycle families. -/
theorem complex_countable_algebraic_cover (n : ℕ)
    {ι : Type*} [Countable ι]
    (I : ι → Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin n) ℂ) (hg : g ≠ 0)
    (hcover : ∀ x : Fin n → ℂ, eval x g ≠ 0 →
      ∃ i, x ∈ zeroLocus ℂ (I i)) :
    ∃ i, zeroLocus ℂ (I i) = Set.univ := by
  classical
  by_contra h
  push Not at h
  have hn (i : ι) : I i ≠ ⊥ := by
    intro hi
    apply h i
    simp only [hi, zeroLocus_bot, Set.top_eq_univ]
  have hp (i : ι) : ∃ p : MvPolynomial (Fin n) ℂ, p ∈ I i ∧ p ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hn i
    apply le_antisymm
    · intro p hp
      exact (Ideal.mem_bot).mpr (hh p hp)
    · exact bot_le
  choose p hpI hpne using hp
  obtain ⟨x, hxg, hxp⟩ := complex_point_in_principal_open_avoiding n g hg p hpne
  obtain ⟨i, hxi⟩ := hcover x hxg
  apply hxp i
  exact hxi (p i) (hpI i)

end CycleQ2VeryGeneral

#print axioms CycleQ2VeryGeneral.exists_avoiding_polynomials
#print axioms CycleQ2VeryGeneral.complex_point_in_principal_open_avoiding
#print axioms CycleQ2VeryGeneral.complex_countable_algebraic_cover
end
end


/- Component: continuation_2/AffineFormalSpecialization.lean -/
section
/-!
An actual formal neighborhood of the protected affine hypersurface.

The normal derivative is already proved nonzero in its function field. Hensel's
lemma therefore solves the exact one-parameter deformation in that function
field's power series ring. This is a specialization tool: it does not turn a
formal primitive at the Fermat member into a rational primitive of the family.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace CycleQ2FormalSpecialization

open scoped PowerSeries

/-- Hensel lifting written with the actual constant-coefficient specialization.
No algebraicity or rationality of the resulting power series is inferred. -/
theorem simple_root_lifts {k : Type*} [Field k]
    (p : Polynomial (PowerSeries k)) (hp : p.Monic) (a : k)
    (ha : p.eval₂ (PowerSeries.constantCoeff (R := k)) a = 0)
    (hderiv : p.derivative.eval₂ (PowerSeries.constantCoeff (R := k)) a ≠ 0) :
    ∃ z : PowerSeries k, p.eval z = 0 ∧ z.constantCoeff = a := by
  let I : Ideal (PowerSeries k) := Ideal.span {PowerSeries.X}
  have hmem : p.eval (PowerSeries.C a) ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simpa only [← Polynomial.eval₂_at_apply, PowerSeries.constantCoeff_C] using ha
  have hu : IsUnit (p.derivative.eval (PowerSeries.C a)) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    apply isUnit_iff_ne_zero.mpr
    simpa only [← Polynomial.eval₂_at_apply, PowerSeries.constantCoeff_C] using hderiv
  obtain ⟨z, hz, hza⟩ := HenselianRing.is_henselian p hp (PowerSeries.C a)
    hmem (hu.map (Ideal.Quotient.mk I))
  refine ⟨z, hz, ?_⟩
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] at hza
  simpa only [map_sub, PowerSeries.constantCoeff_C, sub_eq_zero] using hza

open MvPolynomial CycleQ2AffineClearing CycleQ2AffineGeometry
  CycleQ2AffineHypersurface

abbrev K := AffineFunctionField

def fieldCoordinate (i : Fin 5) : K := affineMap (MvPolynomial.X i)

/-- The family parameter is zero at the protected target and minus one at
the Fermat polynomial. The eliminated coordinate is the polynomial variable;
the other four coordinates are constants in the actual function field. -/
def targetFamily : Polynomial (PowerSeries K) :=
  Polynomial.X ^ 6 +
    Polynomial.C (PowerSeries.C (1 + fieldCoordinate 1 ^ 6 +
      fieldCoordinate 2 ^ 6 + fieldCoordinate 3 ^ 6 + fieldCoordinate 4 ^ 6)) +
    Polynomial.C (PowerSeries.C (1 / 2 : K) * (1 + PowerSeries.X)) *
      (Polynomial.X * Polynomial.C (PowerSeries.C (fieldCoordinate 2 * fieldCoordinate 3)) +
        Polynomial.X ^ 3 * Polynomial.C (PowerSeries.C
          (fieldCoordinate 1 * fieldCoordinate 3 * fieldCoordinate 4)) +
        Polynomial.C (PowerSeries.C
          (fieldCoordinate 1 ^ 3 * fieldCoordinate 4 * fieldCoordinate 2)))

theorem targetFamily_monic : targetFamily.Monic := by
  unfold targetFamily
  rw [add_assoc]
  apply Polynomial.monic_X_pow_add
  compute_degree!

theorem targetFamily_specializes :
    targetFamily.eval₂ (PowerSeries.constantCoeff (R := K)) (fieldCoordinate 0) = 0 := by
  have hc (c : ℂ) : affineMap (MvPolynomial.C c) = algebraMap ℂ K c := rfl
  have h := congrArg affineMap affineF_formula
  simp only [affineMap_F, map_add, map_mul, map_pow, map_one, hc] at h
  norm_num only [map_div₀, map_one, map_ofNat] at h
  convert h.symm using 1 <;> norm_num only [targetFamily, fieldCoordinate,
    Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one, map_add, map_mul,
    map_one, map_zero, map_pow, map_ofNat, PowerSeries.constantCoeff_C,
    PowerSeries.constantCoeff_X] <;> ring

theorem targetFamily_simple :
    targetFamily.derivative.eval₂ (PowerSeries.constantCoeff (R := K))
      (fieldCoordinate 0) ≠ 0 := by
  have hc (c : ℂ) : affineMap (MvPolynomial.C c) = algebraMap ℂ K c := rfl
  have h := congrArg (fun P => affineMap (MvPolynomial.pderiv 0 P)) affineF_formula
  norm_num [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_X, Pi.single_apply, Fin.ext_iff, hc] at h
  have hn := normal_ne_zero
  rw [h] at hn
  convert hn using 1 <;>
    norm_num [targetFamily, fieldCoordinate, Polynomial.derivative_add,
      Polynomial.derivative_mul, Polynomial.derivative_pow,
      Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C] <;> simp only [map_ofNat] <;> ring

/-- The protected hypersurface has a genuine formal solution along the
specified deformation, with its original coordinate as constant coefficient. -/
theorem exists_target_formal_coordinate :
    ∃ z : PowerSeries K, targetFamily.eval z = 0 ∧
      z.constantCoeff = fieldCoordinate 0 :=
  simple_root_lifts targetFamily targetFamily_monic (fieldCoordinate 0)
    targetFamily_specializes targetFamily_simple

end CycleQ2FormalSpecialization

#print axioms CycleQ2FormalSpecialization.simple_root_lifts
#print axioms CycleQ2FormalSpecialization.exists_target_formal_coordinate
end
end


/- Component: continuation_2/LaurentCoefficientDerivations.lean -/
section
/-!
Coefficientwise derivations and exactness under formal Laurent extension.

The exponent is a deformation parameter, not a coordinate to differentiate.
The actual Hahn-series multiplication is used in the Leibniz proof. Taking
any Laurent coefficient commutes with these derivations, including for
series with negative powers. Consequently a Laurent primitive specializes
coefficientwise; no converse from formal deformation to a rational primitive
of a generic algebraic family is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2LaurentDerivation

open scoped BigOperators

variable {C K : Type*} [CommRing C] [CommRing K] [Algebra C K]

abbrev Series := HahnSeries ℤ K

/-- Use the coefficient algebra explicitly. The power-series imports also
provide a compatible algebra through the power-series embedding; fixing
this instance keeps the scalar action definitionally coefficientwise. -/
local instance coefficientAlgebra : Algebra C (Series (K := K)) :=
  HahnSeries.instAlgebra

def coefficientwise (D : Derivation C K K) (s : Series (K := K)) : Series (K := K) where
  coeff n := D (s.coeff n)
  isPWO_support' := s.isPWO_support.mono (by
    intro n hn hzero
    exact hn (by simp only [hzero, map_zero]))

@[simp] theorem coefficientwise_coeff (D : Derivation C K K) (s : Series (K := K)) (n : ℤ) :
    (coefficientwise D s).coeff n = D (s.coeff n) := rfl

theorem support_coefficientwise_subset (D : Derivation C K K) (s : Series (K := K)) :
    (coefficientwise D s).support ⊆ s.support := by
  intro n hn hzero
  exact hn (by simp only [coefficientwise_coeff, hzero, map_zero])

theorem coefficientwise_mul (D : Derivation C K K) (s t : Series (K := K)) :
    coefficientwise D (s * t) = s * coefficientwise D t + t * coefficientwise D s := by
  ext n
  rw [coefficientwise_coeff, HahnSeries.coeff_mul, map_sum, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_right' t.isPWO_support (support_coefficientwise_subset D t),
    mul_comm t (coefficientwise D s),
    HahnSeries.coeff_mul_left' s.isPWO_support (support_coefficientwise_subset D s)]
  simp only [Derivation.leibniz, smul_eq_mul, coefficientwise_coeff, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  exact mul_comm _ _

/-- An actual derivation of the Laurent-series ring, obtained by applying the
coefficient derivation while keeping the formal parameter constant. -/
def extend (D : Derivation C K K) : Derivation C (Series (K := K)) (Series (K := K)) where
  toFun := coefficientwise D
  map_add' s t := by
    ext n
    simp
  map_smul' c s := by
    ext n
    simp only [coefficientwise_coeff, HahnSeries.coeff_smul,
      RingHom.id_apply, Derivation.map_smul]
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [HahnSeries.coeff_one, hn]
  leibniz' s t := by
    change coefficientwise D (s * t) = s * coefficientwise D t + t * coefficientwise D s
    exact coefficientwise_mul D s t

@[simp] theorem extend_coeff (D : Derivation C K K) (s : Series (K := K)) (n : ℤ) :
    (extend D s).coeff n = D (s.coeff n) := rfl

theorem extend_commute (D E : Derivation C K K) (h : Function.Commute D E) :
    Function.Commute (extend D) (extend E) := by
  intro s
  ext n
  exact h (s.coeff n)

@[simp] theorem extend_single (D : Derivation C K K) (n : ℤ) (a : K) :
    extend D (HahnSeries.single n a) = HahnSeries.single n (D a) := by
  ext j
  by_cases hj : j = n <;> simp [hj]

/-- Coefficient extraction is a left inverse on exactness, even when a
primitive has a pole in the deformation parameter. -/
theorem divergence_coefficient {ι : Type*} [Fintype ι]
    (D : ι → Derivation C K K) (v : ι → Series (K := K)) (b : Series (K := K))
    (h : (∑ i, extend (D i) (v i)) = b) (n : ℤ) :
    (∑ i, D i ((v i).coeff n)) = b.coeff n := by
  have hc := congrArg (fun s : Series (K := K) => s.coeff n) h
  simpa only [HahnSeries.coeff_sum, extend_coeff] using hc

/-- Extending the coefficient field to formal Laurent series cannot make a
constant source exact unless it was already exact over the original ring. -/
theorem exists_divergence_constant_iff {ι : Type*} [Fintype ι]
    (D : ι → Derivation C K K) (b : K) :
    (∃ v : ι → Series (K := K), ∑ i, extend (D i) (v i) = HahnSeries.single 0 b) ↔
      ∃ v : ι → K, ∑ i, D i (v i) = b := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨fun i => (v i).coeff 0, ?_⟩
    simpa using divergence_coefficient D v _ hv 0
  · rintro ⟨v, hv⟩
    refine ⟨fun i => HahnSeries.single 0 (v i), ?_⟩
    simp_rw [extend_single]
    change (∑ i, HahnSeries.single.addMonoidHom 0 (D i (v i))) =
      HahnSeries.single.addMonoidHom 0 b
    rw [← map_sum (HahnSeries.single.addMonoidHom 0), hv]

end CycleQ2LaurentDerivation

#print axioms CycleQ2LaurentDerivation.extend
#print axioms CycleQ2LaurentDerivation.divergence_coefficient
#print axioms CycleQ2LaurentDerivation.exists_divergence_constant_iff
end
end


/- Component: continuation_2/AffineNormalExpansion.lean -/
section
/-!
The actual normal formal coordinate at the generic point of f=0.

We solve f(x0(T),x1,...,x4)=T in K[[T]], prove that its constant-coefficient
map is the actual residue map on polynomials, and prove injectivity of the
resulting polynomial substitution. The formal derivative satisfies the
actual normal chain rule. These are local algebraic facts, independent of
any assertion that the target residue is exact.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2NormalExpansion

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineGeometry
  CycleQ2AffineHypersurface CycleQ2FormalSpecialization

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

def normalEquation : Polynomial S :=
  Polynomial.X ^ 6 +
    (Polynomial.C (PowerSeries.C (1 + fieldCoordinate 1 ^ 6 +
      fieldCoordinate 2 ^ 6 + fieldCoordinate 3 ^ 6 + fieldCoordinate 4 ^ 6)) +
      Polynomial.C (PowerSeries.C (1 / 2 : K)) *
        (Polynomial.X * Polynomial.C (PowerSeries.C (fieldCoordinate 2 * fieldCoordinate 3)) +
          Polynomial.X ^ 3 * Polynomial.C (PowerSeries.C
            (fieldCoordinate 1 * fieldCoordinate 3 * fieldCoordinate 4)) +
          Polynomial.C (PowerSeries.C
            (fieldCoordinate 1 ^ 3 * fieldCoordinate 4 * fieldCoordinate 2))) -
      Polynomial.C PowerSeries.X)

theorem normalEquation_monic : normalEquation.Monic := by
  unfold normalEquation
  apply Polynomial.monic_X_pow_add
  compute_degree!

theorem normalEquation_specializes :
    normalEquation.eval₂ (PowerSeries.constantCoeff (R := K)) (fieldCoordinate 0) = 0 := by
  convert targetFamily_specializes using 1 <;>
    simp [normalEquation, targetFamily] <;> ring

theorem normalEquation_simple :
    normalEquation.derivative.eval₂ (PowerSeries.constantCoeff (R := K))
      (fieldCoordinate 0) ≠ 0 := by
  convert targetFamily_simple using 1 <;>
    simp [normalEquation, targetFamily, Polynomial.derivative_pow]

theorem normal_root_exists :
    ∃ z : S, normalEquation.eval z = 0 ∧ z.constantCoeff = fieldCoordinate 0 :=
  simple_root_lifts normalEquation normalEquation_monic (fieldCoordinate 0)
    normalEquation_specializes normalEquation_simple

def normalRoot : S := Classical.choose normal_root_exists

theorem normalRoot_equation : normalEquation.eval normalRoot = 0 :=
  (Classical.choose_spec normal_root_exists).1

@[simp] theorem normalRoot_constantCoeff :
    normalRoot.constantCoeff = fieldCoordinate 0 :=
  (Classical.choose_spec normal_root_exists).2

def normalCoordinates : Fin 5 → S :=
  Fin.cases normalRoot (fun j => PowerSeries.C (fieldCoordinate j.succ))

def normalExpansion : AmbientPoly 4 →+* S :=
  MvPolynomial.eval₂Hom (PowerSeries.C.comp (affineMap.comp MvPolynomial.C)) normalCoordinates

@[simp] theorem normalExpansion_C (c : ℂ) :
    normalExpansion (MvPolynomial.C c) = PowerSeries.C (affineMap (MvPolynomial.C c)) := by
  simp [normalExpansion]

@[simp] theorem normalExpansion_X_zero :
    normalExpansion (MvPolynomial.X (0 : Fin 5)) = normalRoot := by
  simp [normalExpansion, normalCoordinates]

@[simp] theorem normalExpansion_X_succ (j : Fin 4) :
    normalExpansion (MvPolynomial.X j.succ) = PowerSeries.C (fieldCoordinate j.succ) := by
  simp [normalExpansion, normalCoordinates]

/-- The constant coefficient is exactly the previously constructed quotient
map into the protected hypersurface function field, on every polynomial. -/
theorem constantCoeff_normalExpansion (P : AmbientPoly 4) :
    (normalExpansion P).constantCoeff = affineMap P := by
  have h : (PowerSeries.constantCoeff (R := K)).comp normalExpansion = affineMap := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [fieldCoordinate]
      · simp [fieldCoordinate]
  exact RingHom.congr_fun h P

/-- The normal parameter is the actual protected equation f. -/
theorem normalExpansion_F : normalExpansion affineF = PowerSeries.X := by
  have hf := congrArg normalExpansion affineF_formula
  have hr := normalRoot_equation
  have hc : normalExpansion (MvPolynomial.C (1 / 2 : ℂ)) =
      PowerSeries.C (1 / 2 : K) := by
    rw [normalExpansion_C]
    congr 1
    change (affineMap.comp MvPolynomial.C) (1 / 2 : ℂ) = _
    rw [map_div₀, map_one, map_ofNat]
  norm_num [normalEquation, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hr
  simp only [map_add, map_mul, map_pow, map_one, hc] at hf
  have h1 : normalExpansion (MvPolynomial.X (1 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 1) := normalExpansion_X_succ 0
  have h2 : normalExpansion (MvPolynomial.X (2 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 2) := normalExpansion_X_succ 1
  have h3 : normalExpansion (MvPolynomial.X (3 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 3) := normalExpansion_X_succ 2
  have h4 : normalExpansion (MvPolynomial.X (4 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 4) := normalExpansion_X_succ 3
  rw [hf]
  simp only [normalExpansion_X_zero, h1, h2, h3, h4]
  change 1 + normalRoot ^ 6 + PowerSeries.C (fieldCoordinate 1) ^ 6 +
    PowerSeries.C (fieldCoordinate 2) ^ 6 + PowerSeries.C (fieldCoordinate 3) ^ 6 +
    PowerSeries.C (fieldCoordinate 4) ^ 6 +
      PowerSeries.C (1 / 2 : K) *
        (normalRoot * PowerSeries.C (fieldCoordinate 2) * PowerSeries.C (fieldCoordinate 3) +
          normalRoot ^ 3 * PowerSeries.C (fieldCoordinate 1) *
            PowerSeries.C (fieldCoordinate 3) * PowerSeries.C (fieldCoordinate 4) +
          PowerSeries.C (fieldCoordinate 1) ^ 3 * PowerSeries.C (fieldCoordinate 4) *
            PowerSeries.C (fieldCoordinate 2)) = _
  simp only [one_div]
  linear_combination hr

theorem normalExpansion_injective : Function.Injective normalExpansion := by
  have hnonzero (P : AmbientPoly 4) (hP : P ≠ 0) : normalExpansion P ≠ 0 := by
    obtain ⟨m, U, hFU, hfactor⟩ := WfDvdMonoid.max_power_factor hP affineF_irreducible
    have hU : normalExpansion U ≠ 0 := by
      intro h
      have hc := congrArg (PowerSeries.constantCoeff (R := K)) h
      rw [constantCoeff_normalExpansion, map_zero] at hc
      exact hFU ((affineMap_kernel U).mp hc)
    rw [hfactor, map_mul, map_pow, normalExpansion_F]
    exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) hU
  intro P Q h
  by_contra hn
  exact hnonzero (P - Q) (sub_ne_zero.mpr hn) (by rw [map_sub, h, sub_self])

abbrev Dt : Derivation K S S := PowerSeries.derivative K

def normalVelocity : S := Dt normalRoot

/-- Chain rule for every polynomial under the actual formal normal chart. -/
theorem normalExpansion_chain_rule (P : AmbientPoly 4) :
    Dt (normalExpansion P) = normalExpansion (pderiv 0 P) * normalVelocity := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [Dt]
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ, add_mul]
  | mul_X P i ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [map_mul, Derivation.leibniz, normalExpansion_X_zero, ih,
          normalVelocity, pderiv_mul, pderiv_X_self, mul_one, map_add,
          smul_eq_mul]
        ring
      · simp only [map_mul, Derivation.leibniz, normalExpansion_X_succ, ih,
          pderiv_mul, pderiv_X, Pi.single_apply, Fin.succ_ne_zero,
          if_false, mul_zero, add_zero, map_add, map_zero, smul_eq_mul,
          PowerSeries.derivative_C, mul_zero, zero_add]
        ring

theorem normal_velocity_identity :
    normalExpansion (pderiv 0 affineF) * normalVelocity = 1 := by
  have h := normalExpansion_chain_rule affineF
  rw [normalExpansion_F, PowerSeries.derivative_X] at h
  exact h.symm

end CycleQ2NormalExpansion

#print axioms CycleQ2NormalExpansion.normalExpansion_F
#print axioms CycleQ2NormalExpansion.normalExpansion_injective
#print axioms CycleQ2NormalExpansion.normalExpansion_chain_rule
#print axioms CycleQ2NormalExpansion.normal_velocity_identity
end
end


/- Component: continuation_2/AffineFormalResidue.lean -/
section
/-!
The actual pole-three residue coefficient in a genuine formal normal chart.

The normal chart sends f to T and holds the four other coordinates fixed.
Its Jacobian in the normal direction is dx0/dT. We prove that the T^(-1)
coefficient of A(x(T)) (dx0/dT) / T^3 is precisely the previously defined
normal source divided by g. This supplies the local residue calculation;
it does not assert geometric support or global de Rham vanishing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace CycleQ2FormalResidue

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineResidueClosure CycleQ2NormalExpansion HoldoutConstruction
open SplitHigherResidue

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

def normalG : K := affineMap (pderiv 0 affineF)
def normalG1 : K := affineMap (pderiv 0 (pderiv 0 affineF))
def normalG2 : K := affineMap (pderiv 0 (pderiv 0 (pderiv 0 affineF)))

theorem normalG_ne_zero : normalG ≠ 0 := normal_ne_zero

theorem velocity_first_identity :
    normalExpansion (pderiv 0 (pderiv 0 affineF)) * normalVelocity ^ 2 +
      normalExpansion (pderiv 0 affineF) * Dt normalVelocity = 0 := by
  have h := congrArg Dt normal_velocity_identity
  simp only [Derivation.leibniz, normalExpansion_chain_rule,
    smul_eq_mul, Derivation.map_one_eq_zero] at h
  linear_combination h

theorem velocity_second_identity :
    normalExpansion (pderiv 0 (pderiv 0 (pderiv 0 affineF))) * normalVelocity ^ 3 +
      3 * normalExpansion (pderiv 0 (pderiv 0 affineF)) * normalVelocity * Dt normalVelocity +
      normalExpansion (pderiv 0 affineF) * Dt (Dt normalVelocity) = 0 := by
  have h := congrArg Dt velocity_first_identity
  simp only [map_add, Derivation.leibniz, normalExpansion_chain_rule,
    Derivation.leibniz_pow, smul_eq_mul, map_zero] at h
  norm_num only [Nat.cast_ofNat, pow_one, Nat.reduceSub] at h
  linear_combination h

theorem velocity_constant : normalVelocity.constantCoeff = 1 / normalG := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) normal_velocity_identity
  simp only [map_mul, constantCoeff_normalExpansion, map_one] at h
  apply (eq_div_iff normalG_ne_zero).mpr
  simpa only [normalG, mul_comm] using h

theorem velocity_first_constant :
    (Dt normalVelocity).constantCoeff = -normalG1 / normalG ^ 3 := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) velocity_first_identity
  simp only [map_add, map_mul, map_pow, constantCoeff_normalExpansion, map_zero,
    velocity_constant] at h
  change normalG1 * (1 / normalG) ^ 2 +
    normalG * (Dt normalVelocity).constantCoeff = 0 at h
  apply (eq_div_iff (pow_ne_zero _ normalG_ne_zero)).mpr
  field_simp [normalG_ne_zero] at h
  linear_combination h

theorem velocity_second_constant :
    (Dt (Dt normalVelocity)).constantCoeff =
      (3 * normalG1 ^ 2 - normalG * normalG2) / normalG ^ 5 := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) velocity_second_identity
  simp only [map_add, map_mul, map_pow, map_ofNat, constantCoeff_normalExpansion,
    map_zero, velocity_constant, velocity_first_constant] at h
  change normalG2 * (1 / normalG) ^ 3 +
    3 * normalG1 * (1 / normalG) * (-normalG1 / normalG ^ 3) +
    normalG * (Dt (Dt normalVelocity)).constantCoeff = 0 at h
  apply (eq_div_iff (pow_ne_zero _ normalG_ne_zero)).mpr
  field_simp [normalG_ne_zero] at h
  linear_combination h

def densityStream (A : AmbientPoly 4) : S := normalExpansion A * normalVelocity

theorem densityStream_second_derivative (A : AmbientPoly 4) :
    Dt (Dt (densityStream A)) =
      normalExpansion (pderiv 0 (pderiv 0 A)) * normalVelocity ^ 3 +
        3 * normalExpansion (pderiv 0 A) * normalVelocity * Dt normalVelocity +
        normalExpansion A * Dt (Dt normalVelocity) := by
  simp only [densityStream, Derivation.leibniz, map_add, normalExpansion_chain_rule,
    smul_eq_mul]
  ring

/-- The normal Taylor coefficient is the actual residue density used in
the protected affine exactness criterion. -/
theorem densityStream_coefficient_two (A : AmbientPoly 4) :
    PowerSeries.coeff 2 (densityStream A) = affineNormalSource A / normalG := by
  have hcoef := PowerSeries.constantCoeff_iterate_derivative (densityStream A) 2
  norm_num only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, mul_one] at hcoef
  have hderiv := congrArg (PowerSeries.constantCoeff (R := K))
    (densityStream_second_derivative A)
  simp only [map_add, map_mul, map_pow, map_ofNat, constantCoeff_normalExpansion,
    velocity_constant, velocity_first_constant, velocity_second_constant] at hderiv
  have he : PowerSeries.coeff 2 (densityStream A) =
      (affineMap (pderiv 0 (pderiv 0 A)) * (1 / normalG) ^ 3 +
        3 * affineMap (pderiv 0 A) * (1 / normalG) * (-normalG1 / normalG ^ 3) +
        affineMap A * ((3 * normalG1 ^ 2 - normalG * normalG2) / normalG ^ 5)) / 2 := by
    rw [hcoef] at hderiv
    apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).mpr
    simpa only [mul_comm] using hderiv
  rw [he]
  unfold affineNormalSource normalSourceTwo normalG normalG1 normalG2
  field_simp [normal_ne_zero]
  ring

/-- The density of the actual pulled-back pole-three form in the genuine
normal chart. Its denominator is the image of f, not a formal replacement. -/
def poleThreeDensity (A : AmbientPoly 4) : HahnSeries ℤ K :=
  HahnSeries.ofPowerSeries ℤ K (normalExpansion A) /
      (HahnSeries.ofPowerSeries ℤ K (normalExpansion affineF)) ^ 3 *
    HahnSeries.ofPowerSeries ℤ K normalVelocity

theorem poleThreeDensity_expansion (A : AmbientPoly 4) :
    poleThreeDensity A = HahnSeries.ofPowerSeries ℤ K (densityStream A) *
      HahnSeries.single (-3) 1 := by
  simp only [poleThreeDensity, normalExpansion_F, HahnSeries.ofPowerSeries_X,
    div_eq_mul_inv, HahnSeries.single_pow, nsmul_eq_mul, one_pow,
    HahnSeries.inv_single, inv_one, densityStream, map_mul]
  norm_num
  ring

/-- The Laurent residue of the actual pole-three normal pullback is c/g. -/
theorem poleThreeDensity_residue (A : AmbientPoly 4) :
    (poleThreeDensity A).coeff (-1) = affineNormalSource A / normalG := by
  rw [poleThreeDensity_expansion, HahnSeries.coeff_mul_single]
  norm_num only [Int.reduceSub, mul_one]
  change (HahnSeries.ofPowerSeries ℤ K (densityStream A)).coeff ((2 : ℕ) : ℤ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff, densityStream_coefficient_two]

/-- Binding to the genuine exterior form used by the certificate theorem.
The coefficient is computed from the actual normal pullback, not postulated. -/
theorem residueSourceForm_eq_formalResidue (A : AmbientPoly 4) :
    CycleQ2AffineExactness.residueSourceForm A =
      (poleThreeDensity A).coeff (-1) • CycleQ2AffineExterior.volume := by
  rw [poleThreeDensity_residue]
  rfl

end CycleQ2FormalResidue

#print axioms CycleQ2FormalResidue.densityStream_coefficient_two
#print axioms CycleQ2FormalResidue.poleThreeDensity_residue
#print axioms CycleQ2FormalResidue.residueSourceForm_eq_formalResidue
end
end


/- Component: continuation_2/NormalChartDerivations.lean -/
section
/-!+# Actual coordinate derivations and Jacobian of the formal normal chart

The coefficient derivations are the actual complex tangent derivations of
the protected affine function field, extended coefficient by coefficient.
The formal parameter is held constant.  The normal derivative and the four
tangent derivations therefore give the implicit-coordinate Jacobian of the
faithful chart already constructed from `f ↦ T`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace CycleQ2PowerSeriesTangents

variable {C K : Type*} [CommRing C] [CommRing K] [Algebra C K]

def coefficientwise (D : Derivation C K K) (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => D (PowerSeries.coeff n f)

@[simp] theorem coefficientwise_coeff (D : Derivation C K K) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (coefficientwise D f) = D (PowerSeries.coeff n f) := by
  simp [coefficientwise]

theorem coefficientwise_mul (D : Derivation C K K) (f g : PowerSeries K) :
    coefficientwise D (f * g) = f * coefficientwise D g + g * coefficientwise D f := by
  rw [mul_comm g (coefficientwise D f)]
  ext n
  simp only [coefficientwise_coeff, PowerSeries.coeff_mul, map_sum, map_add,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  ring

/-- Coefficientwise extension as an actual complex-linear derivation. -/
def extend (D : Derivation C K K) : Derivation C (PowerSeries K) (PowerSeries K) where
  toFun := coefficientwise D
  map_add' f g := by
    ext n
    simp
  map_smul' c f := by
    ext n
    simp only [coefficientwise_coeff, PowerSeries.coeff_smul, Derivation.map_smul,
      RingHom.id_apply]
  map_one_eq_zero' := by
    ext n
    by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]
  leibniz' f g := by
    change coefficientwise D (f * g) = f * coefficientwise D g + g * coefficientwise D f
    exact coefficientwise_mul D f g

@[simp] theorem extend_coeff (D : Derivation C K K) (f : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (extend D f) = D (PowerSeries.coeff n f) :=
  coefficientwise_coeff D f n

@[simp] theorem extend_C (D : Derivation C K K) (a : K) :
    extend D (PowerSeries.C a) = PowerSeries.C (D a) := by
  ext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

@[simp] theorem extend_X (D : Derivation C K K) : extend D PowerSeries.X = 0 := by
  ext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

theorem extend_commute (D E : Derivation C K K) (h : Function.Commute D E) :
    Function.Commute (extend D) (extend E) := by
  intro f
  ext n
  simpa only [extend_coeff] using h (PowerSeries.coeff n f)

theorem derivative_extend_commute (D : Derivation C K K) :
    Function.Commute (PowerSeries.derivative K) (extend D) := by
  intro f
  ext n
  simp [PowerSeries.coeff_derivative, Derivation.leibniz, smul_eq_mul, mul_comm]

end CycleQ2PowerSeriesTangents

namespace CycleQ2PolynomialChainRule

open MvPolynomial

variable {R B M σ : Type*} [CommRing R] [CommRing B] [Algebra R B]
  [Fintype σ] [DecidableEq σ] [AddCommGroup M] [Module B M] [Module R M]

/-- The genuine derivation chain rule for any polynomial algebra map. -/
theorem apply (φ : MvPolynomial σ R →ₐ[R] B) (δ : Derivation R B M)
    (P : MvPolynomial σ R) :
    δ (φ P) = ∑ i : σ, φ (pderiv i P) • δ (φ (X i)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have hc : φ (MvPolynomial.C c) = algebraMap R B c := φ.commutes c
      rw [hc, Derivation.map_algebraMap]
      simp
  | add P Q ihP ihQ =>
      simp only [map_add, ihP, ihQ, add_smul, Finset.sum_add_distrib]
  | mul_X P i ih =>
      have hs :
          (∑ j : σ, (φ (pderiv j P) * φ (X i)) • δ (φ (X j))) =
          φ (X i) • ∑ j : σ, φ (pderiv j P) • δ (φ (X j)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [smul_smul]
        congr 1
        ring
      have hd :
          (∑ j : σ, (φ P * φ (pderiv j (X i))) • δ (φ (X j))) =
          φ P • δ (φ (X i)) := by
        simp [pderiv_X, Pi.single_apply, apply_ite]
      rw [map_mul, Derivation.leibniz, ih]
      simp only [pderiv_mul, map_add, map_mul, add_smul, Finset.sum_add_distrib]
      rw [hs, hd]
      exact add_comm _ _

end CycleQ2PolynomialChainRule

namespace CycleQ2NormalChart

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
  CycleQ2AffineDifferentials CycleQ2FormalSpecialization CycleQ2NormalExpansion

abbrev K := AffineFunctionField
abbrev S := PowerSeries K

def normalAlgHom : AmbientPoly 4 →ₐ[ℂ] S where
  toRingHom := normalExpansion
  commutes' c := by
    change normalExpansion (MvPolynomial.C c) = algebraMap ℂ S c
    rw [normalExpansion_C, PowerSeries.algebraMap_apply]
    rfl

def tangent (j : Fin 4) : Derivation ℂ S S :=
  CycleQ2PowerSeriesTangents.extend (complexTangent j)

def parameterDerivative : Derivation ℂ S S :=
  (PowerSeries.derivative K).restrictScalars ℂ

@[simp] theorem parameterDerivative_apply (f : S) : parameterDerivative f = Dt f := rfl

@[simp] theorem tangent_C (j : Fin 4) (a : K) :
    tangent j (PowerSeries.C a) = PowerSeries.C (affineTangent j a) := by
  exact CycleQ2PowerSeriesTangents.extend_C (complexTangent j) a

@[simp] theorem tangent_X (j : Fin 4) : tangent j PowerSeries.X = 0 :=
  CycleQ2PowerSeriesTangents.extend_X (complexTangent j)

@[simp] theorem tangent_coordinate (j i : Fin 4) :
    tangent j (PowerSeries.C (fieldCoordinate i.succ)) = if i = j then 1 else 0 := by
  rw [tangent_C]
  simp only [fieldCoordinate, affineTangent_coordinate]
  split_ifs <;> simp

theorem tangent_normalExpansion_chain (j : Fin 4) (P : AmbientPoly 4) :
    tangent j (normalExpansion P) =
      normalExpansion (pderiv 0 P) * tangent j normalRoot +
        normalExpansion (pderiv j.succ P) := by
  have h := CycleQ2PolynomialChainRule.apply normalAlgHom (tangent j) P
  change tangent j (normalExpansion P) =
    ∑ i : Fin 5, normalExpansion (pderiv i P) * tangent j (normalExpansion (X i)) at h
  rw [Fin.sum_univ_succ] at h
  simpa only [normalExpansion_X_zero, normalExpansion_X_succ, tangent_coordinate,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

theorem tangent_normalRoot (j : Fin 4) :
    tangent j normalRoot = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
  have h := tangent_normalExpansion_chain j affineF
  rw [normalExpansion_F, tangent_X] at h
  calc
    tangent j normalRoot =
        (normalExpansion (pderiv 0 affineF) * normalVelocity) * tangent j normalRoot := by
      rw [normal_velocity_identity, one_mul]
    _ = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
      linear_combination -normalVelocity * h

/-- The actual implicit-coordinate derivative with `f` held equal to the
formal parameter.  Its reciprocal normal derivative is the proved velocity. -/
theorem tangent_normalExpansion (j : Fin 4) (P : AmbientPoly 4) :
    tangent j (normalExpansion P) = normalExpansion (pderiv j.succ P) -
      normalVelocity * normalExpansion (pderiv j.succ affineF) *
        normalExpansion (pderiv 0 P) := by
  rw [tangent_normalExpansion_chain, tangent_normalRoot]
  ring

theorem tangents_commute (i j : Fin 4) : Function.Commute (tangent i) (tangent j) := by
  apply CycleQ2PowerSeriesTangents.extend_commute
  exact affineTangents_commute i j

theorem parameter_tangent_commute (j : Fin 4) :
    Function.Commute parameterDerivative (tangent j) :=
  CycleQ2PowerSeriesTangents.derivative_extend_commute (complexTangent j)

/-- The coordinate derivations are ordered `(∂T,E₁,E₂,E₃,E₄)`. -/
def coordinateDerivative : Fin 5 → Derivation ℂ S S :=
  Fin.cases parameterDerivative tangent

/-- Rows are coordinate derivations; columns are the five original affine
coordinate functions after the actual normal substitution. -/
def jacobian : Matrix (Fin 5) (Fin 5) S :=
  fun i j => coordinateDerivative i (normalExpansion (X j))

theorem jacobian_zero_row (i : Fin 5) :
    jacobian 0 i = if i = 0 then normalVelocity else 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [jacobian, coordinateDerivative, normalVelocity]
  · simp [jacobian, coordinateDerivative, Dt]

theorem jacobian_succ_zero (j : Fin 4) :
    jacobian j.succ 0 = -normalVelocity * normalExpansion (pderiv j.succ affineF) := by
  simpa [jacobian, coordinateDerivative] using tangent_normalRoot j

theorem jacobian_succ_succ (i j : Fin 4) :
    jacobian i.succ j.succ = if j = i then 1 else 0 := by
  change tangent i (normalExpansion (X j.succ)) = _
  rw [normalExpansion_X_succ, tangent_coordinate]

/-- The determinant is the actual normal velocity, with positive sign in
the stipulated parameter-first coordinate order. -/
theorem jacobian_det : Matrix.det jacobian = normalVelocity := by
  have hminor : jacobian.submatrix Fin.succ Fin.succ =
      (1 : Matrix (Fin 4) (Fin 4) S) := by
    ext i j
    simp [Matrix.submatrix, jacobian_succ_succ, Matrix.one_apply, eq_comm]
  rw [Matrix.det_succ_row_zero]
  simp [jacobian_zero_row, hminor]

/-! The algebraic Kähler module of a power-series ring need not be generated
by these five coordinate differentials.  The following argument instead
differentiates the actual polynomial relation inside that entire module. -/

abbrev Omega := Ω[S⁄ℂ]
abbrev universalD : Derivation ℂ S Omega := KaehlerDifferential.D ℂ S
abbrev TopForm := ⋀[S]^5 Omega

theorem normalExpansion_complex_constant (c : ℂ) :
    normalExpansion (MvPolynomial.C c) = algebraMap ℂ S c := by
  rw [normalExpansion_C, PowerSeries.algebraMap_apply]
  rfl

/-- The universal polynomial chain rule in the full algebraic Kähler module
of the power-series ring; no finite-rank or continuity assertion is used. -/
theorem universal_polynomial_differential (P : AmbientPoly 4) :
    universalD (normalExpansion P) =
      ∑ i : Fin 5, normalExpansion (pderiv i P) • universalD (normalExpansion (X i)) := by
  exact CycleQ2PolynomialChainRule.apply normalAlgHom universalD P

def tangentDifferential (j : Fin 4) : Omega :=
  universalD (PowerSeries.C (fieldCoordinate j.succ))

theorem universal_normal_differential :
    universalD normalRoot = normalVelocity • universalD PowerSeries.X -
      ∑ j : Fin 4, (normalVelocity * normalExpansion (pderiv j.succ affineF)) •
        tangentDifferential j := by
  have h := universal_polynomial_differential affineF
  rw [normalExpansion_F, Fin.sum_univ_succ] at h
  simp only [normalExpansion_X_zero, normalExpansion_X_succ] at h
  have hm := congrArg (fun η : Omega => normalVelocity • η) h
  have hv : normalVelocity * normalExpansion (pderiv 0 affineF) = 1 := by
    rw [mul_comm, normal_velocity_identity]
  simp only [smul_add, Finset.smul_sum, smul_smul, hv, one_smul] at hm
  exact (eq_sub_iff_add_eq).mpr hm.symm

private def wedgeWithTangents : Omega →ₗ[S] TopForm where
  toFun a := exteriorPower.ιMulti S 5 (Matrix.vecCons a tangentDifferential)
  map_add' a b := (exteriorPower.ιMulti S 5).map_vecCons_add tangentDifferential a b
  map_smul' c a := (exteriorPower.ιMulti S 5).map_vecCons_smul tangentDifferential c a

private theorem wedgeWithTangents_tangent (j : Fin 4) :
    wedgeWithTangents (tangentDifferential j) = 0 := by
  apply (exteriorPower.ιMulti S 5).map_eq_zero_of_eq
    (Matrix.vecCons (tangentDifferential j) tangentDifferential)
    (i := 0) (j := j.succ)
  · simp
  · exact (Fin.succ_ne_zero j).symm

/-- The ordered coordinate volume `dT ∧ dx₁ ∧ ... ∧ dx₄` in the actual
universal exterior power of the formal chart ring. -/
def normalVolume : TopForm :=
  exteriorPower.ιMulti S 5 (Matrix.vecCons (universalD PowerSeries.X) tangentDifferential)

/-- The wedge of the actual universal differentials of the substituted
five affine coordinates: the coordinate-generator exterior pullback. -/
def pulledBackCoordinateVolume : TopForm :=
  exteriorPower.ιMulti S 5 (fun i : Fin 5 => universalD (normalExpansion (X i)))

/-- The Jacobian factor also holds in genuine universal exterior forms,
not merely after evaluating against the five coordinate derivations. -/
theorem pulledBackCoordinateVolume_eq :
    pulledBackCoordinateVolume = normalVelocity • normalVolume := by
  have ht : (fun i : Fin 5 => universalD (normalExpansion (X i))) =
      Matrix.vecCons (universalD normalRoot) tangentDifferential := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [tangentDifferential]
  unfold pulledBackCoordinateVolume
  rw [ht]
  change wedgeWithTangents (universalD normalRoot) = _
  rw [universal_normal_differential, map_sub, map_smul, map_sum]
  simp only [map_smul, wedgeWithTangents_tangent, smul_zero,
    Finset.sum_const_zero, sub_zero]
  rfl

section UniversalExteriorPullback

abbrev AmbientOmega := Ω[(AmbientPoly 4)⁄ℂ]

local instance normalAlgebra : Algebra (AmbientPoly 4) S :=
  normalAlgHom.toRingHom.toAlgebra

local instance normalOmegaModule : Module (AmbientPoly 4) Omega :=
  Module.compHom Omega normalAlgHom.toRingHom

local instance normalTopModule : Module (AmbientPoly 4) TopForm :=
  Module.compHom TopForm normalAlgHom.toRingHom

local instance normalOmegaTower : IsScalarTower (AmbientPoly 4) S Omega where
  smul_assoc a b η := by
    change (normalAlgHom a * b) • η = normalAlgHom a • (b • η)
    exact mul_smul _ _ _

local instance normalTopTower : IsScalarTower (AmbientPoly 4) S TopForm where
  smul_assoc a b η := by
    change (normalAlgHom a * b) • η = normalAlgHom a • (b • η)
    exact mul_smul _ _ _

local instance normalComplexOmegaTower : IsScalarTower ℂ (AmbientPoly 4) Omega where
  smul_assoc c a η := by
    change normalAlgHom (c • a) • η = c • (normalAlgHom a • η)
    rw [map_smul]
    exact smul_assoc _ _ _

/-- The actual map of universal one-forms induced by the normal chart. -/
def oneFormPullback : AmbientOmega →ₗ[AmbientPoly 4] Omega :=
  (universalD.compAlgebraMap (AmbientPoly 4)).liftKaehlerDifferential

@[simp] theorem oneFormPullback_D (P : AmbientPoly 4) :
    oneFormPullback (KaehlerDifferential.D ℂ (AmbientPoly 4) P) =
      universalD (normalExpansion P) := by
  rw [oneFormPullback, Derivation.liftKaehlerDifferential_comp_D]
  rfl

private def targetWedgeOverAmbient :
    Omega [⋀^Fin 5]→ₗ[AmbientPoly 4] TopForm where
  toMultilinearMap := (exteriorPower.ιMulti S 5).toMultilinearMap.restrictScalars (AmbientPoly 4)
  map_eq_zero_of_eq' := (exteriorPower.ιMulti S 5).map_eq_zero_of_eq

/-- The induced exterior pullback, defined by the universal alternating
property and the genuine one-form pullback. -/
def exteriorPullback : (⋀[AmbientPoly 4]^5 AmbientOmega) →ₗ[AmbientPoly 4] TopForm :=
  exteriorPower.alternatingMapLinearEquiv
    (targetWedgeOverAmbient.compLinearMap oneFormPullback)

def ambientCoordinateVolume : ⋀[AmbientPoly 4]^5 AmbientOmega :=
  exteriorPower.ιMulti (AmbientPoly 4) 5
    (fun i : Fin 5 => KaehlerDifferential.D ℂ (AmbientPoly 4) (X i))

theorem exteriorPullback_ambientCoordinateVolume :
    exteriorPullback ambientCoordinateVolume = normalVelocity • normalVolume := by
  rw [exteriorPullback, ambientCoordinateVolume,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  simp only [oneFormPullback_D]
  exact pulledBackCoordinateVolume_eq

end UniversalExteriorPullback

end CycleQ2NormalChart

#print axioms CycleQ2PowerSeriesTangents.extend
#print axioms CycleQ2NormalChart.tangent_normalExpansion
#print axioms CycleQ2NormalChart.jacobian_det
#print axioms CycleQ2NormalChart.universal_normal_differential
#print axioms CycleQ2NormalChart.pulledBackCoordinateVolume_eq
#print axioms CycleQ2NormalChart.exteriorPullback_ambientCoordinateVolume
end
end


/- Component: continuation_2/PureM2Certificate.lean -/
section
/-!+# An exact certificate along the genuine one-term Fermat deformation

For every complex parameter `s`, this module gives a complete certificate for
`sum X_i^6 + s * X₂^3 X₀ X₅ X₃`, with the original protected source monomial.
The denominator is `36 * (X₂^6+X₅^6) * (X₁^6+X₄^6)`.  The factor 36 clears
the rational scalar coefficients of the vector field.  This is a distinct
one-term family, not an assertion about the protected three-term sextic.
-/

noncomputable section
namespace CycleQ2PureM2

set_option maxRecDepth 10000

open MvPolynomial HodgeComputer

abbrev Poly := AmbientPoly 5
abbrev A : Poly := HodgeSubmission.A

def U : Poly := X 2 ^ 6 + X 5 ^ 6
def V : Poly := X 1 ^ 6 + X 4 ^ 6
def M : Poly := X 2 ^ 3 * X 0 * X 5 * X 3
def F (s : ℂ) : Poly :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6 + C s * M

def D : Poly := C 36 * (U * V)

def N (s : ℂ) : Fin 6 → Poly :=
  ![0, C (-2 * s) * (A * M * X 1), C 3 * (A * V * X 2),
    0, C (-2 * s) * (A * M * X 4), C 3 * (A * V * X 5)]

theorem U_homogeneous : U.IsHomogeneous 6 := by
  exact (isHomogeneous_X_pow (2 : Fin 6) 6).add (isHomogeneous_X_pow 5 6)

theorem V_homogeneous : V.IsHomogeneous 6 := by
  exact (isHomogeneous_X_pow (1 : Fin 6) 6).add (isHomogeneous_X_pow 4 6)

theorem M_homogeneous : M.IsHomogeneous 6 := by
  have hx (i : Fin 6) : (X i : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ i
  simpa [M] using ((((hx 2).pow 3).mul (hx 0)).mul (hx 5)).mul (hx 3)

theorem F_homogeneous (s : ℂ) : (F s).IsHomogeneous 6 := by
  exact ((((((isHomogeneous_X_pow (0 : Fin 6) 6).add
    (isHomogeneous_X_pow 1 6)).add (isHomogeneous_X_pow 2 6)).add
    (isHomogeneous_X_pow 3 6)).add (isHomogeneous_X_pow 4 6)).add
    (isHomogeneous_X_pow 5 6)).add (M_homogeneous.C_mul s)

theorem D_homogeneous : D.IsHomogeneous 12 := by
  simpa [D] using (U_homogeneous.mul V_homogeneous).C_mul (36 : ℂ)

theorem D_ne_zero : D ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (fun _ : Fin 6 => (1 : ℂ))) h
  norm_num [D, U, V] at hh

theorem D_totalDegree : D.totalDegree = 12 := D_homogeneous.totalDegree D_ne_zero

theorem N_homogeneous (s : ℂ) (i : Fin 6) : (N s i).IsHomogeneous 19 := by
  have hA : A.IsHomogeneous 12 := CycleQ2Workspace.originalA_homogeneous
  have hx (j : Fin 6) : (X j : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ j
  have hU (j : Fin 6) : (C (3 : ℂ) * (A * V * X j)).IsHomogeneous 19 := by
    simpa using ((hA.mul V_homogeneous).mul (hx j)).C_mul (3 : ℂ)
  have hM (j : Fin 6) : (C (-2 * s) * (A * M * X j)).IsHomogeneous 19 := by
    simpa using ((hA.mul M_homogeneous).mul (hx j)).C_mul (-2 * s)
  fin_cases i
  · exact isHomogeneous_zero (Fin 6) ℂ 19
  · exact hM 1
  · exact hU 2
  · exact isHomogeneous_zero (Fin 6) ℂ 19
  · exact hM 4
  · exact hU 5

/- The elementary univariate retraction and monic argument also used for the
Fermat subset denominators.  Here the perturbation is linear in `X 0`, so it
preserves monicity and both denominator factors are constant in this variable. -/
private def toUni : Poly →+* Polynomial Poly :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => if i = 0 then Polynomial.X else Polynomial.C (X i))

private def fromUni : Polynomial Poly →+* Poly :=
  Polynomial.eval₂RingHom (RingHom.id Poly) (X 0)

private theorem retract : fromUni.comp toUni = RingHom.id Poly := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [toUni, fromUni]
  · intro i
    by_cases hi : i = 0 <;> simp [toUni, fromUni, hi]

private theorem monic_relPrime_constant {R : Type*} [CommRing R] [IsDomain R]
    {f : Polynomial R} (hf : f.Monic) {c : R} (hc : c ≠ 0) :
    IsRelPrime f (Polynomial.C c) := by
  intro p hpf hpc
  by_contra hunit
  have hpos := Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hf hunit hpf
  have hle := Polynomial.natDegree_le_of_dvd hpc (Polynomial.C_ne_zero.mpr hc)
  simp only [Polynomial.natDegree_C] at hle
  omega

private theorem toUni_F_monic (s : ℂ) : (toUni (F s)).Monic := by
  have hrepr : toUni (F s) = (Polynomial.X : Polynomial Poly) ^ 6 +
      (Polynomial.C (C s * X 2 ^ 3 * X 5 * X 3) * Polynomial.X +
       Polynomial.C (X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6)) := by
    simp [toUni, F, M]
    ring
  rw [hrepr]
  apply Polynomial.monic_X_pow_add
  exact (Polynomial.degree_add_le_of_le (Polynomial.degree_C_mul_X_le _)
    Polynomial.degree_C_le).trans_lt (by norm_num)

private theorem toUni_D : toUni D = Polynomial.C D := by
  simp [toUni, D, U, V]

theorem F_ne_zero (s : ℂ) : F s ≠ 0 := by
  intro h
  exact (toUni_F_monic s).ne_zero (by rw [h, map_zero])

theorem denominator_legal (s : ℂ) : IsRelPrime (F s) D := by
  apply HodgeComputer.relPrime_of_retract toUni fromUni retract
  rw [toUni_D]
  exact monic_relPrime_constant (toUni_F_monic s) D_ne_zero

private theorem sum_six (f : Fin 6 → Poly) :
    ∑ i, f i = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

set_option maxHeartbeats 2000000 in
theorem normalized_directional (s : ℂ) :
    (2 : Poly) * HodgeTestbed.directional (F s) (N s) = A * D := by
  unfold HodgeTestbed.directional
  rw [sum_six]
  simp [F, N, A,
    HodgeSubmission.A, D, U, V, M, map_add, pderiv_X, map_mul, map_neg, map_ofNat]
  ring

set_option maxHeartbeats 2000000 in
theorem divergence_zero (s : ℂ) : HodgeTestbed.divergenceNumerator D (N s) = 0 := by
  have h2 (i : Fin 6) : pderiv i (2 : Poly) = 0 := (pderiv i).map_natCast 2
  have h3 (i : Fin 6) : pderiv i (3 : Poly) = 0 := (pderiv i).map_natCast 3
  have h36 (i : Fin 6) : pderiv i (36 : Poly) = 0 := (pderiv i).map_natCast 36
  unfold HodgeTestbed.divergenceNumerator HodgeTestbed.divergence HodgeTestbed.directional
  rw [sum_six, sum_six]
  simp [N, A, HodgeSubmission.A,
    D, U, V, M, map_add, pderiv_mul, pderiv_X,
    h2, h3, h36, map_mul, map_neg, map_ofNat]
  ring

theorem verified (s : ℂ) : Verify (F s) A 6 2 D (N s) 0 where
  hypersurface_ne_zero := F_ne_zero s
  hypersurface_homogeneous := F_homogeneous s
  source_homogeneous := by
    simpa using Homogeneous.of_isHomogeneous CycleQ2Workspace.originalA_homogeneous
  denominator_ne_zero := D_ne_zero
  denominator_homogeneous := by simpa only [D_totalDegree] using D_homogeneous
  numerator_homogeneous := by
    intro i
    simpa [D_totalDegree] using Homogeneous.of_isHomogeneous (N_homogeneous s i)
  denominator_legal := denominator_legal s
  identity := normalized_identity (normalized_directional s) (by
    simpa only [mul_zero] using divergence_zero s)

/-- A complete, unconditional certificate along this one-term family. -/
theorem hasCertificate (s : ℂ) : HasCertificate (F s) 2 HodgeSubmission.A :=
  (verified s).hasCertificate

end CycleQ2PureM2

#print axioms CycleQ2PureM2.denominator_legal
#print axioms CycleQ2PureM2.normalized_directional
#print axioms CycleQ2PureM2.divergence_zero
#print axioms CycleQ2PureM2.hasCertificate
end
end


/- Component: continuation_2/CartierMatrixFactorization.lean -/
section
/-!
# Actual polynomial resolution data for the invariant Cartier curve

All entries below are literal polynomials over an arbitrary commutative ring.
The six by six matrices factor the actual cubic a^3-b^3+c^3+d^3.
The augmentation is the previously constructed elliptic-sextic residual ideal.
The two original second syzygies alone do not give the full hypersurface
resolution: the four columns of H0 are necessary.

No geometric deformation theorem or characteristic-zero rank lifting is
asserted in this file.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CycleQ2CartierResolution

variable {R : Type*} [CommRing R] (a b c d : R)

def cubic : R := a ^ 3 - b ^ 3 + c ^ 3 + d ^ 3

def first : Matrix (Fin 4) (Fin 6) R :=
  !![a^2, b^2, -c^2, d^2, a*d, -b*c;
     c, -d, a, -b, 0, 0;
     b, a, 0, 0, c, -d;
     0, 0, d, c, b, a]

def second : Matrix (Fin 6) (Fin 2) R :=
  !![d, 0; c, 0; 0, b; 0, a; -a, -d; b, -c]

def homotopy0 : Matrix (Fin 6) (Fin 4) R :=
  !![a, c^2, -b^2, b*c;
     -b, -d^2, a^2, a*d;
     -c, a^2, a*d, d^2;
     d, b^2, -b*c, c^2;
     0, -b*c, c^2, -b^2;
     0, -a*d, -d^2, a^2]

def homotopy1 : Matrix (Fin 2) (Fin 6) R :=
  !![d^2, c^2, -b*c, -a*d, -a^2, -b^2;
     -a*d, b*c, -b^2, a^2, -d^2, -c^2]

def even : Matrix (Fin 6) (Fin 6) R :=
  !![d, 0, a, c^2, -b^2, b*c;
     c, 0, -b, -d^2, a^2, a*d;
     0, b, -c, a^2, a*d, d^2;
     0, a, d, b^2, -b*c, c^2;
     -a, -d, 0, -b*c, c^2, -b^2;
     b, -c, 0, -a*d, -d^2, a^2]

def odd : Matrix (Fin 6) (Fin 6) R :=
  !![d^2, c^2, -b*c, -a*d, -a^2, -b^2;
     -a*d, b*c, -b^2, a^2, -d^2, -c^2;
     a^2, b^2, -c^2, d^2, a*d, -b*c;
     c, -d, a, -b, 0, 0;
     b, a, 0, 0, c, -d;
     0, 0, d, c, b, a]

def generators : Matrix (Fin 1) (Fin 4) R :=
  !![a^2*b - c*d^2 + 2*c*(a*c+b*d),
     -2*a^3*c+a^2*d^2+a*b*c^2+2*b^3*c-b^2*c*d,
     -2*a^2*c*d-a*b^3+a*d^3-2*b^2*c^2+b*c^2*d,
     a*b^2*c-2*a*c*d^2-b^3*d+2*b*c^3+d^4]

def cubicColumn : Matrix (Fin 1) (Fin 6) R :=
  !![-a*b, 0, 2*a*c-d^2, -2*b*c, -b*d, 0]

theorem first_second : first a b c d * second a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, second, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem first_homotopy0 : first a b c d * homotopy0 a b c d =
    cubic a b c d • (1 : Matrix (Fin 4) (Fin 4) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, homotopy0, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy_identity :
    second a b c d * homotopy1 a b c d + homotopy0 a b c d * first a b c d =
      cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [first, second, homotopy0, homotopy1, cubic,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy1_second : homotopy1 a b c d * second a b c d =
    cubic a b c d • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [homotopy1, second, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem homotopy1_homotopy0 : homotopy1 a b c d * homotopy0 a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [homotopy1, homotopy0, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem even_odd : even a b c d * odd a b c d =
    cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [even, odd, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem odd_even : odd a b c d * even a b c d =
    cubic a b c d • (1 : Matrix (Fin 6) (Fin 6) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [even, odd, cubic, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem augmentation_first :
    generators a b c d * first a b c d + cubic a b c d • cubicColumn a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [generators, first, cubicColumn, cubic,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem cubicColumn_second : cubicColumn a b c d * second a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicColumn, second, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem cubicColumn_homotopy0 :
    cubicColumn a b c d * homotopy0 a b c d + generators a b c d = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [cubicColumn, homotopy0, generators,
      Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

end CycleQ2CartierResolution

#print axioms CycleQ2CartierResolution.even_odd
#print axioms CycleQ2CartierResolution.odd_even
#print axioms CycleQ2CartierResolution.homotopy_identity
#print axioms CycleQ2CartierResolution.augmentation_first
#print axioms CycleQ2CartierResolution.cubicColumn_homotopy0
end


/- Component: continuation_2/CartierMatrixFactorizationExactness.lean -/
section
/-!
# Genuine exactness of the actual periodic complex modulo the cubic

A matrix factorization over a domain gives an exact two-periodic complex
after quotienting by its nonzero scalar. The proof lifts a kernel vector,
uses divisibility by the scalar, and cancels that scalar in the domain.
The resulting theorem is applied to the actual six by six cubic matrices.

This proves quotient-module exactness. It does not assert saturation,
base change through the cubic section, or nonlinear geometric lifting.
-/

set_option autoImplicit false

noncomputable section
namespace CycleQ2CartierResolution

open Matrix

variable {R : Type*} [CommRing R] [IsDomain R]

theorem matrixFactorization_exact_mod
    {n : Type*} [Fintype n] [DecidableEq n]
    (g : R) (hg : g ≠ 0) (A B : Matrix n n R)
    (hAB : A * B = g • (1 : Matrix n n R))
    (hBA : B * A = g • (1 : Matrix n n R))
    (x : n → R ⧸ Ideal.span ({g} : Set R)) :
    A.map (Ideal.Quotient.mk (Ideal.span ({g} : Set R))) *ᵥ x = 0 ↔
      ∃ y, B.map (Ideal.Quotient.mk (Ideal.span ({g} : Set R))) *ᵥ y = x := by
  let I : Ideal R := Ideal.span ({g} : Set R)
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  change A.map q *ᵥ x = 0 ↔ ∃ y, B.map q *ᵥ y = x
  have hqg : q g = 0 := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mpr
    exact Ideal.subset_span (Set.mem_singleton g)
  have hqAB : A.map q * B.map q = 0 := by
    rw [← Matrix.map_mul, hAB]
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hqg]
  constructor
  · intro hx
    choose z hz using fun i => Ideal.Quotient.mk_surjective (x i)
    have hqz : q ∘ z = x := funext hz
    have hdiv : ∀ i, g ∣ (A *ᵥ z) i := by
      intro i
      apply Ideal.mem_span_singleton.mp
      apply (Ideal.Quotient.eq_zero_iff_mem).mp
      change q ((A *ᵥ z) i) = 0
      rw [RingHom.map_mulVec, hqz, hx]
      rfl
    choose y hy using hdiv
    have hAz : A *ᵥ z = g • y := by
      funext i
      exact hy i
    have hcancel : g • z = g • (B *ᵥ y) := by
      calc
        g • z = (B * A) *ᵥ z := by
          rw [hBA, smul_mulVec, one_mulVec]
        _ = B *ᵥ (A *ᵥ z) := (mulVec_mulVec z B A).symm
        _ = B *ᵥ (g • y) := by rw [hAz]
        _ = g • (B *ᵥ y) := mulVec_smul B g y
    have hzy : z = B *ᵥ y := by
      funext i
      apply mul_left_cancel₀ hg
      exact congrArg (fun v : n → R => v i) hcancel
    refine ⟨q ∘ y, ?_⟩
    funext i
    rw [← RingHom.map_mulVec, ← hzy]
    exact hz i
  · rintro ⟨y, rfl⟩
    rw [mulVec_mulVec, hqAB, zero_mulVec]

abbrev cubicQuotient (a b c d : R) := R ⧸ Ideal.span ({cubic a b c d} : Set R)

def cubicQuotientMap (a b c d : R) : R →+* cubicQuotient a b c d :=
  Ideal.Quotient.mk (Ideal.span ({cubic a b c d} : Set R))

theorem even_exact_mod_cubic (a b c d : R) (hg : cubic a b c d ≠ 0)
    (x : Fin 6 → cubicQuotient a b c d) :
    (even a b c d).map (cubicQuotientMap a b c d) *ᵥ x = 0 ↔
      ∃ y, (odd a b c d).map (cubicQuotientMap a b c d) *ᵥ y = x :=
  matrixFactorization_exact_mod (cubic a b c d) hg (even a b c d) (odd a b c d)
    (even_odd a b c d) (odd_even a b c d) x

theorem odd_exact_mod_cubic (a b c d : R) (hg : cubic a b c d ≠ 0)
    (x : Fin 6 → cubicQuotient a b c d) :
    (odd a b c d).map (cubicQuotientMap a b c d) *ᵥ x = 0 ↔
      ∃ y, (even a b c d).map (cubicQuotientMap a b c d) *ᵥ y = x :=
  matrixFactorization_exact_mod (cubic a b c d) hg (odd a b c d) (even a b c d)
    (odd_even a b c d) (even_odd a b c d) x

end CycleQ2CartierResolution

#print axioms CycleQ2CartierResolution.matrixFactorization_exact_mod
#print axioms CycleQ2CartierResolution.even_exact_mod_cubic
#print axioms CycleQ2CartierResolution.odd_exact_mod_cubic
end
end


/- Component: continuation_2/SegreSyzygyElimination.lean -/
section
/-!
# The actual nonlinear Segre relations and complementary-equation elimination

The sixteen rows are the twelve off-diagonal adjugate relations and four
diagonal differences. They are polynomial identities for every three by
three matrix, not identities only at the geometric seed.

The last two theorems justify dropping redundant equations after adjoining
an inverse of the complementary relation minor. They do not assume that a
selected square system has a solution; that input is supplied separately by
the trusted generic lifting theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CycleQ2SegreRelations
open Matrix

variable {R : Type*} [CommRing R]

def cofactors (M : Matrix (Fin 3) (Fin 3) R) : Fin 9 → R :=
  ![M 1 1*M 2 2-M 1 2*M 2 1,
    M 1 2*M 2 0-M 1 0*M 2 2,
    M 1 0*M 2 1-M 1 1*M 2 0,
    M 0 2*M 2 1-M 0 1*M 2 2,
    M 0 0*M 2 2-M 0 2*M 2 0,
    M 0 1*M 2 0-M 0 0*M 2 1,
    M 0 1*M 1 2-M 0 2*M 1 1,
    M 0 2*M 1 0-M 0 0*M 1 2,
    M 0 0*M 1 1-M 0 1*M 1 0]

def cofactorMatrix (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  !![cofactors M 0, cofactors M 1, cofactors M 2;
     cofactors M 3, cofactors M 4, cofactors M 5;
     cofactors M 6, cofactors M 7, cofactors M 8]

theorem cofactorMatrix_eq_transpose_adjugate (M : Matrix (Fin 3) (Fin 3) R) :
    cofactorMatrix M = M.adjugate.transpose := by
  rw [adjugate_fin_three]
  ext i j
  fin_cases i <;> fin_cases j
  · change M 1 1*M 2 2-M 1 2*M 2 1 = M 1 1*M 2 2-M 1 2*M 2 1
    ring
  · change M 1 2*M 2 0-M 1 0*M 2 2 = -(M 1 0*M 2 2)+M 1 2*M 2 0
    ring
  · change M 1 0*M 2 1-M 1 1*M 2 0 = M 1 0*M 2 1-M 1 1*M 2 0
    ring
  · change M 0 2*M 2 1-M 0 1*M 2 2 = -(M 0 1*M 2 2)+M 0 2*M 2 1
    ring
  · change M 0 0*M 2 2-M 0 2*M 2 0 = M 0 0*M 2 2-M 0 2*M 2 0
    ring
  · change M 0 1*M 2 0-M 0 0*M 2 1 = -(M 0 0*M 2 1)+M 0 1*M 2 0
    ring
  · change M 0 1*M 1 2-M 0 2*M 1 1 = M 0 1*M 1 2-M 0 2*M 1 1
    ring
  · change M 0 2*M 1 0-M 0 0*M 1 2 = -(M 0 0*M 1 2)+M 0 2*M 1 0
    ring
  · change M 0 0*M 1 1-M 0 1*M 1 0 = M 0 0*M 1 1-M 0 1*M 1 0
    ring

def relations (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 16) (Fin 9) R :=
  !![0,0,0, M 0 0,M 0 1,M 0 2, 0,0,0;
     0,0,0, 0,0,0, M 0 0,M 0 1,M 0 2;
     M 1 0,M 1 1,M 1 2, 0,0,0, 0,0,0;
     0,0,0, 0,0,0, M 1 0,M 1 1,M 1 2;
     M 2 0,M 2 1,M 2 2, 0,0,0, 0,0,0;
     0,0,0, M 2 0,M 2 1,M 2 2, 0,0,0;
     M 0 1,0,0, M 1 1,0,0, M 2 1,0,0;
     M 0 2,0,0, M 1 2,0,0, M 2 2,0,0;
     0,M 0 0,0, 0,M 1 0,0, 0,M 2 0,0;
     0,M 0 2,0, 0,M 1 2,0, 0,M 2 2,0;
     0,0,M 0 0, 0,0,M 1 0, 0,0,M 2 0;
     0,0,M 0 1, 0,0,M 1 1, 0,0,M 2 1;
     -M 0 0,-M 0 1,-M 0 2, M 1 0,M 1 1,M 1 2, 0,0,0;
     -M 0 0,-M 0 1,-M 0 2, 0,0,0, M 2 0,M 2 1,M 2 2;
     -M 0 0,M 0 1,0, -M 1 0,M 1 1,0, -M 2 0,M 2 1,0;
     -M 0 0,0,M 0 2, -M 1 0,0,M 1 2, -M 2 0,0,M 2 2]

/-- The sixteen genuine nonlinear polynomial relations on the nine cofactors. -/
theorem relations_cofactors (M : Matrix (Fin 3) (Fin 3) R) :
    relations M *ᵥ cofactors M = 0 := by
  funext i
  fin_cases i <;>
    norm_num [relations, cofactors, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]

/-- At any point where the chosen complementary relation block is a unit,
vanishing of the selected equations forces all residual equations to vanish. -/
theorem residual_eq_zero_of_relation_block
    (A : Matrix n n R) (B : Matrix n m R) (v : n → R) (e : m → R)
    (hrel : A *ᵥ v + B *ᵥ e = 0) (he : e = 0) (hdet : IsUnit A.det) : v = 0 := by
  have hv : A *ᵥ v = 0 := by simpa [he] using hrel
  calc
    v = (A⁻¹ * A) *ᵥ v := by rw [nonsing_inv_mul A hdet, one_mulVec]
    _ = A⁻¹ *ᵥ (A *ᵥ v) := (mulVec_mulVec v A⁻¹ A).symm
    _ = 0 := by rw [hv, mulVec_zero]

/-- The elimination lemma after arbitrary coefficient evaluation, as needed
at the generic algebraic point produced by square-system lifting. -/
theorem evaluated_residual_eq_zero
    {S : Type*} [CommRing S] (f : R →+* S)
    (A : Matrix n n R) (B : Matrix n m R) (v : n → R) (e : m → R)
    (hrel : A *ᵥ v + B *ᵥ e = 0)
    (he : f ∘ e = 0) (hdet : IsUnit (f A.det)) : f ∘ v = 0 := by
  apply residual_eq_zero_of_relation_block (A.map f) (B.map f) (f ∘ v) (f ∘ e)
  · funext i
    change (A.map f *ᵥ (f ∘ v)) i + (B.map f *ᵥ (f ∘ e)) i = 0
    rw [← RingHom.map_mulVec, ← RingHom.map_mulVec, ← map_add]
    have hz := congrArg (fun z : n → R => z i) hrel
    change (A *ᵥ v) i + (B *ᵥ e) i = 0 at hz
    rw [hz, map_zero]
  · exact he
  · change IsUnit (f.mapMatrix A).det
    rw [← f.map_det]
    exact hdet

end CycleQ2SegreRelations

#print axioms CycleQ2SegreRelations.relations_cofactors
#print axioms CycleQ2SegreRelations.residual_eq_zero_of_relation_block
#print axioms CycleQ2SegreRelations.evaluated_residual_eq_zero
end


/- Component: continuation_2/SegreLocalFactorization.lean -/
section
/-!
# Local factorization of the actual three-by-three Segre equations

The nine equations are the row-major cofactors, i.e. the transpose of
mathlib's actual adjugate. Their vanishing is equivalent to all two-by-two
minors vanishing. On every chart where one entry is a unit, the matrix has
an explicit outer-product factorization. Its image has a generator whose
pivot coordinate is one, with the coordinate projection as a left inverse.
No global line-bundle, deformation, or geometric existence claim is made.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section
namespace CycleQ2SegreLocal

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- Row-major signed cofactors; the equation index is `(row,column)`. -/
def cofactors (M : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 3) (Fin 3) R :=
  M.adjugate.transpose

/-- The actual nine cofactor equations imply every two-by-two minor. -/
theorem minors_of_cofactors_zero (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i j k l : Fin 3) :
    M i j * M k l = M i l * M k j := by
  have ha : M.adjugate = 0 := by
    simpa [cofactors] using congrArg Matrix.transpose h
  rw [Matrix.adjugate_fin_three] at ha
  have h00 : M 1 1 * M 2 2 - M 1 2 * M 2 1 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 0 0) ha
  have h01 : -(M 0 1 * M 2 2) + M 0 2 * M 2 1 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 0 1) ha
  have h02 : M 0 1 * M 1 2 - M 0 2 * M 1 1 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 0 2) ha
  have h10 : -(M 1 0 * M 2 2) + M 1 2 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 1 0) ha
  have h11 : M 0 0 * M 2 2 - M 0 2 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 1 1) ha
  have h12 : -(M 0 0 * M 1 2) + M 0 2 * M 1 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 1 2) ha
  have h20 : M 1 0 * M 2 1 - M 1 1 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 2 0) ha
  have h21 : -(M 0 0 * M 2 1) + M 0 1 * M 2 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 2 1) ha
  have h22 : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 0 :=
    congrArg (fun A : Matrix (Fin 3) (Fin 3) R => A 2 2) ha
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> dsimp at * <;>
    solve
    | ring1
    | linear_combination h00
    | linear_combination -h00
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h02
    | linear_combination -h02
    | linear_combination h10
    | linear_combination -h10
    | linear_combination h11
    | linear_combination -h11
    | linear_combination h12
    | linear_combination -h12
    | linear_combination h20
    | linear_combination -h20
    | linear_combination h21
    | linear_combination -h21
    | linear_combination h22
    | linear_combination -h22

/-- A unit entry gives a normalized column and the actual pivot row. -/
theorem unit_pivot_factorization (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i0 j0 : Fin 3) (u : Rˣ)
    (hu : (u : R) = M i0 j0) (i j : Fin 3) :
    M i j = (M i j0 * (↑(u⁻¹) : R)) * M i0 j := by
  have hm := minors_of_cofactors_zero M h i j i0 j0
  calc
    M i j = (M i j * M i0 j0) * (↑(u⁻¹) : R) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    _ = (M i j0 * M i0 j) * (↑(u⁻¹) : R) := by rw [hm]
    _ = (M i j0 * (↑(u⁻¹) : R)) * M i0 j := by ring

/-- Conversely, every literal outer product satisfies all nine equations. -/
theorem cofactors_outerProduct (a b : Fin 3 → R) :
    cofactors (fun i j => a i * b j) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cofactors, Matrix.adjugate_fin_three, Matrix.transpose_apply] <;> ring

/-- No field hypothesis is needed for the pivot chart. -/
theorem normalized_factorization (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i0 j0 : Fin 3) (hu : IsUnit (M i0 j0)) :
    ∃ a b : Fin 3 → R, a i0 = 1 ∧ b = M i0 ∧
      (∀ i j, M i j = a i * b j) := by
  obtain ⟨u, hu⟩ := hu
  refine ⟨fun i => M i j0 * (↑(u⁻¹) : R), M i0, ?_, rfl, ?_⟩
  · change M i0 j0 * (↑(u⁻¹) : R) = 1
    rw [← hu, Units.mul_inv]
  · exact unit_pivot_factorization M h i0 j0 u hu

/-- The normalized column generates the image. Its pivot coordinate gives
an explicit left inverse, so this local image is a free rank-one summand. -/
theorem image_generator_with_retraction (M : Matrix (Fin 3) (Fin 3) R)
    (h : cofactors M = 0) (i0 j0 : Fin 3) (hu : IsUnit (M i0 j0)) :
    ∃ a : Fin 3 → R,
      a i0 = 1 ∧
      (∀ x : Fin 3 → R, M *ᵥ x = (∑ j, M i0 j * x j) • a) ∧
      (∀ r : R, (r • a) i0 = r) ∧
      (∀ r : R, ∃ x : Fin 3 → R, M *ᵥ x = r • a) := by
  obtain ⟨u, hunit⟩ := hu
  let a : Fin 3 → R := fun i => M i j0 * (↑(u⁻¹) : R)
  have ha : a i0 = 1 := by
    dsimp [a]
    rw [← hunit, Units.mul_inv]
  have hf (i j : Fin 3) : M i j = a i * M i0 j :=
    unit_pivot_factorization M h i0 j0 u hunit i j
  have hmul (x : Fin 3 → R) : M *ᵥ x = (∑ j, M i0 j * x j) • a := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hf]
    ring
  refine ⟨a, ha, hmul, ?_, ?_⟩
  · intro r
    simp [ha]
  · intro r
    refine ⟨Pi.single j0 ((↑(u⁻¹) : R) * r), ?_⟩
    rw [hmul]
    simp [Pi.single_apply, ← hunit]

end CycleQ2SegreLocal

#print axioms CycleQ2SegreLocal.minors_of_cofactors_zero
#print axioms CycleQ2SegreLocal.normalized_factorization
#print axioms CycleQ2SegreLocal.image_generator_with_retraction
end
end


/- Component: continuation_2/SegreImageLine.lean -/
section
/-!
# The actual image module on a Segre pivot chart

A vanishing cofactor matrix and a unit entry give an explicit linear
isomorphism from the coefficient ring to the matrix image. The separate
basepoint lemma shows how actual ideal-membership witnesses provide a
pivot after evaluation in a field. Neither theorem assumes a line bundle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace CycleQ2SegreImage

open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The image submodule of the actual matrix map is a free line on any
unit-entry chart. The isomorphism is proved directly from the equations. -/
theorem image_linearEquiv (M : Matrix (Fin 3) (Fin 3) R)
    (h : CycleQ2SegreLocal.cofactors M = 0)
    (i0 j0 : Fin 3) (hu : IsUnit (M i0 j0)) :
    Nonempty (R ≃ₗ[R] LinearMap.range M.mulVecLin) := by
  obtain ⟨a, ha, hmul, hret, hsurj⟩ :=
    CycleQ2SegreLocal.image_generator_with_retraction M h i0 j0 hu
  let f : R →ₗ[R] LinearMap.range M.mulVecLin :=
    { toFun := fun r => ⟨r • a, hsurj r⟩
      map_add' := by
        intro r s
        apply Subtype.ext
        exact add_smul r s a
      map_smul' := by
        intro r s
        apply Subtype.ext
        exact mul_smul r s a }
  have hinj : Function.Injective f := by
    intro r s hrs
    have hval := congrArg (fun v : LinearMap.range M.mulVecLin => v.val i0) hrs
    change (r • a) i0 = (s • a) i0 at hval
    simpa only [hret] using hval
  have honto : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := y.property
    refine ⟨∑ j, M i0 j * x j, ?_⟩
    apply Subtype.ext
    change (∑ j, M i0 j * x j) • a = y.val
    rw [← hmul]
    exact hx
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, honto⟩⟩

/-- Ideal membership is enough to exclude a common zero of the matrix
entries wherever one of the tested coordinates is nonzero. -/
theorem exists_nonzero_entry_of_coordinate_powers
    {ι K : Type*} [Field K] (M : Matrix (Fin 3) (Fin 3) R)
    (coordinates : ι → R) (degrees : ι → ℕ)
    (hmem : ∀ i, coordinates i ^ degrees i ∈
      Ideal.span (Set.range (fun p : Fin 3 × Fin 3 => M p.1 p.2)))
    (φ : R →+* K) (hpoint : ∃ i, φ (coordinates i) ≠ 0) :
    ∃ i j, φ (M i j) ≠ 0 := by
  by_contra! hzero
  have hker : Ideal.span (Set.range (fun p : Fin 3 × Fin 3 => M p.1 p.2)) ≤
      RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro z ⟨p, rfl⟩
    exact hzero p.1 p.2
  obtain ⟨i, hi⟩ := hpoint
  have hz : φ (coordinates i ^ degrees i) = 0 := hker (hmem i)
  rw [map_pow] at hz
  exact pow_ne_zero _ hi hz

/-- The same basepoint witnesses yield an actual unit-entry chart in any
field-valued point satisfying the nonzero-coordinate condition. -/
theorem exists_unit_entry_of_coordinate_powers
    {ι K : Type*} [Field K] (M : Matrix (Fin 3) (Fin 3) R)
    (coordinates : ι → R) (degrees : ι → ℕ)
    (hmem : ∀ i, coordinates i ^ degrees i ∈
      Ideal.span (Set.range (fun p : Fin 3 × Fin 3 => M p.1 p.2)))
    (φ : R →+* K) (hpoint : ∃ i, φ (coordinates i) ≠ 0) :
    ∃ i j, IsUnit (φ (M i j)) := by
  obtain ⟨i, j, hij⟩ := exists_nonzero_entry_of_coordinate_powers
    M coordinates degrees hmem φ hpoint
  exact ⟨i, j, isUnit_iff_ne_zero.mpr hij⟩

end CycleQ2SegreImage

#print axioms CycleQ2SegreImage.image_linearEquiv
#print axioms CycleQ2SegreImage.exists_nonzero_entry_of_coordinate_powers
#print axioms CycleQ2SegreImage.exists_unit_entry_of_coordinate_powers
end
end


/- Component: continuation_2/SegreCechDlog.lean -/
section
/-!
# Explicit overlap units and the Kähler Čech cocycle of a rank-one matrix

The common coefficient ring in these theorems may be the coordinate ring of
any overlap of unit-entry charts. No field hypothesis is used. The transition
units are calculated from the actual matrix entries and chosen pivot units.
The additive cocycle takes values in mathlib's universal Kähler module.

The first-column equations generate the same ideal on overlaps. A separate
nonzerodivisor hypothesis is needed to call their zero scheme an effective
Cartier divisor. This file does not construct a cycle class, a Gysin map, an
Abel--Jacobi map, or a rational primitive.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace CycleQ2SegreCech

open Matrix

variable {R : Type*} [CommRing R]

abbrev Chart := Fin 3 × Fin 3

/-- The image generator normalized to one at the pivot row. -/
def column (M : Matrix (Fin 3) (Fin 3) R) (p : Chart) (up : Rˣ) : Fin 3 → R :=
  fun i => M i p.2 * (↑(up⁻¹) : R)

private theorem transition_mul_reverse
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    (M q.1 p.2 * (↑(up⁻¹) : R)) * (M p.1 q.2 * (↑(uq⁻¹) : R)) = 1 := by
  have hm := CycleQ2SegreLocal.minors_of_cofactors_zero M hM q.1 p.2 p.1 q.2
  calc
    _ = (M q.1 p.2 * M p.1 q.2) * ((↑(up⁻¹) : R) * (↑(uq⁻¹) : R)) := by ring
    _ = (M q.1 q.2 * M p.1 p.2) * ((↑(up⁻¹) : R) * (↑(uq⁻¹) : R)) := by rw [hm]
    _ = ((up : R) * ↑(up⁻¹)) * ((uq : R) * ↑(uq⁻¹)) := by rw [← hp, ← hq]; ring
    _ = 1 := by rw [Units.mul_inv, Units.mul_inv, mul_one]

/-- The unit carrying the normalized image generator on chart `q` to the
one on chart `p`. Its inverse is another explicit matrix-entry ratio. -/
def transition
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) : Rˣ where
  val := M q.1 p.2 * (↑(up⁻¹) : R)
  inv := M p.1 q.2 * (↑(uq⁻¹) : R)
  val_inv := transition_mul_reverse M hM p q up uq hp hq
  inv_val := transition_mul_reverse M hM q p uq up hq hp

@[simp] theorem transition_val
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    (transition M hM p q up uq hp hq : R) = column M p up q.1 := rfl

theorem column_pivot
    (M : Matrix (Fin 3) (Fin 3) R) (p : Chart) (up : Rˣ)
    (hp : (up : R) = M p.1 p.2) : column M p up p.1 = 1 := by
  simp [column, ← hp]

/-- The explicit normalized columns glue by the displayed transition unit. -/
theorem column_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (i : Fin 3) :
    column M p up i = (transition M hM p q up uq hp hq : R) * column M q uq i := by
  change M i p.2 * (↑(up⁻¹) : R) =
    (M q.1 p.2 * (↑(up⁻¹) : R)) * (M i q.2 * (↑(uq⁻¹) : R))
  rw [CycleQ2SegreLocal.unit_pivot_factorization M hM q.1 q.2 uq hq i p.2]
  ring

@[simp] theorem transition_self
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p : Chart) (up : Rˣ) (hp : (up : R) = M p.1 p.2) :
    transition M hM p p up up hp hp = 1 := by
  apply Units.ext
  exact column_pivot M p up hp

theorem transition_reverse
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    transition M hM q p uq up hq hp = (transition M hM p q up uq hp hq)⁻¹ := by
  apply Units.ext
  rfl

/-- The multiplicative Čech cocycle on every triple overlap. -/
theorem transition_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) :
    transition M hM p q up uq hp hq * transition M hM q r uq ur hq hr =
      transition M hM p r up ur hp hr := by
  apply Units.ext
  exact (column_overlap M hM p q up uq hp hq r.1).symm

/-- The pivot row gives the local first-column equation. The same transition
unit relates its equations on different charts. -/
theorem row_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (j : Fin 3) :
    M q.1 j = (transition M hM p q up uq hp hq : R) * M p.1 j :=
  CycleQ2SegreLocal.unit_pivot_factorization M hM p.1 p.2 up hp q.1 j

theorem first_column_ideal_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    Ideal.span ({M q.1 0} : Set R) = Ideal.span ({M p.1 0} : Set R) := by
  rw [row_overlap M hM p q up uq hp hq 0]
  exact Ideal.span_singleton_mul_left_unit (transition M hM p q up uq hp hq).isUnit _

/-- Passing to an overlap ring preserves the actual cofactor equations. -/
theorem cofactors_map_zero
    {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0) :
    CycleQ2SegreLocal.cofactors (f.mapMatrix M) = 0 := by
  unfold CycleQ2SegreLocal.cofactors
  rw [← f.map_adjugate]
  change f.mapMatrix (CycleQ2SegreLocal.cofactors M) = 0
  rw [hM]
  ext i j
  exact f.map_zero

/-- Restriction of an overlap unit is the unit computed from the restricted
matrix. In particular the displayed cocycle is compatible with localization. -/
theorem transition_map
    {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    Units.map f.toMonoidHom (transition M hM p q up uq hp hq) =
      transition (f.mapMatrix M) (cofactors_map_zero f M hM) p q
        (Units.map f.toMonoidHom up) (Units.map f.toMonoidHom uq)
        (congrArg f hp) (congrArg f hq) := by
  apply Units.ext
  exact f.map_mul _ _

/-- A homogeneous matrix of degree `d` needs the ambient `O(d)` transition
as well as the normalized-image transition. Here `xp,xq` trivialize `O(1)`
on the chosen projective coordinate charts. -/
def twistedTransition
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) : Rˣ :=
  (xp * xq⁻¹)^d * transition M hM p q up uq hp hq

theorem twistedTransition_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) (xp xq xr : Rˣ) (d : ℕ) :
    twistedTransition M hM p q up uq hp hq xp xq d *
      twistedTransition M hM q r uq ur hq hr xq xr d =
        twistedTransition M hM p r up ur hp hr xp xr d := by
  have ha : (xp * xq⁻¹)^d * (xq * xr⁻¹)^d = (xp * xr⁻¹)^d := by
    rw [← mul_pow]
    congr 1
    group
  dsimp [twistedTransition]
  calc
    _ = ((xp * xq⁻¹)^d * (xq * xr⁻¹)^d) *
        (transition M hM p q up uq hp hq * transition M hM q r uq ur hq hr) := by
      ac_rfl
    _ = _ := by rw [ha, transition_cocycle]

/-- The degree-`d` local first-column equations transform by the twisted
unit, so their local principal ideals agree. -/
theorem homogeneous_first_column_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) :
    M q.1 0 * (↑(xq⁻¹) : R)^d =
      (twistedTransition M hM p q up uq hp hq xp xq d : R) *
        (M p.1 0 * (↑(xp⁻¹) : R)^d) := by
  have ha : ((xp * xq⁻¹)^d : Rˣ) * (xp⁻¹)^d = (xq⁻¹)^d := by
    rw [← mul_pow]
    congr 1
    calc
      _ = (xp * xp⁻¹) * xq⁻¹ := by ac_rfl
      _ = xq⁻¹ := by rw [mul_inv_cancel, one_mul]
  have hb : (↑(xp * xq⁻¹) : R)^d * (↑(xp⁻¹) : R)^d = (↑(xq⁻¹) : R)^d :=
    congrArg (fun u : Rˣ => (u : R)) ha
  rw [row_overlap M hM p q up uq hp hq 0]
  change ((transition M hM p q up uq hp hq : R) * M p.1 0) * (↑(xq⁻¹) : R)^d =
    ((↑(xp * xq⁻¹) : R)^d * (transition M hM p q up uq hp hq : R)) *
      (M p.1 0 * (↑(xp⁻¹) : R)^d)
  rw [← hb]
  ring

section Differential

variable (K : Type*) [CommRing K] [Algebra K R]

/-- Logarithmic differential in the actual universal Kähler module. -/
def unitDlog (u : Rˣ) : Ω[R⁄K] :=
  (↑(u⁻¹) : R) • KaehlerDifferential.D K R (u : R)

@[simp] theorem unitDlog_one : unitDlog K (1 : Rˣ) = 0 := by
  simp [unitDlog]

theorem unitDlog_mul (u v : Rˣ) :
    unitDlog K (u * v) = unitDlog K u + unitDlog K v := by
  simp only [unitDlog, _root_.mul_inv_rev, Units.val_mul, Derivation.leibniz,
    smul_add, smul_smul]
  have hu : ((↑(v⁻¹) : R) * ↑(u⁻¹)) * ↑u = ↑(v⁻¹) := by simp [mul_assoc]
  have hv : ((↑(v⁻¹) : R) * ↑(u⁻¹)) * ↑v = ↑(u⁻¹) := by
    calc
      _ = (↑(u⁻¹) : R) * (↑(v⁻¹) * ↑v) := by ring
      _ = ↑(u⁻¹) := by rw [Units.inv_mul, mul_one]
  rw [hu, hv, add_comm]

theorem unitDlog_inv (u : Rˣ) : unitDlog K u⁻¹ = -unitDlog K u := by
  have h := unitDlog_mul K u u⁻¹
  simp only [mul_inv_cancel, unitDlog_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem unitDlog_pow (u : Rˣ) (n : ℕ) : unitDlog K (u^n) = n • unitDlog K u := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, unitDlog_mul, ih, succ_nsmul]

/-- Evaluation by any derivation gives the ordinary logarithmic derivative;
the construction is genuinely universal, rather than an assumed trace. -/
theorem unitDlog_apply
    {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower K R V]
    (d : Derivation K R V) (u : Rˣ) :
    d.liftKaehlerDifferential (unitDlog K u) = (↑(u⁻¹) : R) • d (u : R) := by
  simp [unitDlog]

/-- The universal logarithmic differential commutes with restriction to an
algebra, including every further localization of a chart overlap. -/
theorem unitDlog_map
    {S : Type*} [CommRing S] [Algebra K S] [Algebra R S] [IsScalarTower K R S]
    (u : Rˣ) :
    KaehlerDifferential.map K K R S (unitDlog K u) =
      unitDlog K (Units.map (algebraMap R S).toMonoidHom u) := by
  simp only [unitDlog, map_smul, KaehlerDifferential.map_D,
    Units.coe_map_inv, Units.coe_map]
  exact (algebraMap_smul S (↑(u⁻¹) : R) _).symm

/-- The ambient twist is retained in the Kähler cocycle. The actual Segre
entries have `d=14`; identifying the seed divisor class is a separate binding. -/
theorem twistedTransition_dlog
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) :
    unitDlog K (twistedTransition M hM p q up uq hp hq xp xq d) =
      d • (unitDlog K xp - unitDlog K xq) +
        unitDlog K (transition M hM p q up uq hp hq) := by
  rw [twistedTransition, unitDlog_mul, unitDlog_pow, unitDlog_mul, unitDlog_inv,
    sub_eq_add_neg]

/-- The actual Kähler Čech one-cocycle of the normalized image generators. -/
theorem transition_dlog_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) :
    unitDlog K (transition M hM p q up uq hp hq) +
      unitDlog K (transition M hM q r uq ur hq hr) =
        unitDlog K (transition M hM p r up ur hp hr) := by
  rw [← unitDlog_mul, transition_cocycle]

theorem transition_dlog_reverse
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    unitDlog K (transition M hM q p uq up hq hp) =
      -unitDlog K (transition M hM p q up uq hp hq) := by
  rw [transition_reverse, unitDlog_inv]

end Differential
end CycleQ2SegreCech

#print axioms CycleQ2SegreCech.transition_cocycle
#print axioms CycleQ2SegreCech.first_column_ideal_overlap
#print axioms CycleQ2SegreCech.transition_dlog_cocycle
#print axioms CycleQ2SegreCech.unitDlog_apply
end
end


/- Component: continuation_2/OpenSquareLifting.lean -/
section
/-!
A nonsingular square polynomial system has a finite separable generic point
inside any principal open containing the seed.  The open condition is imposed
by an actual additional equation u * c(x) - 1, whose Jacobian is block triangular.
This is an algebraic existence statement, not a formal-series lifting premise.
It creates no particular incidence seed or rank certificate.
-/

noncomputable section

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2OpenSquareLifting

open MvPolynomial HoldoutConstruction

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse coordinate is the left summand; the original coordinates are
in the right summand. -/
def extendedPoint (x : ι → T) (u : T) : Unit ⊕ ι → T :=
  Sum.elim (fun _ => u) x

/-- Actual polynomial equations for the chosen square system on the principal
open defined by c. -/
def openSystem (equations : ι → MvPolynomial ι R) (c : MvPolynomial ι R) :
    Unit ⊕ ι → MvPolynomial (Unit ⊕ ι) R :=
  Sum.elim (fun _ => X (Sum.inl ()) * rename Sum.inr c - 1)
    (fun i => rename Sum.inr (equations i))

@[simp] theorem aeval_extended_rename (x : ι → T) (u : T)
    (p : MvPolynomial ι R) :
    aeval (extendedPoint x u) (rename (Sum.inr : ι → Unit ⊕ ι) p) = aeval x p := by
  rw [aeval_rename]
  rfl

@[simp] theorem pderiv_inverse_rename (p : MvPolynomial ι R) :
    pderiv (Sum.inl ()) (rename (Sum.inr : ι → Unit ⊕ ι) p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [pderiv_mul, hp, pderiv_X, Pi.single_apply]

@[simp] theorem pderiv_original_rename (i : ι) (p : MvPolynomial ι R) :
    pderiv (Sum.inr i) (rename (Sum.inr : ι → Unit ⊕ ι) p) =
      rename Sum.inr (pderiv i p) :=
  pderiv_rename Sum.inr_injective i p

/-- An actual solution with an inverse for c evaluates every augmented
polynomial equation to zero. -/
theorem openSystem_seed (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (x : ι → T) (u : T)
    (hx : ∀ i, aeval x (equations i) = 0) (hu : u * aeval x c = 1) :
    ∀ i, aeval (extendedPoint x u) (openSystem equations c i) = 0 := by
  intro i
  cases i with
  | inl z => cases z; simpa [openSystem, aeval_rename, extendedPoint, Function.comp_def] using sub_eq_zero.mpr hu
  | inr i => simpa [openSystem] using hx i

/-- The full augmented Jacobian is a triangular block matrix.  This equality
holds at every point, independently of the polynomial equations. -/
theorem openSystem_jacobian_det (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (x : ι → T) (u : T) :
    Matrix.det (fun i j => aeval (extendedPoint x u)
      (pderiv i (openSystem equations c j))) =
    aeval x c * Matrix.det (fun i j => aeval x (pderiv i (equations j))) := by
  have hmatrix :
      (fun i j => aeval (extendedPoint x u) (pderiv i (openSystem equations c j))) =
      Matrix.fromBlocks (fun (_ _ : Unit) => aeval x c)
        (0 : Matrix Unit ι T)
        (fun i (_ : Unit) => u * aeval x (pderiv i c))
        (fun i j => aeval x (pderiv i (equations j))) := by
    ext i j
    cases i with
    | inl z =>
      cases z
      cases j with
      | inl w => cases w; simp [openSystem, aeval_rename, extendedPoint, Function.comp_def, Matrix.fromBlocks]
      | inr j => simp [openSystem, Matrix.fromBlocks]
    | inr i =>
      cases j with
      | inl w =>
        cases w
        simp [openSystem, aeval_rename, extendedPoint, Function.comp_def, Matrix.fromBlocks, pderiv_X]
      | inr j => simp [openSystem, Matrix.fromBlocks]
  rw [hmatrix, Matrix.det_fromBlocks_zero₁₂, Matrix.det_unique]

/-- Every solution of the augmented system solves the original system, and
its value of c is a unit. -/
theorem solution_on_open (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (z : Unit ⊕ ι → T)
    (hz : ∀ i, aeval z (openSystem equations c i) = 0) :
    (∀ i, aeval (fun i => z (Sum.inr i)) (equations i) = 0) ∧
      IsUnit (aeval (fun i => z (Sum.inr i)) c) := by
  have hrename (p : MvPolynomial ι R) :
      aeval z (rename (Sum.inr : ι → Unit ⊕ ι) p) =
        aeval (fun i => z (Sum.inr i)) p := by rw [aeval_rename]; rfl
  constructor
  · intro i
    simpa only [openSystem, Sum.elim_inr, hrename] using hz (Sum.inr i)
  · have hi := hz (Sum.inl ())
    simp only [openSystem, Sum.elim_inl, map_sub, map_mul, aeval_X, map_one,
      hrename, sub_eq_zero] at hi
    refine ⟨⟨aeval (fun i => z (Sum.inr i)) c, z (Sum.inl ()), ?_, hi⟩, rfl⟩
    exact (mul_comm (aeval (fun i => z (Sum.inr i)) c) (z (Sum.inl ()))).trans hi

section GenericPoint

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] [Algebra R K] [Nontrivial T]

/-- A genuine finite separable generic solution inside the specified open
locus, obtained from a nonsingular special-fiber seed.  Coefficients must
embed in K; the special-fiber coefficient map need not be injective. -/
theorem square_system_generic_lift_on_open
    (equations : ι → MvPolynomial ι R) (c : MvPolynomial ι R)
    (seed : ι → T)
    (hseed : ∀ i, aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det
      (fun i j => aeval seed (pderiv i (equations j)))))
    (hc : IsUnit (aeval seed c))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (SquareGenericAlgebra K (openSystem equations c)), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I) ∧
      ∃ x : ι → ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I),
        (∀ i, aeval x (equations i) = 0) ∧ IsUnit (aeval x c) := by
  obtain ⟨u, hu⟩ := hc.exists_left_inv
  have haug := openSystem_seed equations c seed u hseed hu
  have hjaug : IsUnit (Matrix.det (fun i j => aeval (extendedPoint seed u)
      (pderiv i (openSystem equations c j)))) := by
    rw [openSystem_jacobian_det]
    exact hc.mul hjac
  obtain ⟨I, hI, hfinite, hsep, hsol, hj⟩ :=
    ReflectionCoupledFano.square_system_generic_lift (K := K)
      (openSystem equations c) (extendedPoint seed u) haug hjaug hinj
  clear hj
  generalize hcoords : squareGenericCoordinates (K := K) (openSystem equations c) I = z at hsol
  refine ⟨I, hI, hfinite, hsep, (fun i => z (Sum.inr i)), ?_, ?_⟩
  · intro i
    have hi := hsol (Sum.inr i)
    change aeval z (rename (Sum.inr : ι → Unit ⊕ ι) (equations i)) = 0 at hi
    rw [aeval_rename] at hi
    exact hi
  · have hi := hsol (Sum.inl ())
    change aeval z (X (Sum.inl ()) * rename (Sum.inr : ι → Unit ⊕ ι) c - 1) = 0 at hi
    simp only [map_sub, map_mul, aeval_X, map_one, aeval_rename, sub_eq_zero] at hi
    refine ⟨⟨aeval (fun i => z (Sum.inr i)) c, z (Sum.inl ()), ?_, hi⟩, rfl⟩
    exact (mul_comm (aeval (fun i => z (Sum.inr i)) c) (z (Sum.inl ()))).trans hi

end GenericPoint

end CycleQ2OpenSquareLifting

#print axioms CycleQ2OpenSquareLifting.openSystem_jacobian_det
#print axioms CycleQ2OpenSquareLifting.square_system_generic_lift_on_open
end
end


/- Component: continuation_2/SquareAdicLifting.lean -/
section
/-!
Actual adic lifting of square polynomial systems with invertible seed Jacobian.
The proof uses the established étale Jacobian localization and mathlib's
compatible infinitesimal lifts into an adically complete ring.  The seed is
preserved.  No existence of a formal solution is assumed.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SquareAdicLifting

open MvPolynomial HoldoutConstruction

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual polynomial presentation map into its Jacobian localization. -/
def polynomialToEtale (equations : ι → MvPolynomial ι R) :
    MvPolynomial ι R →ₐ[R] SquareEtaleRing equations :=
  (IsScalarTower.toAlgHom R (SquareSystemRing equations) (SquareEtaleRing equations)).comp
    (Ideal.Quotient.mkₐ R (Ideal.span (Set.range equations)))

@[simp] theorem polynomialToEtale_equation (equations : ι → MvPolynomial ι R) (i : ι) :
    polynomialToEtale equations (equations i) = 0 := by
  have hz : Ideal.Quotient.mk (Ideal.span (Set.range equations)) (equations i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  change algebraMap (SquareSystemRing equations) (SquareEtaleRing equations)
    (Ideal.Quotient.mk _ (equations i)) = 0
  rw [hz, map_zero]

/-- The square system lifts from the residue ring into any complete adic
algebra, while retaining its specified residue coordinates. -/
theorem square_system_adic_lift (equations : ι → MvPolynomial ι R)
    (I : Ideal S) [IsAdicComplete I S] (seed : ι → S ⧸ I)
    (hseed : ∀ i, aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det
      (fun i j => aeval seed (pderiv i (equations j))))) :
    ∃ x : ι → S,
      (∀ i, Ideal.Quotient.mk I (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) := by
  letI : Algebra.Etale R (SquareEtaleRing equations) :=
    square_system_jacobian_etale equations
  let f : SquareEtaleRing equations →ₐ[R] S ⧸ I :=
    squareSystemEtaleEval equations seed hseed hjac
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete f
  let x : ι → S := fun i => g (polynomialToEtale equations (X i))
  have heval : aeval x = g.comp (polynomialToEtale equations) := by
    ext i
    simp [x]
  have hres : f.comp (polynomialToEtale equations) = aeval seed := by
    ext i
    simp [f, polynomialToEtale, squareSystemEtaleEval, squareSystemEval,
      IsLocalization.Away.liftAlgHom, Ideal.Quotient.lift_mk]
  refine ⟨x, ?_, ?_⟩
  · intro i
    have h := AlgHom.congr_fun hg (polynomialToEtale equations (X i))
    change Ideal.Quotient.mk I (x i) = f (polynomialToEtale equations (X i)) at h
    rw [h]
    have hs := AlgHom.congr_fun hres (X i)
    simpa only [AlgHom.comp_apply, aeval_X] using hs
  · intro i
    rw [heval, AlgHom.comp_apply, polynomialToEtale_equation, map_zero]

section PowerSeries

variable {K : Type*} [CommRing K]

/-- Square equations with arbitrary formal coefficients have an actual
formal solution through each nonsingular constant seed.  The hypotheses
are polynomial evaluation and the actual partial-derivative Jacobian. -/
theorem square_system_powerSeries_lift
    (equations : ι → MvPolynomial ι (PowerSeries K)) (seed : ι → K)
    (hseed : ∀ i, eval₂ PowerSeries.constantCoeff seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det (fun i j =>
      eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j))))) :
    ∃ x : ι → PowerSeries K,
      (∀ i, PowerSeries.constantCoeff (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) := by
  letI : Algebra (PowerSeries K) K := PowerSeries.constantCoeff.toAlgebra
  let cc : PowerSeries K →ₐ[PowerSeries K] K :=
    { PowerSeries.constantCoeff with commutes' := by intro r; rfl }
  let I : Ideal (PowerSeries K) := RingHom.ker cc
  have hI : I = Ideal.span {PowerSeries.X} := by
    ext z
    simp only [I, RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    rfl
  letI : IsAdicComplete I (PowerSeries K) := by
    rw [hI]
    infer_instance
  let e : ((PowerSeries K) ⧸ I) ≃ₐ[PowerSeries K] K :=
    Ideal.quotientKerAlgEquivOfSurjective (f := cc) PowerSeries.constantCoeff_surj
  let seed' : ι → (PowerSeries K) ⧸ I := fun i => e.symm (seed i)
  have heval (p : MvPolynomial ι (PowerSeries K)) :
      aeval seed' p = e.symm (eval₂ PowerSeries.constantCoeff seed p) := by
    exact (MvPolynomial.comp_aeval_apply seed e.symm.toAlgHom p).symm
  have hs : ∀ i, aeval seed' (equations i) = 0 := by
    intro i
    rw [heval, hseed i, map_zero]
  have hj : IsUnit (Matrix.det (fun i j => aeval seed' (pderiv i (equations j)))) := by
    simp only [heval]
    have hd :
        Matrix.det (fun i j => e.symm
          (eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))) =
        e.symm (Matrix.det (fun i j =>
          eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))) :=
      (e.symm.toAlgHom.map_det (fun i j =>
        eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))).symm
    rw [hd]
    exact hjac.map e.symm.toRingEquiv.toRingHom
  obtain ⟨x, hx, heq⟩ := square_system_adic_lift equations I seed' hs hj
  refine ⟨x, ?_, heq⟩
  intro i
  have hi := congrArg e (hx i)
  change cc (x i) = e (e.symm (seed i)) at hi
  have hcc (z : PowerSeries K) : cc z = PowerSeries.constantCoeff z := rfl
  simpa only [AlgEquiv.apply_symm_apply, hcc] using hi

end PowerSeries

end CycleQ2SquareAdicLifting

#print axioms CycleQ2SquareAdicLifting.square_system_adic_lift
#print axioms CycleQ2SquareAdicLifting.square_system_powerSeries_lift
end
end


/- Component: continuation_2/SegreFormalLifting.lean -/
section
/-!
# Formal lifting with genuine redundant polynomial equations

A nonsingular square subsystem lifts through its seed. If the residual
polynomials satisfy actual polynomial relations whose complementary block
is invertible at the seed, every omitted equation vanishes along that lift.
All coefficient series may vary: the theorem is not a tangent-only statement.
No seed or minor of the particular large incidence system is assumed proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace CycleQ2SegreFormalLifting

open MvPolynomial Matrix

variable {K ι κ : Type*} [CommRing K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The complete nonlinear system has a seed-preserving formal solution.
The premises concern polynomial identities and the two actual seed minors;
none assumes a formal solution of either the full or square system. -/
theorem lift_all_equations
    (equations : ι → MvPolynomial ι (PowerSeries K))
    (residual : κ → MvPolynomial ι (PowerSeries K))
    (A : Matrix κ κ (MvPolynomial ι (PowerSeries K)))
    (B : Matrix κ ι (MvPolynomial ι (PowerSeries K)))
    (hrelations : A *ᵥ residual + B *ᵥ equations = 0)
    (seed : ι → K)
    (hseed : ∀ i, eval₂ PowerSeries.constantCoeff seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det (fun i j =>
      eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))))
    (hcomplement : IsUnit (eval₂ PowerSeries.constantCoeff seed A.det)) :
    ∃ x : ι → PowerSeries K,
      (∀ i, PowerSeries.constantCoeff (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) ∧
      (∀ j, aeval x (residual j) = 0) := by
  obtain ⟨x, hx, heq⟩ :=
    CycleQ2SquareAdicLifting.square_system_powerSeries_lift equations seed hseed hjac
  have hcc (p : MvPolynomial ι (PowerSeries K)) :
      PowerSeries.constantCoeff (aeval x p) = eval₂ PowerSeries.constantCoeff seed p := by
    induction p using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, aeval_X, eval₂_mul, eval₂_X, hp, hx]
  have hunit : IsUnit (aeval x A.det) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [hcc]
    exact hcomplement
  let φ : MvPolynomial ι (PowerSeries K) →+* PowerSeries K :=
    (aeval x).toRingHom
  have heq' : φ ∘ equations = 0 := by
    funext i
    exact heq i
  have hr : φ ∘ residual = 0 :=
    CycleQ2SegreRelations.evaluated_residual_eq_zero
      φ A B residual equations hrelations heq' hunit
  refine ⟨x, hx, heq, ?_⟩
  intro j
  exact congrFun hr j

end CycleQ2SegreFormalLifting

#print axioms CycleQ2SegreFormalLifting.lift_all_equations
end
end


