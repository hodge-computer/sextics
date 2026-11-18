import Proposal.PExplicitWitnessDefinitions
import Proposal.PDescentFrozenIrreducible
import Mathlib.Tactic.ComputeDegree
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Denominator legality through an actual QQ polynomial specialization. -/
set_option autoImplicit false
noncomputable section
namespace HodgeTestbed.ExplicitWitness
open MvPolynomial HodgeTestbed.Frozen

def linePoint (i : Fin 6) : Polynomial ℚ := if i = 0 then Polynomial.X else 1

def lineMap : SexticPoly →+* Polynomial ℚ := eval₂Hom Polynomial.C linePoint

def lineF : Polynomial ℚ := (634) + (58) * Polynomial.X^2 + (28) * Polynomial.X^4 + (14) * Polynomial.X^6

def lineD : Polynomial ℚ := (-37798690365894673291452701368320) * Polynomial.X + (-20313643691181699333801526394880) * Polynomial.X^3 + (10194122788303772906793555517440) * Polynomial.X^5 + (13984114727676480763218606489600) * Polynomial.X^7 + (2405981827067502652967069245440) * Polynomial.X^9 + (-1100543548755039613457925242880) * Polynomial.X^11 + (-481499986679670392862224670720) * Polynomial.X^13

def lineQuotient : Polynomial ℚ := (1929092833063476110000417771520) * Polynomial.X + (333989616925742281143292477440) * Polynomial.X^3 + (-9824541099692773409533992960) * Polynomial.X^5 + (-34392856191405028061587476480) * Polynomial.X^7

def lineRemainder : Polynomial ℚ := (-1260843546528138527031717568512000) * Polynomial.X + (-343950445139783919958673187840000) * Polynomial.X^3 + (-56963115261961392137884554240000) * Polynomial.X^5

theorem lineMap_F : lineMap Frozen.F = lineF := by
  norm_num [lineMap, linePoint, Fin.ext_iff, Frozen.F, Frozen.X0, Frozen.X1, Frozen.X2,
    Frozen.Y0, Frozen.Y1, Frozen.Y2, lineF]
  <;> ring

theorem lineMap_D : lineMap D = lineD := by
  norm_num [lineMap, linePoint, Fin.ext_iff, D, G, P, Q, HP, HQ, h0P, deltaP, deltaQ,
    pA, pB, pC, pD, qA, qB, qC, qD,
    Frozen.X0, Frozen.X1, Frozen.X2, Frozen.Y0, Frozen.Y1, Frozen.Y2, lineD]
  <;> ring

theorem line_division : lineD = lineF * lineQuotient + lineRemainder := by
  unfold lineD lineF lineQuotient lineRemainder
  ring

theorem lineRemainder_ne_zero : lineRemainder ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial ℚ => p.coeff 1) h
  norm_num [lineRemainder] at hc

theorem lineF_natDegree : lineF.natDegree = 6 := by
  unfold lineF
  compute_degree!

theorem lineRemainder_natDegree : lineRemainder.natDegree = 5 := by
  unfold lineRemainder
  compute_degree!

theorem F_not_dvd_D : ¬ Frozen.F ∣ D := by
  rintro ⟨k, hk⟩
  have hm : lineD = lineF * lineMap k := by
    rw [← lineMap_D, hk, map_mul, lineMap_F]
  have hr : lineRemainder = lineF * (lineMap k - lineQuotient) := by
    calc
      lineRemainder = lineD - lineF * lineQuotient := by rw [line_division]; ring
      _ = lineF * (lineMap k - lineQuotient) := by rw [hm]; ring
  have hd : lineF ∣ lineRemainder := ⟨_, hr⟩
  have hdegree := Polynomial.natDegree_le_of_dvd hd lineRemainder_ne_zero
  rw [lineF_natDegree, lineRemainder_natDegree] at hdegree
  omega

theorem denominator_ne_zero : D ≠ 0 := by
  intro h
  apply F_not_dvd_D
  rw [h]
  exact dvd_zero _

theorem denominator_legal : DenominatorLegal Frozen.F D :=
  (Descent.frozen_denominator_legal_iff D).mpr F_not_dvd_D

end HodgeTestbed.ExplicitWitness
