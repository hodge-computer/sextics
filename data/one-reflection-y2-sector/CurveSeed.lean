import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

/- Adapted for the instance `one-reflection-y2-sector` from the accepted holdout proof by `fqlx`
(prepared with OpenAI ChatGPT assistance). The conic family,
its coefficient relations and the two Jacobian polynomials are fqlx's; only the seed parameter
changes: the quotient of the one-reflection sextic is the holdout quotient with both coupling
coefficients equal, which selects the members of fqlx's conic family with beta = alpha. These
form the roots of an integer polynomial of degree eight with a root in (-13,-12), where every
denominator and both Jacobian polynomials are sign-definite. Adaptation prepared with Claude
Code assistance for `DiamondJM`. -/

/- Source component: CurveSeed -/
section
/-!
An exact characteristic-zero seed for the weighted-conic construction on the
one-reflection quotient. The parameter lies in (-13,-12), where all
denominators and both explicit evaluation minors are nonzero. Existence uses
the intermediate value theorem; no modular-to-characteristic-zero lifting is
assumed.
-/

noncomputable section

namespace HoldoutConic

/-- The members of the conic family whose two coupling coefficients coincide. -/
def g (r : ℝ) : ℝ :=
  r^8 + 7*r^7 - 58*r^6 + 149*r^5 - 178*r^4 + 115*r^3 - 44*r^2 + 10*r - 1

def m (r : ℝ) : ℝ := r^4 - 4*r^3 + 5*r^2 + r - 2

def gEven (r : ℝ) : ℝ :=
  16*r^11 - 80*r^10 + 96*r^9 + 144*r^8 - 380*r^7 + 240*r^6 +
  84*r^5 - 178*r^4 + 63*r^3 + 9*r^2 - 8*r + 1

def gOdd (r : ℝ) : ℝ :=
  8*r^11 - 48*r^10 + 112*r^9 - 16*r^8 - 224*r^7 + 352*r^6 -
  275*r^5 + 101*r^4 + 11*r^3 - 24*r^2 + 8*r - 1

theorem m_pos {r : ℝ} (hr : r < -12) : 0 < m r := by
  have hu : 0 < -12 - r := by linarith
  have he : m r = (-12-r)^4 + 52*(-12-r)^3 + 1013*(-12-r)^2 +
      8759*(-12-r) + 28354 := by unfold m; ring
  rw [he]
  positivity

theorem gEven_neg {r : ℝ} (hr : r < -12) : gEven r < 0 := by
  have hu : 0 < -12 - r := by linarith
  have he : gEven r =
      -(16*(-12-r)^11 + 2192*(-12-r)^10 + 136416*(-12-r)^9 +
      5090544*(-12-r)^8 + 126558340*(-12-r)^7 + 2201052768*(-12-r)^6 +
      27324568596*(-12-r)^5 + 242133834850*(-12-r)^4 +
      1500925474335*(-12-r)^3 + 6198277334931*(-12-r)^2 +
      15347215258480*(-12-r) + 17260636595663) := by unfold gEven; ring
  rw [he, neg_lt_zero]
  positivity

theorem gOdd_neg {r : ℝ} (hr : r < -12) : gOdd r < 0 := by
  have hu : 0 < -12 - r := by linarith
  have he : gOdd r =
      -(8*(-12-r)^11 + 1104*(-12-r)^10 + 69232*(-12-r)^9 +
      2604112*(-12-r)^8 + 65278240*(-12-r)^7 + 1145004320*(-12-r)^6 +
      14339540461*(-12-r)^5 + 128215108903*(-12-r)^4 +
      802107007547*(-12-r)^3 + 3343590558276*(-12-r)^2 +
      8358193880792*(-12-r) + 9491727662881) := by unfold gOdd; ring
  rw [he, neg_lt_zero]
  positivity

theorem gEven_ne_zero {r : ℝ} (hr : r < -12) : gEven r ≠ 0 := ne_of_lt (gEven_neg hr)

theorem gOdd_ne_zero {r : ℝ} (hr : r < -12) : gOdd r ≠ 0 := ne_of_lt (gOdd_neg hr)

theorem exists_parameter : ∃ r : ℝ, -13 < r ∧ r < -12 ∧ g r = 0 := by
  have h13 : g (-13) = 35869443 := by norm_num [g]
  have h12 : g (-12) = -35000185 := by norm_num [g]
  have hc : Continuous g := by unfold g; fun_prop
  have hz : (0 : ℝ) ∈ Set.Icc (g (-12)) (g (-13)) := by
    rw [h12, h13]
    constructor <;> norm_num
  obtain ⟨r, hr, hg⟩ := intermediate_value_Icc' (by norm_num : (-13 : ℝ) ≤ -12)
    hc.continuousOn hz
  refine ⟨r, ?_, ?_, hg⟩
  · rcases lt_or_eq_of_le hr.1 with h | h
    · exact h
    · subst r; linarith
  · rcases lt_or_eq_of_le hr.2 with h | h
    · exact h
    · subst r; linarith

def R (r : ℝ) : ℝ := r*(1-r-r^2)/(1-r)
def M (r : ℝ) : ℝ := r^2*m r/(r-1)^2
def a (r : ℝ) : ℝ := 3*(1-2*r)/(1-r)
def b (r : ℝ) : ℝ := 3*(1-2*r)

theorem quad_neg {r : ℝ} (hr : r < -12) : 1-r-r^2 < 0 := by
  have hu : 0 < -12 - r := by linarith
  have he : -(1-r-r^2) = (-12-r)^2 + 23*(-12-r) + 131 := by ring
  have hp : 0 < -(1-r-r^2) := by rw [he]; positivity
  linarith

theorem R_pos {r : ℝ} (hr : r < -12) : 0 < R r := by
  have hr0 : r < 0 := by linarith
  have hnum : 1-r-r^2 < 0 := quad_neg hr
  have hden : 0 < 1-r := by linarith
  exact div_pos (mul_pos_of_neg_of_neg hr0 hnum) hden

theorem M_pos {r : ℝ} (hr : r < -12) : 0 < M r := by
  have hr0 : r ≠ 0 := by linarith
  have hd : r - 1 ≠ 0 := by linarith
  unfold M
  exact div_pos (mul_pos (by positivity) (m_pos hr)) (by positivity)

theorem a_ne_zero {r : ℝ} (hr : r < -12) : a r ≠ 0 := by
  unfold a
  apply div_ne_zero
  · apply mul_ne_zero (by norm_num)
    linarith
  · linarith

theorem b_ne_zero {r : ℝ} (hr : r < -12) : b r ≠ 0 := by
  unfold b
  apply mul_ne_zero (by norm_num)
  linarith

/-- On the beta = alpha locus of the family, `q^2 = M/(1-r)^3` is compatible with
`q^4 = R`: this is exactly the defining polynomial `g`. -/
theorem parameter_relation {r : ℝ} (hr : r < -12) (hg : g r = 0) :
    (M r)^2 = R r*(1-r)^6 := by
  have h1 : r - 1 ≠ 0 := by linarith
  have h2 : 1 - r ≠ 0 := by linarith
  have key : r^3*(m r)^2 = (1-r-r^2)*(1-r)^9 := by
    unfold g at hg
    unfold m
    linear_combination hg
  unfold M R
  rw [div_pow, div_mul_eq_mul_div, div_eq_div_iff (pow_ne_zero 2 (pow_ne_zero 2 h1)) h2]
  linear_combination r*(1-r)*key

theorem coefficient_relations {r : ℝ} (hr : r < -12) :
    a r*r + 3*r^2 - 3*R r = 0 ∧
    a r + 3*r^2 + 6*r - 3*R r - 3 = 0 ∧
    M r + b r*r + 3*r^2 + 6*r*R r - (R r)^2 - 3*R r = 0 ∧
    b r + 6*r - 3 = 0 := by
  have h1 : 1-r ≠ 0 := by linarith
  have h2 : r-1 ≠ 0 := by linarith
  unfold a b M R m
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  · ring

/-- The one-reflection seed: a member of the holdout conic family with equal coupling
coefficients, together with a base point of the Fermat curve above its alpha. -/
structure Seed where
  r : ℝ
  lower : -13 < r
  upper : r < -12
  root : g r = 0
  q : ℂ
  k : ℂ
  q_power : q^4 = (R r : ℂ)
  k_power : k^6 = (M r : ℂ)/q^2
  k_square : k^2 = 1 - (r : ℂ)
  baseBeta : ℂ
  baseBeta_power : baseBeta^6 = 1 - ((a r : ℂ)/(k*q))^6

theorem Seed.q_ne_zero (p : Seed) : p.q ≠ 0 := by
  intro h
  have hq := p.q_power
  rw [h, zero_pow (by decide)] at hq
  have hR : R p.r ≠ 0 := ne_of_gt (R_pos p.upper)
  exact hR (by exact_mod_cast hq.symm)

theorem Seed.k_ne_zero (p : Seed) : p.k ≠ 0 := by
  have hM : (M p.r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (M_pos p.upper)
  intro h
  have hk := p.k_power
  rw [h, zero_pow (by decide)] at hk
  exact (div_ne_zero hM (pow_ne_zero 2 p.q_ne_zero)) hk.symm

theorem exists_seed : Nonempty Seed := by
  obtain ⟨r, hl, hu, hg⟩ := exists_parameter
  have hM : (M r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (M_pos hu)
  have h1 : (1 - (r : ℂ)) ≠ 0 := by
    have : (1 - r : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  obtain ⟨q, hq⟩ := IsAlgClosed.exists_pow_nat_eq ((M r : ℂ)/(1-(r : ℂ))^3) (by decide : 0 < 2)
  obtain ⟨k, hk⟩ := IsAlgClosed.exists_pow_nat_eq (1-(r : ℂ)) (by decide : 0 < 2)
  have hq0 : q ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hq
    exact (div_ne_zero hM (pow_ne_zero 3 h1)) hq.symm
  have hrel : ((M r : ℂ))^2 = (R r : ℂ)*(1-(r : ℂ))^6 := by
    exact_mod_cast parameter_relation hu hg
  have hq4 : q^4 = (R r : ℂ) := by
    calc
      q^4 = (q^2)^2 := by ring
      _ = ((M r : ℂ)/(1-(r : ℂ))^3)^2 := by rw [hq]
      _ = (R r : ℂ) := by
        rw [div_pow, hrel]
        field_simp <;> ring
  have hk6 : k^6 = (M r : ℂ)/q^2 := by
    calc
      k^6 = (k^2)^3 := by ring
      _ = (1-(r : ℂ))^3 := by rw [hk]
      _ = (M r : ℂ)/q^2 := by
        rw [hq]
        field_simp
  obtain ⟨bb, hbb⟩ := IsAlgClosed.exists_pow_nat_eq (1-((a r : ℂ)/(k*q))^6) (by decide : 0 < 6)
  exact ⟨⟨r, hl, hu, hg, q, k, hq4, hk6, hk, bb, hbb⟩⟩

def Seed.alpha (p : Seed) : ℂ := (a p.r : ℂ)/(p.k*p.q)
def Seed.beta (p : Seed) : ℂ := (b p.r : ℂ)/(p.k^3*p.q)

/-- The seed lies on the Fermat curve through its own alpha and the chosen base beta. -/
theorem Seed.base_relation (p : Seed) : p.alpha^6 + p.baseBeta^6 = 1 := by
  rw [p.baseBeta_power]
  unfold Seed.alpha
  ring

/-- Equal coupling coefficients: `beta = alpha` on this seed. -/
theorem Seed.beta_eq_alpha (p : Seed) : p.beta = p.alpha := by
  have hk := p.k_ne_zero
  have hq := p.q_ne_zero
  have h1 : (1 - p.r : ℝ) ≠ 0 := by linarith [p.upper]
  have hab : (a p.r : ℂ)*(1 - (p.r : ℂ)) = (b p.r : ℂ) := by
    have h : a p.r*(1 - p.r) = b p.r := by
      unfold a b
      field_simp
    exact_mod_cast h
  unfold Seed.alpha Seed.beta
  rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero 3 hk) hq) (mul_ne_zero hk hq)]
  linear_combination (-(a p.r : ℂ)*p.k*p.q) * p.k_square + (-(p.k*p.q)) * hab

def H (alpha beta x0 x1 x2 S P : ℂ) : ℂ :=
  x0^6 + x1^6 + x2^6 + P*(alpha*x0^3*x1 + beta*x1^3*x2) + S^3 - 3*S*P^2

def scaledH (_r z x0 x1 x2 S Q : ℂ) (mm aa bb : ℂ) : ℂ :=
  z*(x0^6+x2^6+S^3) + mm*x1^6 + aa*x0^3*x1*Q + bb*x1^3*x2*Q - 3*S*Q^2

theorem scaled_curve_identity (r z mm aa bb : ℂ)
    (h2 : aa*r + 3*r^2 - 3*z^2 = 0)
    (h4 : aa + 3*r^2 + 6*r - 3*z^2 - 3 = 0)
    (h6 : mm + bb*r + 3*r^2 + 6*r*z^2 - z^4 - 3*z^2 = 0)
    (h8 : bb + 6*r - 3 = 0) (s t : ℂ) :
    scaledH r z (s^2) (s*t) (t^2)
      (-(s^4+z*s^2*t^2+t^4)) (r*s^3*t+z*s*t^3) mm aa bb = 0 := by
  unfold scaledH
  linear_combination s^10*t^2*h2 + z*s^8*t^4*h4 + s^6*t^6*h6 + z*s^4*t^8*h8

theorem Seed.scaled_curve (p : Seed) (s t : ℂ) :
    scaledH (p.r : ℂ) (p.q^2) (s^2) (s*t) (t^2)
      (-(s^4+p.q^2*s^2*t^2+t^4)) ((p.r : ℂ)*s^3*t+p.q^2*s*t^3)
      (M p.r : ℂ) (a p.r : ℂ) (b p.r : ℂ) = 0 := by
  obtain ⟨h2, h4, h6, h8⟩ := coefficient_relations p.upper
  have hqq : (p.q^2)^2 = (R p.r : ℂ) := by
    rw [← pow_mul, show 2*2=4 by decide, p.q_power]
  apply scaled_curve_identity
  · rw [hqq]; exact_mod_cast h2
  · rw [hqq]; exact_mod_cast h4
  · rw [show (p.q^2)^4 = ((p.q^2)^2)^2 by ring, hqq]
    exact_mod_cast h6
  · exact_mod_cast h8

theorem Seed.curve_beta (p : Seed) (s t : ℂ) :
    H p.alpha p.beta (s^2) (p.k*s*t) (t^2)
      (-(s^4+p.q^2*s^2*t^2+t^4))
      (((p.r : ℂ)/p.q)*s^3*t+p.q*s*t^3) = 0 := by
  have hq := p.q_ne_zero
  have hk := p.k_ne_zero
  have hc := p.scaled_curve s t
  have hm : p.k^6*p.q^2 = (M p.r : ℂ) := by
    rw [p.k_power]
    field_simp
  have he : p.q^2 * H p.alpha p.beta (s^2) (p.k*s*t) (t^2)
      (-(s^4+p.q^2*s^2*t^2+t^4))
      (((p.r : ℂ)/p.q)*s^3*t+p.q*s*t^3) =
    scaledH (p.r : ℂ) (p.q^2) (s^2) (s*t) (t^2)
      (-(s^4+p.q^2*s^2*t^2+t^4)) ((p.r : ℂ)*s^3*t+p.q^2*s*t^3)
      (M p.r : ℂ) (a p.r : ℂ) (b p.r : ℂ) := by
    unfold H scaledH Seed.alpha Seed.beta
    field_simp
    linear_combination s^6*t^6*hm
  rw [hc] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hq)

/-- The conic lies on the quotient hypersurface with both coupling coefficients `alpha`. -/
theorem Seed.curve (p : Seed) (s t : ℂ) :
    H p.alpha p.alpha (s^2) (p.k*s*t) (t^2)
      (-(s^4+p.q^2*s^2*t^2+t^4))
      (((p.r : ℂ)/p.q)*s^3*t+p.q*s*t^3) = 0 := by
  have h := p.curve_beta s t
  rwa [p.beta_eq_alpha] at h

end HoldoutConic

#print axioms HoldoutConic.exists_parameter
#print axioms HoldoutConic.parameter_relation
#print axioms HoldoutConic.exists_seed
#print axioms HoldoutConic.Seed.base_relation
#print axioms HoldoutConic.Seed.beta_eq_alpha
#print axioms HoldoutConic.Seed.curve
end
end
