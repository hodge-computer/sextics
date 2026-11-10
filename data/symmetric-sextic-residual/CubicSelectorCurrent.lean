import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact algebra for a general-cubic moving-point current

The three displayed rational coefficients represent `eta wedge Theta`,
where `eta = U dr + V ds` is closed and
`Theta = k (dlog(t-a) - dlog(t+a))`.  The weight `k` is unrestricted:
in particular it may be the corrected Cauchy weight `q / f_u(t,u)`.

The local cubic identity proves the cancellation at a moving root for the
Lagrange selector.  These are exact differential identities, not an
existence assertion for the protected sextic primitive.  The prescribed
source still has to be identified after finite trace and chart comparison.
-/

noncomputable section

namespace CubicSelectorCurrent

variable {K : Type*} [Field K]

def movingDenominator (t a : K) : K := t ^ 2 - a ^ 2

def movingVelocity (R S : Derivation ℤ K K) (a U V : K) : K :=
  U * S a - V * R a

def currentT (R S : Derivation ℤ K K) (t a U V k : K) : K :=
  -2 * k * t * movingVelocity R S a U V / movingDenominator t a

def currentR (t a V k : K) : K :=
  2 * k * a * V / movingDenominator t a

def currentS (t a U k : K) : K :=
  -2 * k * a * U / movingDenominator t a

/-- The current differentiation is valid for any rational selector weight.
The needed compatibility and closedness hypotheses are explicit. -/
theorem current_divergence
    (T R S : Derivation ℤ K K) (t a U V k : K)
    (hTt : T t = 1) (hRt : R t = 0) (hSt : S t = 0)
    (hTa : T a = 0) (hTU : T U = 0) (hTV : T V = 0)
    (hTRa : T (R a) = 0) (hTSa : T (S a) = 0)
    (hclosed : R V = S U)
    (hd : movingDenominator t a ≠ 0) :
    T (currentT R S t a U V k) + R (currentR t a V k) +
      S (currentS t a U k) =
      (-2 * t * movingVelocity R S a U V * T k +
        2 * a * (V * R k - U * S k)) / movingDenominator t a := by
  have hTd : T (movingDenominator t a) = 2 * t := by
    simp [movingDenominator, Derivation.leibniz_pow, hTt, hTa, smul_eq_mul]
  have hRd : R (movingDenominator t a) = -2 * a * R a := by
    simp [movingDenominator, Derivation.leibniz_pow, hRt, smul_eq_mul]
    ring
  have hSd : S (movingDenominator t a) = -2 * a * S a := by
    simp [movingDenominator, Derivation.leibniz_pow, hSt, smul_eq_mul]
    ring
  have hTZ : T (movingVelocity R S a U V) = 0 := by
    simp [movingVelocity, Derivation.leibniz, hTU, hTV, hTRa, hTSa]
  have hT2 : T (2 : K) = 0 := T.map_natCast 2
  have hR2 : R (2 : K) = 0 := R.map_natCast 2
  have hS2 : S (2 : K) = 0 := S.map_natCast 2
  simp only [currentT, currentR, currentS, Derivation.leibniz_div,
    Derivation.leibniz, map_neg, smul_eq_mul,
    hTt, hTZ, hTd, hRd, hSd, hclosed, hT2, hR2, hS2]
  field_simp [hd]
  simp only [movingDenominator, movingVelocity]
  ring

/-- Commuting tangent derivations give the mixed derivative hypotheses
automatically when the moving point is constant in the `t` direction. -/
theorem current_divergence_of_commute
    (T R S : Derivation ℤ K K) (t a U V k : K)
    (hTR : ∀ x, T (R x) = R (T x))
    (hTS : ∀ x, T (S x) = S (T x))
    (hTt : T t = 1) (hRt : R t = 0) (hSt : S t = 0)
    (hTa : T a = 0) (hTU : T U = 0) (hTV : T V = 0)
    (hclosed : R V = S U)
    (hd : movingDenominator t a ≠ 0) :
    T (currentT R S t a U V k) + R (currentR t a V k) +
      S (currentS t a U k) =
      (-2 * t * movingVelocity R S a U V * T k +
        2 * a * (V * R k - U * S k)) / movingDenominator t a := by
  apply current_divergence T R S t a U V k hTt hRt hSt hTa hTU hTV
  · rw [hTR, hTa, map_zero]
  · rw [hTS, hTa, map_zero]
  · exact hclosed
  · exact hd

/-- Differentiation of the corrected Cauchy weight `q/f_u`.  The displayed
chain rules are those of the canonical tangent derivatives of `f(t,u)=0`.
No equality between this source and a prescribed sextic source is assumed. -/
theorem cauchy_current_divergence
    (T R S : Derivation ℤ K K) (t a U V q g : K)
    (qu fuu ft fr fs ftu fru fsu qr qs : K)
    (hTt : T t = 1) (hRt : R t = 0) (hSt : S t = 0)
    (hTa : T a = 0) (hTU : T U = 0) (hTV : T V = 0)
    (hTRa : T (R a) = 0) (hTSa : T (S a) = 0)
    (hclosed : R V = S U)
    (hTq : T q = -qu * ft / g)
    (hRq : R q = qr - qu * fr / g)
    (hSq : S q = qs - qu * fs / g)
    (hTg : T g = ftu - fuu * ft / g)
    (hRg : R g = fru - fuu * fr / g)
    (hSg : S g = fsu - fuu * fs / g)
    (hd : movingDenominator t a ≠ 0) (hg : g ≠ 0) :
    T (currentT R S t a U V (q / g)) + R (currentR t a V (q / g)) +
      S (currentS t a U (q / g)) =
      2 * ((g * qu - q * fuu) *
            (t * movingVelocity R S a U V * ft + a * (U * fs - V * fr)) +
          g * q * (t * movingVelocity R S a U V * ftu + a * (U * fsu - V * fru)) -
          a * g ^ 2 * (U * qs - V * qr)) /
        (movingDenominator t a * g ^ 3) := by
  rw [current_divergence T R S t a U V (q / g)
    hTt hRt hSt hTa hTU hTV hTRa hTSa hclosed hd]
  simp only [Derivation.leibniz_div, smul_eq_mul,
    hTq, hRq, hSq, hTg, hRg, hSg]
  field_simp [hd, hg]
  ring

def shiftedCubic (u b g a l : K) : K :=
  (u - b) * (g + a * (u - b) + l * (u - b) ^ 2)

def shiftedCubicNormal (u b g a l : K) : K :=
  g + 2 * a * (u - b) + 3 * l * (u - b) ^ 2

def cubicSelector (u b g a l : K) : K :=
  (g + a * (u - b) + l * (u - b) ^ 2) / g

def cubicSelectorNormal (u b g a l : K) : K :=
  (a + 2 * l * (u - b)) / g

def shiftedQuadratic (u b g a l : K) : K :=
  g + a * (u - b) + l * (u - b) ^ 2

def shiftedQuadraticNormal (u b a l : K) : K :=
  a + 2 * l * (u - b)

def shiftedCubicSecond (u b a l : K) : K :=
  2 * a + 6 * l * (u - b)

/-- At a moving cubic root, the selector's Wronskian is a multiple of the
cubic itself.  The quotient is linear in the normal variable.  The root's
velocity cancels, leaving only coefficient and normalizer derivatives. -/
theorem cubic_selector_local_cancellation
    (D : Derivation ℤ K K) (u b g a l : K)
    (hu : D u = 0) (hg : g ≠ 0) :
    cubicSelectorNormal u b g a l * D (shiftedCubic u b g a l) -
      shiftedCubicNormal u b g a l * D (cubicSelector u b g a l) =
      shiftedCubic u b g a l *
        (((3 * l * D g - g * D l) * (u - b) +
          (2 * a * D g - g * D a)) / g ^ 2) := by
  simp only [cubicSelectorNormal, shiftedCubicNormal, shiftedCubic,
    cubicSelector, Derivation.leibniz_div, Derivation.leibniz,
    Derivation.leibniz_pow, map_add, map_sub, hu, smul_eq_mul]
  field_simp [hg]
  ring

/-- The corrected Cauchy source also cancels its moving-section pole.
This identity is polynomial: its quotient is quadratic, and no inverse
normalizer or nonvanishing hypothesis is needed for the cancellation. -/
theorem cauchy_selector_local_cancellation
    (D : Derivation ℤ K K) (u b g a l : K)
    (hu : D u = 0) :
    (shiftedCubicNormal u b g a l * shiftedQuadraticNormal u b a l -
        shiftedQuadratic u b g a l * shiftedCubicSecond u b a l) *
        D (shiftedCubic u b g a l) +
      shiftedCubicNormal u b g a l * shiftedQuadratic u b g a l *
        D (shiftedCubicNormal u b g a l) -
      (shiftedCubicNormal u b g a l) ^ 2 * D (shiftedQuadratic u b g a l) =
      shiftedCubic u b g a l *
        (g * D a - 2 * a * D g +
          (2 * g * D l - 6 * l * D g) * (u - b) +
          (2 * a * D l - 3 * l * D a) * (u - b) ^ 2) := by
  have hD2 : D (2 : K) = 0 := D.map_natCast 2
  have hD3 : D (3 : K) = 0 := D.map_natCast 3
  simp only [shiftedCubicNormal, shiftedQuadraticNormal,
    shiftedQuadratic, shiftedCubicSecond, shiftedCubic,
    Derivation.leibniz, Derivation.leibniz_pow,
    map_add, map_sub, hu, hD2, hD3, smul_eq_mul]
  ring

/-- Removing a constant normal-derivative multiple leaves the local Cauchy
cancellation numerator unchanged.  In particular this applies to `q-f_u/3`. -/
theorem cauchy_local_normal_gauge (g gu df dg q qu dq k : K) :
    (g*(qu-k*gu)-(q-k*g)*gu)*df +
      g*(q-k*g)*dg-g^2*(dq-k*dg) =
    (g*qu-q*gu)*df+g*q*dg-g^2*dq := by
  ring

/-- The trace-free cubic selector numerator is linear in the normal variable. -/
theorem traceFree_selector_linear [CharZero K] (u b g a l : K) :
    shiftedQuadratic u b g a l-shiftedCubicNormal u b g a l/3 =
      (2*g+a*(u-b))/3 := by
  simp only [shiftedQuadratic, shiftedCubicNormal]
  field_simp
  ring

end CubicSelectorCurrent

#print axioms CubicSelectorCurrent.current_divergence
#print axioms CubicSelectorCurrent.current_divergence_of_commute
#print axioms CubicSelectorCurrent.cauchy_current_divergence
#print axioms CubicSelectorCurrent.cubic_selector_local_cancellation
#print axioms CubicSelectorCurrent.cauchy_selector_local_cancellation
#print axioms CubicSelectorCurrent.cauchy_local_normal_gauge
#print axioms CubicSelectorCurrent.traceFree_selector_linear
