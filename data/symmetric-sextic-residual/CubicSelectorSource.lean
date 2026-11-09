import Proposal.CubicTraceDescent
import Proposal.CubicSelectorCurrent
import Mathlib.Tactic.ComputeDegree

/-!
# The literal source of a normalized moving cubic selector

The shifted normal coordinate is `w = u - beta`. The equation at the
moving section is `l*w^3 + a*w^2 + g*w`, and the full equation differs
by `delta*H`, where `delta = t^2-alpha^2` and `H` is quadratic in `w`.
The leading cubic coefficient is constant in the relative base directions.

`numeratorThree` is three times the numerator obtained by differentiating
the corrected selector `(a*w+2*g)/(3*f_u)`. The two explicit source
coefficients below remove the section denominator and reconstruct the
entire density, modulo the actual cubic equation. This calculation does
not supply a moving-point extension or the required finite source traces.
-/

noncomputable section

namespace CubicSelectorSource

section RingIdentities

variable {R : Type*} [CommRing R]

structure Jet (R : Type*) where
  l : R
  a : R
  g : R
  alpha : R
  aDot : R
  gDot : R
  betaDot : R
  delta : R
  h0 : R
  h1 : R
  h2 : R
  k0 : R
  k1 : R
  k2 : R

def Jet.map {S : Type*} (f : R → S) (j : Jet R) : Jet S where
  l := f j.l
  a := f j.a
  g := f j.g
  alpha := f j.alpha
  aDot := f j.aDot
  gDot := f j.gDot
  betaDot := f j.betaDot
  delta := f j.delta
  h0 := f j.h0
  h1 := f j.h1
  h2 := f j.h2
  k0 := f j.k0
  k1 := f j.k1
  k2 := f j.k2

def cubicB (j : Jet R) : R := j.a+j.delta*j.h2
def cubicC (j : Jet R) : R := j.g+j.delta*j.h1
def cubicD (j : Jet R) : R := j.delta*j.h0

def equation (j : Jet R) (w : R) : R :=
  j.l*w^3+cubicB j*w^2+cubicC j*w+cubicD j

def normal (j : Jet R) (w : R) : R :=
  3*j.l*w^2+2*cubicB j*w+cubicC j

def secondNormal (j : Jet R) (w : R) : R := 6*j.l*w+2*cubicB j

def motion (j : Jet R) (w : R) : R :=
  j.alpha*((j.aDot-3*j.l*j.betaDot)*w^2+
    (j.gDot-2*j.a*j.betaDot)*w-j.g*j.betaDot)+
    j.delta*(j.k0+j.k1*w+j.k2*w^2)

def normalMotion (j : Jet R) (w : R) : R :=
  j.alpha*(2*(j.aDot-3*j.l*j.betaDot)*w+j.gDot-2*j.a*j.betaDot)+
    j.delta*(j.k1+2*j.k2*w)

def numeratorThree (j : Jet R) (w : R) : R :=
  (normal j w*j.a-(j.a*w+2*j.g)*secondNormal j w)*motion j w+
    normal j w*(j.a*w+2*j.g)*normalMotion j w-
    j.alpha*(normal j w)^2*(j.aDot*w+2*j.gDot-j.a*j.betaDot)

def quotientLinear (j : Jet R) : R := j.a*j.k2-j.alpha*j.aDot*j.h2

def quotientConstantNumerator (j : Jet R) : R :=
  cubicB j*quotientLinear j+3*j.l*j.alpha*(j.aDot*j.h1-2*j.gDot*j.h2)

def remainderOneThree (j : Jet R) : R :=
  cubicC j*(4*j.a*j.alpha*j.betaDot*j.h2+2*j.a*j.k1-
    j.alpha*j.aDot*j.h1-8*j.alpha*j.gDot*j.h2+4*j.g*j.k2)+
    6*j.l*(-2*j.alpha*j.betaDot*j.g*j.h1+3*j.alpha*j.gDot*j.h0-2*j.g*j.k0)

def remainderTwoThree (j : Jet R) : R :=
  cubicB j*(4*j.a*j.alpha*j.betaDot*j.h2+2*j.a*j.k1-
    8*j.alpha*j.gDot*j.h2+4*j.g*j.k2)+
    3*quotientLinear j*cubicC j-j.alpha*j.aDot*j.h1*(j.a+j.delta*j.h2)+
    3*j.l*(-j.a*j.alpha*j.betaDot*j.h1-j.a*j.k0+3*j.alpha*j.aDot*j.h0-
      4*j.alpha*j.betaDot*j.g*j.h2+2*j.alpha*j.gDot*j.h1-2*j.g*j.k1)

def sourceZeroNumerator (j : Jet R) : R :=
  cubicC j*quotientConstantNumerator j+
    3*j.l*cubicD j*quotientLinear j-j.l*remainderOneThree j

def sourceOneNumerator (j : Jet R) : R :=
  cubicB j*quotientConstantNumerator j+
    3*j.l*cubicC j*quotientLinear j-j.l*remainderTwoThree j

theorem sourceZeroNumerator_map {S : Type*} [CommRing S]
    (f : R →+* S) (j : Jet R) :
    sourceZeroNumerator (j.map f) = f (sourceZeroNumerator j) := by
  simp [sourceZeroNumerator, cubicB, cubicC, cubicD, quotientLinear,
    quotientConstantNumerator, remainderOneThree, Jet.map, map_ofNat]

theorem sourceOneNumerator_map {S : Type*} [CommRing S]
    (f : R →+* S) (j : Jet R) :
    sourceOneNumerator (j.map f) = f (sourceOneNumerator j) := by
  simp [sourceOneNumerator, cubicB, cubicC, quotientLinear,
    quotientConstantNumerator, remainderTwoThree, Jet.map, map_ofNat]

def localQuotient (j : Jet R) (w : R) : R :=
  j.g*j.aDot-2*j.a*j.gDot-6*j.l*j.gDot*w-3*j.l*j.aDot*w^2

/-- The section cancellation and the linear-source reconstruction hold in
one polynomial identity. No root simplicity or inverses are used here. -/
theorem cleared_source_identity (j : Jet R) (w : R) :
    6*j.l^2*numeratorThree j w =
      j.delta*(normal j w*(2*sourceOneNumerator j)-
        secondNormal j w*(sourceZeroNumerator j+2*sourceOneNumerator j*w))+
      equation j w*(18*j.l^2*j.alpha*localQuotient j w+
        6*j.l*j.delta*(3*j.l*quotientLinear j*w+quotientConstantNumerator j)) := by
  simp only [numeratorThree, normal, secondNormal, motion, normalMotion,
    equation, cubicB, cubicC, cubicD, sourceZeroNumerator, sourceOneNumerator,
    quotientLinear, quotientConstantNumerator, remainderOneThree,
    remainderTwoThree, localQuotient]
  ring

end RingIdentities

section FieldIdentities

variable {K : Type*} [Field K] [CharZero K]

def sourceZero (j : Jet K) : K := sourceZeroNumerator j/(18*j.l^2)
def sourceOne (j : Jet K) : K := sourceOneNumerator j/(9*j.l^2)

def selector (j : Jet K) (w : K) : K := (j.a*w+2*j.g)/3

def movingOperator (T R S : Derivation ℤ K K) (t alpha U V : K) : Derivation ℤ K K :=
  (t*CubicSelectorCurrent.movingVelocity R S alpha U V) • T+
    alpha • (U • S-V • R)

/-- Moving the normal origin changes the constant source coefficient.
This product must be unshifted before taking a finite trace. -/
theorem linearDensity_shift (g gu u beta s0 s1 : K) :
    CubicTraceDescent.linearDensity g gu (u-beta) s0 s1 =
      CubicTraceDescent.linearDensity g gu u (s0-beta*s1) s1 := by
  unfold CubicTraceDescent.linearDensity
  ring

/-- The source produced by this particular selector, before any finite
trace or comparison with the protected target. -/
theorem selector_density (j : Jet K) (w : K)
    (hl : j.l ≠ 0) (hd : j.delta ≠ 0) (hg : normal j w ≠ 0)
    (hf : equation j w = 0) :
    2*numeratorThree j w/(3*j.delta*(normal j w)^3) =
      CubicTraceDescent.linearDensity (normal j w) (secondNormal j w) w
        (sourceZero j) (sourceOne j) := by
  have h := cleared_source_identity j w
  rw [hf, zero_mul, add_zero] at h
  have hnum : numeratorThree j w =
      3*j.delta*(normal j w*sourceOne j-
        secondNormal j w*(sourceZero j+sourceOne j*w)) := by
    apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (6 : K) ≠ 0) (pow_ne_zero 2 hl))
    calc
      6*j.l^2*numeratorThree j w = _ := h
      _ = 6*j.l^2*(3*j.delta*(normal j w*sourceOne j-
          secondNormal j w*(sourceZero j+sourceOne j*w))) := by
        dsimp only [sourceZero, sourceOne]
        field_simp
        ring
  rw [hnum, CubicTraceDescent.linearDensity]
  field_simp

/-- The explicit paired current of a closed one-form has the calculated
linear source. Only the two moving-point jet chain rules are inputs;
its divergence and its source reconstruction are conclusions. -/
theorem current_density
    (T R S : Derivation ℤ K K) (t w U V : K) (j : Jet K)
    (hTR : ∀ x, T (R x) = R (T x))
    (hTS : ∀ x, T (S x) = S (T x))
    (hTt : T t = 1) (hRt : R t = 0) (hSt : S t = 0)
    (hTa : T j.alpha = 0) (hTU : T U = 0) (hTV : T V = 0)
    (hclosed : R V = S U)
    (hdelta : j.delta = CubicSelectorCurrent.movingDenominator t j.alpha)
    (hl : j.l ≠ 0) (hd : j.delta ≠ 0) (hg : normal j w ≠ 0)
    (hf : equation j w = 0)
    (hselector : movingOperator T R S t j.alpha U V (selector j w) =
      j.alpha*(j.aDot*w+2*j.gDot-j.a*j.betaDot)/3-
        j.a*motion j w/(3*normal j w))
    (hnormal : movingOperator T R S t j.alpha U V (normal j w) =
      normalMotion j w-secondNormal j w*motion j w/normal j w) :
    T (CubicSelectorCurrent.currentT R S t j.alpha U V (selector j w/normal j w))+
      R (CubicSelectorCurrent.currentR t j.alpha V (selector j w/normal j w))+
      S (CubicSelectorCurrent.currentS t j.alpha U (selector j w/normal j w)) =
        CubicTraceDescent.linearDensity (normal j w) (secondNormal j w) w
          (sourceZero j) (sourceOne j) := by
  have hd' : CubicSelectorCurrent.movingDenominator t j.alpha ≠ 0 := by
    rwa [← hdelta]
  rw [CubicSelectorCurrent.current_divergence_of_commute T R S t j.alpha U V
    (selector j w/normal j w) hTR hTS hTt hRt hSt hTa hTU hTV hclosed hd', ← hdelta]
  have hcombined :
      (-2*t*CubicSelectorCurrent.movingVelocity R S j.alpha U V*
          T (selector j w/normal j w)+
        2*j.alpha*(V*R (selector j w/normal j w)-U*S (selector j w/normal j w)))/j.delta =
      -2*movingOperator T R S t j.alpha U V (selector j w/normal j w)/j.delta := by
    simp only [movingOperator, Derivation.add_apply, Derivation.sub_apply,
      Derivation.smul_apply, smul_eq_mul]
    ring
  rw [hcombined]
  calc
    _ = 2*numeratorThree j w/(3*j.delta*(normal j w)^3) := by
      rw [Derivation.leibniz_div, hselector, hnormal]
      simp only [smul_eq_mul]
      dsimp only [selector, numeratorThree]
      generalize normal j w = g at hg ⊢
      field_simp [hd, hg]
      ring
    _ = _ := selector_density j w hl hd hg hf

end FieldIdentities

section FiberDegrees

open Polynomial

variable {K : Type*} [Field K]

/-- Regard the six divided-difference coefficients as polynomials in
`x=t^2`, while all moving-point data belong to the coefficient field. -/
def fiberJet (j : Jet K) (h k : Fin 3 → Polynomial K) : Jet (Polynomial K) where
  l := C j.l
  a := C j.a
  g := C j.g
  alpha := C j.alpha
  aDot := C j.aDot
  gDot := C j.gDot
  betaDot := C j.betaDot
  delta := X-C (j.alpha^2)
  h0 := h 0
  h1 := h 1
  h2 := h 2
  k0 := k 0
  k1 := k 1
  k2 := k 2

def sourceZeroPolynomial (j : Jet K) (h k : Fin 3 → Polynomial K) : Polynomial K :=
  C (1/(18*j.l^2))*sourceZeroNumerator (fiberJet j h k)

def sourceOnePolynomial (j : Jet K) (h k : Fin 3 → Polynomial K) : Polynomial K :=
  C (1/(9*j.l^2))*sourceOneNumerator (fiberJet j h k)

theorem sourceZeroPolynomial_eval (j : Jet K) (h k : Fin 3 → Polynomial K) (x : K) :
    (sourceZeroPolynomial j h k).eval x =
      sourceZero ((fiberJet j h k).map (evalRingHom x)) := by
  rw [sourceZero, sourceZeroNumerator_map]
  simp [sourceZeroPolynomial, Jet.map, fiberJet, div_eq_mul_inv, mul_comm]

theorem sourceOnePolynomial_eval (j : Jet K) (h k : Fin 3 → Polynomial K) (x : K) :
    (sourceOnePolynomial j h k).eval x =
      sourceOne ((fiberJet j h k).map (evalRingHom x)) := by
  rw [sourceOne, sourceOneNumerator_map]
  simp [sourceOnePolynomial, Jet.map, fiberJet, div_eq_mul_inv, mul_comm]

/-- The bound is uniform in the moving-point extension and all parameter
poles of its coefficients. It bounds only the `x=t^2` degree. -/
theorem sourceZeroPolynomial_degree (j : Jet K) (h k : Fin 3 → Polynomial K)
    (hh0 : (h 0).natDegree ≤ 2) (hh1 : (h 1).natDegree ≤ 1)
    (hh2 : (h 2).natDegree ≤ 0) (hk0 : (k 0).natDegree ≤ 2)
    (hk1 : (k 1).natDegree ≤ 1) (hk2 : (k 2).natDegree ≤ 0) :
    (sourceZeroPolynomial j h k).natDegree ≤ 3 := by
  simp only [sourceZeroPolynomial, sourceZeroNumerator, cubicB, cubicC,
    cubicD, quotientLinear, quotientConstantNumerator, remainderOneThree,
    fiberJet]
  compute_degree!
  all_goals omega

theorem sourceOnePolynomial_degree (j : Jet K) (h k : Fin 3 → Polynomial K)
    (hh0 : (h 0).natDegree ≤ 2) (hh1 : (h 1).natDegree ≤ 1)
    (hh2 : (h 2).natDegree ≤ 0) (hk0 : (k 0).natDegree ≤ 2)
    (hk1 : (k 1).natDegree ≤ 1) (hk2 : (k 2).natDegree ≤ 0) :
    (sourceOnePolynomial j h k).natDegree ≤ 2 := by
  simp only [sourceOnePolynomial, sourceOneNumerator, cubicB, cubicC,
    quotientLinear, quotientConstantNumerator, remainderTwoThree, fiberJet]
  compute_degree!
  all_goals omega

end FiberDegrees

end CubicSelectorSource

#print axioms CubicSelectorSource.cleared_source_identity
#print axioms CubicSelectorSource.linearDensity_shift
#print axioms CubicSelectorSource.selector_density
#print axioms CubicSelectorSource.current_density
#print axioms CubicSelectorSource.sourceZeroPolynomial_eval
#print axioms CubicSelectorSource.sourceOnePolynomial_eval
#print axioms CubicSelectorSource.sourceZeroPolynomial_degree
#print axioms CubicSelectorSource.sourceOnePolynomial_degree
