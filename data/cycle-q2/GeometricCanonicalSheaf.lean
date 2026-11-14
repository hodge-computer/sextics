import Proposal.GeometricCurveCoordinates
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Proposal.GeometricSeedCurveGradientArithmetic
import Proposal.GeometricSparseJacobianCover
import Proposal.GeometricCanonicalOverlap
import Proposal.GeometricProjectiveOverlap
import Proposal.GeometricProjectiveFrames
import Proposal.GeometricTwistedDifferential
import Proposal.GeometricProjectiveAffineCoefficients
import Proposal.GeometricTwistedModule
import Proposal.GeometricProjectiveCanonicalH1
import Proposal.GeometricIncidenceCechTrace

section SourceGeometricCompatibleSmoothSeed

/-!
# A simultaneous nonsingular member of the factorized seed family

The cubic b = x0^3 + x2^3 gives one explicit member for which the weighted
threefold, its cubic surface section, and the complete-intersection curve
all satisfy their field-valued Jacobian criteria. The same genuine parameter
r^3 = 2 is used throughout. The defining quartics are the existing cofactors.

These statements concern the actual polynomial equations over every
characteristic-zero field extension. They supply a simultaneous smooth-member
witness, not an intersection with the trace-rank open or a moving-cycle theorem.
The factorized-family and geometric strategy are due to Benjamin E. Diamond;
this elementary member and formalization were prepared for fqlx with ChatGPT.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2CompatibleSmoothSeed

open MvPolynomial CycleQ2SeedTrace

def firstEquation (r : ℂ) : WeightedPoly := X 0 ^ 2 - C r * X 1 * X 3
def secondEquation : WeightedPoly := X 4 + X 2 ^ 2
def cubic : WeightedPoly := X 0 ^ 3 + X 2 ^ 3
def axisCubic : WeightedPoly := X 1 ^ 3 + X 3 ^ 3
def sectionEquation : WeightedPoly := cubic - C Complex.I * axisCubic
def companionEquation : WeightedPoly := cubic + C Complex.I * axisCubic
def residualEquation (r : ℂ) : WeightedPoly :=
  firstEquation r * originalG1 r + secondEquation * originalG2
def threefoldEquation (r : ℂ) : WeightedPoly :=
  residualEquation r + sectionEquation * companionEquation

theorem residualEquation_expanded (r : ℂ) :
    residualEquation r = X 0 ^ 6 + X 2 ^ 6 + X 4 ^ 3 -
      C (r ^ 3) * X 1 ^ 3 * X 3 ^ 3 := by
  simp only [residualEquation, firstEquation, secondEquation, originalG1,
    originalG2, map_pow]
  ring

theorem threefoldEquation_expanded (r : ℂ) (hr : r ^ 3 = 2) :
    threefoldEquation r = 2 * X 0 ^ 6 + X 1 ^ 6 + 2 * X 2 ^ 6 +
      X 3 ^ 6 + X 4 ^ 3 + 2 * X 0 ^ 3 * X 2 ^ 3 := by
  have hi : (C Complex.I : WeightedPoly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  rw [threefoldEquation, residualEquation_expanded, hr]
  simp only [sectionEquation, companionEquation, cubic, axisCubic, map_ofNat]
  linear_combination -(X 1 ^ 3 + X 3 ^ 3)^2 * hi

section Arithmetic

variable {K : Type*} [Field K] [CharZero K]

def surfaceValue (i : K) (x : Fin 5 → K) : K :=
  x 0 ^ 3 + x 2 ^ 3 - i * (x 1 ^ 3 + x 3 ^ 3)

def residualValue (x : Fin 5 → K) : K :=
  x 0 ^ 6 + x 2 ^ 6 + x 4 ^ 3 - 2 * x 1 ^ 3 * x 3 ^ 3

def threefoldGradient (x : Fin 5 → K) : Fin 5 → K :=
  ![6 * x 0 ^ 2 * (2 * x 0 ^ 3 + x 2 ^ 3), 6 * x 1 ^ 5,
    6 * x 2 ^ 2 * (2 * x 2 ^ 3 + x 0 ^ 3), 6 * x 3 ^ 5, 3 * x 4 ^ 2]

def residualGradient (x : Fin 5 → K) : Fin 5 → K :=
  ![6 * x 0 ^ 5, -6 * x 1 ^ 2 * x 3 ^ 3,
    6 * x 2 ^ 5, -6 * x 1 ^ 3 * x 3 ^ 2, 3 * x 4 ^ 2]

def sectionGradient (i : K) (x : Fin 5 → K) : Fin 5 → K :=
  ![3 * x 0 ^ 2, -3 * i * x 1 ^ 2, 3 * x 2 ^ 2, -3 * i * x 3 ^ 2, 0]

def firstGradient (r : K) (x : Fin 5 → K) : Fin 5 → K :=
  ![2 * x 0, -r * x 3, 0, -r * x 1, 0]

def secondGradient (x : Fin 5 → K) : Fin 5 → K := ![0, 0, 2 * x 2, 0, 1]

private theorem i_ne_zero (i : K) (hi : i ^ 2 = -1) : i ≠ 0 := by
  intro h
  rw [h] at hi
  norm_num at hi

omit [CharZero K] in
private theorem active_cubes (u t : K) (h : u ^ 2 * (2 * u ^ 3 - t) = 0) :
    u ^ 3 = 0 ∨ 2 * u ^ 3 = t := by
  rcases mul_eq_zero.mp h with hz | hz
  · exact Or.inl (by rw [eq_zero_of_pow_eq_zero hz]; norm_num)
  · exact Or.inr (sub_eq_zero.mp hz)

private theorem two_branches_zero (a b t : K)
    (ha : a = 0 ∨ 2 * a = t) (hb : b = 0 ∨ 2 * b = t)
    (hab : a + b = 0) : a = 0 ∧ b = 0 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact ⟨ha, hb⟩
  · exact ⟨ha, by linear_combination hab - ha⟩
  · exact ⟨by linear_combination hab - hb, hb⟩
  · constructor
    · linear_combination (1 / 2 : K) * hab + (1 / 4 : K) * ha - (1 / 4 : K) * hb
    · linear_combination (1 / 2 : K) * hab - (1 / 4 : K) * ha + (1 / 4 : K) * hb

private theorem two_branches_shift (a b t : K)
    (ha : a = 0 ∨ 2 * a = t) (hb : b = 0 ∨ 2 * b = t)
    (hab : a + b + t = 0) : t = 0 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · linear_combination hab - ha - hb
  · linear_combination (2 / 3 : K) * hab - (2 / 3 : K) * ha - (1 / 3 : K) * hb
  · linear_combination (2 / 3 : K) * hab - (1 / 3 : K) * ha - (2 / 3 : K) * hb
  · linear_combination (1 / 2 : K) * hab - (1 / 4 : K) * ha - (1 / 4 : K) * hb

theorem threefoldGradient_common_zero (x : Fin 5 → K)
    (hx : ∀ j, threefoldGradient x j = 0) : x = 0 := by
  have h0 : x 0 ^ 2 * (2 * x 0 ^ 3 + x 2 ^ 3) = 0 := by
    have h := hx 0
    change 6 * x 0 ^ 2 * (2 * x 0 ^ 3 + x 2 ^ 3) = 0 at h
    linear_combination (1 / 6 : K) * h
  have h2 : x 2 ^ 2 * (2 * x 2 ^ 3 + x 0 ^ 3) = 0 := by
    have h := hx 2
    change 6 * x 2 ^ 2 * (2 * x 2 ^ 3 + x 0 ^ 3) = 0 at h
    linear_combination (1 / 6 : K) * h
  have h02 : x 0 = 0 ∧ x 2 = 0 := by
    rcases mul_eq_zero.mp h0 with h0 | h0
    · have hz := eq_zero_of_pow_eq_zero h0
      refine ⟨hz, ?_⟩
      rw [hz] at h2
      have hp : x 2 ^ 5 = 0 := by linear_combination (1 / 2 : K) * h2
      exact eq_zero_of_pow_eq_zero hp
    · rcases mul_eq_zero.mp h2 with h2 | h2
      · have hz := eq_zero_of_pow_eq_zero h2
        refine ⟨?_, hz⟩
        rw [hz] at h0
        have hp : x 0 ^ 3 = 0 := by linear_combination (1 / 2 : K) * h0
        exact eq_zero_of_pow_eq_zero hp
      · have hp0 : x 0 ^ 3 = 0 := by
          linear_combination (2 / 3 : K) * h0 - (1 / 3 : K) * h2
        have hp2 : x 2 ^ 3 = 0 := by
          linear_combination (2 / 3 : K) * h2 - (1 / 3 : K) * h0
        exact ⟨eq_zero_of_pow_eq_zero hp0, eq_zero_of_pow_eq_zero hp2⟩
  ext j
  fin_cases j
  · exact h02.1
  · have h := hx 1
    simpa [threefoldGradient] using h
  · exact h02.2
  · have h := hx 3
    simpa [threefoldGradient] using h
  · have h := hx 4
    simpa [threefoldGradient] using h

/-- The residual and cubic gradient cannot be proportional at a nonzero
point of the cubic section. The residual equation itself is not needed. -/
theorem residual_proportional_section (i : K) (hi : i ^ 2 = -1)
    (x : Fin 5 → K) (hh : surfaceValue i x = 0) (t : K)
    (ht : ∀ j, residualGradient x j = t * sectionGradient i x j) : x = 0 := by
  have hi0 := i_ne_zero i hi
  have h0 : x 0 ^ 2 * (2 * x 0 ^ 3 - t) = 0 := by
    have h := ht 0
    simp only [residualGradient, sectionGradient, Matrix.cons_val_zero] at h
    linear_combination (1 / 3 : K) * h
  have h2 : x 2 ^ 2 * (2 * x 2 ^ 3 - t) = 0 := by
    have h := ht 2
    change 6 * x 2 ^ 5 = t * (3 * x 2 ^ 2) at h
    linear_combination (1 / 3 : K) * h
  have h1 : x 1 ^ 2 * (2 * x 3 ^ 3 - i * t) = 0 := by
    have h := ht 1
    change -6 * x 1 ^ 2 * x 3 ^ 3 = t * (-3 * i * x 1 ^ 2) at h
    linear_combination (-1 / 3 : K) * h
  have h3 : x 3 ^ 2 * (2 * x 1 ^ 3 - i * t) = 0 := by
    have h := ht 3
    change -6 * x 1 ^ 3 * x 3 ^ 2 = t * (-3 * i * x 3 ^ 2) at h
    linear_combination (-1 / 3 : K) * h
  have h4 : x 4 = 0 := by
    have h := ht 4
    simpa [residualGradient, sectionGradient] using h
  change x 0 ^ 3 + x 2 ^ 3 - i * (x 1 ^ 3 + x 3 ^ 3) = 0 at hh
  have ha := active_cubes (x 0) t h0
  have hb := active_cubes (x 2) t h2
  have allzero_of_t (hz : t = 0) : x = 0 := by
    have hz0 : x 0 = 0 := by
      rcases ha with hp | hp
      · exact eq_zero_of_pow_eq_zero hp
      · have hp' : x 0 ^ 3 = 0 := by linear_combination (1 / 2 : K) * hp + (1 / 2 : K) * hz
        exact eq_zero_of_pow_eq_zero hp'
    have hz2 : x 2 = 0 := by
      rcases hb with hp | hp
      · exact eq_zero_of_pow_eq_zero hp
      · have hp' : x 2 ^ 3 = 0 := by linear_combination (1 / 2 : K) * hp + (1 / 2 : K) * hz
        exact eq_zero_of_pow_eq_zero hp'
    have h13 : x 1 = 0 ∧ x 3 = 0 := by
      by_cases hz1 : x 1 = 0
      · refine ⟨hz1, ?_⟩
        rw [hz0, hz1, hz2] at hh
        have hp : x 3 ^ 3 = 0 := by
          simpa using (mul_eq_zero.mp (by simpa using hh : i * x 3 ^ 3 = 0)).resolve_left hi0
        exact eq_zero_of_pow_eq_zero hp
      · have hp3 : x 3 ^ 3 = 0 := by
          have hs := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 hz1)
          rw [hz] at hs
          linear_combination (1 / 2 : K) * hs
        have hz3 := eq_zero_of_pow_eq_zero hp3
        refine ⟨?_, hz3⟩
        rw [hz0, hz2, hz3] at hh
        have hp : x 1 ^ 3 = 0 :=
          (mul_eq_zero.mp (by simpa using hh : i * x 1 ^ 3 = 0)).resolve_left hi0
        exact eq_zero_of_pow_eq_zero hp
    ext j
    fin_cases j <;> simp [hz0, hz2, h13.1, h13.2, h4]
  by_cases hx1 : x 1 = 0
  · by_cases hx3 : x 3 = 0
    · have hs : x 0 ^ 3 + x 2 ^ 3 = 0 := by simpa [hx1, hx3] using hh
      obtain ⟨hz0, hz2⟩ := two_branches_zero _ _ _ ha hb hs
      have hx0 := eq_zero_of_pow_eq_zero hz0
      have hx2 := eq_zero_of_pow_eq_zero hz2
      ext j
      fin_cases j <;> simp [hx0, hx1, hx2, hx3, h4]
    · apply allzero_of_t
      have hs := (mul_eq_zero.mp h3).resolve_left (pow_ne_zero 2 hx3)
      rw [hx1] at hs
      exact (mul_eq_zero.mp (by simpa using hs : i * t = 0)).resolve_left hi0
  · by_cases hx3 : x 3 = 0
    · apply allzero_of_t
      have hs := (mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 hx1)
      rw [hx3] at hs
      exact (mul_eq_zero.mp (by simpa using hs : i * t = 0)).resolve_left hi0
    · have he1 : 2 * x 3 ^ 3 = i * t :=
        sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left (pow_ne_zero 2 hx1))
      have he3 : 2 * x 1 ^ 3 = i * t :=
        sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left (pow_ne_zero 2 hx3))
      have hs : x 0 ^ 3 + x 2 ^ 3 + t = 0 := by
        linear_combination hh + (i / 2) * he1 + (i / 2) * he3 + t * hi
      exact allzero_of_t (two_branches_shift _ _ _ ha hb hs)

theorem sectionGradient_common_zero (i : K) (hi : i ^ 2 = -1)
    (x : Fin 5 → K) (hg : residualValue x = 0)
    (hx : ∀ j, sectionGradient i x j = 0) : x = 0 := by
  have hi0 := i_ne_zero i hi
  have h0 : x 0 = 0 := by simpa [sectionGradient] using hx 0
  have h1 : x 1 = 0 := by simpa [sectionGradient, hi0] using hx 1
  have h2 : x 2 = 0 := by simpa [sectionGradient] using hx 2
  have h3 : x 3 = 0 := by simpa [sectionGradient, hi0] using hx 3
  have h4 : x 4 = 0 := by simpa [residualValue, h0, h1, h2, h3] using hg
  ext j
  fin_cases j <;> simp [h0, h1, h2, h3, h4]

/-- Full row rank of the literal two-equation surface Jacobian. -/
theorem surface_gradient_independent (i : K) (hi : i ^ 2 = -1)
    (x : Fin 5 → K) (hx : x ≠ 0) (hg : residualValue x = 0)
    (hh : surfaceValue i x = 0) (a b : K)
    (hab : ∀ j, a * residualGradient x j + b * sectionGradient i x j = 0) :
    a = 0 ∧ b = 0 := by
  by_cases ha : a = 0
  · refine ⟨ha, ?_⟩
    by_contra hb
    apply hx
    apply sectionGradient_common_zero i hi x hg
    intro j
    have h := hab j
    rw [ha, zero_mul, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left hb
  · exfalso
    apply hx
    apply residual_proportional_section i hi x hh (-b / a)
    intro j
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff ha).mpr
    have h := hab j
    linear_combination h

theorem section_proportional_first (i r : K) (hi : i ^ 2 = -1) (hr : r ^ 3 = 2)
    (x : Fin 5 → K) (hq : x 0 ^ 2 - r * x 1 * x 3 = 0)
    (hw : x 4 + x 2 ^ 2 = 0) (t : K)
    (ht : ∀ j, sectionGradient i x j = t * firstGradient r x j) : x = 0 := by
  have hi0 := i_ne_zero i hi
  have hr0 : r ≠ 0 := by
    intro hz
    rw [hz] at hr
    norm_num at hr
  have hx2 : x 2 = 0 := by simpa [sectionGradient, firstGradient] using ht 2
  have hx4 : x 4 = 0 := by simpa [hx2] using hw
  have he0 : x 0 * (3 * x 0 - 2 * t) = 0 := by
    have h := ht 0
    change 3 * x 0 ^ 2 = t * (2 * x 0) at h
    linear_combination h
  have he1 : 3 * i * x 1 ^ 2 = t * r * x 3 := by
    have h := ht 1
    change -3 * i * x 1 ^ 2 = t * (-r * x 3) at h
    linear_combination -h
  have he3 : 3 * i * x 3 ^ 2 = t * r * x 1 := by
    have h := ht 3
    change -3 * i * x 3 ^ 2 = t * (-r * x 1) at h
    linear_combination -h
  have hx0 : x 0 = 0 := by
    by_contra hx0
    have het : 3 * x 0 = 2 * t :=
      sub_eq_zero.mp ((mul_eq_zero.mp he0).resolve_left hx0)
    have h13 : x 1 * x 3 ≠ 0 := by
      intro hz
      have hp : x 0 ^ 2 = 0 := by
        linear_combination hq + r * hz
      exact hx0 (eq_zero_of_pow_eq_zero hp)
    have hp := congrArg₂ (fun u v : K => u * v) he1 he3
    have hz : (54 : K) * (x 1 * x 3) ^ 2 = 0 := by
      linear_combination -4 * hp + 36 * (x 1 * x 3) ^ 2 * hi +
        r ^ 2 * x 1 * x 3 * (3 * x 0 + 2 * t) * het -
        9 * r ^ 2 * x 1 * x 3 * hq - 9 * (x 1 * x 3) ^ 2 * hr
    exact (mul_ne_zero (by norm_num : (54 : K) ≠ 0) (pow_ne_zero 2 h13)) hz
  have h13 : x 1 * x 3 = 0 := by
    have hz : r * (x 1 * x 3) = 0 := by
      rw [hx0] at hq
      linear_combination -hq
    exact (mul_eq_zero.mp hz).resolve_left hr0
  have hx13 : x 1 = 0 ∧ x 3 = 0 := by
    rcases mul_eq_zero.mp h13 with hz1 | hz3
    · refine ⟨hz1, ?_⟩
      rw [hz1, mul_zero] at he3
      simpa [hi0] using he3
    · refine ⟨?_, hz3⟩
      rw [hz3, mul_zero] at he1
      simpa [hi0] using he1
  ext j
  fin_cases j <;> simp [hx0, hx13.1, hx2, hx13.2, hx4]

/-- Full row rank of the three actual curve equations. This is independent
of a projective Jacobian-criterion implementation. -/
theorem curve_gradient_independent (i r : K) (hi : i ^ 2 = -1) (hr : r ^ 3 = 2)
    (x : Fin 5 → K) (hx : x ≠ 0) (hq : x 0 ^ 2 - r * x 1 * x 3 = 0)
    (hw : x 4 + x 2 ^ 2 = 0) (hh : surfaceValue i x = 0) (a b c : K)
    (habc : ∀ j, a * firstGradient r x j + b * secondGradient x j +
      c * sectionGradient i x j = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hb : b = 0 := by simpa [firstGradient, secondGradient, sectionGradient] using habc 4
  by_cases hc : c = 0
  · refine ⟨?_, hb, hc⟩
    by_contra ha
    have hz (j : Fin 5) : firstGradient r x j = 0 := by
      have h := habc j
      rw [hb, hc, zero_mul, zero_mul, add_zero, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left ha
    have hr0 : r ≠ 0 := by
      intro h
      rw [h] at hr
      norm_num at hr
    have hx0 : x 0 = 0 := by simpa [firstGradient] using hz 0
    have hx1 : x 1 = 0 := by simpa [firstGradient, hr0] using hz 3
    have hx3 : x 3 = 0 := by simpa [firstGradient, hr0] using hz 1
    have hx2 : x 2 = 0 := by simpa [surfaceValue, hx0, hx1, hx3] using hh
    have hx4 : x 4 = 0 := by simpa [hx2] using hw
    apply hx
    ext j
    fin_cases j <;> simp [hx0, hx1, hx2, hx3, hx4]
  · exfalso
    apply hx
    apply section_proportional_first i r hi hr x hq hw (-a / c)
    intro j
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hc).mpr
    have h := habc j
    rw [hb, zero_mul, add_zero] at h
    linear_combination h

end Arithmetic

section PolynomialBinding

variable {K : Type*} [Field K] [CharZero K] [Algebra ℂ K]

private theorem complex_i (K : Type*) [Field K] [Algebra ℂ K] :
    (algebraMap ℂ K Complex.I) ^ 2 = -1 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]

omit [CharZero K] in
theorem eval_residualEquation (r : ℂ) (hr : r ^ 3 = 2) (x : Fin 5 → K) :
    aeval x (residualEquation r) = residualValue x := by
  norm_num [residualEquation_expanded, hr, residualValue, map_ofNat]

omit [CharZero K] in
theorem eval_sectionEquation (x : Fin 5 → K) :
    aeval x sectionEquation = surfaceValue (algebraMap ℂ K Complex.I) x := by
  simp [sectionEquation, cubic, axisCubic, surfaceValue]

private theorem pderiv_two (j : Fin 5) : pderiv j (2 : WeightedPoly) = 0 := by
  simpa only [map_ofNat] using (pderiv_C (i := j) (a := (2 : ℂ)))

theorem eval_threefold_pderiv (r : ℂ) (hr : r ^ 3 = 2)
    (x : Fin 5 → K) (j : Fin 5) :
    aeval x (pderiv j (threefoldEquation r)) = threefoldGradient x j := by
  rw [threefoldEquation_expanded r hr]
  fin_cases j <;>
    norm_num [threefoldGradient, Derivation.leibniz, pderiv_pow, pderiv_C, pderiv_two, map_ofNat, map_natCast, Derivation.map_natCast,
      Pi.single_apply, Fin.ext_iff] <;> ring

theorem eval_residual_pderiv (r : ℂ) (hr : r ^ 3 = 2)
    (x : Fin 5 → K) (j : Fin 5) :
    aeval x (pderiv j (residualEquation r)) = residualGradient x j := by
  rw [residualEquation_expanded r, hr]
  fin_cases j <;>
    norm_num [residualGradient, Derivation.leibniz, pderiv_pow, pderiv_C, pderiv_two, map_ofNat, map_natCast, Derivation.map_natCast,
      Pi.single_apply, Fin.ext_iff] <;> ring

theorem eval_section_pderiv (x : Fin 5 → K) (j : Fin 5) :
    aeval x (pderiv j sectionEquation) =
      sectionGradient (algebraMap ℂ K Complex.I) x j := by
  fin_cases j <;>
    norm_num [sectionEquation, cubic, axisCubic, sectionGradient,
      Derivation.leibniz, pderiv_pow, pderiv_C, pderiv_two, map_ofNat, map_natCast, Derivation.map_natCast,
      Pi.single_apply, Fin.ext_iff] <;> ring

theorem eval_first_pderiv (r : ℂ) (x : Fin 5 → K) (j : Fin 5) :
    aeval x (pderiv j (firstEquation r)) =
      firstGradient (algebraMap ℂ K r) x j := by
  fin_cases j <;>
    norm_num [firstEquation, firstGradient, Derivation.leibniz, pderiv_pow, pderiv_C, pderiv_two, map_ofNat, map_natCast, Derivation.map_natCast,
      Pi.single_apply, Fin.ext_iff] <;> ring

theorem eval_second_pderiv (x : Fin 5 → K) (j : Fin 5) :
    aeval x (pderiv j secondEquation) = secondGradient x j := by
  fin_cases j <;>
    norm_num [secondEquation, secondGradient, Derivation.leibniz, pderiv_pow, pderiv_C, pderiv_two, map_ofNat, map_natCast, Derivation.map_natCast,
      Pi.single_apply, Fin.ext_iff] <;> ring

/-- No nonzero projective point over any complex extension is singular
for the literal weighted sextic at this member. -/
theorem actual_threefold_gradient_nonzero (r : ℂ) (hr : r ^ 3 = 2)
    (x : Fin 5 → K) (hx : x ≠ 0) :
    ∃ j, aeval x (pderiv j (threefoldEquation r)) ≠ 0 := by
  by_contra! h
  apply hx
  apply threefoldGradient_common_zero x
  intro j
  simpa only [eval_threefold_pderiv r hr] using h j

/-- Full rank for the actual surface pair (F,h). The product-rule
correction changes the h coefficient by a*k, and is retained explicitly. -/
theorem actual_surface_gradient_independent (r : ℂ) (hr : r ^ 3 = 2)
    (x : Fin 5 → K) (hx : x ≠ 0)
    (hF : aeval x (threefoldEquation r) = 0)
    (hh : aeval x sectionEquation = 0) (a b : K)
    (hab : ∀ j, a * aeval x (pderiv j (threefoldEquation r)) +
      b * aeval x (pderiv j sectionEquation) = 0) : a = 0 ∧ b = 0 := by
  have hg : residualValue x = 0 := by
    simpa only [threefoldEquation, map_add, map_mul, hh, zero_mul, add_zero,
      eval_residualEquation r hr] using hF
  have hhh : surfaceValue (algebraMap ℂ K Complex.I) x = 0 := by
    simpa only [eval_sectionEquation] using hh
  have hrel (j : Fin 5) : a * residualGradient x j +
      (a * aeval x companionEquation + b) *
        sectionGradient (algebraMap ℂ K Complex.I) x j = 0 := by
    have h := hab j
    simp only [threefoldEquation, map_add, Derivation.leibniz, smul_eq_mul,
      map_mul, hh, mul_zero, zero_add, eval_residual_pderiv r hr,
      eval_section_pderiv] at h
    linear_combination h
  obtain ⟨ha, hb⟩ := surface_gradient_independent _ (complex_i K) x hx hg hhh
    a (a * aeval x companionEquation + b) hrel
  exact ⟨ha, by simpa [ha] using hb⟩

/-- Full rank for the literal curve pair and section, including the
eliminated weight-two coordinate. -/
theorem actual_curve_gradient_independent (r : ℂ) (hr : r ^ 3 = 2)
    (x : Fin 5 → K) (hx : x ≠ 0)
    (hq : aeval x (firstEquation r) = 0)
    (hw : aeval x secondEquation = 0)
    (hh : aeval x sectionEquation = 0) (a b c : K)
    (habc : ∀ j, a * aeval x (pderiv j (firstEquation r)) +
      b * aeval x (pderiv j secondEquation) +
      c * aeval x (pderiv j sectionEquation) = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hrK : (algebraMap ℂ K r) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  apply curve_gradient_independent (algebraMap ℂ K Complex.I) (algebraMap ℂ K r)
    (complex_i K) hrK x hx
  · simpa [firstEquation] using hq
  · simpa [secondEquation] using hw
  · simpa only [eval_sectionEquation] using hh
  · intro j
    simpa only [eval_first_pderiv, eval_second_pderiv, eval_section_pderiv] using habc j

end PolynomialBinding

#print axioms actual_threefold_gradient_nonzero
#print axioms actual_surface_gradient_independent
#print axioms actual_curve_gradient_independent

end CycleQ2CompatibleSmoothSeed
end

end SourceGeometricCompatibleSmoothSeed

section SourceGeometricIncidenceJacobianCover

/-!
# The Jacobian cover at the literal incidence parameter

The existing homogeneous integral certificates specialize at `x1 = 1` and
`x2 = 1`. Euler's identities express the deleted-column minors in terms of
the three actual affine cofactors and the two equations. Thus the actual
Jacobian ideals in the two chart quotients are the unit ideal at `(57, 1)`.

This uses the same `firstEquations`, `secondEquations`, `chartMinor`, and
`jacobianIdeal` as the affine differential and canonical-frame construction.
It supplies nonsingularity at the literal incidence parameter, without
assuming that the distinct sparse parameter has the same geometric fiber.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricIncidenceJacobianCover

open MvPolynomial CycleQ2GeometricAffineCurveCharts
  CycleQ2GeometricAdjunctionOverlap CycleQ2GeometricAffineOverlap
  CycleQ2GeometricResidueFrames CycleQ2GeometricSparseJacobianCover
open scoped BigOperators

section Algebra
variable {R : Type*} [CommRing R]

private theorem first_generator_formula (i a b c : R) :
    let q := quadricOne 57 a b c
    let h := cubicOne i 1 a b c
    let u := gradQuadricOne 57 a
    let v := gradCubicOne i 1 a b c
    let m := jacobianMinors u v
    CycleQ2SeedCurveGradientArithmetic.generators i a 1 b c =
      ![q, h,
        3 * h * u 0 - 2 * q * v 0 - b * m 2 + c * m 1,
        m 2,
        -m 1,
        2 * q * v 1 - 3 * h * u 1 - a * m 2 + c * m 0,
        2 * q * v 2 - 3 * h * u 2 + a * m 1 - b * m 0,
        m 0] := by
  dsimp only
  funext k
  fin_cases k <;>
    simp [CycleQ2SeedCurveGradientArithmetic.generators, quadricOne, cubicOne,
      gradQuadricOne, gradCubicOne, jacobianMinors] <;> ring

private theorem second_generator_formula (i a b c : R) :
    let q := quadricTwo 57 a b c
    let h := cubicTwo i 1 a b c
    let u := gradQuadricTwo 57 a b c
    let v := gradCubicTwo i 1 a b c
    let m := jacobianMinors u v
    CycleQ2SeedCurveGradientArithmetic.generators i a b 1 c =
      ![q, h,
        m 2,
        3 * h * u 0 - 2 * q * v 0 - b * m 2 + c * m 1,
        -m 1,
        3 * h * u 1 - 2 * q * v 1 + a * m 2 - c * m 0,
        m 0,
        2 * q * v 2 - 3 * h * u 2 + a * m 1 - b * m 0] := by
  dsimp only
  funext k
  fin_cases k <;>
    simp [CycleQ2SeedCurveGradientArithmetic.generators, quadricTwo, cubicTwo,
      gradQuadricTwo, gradCubicTwo, jacobianMinors] <;> ring

private theorem first_generators_mem (J : Ideal R) (i a b c : R)
    (hq : quadricOne 57 a b c = 0) (hh : cubicOne i 1 a b c = 0)
    (hm : ∀ j,
      jacobianMinors (gradQuadricOne 57 a) (gradCubicOne i 1 a b c) j ∈ J)
    (k : Fin 8) : CycleQ2SeedCurveGradientArithmetic.generators i a 1 b c k ∈ J := by
  have hform := congrFun (first_generator_formula i a b c) k
  simp only [hq, hh, mul_zero, zero_mul, zero_sub, sub_zero, zero_add] at hform
  rw [hform]
  fin_cases k
  · exact J.zero_mem
  · exact J.zero_mem
  · exact J.add_mem (J.neg_mem (J.mul_mem_left b (hm 2))) (J.mul_mem_left c (hm 1))
  · exact hm 2
  · exact J.neg_mem (hm 1)
  · exact J.add_mem (J.neg_mem (J.mul_mem_left a (hm 2))) (J.mul_mem_left c (hm 0))
  · exact J.sub_mem (J.mul_mem_left a (hm 1)) (J.mul_mem_left b (hm 0))
  · exact hm 0

private theorem second_generators_mem (J : Ideal R) (i a b c : R)
    (hq : quadricTwo 57 a b c = 0) (hh : cubicTwo i 1 a b c = 0)
    (hm : ∀ j,
      jacobianMinors (gradQuadricTwo 57 a b c) (gradCubicTwo i 1 a b c) j ∈ J)
    (k : Fin 8) : CycleQ2SeedCurveGradientArithmetic.generators i a b 1 c k ∈ J := by
  have hform := congrFun (second_generator_formula i a b c) k
  simp only [hq, hh, mul_zero, zero_mul, zero_sub, sub_zero, zero_add] at hform
  rw [hform]
  fin_cases k
  · exact J.zero_mem
  · exact J.zero_mem
  · exact hm 2
  · exact J.add_mem (J.neg_mem (J.mul_mem_left b (hm 2))) (J.mul_mem_left c (hm 1))
  · exact J.neg_mem (hm 1)
  · exact J.sub_mem (J.mul_mem_left a (hm 2)) (J.mul_mem_left c (hm 0))
  · exact hm 0
  · exact J.sub_mem (J.mul_mem_left a (hm 1)) (J.mul_mem_left b (hm 0))

private theorem first_minors_unit_ideal (φ : ℂ →+* R) (a b c : R) (J : Ideal R)
    (hq : quadricOne 57 a b c = 0) (hh : cubicOne (φ Complex.I) 1 a b c = 0)
    (hm : ∀ j,
      jacobianMinors (gradQuadricOne 57 a) (gradCubicOne (φ Complex.I) 1 a b c) j ∈ J) :
    J = ⊤ := by
  have hi : (φ Complex.I) ^ 2 + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using
      congrArg φ (show Complex.I ^ 2 + 1 = 0 by simp)
  have hcert := CycleQ2SeedCurveGradientArithmetic.identity1 (φ Complex.I) a 1 b c hi
  simp only [one_pow, mul_one] at hcert
  have hmem :
      (6059424584881633543806844729000010994813153255561185835799340535703920806958867401340 : R)
        ∈ J := by
    rw [hcert]
    exact J.sum_mem fun k _ => J.mul_mem_left _ (first_generators_mem J _ a b c hq hh hm k)
  have hu : IsUnit
      (6059424584881633543806844729000010994813153255561185835799340535703920806958867401340 : ℂ) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  exact J.eq_top_of_isUnit_mem hmem (by simpa only [map_ofNat] using hu.map φ)

private theorem second_minors_unit_ideal (φ : ℂ →+* R) (a b c : R) (J : Ideal R)
    (hq : quadricTwo 57 a b c = 0) (hh : cubicTwo (φ Complex.I) 1 a b c = 0)
    (hm : ∀ j,
      jacobianMinors (gradQuadricTwo 57 a b c) (gradCubicTwo (φ Complex.I) 1 a b c) j ∈ J) :
    J = ⊤ := by
  have hi : (φ Complex.I) ^ 2 + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using
      congrArg φ (show Complex.I ^ 2 + 1 = 0 by simp)
  have hcert := CycleQ2SeedCurveGradientArithmetic.identity2 (φ Complex.I) a b 1 c hi
  simp only [one_pow, mul_one] at hcert
  have hmem :
      (12118849169763267087613689458000021989626306511122371671598681071407841613917734802680 : R)
        ∈ J := by
    rw [hcert]
    exact J.sum_mem fun k _ => J.mul_mem_left _ (second_generators_mem J _ a b c hq hh hm k)
  have hu : IsUnit
      (12118849169763267087613689458000021989626306511122371671598681071407841613917734802680 : ℂ) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  exact J.eq_top_of_isUnit_mem hmem (by simpa only [map_ofNat] using hu.map φ)

end Algebra

/-- The first actual incidence chart is covered by its three Jacobian opens. -/
theorem first_chart_jacobianIdeal_eq_top :
    jacobianIdeal (firstEquations 57 1) = ⊤ := by
  let f := chartMap (firstEquations 57 1)
  apply first_minors_unit_ideal (algebraMap ℂ _) (f (X 0)) (f (X 1)) (f (X 2))
  · have hz := chartMap_relation (firstEquations 57 1) 0
    change f (firstQuadric 57) = 0 at hz
    rw [map_firstQuadric] at hz
    simpa only [map_ofNat] using hz
  · have hz := chartMap_relation (firstEquations 57 1) 1
    change f (firstCubic 1) = 0 at hz
    rw [map_firstCubic] at hz
    simpa only [map_one] using hz
  · intro j
    have hm : chartMinor (firstEquations 57 1) j ∈ jacobianIdeal (firstEquations 57 1) :=
      Ideal.subset_span ⟨j, rfl⟩
    change f (jacobianMinors (fun k => pderiv k (firstEquations 57 1 0))
      (fun k => pderiv k (firstEquations 57 1 1)) j) ∈ _ at hm
    rw [map_first_minors] at hm
    simpa only [map_ofNat, map_one] using hm

/-- The second actual incidence chart has the same proved Jacobian cover. -/
theorem second_chart_jacobianIdeal_eq_top :
    jacobianIdeal (secondEquations 57 1) = ⊤ := by
  let f := chartMap (secondEquations 57 1)
  apply second_minors_unit_ideal (algebraMap ℂ _) (f (X 0)) (f (X 1)) (f (X 2))
  · have hz := chartMap_relation (secondEquations 57 1) 0
    change f (secondQuadric 57) = 0 at hz
    rw [map_secondQuadric] at hz
    simpa only [map_ofNat] using hz
  · have hz := chartMap_relation (secondEquations 57 1) 1
    change f (secondCubic 1) = 0 at hz
    rw [map_secondCubic] at hz
    simpa only [map_one] using hz
  · intro j
    have hm : chartMinor (secondEquations 57 1) j ∈ jacobianIdeal (secondEquations 57 1) :=
      Ideal.subset_span ⟨j, rfl⟩
    change f (jacobianMinors (fun k => pderiv k (secondEquations 57 1 0))
      (fun k => pderiv k (secondEquations 57 1 1)) j) ∈ _ at hm
    rw [map_second_minors] at hm
    simpa only [map_ofNat, map_one] using hm

theorem first_chart_exists_minor_not_mem
    (P : Ideal (ChartRing (firstEquations 57 1))) (hP : P.IsPrime) :
    ∃ j : Fin 3, chartMinor (firstEquations 57 1) j ∉ P :=
  exists_minor_not_mem _ first_chart_jacobianIdeal_eq_top P hP

theorem second_chart_exists_minor_not_mem
    (P : Ideal (ChartRing (secondEquations 57 1))) (hP : P.IsPrime) :
    ∃ j : Fin 3, chartMinor (secondEquations 57 1) j ∉ P :=
  exists_minor_not_mem _ second_chart_jacobianIdeal_eq_top P hP

theorem first_chart_basicOpen_cover :
    (⨆ j : Fin 3, PrimeSpectrum.basicOpen (chartMinor (firstEquations 57 1) j)) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr first_chart_jacobianIdeal_eq_top

theorem second_chart_basicOpen_cover :
    (⨆ j : Fin 3, PrimeSpectrum.basicOpen (chartMinor (secondEquations 57 1) j)) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr second_chart_jacobianIdeal_eq_top

theorem first_chart_exists_pivot
    (P : Ideal (ChartRing (firstEquations 57 1))) (hP : P.IsPrime) :
    ∃ e : Equiv.Perm (Fin 3), (chartPresentation (firstEquations 57 1) e).jacobian ∉ P := by
  obtain ⟨j, hj⟩ := first_chart_exists_minor_not_mem P hP
  exact ⟨pivotPermutation j, by rwa [pivot_jacobian]⟩

theorem second_chart_exists_pivot
    (P : Ideal (ChartRing (secondEquations 57 1))) (hP : P.IsPrime) :
    ∃ e : Equiv.Perm (Fin 3), (chartPresentation (secondEquations 57 1) e).jacobian ∉ P := by
  obtain ⟨j, hj⟩ := second_chart_exists_minor_not_mem P hP
  exact ⟨pivotPermutation j, by rwa [pivot_jacobian]⟩

end CycleQ2GeometricIncidenceJacobianCover

#print axioms CycleQ2GeometricIncidenceJacobianCover.first_chart_jacobianIdeal_eq_top
#print axioms CycleQ2GeometricIncidenceJacobianCover.second_chart_jacobianIdeal_eq_top
#print axioms CycleQ2GeometricIncidenceJacobianCover.first_chart_basicOpen_cover
#print axioms CycleQ2GeometricIncidenceJacobianCover.second_chart_basicOpen_cover

end

end SourceGeometricIncidenceJacobianCover

section SourceGeometricSmoothCanonicalOverlap

/-!
# Canonical transition for every smooth member of the literal curve family

The whole-chart argument is parameterized by the two actual unit Jacobian
ideals. It applies to any parameters with those proved identities, including
the incidence member (57, 1). No further minor localization is introduced.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSmoothCanonicalOverlap

set_option linter.unusedVariables false

open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricAffineOverlap
  CycleQ2GeometricSparseJacobianCover

/-- The actual localization homomorphism from an entire affine chart. -/
def localizationMap (v : Fin 2 → AffinePoly) :
    ChartRing v →ₐ[ℂ] CoordinateOverlap v :=
  IsScalarTower.toAlgHom ℂ (ChartRing v) (CoordinateOverlap v)

def firstChartMap (r θ : ℂ) : ChartRing (firstEquations r θ) →ₐ[ℂ] FirstOverlap r θ :=
  localizationMap (firstEquations r θ)

/-- The second chart maps into the same actual overlap through the proved
coordinate-change algebra equivalence. -/
def secondChartMap (r θ : ℂ) : ChartRing (secondEquations r θ) →ₐ[ℂ] FirstOverlap r θ :=
  (overlapEquiv r θ).toAlgHom.comp (localizationMap (secondEquations r θ))

@[simp] theorem localizationMap_coordinate (v : Fin 2 → AffinePoly) (j : Fin 3) :
    localizationMap v (CycleQ2GeometricChartKaehler.coordinate v j) = coordinate v j := rfl

@[simp] theorem localizationMap_minor (v : Fin 2 → AffinePoly) (j : Fin 3) :
    localizationMap v (chartMinor v j) = chartMinors v j := rfl

@[simp] theorem secondChartMap_coordinate (r θ : ℂ) (j : Fin 3) :
    secondChartMap r θ (CycleQ2GeometricChartKaehler.coordinate (secondEquations r θ) j) =
      overlapEquiv r θ (coordinate (secondEquations r θ) j) := rfl

@[simp] theorem secondChartMap_minor (r θ : ℂ) (j : Fin 3) :
    secondChartMap r θ (chartMinor (secondEquations r θ) j) =
      overlapEquiv r θ (chartMinors (secondEquations r θ) j) := rfl

/-- The first whole-chart form restricted to the actual overlap. -/
def firstForm (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) : KaehlerDifferential ℂ (FirstOverlap r θ) :=
  differentialMap (firstChartMap r θ) (CycleQ2GeometricChartKaehler.globalForm (firstEquations r θ) h1)

/-- The second whole-chart form transported into the actual first overlap. -/
def secondForm (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) : KaehlerDifferential ℂ (FirstOverlap r θ) :=
  differentialMap (secondChartMap r θ) (CycleQ2GeometricChartKaehler.globalForm (secondEquations r θ) h2)

/-- Universal differentiation commutes with the actual algebra maps. -/
theorem mapped_coordinate_differential (v : Fin 2 → AffinePoly) (h : jacobianIdeal v = ⊤)
    {S : Type*} [CommRing S] [Algebra ℂ S] (f : ChartRing v →ₐ[ℂ] S) (j : Fin 3) :
    KaehlerDifferential.D ℂ S (f (CycleQ2GeometricChartKaehler.coordinate v j)) =
      f (chartMinor v j) • differentialMap f (CycleQ2GeometricChartKaehler.globalForm v h) := by
  simpa only [differentialMap_D, differentialMap_smul] using
    congrArg (differentialMap f) (CycleQ2GeometricChartKaehler.differential_coordinate_eq_smul v h j)

theorem first_coordinate_differential (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) (j : Fin 3) :
    KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) j) =
      chartMinors (firstEquations r θ) j • firstForm r θ h1 h2 :=
  mapped_coordinate_differential (firstEquations r θ)
    (h1) (firstChartMap r θ) j

theorem second_coordinate_differential (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) (j : Fin 3) :
    KaehlerDifferential.D ℂ (FirstOverlap r θ)
        (overlapEquiv r θ (coordinate (secondEquations r θ) j)) =
      overlapEquiv r θ (chartMinors (secondEquations r θ) j) • secondForm r θ h1 h2 :=
  mapped_coordinate_differential (secondEquations r θ)
    (h2) (secondChartMap r θ) j

section CoefficientIdentities
variable {R : Type*} [CommRing R]

private theorem outer_coefficient (a b t m n : R) (ht : b * t = 1) :
    t * m - a * t ^ 2 * n = (-t ^ 2 * m + a * t ^ 3 * n) * (-b) := by
  linear_combination (-t * m + a * t ^ 2 * n) * ht

private theorem middle_coefficient (b t n : R) (ht : b * t = 1) :
    (-t ^ 2) * n = (t ^ 3 * n) * (-b) := by
  linear_combination t ^ 2 * n * ht

end CoefficientIdentities

/-- The chain rule and all three actual cofactor transformations give the
same candidate transition for every coordinate differential. -/
theorem coordinate_transition (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) (j : Fin 3) :
    overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) j)) =
      overlapEquiv r θ (chartMinors (secondEquations r θ) j) •
        (-(coordinate (firstEquations r θ) 1) • firstForm r θ h1 h2) := by
  have hmin := congrFun (overlapEquiv_allMinors r θ) j
  fin_cases j
  · change overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) 0)) =
        overlapEquiv r θ (chartMinors (secondEquations r θ) 0) •
          (-(coordinate (firstEquations r θ) 1) • firstForm r θ h1 h2)
    rw [overlapDifferential_coordinate0 r θ, first_coordinate_differential r θ h1 h2 0,
      first_coordinate_differential r θ h1 h2 1]
    change overlapEquiv r θ (chartMinors (secondEquations r θ) 0) =
      -inverse (firstEquations r θ) ^ 2 * chartMinors (firstEquations r θ) 0 +
        coordinate (firstEquations r θ) 0 * inverse (firstEquations r θ) ^ 3 *
          chartMinors (firstEquations r θ) 1 at hmin
    rw [hmin]
    simp only [smul_smul, ← sub_smul]
    rw [outer_coefficient _ _ _ _ _ (coordinate_mul_inverse (firstEquations r θ))]
  · change overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) 1)) =
        overlapEquiv r θ (chartMinors (secondEquations r θ) 1) •
          (-(coordinate (firstEquations r θ) 1) • firstForm r θ h1 h2)
    rw [overlapDifferential_coordinate1 r θ, first_coordinate_differential r θ h1 h2 1]
    change overlapEquiv r θ (chartMinors (secondEquations r θ) 1) =
      inverse (firstEquations r θ) ^ 3 * chartMinors (firstEquations r θ) 1 at hmin
    rw [hmin]
    simp only [smul_smul]
    rw [middle_coefficient _ _ _ (coordinate_mul_inverse (firstEquations r θ))]
  · change overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) 2)) =
        overlapEquiv r θ (chartMinors (secondEquations r θ) 2) •
          (-(coordinate (firstEquations r θ) 1) • firstForm r θ h1 h2)
    rw [overlapDifferential_coordinate2 r θ, first_coordinate_differential r θ h1 h2 2,
      first_coordinate_differential r θ h1 h2 1]
    change overlapEquiv r θ (chartMinors (secondEquations r θ) 2) =
      -inverse (firstEquations r θ) ^ 2 * chartMinors (firstEquations r θ) 2 +
        coordinate (firstEquations r θ) 2 * inverse (firstEquations r θ) ^ 3 *
          chartMinors (firstEquations r θ) 1 at hmin
    rw [hmin]
    simp only [smul_smul, ← sub_smul]
    rw [outer_coefficient _ _ _ _ _ (coordinate_mul_inverse (firstEquations r θ))]

/-- All three actual minors kill the difference between the two forms. -/
theorem minor_smul_transition (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) (j : Fin 3) :
    secondChartMap r θ (chartMinor (secondEquations r θ) j) • secondForm r θ h1 h2 =
      secondChartMap r θ (chartMinor (secondEquations r θ) j) •
        (-(coordinate (firstEquations r θ) 1) • firstForm r θ h1 h2) := by
  rw [secondChartMap_minor, ← second_coordinate_differential]
  exact (differentialEquiv_D (overlapEquiv r θ)
    (coordinate (secondEquations r θ) j)).symm.trans (coordinate_transition r θ h1 h2 j)

section BezoutUniqueness
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- A finite unit-ideal family detects equality in any module. -/
theorem eq_of_bezout_smul (c w : Fin 3 → R) (hw : ∑ j, w j * c j = 1)
    (x y : M) (hxy : ∀ j, c j • x = c j • y) : x = y := by
  calc
    x = (∑ j, w j * c j) • x := by rw [hw, one_smul]
    _ = ∑ j, w j • (c j • x) := by simp only [Finset.sum_smul, smul_smul]
    _ = ∑ j, w j • (c j • y) := Finset.sum_congr rfl (fun j _ => congrArg (w j • ·) (hxy j))
    _ = (∑ j, w j * c j) • y := by simp only [Finset.sum_smul, smul_smul]
    _ = y := by rw [hw, one_smul]

end BezoutUniqueness

/-- The full affine overlap transition, without inverting a Jacobian minor. -/
theorem full_overlap_transition (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) :
    secondForm r θ h1 h2 = -(coordinate (firstEquations r θ) 1) • firstForm r θ h1 h2 := by
  have hone : (1 : ChartRing (secondEquations r θ)) ∈
      Ideal.span (Set.range (chartMinor (secondEquations r θ))) := by
    change (1 : ChartRing (secondEquations r θ)) ∈ jacobianIdeal (secondEquations r θ)
    rw [h2]
    trivial
  obtain ⟨w, hw⟩ := Ideal.mem_span_range_iff_exists_fun.mp hone
  have hmap : ∑ j, secondChartMap r θ (w j) *
      secondChartMap r θ (chartMinor (secondEquations r θ) j) = 1 := by
    simpa only [map_sum, map_mul, map_one] using congrArg (secondChartMap r θ) hw
  exact eq_of_bezout_smul _ _ hmap _ _ (minor_smul_transition r θ h1 h2)

/-- Projective orientation of the first chart's genuine differential. -/
def firstOrientedForm (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) : KaehlerDifferential ℂ (FirstOverlap r θ) :=
  -firstForm r θ h1 h2

/-- In projective orientation, the factor is precisely the coordinate x2/x1. -/
theorem oriented_overlap_transition (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) :
    secondForm r θ h1 h2 = coordinate (firstEquations r θ) 1 • firstOrientedForm r θ h1 h2 := by
  rw [full_overlap_transition, firstOrientedForm, smul_neg, neg_smul]

/-- The identity explicitly displays both maps out of the original chart rings. -/
theorem actual_chart_form_transition (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) :
    differentialMap (secondChartMap r θ) (CycleQ2GeometricChartKaehler.globalForm (secondEquations r θ) h2) =
      coordinate (firstEquations r θ) 1 • differentialMap (firstChartMap r θ)
        (-CycleQ2GeometricChartKaehler.globalForm (firstEquations r θ) h1) := by
  simpa only [firstOrientedForm, firstForm, secondForm, map_neg] using
    oriented_overlap_transition r θ h1 h2

/-- Equivalently, restriction to the second overlap followed by the actual
Kähler equivalence gives the same oriented transition. -/
theorem overlap_equivalence_form_transition (r θ : ℂ)
    (h1 : jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : jacobianIdeal (secondEquations r θ) = ⊤) :
    overlapDifferentialEquiv r θ
      (differentialMap (localizationMap (secondEquations r θ))
        (CycleQ2GeometricChartKaehler.globalForm (secondEquations r θ) h2)) =
      coordinate (firstEquations r θ) 1 •
        differentialMap (localizationMap (firstEquations r θ))
          (-CycleQ2GeometricChartKaehler.globalForm (firstEquations r θ) h1) := by
  change differentialMap (overlapEquiv r θ).toAlgHom
    (differentialMap (localizationMap (secondEquations r θ)) _) = _
  rw [differentialMap_comp]
  exact actual_chart_form_transition r θ h1 h2

#print axioms full_overlap_transition
#print axioms oriented_overlap_transition
#print axioms actual_chart_form_transition
#print axioms overlap_equivalence_form_transition

end CycleQ2GeometricSmoothCanonicalOverlap
end

end SourceGeometricSmoothCanonicalOverlap

section SourceGeometricProjectiveKaehler

/-!
# Canonical differentials on the actual projective coordinate rings

The affine residue frames are transported through the proved coordinate
presentations. Their transition is proved for the actual homogeneous
localization maps, which are already identified with structure-sheaf
restriction. In particular the coordinate x2/x1, the complex coefficient
maps, and both differential restrictions belong to the same projective curve.

This is the coordinate-ring comparison. Extension to the sheaf of
differentials and the global Serre comparison are separate constructions.
-/

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveKaehler

open CycleQ2GeometricProjectiveAffine CycleQ2GeometricProjectiveOverlap
  CycleQ2GeometricAffineCurveCharts CycleQ2GeometricAffineOverlap

section Transport

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- Transport a genuine rank-one differential module along an algebra
equivalence. The resulting frame is linear over the original ring. -/
def transportFrame (e : A ≃ₐ[ℂ] B)
    (t : KaehlerDifferential ℂ B ≃ₗ[B] B) : KaehlerDifferential ℂ A ≃ₗ[A] A where
  toEquiv := (differentialEquiv e).toEquiv.trans (t.toEquiv.trans e.symm.toEquiv)
  map_add' x y := by
    change e.symm (t (differentialEquiv e (x + y))) =
      e.symm (t (differentialEquiv e x)) + e.symm (t (differentialEquiv e y))
    rw [map_add, map_add, map_add]
  map_smul' a x := by
    change e.symm (t (differentialEquiv e (a • x))) =
      a • e.symm (t (differentialEquiv e x))
    rw [differentialEquiv_smul, map_smul]
    change e.symm (e a * t (differentialEquiv e x)) =
      a * e.symm (t (differentialEquiv e x))
    rw [map_mul, AlgEquiv.symm_apply_apply]

@[simp] theorem transportFrame_apply (e : A ≃ₐ[ℂ] B)
    (t : KaehlerDifferential ℂ B ≃ₗ[B] B) (x : KaehlerDifferential ℂ A) :
    transportFrame e t x = e.symm (t (differentialEquiv e x)) := rfl

end Transport

/-- The first genuine projective restriction, as a complex algebra map. -/
def firstRestriction (r θ : ℂ) :
    ProjectiveCoordinateRing r θ 1 →ₐ[ℂ] ProjectiveCoordinateOverlapRing r θ :=
  (firstOverlapEquiv r θ).symm.toAlgHom.comp
    ((CycleQ2GeometricCanonicalOverlap.localizationMap (firstEquations r θ)).comp
      (firstCoordinateEquiv r θ).toAlgHom)

/-- The second genuine projective restriction, as a complex algebra map. -/
def secondRestriction (r θ : ℂ) :
    ProjectiveCoordinateRing r θ 2 →ₐ[ℂ] ProjectiveCoordinateOverlapRing r θ :=
  (secondOverlapEquiv r θ).symm.toAlgHom.comp
    ((CycleQ2GeometricCanonicalOverlap.localizationMap (secondEquations r θ)).comp
      (secondCoordinateEquiv r θ).toAlgHom)

@[simp] theorem firstRestriction_apply (r θ : ℂ) (a : ProjectiveCoordinateRing r θ 1) :
    firstRestriction r θ a = firstCoordinateRestriction r θ a := by
  change (firstOverlapEquiv r θ).symm
    (algebraMap (FirstChartRing r θ) (FirstOverlap r θ) (firstCoordinateEquiv r θ a)) = _
  rw [firstOverlapEquiv_symm_base, AlgEquiv.symm_apply_apply]

@[simp] theorem secondRestriction_apply (r θ : ℂ) (a : ProjectiveCoordinateRing r θ 2) :
    secondRestriction r θ a = secondCoordinateRestriction r θ a := by
  change (secondOverlapEquiv r θ).symm
    (algebraMap (SecondChartRing r θ) (SecondOverlap r θ) (secondCoordinateEquiv r θ a)) = _
  rw [secondOverlapEquiv_symm_base, AlgEquiv.symm_apply_apply]

theorem first_restriction_differential (r θ : ℂ)
    (ω : KaehlerDifferential ℂ (ProjectiveCoordinateRing r θ 1)) :
    differentialEquiv (firstOverlapEquiv r θ) (differentialMap (firstRestriction r θ) ω) =
      differentialMap (CycleQ2GeometricCanonicalOverlap.localizationMap (firstEquations r θ))
        (differentialEquiv (firstCoordinateEquiv r θ) ω) := by
  change differentialMap (firstOverlapEquiv r θ).toAlgHom
      (differentialMap (firstRestriction r θ) ω) =
    differentialMap _ (differentialMap (firstCoordinateEquiv r θ).toAlgHom ω)
  rw [differentialMap_comp, differentialMap_comp]
  congr 1
  apply congrArg differentialMap
  apply AlgHom.ext
  intro a
  change firstOverlapEquiv r θ ((firstOverlapEquiv r θ).symm _) = _
  exact AlgEquiv.apply_symm_apply _ _

theorem second_restriction_differential (r θ : ℂ)
    (ω : KaehlerDifferential ℂ (ProjectiveCoordinateRing r θ 2)) :
    differentialEquiv (secondOverlapEquiv r θ) (differentialMap (secondRestriction r θ) ω) =
      differentialMap (CycleQ2GeometricCanonicalOverlap.localizationMap (secondEquations r θ))
        (differentialEquiv (secondCoordinateEquiv r θ) ω) := by
  change differentialMap (secondOverlapEquiv r θ).toAlgHom
      (differentialMap (secondRestriction r θ) ω) =
    differentialMap _ (differentialMap (secondCoordinateEquiv r θ).toAlgHom ω)
  rw [differentialMap_comp, differentialMap_comp]
  congr 1
  apply congrArg differentialMap
  apply AlgHom.ext
  intro a
  change secondOverlapEquiv r θ ((secondOverlapEquiv r θ).symm _) = _
  exact AlgEquiv.apply_symm_apply _ _

theorem overlap_differential_compatibility (r θ : ℂ)
    (ω : KaehlerDifferential ℂ (ProjectiveCoordinateOverlapRing r θ)) :
    differentialEquiv (firstOverlapEquiv r θ) ω =
      overlapDifferentialEquiv r θ (differentialEquiv (secondOverlapEquiv r θ) ω) := by
  change differentialMap (firstOverlapEquiv r θ).toAlgHom ω =
    differentialMap (overlapEquiv r θ).toAlgHom
      (differentialMap (secondOverlapEquiv r θ).toAlgHom ω)
  rw [differentialMap_comp]
  congr 1
  apply congrArg differentialMap
  apply AlgHom.ext
  intro a
  exact overlapEquiv_compatibility r θ a

/-- The actual first projective chart has a differential frame, without
inverting an additional Jacobian minor. -/
def firstResidueEquiv (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    KaehlerDifferential ℂ (ProjectiveCoordinateRing r θ 1) ≃ₗ[
      ProjectiveCoordinateRing r θ 1] ProjectiveCoordinateRing r θ 1 :=
  transportFrame (firstCoordinateEquiv r θ)
    (CycleQ2GeometricChartKaehler.kaehlerResidueEquiv (firstEquations r θ) h1)

/-- The corresponding frame on the whole second projective chart. -/
def secondResidueEquiv (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    KaehlerDifferential ℂ (ProjectiveCoordinateRing r θ 2) ≃ₗ[
      ProjectiveCoordinateRing r θ 2] ProjectiveCoordinateRing r θ 2 :=
  transportFrame (secondCoordinateEquiv r θ)
    (CycleQ2GeometricChartKaehler.kaehlerResidueEquiv (secondEquations r θ) h2)

def firstOrientedFrame (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    KaehlerDifferential ℂ (ProjectiveCoordinateRing r θ 1) :=
  (differentialEquiv (firstCoordinateEquiv r θ)).symm
    (-CycleQ2GeometricChartKaehler.globalForm (firstEquations r θ) h1)

def secondOrientedFrame (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    KaehlerDifferential ℂ (ProjectiveCoordinateRing r θ 2) :=
  (differentialEquiv (secondCoordinateEquiv r θ)).symm
    (CycleQ2GeometricChartKaehler.globalForm (secondEquations r θ) h2)

@[simp] theorem firstOrientedFrame_image (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    differentialEquiv (firstCoordinateEquiv r θ) (firstOrientedFrame r θ h1 h2) =
      -CycleQ2GeometricChartKaehler.globalForm (firstEquations r θ) h1 :=
  LinearEquiv.apply_symm_apply _ _

@[simp] theorem secondOrientedFrame_image (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    differentialEquiv (secondCoordinateEquiv r θ) (secondOrientedFrame r θ h1 h2) =
      CycleQ2GeometricChartKaehler.globalForm (secondEquations r θ) h2 :=
  LinearEquiv.apply_symm_apply _ _

@[simp] theorem firstOrientedFrame_coefficient (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    firstResidueEquiv r θ h1 h2 (firstOrientedFrame r θ h1 h2) = -1 := by
  change (firstCoordinateEquiv r θ).symm
    (CycleQ2GeometricChartKaehler.kaehlerResidueEquiv (firstEquations r θ) h1
      (differentialEquiv (firstCoordinateEquiv r θ) (firstOrientedFrame r θ h1 h2))) = -1
  rw [firstOrientedFrame_image, map_neg,
    CycleQ2GeometricChartKaehler.kaehlerResidueEquiv_globalForm, map_neg, map_one]

@[simp] theorem secondOrientedFrame_coefficient (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    secondResidueEquiv r θ h1 h2 (secondOrientedFrame r θ h1 h2) = 1 := by
  change (secondCoordinateEquiv r θ).symm
    (CycleQ2GeometricChartKaehler.kaehlerResidueEquiv (secondEquations r θ) h2
      (differentialEquiv (secondCoordinateEquiv r θ) (secondOrientedFrame r θ h1 h2))) = 1
  rw [secondOrientedFrame_image,
    CycleQ2GeometricChartKaehler.kaehlerResidueEquiv_globalForm, map_one]

/-- The canonical transition on the actual projective overlap: both maps
are the previously proved structure-sheaf restrictions. -/
theorem projective_frame_transition (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    differentialMap (secondRestriction r θ) (secondOrientedFrame r θ h1 h2) =
      firstCoordinateRestriction r θ (coordinateRatio r θ 1 2) •
        differentialMap (firstRestriction r θ) (firstOrientedFrame r θ h1 h2) := by
  apply (differentialEquiv (firstOverlapEquiv r θ)).injective
  rw [differentialEquiv_smul, firstOverlapEquiv_ratio,
    overlap_differential_compatibility, second_restriction_differential,
    first_restriction_differential, firstOrientedFrame_image, secondOrientedFrame_image]
  simp only [CycleQ2GeometricAffineCurveCharts.firstDehomogenize, MvPolynomial.aeval_X,
    Matrix.cons_val_two]
  change overlapDifferentialEquiv r θ
    (differentialMap (CycleQ2GeometricCanonicalOverlap.localizationMap (secondEquations r θ))
      (CycleQ2GeometricChartKaehler.globalForm (secondEquations r θ) h2)) =
    coordinate (firstEquations r θ) 1 •
      differentialMap (CycleQ2GeometricCanonicalOverlap.localizationMap (firstEquations r θ))
        (-CycleQ2GeometricChartKaehler.globalForm (firstEquations r θ) h1)
  exact CycleQ2GeometricSmoothCanonicalOverlap.overlap_equivalence_form_transition r θ h1 h2

#print axioms firstResidueEquiv
#print axioms secondResidueEquiv
#print axioms projective_frame_transition

end CycleQ2GeometricProjectiveKaehler

end

end SourceGeometricProjectiveKaehler

section SourceGeometricProjectiveSectionForms

/-!
# Canonical frame sections in the actual projective differential sheaf

The coordinate-ring frames are placed in the genuine sheaf of complex
differentials by the sheafification unit. Their transition is proved in
that sheaf, over the actual coordinate overlap and with the actual
structure-sheaf transition section.
-/

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveSectionForms

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveAffine
  CycleQ2GeometricProjectiveOverlap CycleQ2GeometricProjectiveKaehler
  CycleQ2GeometricProjectiveCoefficients CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricAffineOverlap

local instance (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Algebra ℂ Γ(projectiveCurve r θ, O) :=
  sectionAlgebra (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O

local instance (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Algebra ℂ (SectionRing (projectiveCurve r θ).sheaf O) :=
  sectionAlgebra (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O

local instance (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Module Γ(projectiveCurve r θ, O)
      (SectionForms (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O) := by
  change Module (SectionRing (projectiveCurve r θ).sheaf O)
    (KaehlerDifferential ℂ (SectionRing (projectiveCurve r θ).sheaf O))
  infer_instance

def coordinateSectionsAlgEquiv (r θ : ℂ) (j : Fin 4) :
    Γ(projectiveCurve r θ, coordinateProjectivePatch r θ j) ≃ₐ[ℂ]
      ProjectiveCoordinateRing r θ j where
  __ := (Proj.basicOpenIsoAway (curveGrade r θ) (coordinateDen r θ j)
    (coordinate_mem_grade r θ j) (by decide)).symm.commRingCatIsoToRingEquiv
  commutes' := coefficientOn_coordinatePatch r θ j

def overlapSectionsAlgEquiv (r θ : ℂ) :
    Γ(projectiveCurve r θ, coordinateOverlapPatch r θ) ≃ₐ[ℂ]
      ProjectiveCoordinateOverlapRing r θ where
  __ := (coordinateOverlapSectionsIso r θ).symm.commRingCatIsoToRingEquiv
  commutes' c := coefficientOn_basicOpen r θ (coordinateOverlapDen r θ)
    (coordinateOverlapDen_mem_grade r θ) (by decide) c

theorem first_sections_restriction (r θ : ℂ)
    (s : Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1)) :
    overlapSectionsAlgEquiv r θ
        ((projectiveCurve r θ).presheaf.map (homOfLE (coordinateOverlap_le_first r θ)).op s) =
      firstRestriction r θ (coordinateSectionsAlgEquiv r θ 1 s) := by
  apply (firstOverlapEquiv r θ).injective
  rw [firstRestriction_apply, firstOverlapEquiv_restriction]
  exact firstOverlapSectionsEquiv_restriction r θ s

theorem second_sections_restriction (r θ : ℂ)
    (s : Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 2)) :
    overlapSectionsAlgEquiv r θ
        ((projectiveCurve r θ).presheaf.map (homOfLE (coordinateOverlap_le_second r θ)).op s) =
      secondRestriction r θ (coordinateSectionsAlgEquiv r θ 2 s) := by
  apply (secondOverlapEquiv r θ).injective
  rw [secondRestriction_apply, secondOverlapEquiv_restriction]
  exact secondOverlapSectionsEquiv_restriction r θ s

theorem first_differentials_restriction (r θ : ℂ)
    (ω : SectionForms (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (coordinateProjectivePatch r θ 1)) :
    differentialEquiv (overlapSectionsAlgEquiv r θ)
        (differentialMap (sectionRestriction (projectiveCurve r θ).sheaf
          (projectiveGlobalCoefficient r θ) (coordinateOverlap_le_first r θ)) ω) =
      differentialMap (firstRestriction r θ)
        (differentialEquiv (coordinateSectionsAlgEquiv r θ 1) ω) := by
  change differentialMap (overlapSectionsAlgEquiv r θ).toAlgHom (differentialMap _ ω) =
    differentialMap _ (differentialMap (coordinateSectionsAlgEquiv r θ 1).toAlgHom ω)
  rw [differentialMap_comp, differentialMap_comp]
  congr 1
  apply congrArg differentialMap
  apply AlgHom.ext
  intro a
  exact first_sections_restriction r θ a

theorem second_differentials_restriction (r θ : ℂ)
    (ω : SectionForms (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (coordinateProjectivePatch r θ 2)) :
    differentialEquiv (overlapSectionsAlgEquiv r θ)
        (differentialMap (sectionRestriction (projectiveCurve r θ).sheaf
          (projectiveGlobalCoefficient r θ) (coordinateOverlap_le_second r θ)) ω) =
      differentialMap (secondRestriction r θ)
        (differentialEquiv (coordinateSectionsAlgEquiv r θ 2) ω) := by
  change differentialMap (overlapSectionsAlgEquiv r θ).toAlgHom (differentialMap _ ω) =
    differentialMap _ (differentialMap (coordinateSectionsAlgEquiv r θ 2).toAlgHom ω)
  rw [differentialMap_comp, differentialMap_comp]
  congr 1
  apply congrArg differentialMap
  apply AlgHom.ext
  intro a
  exact second_sections_restriction r θ a

def firstSectionForm (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    SectionForms (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (coordinateProjectivePatch r θ 1) :=
  (differentialEquiv (coordinateSectionsAlgEquiv r θ 1)).symm (firstOrientedFrame r θ h1 h2)

def secondSectionForm (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    SectionForms (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (coordinateProjectivePatch r θ 2) :=
  (differentialEquiv (coordinateSectionsAlgEquiv r θ 2)).symm (secondOrientedFrame r θ h1 h2)

def transitionSection (r θ : ℂ) : Γ(projectiveCurve r θ, coordinateOverlapPatch r θ) :=
  (overlapSectionsAlgEquiv r θ).symm
    (firstCoordinateRestriction r θ (coordinateRatio r θ 1 2))

theorem section_form_transition (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    differentialMap (sectionRestriction (projectiveCurve r θ).sheaf
        (projectiveGlobalCoefficient r θ) (coordinateOverlap_le_second r θ))
        (secondSectionForm r θ h1 h2) =
      (transitionSection r θ : SectionRing (projectiveCurve r θ).sheaf
        (coordinateOverlapPatch r θ)) •
        differentialMap (sectionRestriction (projectiveCurve r θ).sheaf
          (projectiveGlobalCoefficient r θ) (coordinateOverlap_le_first r θ))
          (firstSectionForm r θ h1 h2) := by
  apply (differentialEquiv (overlapSectionsAlgEquiv r θ)).injective
  rw [differentialEquiv_smul, first_differentials_restriction, second_differentials_restriction]
  simp only [firstSectionForm, secondSectionForm, LinearEquiv.apply_symm_apply,
    transitionSection, AlgEquiv.apply_symm_apply]
  exact projective_frame_transition r θ h1 h2

/-- An actual section of the projective differential sheaf on the whole
first coordinate chart. -/
def firstSheafFrame (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    (projectiveDifferentialSheaf r θ).val.obj (op (coordinateProjectivePatch r θ 1)) :=
  toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) _ (firstSectionForm r θ h1 h2)

/-- The corresponding actual section on the whole second coordinate chart. -/
def secondSheafFrame (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    (projectiveDifferentialSheaf r θ).val.obj (op (coordinateProjectivePatch r θ 2)) :=
  toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) _ (secondSectionForm r θ h1 h2)

/-- The canonical transition now holds in the genuine differential sheaf,
with the actual section restrictions, not only in a quotient model. -/
theorem sheaf_frame_transition (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    (projectiveDifferentialSheaf r θ).val.map
        (homOfLE (coordinateOverlap_le_second r θ)).op (secondSheafFrame r θ h1 h2) =
      transitionSection r θ • (projectiveDifferentialSheaf r θ).val.map
        (homOfLE (coordinateOverlap_le_first r θ)).op (firstSheafFrame r θ h1 h2) :=
  toSheaf_relation (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (coordinateOverlap_le_first r θ) (coordinateOverlap_le_second r θ)
    (firstSectionForm r θ h1 h2) (secondSectionForm r θ h1 h2) (transitionSection r θ)
    (section_form_transition r θ h1 h2)

#print axioms sheaf_frame_transition

end CycleQ2GeometricProjectiveSectionForms

end

end SourceGeometricProjectiveSectionForms

section SourceGeometricProjectiveFrameRestriction

/-!
# Canonical frames on the original Cech cover

The coordinate-overlap transition restricts to the exact transition unit
used to construct the original degree-one sheaf and its nonzero Cech class.
Consequently the genuine differential-sheaf frames satisfy that same
gluing equation on the original quartic-denominator cover.
-/

set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveFrameRestriction

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
  CycleQ2NormalConnecting CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveAffine CycleQ2GeometricProjectiveOverlap
  CycleQ2GeometricProjectiveSectionForms CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricTwistedFrameMap

local instance (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Module Γ(projectiveCurve r θ, O)
      ((projectiveDifferentialSheaf r θ).val.obj (op O)) :=
  inferInstanceAs (Module ((ringSheaf (projectiveCurve r θ).sheaf).obj.obj (op O))
    ((projectiveDifferentialSheaf r θ).val.obj (op O)))

def denominatorOverlapComplement (r θ : ℂ) : CurveRing r θ :=
  firstFrameComplement r θ * secondFrameComplement r θ

theorem denominatorOverlapComplement_grade (r θ : ℂ) :
    denominatorOverlapComplement r θ ∈ curveGrade r θ 6 :=
  SetLike.mul_mem_graded (firstFrameComplement_grade r θ) (secondFrameComplement_grade r θ)

theorem denominatorOverlap_factorization (r θ : ℂ) :
    curveG1 r θ * curveG2 r θ =
      coordinateOverlapDen r θ * denominatorOverlapComplement r θ := by
  rw [firstFrame_factorization, secondFrame_factorization]
  change (coordinateDen r θ 1 * firstFrameComplement r θ) *
      (coordinateDen r θ 2 * secondFrameComplement r θ) =
    (coordinateDen r θ 1 * coordinateDen r θ 2) *
      (firstFrameComplement r θ * secondFrameComplement r θ)
  ring

def denominatorOverlapRestriction (r θ : ℂ) :
    ProjectiveCoordinateOverlapRing r θ →+* OverlapProjectiveRing r θ :=
  HomogeneousLocalization.awayMap (curveGrade r θ)
    (denominatorOverlapComplement_grade r θ) (denominatorOverlap_factorization r θ)

theorem coordinateRatio_mul_coordinate (r θ : ℂ) :
    (firstCoordinateRestriction r θ (coordinateRatio r θ 1 2)).val *
        algebraMap (CurveRing r θ) (Localization.Away (coordinateOverlapDen r θ))
          (coordinateDen r θ 1) =
      algebraMap (CurveRing r θ) (Localization.Away (coordinateOverlapDen r θ))
        (coordinateDen r θ 2) := by
  rw [firstCoordinateRestriction, coordinateRestriction_ratio_val]
  rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, one_mul, mul_one,
    coordinateOverlapDen]
  ring

/-- The computed coordinate ratio is exactly the earlier degree-one
transition, after restricting to the original denominator overlap. -/
theorem denominatorOverlapRestriction_transition (r θ : ℂ) :
    denominatorOverlapRestriction r θ
        (firstCoordinateRestriction r θ (coordinateRatio r θ 1 2)) =
      overlapTransition r θ := by
  apply HomogeneousLocalization.val_injective
  apply (frameCoordinate_isUnit r θ _ _ _ (overlapFirstFrame_factorization r θ)).mul_right_cancel
  rw [overlapTransition_coordinate]
  have h := congrArg
    (awayRestriction r θ (coordinateOverlapDen r θ) (denominatorOverlapComplement r θ)
      (curveG1 r θ * curveG2 r θ) (denominatorOverlap_factorization r θ))
    (coordinateRatio_mul_coordinate r θ)
  rw [map_mul, awayRestriction_base, awayRestriction_base] at h
  change (denominatorOverlapRestriction r θ _).val *
    algebraMap (CurveRing r θ) (Overlap r θ) (coordinateDen r θ 1) = _
  rw [denominatorOverlapRestriction, awayRestriction_val]
  exact h

theorem denominatorOverlapRestriction_is_sheaf_restriction (r θ : ℂ)
    (a : ProjectiveCoordinateOverlapRing r θ) :
    (projectiveCurve r θ).presheaf.map
        (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)).op
        ((coordinateOverlapSectionsIso r θ).hom a) =
      (overlapProjectiveSectionsIso r θ).hom (denominatorOverlapRestriction r θ a) := by
  exact congrArg (fun k => k a)
    (Proj.awayMap_awayToSection (curveGrade r θ)
      (denominatorOverlapComplement_grade r θ) (denominatorOverlap_factorization r θ)).symm

theorem transitionSection_restrict (r θ : ℂ) :
    (projectiveCurve r θ).presheaf.map
        (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)).op (transitionSection r θ) =
      (projectiveTransitionUnit r θ :
        Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) := by
  change (projectiveCurve r θ).presheaf.map
      (homOfLE (denominatorOverlap_le_coordinateOverlap r θ)).op
      ((coordinateOverlapSectionsIso r θ).hom
        (firstCoordinateRestriction r θ (coordinateRatio r θ 1 2))) =
    (overlapProjectiveSectionsIso r θ).hom (overlapTransition r θ)
  rw [denominatorOverlapRestriction_is_sheaf_restriction,
    denominatorOverlapRestriction_transition]

def firstDenominatorFrame (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    (projectiveDifferentialSheaf r θ).val.obj (op (firstProjectivePatch r θ)) :=
  (projectiveDifferentialSheaf r θ).val.map
    (homOfLE (firstProjectivePatch_le_firstCoordinate r θ)).op (firstSheafFrame r θ h1 h2)

def secondDenominatorFrame (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    (projectiveDifferentialSheaf r θ).val.obj (op (secondProjectivePatch r θ)) :=
  (projectiveDifferentialSheaf r θ).val.map
    (homOfLE (secondProjectivePatch_le_secondCoordinate r θ)).op (secondSheafFrame r θ h1 h2)

private theorem overlap_le_first (r θ : ℂ) :
    overlapProjectivePatch r θ ≤ firstProjectivePatch r θ :=
  (overlapProjectivePatch_eq r θ).le.trans inf_le_left

private theorem overlap_le_second (r θ : ℂ) :
    overlapProjectivePatch r θ ≤ secondProjectivePatch r θ :=
  (overlapProjectivePatch_eq r θ).le.trans inf_le_right

set_option maxHeartbeats 400000 in
/-- The genuine differential-sheaf frames satisfy the exact gluing
equation defining the original degree-one module sheaf. -/
theorem denominator_frame_transition (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (overlap_le_second r θ)
          (secondDenominatorFrame r θ h1 h2) =
      (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) •
        restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
          (overlap_le_first r θ)
            (firstDenominatorFrame r θ h1 h2) := by
  have h := congrArg (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
      (denominatorOverlap_le_coordinateOverlap r θ))
    (sheaf_frame_transition r θ h1 h2)
  have ht : Twisted.res (projectiveCurve r θ).sheaf
      (denominatorOverlap_le_coordinateOverlap r θ) (transitionSection r θ) =
        (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) :=
    transitionSection_restrict r θ
  rw [restrict_smul, ht] at h
  change restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
      (denominatorOverlap_le_coordinateOverlap r θ)
      (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (coordinateOverlap_le_second r θ) (secondSheafFrame r θ h1 h2)) =
    (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) •
      restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (denominatorOverlap_le_coordinateOverlap r θ)
        (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
          (coordinateOverlap_le_first r θ) (firstSheafFrame r θ h1 h2)) at h
  change restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
      (overlap_le_second r θ)
      (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (secondProjectivePatch_le_secondCoordinate r θ) (secondSheafFrame r θ h1 h2)) =
    (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) •
      restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (overlap_le_first r θ)
        (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
          (firstProjectivePatch_le_firstCoordinate r θ) (firstSheafFrame r θ h1 h2))
  simpa only [restrict_comp] using h

#print axioms transitionSection_restrict
#print axioms denominator_frame_transition

end CycleQ2GeometricProjectiveFrameRestriction

end

end SourceGeometricProjectiveFrameRestriction

section SourceGeometricProjectiveChartModules

/-!
# The actual section maps of the projective affine charts

The open immersion obtained from the proved affine presentation induces
exactly the section map used to place coordinate-ring differentials in the
projective differential sheaf. Both parameters remain arbitrary throughout.
The comparison then identifies the actual sheaf-valued image of every
affine differential, including the chosen oriented residue frames.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveChartModules

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveAffine
  CycleQ2GeometricProjectiveCoefficients CycleQ2GeometricProjectiveSectionForms
  CycleQ2GeometricProjectiveAffineCoefficients CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricChartModules CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2GeometricSectionDifferentials CycleQ2GeometricAffineOverlap

section OpenChart

variable {A : Type} [CommRing A] {Y : Scheme.{0}}
  (U : Y.Opens) (e : U.toScheme ≅ Spec (CommRingCat.of A))

def chartImmersion : Spec (CommRingCat.of A) ⟶ Y := e.inv ≫ U.ι

instance : IsOpenImmersion (chartImmersion U e) := by
  unfold chartImmersion
  infer_instance

theorem chartImmersion_image_top : chartImmersion U e ''ᵁ ⊤ = U := by
  simp only [chartImmersion, Scheme.Hom.comp_image, Scheme.Hom.inv_image,
    Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top]

/-- A coordinate chart's inverse section map is the pullback through the
actual inverse isomorphism, followed by the actual restriction-top map. -/
theorem chartImmersion_appIso_inv :
    ((chartImmersion U e).appIso ⊤).inv ≫
        Y.presheaf.map (eqToHom (chartImmersion_image_top U e).symm).op =
      e.hom.appTop ≫ U.topIso.hom := by
  have hh :
      Y.presheaf.map (eqToHom (chartImmersion_image_top U e).symm).op ≫
          U.topIso.inv ≫ e.inv.appTop = ((chartImmersion U e).appIso ⊤).hom := by
    simp [chartImmersion, Scheme.Hom.comp_appIso, Scheme.Hom.appIso_hom,
      Scheme.Opens.topIso]
    rw [Scheme.Hom.app_eq e.inv (show e.inv ''ᵁ ⊤ = ⊤ by simp)]
    simp [Scheme.Opens.toScheme_presheaf_map, Category.assoc, ← Functor.map_comp]
    rw [← Category.assoc, ← Functor.map_comp]
    rfl
  apply (cancel_mono (U.topIso.inv ≫ e.inv.appTop)).mp
  rw [Category.assoc, hh, Iso.inv_hom_id]
  simp [← Scheme.Hom.comp_appTop]

end OpenChart

local instance (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Algebra ℂ Γ(projectiveCurve r θ, O) :=
  sectionAlgebra (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O

def firstChartImmersion (r θ : ℂ) :
    Spec (CommRingCat.of (FirstChartRing r θ)) ⟶ projectiveCurve r θ :=
  chartImmersion (coordinateProjectivePatch r θ 1) (firstCoordinateChartIso r θ)

def secondChartImmersion (r θ : ℂ) :
    Spec (CommRingCat.of (SecondChartRing r θ)) ⟶ projectiveCurve r θ :=
  chartImmersion (coordinateProjectivePatch r θ 2) (secondCoordinateChartIso r θ)

instance (r θ : ℂ) : IsOpenImmersion (firstChartImmersion r θ) := by
  unfold firstChartImmersion
  infer_instance

instance (r θ : ℂ) : IsOpenImmersion (secondChartImmersion r θ) := by
  unfold secondChartImmersion
  infer_instance

theorem firstChartImmersion_image_top (r θ : ℂ) :
    firstChartImmersion r θ ''ᵁ ⊤ = coordinateProjectivePatch r θ 1 :=
  chartImmersion_image_top _ _

theorem secondChartImmersion_image_top (r θ : ℂ) :
    secondChartImmersion r θ ''ᵁ ⊤ = coordinateProjectivePatch r θ 2 :=
  chartImmersion_image_top _ _

def firstSectionAlgEquiv (r θ : ℂ) :
    FirstChartRing r θ ≃ₐ[ℂ] Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1) :=
  (firstCoordinateEquiv r θ).symm.trans (coordinateSectionsAlgEquiv r θ 1).symm

def secondSectionAlgEquiv (r θ : ℂ) :
    SecondChartRing r θ ≃ₐ[ℂ] Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 2) :=
  (secondCoordinateEquiv r θ).symm.trans (coordinateSectionsAlgEquiv r θ 2).symm

theorem firstCoordinateChartIso_section_map (r θ : ℂ) :
    (Scheme.ΓSpecIso (CommRingCat.of (FirstChartRing r θ))).inv ≫
        (firstCoordinateChartIso r θ).hom.appTop ≫
          (coordinateProjectivePatch r θ 1).topIso.hom =
      CommRingCat.ofHom (firstSectionAlgEquiv r θ).toRingHom := by
  change (Scheme.ΓSpecIso (CommRingCat.of (FirstChartRing r θ))).inv ≫
      (Spec.map (CommRingCat.ofHom (firstCoordinateEquiv r θ).symm.toRingHom)).appTop ≫
      (Proj.basicOpenToSpec (curveGrade r θ) (coordinateDen r θ 1)).appTop ≫
        (coordinateProjectivePatch r θ 1).topIso.hom = _
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rw [show (Proj.basicOpenToSpec (curveGrade r θ) (coordinateDen r θ 1)).appTop =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (curveGrade r θ) (coordinateDen r θ 1) ≫
        (coordinateProjectivePatch r θ 1).topIso.inv from Proj.basicOpenToSpec_app_top _ _]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem secondCoordinateChartIso_section_map (r θ : ℂ) :
    (Scheme.ΓSpecIso (CommRingCat.of (SecondChartRing r θ))).inv ≫
        (secondCoordinateChartIso r θ).hom.appTop ≫
          (coordinateProjectivePatch r θ 2).topIso.hom =
      CommRingCat.ofHom (secondSectionAlgEquiv r θ).toRingHom := by
  change (Scheme.ΓSpecIso (CommRingCat.of (SecondChartRing r θ))).inv ≫
      (Spec.map (CommRingCat.ofHom (secondCoordinateEquiv r θ).symm.toRingHom)).appTop ≫
      (Proj.basicOpenToSpec (curveGrade r θ) (coordinateDen r θ 2)).appTop ≫
        (coordinateProjectivePatch r θ 2).topIso.hom = _
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rw [show (Proj.basicOpenToSpec (curveGrade r θ) (coordinateDen r θ 2)).appTop =
      (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection (curveGrade r θ) (coordinateDen r θ 2) ≫
        (coordinateProjectivePatch r θ 2).topIso.inv from Proj.basicOpenToSpec_app_top _ _]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

theorem firstChartImmersion_section_map (r θ : ℂ) :
    (Scheme.ΓSpecIso (CommRingCat.of (FirstChartRing r θ))).inv ≫
        ((firstChartImmersion r θ).appIso ⊤).inv ≫
          (projectiveCurve r θ).presheaf.map
            (eqToHom (firstChartImmersion_image_top r θ).symm).op =
      CommRingCat.ofHom (firstSectionAlgEquiv r θ).toRingHom := by
  have h := congrArg
    (fun f : Γ(Spec (CommRingCat.of (FirstChartRing r θ)), ⊤) ⟶
        Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1) =>
      (Scheme.ΓSpecIso (CommRingCat.of (FirstChartRing r θ))).inv ≫ f)
    (chartImmersion_appIso_inv (coordinateProjectivePatch r θ 1) (firstCoordinateChartIso r θ))
  exact h.trans (firstCoordinateChartIso_section_map r θ)

theorem secondChartImmersion_section_map (r θ : ℂ) :
    (Scheme.ΓSpecIso (CommRingCat.of (SecondChartRing r θ))).inv ≫
        ((secondChartImmersion r θ).appIso ⊤).inv ≫
          (projectiveCurve r θ).presheaf.map
            (eqToHom (secondChartImmersion_image_top r θ).symm).op =
      CommRingCat.ofHom (secondSectionAlgEquiv r θ).toRingHom := by
  have h := congrArg
    (fun f : Γ(Spec (CommRingCat.of (SecondChartRing r θ)), ⊤) ⟶
        Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 2) =>
      (Scheme.ΓSpecIso (CommRingCat.of (SecondChartRing r θ))).inv ≫ f)
    (chartImmersion_appIso_inv (coordinateProjectivePatch r θ 2) (secondCoordinateChartIso r θ))
  exact h.trans (secondCoordinateChartIso_section_map r θ)

section DifferentialComparison

variable {A : Type} [CommRing A] [Algebra ℂ A] {Y : Scheme.{0}}
  (c : ℂ →+* Γ(Y, ⊤))

theorem chart_globalKaehlerMap (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (V : Y.Opens) (hV : j ''ᵁ ⊤ = V) (hc : CoefficientCompatible j c)
    (φ : letI : Algebra ℂ Γ(Y, V) := sectionAlgebra Y.sheaf c V; A →ₐ[ℂ] Γ(Y, V))
    (hφ : ∀ a : A, Y.presheaf.map (eqToHom hV.symm).op
      ((j.appIso ⊤).inv (algebraMap A (AffineSections A ⊤) a)) = φ a)
    (ω : KaehlerDifferential ℂ A) :
    letI : Algebra ℂ Γ(Y, V) := sectionAlgebra Y.sheaf c V
    (differentialSheaf Y.sheaf c).val.map (eqToHom hV.symm).op
        (globalKaehlerMap (chartModule j (differentialSheaf Y.sheaf c))
          (chartDerivation j c (differentialSheaf Y.sheaf c)
            (universalDifferential Y.sheaf c) hc) ω) =
      toSheaf Y.sheaf c V (differentialMap φ ω) := by
  letI : Algebra ℂ Γ(Y, V) := sectionAlgebra Y.sheaf c V
  letI (O : Y.Opens) :
      Module Γ(Y, O) ((differentialSheaf Y.sheaf c).val.obj (op O)) :=
    inferInstanceAs (Module ((ringSheaf Y.sheaf).obj.obj (op O))
      ((differentialSheaf Y.sheaf c).val.obj (op O)))
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [globalKaehlerMap_D, chartDerivation_apply, differentialMap_D]
      change _ = (universalDifferential Y.sheaf c).d (X := op V) (φ a)
      exact ((universalDifferential Y.sheaf c).d_map (eqToHom hV.symm).op
        ((j.appIso ⊤).inv (algebraMap A (AffineSections A ⊤) a))).symm.trans
          (congrArg (universalDifferential Y.sheaf c).d (hφ a))
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      let G := globalKaehlerMap (chartModule j (differentialSheaf Y.sheaf c))
        (chartDerivation j c (differentialSheaf Y.sheaf c)
          (universalDifferential Y.sheaf c) hc)
      have hG : G (a • x) =
          ((j.appIso ⊤).inv (algebraMap A (AffineSections A ⊤) a)) •
            (show (differentialSheaf Y.sheaf c).val.obj (op (j ''ᵁ ⊤)) from G x) :=
        G.map_smul a x
      calc
        _ = (differentialSheaf Y.sheaf c).val.map (eqToHom hV.symm).op
            (((j.appIso ⊤).inv (algebraMap A (AffineSections A ⊤) a)) •
              (show (differentialSheaf Y.sheaf c).val.obj (op (j ''ᵁ ⊤)) from G x)) :=
          congrArg ((differentialSheaf Y.sheaf c).val.map (eqToHom hV.symm).op) hG
        _ = Y.presheaf.map (eqToHom hV.symm).op
              ((j.appIso ⊤).inv (algebraMap A (AffineSections A ⊤) a)) •
            (differentialSheaf Y.sheaf c).val.map (eqToHom hV.symm).op (G x) :=
          (differentialSheaf Y.sheaf c).val.map_smul (eqToHom hV.symm).op _ _
        _ = φ a • toSheaf Y.sheaf c V (differentialMap φ x) := by
          rw [hφ a]
          exact congrArg (fun z : (differentialSheaf Y.sheaf c).val.obj (op V) => φ a • z) hx
        _ = toSheaf Y.sheaf c V (differentialMap φ (a • x)) := by
          rw [differentialMap_smul]
          exact ((toSheaf Y.sheaf c V).map_smul (φ a) (differentialMap φ x)).symm


end DifferentialComparison

/-- Pulling an actual chart section back through the immersion recovers
the corresponding affine regular function. -/
theorem chart_sectionMap_pullback {A : Type} [CommRing A] [Algebra ℂ A]
    {Y : Scheme.{0}} (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (V : Y.Opens) (hV : j ''ᵁ ⊤ = V) (a : A) :
    j.app V (Y.presheaf.map (eqToHom hV.symm).op
      ((j.appIso ⊤).inv (algebraMap A (AffineSections A ⊤) a))) =
      algebraMap A (AffineSections A (j ⁻¹ᵁ V)) a := by
  have h : (j.appIso ⊤).inv ≫ Y.presheaf.map (eqToHom hV.symm).op ≫ j.app V =
      (Spec (CommRingCat.of A)).presheaf.map
        (homOfLE (show j ⁻¹ᵁ V ≤ ⊤ from le_top)).op := by
    rw [← j.appLE_eq_app, j.map_appLE, j.appIso_inv_appLE]
  exact congrArg (fun f : Γ(Spec (CommRingCat.of A), ⊤) ⟶
      Γ(Spec (CommRingCat.of A), j ⁻¹ᵁ V) =>
    f (algebraMap A (AffineSections A ⊤) a)) h

theorem firstChartImmersion_section_apply (r θ : ℂ) (a : FirstChartRing r θ) :
    (projectiveCurve r θ).presheaf.map
        (eqToHom (firstChartImmersion_image_top r θ).symm).op
        (((firstChartImmersion r θ).appIso ⊤).inv
          (algebraMap (FirstChartRing r θ) (AffineSections (FirstChartRing r θ) ⊤) a)) =
      firstSectionAlgEquiv r θ a :=
  congrArg (fun f : CommRingCat.of (FirstChartRing r θ) ⟶
      Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 1) => f a)
    (firstChartImmersion_section_map r θ)

theorem secondChartImmersion_section_apply (r θ : ℂ) (a : SecondChartRing r θ) :
    (projectiveCurve r θ).presheaf.map
        (eqToHom (secondChartImmersion_image_top r θ).symm).op
        (((secondChartImmersion r θ).appIso ⊤).inv
          (algebraMap (SecondChartRing r θ) (AffineSections (SecondChartRing r θ) ⊤) a)) =
      secondSectionAlgEquiv r θ a :=
  congrArg (fun f : CommRingCat.of (SecondChartRing r θ) ⟶
      Γ(projectiveCurve r θ, coordinateProjectivePatch r θ 2) => f a)
    (secondChartImmersion_section_map r θ)

theorem firstSectionAlgEquiv_pullback (r θ : ℂ) (a : FirstChartRing r θ) :
    (firstChartImmersion r θ).app (coordinateProjectivePatch r θ 1)
        (firstSectionAlgEquiv r θ a) =
      algebraMap (FirstChartRing r θ)
        (AffineSections (FirstChartRing r θ)
          (firstChartImmersion r θ ⁻¹ᵁ coordinateProjectivePatch r θ 1)) a := by
  rw [← firstChartImmersion_section_apply]
  exact chart_sectionMap_pullback _ _ (firstChartImmersion_image_top r θ) a

theorem secondSectionAlgEquiv_pullback (r θ : ℂ) (a : SecondChartRing r θ) :
    (secondChartImmersion r θ).app (coordinateProjectivePatch r θ 2)
        (secondSectionAlgEquiv r θ a) =
      algebraMap (SecondChartRing r θ)
        (AffineSections (SecondChartRing r θ)
          (secondChartImmersion r θ ⁻¹ᵁ coordinateProjectivePatch r θ 2)) a := by
  rw [← secondChartImmersion_section_apply]
  exact chart_sectionMap_pullback _ _ (secondChartImmersion_image_top r θ) a

theorem firstCoefficientCompatible (r θ : ℂ) :
    CoefficientCompatible (firstChartImmersion r θ) (projectiveGlobalCoefficient r θ) :=
  coefficientCompatible_of_overComplex _ (projectiveToComplex r θ)
    (firstCoordinateChartIso_overComplex r θ)

theorem secondCoefficientCompatible (r θ : ℂ) :
    CoefficientCompatible (secondChartImmersion r θ) (projectiveGlobalCoefficient r θ) :=
  coefficientCompatible_of_overComplex _ (projectiveToComplex r θ)
    (secondCoordinateChartIso_overComplex r θ)

theorem first_chartGlobalKaehlerMap (r θ : ℂ)
    (ω : KaehlerDifferential ℂ (FirstChartRing r θ)) :
    (projectiveDifferentialSheaf r θ).val.map
        (eqToHom (firstChartImmersion_image_top r θ).symm).op
        (globalKaehlerMap (chartModule (firstChartImmersion r θ) (projectiveDifferentialSheaf r θ))
          (chartDerivation (firstChartImmersion r θ) (projectiveGlobalCoefficient r θ)
            (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ)
            (firstCoefficientCompatible r θ)) ω) =
      toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (coordinateProjectivePatch r θ 1) (differentialMap (firstSectionAlgEquiv r θ).toAlgHom ω) :=
  chart_globalKaehlerMap (projectiveGlobalCoefficient r θ) _ _
    (firstChartImmersion_image_top r θ) (firstCoefficientCompatible r θ)
    (firstSectionAlgEquiv r θ).toAlgHom (firstChartImmersion_section_apply r θ) ω

theorem second_chartGlobalKaehlerMap (r θ : ℂ)
    (ω : KaehlerDifferential ℂ (SecondChartRing r θ)) :
    (projectiveDifferentialSheaf r θ).val.map
        (eqToHom (secondChartImmersion_image_top r θ).symm).op
        (globalKaehlerMap (chartModule (secondChartImmersion r θ) (projectiveDifferentialSheaf r θ))
          (chartDerivation (secondChartImmersion r θ) (projectiveGlobalCoefficient r θ)
            (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ)
            (secondCoefficientCompatible r θ)) ω) =
      toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (coordinateProjectivePatch r θ 2) (differentialMap (secondSectionAlgEquiv r θ).toAlgHom ω) :=
  chart_globalKaehlerMap (projectiveGlobalCoefficient r θ) _ _
    (secondChartImmersion_image_top r θ) (secondCoefficientCompatible r θ)
    (secondSectionAlgEquiv r θ).toAlgHom (secondChartImmersion_section_apply r θ) ω

/-- The first affine residue frame has the sign of the projective
adjunction transition already proved for the canonical sections. -/
def firstOrientedAffineEquiv (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (firstEquations r θ) = ⊤) :
    KaehlerDifferential ℂ (FirstChartRing r θ) ≃ₗ[FirstChartRing r θ] FirstChartRing r θ :=
  (CycleQ2GeometricChartKaehler.kaehlerResidueEquiv (firstEquations r θ) h1).trans
    (LinearEquiv.neg (FirstChartRing r θ))

def secondOrientedAffineEquiv (r θ : ℂ)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (secondEquations r θ) = ⊤) :
    KaehlerDifferential ℂ (SecondChartRing r θ) ≃ₗ[SecondChartRing r θ] SecondChartRing r θ :=
  CycleQ2GeometricChartKaehler.kaehlerResidueEquiv (secondEquations r θ) h2

theorem firstOrientedAffineEquiv_symm_one (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (firstEquations r θ) = ⊤) :
    (firstOrientedAffineEquiv r θ h1).symm 1 =
      -CycleQ2GeometricChartKaehler.globalForm (firstEquations r θ) h1 := by
  apply (firstOrientedAffineEquiv r θ h1).injective
  simp [firstOrientedAffineEquiv, CycleQ2GeometricChartKaehler.kaehlerResidueEquiv_globalForm]

theorem secondOrientedAffineEquiv_symm_one (r θ : ℂ)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (secondEquations r θ) = ⊤) :
    (secondOrientedAffineEquiv r θ h2).symm 1 =
      CycleQ2GeometricChartKaehler.globalForm (secondEquations r θ) h2 := by
  apply (secondOrientedAffineEquiv r θ h2).injective
  simp [secondOrientedAffineEquiv, CycleQ2GeometricChartKaehler.kaehlerResidueEquiv_globalForm]

theorem firstSectionForm_eq (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (secondEquations r θ) = ⊤) :
    differentialMap (firstSectionAlgEquiv r θ).toAlgHom
        ((firstOrientedAffineEquiv r θ h1).symm 1) = firstSectionForm r θ h1 h2 := by
  rw [firstOrientedAffineEquiv_symm_one]
  change differentialMap (firstSectionAlgEquiv r θ).toAlgHom _ =
    differentialMap (coordinateSectionsAlgEquiv r θ 1).symm.toAlgHom
      (differentialMap (firstCoordinateEquiv r θ).symm.toAlgHom _)
  rw [differentialMap_comp]
  rfl

theorem secondSectionForm_eq (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (secondEquations r θ) = ⊤) :
    differentialMap (secondSectionAlgEquiv r θ).toAlgHom
        ((secondOrientedAffineEquiv r θ h2).symm 1) = secondSectionForm r θ h1 h2 := by
  rw [secondOrientedAffineEquiv_symm_one]
  change differentialMap (secondSectionAlgEquiv r θ).toAlgHom _ =
    differentialMap (coordinateSectionsAlgEquiv r θ 2).symm.toAlgHom
      (differentialMap (secondCoordinateEquiv r θ).symm.toAlgHom _)
  rw [differentialMap_comp]
  rfl

/-- The generic affine sheaf construction produces exactly the existing
first projective frame, on the actual coordinate open. -/
theorem first_chartFrame_eq_sheafFrame (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (secondEquations r θ) = ⊤) :
    (projectiveDifferentialSheaf r θ).val.map
        (eqToHom (firstChartImmersion_image_top r θ).symm).op
        (chartFrame (firstChartImmersion r θ) (projectiveGlobalCoefficient r θ)
          (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ)
          (firstCoefficientCompatible r θ) (firstOrientedAffineEquiv r θ h1)) =
      firstSheafFrame r θ h1 h2 := by
  unfold chartFrame
  rw [first_chartGlobalKaehlerMap, firstSectionForm_eq r θ h1 h2]
  rfl

/-- The same comparison holds on the second actual coordinate open. -/
theorem second_chartFrame_eq_sheafFrame (r θ : ℂ)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (secondEquations r θ) = ⊤) :
    (projectiveDifferentialSheaf r θ).val.map
        (eqToHom (secondChartImmersion_image_top r θ).symm).op
        (chartFrame (secondChartImmersion r θ) (projectiveGlobalCoefficient r θ)
          (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ)
          (secondCoefficientCompatible r θ) (secondOrientedAffineEquiv r θ h2)) =
      secondSheafFrame r θ h1 h2 := by
  unfold chartFrame
  rw [second_chartGlobalKaehlerMap, secondSectionForm_eq r θ h1 h2]
  rfl

#print axioms first_chartFrame_eq_sheafFrame
#print axioms second_chartFrame_eq_sheafFrame

#print axioms firstChartImmersion_section_map
#print axioms secondChartImmersion_section_map

end CycleQ2GeometricProjectiveChartModules
end

end SourceGeometricProjectiveChartModules

section SourceGeometricCanonicalSheaf

/-!
# The canonical comparison morphism on the actual projective curve

The two normalized differential-sheaf sections glue to a genuine morphism
from the existing degree-one module sheaf to the existing differential
sheaf. The source is exactly the sheaf used by the Cech and projective
cohomology constructions. The two local formulas retain the original
trivializations, with no assumed sheaf comparison map.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricCanonicalSheaf

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricProjectiveFrameRestriction CycleQ2GeometricTwistedFrameMap

local instance (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Module Γ(projectiveCurve r θ, O)
      ((projectiveDifferentialSheaf r θ).val.obj (op O)) :=
  inferInstanceAs (Module ((ringSheaf (projectiveCurve r θ).sheaf).obj.obj (op O))
    ((projectiveDifferentialSheaf r θ).val.obj (op O)))

/-- The actual comparison from the original degree-one module sheaf to
the genuine sheaf of complex differentials. -/
def canonicalSheafMap (r θ : ℂ) (hr : r ≠ 0)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤) :
    degreeOneModuleSheaf r θ ⟶ projectiveDifferentialSheaf r θ :=
  frameMorphism (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (projective_twoOpen_cover r θ hr)
    (firstDenominatorFrame r θ h1 h2) (secondDenominatorFrame r θ h1 h2)
    (denominator_frame_transition r θ h1 h2)

theorem canonicalSheafMap_first_local (r θ : ℂ) (hr : r ≠ 0)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤)
    (O : (projectiveCurve r θ).Opens) (hO : O ≤ firstProjectivePatch r θ)
    (s : (degreeOneModuleSheaf r θ).val.obj (op O)) :
    (canonicalSheafMap r θ hr h1 h2).val.app (op O) s =
      Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
        (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
        (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO s •
      (projectiveDifferentialSheaf r θ).val.map (homOfLE hO).op (firstDenominatorFrame r θ h1 h2) :=
  frameMorphism_first_local (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (projective_twoOpen_cover r θ hr)
    (firstDenominatorFrame r θ h1 h2) (secondDenominatorFrame r θ h1 h2)
    (denominator_frame_transition r θ h1 h2) O hO s

theorem canonicalSheafMap_second_local (r θ : ℂ) (hr : r ≠ 0)
    (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.firstEquations r θ) = ⊤)
    (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal
      (CycleQ2GeometricAffineOverlap.secondEquations r θ) = ⊤)
    (O : (projectiveCurve r θ).Opens) (hO : O ≤ secondProjectivePatch r θ)
    (s : (degreeOneModuleSheaf r θ).val.obj (op O)) :
    (canonicalSheafMap r θ hr h1 h2).val.app (op O) s =
      Twisted.secondLocalSectionsEquiv (projectiveCurve r θ).sheaf
        (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
        (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO s •
      (projectiveDifferentialSheaf r θ).val.map (homOfLE hO).op (secondDenominatorFrame r θ h1 h2) :=
  frameMorphism_second_local (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (projective_twoOpen_cover r θ hr)
    (firstDenominatorFrame r θ h1 h2) (secondDenominatorFrame r θ h1 h2)
    (denominator_frame_transition r θ h1 h2) O hO s

/-- The canonical comparison on the same literal incidence curve whose
degree-one Cech class and normal trace have been proved nonzero. The two
Jacobian hypotheses of the generic construction are discharged by exact
polynomial identities on this member. -/
def incidenceCanonicalSheafMap :
    degreeOneModuleSheaf 57 1 ⟶ projectiveDifferentialSheaf 57 1 :=
  canonicalSheafMap 57 1 (by norm_num)
    CycleQ2GeometricIncidenceJacobianCover.first_chart_jacobianIdeal_eq_top
    CycleQ2GeometricIncidenceJacobianCover.second_chart_jacobianIdeal_eq_top


open CycleQ2GeometricProjectiveChartModules CycleQ2GeometricChartCoefficient
  CycleQ2GeometricChartModules CycleQ2GeometricChartDerivation
  CycleQ2GeometricProjectiveSectionForms CycleQ2GeometricProjectiveAffine
  CycleQ2GeometricProjectiveAffineCoefficients CycleQ2GeometricSectionDifferentials
  CycleQ2GeometricTwistedDifferential CycleQ2GeometricTwistedDifferentialIso
  CycleQ2GeometricAffineOverlap

local instance (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Algebra ℂ Γ(projectiveCurve r θ, O) :=
  sectionAlgebra (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O

theorem firstCoordinate_le_range (r θ : ℂ) :
    coordinateProjectivePatch r θ 1 ≤ (firstChartImmersion r θ).opensRange := by
  rw [← (firstChartImmersion r θ).image_top_eq_opensRange,
    firstChartImmersion_image_top]

theorem secondCoordinate_le_range (r θ : ℂ) :
    coordinateProjectivePatch r θ 2 ≤ (secondChartImmersion r θ).opensRange := by
  rw [← (secondChartImmersion r θ).image_top_eq_opensRange,
    secondChartImmersion_image_top]

theorem firstDenominator_le_range (r θ : ℂ) :
    firstProjectivePatch r θ ≤ (firstChartImmersion r θ).opensRange :=
  (firstProjectivePatch_le_firstCoordinate r θ).trans (firstCoordinate_le_range r θ)

theorem secondDenominator_le_range (r θ : ℂ) :
    secondProjectivePatch r θ ≤ (secondChartImmersion r θ).opensRange :=
  (secondProjectivePatch_le_secondCoordinate r θ).trans (secondCoordinate_le_range r θ)

theorem firstTopCoefficients (r θ : ℂ) (z : ℂ) :
    (firstChartImmersion r θ).appTop (projectiveGlobalCoefficient r θ z) =
      algebraMap (FirstChartRing r θ)
        (CycleQ2GeometricAffineDifferentialSheaf.AffineSections (FirstChartRing r θ) ⊤)
        (algebraMap ℂ (FirstChartRing r θ) z) :=
  coefficients_appTop_of_overComplex (firstChartImmersion r θ) (projectiveToComplex r θ)
    (firstCoordinateChartIso_overComplex r θ) z

theorem secondTopCoefficients (r θ : ℂ) (z : ℂ) :
    (secondChartImmersion r θ).appTop (projectiveGlobalCoefficient r θ z) =
      algebraMap (SecondChartRing r θ)
        (CycleQ2GeometricAffineDifferentialSheaf.AffineSections (SecondChartRing r θ) ⊤)
        (algebraMap ℂ (SecondChartRing r θ) z) :=
  coefficients_appTop_of_overComplex (secondChartImmersion r θ) (projectiveToComplex r θ)
    (secondCoordinateChartIso_overComplex r θ) z

section SmoothFrames

variable (r θ : ℂ)
  (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (firstEquations r θ) = ⊤)
  (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (secondEquations r θ) = ⊤)

def firstCanonicalCoefficient : LocalCoefficient (projectiveCurve r θ).sheaf
    (projectiveGlobalCoefficient r θ) (firstProjectivePatch r θ) :=
  chartLocalCoefficient (firstChartImmersion r θ) (projectiveGlobalCoefficient r θ)
    (firstTopCoefficients r θ) (firstOrientedAffineEquiv r θ h1)
    (firstProjectivePatch r θ) (firstDenominator_le_range r θ)

def secondCanonicalCoefficient : LocalCoefficient (projectiveCurve r θ).sheaf
    (projectiveGlobalCoefficient r θ) (secondProjectivePatch r θ) :=
  chartLocalCoefficient (secondChartImmersion r θ) (projectiveGlobalCoefficient r θ)
    (secondTopCoefficients r θ) (secondOrientedAffineEquiv r θ h2)
    (secondProjectivePatch r θ) (secondDenominator_le_range r θ)

theorem first_rangeFrame_restrict (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ firstProjectivePatch r θ) :
    restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (hO.trans (firstDenominator_le_range r θ))
        (chartRangeFrame (firstChartImmersion r θ) (projectiveGlobalCoefficient r θ)
          (firstOrientedAffineEquiv r θ h1) (projectiveDifferentialSheaf r θ)
          (projectiveUniversalDifferential r θ) (firstCoefficientCompatible r θ)) =
      restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ) hO
        (firstDenominatorFrame r θ h1 h2) := by
  rw [firstDenominatorFrame, ← first_chartFrame_eq_sheafFrame r θ h1 h2]
  let η := chartFrame (firstChartImmersion r θ) (projectiveGlobalCoefficient r θ)
    (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ)
    (firstCoefficientCompatible r θ) (firstOrientedAffineEquiv r θ h1)
  change restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
      (hO.trans (firstDenominator_le_range r θ))
      (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (firstChartImmersion r θ).image_top_eq_opensRange.ge η) =
    restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ) hO
      (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (firstProjectivePatch_le_firstCoordinate r θ)
        (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
          (firstChartImmersion_image_top r θ).ge η))
  rw [restrict_comp, restrict_comp, restrict_comp]

theorem second_rangeFrame_restrict (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ secondProjectivePatch r θ) :
    restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (hO.trans (secondDenominator_le_range r θ))
        (chartRangeFrame (secondChartImmersion r θ) (projectiveGlobalCoefficient r θ)
          (secondOrientedAffineEquiv r θ h2) (projectiveDifferentialSheaf r θ)
          (projectiveUniversalDifferential r θ) (secondCoefficientCompatible r θ)) =
      restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ) hO
        (secondDenominatorFrame r θ h1 h2) := by
  rw [secondDenominatorFrame, ← second_chartFrame_eq_sheafFrame r θ h1 h2]
  let η := chartFrame (secondChartImmersion r θ) (projectiveGlobalCoefficient r θ)
    (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ)
    (secondCoefficientCompatible r θ) (secondOrientedAffineEquiv r θ h2)
  change restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
      (hO.trans (secondDenominator_le_range r θ))
      (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (secondChartImmersion r θ).image_top_eq_opensRange.ge η) =
    restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ) hO
      (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (secondProjectivePatch_le_secondCoordinate r θ)
        (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
          (secondChartImmersion_image_top r θ).ge η))
  rw [restrict_comp, restrict_comp, restrict_comp]

theorem first_differential_reconstruction (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ firstProjectivePatch r θ) (a : Γ(projectiveCurve r θ, O)) :
    (projectiveUniversalDifferential r θ).d a =
      (firstCanonicalCoefficient r θ h1).app O hO a •
        restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ) hO
          (firstDenominatorFrame r θ h1 h2) := by
  have h := chartDerivation_factorization_subopen (firstChartImmersion r θ)
    (projectiveGlobalCoefficient r θ) (firstOrientedAffineEquiv r θ h1)
    (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ)
    (firstCoefficientCompatible r θ) O (hO.trans (firstDenominator_le_range r θ)) a
  rw [first_rangeFrame_restrict r θ h1 h2] at h
  exact h

theorem second_differential_reconstruction (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ secondProjectivePatch r θ) (a : Γ(projectiveCurve r θ, O)) :
    (projectiveUniversalDifferential r θ).d a =
      (secondCanonicalCoefficient r θ h2).app O hO a •
        restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ) hO
          (secondDenominatorFrame r θ h1 h2) := by
  have h := chartDerivation_factorization_subopen (secondChartImmersion r θ)
    (projectiveGlobalCoefficient r θ) (secondOrientedAffineEquiv r θ h2)
    (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ)
    (secondCoefficientCompatible r θ) O (hO.trans (secondDenominator_le_range r θ)) a
  rw [second_rangeFrame_restrict r θ h1 h2] at h
  exact h

def firstCoefficientMap (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ firstProjectivePatch r θ) :
    (projectiveDifferentialSheaf r θ).val.obj (op O) →ₗ[Γ(projectiveCurve r θ, O)]
      Γ(projectiveCurve r θ, O) :=
  localCoefficientMap (firstChartImmersion r θ) (projectiveGlobalCoefficient r θ)
    (firstTopCoefficients r θ) (firstOrientedAffineEquiv r θ h1) O
    (hO.trans (firstDenominator_le_range r θ))

def secondCoefficientMap (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ secondProjectivePatch r θ) :
    (projectiveDifferentialSheaf r θ).val.obj (op O) →ₗ[Γ(projectiveCurve r θ, O)]
      Γ(projectiveCurve r θ, O) :=
  localCoefficientMap (secondChartImmersion r θ) (projectiveGlobalCoefficient r θ)
    (secondTopCoefficients r θ) (secondOrientedAffineEquiv r θ h2) O
    (hO.trans (secondDenominator_le_range r θ))

theorem firstCoefficientMap_frame (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ firstProjectivePatch r θ) :
    firstCoefficientMap r θ h1 O hO
      (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ) hO
        (firstDenominatorFrame r θ h1 h2)) = 1 := by
  have hnorm := localCoefficientMap_normalized_frame (firstChartImmersion r θ)
    (projectiveGlobalCoefficient r θ) (firstTopCoefficients r θ)
    (firstOrientedAffineEquiv r θ h1) (coordinateProjectivePatch r θ 1)
    (firstCoordinate_le_range r θ) (firstSectionAlgEquiv r θ).toAlgHom
    (firstSectionAlgEquiv_pullback r θ)
  have hnormFrame : localCoefficientMap (firstChartImmersion r θ)
      (projectiveGlobalCoefficient r θ) (firstTopCoefficients r θ)
      (firstOrientedAffineEquiv r θ h1) (coordinateProjectivePatch r θ 1)
      (firstCoordinate_le_range r θ) (firstSheafFrame r θ h1 h2) = 1 :=
    (congrArg (fun ω : SectionForms (projectiveCurve r θ).sheaf
        (projectiveGlobalCoefficient r θ) (coordinateProjectivePatch r θ 1) =>
      localCoefficientMap (firstChartImmersion r θ) (projectiveGlobalCoefficient r θ)
        (firstTopCoefficients r θ) (firstOrientedAffineEquiv r θ h1)
        (coordinateProjectivePatch r θ 1) (firstCoordinate_le_range r θ)
        (toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
          (coordinateProjectivePatch r θ 1) ω))
      (firstSectionForm_eq r θ h1 h2)).symm.trans hnorm
  have hres := localCoefficientMap_restrict (firstChartImmersion r θ)
    (projectiveGlobalCoefficient r θ) (firstTopCoefficients r θ)
    (firstOrientedAffineEquiv r θ h1)
    (hO.trans (firstProjectivePatch_le_firstCoordinate r θ))
    (firstCoordinate_le_range r θ) (hO.trans (firstDenominator_le_range r θ))
    (firstSheafFrame r θ h1 h2)
  rw [hnormFrame, map_one] at hres
  change localCoefficientMap (firstChartImmersion r θ) (projectiveGlobalCoefficient r θ)
    (firstTopCoefficients r θ) (firstOrientedAffineEquiv r θ h1) O
    (hO.trans (firstDenominator_le_range r θ))
    (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ) hO
      (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (firstProjectivePatch_le_firstCoordinate r θ) (firstSheafFrame r θ h1 h2))) = 1
  rw [restrict_comp]
  exact hres

theorem secondCoefficientMap_frame (O : (projectiveCurve r θ).Opens)
    (hO : O ≤ secondProjectivePatch r θ) :
    secondCoefficientMap r θ h2 O hO
      (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ) hO
        (secondDenominatorFrame r θ h1 h2)) = 1 := by
  have hnorm := localCoefficientMap_normalized_frame (secondChartImmersion r θ)
    (projectiveGlobalCoefficient r θ) (secondTopCoefficients r θ)
    (secondOrientedAffineEquiv r θ h2) (coordinateProjectivePatch r θ 2)
    (secondCoordinate_le_range r θ) (secondSectionAlgEquiv r θ).toAlgHom
    (secondSectionAlgEquiv_pullback r θ)
  have hnormFrame : localCoefficientMap (secondChartImmersion r θ)
      (projectiveGlobalCoefficient r θ) (secondTopCoefficients r θ)
      (secondOrientedAffineEquiv r θ h2) (coordinateProjectivePatch r θ 2)
      (secondCoordinate_le_range r θ) (secondSheafFrame r θ h1 h2) = 1 :=
    (congrArg (fun ω : SectionForms (projectiveCurve r θ).sheaf
        (projectiveGlobalCoefficient r θ) (coordinateProjectivePatch r θ 2) =>
      localCoefficientMap (secondChartImmersion r θ) (projectiveGlobalCoefficient r θ)
        (secondTopCoefficients r θ) (secondOrientedAffineEquiv r θ h2)
        (coordinateProjectivePatch r θ 2) (secondCoordinate_le_range r θ)
        (toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
          (coordinateProjectivePatch r θ 2) ω))
      (secondSectionForm_eq r θ h1 h2)).symm.trans hnorm
  have hres := localCoefficientMap_restrict (secondChartImmersion r θ)
    (projectiveGlobalCoefficient r θ) (secondTopCoefficients r θ)
    (secondOrientedAffineEquiv r θ h2)
    (hO.trans (secondProjectivePatch_le_secondCoordinate r θ))
    (secondCoordinate_le_range r θ) (hO.trans (secondDenominator_le_range r θ))
    (secondSheafFrame r θ h1 h2)
  rw [hnormFrame, map_one] at hres
  change localCoefficientMap (secondChartImmersion r θ) (projectiveGlobalCoefficient r θ)
    (secondTopCoefficients r θ) (secondOrientedAffineEquiv r θ h2) O
    (hO.trans (secondDenominator_le_range r θ))
    (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ) hO
      (restrict (projectiveCurve r θ).sheaf (projectiveDifferentialSheaf r θ)
        (secondProjectivePatch_le_secondCoordinate r θ) (secondSheafFrame r θ h1 h2))) = 1
  rw [restrict_comp]
  exact hres

end SmoothFrames


local instance (r θ : ℂ) (O : (projectiveCurve r θ).Opens) :
    Module Γ(projectiveCurve r θ, O)
      ((degreeOneModuleSheaf r θ).val.obj (op O)) :=
  inferInstanceAs (Module
    ((TwistedModule.ringSheaf (projectiveCurve r θ).sheaf).obj.obj (op O))
      ((degreeOneModuleSheaf r θ).val.obj (op O)))

section SmoothFrames

variable (r θ : ℂ)
  (h1 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (firstEquations r θ) = ⊤)
  (h2 : CycleQ2GeometricSparseJacobianCover.jacobianIdeal (secondEquations r θ) = ⊤)

/-- The two independently constructed actual coefficient derivations have
exactly the transition of the original degree-one module sheaf. -/
theorem canonicalCoefficients_compatible :
    Compatible (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
      (firstCanonicalCoefficient r θ h1) (secondCanonicalCoefficient r θ h2) := by
  refine coefficients_compatible_of_frame
    (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (firstCanonicalCoefficient r θ h1) (secondCanonicalCoefficient r θ h2)
    (projectiveDifferentialSheaf r θ) (projectiveUniversalDifferential r θ)
    (firstDenominatorFrame r θ h1 h2) (secondDenominatorFrame r θ h1 h2)
    (denominator_frame_transition r θ h1 h2)
    (second_differential_reconstruction r θ h1 h2)
    (firstCoefficientMap r θ h1) ?_ (firstCoefficientMap_frame r θ h1 h2)
  intro O hO a
  exact localCoefficientMap_D (firstChartImmersion r θ) (projectiveGlobalCoefficient r θ)
    (firstTopCoefficients r θ) (firstOrientedAffineEquiv r θ h1) O
    (hO.trans (firstDenominator_le_range r θ)) a

/-- The actual differential universal property now gives the coefficient
morphism into the original degree-one module sheaf. -/
def canonicalCoefficientMorphism :
    projectiveDifferentialSheaf r θ ⟶ degreeOneModuleSheaf r θ :=
  coefficientMorphism (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (firstCanonicalCoefficient r θ h1) (secondCanonicalCoefficient r θ h2)
    (canonicalCoefficients_compatible r θ h1 h2)

/-- On finite sectionwise forms, the first coordinate of the glued map
agrees with the independent actual affine coefficient map. -/
theorem canonicalCoefficientMorphism_first_on_form
    (O : (projectiveCurve r θ).Opens) (hO : O ≤ firstProjectivePatch r θ)
    (ω : SectionForms (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O) :
    Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
      ((canonicalCoefficientMorphism r θ h1 h2).val.app (op O)
        (toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O ω)) =
      firstCoefficientMap r θ h1 O hO
        (toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O ω) := by
  let f : (projectiveDifferentialSheaf r θ).val.obj (op O) →ₗ[Γ(projectiveCurve r θ, O)]
      Γ(projectiveCurve r θ, O) :=
    (TwistedModule.firstLocalSectionsLinearEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO).toLinearMap.comp
        ((canonicalCoefficientMorphism r θ h1 h2).val.app (op O)).hom
  have hf (a : Γ(projectiveCurve r θ, O)) :
      f ((projectiveUniversalDifferential r θ).d a) =
        chartDerivative (firstChartImmersion r θ) (firstOrientedAffineEquiv r θ h1) O
          (hO.trans (firstDenominator_le_range r θ)) a :=
    coefficientMorphism_D_first (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
      (firstCanonicalCoefficient r θ h1) (secondCanonicalCoefficient r θ h2)
      (canonicalCoefficients_compatible r θ h1 h2) O hO a
  exact localCoefficientMap_compare_on_forms (firstChartImmersion r θ)
    (projectiveGlobalCoefficient r θ) (firstTopCoefficients r θ)
    (firstOrientedAffineEquiv r θ h1) O (hO.trans (firstDenominator_le_range r θ)) f hf ω

theorem canonicalCoefficientMorphism_second_on_form
    (O : (projectiveCurve r θ).Opens) (hO : O ≤ secondProjectivePatch r θ)
    (ω : SectionForms (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O) :
    Twisted.secondLocalSectionsEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
      ((canonicalCoefficientMorphism r θ h1 h2).val.app (op O)
        (toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O ω)) =
      secondCoefficientMap r θ h2 O hO
        (toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ) O ω) := by
  let f : (projectiveDifferentialSheaf r θ).val.obj (op O) →ₗ[Γ(projectiveCurve r θ, O)]
      Γ(projectiveCurve r θ, O) :=
    (TwistedModule.secondLocalSectionsLinearEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO).toLinearMap.comp
        ((canonicalCoefficientMorphism r θ h1 h2).val.app (op O)).hom
  have hf (a : Γ(projectiveCurve r θ, O)) :
      f ((projectiveUniversalDifferential r θ).d a) =
        chartDerivative (secondChartImmersion r θ) (secondOrientedAffineEquiv r θ h2) O
          (hO.trans (secondDenominator_le_range r θ)) a :=
    coefficientMorphism_D_second (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
      (firstCanonicalCoefficient r θ h1) (secondCanonicalCoefficient r θ h2)
      (canonicalCoefficients_compatible r θ h1 h2) O hO a
  exact localCoefficientMap_compare_on_forms (secondChartImmersion r θ)
    (projectiveGlobalCoefficient r θ) (secondTopCoefficients r θ)
    (secondOrientedAffineEquiv r θ h2) O (hO.trans (secondDenominator_le_range r θ)) f hf ω

/-- The first actual denominator frame is normalized by the glued
coefficient map, as proved on its finite sectionwise representative. -/
theorem canonicalCoefficientMorphism_first_frame :
    Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
      (firstProjectivePatch r θ) le_rfl
      ((canonicalCoefficientMorphism r θ h1 h2).val.app (op (firstProjectivePatch r θ))
        (firstDenominatorFrame r θ h1 h2)) = 1 := by
  letI := sectionAlgebra (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (coordinateProjectivePatch r θ 1)
  letI := sectionAlgebra (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (firstProjectivePatch r θ)
  let ω : SectionForms (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (firstProjectivePatch r θ) :=
    differentialMap (sectionRestriction (projectiveCurve r θ).sheaf
      (projectiveGlobalCoefficient r θ) (firstProjectivePatch_le_firstCoordinate r θ))
        (firstSectionForm r θ h1 h2)
  have hs : firstDenominatorFrame r θ h1 h2 =
      toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (firstProjectivePatch r θ) ω :=
    toSheaf_restrict (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (firstProjectivePatch_le_firstCoordinate r θ) (firstSectionForm r θ h1 h2)
  have hf := canonicalCoefficientMorphism_first_on_form r θ h1 h2
    (firstProjectivePatch r θ) le_rfl ω
  rw [← hs] at hf
  exact hf.trans (by simpa only [restrict_self] using
    firstCoefficientMap_frame r θ h1 h2 (firstProjectivePatch r θ) le_rfl)

theorem canonicalCoefficientMorphism_second_frame :
    Twisted.secondLocalSectionsEquiv (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
      (secondProjectivePatch r θ) le_rfl
      ((canonicalCoefficientMorphism r θ h1 h2).val.app (op (secondProjectivePatch r θ))
        (secondDenominatorFrame r θ h1 h2)) = 1 := by
  letI := sectionAlgebra (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (coordinateProjectivePatch r θ 2)
  letI := sectionAlgebra (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (secondProjectivePatch r θ)
  let ω : SectionForms (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (secondProjectivePatch r θ) :=
    differentialMap (sectionRestriction (projectiveCurve r θ).sheaf
      (projectiveGlobalCoefficient r θ) (secondProjectivePatch_le_secondCoordinate r θ))
        (secondSectionForm r θ h1 h2)
  have hs : secondDenominatorFrame r θ h1 h2 =
      toSheaf (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (secondProjectivePatch r θ) ω :=
    toSheaf_restrict (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (secondProjectivePatch_le_secondCoordinate r θ) (secondSectionForm r θ h1 h2)
  have hf := canonicalCoefficientMorphism_second_on_form r θ h1 h2
    (secondProjectivePatch r θ) le_rfl ω
  rw [← hs] at hf
  exact hf.trans (by simpa only [restrict_self] using
    secondCoefficientMap_frame r θ h1 h2 (secondProjectivePatch r θ) le_rfl)

/-- The original degree-one module sheaf is the actual sheaf of complex
differentials on the literal smooth projective curve. Both morphisms and
both inverse identities are supplied by the proved local constructions. -/
def canonicalSheafIso (hr : r ≠ 0) :
    degreeOneModuleSheaf r θ ≅ projectiveDifferentialSheaf r θ :=
  (differentialTwistedIso (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (projective_twoOpen_cover r θ hr)
    (firstCanonicalCoefficient r θ h1) (secondCanonicalCoefficient r θ h2)
    (canonicalCoefficients_compatible r θ h1 h2)
    (firstDenominatorFrame r θ h1 h2) (secondDenominatorFrame r θ h1 h2)
    (denominator_frame_transition r θ h1 h2)
    (first_differential_reconstruction r θ h1 h2)
    (second_differential_reconstruction r θ h1 h2)
    (canonicalCoefficientMorphism_first_frame r θ h1 h2)
    (canonicalCoefficientMorphism_second_frame r θ h1 h2)).symm

@[simp] theorem canonicalSheafIso_hom (hr : r ≠ 0) :
    (canonicalSheafIso r θ h1 h2 hr).hom = canonicalSheafMap r θ hr h1 h2 := rfl

@[simp] theorem canonicalSheafIso_inv (hr : r ≠ 0) :
    (canonicalSheafIso r θ h1 h2 hr).inv = canonicalCoefficientMorphism r θ h1 h2 := rfl

end SmoothFrames

/-- The canonical comparison is an actual sheaf isomorphism on the
specific incidence member used by the nonzero Cech and trace constructions. -/
def incidenceCanonicalSheafIso :
    degreeOneModuleSheaf 57 1 ≅ projectiveDifferentialSheaf 57 1 :=
  canonicalSheafIso 57 1
    CycleQ2GeometricIncidenceJacobianCover.first_chart_jacobianIdeal_eq_top
    CycleQ2GeometricIncidenceJacobianCover.second_chart_jacobianIdeal_eq_top
    (by norm_num)

#print axioms canonicalCoefficients_compatible
#print axioms canonicalCoefficientMorphism
#print axioms canonicalSheafIso
#print axioms incidenceCanonicalSheafIso

#print axioms canonicalSheafMap
#print axioms canonicalSheafMap_first_local
#print axioms incidenceCanonicalSheafMap

end CycleQ2GeometricCanonicalSheaf

end

end SourceGeometricCanonicalSheaf

section SourceGeometricIncidenceCanonicalH1

/-!
# The incidence canonical comparison in genuine derived cohomology

The proved canonical sheaf isomorphism on the actual member `(r, θ) = (57, 1)`
transports the existing Mayer–Vietoris injection into the derived first
cohomology of the actual differential sheaf. The zero criterion below refers
to the original Cech quotient and requires no new nonvanishing assumption.

The fixed incidence normalization survives in this derived group. The original
paired normal class has zero image exactly when its computed derivative
coordinate vanishes.

-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricCanonicalSheaf

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveCanonicalH1

local instance incidenceSheavesHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve 57 1))
      AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Forgetting the module structure of the proved incidence canonical
comparison gives this actual additive-sheaf isomorphism. -/
def incidenceCanonicalAdditiveIso :
    degreeOneSheaf 57 1 ≅ differentialAdditiveSheaf 57 1 :=
  (SheafOfModules.toSheaf (ringSheaf (projectiveCurve 57 1).sheaf)).mapIso
    incidenceCanonicalSheafIso

/-- The derived cohomology equivalence is induced by the actual sheaf
isomorphism on the same incidence curve. -/
def incidenceCanonicalH1Equiv :
    ProjectiveSheafH1 57 1 ≃+ DifferentialSheafH1 57 1 :=
  (((Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology (projectiveCurve 57 1)) 1).mapIso
        incidenceCanonicalAdditiveIso).app (op ⊤)).addCommGroupIsoToAddEquiv

/-- The original incidence Cech quotient maps to actual derived first
cohomology of the canonical differential sheaf. -/
def incidenceDegreeOneToCanonicalH1 :
    DegreeOneCech 57 1 →+ DifferentialSheafH1 57 1 :=
  incidenceCanonicalH1Equiv.toAddMonoidHom.comp
    (degreeOneToProjectiveH1 57 1 (by norm_num))

theorem incidenceDegreeOneToCanonicalH1_injective :
    Function.Injective incidenceDegreeOneToCanonicalH1 :=
  incidenceCanonicalH1Equiv.injective.comp
    (degreeOneToProjectiveH1_injective 57 1 (by norm_num))

@[simp] theorem incidenceDegreeOneToCanonicalH1_eq_zero_iff
    (ξ : DegreeOneCech 57 1) :
    incidenceDegreeOneToCanonicalH1 ξ = 0 ↔ ξ = 0 := by
  constructor
  · intro h
    apply incidenceDegreeOneToCanonicalH1_injective
    simpa only [map_zero] using h
  · rintro rfl
    exact map_zero _

/-- The literal incidence normalization, mapped into derived cohomology
of the actual canonical differential sheaf. -/
def incidenceNormalizationCanonicalClass : DifferentialSheafH1 57 1 :=
  incidenceDegreeOneToCanonicalH1
    CycleQ2GeometricIncidenceCechSurjectivity.incidenceCechNormalization

theorem incidenceNormalizationCanonicalClass_ne_zero :
    incidenceNormalizationCanonicalClass ≠ 0 := by
  intro h
  exact CycleQ2GeometricIncidenceCechTrace.incidenceCechNormalization_ne_zero
    ((incidenceDegreeOneToCanonicalH1_eq_zero_iff
      CycleQ2GeometricIncidenceCechSurjectivity.incidenceCechNormalization).mp h)

/-- The actual differential sheaf on the incidence member has nontrivial
derived first cohomology. -/
theorem incidenceDifferentialSheafH1_nontrivial :
    Nontrivial (DifferentialSheafH1 57 1) :=
  ⟨⟨incidenceNormalizationCanonicalClass, 0,
    incidenceNormalizationCanonicalClass_ne_zero⟩⟩

/-- The original paired normal class, transported through the proved
Mayer–Vietoris injection and canonical sheaf comparison. -/
def incidencePairedCanonicalClass (v : Fin 9 → ℂ) : DifferentialSheafH1 57 1 :=
  incidenceDegreeOneToCanonicalH1 (pairedDegreeOneClass 57 1 v)

/-- The computed derivative row detects vanishing of the original paired
class in the genuine derived cohomology of the actual differential sheaf. -/
theorem incidencePairedCanonicalClass_eq_zero_iff_derivativeTrace_zero
    (v : Fin 9 → ℂ) :
    incidencePairedCanonicalClass v = 0 ↔
      CycleQ2SeedCechTheta.derivativeTrace 1 v = 0 := by
  exact (incidenceDegreeOneToCanonicalH1_eq_zero_iff
    (pairedDegreeOneClass 57 1 v)).trans
      (CycleQ2GeometricIncidenceCechTrace.pairedDegreeOneClass_eq_zero_iff_derivativeTrace_zero v)

#print axioms incidenceCanonicalH1Equiv
#print axioms incidenceDegreeOneToCanonicalH1_injective
#print axioms incidenceDegreeOneToCanonicalH1_eq_zero_iff
#print axioms incidenceNormalizationCanonicalClass_ne_zero
#print axioms incidenceDifferentialSheafH1_nontrivial
#print axioms incidencePairedCanonicalClass_eq_zero_iff_derivativeTrace_zero

end CycleQ2GeometricCanonicalSheaf

end

end SourceGeometricIncidenceCanonicalH1
