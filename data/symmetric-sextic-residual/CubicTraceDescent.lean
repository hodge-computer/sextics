import Proposal.CubicSourceReconstruction
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace

/-!
# Two scalar trace identities suffice for the cubic residue source

An already constructed upstairs current can be descended by taking the
finite normalized trace of each component.  For a cubic residue written
using a linear source, the exact source comparison reduces to the traces
of its two coefficients.  The comparison hypotheses remain explicit.

The final identity rewrites the concrete lower-pole residual `2*delta/f_u`
in this same two-coefficient language.  It does not assert the existence
of a current realizing those coefficient traces.
-/

noncomputable section

namespace CubicTraceDescent

open CubicSourceReconstruction HoldoutConstruction
open scoped BigOperators

variable {K : Type*} [Field K]

def linearDensity (g gu u s0 s1 : K) : K :=
  2*(g*s1-gu*(s0+s1*u))/g^3

theorem linearDensity_coefficients (g gu u s0 s1 : K) :
    linearDensity g gu u s0 s1 =
      (-2*gu/g^3)*s0+(2*(g-gu*u)/g^3)*s1 := by
  simp only [linearDensity, div_eq_mul_inv]
  ring

section FiniteTrace

variable {L ι : Type*} [CharZero K] [Field L]
variable [Algebra K L] [FiniteDimensional K L] [Fintype ι]

theorem finiteTrace_linearDensity (g gu u : K) (s0 s1 : L) :
    Algebra.normalizedTrace K L
      (linearDensity (algebraMap K L g) (algebraMap K L gu)
        (algebraMap K L u) s0 s1) =
      linearDensity g gu u (Algebra.normalizedTrace K L s0)
        (Algebra.normalizedTrace K L s1) := by
  have h : linearDensity (algebraMap K L g) (algebraMap K L gu)
      (algebraMap K L u) s0 s1 =
      (-2*gu/g^3) • s0 + (2*(g-gu*u)/g^3) • s1 := by
    rw [linearDensity_coefficients]
    simp only [Algebra.smul_def, map_div₀, map_mul, map_neg,
      map_ofNat, map_pow, map_sub]
  rw [h, map_add, map_smul, map_smul, linearDensity_coefficients]
  simp only [smul_eq_mul]

/-- The finite trace of the componentwise current solves the literal target
density when the two canonical source coefficients match. -/
theorem finiteTrace_primitive_of_source_match
    (D : ι → Derivation ℤ K K) (E : ι → Derivation ℤ L L)
    (compatible : ∀ i x, E i (algebraMap K L x) = algebraMap K L (D i x))
    (g gu u p0 p1 : K) (s0 s1 : L) (w : ι → L)
    (hequation : (∑ i, E i (w i)) =
      linearDensity (algebraMap K L g) (algebraMap K L gu)
        (algebraMap K L u) s0 s1)
    (hsource0 : Algebra.normalizedTrace K L s0 = p0)
    (hsource1 : Algebra.normalizedTrace K L s1 = p1) :
    (∑ i, D i (Algebra.normalizedTrace K L (w i))) =
      linearDensity g gu u p0 p1 := by
  calc
    _ = ∑ i, Algebra.normalizedTrace K L (E i (w i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (finiteNormalizedTrace_derivation (D i) (E i) (compatible i) (w i)).symm
    _ = Algebra.normalizedTrace K L (∑ i, E i (w i)) := (map_sum _ _ _).symm
    _ = _ := by
      rw [hequation, finiteTrace_linearDensity, hsource0, hsource1]

end FiniteTrace

def cubic (l B C D u : K) : K := l*u^3+B*u^2+C*u+D

/-- Exact polynomial division of the square of the normal derivative. -/
theorem normal_square_remainder (l B C D u : K) :
    (cubicNormal l B C u)^2 =
      (C^2-3*B*D)+(B*C-9*l*D)*u+(B^2-3*l*C)*u^2 +
        (9*l*u+3*B)*cubic l B C D u := by
  simp only [cubicNormal, cubic]
  ring

variable [CharZero K]

def residualSource0 (l B C D delta : K) : K :=
  delta*(9*l*D-B*C)/(6*l)

def residualSource1 (l B C delta : K) : K :=
  delta*(3*l*C-B^2)/(3*l)

theorem residual_source_numerator (l B C D delta u : K) (hl : l ≠ 0) :
    cubicNormal l B C u * residualSource1 l B C delta -
      cubicSecond l B u *
        (residualSource0 l B C D delta + residualSource1 l B C delta*u) =
      delta*((cubicNormal l B C u)^2 -
        (9*l*u+3*B)*cubic l B C D u) := by
  simp only [cubicNormal, cubicSecond, residualSource0, residualSource1, cubic]
  field_simp [hl]
  ring

/-- The reduced source is exactly a cubic residue with two explicit linear
source coefficients.  Its equality is on the actual cubic relation. -/
theorem residual_density_as_linear_source (l B C D delta u : K)
    (hl : l ≠ 0) (hg : cubicNormal l B C u ≠ 0)
    (hf : cubic l B C D u = 0) :
    linearDensity (cubicNormal l B C u) (cubicSecond l B u) u
      (residualSource0 l B C D delta) (residualSource1 l B C delta) =
      2*delta/cubicNormal l B C u := by
  rw [linearDensity, residual_source_numerator l B C D delta u hl, hf]
  simp only [mul_zero, sub_zero]
  field_simp [hg]

section FullRelativeCurrent

variable {ι : Type*} [Fintype ι]

/-- The field-calculus core permits normal dependence in every base component.
The normal component enters the two matching equations and cancels from the
resulting relative primitive. -/
theorem field_primitive_of_ordinary_game
    (E : ι → Derivation ℤ K K) (g gu p pu v : K)
    (w dw nw df dg : ι → K) (hg : g ≠ 0)
    (hw : ∀ i, E i (w i) = dw i-df i/g*nw i)
    (hEg : ∀ i, E i g = dg i-df i/g*gu)
    (hgame : (∑ i, w i*df i)+v*g = p)
    (hnormal : (∑ i, (nw i*df i+w i*dg i))+v*gu = pu+g*(∑ i, dw i)) :
    (∑ i, E i (-2*w i/g)) = 2*(g*pu-gu*p)/g^3 := by
  have hterm (i : ι) : E i (-2*w i/g) =
      (-2/g)*dw i+(2/g^2)*(nw i*df i+w i*dg i)-
        (2*gu/g^3)*(w i*df i) := by
    have htwo : E i (2 : K) = 0 := (E i).map_natCast 2
    simp only [Derivation.leibniz_div, Derivation.leibniz, map_neg,
      htwo, smul_eq_mul, hw, hEg]
    field_simp [hg]
    ring
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  simp only [Finset.sum_add_distrib] at hnormal
  field_simp [hg]
  linear_combination g*hnormal-gu*hgame

variable {R : Type*} [CommRing R]

/-- An ordinary current in a polynomial or localized coefficient ring gives
a relative primitive on `f=0`.  All base directions are retained; there is no
normal-independence assumption on the components or the denominator ring. -/
theorem relative_primitive_of_ordinary_game
    (phi : R →+* K) (T : Derivation ℤ R R)
    (D : ι → Derivation ℤ R R) (E : ι → Derivation ℤ K K)
    (f p v : R) (w : ι → R)
    (hf : phi f = 0) (hg : phi (T f) ≠ 0)
    (hchain : ∀ i x, E i (phi x) = phi (D i x)-phi (D i f)/phi (T f)*phi (T x))
    (hcomm : ∀ i, T (D i f) = D i (T f))
    (hgame : (∑ i, w i*D i f)+v*T f-f*((∑ i, D i (w i))+T v) = p) :
    (∑ i, E i (-2*phi (w i)/phi (T f))) =
      2*(phi (T f)*phi (T p)-phi (T (T f))*phi p)/(phi (T f))^3 := by
  apply field_primitive_of_ordinary_game E (phi (T f)) (phi (T (T f)))
    (phi p) (phi (T p)) (phi v)
    (fun i => phi (w i)) (fun i => phi (D i (w i))) (fun i => phi (T (w i)))
    (fun i => phi (D i f)) (fun i => phi (D i (T f))) hg
  · intro i
    exact hchain i (w i)
  · intro i
    exact hchain i (T f)
  · have h := congrArg phi hgame
    simpa only [map_sub, map_add, map_sum, map_mul, hf, zero_mul, sub_zero] using h
  · let L := (∑ i, D i (w i))+T v
    have hgame' : (∑ i, w i*D i f)+v*T f-f*L = p := hgame
    have h := congrArg T hgame'
    simp only [map_sub, map_add, map_sum, Derivation.leibniz, smul_eq_mul,
      hcomm] at h
    have hm := congrArg phi h
    simp only [map_sub, map_add, map_sum, map_mul, hf, zero_mul,
      L] at hm
    have hs : (∑ i, (phi (T (w i))*phi (D i f)+phi (w i)*phi (D i (T f)))) =
        ∑ i, (phi (w i)*phi (D i (T f))+phi (D i f)*phi (T (w i))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    linear_combination hm

end FullRelativeCurrent

end CubicTraceDescent

#print axioms CubicTraceDescent.finiteTrace_linearDensity
#print axioms CubicTraceDescent.finiteTrace_primitive_of_source_match
#print axioms CubicTraceDescent.normal_square_remainder
#print axioms CubicTraceDescent.residual_source_numerator
#print axioms CubicTraceDescent.residual_density_as_linear_source
#print axioms CubicTraceDescent.field_primitive_of_ordinary_game
#print axioms CubicTraceDescent.relative_primitive_of_ordinary_game
