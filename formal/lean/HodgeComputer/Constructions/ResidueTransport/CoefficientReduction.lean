import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Reducing a normal residue with a coefficient vector field

Let `T` be a normal derivation, `D i` coefficient derivations and `f` an
equation. A coefficient vector field `W`, independent of the normal
coordinate, satisfying `W f = P + h*f` reduces the double-pole residue
`2*(f_u*P_u-f_uu*P)/f_u^3` to `2*(div W-h)/f_u` on `f=0`.

The reduction constructs the rational current `-2*W/f_u` and proves both
directions of primitive existence. In the cleared interface, `W=Z/J`;
the numerators, denominator and exact polynomial identity are explicit
inputs. The map to the hypersurface field need not be injective. In
particular, no map from the entire ambient fraction field through `f=0`
is assumed.

All index sets, equations, coefficient rings and fields are arbitrary.
The remaining lower-pole primitive is an application obligation.
-/

noncomputable section

namespace ResidueCoefficientReduction

open scoped BigOperators

section FieldCalculus

variable {K ι : Type*} [Field K] [Fintype ι]

def divergence (E : ι → Derivation ℤ K K) (v : ι → K) : K :=
  ∑ i, E i (v i)

def HasPrimitive (E : ι → Derivation ℤ K K) (r : K) : Prop :=
  ∃ v : ι → K, divergence E v = r

theorem divergence_add (E : ι → Derivation ℤ K K) (v w : ι → K) :
    divergence E (v+w) = divergence E v + divergence E w := by
  simp [divergence, Finset.sum_add_distrib]

theorem divergence_sub (E : ι → Derivation ℤ K K) (v w : ι → K) :
    divergence E (v-w) = divergence E v - divergence E w := by
  simp [divergence, Finset.sum_sub_distrib]

/-- A displayed current identifies the two primitive problems in both directions. -/
theorem hasPrimitive_iff_of_reduction (E : ι → Derivation ℤ K K)
    (v : ι → K) (r s : K) (hv : divergence E v = r-s) :
    HasPrimitive E r ↔ HasPrimitive E s := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w-v, ?_⟩
    rw [divergence_sub, hw, hv]
    ring
  · rintro ⟨w, hw⟩
    refine ⟨v+w, ?_⟩
    rw [divergence_add, hw, hv]
    ring

/-- Quotient-rule core. `df` and `dg` are the coefficient derivatives of
the equation and its normal derivative, before implicit restriction. -/
theorem field_reduction (E : ι → Derivation ℤ K K)
    (g gu p pu h : K) (w dw df dg : ι → K)
    (hg : g ≠ 0)
    (hw : ∀ i, E i (w i) = dw i)
    (hEg : ∀ i, E i g = dg i-df i/g*gu)
    (hWf : (∑ i, w i*df i) = p)
    (hWg : (∑ i, w i*dg i) = pu+h*g) :
    divergence E (fun i => -2*w i/g) =
      2*(g*pu-gu*p)/g^3 - 2*((∑ i, dw i)-h)/g := by
  have hterm (i : ι) :
      E i (-2*w i/g) =
        (-2/g)*dw i + (2/g^2)*(w i*dg i) -
          (2*gu/g^3)*(w i*df i) := by
    have htwo : E i (2 : K) = 0 := (E i).map_natCast 2
    simp only [Derivation.leibniz_div, Derivation.leibniz, map_neg,
      htwo, smul_eq_mul, hw, hEg, neg_zero]
    field_simp; ring
  simp only [divergence, hterm, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, hWf, hWg]
  field_simp; ring

/-- The correction in `field_reduction` is reversible, so it imposes no
additional restriction on the eventual rational primitive. -/
theorem field_primitive_iff (E : ι → Derivation ℤ K K)
    (g gu p pu h : K) (w dw df dg : ι → K)
    (hg : g ≠ 0)
    (hw : ∀ i, E i (w i) = dw i)
    (hEg : ∀ i, E i g = dg i-df i/g*gu)
    (hWf : (∑ i, w i*df i) = p)
    (hWg : (∑ i, w i*dg i) = pu+h*g) :
    HasPrimitive E (2*(g*pu-gu*p)/g^3) ↔
      HasPrimitive E (2*((∑ i, dw i)-h)/g) :=
  hasPrimitive_iff_of_reduction E _ _ _
    (field_reduction E g gu p pu h w dw df dg hg hw hEg hWf hWg)

end FieldCalculus

section ClearedCoefficientField

variable {R K ι : Type*} [CommRing R] [Field K] [Fintype ι]

/-- The implicit tangent chain rule on a quotient field. -/
def ImplicitTangents (φ : R →+* K) (T : Derivation ℤ R R)
    (D : ι → Derivation ℤ R R) (E : ι → Derivation ℤ K K) (f : R) : Prop :=
  ∀ i p, E i (φ p) = φ (D i p) - φ (D i f)/φ (T f)*φ (T p)

/-- The base divergence of `Z/J`, evaluated on the hypersurface. -/
def coefficientDivergence (φ : R →+* K) (D : ι → Derivation ℤ R R)
    (J : R) (Z : ι → R) : K :=
  ∑ i, (φ (D i (Z i))*φ J - φ (Z i)*φ (D i J))/(φ J)^2

/-- The coefficient derivatives remain ordinary base derivatives because
both the numerator and denominator are constant in the normal direction. -/
theorem coefficient_derivative (φ : R →+* K) (T : Derivation ℤ R R)
    (D : ι → Derivation ℤ R R) (E : ι → Derivation ℤ K K)
    (f J : R) (Z : ι → R)
    (hchain : ImplicitTangents φ T D E f)
    (hZ : ∀ i, T (Z i) = 0) (hJ : T J = 0) (i : ι) :
    E i (φ (Z i)/φ J) =
      (φ (D i (Z i))*φ J-φ (Z i)*φ (D i J))/(φ J)^2 := by
  rw [Derivation.leibniz_div, hchain i (Z i), hchain i J, hZ, hJ, map_zero]
  simp only [smul_eq_mul, mul_zero, sub_zero, div_eq_mul_inv, inv_pow]
  ring

theorem coefficientDivergence_eq (φ : R →+* K) (T : Derivation ℤ R R)
    (D : ι → Derivation ℤ R R) (E : ι → Derivation ℤ K K)
    (f J : R) (Z : ι → R)
    (hchain : ImplicitTangents φ T D E f)
    (hZ : ∀ i, T (Z i) = 0) (hJ : T J = 0) :
    coefficientDivergence φ D J Z =
      divergence E (fun i => φ (Z i)/φ J) := by
  simp only [coefficientDivergence, divergence,
    coefficient_derivative φ T D E f J Z hchain hZ hJ]

/-- Differentiate the coefficient matching identity before restriction.
This derives the needed normal identity, instead of assuming it. -/
theorem normal_matching (φ : R →+* K) (T : Derivation ℤ R R)
    (D : ι → Derivation ℤ R R) (f P h J : R) (Z : ι → R)
    (hf : φ f = 0)
    (hZ : ∀ i, T (Z i) = 0) (hJ : T J = 0)
    (hcomm : ∀ i, T (D i f) = D i (T f))
    (hmatch : (∑ i, Z i*D i f) = J*(P+h*f)) :
    (∑ i, φ (Z i)*φ (D i (T f))) =
      φ J*(φ (T P)+φ h*φ (T f)) := by
  have hn := congrArg T hmatch
  simp only [map_sum, map_add, Derivation.leibniz, smul_eq_mul,
    hZ, hJ, hcomm, mul_zero, add_zero] at hn
  have he := congrArg φ hn
  simpa only [map_sum, map_mul, map_add, hf, mul_zero, zero_mul,
    zero_add, add_zero] using he

/-- A coefficient vector field with a common denominator supplies the
exact high-pole correction. `h=0` is ordinary coefficient matching;
`h≠0` also permits matching modulo the equation. -/
theorem cleared_coefficient_reduction
    (φ : R →+* K) (T : Derivation ℤ R R)
    (D : ι → Derivation ℤ R R) (E : ι → Derivation ℤ K K)
    (f P h J : R) (Z : ι → R)
    (hf : φ f = 0) (hg : φ (T f) ≠ 0) (hJ0 : φ J ≠ 0)
    (hchain : ImplicitTangents φ T D E f)
    (hZ : ∀ i, T (Z i) = 0) (hJ : T J = 0)
    (hcomm : ∀ i, T (D i f) = D i (T f))
    (hmatch : (∑ i, Z i*D i f) = J*(P+h*f)) :
    divergence E (fun i => -2*(φ (Z i)/φ J)/φ (T f)) =
      2*(φ (T f)*φ (T P)-φ (T (T f))*φ P)/(φ (T f))^3 -
        2*(coefficientDivergence φ D J Z-φ h)/φ (T f) := by
  apply field_reduction E (φ (T f)) (φ (T (T f))) (φ P) (φ (T P)) (φ h)
    (fun i => φ (Z i)/φ J)
    (fun i => (φ (D i (Z i))*φ J-φ (Z i)*φ (D i J))/(φ J)^2)
    (fun i => φ (D i f)) (fun i => φ (D i (T f))) hg
  · exact coefficient_derivative φ T D E f J Z hchain hZ hJ
  · intro i
    exact hchain i (T f)
  · have he := congrArg φ hmatch
    simp only [map_sum, map_mul, map_add, hf, mul_zero, add_zero] at he
    calc
      (∑ i, φ (Z i)/φ J*φ (D i f)) =
          (∑ i, φ (Z i)*φ (D i f)) / φ J := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = φ P := by rw [he]; field_simp
  · have he := normal_matching φ T D f P h J Z hf hZ hJ hcomm hmatch
    calc
      (∑ i, φ (Z i)/φ J*φ (D i (T f))) =
          (∑ i, φ (Z i)*φ (D i (T f))) / φ J := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = φ (T P)+φ h*φ (T f) := by rw [he]; field_simp

/-- An exact equivalence of primitive problems with explicit denominator
and coefficient identities. No upper bound on poles of the new primitive
is imposed. -/
theorem cleared_primitive_iff
    (φ : R →+* K) (T : Derivation ℤ R R)
    (D : ι → Derivation ℤ R R) (E : ι → Derivation ℤ K K)
    (f P h J : R) (Z : ι → R)
    (hf : φ f = 0) (hg : φ (T f) ≠ 0) (hJ0 : φ J ≠ 0)
    (hchain : ImplicitTangents φ T D E f)
    (hZ : ∀ i, T (Z i) = 0) (hJ : T J = 0)
    (hcomm : ∀ i, T (D i f) = D i (T f))
    (hmatch : (∑ i, Z i*D i f) = J*(P+h*f)) :
    HasPrimitive E
      (2*(φ (T f)*φ (T P)-φ (T (T f))*φ P)/(φ (T f))^3) ↔
    HasPrimitive E (2*(coefficientDivergence φ D J Z-φ h)/φ (T f)) :=
  hasPrimitive_iff_of_reduction E _ _ _
    (cleared_coefficient_reduction φ T D E f P h J Z hf hg hJ0
      hchain hZ hJ hcomm hmatch)

end ClearedCoefficientField

#print axioms field_reduction
#print axioms normal_matching
#print axioms cleared_coefficient_reduction
#print axioms cleared_primitive_iff

end ResidueCoefficientReduction
