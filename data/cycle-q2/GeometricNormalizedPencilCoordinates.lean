import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Proposal.GeometricGenericWeightedPencilEquation
import Proposal.GeometricGenericWeightedMonicOpen
import Proposal.GeometricUniversalWeightedChart
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

section
/-!
# Differentiating the weighted pencil in its relative coordinates

The relative derivations kill the deformation parameter and the pencil
ratio. Differentiating the weighted hypersurface equation at its actual
point therefore determines the derivative of the implicit coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GenericWeightedChainRule

open MvPolynomial CycleQ2Bridge CycleQ2AffineClearing CycleQ2GenericSpecialization
  CycleQ2GenericPencilLift CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedPencilEquation

section ChainRule

variable {R K : Type} [CommRing R] [Field K] [Algebra ℂ K]
  (D : Derivation ℂ K K) (f : R →+* K) (x : Fin 5 → K)

private def chain (p : MvPolynomial (Fin 5) R) : Prop :=
  D (eval₂Hom f x p) = ∑ i, eval₂Hom f x (pderiv i p) * D (x i)

private theorem chain_C (c : R) (hc : D (f c) = 0) : chain D f x (C c) := by
  simp [chain, hc]

private theorem chain_X (i : Fin 5) : chain D f x (X i) := by
  classical
  simp [chain, pderiv_X, Pi.single_apply, apply_ite]

private theorem chain_add {p q : MvPolynomial (Fin 5) R} (hp : chain D f x p) (hq : chain D f x q) :
    chain D f x (p + q) := by
  change D _ = _
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hp hq

private theorem chain_mul {p q : MvPolynomial (Fin 5) R} (hp : chain D f x p) (hq : chain D f x q) :
    chain D f x (p * q) := by
  unfold chain at hp hq ⊢
  simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp, hq, map_add,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intros <;> ring

private theorem chain_pow {p : MvPolynomial (Fin 5) R} (hp : chain D f x p) (n : ℕ) :
    chain D f x (p ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using chain_C D f x 1 (by rw [map_one, D.map_one_eq_zero])
  | succ n ih => rw [pow_succ]; exact chain_mul D f x ih hp

theorem eval_chain_rule (hf : ∀ c, D (f c) = 0) (p : MvPolynomial (Fin 5) R) :
    D (eval₂Hom f x p) = ∑ i, eval₂Hom f x (pderiv i p) * D (x i) := by
  change chain D f x p
  induction p using MvPolynomial.induction_on with
  | C c => exact chain_C D f x c (hf c)
  | add p q hp hq => exact chain_add D f x hp hq
  | mul_X p i hp => exact chain_mul D f x hp (chain_X D f x i)

private theorem chain_map (hf : ∀ c, D (f c) = 0) (p : MvPolynomial (Fin 5) R) :
    chain D (RingHom.id K) x (MvPolynomial.map f p) := by
  change D (eval x (MvPolynomial.map f p)) =
    ∑ i, eval x (pderiv i (MvPolynomial.map f p)) * D (x i)
  simp only [pderiv_map, eval_map]
  exact eval_chain_rule D f x hf p

end ChainRule

section Fraction
variable {R K : Type} [CommRing R] [Field K] [Algebra ℂ K]

/-- Evaluate the coordinate partial of a quotient by the usual quotient rule. -/
def quotientPartial (f : R →+* K) (x : Fin 5 → K) (p q : MvPolynomial (Fin 5) R) (i : Fin 5) : K :=
  (eval₂Hom f x (pderiv i p) * eval₂Hom f x q -
    eval₂Hom f x p * eval₂Hom f x (pderiv i q)) / (eval₂Hom f x q) ^ 2

theorem eval_fraction_chain_rule (D : Derivation ℂ K K) (f : R →+* K)
    (hf : ∀ c, D (f c) = 0) (x : Fin 5 → K) (p q : MvPolynomial (Fin 5) R) :
    D (eval₂Hom f x p / eval₂Hom f x q) = ∑ i, quotientPartial f x p q i * D (x i) := by
  unfold quotientPartial
  rw [Derivation.leibniz_div, eval_chain_rule D f x hf p, eval_chain_rule D f x hf q]
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv, inv_pow]
  ring

end Fraction

theorem parameter_coefficients_constant {K : Type} [Field K] [Algebra ℂ K]
    (D : Derivation ℂ K K) (τ l : K) (hτ : D τ = 0) (hl : D l = 0)
    (c : MvPolynomial (Fin 2) ℂ) :
    D (eval₂Hom (algebraMap ℂ K) ![τ, l] c) = 0 := by
  have hx (i : Fin 2) : D (![τ, l] i) = 0 := by
    fin_cases i
    · exact hτ
    · exact hl
  induction c using MvPolynomial.induction_on with
  | C c => simp only [eval₂Hom_C, D.map_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | mul_X a i ha => simp only [map_mul, eval₂Hom_X', Derivation.leibniz, ha, hx, smul_zero, add_zero]

/-- The entire coefficient field generated over the complex numbers is constant. -/
theorem adjoin_parameters_constant {K : Type} [Field K] [Algebra ℂ K]
    (D : Derivation ℂ K K) (τ l : K) (hτ : D τ = 0) (hl : D l = 0)
    (r : IntermediateField.adjoin ℂ ({τ, l} : Set K)) : D (r : K) = 0 := by
  refine IntermediateField.adjoin_induction ℂ (p := fun x _ => D x = 0) ?_
    D.map_algebraMap ?_ ?_ ?_ r.property
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · exact h ▸ hτ
    · exact (Set.mem_singleton_iff.mp h) ▸ hl
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro x _ hx
    rw [Derivation.leibniz_inv, hx, smul_zero]
  · intro x y _ _ hx hy
    rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]

private theorem equation_chain (D : Derivation ℂ RF RF) (tau l : RF)
    (ht : D tau = 0) (hl : D l = 0) (h : WeightedPoly) :
    D (eval weightedPoint (equation tau l h)) =
      ∑ i, eval weightedPoint (pderiv i (equation tau l h)) * D (weightedPoint i) := by
  change chain D (RingHom.id RF) weightedPoint (equation tau l h)
  have h₆ : D (1 + l ^ 6) = 0 := by
    simp only [map_add, D.map_one_eq_zero, D.leibniz_pow, hl, smul_zero, add_zero]
  have h₂ : D (1 / 2) = 0 := by
    rw [one_div, D.leibniz_inv, show D 2 = 0 from D.map_natCast 2, smul_zero]
  let F := RingHom.id RF
  let H := chain D F weightedPoint
  have add {p q : MvPolynomial (Fin 5) RF} (hp : H p) (hq : H q) : H (p + q) :=
    chain_add D F weightedPoint hp hq
  have mul {p q : MvPolynomial (Fin 5) RF} (hp : H p) (hq : H q) : H (p * q) :=
    chain_mul D F weightedPoint hp hq
  have X' (i : Fin 5) : H (X i) := chain_X D F weightedPoint i
  have pow (i : Fin 5) (n : ℕ) : H (X i ^ n) := chain_pow D F weightedPoint (X' i) n
  have C' (a : RF) (ha : D a = 0) : H (C a) := chain_C D F weightedPoint a ha
  have hτ := C' _ ht
  have hl' := C' _ hl
  have h₆' := C' _ h₆
  have h₂' := C' _ h₂
  have hh := chain_map D (algebraMap ℂ RF) weightedPoint D.map_algebraMap h
  change H (equation tau l h)
  unfold equation
  with_reducible
    repeat' first | assumption | apply add | apply mul | apply pow | apply X'

theorem weighted_coordinate_sum (d : Direction) (j : Fin 3) (F : Fin 5 → RF) :
    ∑ i, F i * relativeDerivation d j (weightedPoint i) =
      F 1 * relativeDerivation d j (z 0) + F j.succ.succ := by
  have hcoord (k : Fin 3) : weightedPoint k.succ.succ = relativeCoordinate k := by
    fin_cases k <;> rfl
  have hsum : ∑ k : Fin 3, F k.succ.succ * relativeDerivation d j (weightedPoint k.succ.succ) =
      F j.succ.succ := by
    simp [hcoord, relativeDerivation_coordinate]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hsum]
  change F 0 * relativeDerivation d j 1 + _ = _
  rw [Derivation.map_one_eq_zero, mul_zero, zero_add]
  rfl

open CycleQ2IncidenceNormalForm

variable (c : FullInvariantIndex 6 → ℂ) (hc : endpointDifference c ≠ 0)

abbrev endpointEquation := equation (parameter (endpointDirection c hc)) lambda (endpointDifference c)

theorem normal_coordinate (j : Fin 3) :
    relativeDerivation (endpointDirection c hc) j (z 0) =
      -eval weightedPoint (pderiv j.succ.succ (endpointEquation c hc)) /
        eval weightedPoint (pderiv 1 (endpointEquation c hc)) := by
  let d := endpointDirection c hc
  have h := equation_chain (relativeDerivation d j) (parameter d) lambda
    (relative_tau d j) (relative_lambda d j) (endpointDifference c)
  rw [endpoint_equation c hc, map_zero, weighted_coordinate_sum] at h
  apply (eq_div_iff (endpoint_normal_ne_zero c hc)).mpr
  rw [mul_comm]
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The directional derivative after solving for the second weighted coordinate. -/
theorem weighted_derivative {R : Type} [CommRing R] (j : Fin 3) (f : R →+* RF)
    (hf : ∀ a, relativeDerivation (endpointDirection c hc) j (f a) = 0)
    (p : MvPolynomial (Fin 5) R) :
    relativeDerivation (endpointDirection c hc) j (eval₂Hom f weightedPoint p) =
      eval₂Hom f weightedPoint (pderiv j.succ.succ p) -
        eval₂Hom f weightedPoint (pderiv 1 p) *
        eval weightedPoint (pderiv j.succ.succ (endpointEquation c hc)) /
          eval weightedPoint (pderiv 1 (endpointEquation c hc)) := by
  rw [eval_chain_rule _ f weightedPoint hf p, weighted_coordinate_sum, normal_coordinate c hc]
  ring

theorem weighted_fraction_derivative {R : Type} [CommRing R] (j : Fin 3) (f : R →+* RF)
    (hf : ∀ a, relativeDerivation (endpointDirection c hc) j (f a) = 0)
    (p q : MvPolynomial (Fin 5) R) :
    relativeDerivation (endpointDirection c hc) j
        (eval₂Hom f weightedPoint p / eval₂Hom f weightedPoint q) =
      quotientPartial f weightedPoint p q j.succ.succ -
        quotientPartial f weightedPoint p q 1 *
          eval weightedPoint (pderiv j.succ.succ (endpointEquation c hc)) /
            eval weightedPoint (pderiv 1 (endpointEquation c hc)) := by
  rw [eval_fraction_chain_rule _ f hf weightedPoint p q, weighted_coordinate_sum, normal_coordinate c hc]
  ring

end CycleQ2GenericWeightedChainRule
end

#print axioms CycleQ2GenericWeightedChainRule.normal_coordinate
#print axioms CycleQ2GenericWeightedChainRule.weighted_derivative
#print axioms CycleQ2GenericWeightedChainRule.weighted_fraction_derivative
end

section
/-!
# The coefficient field of the normalized deformed pencil

The leading coefficient and all 44 normalized coefficients are rational
functions of the deformation parameter and weighted pencil ratio. They are
constants for each of the three relative derivations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GenericWeightedMonicCoefficients

open CycleQ2GenericSpecialization (Direction RF parameter)
open CycleQ2GenericWeightedCoordinates (relativeDerivation relative_tau relative_lambda)
open CycleQ2GenericPencilOpen CycleQ2GenericWeightedOpen CycleQ2GenericWeightedMonicOpen
open CycleQ2IncidenceNormalForm

/-- The two-parameter coefficient field inside the actual deformed function field. -/
abbrev coefficientField (d : Direction) :=
  IntermediateField.adjoin ℂ ({parameter d, CycleQ2GenericWeightedCoordinates.lambda} : Set RF)

private theorem polynomial_mem {A : Type} [CommRing A] (d : Direction)
    (φ : Polynomial A →+* RF) (hC : ∀ a, φ (Polynomial.C a) ∈ coefficientField d)
    (hX : φ Polynomial.X ∈ coefficientField d) (p : Polynomial A) :
    φ p ∈ coefficientField d := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact (coefficientField d).add_mem hp hq
  | monomial n a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    exact (coefficientField d).mul_mem (hC a) ((coefficientField d).pow_mem hX n)

theorem evaluation_mem (d : Direction) (p : TwoParameterRing) :
    evaluation d p ∈ coefficientField d := by
  refine polynomial_mem d (evaluation d) ?_ ?_ p
  · intro a
    change ((evaluation d).comp Polynomial.C) a ∈ coefficientField d
    refine polynomial_mem d ((evaluation d).comp Polynomial.C) ?_ ?_ a
    · intro b
      change evaluation d (constantParameters b) ∈ coefficientField d
      rw [evaluation_constant]
      exact (coefficientField d).algebraMap_mem b
    · change evaluation d CycleQ2GenericPencilOpen.tau ∈ coefficientField d
      rw [evaluation_tau]
      exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert _ _)
  · change evaluation d CycleQ2GenericPencilOpen.lambda ∈ coefficientField d
    rw [evaluation_lambda]
    exact IntermediateField.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

def leading (d : Direction) (c : ParameterIndex → ℂ) : coefficientField d :=
  ⟨coefficientPoint d c fullSexticLeadingIndex, evaluation_mem _ _⟩

@[simp] theorem leading_coe (d : Direction) (c : ParameterIndex → ℂ) :
    (leading d c : RF) = coefficientPoint d c fullSexticLeadingIndex := rfl

def coefficients (d : Direction) (c : ParameterIndex → ℂ) (e : FullSexticTailIndex) :
    coefficientField d :=
  ⟨normalizedCoefficientPoint d c e, (coefficientField d).div_mem (evaluation_mem _ _)
    (leading d c).property⟩

@[simp] theorem coefficients_coe (d : Direction) (c : ParameterIndex → ℂ) (e : FullSexticTailIndex) :
    (coefficients d c e : RF) = normalizedCoefficientPoint d c e := rfl

theorem deriv_coefficientField (d : Direction) (j : Fin 3) (a : coefficientField d) :
    relativeDerivation d j (a : RF) = 0 :=
  CycleQ2GenericWeightedChainRule.adjoin_parameters_constant _ _ _ (relative_tau d j) (relative_lambda d j) a


@[simp] theorem deriv_leading (d : Direction) (j : Fin 3) (c : ParameterIndex → ℂ) :
    relativeDerivation d j (coefficientPoint d c fullSexticLeadingIndex) = 0 :=
  deriv_coefficientField d j (leading d c)

@[simp] theorem deriv_normalized (d : Direction) (j : Fin 3) (c : ParameterIndex → ℂ)
    (e : FullSexticTailIndex) :
    relativeDerivation d j (normalizedCoefficientPoint d c e) = 0 :=
  deriv_coefficientField d j (coefficients d c e)

end CycleQ2GenericWeightedMonicCoefficients
end

#print axioms CycleQ2GenericWeightedMonicCoefficients.evaluation_mem
#print axioms CycleQ2GenericWeightedMonicCoefficients.deriv_coefficientField
end

section
/-!
# The monic spatial cubic over the deformed parameter field

The three spatial coordinates and both parameters generate a field over
which the remaining squared coordinate satisfies the normalized sextic,
viewed as its monic cubic in the final variable.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GenericWeightedSpatialCubic

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2GenericSpecialization
  CycleQ2GenericPencilLift CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedMonicCoefficients
open CycleQ2GenericWeightedOpen (coefficientPoint)
open CycleQ2GenericWeightedMonicOpen (normalizedCoefficientPoint equation_eq_leading_mul_normalized)
open CycleQ2GenericWeightedPencilEquation (weightedPoint endpoint_equation)
open CycleQ2GeometricHodgeThreefoldCubic (baseValue expand)

/-- Parameters and three spatial coordinates, inside the actual ambient rational field. -/
def parameters (d : Direction) : Fin 5 → RF := ![parameter d, lambda, z 0, z 2, z 3]

abbrev spatialField (d : Direction) := IntermediateField.adjoin ℂ (Set.range (parameters d))

theorem parameter_mem (d : Direction) (i : Fin 5) : parameters d i ∈ spatialField d :=
  IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)

theorem coefficientField_le (d : Direction) : coefficientField d ≤ spatialField d := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with h | h
  · exact h ▸ parameter_mem d 0
  · exact (Set.mem_singleton_iff.mp h) ▸ parameter_mem d 1

/-- Evaluation of the univariate expansion at the remaining weight-two coordinate. -/
private theorem eval_cubic {A K : Type} [CommRing A] [Field K] [Algebra A K]
    (x : Fin 3 → A) (s : K) (p : MvPolynomial (Fin 5) A) :
    Polynomial.eval₂ (algebraMap A K) s
      ((expand 0 p).map (eval x)) =
        eval₂Hom (algebraMap A K) ![1, algebraMap A K (x 0), algebraMap A K (x 1),
          algebraMap A K (x 2), s] p := by
  let φ := (Polynomial.eval₂RingHom (algebraMap A K) s).comp
    ((Polynomial.mapRingHom (eval x)).comp (expand 0).toRingHom)
  have he : φ = eval₂Hom (algebraMap A K) ![1, algebraMap A K (x 0), algebraMap A K (x 1),
      algebraMap A K (x 2), s] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change Polynomial.eval₂ (algebraMap A K) s ((expand 0 (C a)).map (eval x)) = _
      rw [expand, aeval_C, eval₂Hom_C]
      change Polynomial.eval₂ (algebraMap A K) s ((Polynomial.C (C a : MvPolynomial (Fin 3) A)).map (eval x)) = algebraMap A K a
      simp
    · intro i
      change Polynomial.eval₂ (algebraMap A K) s ((expand 0 (X i)).map (eval x)) = _
      rw [expand, aeval_X, eval₂Hom_X']
      fin_cases i
      all_goals first
        | change Polynomial.eval₂ (algebraMap A K) s ((Polynomial.C (1 : MvPolynomial (Fin 3) A)).map (eval x)) = 1
          simp
        | change Polynomial.eval₂ (algebraMap A K) s ((Polynomial.C (X _ : MvPolynomial (Fin 3) A)).map (eval x)) = algebraMap A K (x _)
          simp
        | change Polynomial.eval₂ (algebraMap A K) s ((Polynomial.X : Polynomial (MvPolynomial (Fin 3) A)).map (eval x)) = s
          simp
        | simp [φ, expand, baseValue, Fin.snoc]
      all_goals rfl
  exact RingHom.congr_fun he p

private theorem integral_of_normalized {A K : Type} [Field A] [Field K] [Algebra A K]
    (x : Fin 3 → A) (s : K) (h : FullSexticTailIndex → A)
    (he : eval₂Hom (algebraMap A K) ![1, algebraMap A K (x 0), algebraMap A K (x 1),
      algebraMap A K (x 2), s] (normalizedFullSextic h) = 0) : IsIntegral A s := by
  let p := CycleQ2MonicWeightedAffineEquation.equation h
  refine ⟨p.map (eval x), (CycleQ2MonicWeightedAffineEquation.monic h).map _, ?_⟩
  exact (eval_cubic x s (normalizedFullSextic h)).trans he

variable (c : FullInvariantIndex 6 → ℂ) (hc : endpointDifference c ≠ 0)

theorem square_integral
    (hL : coefficientPoint (endpointDirection c hc) c fullSexticLeadingIndex ≠ 0) :
    IsIntegral (spatialField (endpointDirection c hc)) (u ^ 2) := by
  let d := endpointDirection c hc
  let F := spatialField d
  let x : Fin 3 → F := ![⟨z 0, parameter_mem d 2⟩, ⟨z 2, parameter_mem d 3⟩,
    ⟨z 3, parameter_mem d 4⟩]
  let h : FullSexticTailIndex → F := fun e =>
    ⟨_, coefficientField_le d (coefficients d c e).property⟩
  apply integral_of_normalized x (u ^ 2) h
  change eval₂Hom (algebraMap F RF) weightedPoint (normalizedFullSextic h) = 0
  rw [show eval₂Hom (algebraMap F RF) weightedPoint (normalizedFullSextic h) =
    eval weightedPoint (MvPolynomial.map (algebraMap F RF) (normalizedFullSextic h)) from
    MvPolynomial.eval₂_eq_eval_map ..]
  have hmap : MvPolynomial.map (algebraMap F RF) (normalizedFullSextic h) =
      normalizedFullSextic (normalizedCoefficientPoint d c) := by
    simp only [normalizedFullSextic, map_add, map_sum, map_monomial, map_one]
    rfl
  rw [hmap]
  have hz := endpoint_equation c hc
  rw [equation_eq_leading_mul_normalized _ _ hL, map_mul, eval_C] at hz
  exact (mul_eq_zero.mp hz).resolve_left hL

theorem u_integral
    (hL : coefficientPoint (endpointDirection c hc) c fullSexticLeadingIndex ≠ 0) :
    IsIntegral (spatialField (endpointDirection c hc)) u :=
  IsIntegral.of_pow (by decide : 0 < 2) (square_integral c hc hL)

end CycleQ2GenericWeightedSpatialCubic
end

#print axioms CycleQ2GenericWeightedSpatialCubic.u_integral
end

section
/-!
# Algebraic independence of the three surviving spatial coordinates

The actual rational-function field is algebraic over the field generated by the
deformation parameter, the ratio and three spatial coordinates. The missing
coordinate is integral by the monic weighted cubic. Comparing with the five
independent original coordinates proves that every nonzero spatial polynomial
over the two-parameter field stays nonzero on the deformed pencil.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GenericWeightedSpatialIndependence

open HodgeComputer MvPolynomial CycleQ2Bridge CycleQ2GenericSpecialization
  CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedSpatialCubic
  CycleQ2GenericPencilLift CycleQ2IncidenceNormalForm
open CycleQ2GenericWeightedMonicCoefficients (coefficientField)
open CycleQ2GenericWeightedOpen (coefficientPoint)

private theorem algebraic_extension (d : Direction) (hu : IsIntegral (spatialField d) u) :
    Algebra.IsAlgebraic (spatialField d) RF := by
  let F := spatialField d
  let C := algebraicClosure F RF
  have hF {x : RF} (hx : x ∈ F) : x ∈ C := C.algebraMap_mem (⟨x, hx⟩ : F)
  have hm (i : Fin 5) : parameters d i ∈ C :=
    hF (IntermediateField.subset_adjoin ℂ _ ⟨i, rfl⟩)
  have hu' : u ∈ C := mem_algebraicClosure_iff'.mpr hu
  have hz (i : Fin 5) : z i ∈ C := by
    fin_cases i
    · exact hm 2
    · exact hu'
    · exact hm 3
    · exact hm 4
    · change v ∈ C
      rw [← lambda_mul_u]
      exact C.mul_mem (hm 1) hu'
  have hp (p : AmbientPoly 4) : polynomialMap 4 p ∈ C := by
    induction p using MvPolynomial.induction_on with
    | C a => exact hF (F.algebraMap_mem a)
    | add p q hp hq =>
      rw [map_add]
      exact C.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact C.mul_mem hp (hz i)
  constructor
  intro y
  obtain ⟨p,q,_,rfl⟩ := IsFractionRing.div_surjective (AmbientPoly 4) y
  exact mem_algebraicClosure_iff.mp (C.div_mem (hp p) (hp q))

private theorem parameters_independent_of_integral (d : Direction)
    (hu : IsIntegral (spatialField d) u) : AlgebraicIndependent ℂ (parameters d) := by
  have hz : AlgebraicIndependent ℂ z :=
    (MvPolynomial.algebraicIndependent_X (Fin 5) ℂ).map'
      (f := IsScalarTower.toAlgHom ℂ (AmbientPoly 4) RF) (IsFractionRing.injective (AmbientPoly 4) RF)
  have := algebraic_extension d hu
  have : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range (parameters d))) RF :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp ‹Algebra.IsAlgebraic (spatialField d) RF›
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℂ (parameters d)
    hz.cardinalMk_le_trdeg).1

private theorem spatial_independent_over_parameters
    {k L : Type*} [Field k] [Field L] [Algebra k L] (τ l a b c : L)
    (H : AlgebraicIndependent k (![τ, l, a, b, c] : Fin 5 → L)) :
    AlgebraicIndependent (IntermediateField.adjoin k ({τ, l} : Set L)) (![a, b, c] : Fin 3 → L) := by
  let ii : Fin 3 ⊕ Fin 2 ≃ Fin 5 := (Equiv.sumComm (Fin 3) (Fin 2)).trans finSumFinEquiv
  have hs : (![τ, l, a, b, c] : Fin 5 → L) ∘ ii =
      Sum.elim (![a, b, c] : Fin 3 → L) (![τ, l] : Fin 2 → L) := by
    funext x
    rcases x with x | x <;> fin_cases x <;> rfl
  have hr : Set.range (![τ, l] : Fin 2 → L) = ({τ, l} : Set L) := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro ht
      rcases Set.mem_insert_iff.mp ht with h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp h).symm⟩
  have htotal := H.comp ii ii.injective
  rw [hs] at htotal
  have hsp := (AlgebraicIndependent.sumElim_iff.mp htotal).2
  rw [hr] at hsp
  exact IntermediateField.algebraicIndependent_adjoin_iff.mpr hsp

variable (c : FullInvariantIndex 6 → ℂ) (hc : endpointDifference c ≠ 0)
variable (hL : coefficientPoint (endpointDirection c hc) c fullSexticLeadingIndex ≠ 0)

include hL

/-- The two pencil parameters and the three spatial coordinates form an
algebraically independent family in the actual rational function field. -/
theorem parameters_independent : AlgebraicIndependent ℂ (parameters (endpointDirection c hc)) :=
  parameters_independent_of_integral _ (u_integral c hc hL)

/-- The three free coordinates remain algebraically independent over the joint
rational coefficient field of both pencil parameters. -/
theorem spatial_independent :
    AlgebraicIndependent (coefficientField (endpointDirection c hc)) (![z 0, z 2, z 3] : Fin 3 → RF) :=
  spatial_independent_over_parameters _ _ _ _ _ (parameters_independent c hc hL)

/-- A surviving spatial polynomial supplies an actual nonzero denominator. -/
theorem spatial_eval_ne_zero
    (q : MvPolynomial (Fin 3) (coefficientField (endpointDirection c hc))) (hq : q ≠ 0) :
    eval₂Hom (algebraMap (coefficientField (endpointDirection c hc)) RF)
      (![z 0, z 2, z 3] : Fin 3 → RF) q ≠ 0 :=
  fun h => hq ((spatial_independent c hc hL).eq_zero_of_aeval_eq_zero q h)

end CycleQ2GenericWeightedSpatialIndependence
end

#print axioms CycleQ2GenericWeightedSpatialIndependence.parameters_independent
#print axioms CycleQ2GenericWeightedSpatialIndependence.spatial_eval_ne_zero
end
