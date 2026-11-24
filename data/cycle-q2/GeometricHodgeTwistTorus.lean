import Proposal.GeometricSurfaceCoordinates
import Proposal.GeometricHodgeThreefoldCubicRestriction
import Proposal.GeometricLocalizedDerivations
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Evaluation of localized chart coefficients on the common torus

The three normalized weight-one coordinates are units on the common torus.
The Laurent expansion of a localized chart coefficient can therefore be
evaluated there. The resulting ring homomorphism agrees with every chart
restriction carrying the original coordinates and constants to these values.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeTwistTorus

open MvPolynomial CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
open CycleQ2SeedQuotientFiniteFree (Base)

variable {R Tgt : Type*} [CommRing R] [CommRing Tgt] (ρ : R →+* Tgt) (u : Fin 3 → Tgtˣ)

def powers : Multiplicative LaurentExponent →* Tgt where
  toFun e := ((∏ q, u q ^ e.toAdd q : Tgtˣ) : Tgt)
  map_one' := by simp
  map_mul' x y := by
    change ((∏ q, u q ^ (x.toAdd q + y.toAdd q) : Tgtˣ) : Tgt) = _
    simp only [zpow_add, Finset.prod_mul_distrib, Units.val_mul]

def evaluate : Laurent (R := R) →+* Tgt :=
  AddMonoidAlgebra.liftNCRingHom ρ (powers u) (fun _ _ => Commute.all _ _)

theorem evaluate_single (e : LaurentExponent) (c : R) :
    evaluate ρ u (AddMonoidAlgebra.single e c) = ρ c * ((∏ q, u q ^ e q : Tgtˣ) : Tgt) := by
  exact AddMonoidAlgebra.liftNCRingHom_single ..

theorem evaluate_sum (p : Laurent (R := R)) :
    evaluate ρ u p = p.coeff.sum (fun e c => ρ c * ((∏ q, u q ^ e q : Tgtˣ) : Tgt)) := by
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p]
  rw [map_finsuppSum]
  simp only [evaluate_single]

theorem evaluate_C (c : R) : evaluate ρ u (baseToLaurent R (C c)) = ρ c := by
  change evaluate ρ u (baseToLaurent R (monomial 0 c)) = _
  rw [baseToLaurent_monomial, evaluate_single]
  simp

theorem evaluate_X (q : Fin 3) : evaluate ρ u (baseToLaurent R (X q)) = (u q).val := by
  rw [baseToLaurent_X]
  change evaluate ρ u (AddMonoidAlgebra.single (openExponent {q}) 1) = _
  rw [evaluate_single]
  classical
  simp [openExponent, Finset.prod_ite_eq']

/-- A chart-to-torus map is determined by the three original coordinates and the scalars. -/
theorem evaluate_restriction (B : Finset (Fin 3)) (g : coordinateLocalization R B →+* Tgt)
    (hc : ∀ c : R, g (algebraMap (Base R) (coordinateLocalization R B) (C c)) = ρ c)
    (hx : ∀ q : Fin 3, g (algebraMap (Base R) (coordinateLocalization R B) (X q)) = (u q).val)
    (p : coordinateLocalization R B) :
    evaluate ρ u (localizationToLaurent R B p) = g p := by
  have he : (evaluate ρ u).comp (localizationToLaurent R B) = g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (baseProduct R B))
    apply MvPolynomial.ringHom_ext
    · intro c
      change evaluate ρ u (localizationToLaurent R B (algebraMap _ _ (C c))) = _
      rw [localizationToLaurent_algebraMap, evaluate_C]
      exact (hc c).symm
    · intro q
      change evaluate ρ u (localizationToLaurent R B (algebraMap _ _ (X q))) = _
      rw [localizationToLaurent_algebraMap, evaluate_X]
      exact (hx q).symm
  exact RingHom.congr_fun he p

end CycleQ2HodgeTwistTorus
end

#print axioms CycleQ2HodgeTwistTorus.evaluate_restriction

/-! The three logarithmic derivatives act on the same finite Laurent
coefficients used by the native projective face coordinates. Their constant
coefficients vanish, including after the original product localization. -/

noncomputable section
namespace CycleQ2TorusLogDerivatives

open CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
open CycleQ2SeedQuotientFiniteFree (Base)

variable (R : Type*) [CommRing R]

def linear (j : Fin 3) : Laurent (R := R) →ₗ[R] Laurent (R := R) :=
  (Finsupp.lsum R (fun e : LaurentExponent =>
    (e j : R) • (AddMonoidAlgebra.lsingle e : R →ₗ[R] Laurent (R := R)))).comp
      (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

theorem linear_single (j : Fin 3) (e : LaurentExponent) (a : R) :
    linear R j (AddMonoidAlgebra.single e a) =
      AddMonoidAlgebra.single e ((e j : R) * a) := by
  change Finsupp.lsum R (fun f : LaurentExponent =>
    (f j : R) • (AddMonoidAlgebra.lsingle f : R →ₗ[R] Laurent (R := R)))
      (Finsupp.single e a) = _
  rw [Finsupp.lsum_single, LinearMap.smul_apply, AddMonoidAlgebra.lsingle_apply,
    AddMonoidAlgebra.smul_single, smul_eq_mul]

private theorem linear_leibniz (j : Fin 3) (x y : Laurent (R := R)) :
    linear R j (x*y) = x * linear R j y + y * linear R j x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x z hx hz =>
      rw [add_mul, map_add, hx, hz, map_add]
      ring
  | single e a =>
      induction y using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add y z hy hz =>
          rw [mul_add, map_add, hy, hz, map_add]
          ring
      | single f b =>
          rw [AddMonoidAlgebra.single_mul_single, linear_single, linear_single,
            linear_single, AddMonoidAlgebra.single_mul_single,
            AddMonoidAlgebra.single_mul_single, add_comm f e,
            ← AddMonoidAlgebra.single_add]
          apply congrArg (AddMonoidAlgebra.single (e+f))
          simp only [Pi.add_apply, Int.cast_add]
          ring

/-- The original Laurent-coordinate Euler derivation, with no completion
or field extension. -/
def logarithmic (j : Fin 3) : Derivation R (Laurent (R := R)) (Laurent (R := R)) where
  toLinearMap := linear R j
  map_one_eq_zero' := by
    change linear R j (AddMonoidAlgebra.single 0 1) = 0
    rw [linear_single]
    simp
  leibniz' := linear_leibniz R j

theorem logarithmic_single (j : Fin 3) (e : LaurentExponent) (a : R) :
    logarithmic R j (AddMonoidAlgebra.single e a) =
      AddMonoidAlgebra.single e ((e j : R) * a) := linear_single R j e a

theorem logarithmic_coeff (j : Fin 3) (p : Laurent (R := R)) (e : LaurentExponent) :
    (logarithmic R j p).coeff e = (e j : R) * p.coeff e := by
  classical
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hp, hq, mul_add]
  | single f a =>
      rw [logarithmic_single]
      change (Finsupp.single f ((f j : R)*a)) e =
        (e j : R) * (Finsupp.single f a) e
      by_cases h : f = e
      · subst f; simp
      · simp [h]

theorem logarithmic_commute (i j : Fin 3) :
    Function.Commute (logarithmic R i) (logarithmic R j) := by
  intro p
  apply AddMonoidAlgebra.coeff_injective
  ext e
  simp only [logarithmic_coeff]
  ring

@[simp] theorem logarithmic_constant (j : Fin 3) (p : Laurent (R := R)) :
    (logarithmic R j p).coeff 0 = 0 := by
  rw [logarithmic_coeff]
  simp

def polynomialLogarithmic (j : Fin 3) : Derivation R (Base R) (Base R) :=
  MvPolynomial.X j • MvPolynomial.pderiv j

theorem logarithmic_polynomial (j : Fin 3) (p : Base R) :
    logarithmic R j (baseToLaurent R p) =
      baseToLaurent R (polynomialLogarithmic R j p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial e a =>
      change logarithmic R j (baseToLaurent R (MvPolynomial.monomial e a)) =
        baseToLaurent R (MvPolynomial.X j * MvPolynomial.pderiv j (MvPolynomial.monomial e a))
      rw [MvPolynomial.X_mul_pderiv_monomial, map_nsmul,
        baseToLaurent_monomial, logarithmic_single, AddMonoidAlgebra.smul_single]
      simp only [castExponent_apply, Int.cast_natCast, nsmul_eq_mul]

/-- The same derivation on the actual localization of the three chart
coordinates used in `localizedBasis`. -/
def localizedLogarithmic (S : Finset (Fin 3)) (j : Fin 3) :
    Derivation R (coordinateLocalization R S) (coordinateLocalization R S) :=
  CycleQ2GeometricLocalizedDerivations.localizedBaseDerivation
    (Submonoid.powers (baseProduct R S)) (coordinateLocalization R S)
    (polynomialLogarithmic R j)

theorem localizedLogarithmic_algebraMap (S : Finset (Fin 3)) (j : Fin 3) (p : Base R) :
    localizedLogarithmic R S j (algebraMap (Base R) (coordinateLocalization R S) p) =
      algebraMap (Base R) (coordinateLocalization R S) (polynomialLogarithmic R j p) :=
  CycleQ2GeometricLocalizedDerivations.localizedBaseDerivation_algebraMap _ _ _ _

theorem localizationToLaurent_logarithmic (S : Finset (Fin 3)) (j : Fin 3)
    (p : coordinateLocalization R S) :
    logarithmic R j (localizationToLaurent R S p) =
      localizationToLaurent R S (localizedLogarithmic R S j p) := by
  apply CycleQ2GeometricLocalizedDerivations.derivation_commutes_of_algebraMap
    (Submonoid.powers (baseProduct R S))
    ((localizedLogarithmic R S j).restrictScalars ℤ)
    ((logarithmic R j).restrictScalars ℤ) (localizationToLaurent R S)
  intro a
  simp only [Derivation.restrictScalars_apply, localizedLogarithmic_algebraMap,
    localizationToLaurent_algebraMap, logarithmic_polynomial]

theorem localizedLogarithmic_commute (S : Finset (Fin 3)) (i j : Fin 3) :
    Function.Commute (localizedLogarithmic R S i) (localizedLogarithmic R S j) := by
  intro p
  apply localizationToLaurent_injective R S
  simp only [← localizationToLaurent_logarithmic]
  exact logarithmic_commute R i j _

@[simp] theorem localizedLogarithmic_constant (S : Finset (Fin 3)) (j : Fin 3)
    (p : coordinateLocalization R S) :
    (localizationToLaurent R S (localizedLogarithmic R S j p)).coeff 0 = 0 := by
  rw [← localizationToLaurent_logarithmic, logarithmic_constant]

end CycleQ2TorusLogDerivatives
end

#print axioms CycleQ2TorusLogDerivatives.localizationToLaurent_logarithmic
#print axioms CycleQ2TorusLogDerivatives.localizedLogarithmic_constant

/-! Finite cubic residue identities. The coefficient functional is the
third coordinate of an actual power basis, not a field trace or a
functional postulated to kill differentials. -/

noncomputable section
namespace CycleQ2CubicCoefficientTrace

open Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

def normal (w : B) (a : Fin 3 → A) : B :=
  algebraMap A B (a 0) + algebraMap A B (a 1) * w + algebraMap A B (a 2) * w^2

def top (b : Basis (Fin 3) A B) : B →ₗ[A] A := b.coord 2

variable (b : Basis (Fin 3) A B) (w : B) (hw : ∀ j, b j = w^j.val)

theorem normal_sum (a : Fin 3 → A) : normal w a = ∑ j, a j • b j := by
  simp only [normal, Fin.sum_univ_three, hw, Algebra.smul_def, pow_zero, pow_one,
    mul_one, Fin.val_zero, Fin.val_one, show (2 : Fin 3).val = 2 from rfl]

theorem normal_repr (x : B) : normal w (fun j => b.repr x j) = x := by
  rw [normal_sum b w hw]
  exact b.sum_repr x

theorem repr_normal (a : Fin 3 → A) (j : Fin 3) : b.repr (normal w a) j = a j := by
  classical
  rw [normal_sum b w hw]
  simp [map_sum, map_smul, Basis.repr_self, Finsupp.single_apply]

theorem top_normal (a : Fin 3 → A) : top b (normal w a) = a 2 :=
  repr_normal b w hw a 2

theorem normal_translate (u : A) (a : Fin 3 → A) :
    normal (w + algebraMap A B u) a =
      normal w ![a 0 + u*a 1 + u^2*a 2, a 1 + 2*u*a 2, a 2] := by
  simp [normal] <;> ring

/-- Translating the cubic root by a base coefficient preserves its top
power-basis coordinate. This includes the literal change z=w+x₂². -/
theorem top_translated_normal (u : A) (a : Fin 3 → A) :
    top b (normal (w + algebraMap A B u) a) = a 2 := by
  rw [normal_translate, top_normal b w hw]

theorem exists_translated_normal (u : A) (x : B) :
    ∃ a : Fin 3 → A, normal (w + algebraMap A B u) a = x := by
  let a := fun j => b.repr x j
  refine ⟨![a 0-u*a 1+u^2*a 2, a 1-2*u*a 2, a 2], ?_⟩
  rw [normal_translate]
  calc
    _ = normal w a := by
      apply congrArg (normal w)
      funext j
      fin_cases j <;> simp <;> ring
    _ = x := normal_repr b w hw x

private theorem top_power (j : Fin 3) :
    top b (w^j.val) = if j = 2 then 1 else 0 := by
  classical
  rw [← hw j]
  simp [top, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]

theorem top_one : top b 1 = 0 := by simpa using top_power b w hw 0
theorem top_root : top b w = 0 := by simpa using top_power b w hw 1
theorem top_square : top b (w^2) = 1 := by simpa using top_power b w hw 2

private theorem top_scalar_power (a : A) (n : ℕ) :
    top b (algebraMap A B a * w^n) = a * top b (w^n) := by
  simpa only [Algebra.smul_def, smul_eq_mul] using (top b).map_smul a (w^n)

variable (c : Fin 3 → A) (hc : w^3 = -normal w c)

theorem top_cube : top b (w^3) = -c 2 := by
  rw [hc, map_neg, top_normal b w hw]

theorem top_fourth : top b (w^4) = c 2 ^ 2 - c 1 := by
  have h4 : w^4 = -(algebraMap A B (c 0)*w^1 +
      algebraMap A B (c 1)*w^2 + algebraMap A B (c 2)*w^3) := by
    calc
      w^4 = w^3*w := by ring
      _ = _ := by rw [hc]; simp only [normal]; ring
  rw [h4, map_neg, map_add, map_add, top_scalar_power, top_scalar_power, top_scalar_power]
  simp only [pow_one, top_root b w hw, top_square b w hw, top_cube b w hw c hc]
  ring

/-- Multiplication followed by the genuine third power coordinate uses
only the reductions of w³ and w⁴. -/
theorem top_mul_normal (a d : Fin 3 → A) :
    top b (normal w a * normal w d) =
      a 0*d 2 + a 1*d 1 + a 2*d 0 -
        c 2*(a 1*d 2 + a 2*d 1) + (c 2^2-c 1)*a 2*d 2 := by
  have hmul : normal w a * normal w d =
      algebraMap A B (a 0*d 0)*w^0 +
      algebraMap A B (a 0*d 1+a 1*d 0)*w^1 +
      algebraMap A B (a 0*d 2+a 1*d 1+a 2*d 0)*w^2 +
      algebraMap A B (a 1*d 2+a 2*d 1)*w^3 +
      algebraMap A B (a 2*d 2)*w^4 := by
    simp only [normal, map_add, map_mul]
    ring
  rw [hmul]
  simp only [map_add, top_scalar_power, pow_zero, pow_one, top_one b w hw,
    top_root b w hw, top_square b w hw, top_cube b w hw c hc, top_fourth b w hw c hc]
  ring

def traceValue (a : Fin 3 → A) : A :=
  3*a 0-c 2*a 1+(c 2^2-2*c 1)*a 2

variable {k : Type*} [CommRing k] [Algebra k A]

/-- The coefficient of the derivative of a horizontal two-form is an
actual derivative in the base algebra. D acts on the three normal-form
coefficients and fixes the indeterminate w. -/
theorem horizontal_identity (D : Derivation k A A) (a : Fin 3 → A) :
    top b (normal w ![c 1,2*c 2,3] * normal w (D ∘ a) -
      normal w (D ∘ c) * normal w ![a 1,2*a 2,0]) = D (traceValue c a) := by
  rw [map_sub, top_mul_normal b w hw c hc, top_mul_normal b w hw c hc]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Function.comp_apply, traceValue, pow_two, map_sub, map_add,
    Derivation.leibniz, Derivation.map_natCast, smul_eq_mul]
  ring

/-- The corresponding coefficient identity for a two-form containing dw.
Mixed derivatives cancel because the two actual base derivations commute. -/
theorem mixed_identity (D E : Derivation k A A) (hDE : Function.Commute D E)
    (a : Fin 3 → A) :
    E (top b (normal w a * normal w (D ∘ c))) -
      D (top b (normal w a * normal w (E ∘ c))) =
    top b (normal w (E ∘ a) * normal w (D ∘ c) -
      normal w (D ∘ a) * normal w (E ∘ c)) := by
  simp only [map_sub, top_mul_normal b w hw c hc, Function.comp_apply, pow_two,
    map_add, Derivation.leibniz, smul_eq_mul, hDE]
  ring

end CycleQ2CubicCoefficientTrace
end

noncomputable section
namespace CycleQ2TorusCubicTrace

open Module Polynomial CycleQ2GeometricHodgeThreefoldCubic
open CycleQ2SeedCechLocalization CycleQ2SeedQuotientFiniteFree
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (vertexCoefficient)
open CycleQ2CubicCoefficientTrace (normal)

variable {R : Type} [CommRing R] [Nontrivial R]
  (φ : CoeffRing →+* R) (i : Fin 4) (h : IsUnit (φ vertexCoefficient))
  (S : Finset (Fin 3))

abbrev Coefficients := coordinateLocalization R S
abbrev Cubic := AwayStage φ i h (Submonoid.powers (baseProduct R S))

def powerBasis : Basis (Fin 3) (Coefficients (R := R) S) (Cubic φ i h S) :=
  localizedBasis φ i h (Submonoid.powers (baseProduct R S))

def root : Cubic φ i h S :=
  algebraMap (Stage φ i h) (Cubic φ i h S) (AdjoinRoot.root (cubic φ i h))

theorem powerBasis_apply (j : Fin 3) : powerBasis φ i h S j = (root φ i h S)^j.val := by
  simpa only [powerBasis, root, map_pow] using
    localizedBasis_apply φ i h (Submonoid.powers (baseProduct R S)) j

def coefficients (j : Fin 3) : Coefficients (R := R) S :=
  algebraMap (Base R) (Coefficients (R := R) S) ((cubic φ i h).coeff j.val)

/-- This is the relation of the original localized cubic, with its actual
lower coefficients. No squarefreeness or branch denominator is required. -/
theorem root_relation :
    (root φ i h S)^3 = -normal (root φ i h S) (coefficients φ i h S) := by
  let p := cubic φ i h
  have h3 : p.coeff 3 = 1 := by
    have hm := (cubic_monic φ i h).leadingCoeff
    change p.coeff p.natDegree = 1 at hm
    simpa only [p, cubic_natDegree] using hm
  have hp : p = ∑ j : Fin 4, Polynomial.C (p.coeff j.val) * Polynomial.X^j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => Polynomial.C (p.coeff j) * Polynomial.X^j)]
    exact p.as_sum_range_C_mul_X_pow' (by rw [show p.natDegree = 3 from cubic_natDegree φ i h]; decide)
  have hz : aeval (AdjoinRoot.root p)
      (∑ j : Fin 4, Polynomial.C (p.coeff j.val) * Polynomial.X^j.val) = 0 :=
    (congrArg (aeval (AdjoinRoot.root p)) hp).symm.trans (by simp)
  rw [Fin.sum_univ_four] at hz
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X,
    Fin.val_zero, Fin.val_one, show (2 : Fin 4).val = 2 from rfl,
    show (3 : Fin 4).val = 3 from rfl, h3, map_one, pow_zero, pow_one,
    one_mul, mul_one] at hz
  have hz' := congrArg (algebraMap (Stage φ i h) (Cubic φ i h S)) hz
  simp only [map_add, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply (Base R) (Stage φ i h) (Cubic φ i h S)] at hz'
  change (root φ i h S)^3 = -(algebraMap (Coefficients (R := R) S) (Cubic φ i h S)
    (coefficients φ i h S 0) + algebraMap (Coefficients (R := R) S) (Cubic φ i h S)
    (coefficients φ i h S 1) * root φ i h S +
    algebraMap (Coefficients (R := R) S) (Cubic φ i h S)
      (coefficients φ i h S 2) * (root φ i h S)^2)
  simp only [coefficients, ← IsScalarTower.algebraMap_apply]
  dsimp only [root, p] at hz' ⊢
  linear_combination hz'

/-- The third coordinate of the same localized power basis used by the
native projective torus chart. -/
def topCoefficient : Cubic φ i h S →ₗ[Coefficients (R := R) S] Coefficients (R := R) S :=
  (powerBasis φ i h S).coord 2

def logarithmicTrace : Cubic φ i h S →+ R where
  toFun a := (localizationToLaurent R S (topCoefficient φ i h S a)).coeff 0
  map_zero' := by simp [topCoefficient]
  map_add' a b := by simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

theorem horizontal_identity
    (D : Derivation R (Coefficients (R := R) S) (Coefficients (R := R) S))
    (a : Fin 3 → Coefficients (R := R) S) :
    topCoefficient φ i h S
      (normal (root φ i h S) ![coefficients φ i h S 1,2*coefficients φ i h S 2,3] *
        normal (root φ i h S) (D ∘ a) -
      normal (root φ i h S) (D ∘ coefficients φ i h S) *
        normal (root φ i h S) ![a 1,2*a 2,0]) =
      D (CycleQ2CubicCoefficientTrace.traceValue (coefficients φ i h S) a) :=
  CycleQ2CubicCoefficientTrace.horizontal_identity (powerBasis φ i h S) (root φ i h S)
    (powerBasis_apply φ i h S) (coefficients φ i h S) (root_relation φ i h S) D a

theorem logarithmicTrace_horizontal (j : Fin 3) (a : Fin 3 → Coefficients (R := R) S) :
    let D := CycleQ2TorusLogDerivatives.localizedLogarithmic R S j
    logarithmicTrace φ i h S
      (normal (root φ i h S) ![coefficients φ i h S 1,2*coefficients φ i h S 2,3] *
        normal (root φ i h S) (D ∘ a) -
      normal (root φ i h S) (D ∘ coefficients φ i h S) *
        normal (root φ i h S) ![a 1,2*a 2,0]) = 0 := by
  dsimp only
  change (localizationToLaurent R S (topCoefficient φ i h S _)).coeff 0 = 0
  rw [horizontal_identity, CycleQ2TorusLogDerivatives.localizedLogarithmic_constant]

theorem logarithmicTrace_mixed (j k : Fin 3) (a : Fin 3 → Coefficients (R := R) S) :
    let D := CycleQ2TorusLogDerivatives.localizedLogarithmic R S j
    let E := CycleQ2TorusLogDerivatives.localizedLogarithmic R S k
    logarithmicTrace φ i h S
      (normal (root φ i h S) (E ∘ a) * normal (root φ i h S) (D ∘ coefficients φ i h S) -
        normal (root φ i h S) (D ∘ a) * normal (root φ i h S) (E ∘ coefficients φ i h S)) = 0 := by
  dsimp only
  let D := CycleQ2TorusLogDerivatives.localizedLogarithmic R S j
  let E := CycleQ2TorusLogDerivatives.localizedLogarithmic R S k
  have hm := CycleQ2CubicCoefficientTrace.mixed_identity (powerBasis φ i h S) (root φ i h S)
    (powerBasis_apply φ i h S) (coefficients φ i h S) (root_relation φ i h S) D E
    (CycleQ2TorusLogDerivatives.localizedLogarithmic_commute R S j k) a
  change (localizationToLaurent R S (CycleQ2CubicCoefficientTrace.top (powerBasis φ i h S) _)).coeff 0 = 0
  rw [← hm, map_sub]
  change (localizationToLaurent R S (E _) ).coeff 0 -
    (localizationToLaurent R S (D _) ).coeff 0 = 0
  rw [CycleQ2TorusLogDerivatives.localizedLogarithmic_constant,
    CycleQ2TorusLogDerivatives.localizedLogarithmic_constant, sub_self]

end CycleQ2TorusCubicTrace
end

#print axioms CycleQ2TorusCubicTrace.root_relation
#print axioms CycleQ2TorusCubicTrace.logarithmicTrace_horizontal
#print axioms CycleQ2TorusCubicTrace.logarithmicTrace_mixed

/-! Ordinary coordinate derivatives on the same Laurent chart.  Their
coefficient at (-1,-1,-1) vanishes.  This is the normalization appropriate
for the original residue volume and exact coordinate two-wedges. -/

noncomputable section
namespace CycleQ2TorusLogDerivatives

open CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
open CycleQ2SeedQuotientFiniteFree (Base)

variable (R : Type*) [CommRing R]

def partial (j : Fin 3) : Derivation R (Laurent (R := R)) (Laurent (R := R)) :=
  T R (-openExponent {j}) • logarithmic R j

theorem partial_coeff (j : Fin 3) (p : Laurent (R := R)) (e : LaurentExponent) :
    (partial R j p).coeff e =
      ((e j + 1 : ℤ) : R) * p.coeff (e + openExponent {j}) := by
  change (T R (-openExponent {j}) * logarithmic R j p).coeff e = _
  rw [mul_comm, coeff_mul_T, sub_neg_eq_add, logarithmic_coeff]
  simp only [Pi.add_apply, openExponent, Finset.mem_singleton, if_pos rfl]

theorem partial_polynomial (j : Fin 3) (p : Base R) :
    partial R j (baseToLaurent R p) = baseToLaurent R (MvPolynomial.pderiv j p) := by
  change T R (-openExponent {j}) * logarithmic R j (baseToLaurent R p) = _
  rw [logarithmic_polynomial]
  change T R (-openExponent {j}) *
    baseToLaurent R (MvPolynomial.X j * MvPolynomial.pderiv j p) = _
  rw [map_mul, baseToLaurent_X, ← mul_assoc, T_mul, neg_add_cancel, T_zero, one_mul]

theorem partial_commute (i j : Fin 3) : Function.Commute (partial R i) (partial R j) := by
  intro p
  apply AddMonoidAlgebra.coeff_injective
  ext e
  simp only [partial_coeff, Pi.add_apply]
  have hshift : (e + openExponent {i}) + openExponent {j} =
      (e + openExponent {j}) + openExponent {i} := by abel
  rw [hshift]
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [openExponent, Finset.mem_singleton, if_neg hij, if_neg hij.symm,
      add_zero]
    ring

@[simp] theorem partial_residue (j : Fin 3) (p : Laurent (R := R)) :
    (partial R j p).coeff (fun _ => -1) = 0 := by
  rw [partial_coeff]
  simp

/-- The actual extension of the polynomial coordinate partial to the
same base-product localization used by the cubic power basis. -/
def localizedPartial (S : Finset (Fin 3)) (j : Fin 3) :
    Derivation R (coordinateLocalization R S) (coordinateLocalization R S) :=
  CycleQ2GeometricLocalizedDerivations.localizedBaseDerivation
    (Submonoid.powers (baseProduct R S)) (coordinateLocalization R S)
    (MvPolynomial.pderiv j)

theorem localizedPartial_algebraMap (S : Finset (Fin 3)) (j : Fin 3) (p : Base R) :
    localizedPartial R S j (algebraMap (Base R) (coordinateLocalization R S) p) =
      algebraMap (Base R) (coordinateLocalization R S) (MvPolynomial.pderiv j p) :=
  CycleQ2GeometricLocalizedDerivations.localizedBaseDerivation_algebraMap _ _ _ _

theorem localizationToLaurent_partial (S : Finset (Fin 3)) (j : Fin 3)
    (p : coordinateLocalization R S) :
    partial R j (localizationToLaurent R S p) =
      localizationToLaurent R S (localizedPartial R S j p) := by
  apply CycleQ2GeometricLocalizedDerivations.derivation_commutes_of_algebraMap
    (Submonoid.powers (baseProduct R S))
    ((localizedPartial R S j).restrictScalars ℤ)
    ((partial R j).restrictScalars ℤ) (localizationToLaurent R S)
  intro a
  simp only [Derivation.restrictScalars_apply, localizedPartial_algebraMap,
    localizationToLaurent_algebraMap, partial_polynomial]

theorem localizedPartial_commute (S : Finset (Fin 3)) (i j : Fin 3) :
    Function.Commute (localizedPartial R S i) (localizedPartial R S j) := by
  intro p
  apply localizationToLaurent_injective R S
  simp only [← localizationToLaurent_partial]
  exact partial_commute R i j _

@[simp] theorem localizedPartial_residue (S : Finset (Fin 3)) (j : Fin 3)
    (p : coordinateLocalization R S) :
    (localizationToLaurent R S (localizedPartial R S j p)).coeff (fun _ => -1) = 0 := by
  rw [← localizationToLaurent_partial, partial_residue]

end CycleQ2TorusLogDerivatives
end

#print axioms CycleQ2TorusLogDerivatives.localizedPartial_algebraMap
#print axioms CycleQ2TorusLogDerivatives.localizedPartial_residue

noncomputable section
namespace CycleQ2CubicCoefficientTrace

open Module

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  (b : Basis (Fin 3) A B) (w : B) (hw : ∀ j, b j = w^j.val)

/-- The translated quadratic normal form is an actual linear
equivalence, without dividing by the cubic derivative. -/
def translatedEquiv (u : A) : (Fin 3 → A) ≃ₗ[A] B where
  toFun a := normal (w + algebraMap A B u) a
  invFun x := ![b.repr x 0 - u*b.repr x 1 + u^2*b.repr x 2,
    b.repr x 1 - 2*u*b.repr x 2, b.repr x 2]
  left_inv a := by
    rw [normal_translate]
    funext j
    fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, repr_normal b w hw] <;> ring
  right_inv x := by
    rw [normal_translate]
    calc
      _ = normal w (fun j => b.repr x j) := by
        congr 1
        funext j
        fin_cases j <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two] <;> ring
      _ = x := normal_repr b w hw x
  map_add' a d := by
    simp only [normal, Pi.add_apply, map_add]
    ring
  map_smul' r a := by
    simp only [normal, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
    ring

def translatedBasis (u : A) : Basis (Fin 3) A B :=
  Basis.ofEquivFun (translatedEquiv b w hw u).symm

theorem translatedBasis_apply (u : A) (j : Fin 3) :
    translatedBasis b w hw u j = (w + algebraMap A B u)^j.val := by
  rw [show translatedBasis b w hw u j =
      (translatedEquiv b w hw u) (Pi.single j 1) from
    congrFun (Basis.coe_ofEquivFun (translatedEquiv b w hw u).symm) j]
  change normal (w + algebraMap A B u) (Pi.single j 1) = _
  fin_cases j <;> simp [normal, Pi.single_apply]

/-- Translation does not alter the top cubic-coordinate functional. -/
theorem top_translatedBasis (u : A) (x : B) :
    top (translatedBasis b w hw u) x = top b x := by
  obtain ⟨a,rfl⟩ := (translatedEquiv b w hw u).surjective x
  change top (translatedBasis b w hw u) (normal (w + algebraMap A B u) a) =
    top b (normal (w + algebraMap A B u) a)
  rw [top_normal (translatedBasis b w hw u) (w + algebraMap A B u)
    (translatedBasis_apply b w hw u), top_translated_normal b w hw]

end CycleQ2CubicCoefficientTrace
end

#print axioms CycleQ2CubicCoefficientTrace.translatedBasis_apply
#print axioms CycleQ2CubicCoefficientTrace.top_translatedBasis

noncomputable section
namespace CycleQ2TorusLogDerivatives

open CycleQ2SeedCechLocalization
open CycleQ2SeedQuotientFiniteFree (Base)

variable (R : Type*) [CommRing R] (S : Finset (Fin 3))

private theorem differential_polynomial (p : Base R) :
    KaehlerDifferential.D R (coordinateLocalization R S)
        (algebraMap (Base R) (coordinateLocalization R S) p) =
      ∑ j : Fin 3,
        algebraMap (Base R) (coordinateLocalization R S) (MvPolynomial.pderiv j p) •
          KaehlerDifferential.D R (coordinateLocalization R S)
            (algebraMap (Base R) (coordinateLocalization R S) (MvPolynomial.X j)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
      simp only [map_mul, Derivation.leibniz, hp, smul_eq_mul, map_add,
        MvPolynomial.pderiv_X, add_smul, Finset.sum_add_distrib, mul_smul]
      simp [Pi.single_apply, Finset.smul_sum]

/-- The universal differential on the actual base localization is the
sum of its three ordinary coordinate partials. -/
theorem localized_differential (a : coordinateLocalization R S) :
    KaehlerDifferential.D R (coordinateLocalization R S) a =
      ∑ j : Fin 3, localizedPartial R S j a •
        KaehlerDifferential.D R (coordinateLocalization R S)
          (algebraMap (Base R) (coordinateLocalization R S) (MvPolynomial.X j)) := by
  let L := coordinateLocalization R S
  let x := fun j : Fin 3 => algebraMap (Base R) L (MvPolynomial.X j)
  obtain ⟨⟨p,s⟩,hs⟩ := IsLocalization.surj (Submonoid.powers (baseProduct R S)) a
  have hd := congrArg (KaehlerDifferential.D R L) hs
  rw [Derivation.leibniz] at hd
  have he : algebraMap (Base R) L s • KaehlerDifferential.D R L a =
      KaehlerDifferential.D R L (algebraMap (Base R) L p) -
        a • KaehlerDifferential.D R L (algebraMap (Base R) L s) :=
    eq_sub_of_add_eq (by simpa only [add_comm] using hd)
  have hp (j : Fin 3) :
      algebraMap (Base R) L (MvPolynomial.pderiv j p) -
          a * algebraMap (Base R) L (MvPolynomial.pderiv j (s : Base R)) =
        algebraMap (Base R) L s * localizedPartial R S j a := by
    have h := congrArg (localizedPartial R S j) hs
    simp only [Derivation.leibniz, smul_eq_mul, localizedPartial_algebraMap] at h
    exact (eq_sub_of_add_eq (by simpa only [add_comm] using h)).symm
  apply (IsUnit.smul_left_cancel (IsLocalization.map_units L s)).mp
  calc
    algebraMap (Base R) L s • KaehlerDifferential.D R L a =
        KaehlerDifferential.D R L (algebraMap (Base R) L p) -
          a • KaehlerDifferential.D R L (algebraMap (Base R) L s) := he
    _ = ∑ j : Fin 3,
        (algebraMap (Base R) L (MvPolynomial.pderiv j p) -
          a * algebraMap (Base R) L (MvPolynomial.pderiv j (s : Base R))) •
            KaehlerDifferential.D R L (x j) := by
      rw [differential_polynomial, differential_polynomial, Finset.smul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [sub_smul, mul_smul]
    _ = algebraMap (Base R) L s •
        ∑ j : Fin 3, localizedPartial R S j a • KaehlerDifferential.D R L (x j) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [hp, mul_smul]

theorem localized_differential_map {B : Type*} [CommRing B] [Algebra R B]
    [Algebra (coordinateLocalization R S) B] [IsScalarTower R (coordinateLocalization R S) B]
    (a : coordinateLocalization R S) :
    KaehlerDifferential.D R B (algebraMap (coordinateLocalization R S) B a) =
      ∑ j : Fin 3, algebraMap (coordinateLocalization R S) B (localizedPartial R S j a) •
        KaehlerDifferential.D R B
          (algebraMap (coordinateLocalization R S) B
            (algebraMap (Base R) (coordinateLocalization R S) (MvPolynomial.X j))) := by
  have h := congrArg (KaehlerDifferential.map R R (coordinateLocalization R S) B)
    (localized_differential R S a)
  simpa only [KaehlerDifferential.map_D, map_sum, map_smul,
    IsScalarTower.algebraMap_smul] using h

end CycleQ2TorusLogDerivatives

namespace CycleQ2TorusCubicTrace

open CycleQ2SeedCechLocalization
open CycleQ2SeedQuotientFiniteFree (Base)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (vertexCoefficient)
open CycleQ2CubicCoefficientTrace (normal)

variable {R : Type} [CommRing R] [Nontrivial R]
  (φ : CoeffRing →+* R) (i : Fin 4) (h : IsUnit (φ vertexCoefficient))
  (S : Finset (Fin 3))

/-- Differentiating the actual finite cubic normal form separates the
normal derivative and the three base-coordinate derivatives. -/
theorem normal_differential (z : Cubic φ i h S) (a : Fin 3 → Coefficients (R := R) S) :
    KaehlerDifferential.D R (Cubic φ i h S) (normal z a) =
      normal z ![a 1, 2*a 2, 0] • KaehlerDifferential.D R (Cubic φ i h S) z +
        ∑ j : Fin 3,
          normal z ((CycleQ2TorusLogDerivatives.localizedPartial R S j) ∘ a) •
            KaehlerDifferential.D R (Cubic φ i h S)
              (algebraMap (Coefficients (R := R) S) (Cubic φ i h S)
                (algebraMap (Base R) (Coefficients (R := R) S) (MvPolynomial.X j))) := by
  simp only [normal, map_add, Derivation.leibniz, Derivation.leibniz_pow,
    CycleQ2TorusLogDerivatives.localized_differential_map, Fin.sum_univ_three,
    Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, map_zero, map_mul, map_ofNat, zero_mul, add_zero,
    show 2 - 1 = 1 from rfl, pow_one]
  module

/-- The ordinary residue coefficient in the original cubic power basis. -/
def residueTrace : Cubic φ i h S →+ R where
  toFun a := (localizationToLaurent R S (topCoefficient φ i h S a)).coeff (fun _ => -1)
  map_zero' := by simp [topCoefficient]
  map_add' a b := by simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

end CycleQ2TorusCubicTrace
end

#print axioms CycleQ2TorusLogDerivatives.localized_differential
#print axioms CycleQ2TorusCubicTrace.normal_differential

noncomputable section
namespace CycleQ2TorusCubicTrace

open CycleQ2SeedCechLocalization
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (vertexCoefficient)
open CycleQ2CubicCoefficientTrace (normal)
open CycleQ2TorusLogDerivatives (localizedPartial localizedPartial_commute localizedPartial_residue)

variable {R : Type} [CommRing R] [Nontrivial R]
  (φ : CoeffRing →+* R) (i : Fin 4) (h : IsUnit (φ vertexCoefficient))
  (S : Finset (Fin 3))

/-- The ordinary residue, in the original monic cubic power basis,
annihilates the normal/base-coordinate derivative cross-term. -/
theorem residueTrace_horizontal (j : Fin 3) (a : Fin 3 → Coefficients (R := R) S) :
    let D := localizedPartial R S j
    residueTrace φ i h S
      (normal (root φ i h S) ![coefficients φ i h S 1,2*coefficients φ i h S 2,3] *
        normal (root φ i h S) (D ∘ a) -
       normal (root φ i h S) (D ∘ coefficients φ i h S) *
        normal (root φ i h S) ![a 1,2*a 2,0]) = 0 := by
  dsimp only
  change (localizationToLaurent R S (topCoefficient φ i h S _)).coeff (fun _ => -1) = 0
  rw [horizontal_identity,localizedPartial_residue]

/-- The same actual residue annihilates the two-base-coordinate
cross-term. Commutation is supplied by the original localized partials. -/
theorem residueTrace_mixed (j k : Fin 3) (a : Fin 3 → Coefficients (R := R) S) :
    let D := localizedPartial R S j
    let E := localizedPartial R S k
    residueTrace φ i h S
      (normal (root φ i h S) (E ∘ a) * normal (root φ i h S) (D ∘ coefficients φ i h S) -
       normal (root φ i h S) (D ∘ a) * normal (root φ i h S) (E ∘ coefficients φ i h S)) = 0 := by
  dsimp only
  let D := localizedPartial R S j
  let E := localizedPartial R S k
  have hm := CycleQ2CubicCoefficientTrace.mixed_identity (powerBasis φ i h S) (root φ i h S)
    (powerBasis_apply φ i h S) (coefficients φ i h S) (root_relation φ i h S) D E
    (localizedPartial_commute R S j k) a
  change (localizationToLaurent R S (CycleQ2CubicCoefficientTrace.top (powerBasis φ i h S) _)).coeff
    (fun _ => -1) = 0
  rw [← hm,map_sub]
  change (localizationToLaurent R S (E _)).coeff (fun _ => -1) -
    (localizationToLaurent R S (D _)).coeff (fun _ => -1) = 0
  rw [localizedPartial_residue,localizedPartial_residue,sub_self]

end CycleQ2TorusCubicTrace
end

#print axioms CycleQ2TorusCubicTrace.residueTrace_horizontal
#print axioms CycleQ2TorusCubicTrace.residueTrace_mixed
