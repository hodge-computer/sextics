import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import HodgeTarget
import Proposal.GeometricTarget
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs
import Proposal.Normalization
import Proposal.SolutionSupport08

/-! Source partition of Solution.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_20261112/IncidenceTraceCharacterComponent.lean -/
section
/-!
# Character-one cohomology on the actual pointed incidence component

The actual coefficient ring, preserved geometric open, generic embedding,
and seed specialization are the previously checked constructions.  Only
the specified character of the actual Cech complex changes.  Character one
has rank eight and is the piece paired with the character-two canonical
residue of an invariant cubic.

Persistence below is conditional on an actual class and its nonzero seed
image.  It does not construct the geometric ambient-test class or identify
that class with the seed normal/residue calculation.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceTraceCharacterComponent

open MvPolynomial Matrix CycleQ2IncidenceNormalForm
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SegreFullJacobianBounds
  CycleQ2IncidenceTraceFamily CycleQ2IncidenceTraceGenericPoint
  CycleQ2IncidenceTraceComponent CycleQ2UniversalSurfaceCharacterCech
  CycleQ2UniversalSurfaceCharacterPersistence
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

variable {S : Type} [CommRing S] [Nontrivial S] [Algebra ℂ S]
  [Algebra TraceRing S] [IsScalarTower ℂ TraceRing S]

variable (P : Matrix SquareIndex ColumnIndex ℂ)
  (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
  (z : SquareIndex → S) (hz : IsPointedTracePoint P B c z) (χ : ZMod 3)

abbrev CharacterComponentTopCech :=
  ActualTopCechQuotient (ComponentRing P B c z hz) χ
    (componentCubic P B c z hz) (componentSextic P B c z hz)

theorem componentTop_generic_injective :
    Function.Injective (actualTopMap χ (componentGeneric P B c z hz)
      (componentCubic P B c z hz) (componentSextic P B c z hz)) :=
  actualTopMap_injective χ _ (componentGeneric_injective P B c z hz) _ _

theorem componentTop_nonzero
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1)
    (ξ : CharacterComponentTopCech P B c z hz χ)
    (hξ : actualTopMap χ (componentSeed P B c z hz hc)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0) :
    actualTopMap χ (componentGeneric P B c z hz)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0 := by
  intro hzero
  have hξzero : ξ = 0 := (componentTop_generic_injective P B c z hz χ)
    (hzero.trans (map_zero _).symm)
  exact hξ (by rw [hξzero, map_zero])

theorem characterOne_rank_eight :
    Module.finrank (ComponentRing P B c z hz)
      (CharacterComponentTopCech P B c z hz (1 : ZMod 3)) = 8 :=
  actualTop_rank_characterOne (ComponentRing P B c z hz)
    (componentCubic P B c z hz) (componentSextic P B c z hz)

theorem characterOne_nonzero
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1)
    (ξ : CharacterComponentTopCech P B c z hz (1 : ZMod 3))
    (hξ : actualTopMap (1 : ZMod 3) (componentSeed P B c z hz hc)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0) :
    actualTopMap (1 : ZMod 3) (componentGeneric P B c z hz)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0 :=
  componentTop_nonzero P B c z hz (1 : ZMod 3) hc ξ hξ

end CycleQ2IncidenceTraceCharacterComponent

#print axioms CycleQ2IncidenceTraceCharacterComponent.characterOne_rank_eight
#print axioms CycleQ2IncidenceTraceCharacterComponent.characterOne_nonzero
end
end


/- Uncompiled continuation: OrbitTraceBridge.lean (2026-11-12). -/
section Q2UncompiledOrbitTrace

/-!
# The actual cyclic action and the character-one orbit trace

Development continuation; compilation status is recorded in solution.md.
Written against the source snapshot at commit 8d88f06, this component is
integrated before the nonconstructive endpoint in `Solution.lean`.

The localization statements below concern the existing, literal diagonal
action on the seed quotient and its actual coordinate localizations. In
particular, the character is proved from the homogeneous-fraction theorem;
it is not imposed by defining the action to be scalar multiplication.

The final trace statements are algebraic. They do not construct the missing
semiregularity map from `CycleQ2ActualNormalCech.NormalCech` to the surface
character-one top Cech quotient. They also do not identify an arbitrary
linear functional with Serre duality or Abel--Jacobi. That geometric map,
its covariance for the fixed ambient test, and its pairing comparison are
still needed before applying these lemmas to the computed normal class.

No theorem below uses `Submission.missing_geometric_existence`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2OrbitTraceBridge

section LinearOrbit

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- For a fixed ambient test of character `zeta`, the three responses use
the inverse characters: `v + zeta^2 g(v) + zeta g^2(v)`. -/
def twistedOrbit (ζ : R) (g : V →ₗ[R] V) (v : V) : V :=
  v + ζ ^ 2 • g v + ζ • g (g v)

/-- On the character-one eigenspace, the correctly twisted orbit is three
times the class. An untwisted orbit does not have this property. -/
theorem twistedOrbit_eq_three_smul (ζ : R) (hζ : ζ ^ 3 = 1)
    (g : V →ₗ[R] V) (v : V) (hv : g v = ζ • v) :
    twistedOrbit ζ g v = (3 : R) • v := by
  have hc : 1 + ζ ^ 2 * ζ + ζ * (ζ * ζ) = (3 : R) := by
    linear_combination 2 * hζ
  unfold twistedOrbit
  simp only [hv, map_smul]
  calc
    v + ζ ^ 2 • (ζ • v) + ζ • (ζ • (ζ • v)) =
        (1 + ζ ^ 2 * ζ + ζ * (ζ * ζ)) • v := by
      simp only [add_smul, smul_smul, one_smul]
    _ = (3 : R) • v := by rw [hc]

/-- The dual character is sufficient: the original class need not itself
already lie in the character-one eigenspace. -/
theorem pairing_twistedOrbit (ζ : R) (hζ : ζ ^ 3 = 1)
    (g : V →ₗ[R] V) (φ : V →ₗ[R] R)
    (hφ : ∀ v, φ (g v) = ζ * φ v) (v : V) :
    φ (twistedOrbit ζ g v) = 3 * φ v := by
  simp only [twistedOrbit, map_add, map_smul, hφ, smul_eq_mul]
  linear_combination (2 * φ v) * hζ

/-- The inverse-character factor is necessary: the ordinary orbit kills
a character-one vector for a primitive cube root. -/
theorem untwistedOrbit_eq_zero (ζ : R) (hζ : ζ ^ 2 + ζ + 1 = 0)
    (g : V →ₗ[R] V) (v : V) (hv : g v = ζ • v) :
    v + g v + g (g v) = 0 := by
  have hc : 1 + ζ + ζ * ζ = 0 := by
    linear_combination hζ
  simp only [hv, map_smul]
  calc
    v + ζ • v + ζ • (ζ • v) = (1 + ζ + ζ * ζ) • v := by
      simp only [add_smul, smul_smul, one_smul]
    _ = 0 := by rw [hc, zero_smul]

end LinearOrbit

section DualCharacter

variable {R V W : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- An invariant bilinear pairing against a character-two test vector has
the dual character required by `pairing_twistedOrbit`. This is an algebraic
identity; no geometric Serre pairing is introduced or assumed to exist. -/
theorem dualCharacter_of_invariantPairing (ζ : R) (hζ : ζ ^ 3 = 1)
    (g : V →ₗ[R] V) (h : W →ₗ[R] W) (P : V →ₗ[R] W →ₗ[R] R)
    (hP : ∀ v w, P (g v) (h w) = P v w)
    (w : W) (hw : h w = ζ ^ 2 • w) :
    ∀ v, P (g v) w = ζ * P v w := by
  intro v
  have he := hP v w
  rw [hw, map_smul, smul_eq_mul] at he
  have hc : ζ * ζ ^ 2 = 1 := by
    linear_combination hζ
  calc
    P (g v) w = (ζ * ζ ^ 2) * P (g v) w := by rw [hc, one_mul]
    _ = ζ * (ζ ^ 2 * P (g v) w) := by ring
    _ = ζ * P v w := by rw [he]

end DualCharacter

section NonzeroPairing

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pairing_twistedOrbit_ne_zero (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (g : V →ₗ[ℂ] V) (φ : V →ₗ[ℂ] ℂ)
    (hφ : ∀ v, φ (g v) = ζ * φ v) (v : V) (hv : φ v ≠ 0) :
    φ (twistedOrbit ζ g v) ≠ 0 := by
  rw [pairing_twistedOrbit ζ hζ g φ hφ]
  exact mul_ne_zero (by norm_num) hv

theorem twistedOrbit_ne_zero_of_pairing (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (g : V →ₗ[ℂ] V) (φ : V →ₗ[ℂ] ℂ)
    (hφ : ∀ v, φ (g v) = ζ * φ v) (v : V) (hv : φ v ≠ 0) :
    twistedOrbit ζ g v ≠ 0 := by
  intro hz
  have h := pairing_twistedOrbit_ne_zero ζ hζ g φ hφ v hv
  apply h
  rw [hz, map_zero]

end NonzeroPairing

section ActualLocalization

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
open CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
open CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions
open CycleQ2SeedQuotientGrading CycleQ2SeedCyclicAction
open CycleQ2SeedCyclicLocalization

variable {R : Type*} [CommRing R]

/-- The actual localization action fixes the coefficient ring. -/
theorem localAction_scalar (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (s : Finset (Fin 3)) (c : R) :
    localAction ζ hζ r ι s (algebraMap R (SeedLocal R r ι s) c) =
      algebraMap R (SeedLocal R r ι s) c := by
  rw [IsScalarTower.algebraMap_apply R (SeedRing r ι) (SeedLocal R r ι s)]
  change localAction ζ hζ r ι s
      (algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (C c))) =
    algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (C c))
  rw [localAction_mk, polynomialAction_C]

/-- The existing ring action, with its proved coefficient linearity. -/
def localLinearAction (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (s : Finset (Fin 3)) : SeedLocal R r ι s →ₗ[R] SeedLocal R r ι s where
  __ := (localAction ζ hζ r ι s).toAddMonoidHom
  map_smul' c q := by
    simp only [Algebra.smul_def, map_mul, localAction_scalar]

@[simp] theorem localLinearAction_apply (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (s : Finset (Fin 3)) (q : SeedLocal R r ι s) :
    localLinearAction ζ hζ r ι s q = localAction ζ hζ r ι s q := rfl

/-- The triple-open denominator is `x1*x2*x3`, of trivial character. -/
theorem baseFactor_univ (ζ : R) (hζ : ζ ^ 3 = 1) :
    baseFactor ζ (Finset.univ : Finset (Fin 3)) = 1 := by
  calc
    baseFactor ζ (Finset.univ : Finset (Fin 3)) = ζ ^ 2 * ζ := by
      simp [baseFactor, baseScalars, Fin.prod_univ_succ]
    _ = ζ ^ 3 := by ring
    _ = 1 := hζ

/-- Arbitrary powers of that denominator add no character to a fraction. -/
theorem tripleDenominator_character (n : ℕ) :
    (baseGrade (n • openExponent (Finset.univ : Finset (Fin 3)))).2 = 0 := by
  have hb : (baseGrade (openExponent (Finset.univ : Finset (Fin 3)))).2 = 0 := by
    norm_num [baseGrade, openExponent]
  rw [map_nsmul]
  change n • (baseGrade (openExponent (Finset.univ : Finset (Fin 3)))).2 = 0
  rw [hb, nsmul_zero]

/-- Every genuinely homogeneous section on the actual triple localization
has its declared eigenvalue under the existing diagonal action. -/
theorem localAction_triple_homogeneous [Nontrivial R]
    (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (q : SeedLocal R r ι Finset.univ) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g
      (localizedCoordinates R r ι Finset.univ q ab)) :
    localAction ζ hζ r ι Finset.univ q = ζ ^ g.2.val • q := by
  obtain ⟨n, p, hp, hfrac⟩ :=
    (localized_homogeneous_iff_fraction R r ι Finset.univ q g).mp hq
  let φ := algebraMap (SeedRing r ι) (SeedLocal R r ι Finset.univ)
  let π := Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
  let den := φ (algebraMap (Base R) (SeedRing r ι)
    (baseProduct R (Finset.univ : Finset (Fin 3)) ^ n))
  have hden : IsUnit den := by
    dsimp [den, φ]
    simpa only [map_pow] using
      (seedProduct_isUnit R r ι (Finset.Subset.refl Finset.univ)).pow n
  have hden_fixed : localAction ζ hζ r ι Finset.univ den = den := by
    dsimp [den, φ]
    simp only [map_pow, localAction_algebraMap, seedAction_baseProduct,
      baseFactor_univ ζ hζ, map_one, one_mul]
  have hchar : (g + baseGrade
      (n • openExponent (Finset.univ : Finset (Fin 3)))).2 = g.2 := by
    change g.2 + (baseGrade
      (n • openExponent (Finset.univ : Finset (Fin 3)))).2 = g.2
    rw [tripleDenominator_character, add_zero]
  change q * den = φ (π p) at hfrac
  have he := congrArg (localAction ζ hζ r ι Finset.univ) hfrac
  rw [map_mul, hden_fixed, localAction_mk,
    polynomialAction_signedHomogeneous ζ hζ p _ hp, hchar, map_mul, map_mul] at he
  change localAction ζ hζ r ι Finset.univ q * den =
    φ (π (C (ζ ^ g.2.val))) * φ (π p) at he
  rw [← hfrac] at he
  obtain ⟨u, hu⟩ := hden
  have he' := congrArg
    (fun z : SeedLocal R r ι Finset.univ => z * (↑(u⁻¹) : SeedLocal R r ι Finset.univ)) he
  rw [← hu] at he'
  have hcancel : localAction ζ hζ r ι Finset.univ q =
      φ (π (C (ζ ^ g.2.val))) * q := by
    simpa only [mul_assoc, u.mul_inv, mul_one] using he'
  rw [Algebra.smul_def,
    IsScalarTower.algebraMap_apply R (SeedRing r ι) (SeedLocal R r ι Finset.univ)]
  exact hcancel

/-- In particular the actual character-one triple sections have eigenvalue
`zeta`; this is the character required by the ambient test. -/
theorem localLinearAction_characterOne [Nontrivial R]
    (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (q : SeedLocal R r ι Finset.univ)
    (hq : ∀ ab, HasGrade ab (0, (1 : ZMod 3))
      (localizedCoordinates R r ι Finset.univ q ab)) :
    localLinearAction ζ hζ r ι Finset.univ q = ζ • q := by
  simpa using localAction_triple_homogeneous ζ hζ r ι q
    (0, (1 : ZMod 3)) hq

theorem actual_triple_twistedOrbit_eq_three_smul [Nontrivial R]
    (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (q : SeedLocal R r ι Finset.univ)
    (hq : ∀ ab, HasGrade ab (0, (1 : ZMod 3))
      (localizedCoordinates R r ι Finset.univ q ab)) :
    twistedOrbit ζ (localLinearAction ζ hζ r ι Finset.univ) q = (3 : R) • q :=
  twistedOrbit_eq_three_smul ζ hζ _ q
    (localLinearAction_characterOne ζ hζ r ι q hq)

end ActualLocalization

section ActualAmbientTest

open MvPolynomial CycleQ2SeedCyclicAction CycleQ2SeedCyclicLocalization
open CycleQ2IncidenceEquations CycleQ2SegreTangentLocal
open CycleQ2SeedCechLocalizedBasis

/-- The external test used by the normal connecting class has character
one under the literal polynomial action. -/
theorem polynomialAction_ambientTest (ζ : ℂ) :
    polynomialAction ζ CycleQ2NormalConnecting.derivativeA =
      C ζ * CycleQ2NormalConnecting.derivativeA := by
  simp only [CycleQ2NormalConnecting.derivativeA, map_mul, map_pow,
    polynomialAction_X]
  change (C ζ * X 2) * (X 3) ^ 3 * X 4 =
    C ζ * (X 2 * X 3 ^ 3 * X 4)
  ring

/-- The same equality holds on every actual seed coordinate localization. -/
theorem localAction_ambientTest (ζ : ℂ) (hζ : ζ ^ 3 = 1) (r ι : ℂ)
    (s : Finset (Fin 3)) :
    localAction ζ hζ r ι s
      (algebraMap (SeedRing r ι) (SeedLocal ℂ r ι s)
        (Ideal.Quotient.mk (CycleQ2IncidenceNormalForm.equationsIdeal
          (smoothH ι) (smoothF r ι)) CycleQ2NormalConnecting.derivativeA)) =
      ζ • algebraMap (SeedRing r ι) (SeedLocal ℂ r ι s)
        (Ideal.Quotient.mk (CycleQ2IncidenceNormalForm.equationsIdeal
          (smoothH ι) (smoothF r ι)) CycleQ2NormalConnecting.derivativeA) := by
  rw [localAction_mk, polynomialAction_ambientTest, map_mul, map_mul,
    Algebra.smul_def,
    IsScalarTower.algebraMap_apply ℂ (SeedRing r ι) (SeedLocal ℂ r ι s)]
  rfl

end ActualAmbientTest

section ActualNonzeroPairing

open CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis

/-- This is an application to the actual localization action. The remaining
geometric task is to supply the ambient-test class and its genuine trace
functional, rather than to assume their comparison with these objects. -/
theorem actual_triple_pairing_ne_zero
    (ζ : ℂ) (hζ : ζ ^ 3 = 1) (r ι : ℂ)
    (q : SeedLocal ℂ r ι Finset.univ)
    (hq : ∀ ab, HasGrade ab (0, (1 : ZMod 3))
      (localizedCoordinates ℂ r ι Finset.univ q ab))
    (φ : SeedLocal ℂ r ι Finset.univ →ₗ[ℂ] ℂ) (hφ : φ q ≠ 0) :
    φ (twistedOrbit ζ (localLinearAction ζ hζ r ι Finset.univ) q) ≠ 0 := by
  rw [actual_triple_twistedOrbit_eq_three_smul ζ hζ r ι q hq,
    map_smul, smul_eq_mul]
  exact mul_ne_zero (by norm_num) hφ

end ActualNonzeroPairing

end CycleQ2OrbitTraceBridge

end

end Q2UncompiledOrbitTrace

