import Proposal.GeometricGenericPencilLift
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# The generic deformed pencil meets every prescribed nonempty principal open

Status: source-only proof draft. Compilation and independent kernel replay
are deferred at the user's request.

The coefficient family below is the actual weighted quotient of the protected
deformation constructed in GeometricGenericPencilLift. The two parameters are
represented by C[X_tau][X_lambda]. If a coefficient polynomial is nonzero at
the chosen endpoint, its pullback is nonzero, and remains so in
C(tau)[X_lambda]. A second argument chooses that endpoint in any nonempty
principal open while excluding the original endpoint, thereby supplying a
genuine existing Direction.

This proves algebraic avoidance for the actual pencil. It does not assert that
the good geometric open or a relative correspondence has been constructed.
In particular, no embedding C(tau) -> C fixing C is invoked.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GenericPencilOpen

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2GenericPencilLift

abbrev ParameterIndex := FullInvariantIndex 6
abbrev ParameterRing := MvPolynomial ParameterIndex ℂ
abbrev TwoParameterRing := Polynomial (Polynomial ℂ)
abbrev GenericParameterField := RatFunc ℂ

/-- Constants in C[tau][lambda], with lambda the outer polynomial variable. -/
def constantParameters : ℂ →+* TwoParameterRing :=
  Polynomial.C.comp Polynomial.C

def tau : TwoParameterRing := Polynomial.C Polynomial.X
def lambda : TwoParameterRing := Polynomial.X

def specialize (t l : ℂ) : TwoParameterRing →+* ℂ :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom t) l

@[simp] theorem specialize_constant (t l a : ℂ) :
    specialize t l (constantParameters a) = a := by
  simp [specialize, constantParameters]

@[simp] theorem specialize_tau (t l : ℂ) : specialize t l tau = t := by
  simp [specialize, tau]

@[simp] theorem specialize_lambda (t l : ℂ) : specialize t l lambda = l := by
  simp [specialize, lambda]

@[simp] theorem specialize_comp_constants (t l : ℂ) :
    (specialize t l).comp constantParameters = RingHom.id ℂ := by
  ext a
  exact specialize_constant t l a

/-- The original quotient equation, retaining both polynomial parameters. -/
def universalPencil : MvPolynomial (Fin 5) TwoParameterRing :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + C (1 + lambda ^ 6) * X 4 ^ 3 +
    C (constantParameters (1 / 2 : ℂ)) *
      (X 0 ^ 3 * X 1 * X 2 * X 3 +
        C lambda * X 1 ^ 3 * X 3 * X 4 + C lambda * X 0 * X 2 * X 4 ^ 2)

theorem universalPencil_specialize (t l : ℂ) :
    MvPolynomial.map (specialize t l) universalPencil = weightedPencil l := by
  simp [universalPencil, weightedPencil]

def universalDeformation (c : ParameterIndex → ℂ) :
    MvPolynomial (Fin 5) TwoParameterRing :=
  universalPencil + C tau * MvPolynomial.map constantParameters (endpointDifference c)

theorem universalDeformation_specialize (c : ParameterIndex → ℂ) (t l : ℂ) :
    MvPolynomial.map (specialize t l) (universalDeformation c) =
      quotientDeformation t l (endpointDifference c) := by
  simp only [universalDeformation, map_add, map_mul, MvPolynomial.map_C,
    specialize_tau, MvPolynomial.map_map, specialize_comp_constants,
    MvPolynomial.map_id, universalPencil_specialize, quotientDeformation]

def universalCoefficient (c : ParameterIndex → ℂ) (e : ParameterIndex) :
    TwoParameterRing :=
  (universalDeformation c).coeff (fullExponentOf e.val)

theorem universalCoefficient_specialize (c : ParameterIndex → ℂ)
    (e : ParameterIndex) (t l : ℂ) :
    specialize t l (universalCoefficient c e) =
      (quotientDeformation t l (endpointDifference c)).coeff (fullExponentOf e.val) := by
  have h := congrArg (fun p => MvPolynomial.coeff (fullExponentOf e.val) p)
    (universalDeformation_specialize c t l)
  simpa only [MvPolynomial.coeff_map, universalCoefficient] using h

@[simp] theorem universalCoefficient_endpoint (c : ParameterIndex → ℂ)
    (e : ParameterIndex) : specialize 1 0 (universalCoefficient c e) = c e := by
  rw [universalCoefficient_specialize, fullInvariant_endpoint,
    fullInvariantPolynomial_coeff]

/-- Pullback of equations on the full invariant coefficient space. -/
def parameterPullback (c : ParameterIndex → ℂ) : ParameterRing →+* TwoParameterRing :=
  MvPolynomial.eval₂Hom constantParameters (universalCoefficient c)

theorem parameterPullback_specialize (c : ParameterIndex → ℂ) (t l : ℂ) :
    (specialize t l).comp (parameterPullback c) =
      MvPolynomial.eval (fun e =>
        (quotientDeformation t l (endpointDifference c)).coeff (fullExponentOf e.val)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [parameterPullback]
  · intro e
    simp only [RingHom.comp_apply, parameterPullback, MvPolynomial.eval₂Hom_X',
      MvPolynomial.eval_X, universalCoefficient_specialize]

@[simp] theorem parameterPullback_endpoint (c : ParameterIndex → ℂ)
    (f : ParameterRing) : specialize 1 0 (parameterPullback c f) = MvPolynomial.eval c f := by
  have h : (specialize 1 0).comp (parameterPullback c) = MvPolynomial.eval c := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [parameterPullback]
    · intro e
      simp [parameterPullback]
  exact RingHom.congr_fun h f

/-- A good endpoint prevents the actual two-parameter family from lying
entirely in the closed exceptional locus. -/
theorem parameterPullback_ne_zero (c : ParameterIndex → ℂ) (f : ParameterRing)
    (hf : MvPolynomial.eval c f ≠ 0) : parameterPullback c f ≠ 0 := by
  intro h
  apply hf
  rw [← parameterPullback_endpoint c f, h, map_zero]

/-- Only the tau coefficient ring is localized; lambda remains a variable. -/
def genericCoefficients : TwoParameterRing →+* Polynomial GenericParameterField :=
  Polynomial.mapRingHom (algebraMap (Polynomial ℂ) (RatFunc ℂ))

theorem genericCoefficients_injective : Function.Injective genericCoefficients :=
  Polynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)

def genericOpenPolynomial (c : ParameterIndex → ℂ) (f : ParameterRing) :
    Polynomial GenericParameterField := genericCoefficients (parameterPullback c f)

/-- The actual constant-field embedding used in the generic coefficient ring. -/
def genericConstants : ℂ →+* GenericParameterField :=
  (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp Polynomial.C

/-- Evaluate the actual generic coefficient family at a pencil parameter. -/
def genericCoefficientPoint (c : ParameterIndex → ℂ) (l : GenericParameterField)
    (e : ParameterIndex) : GenericParameterField :=
  (genericCoefficients (universalCoefficient c e)).eval l

/-- The polynomial detected below is literally the given exceptional-locus
equation evaluated at the generic pencil's coefficient point. -/
theorem genericOpenPolynomial_eval (c : ParameterIndex → ℂ) (f : ParameterRing)
    (l : GenericParameterField) :
    (genericOpenPolynomial c f).eval l =
      MvPolynomial.eval₂Hom genericConstants (genericCoefficientPoint c l) f := by
  let φ : TwoParameterRing →+* GenericParameterField :=
    (Polynomial.evalRingHom l).comp genericCoefficients
  have hconstants : φ.comp constantParameters = genericConstants := by
    ext a
    simp [φ, constantParameters, genericCoefficients, genericConstants,
      Polynomial.coe_mapRingHom]
  change φ (MvPolynomial.eval₂Hom constantParameters (universalCoefficient c) f) = _
  rw [MvPolynomial.map_eval₂Hom, hconstants]
  rfl

/-- Nonvanishing survives passage to the generic deformation parameter. -/
theorem genericOpenPolynomial_ne_zero (c : ParameterIndex → ℂ) (f : ParameterRing)
    (hf : MvPolynomial.eval c f ≠ 0) : genericOpenPolynomial c f ≠ 0 := by
  intro h
  apply parameterPullback_ne_zero c f hf
  apply genericCoefficients_injective
  simpa only [map_zero, genericOpenPolynomial] using h

/-- The generic pencil has an actual point outside the pulled-back closed
locus, over its rational-function coefficient field. -/
theorem exists_generic_parameter (c : ParameterIndex → ℂ) (f : ParameterRing)
    (hf : MvPolynomial.eval c f ≠ 0) :
    ∃ l : GenericParameterField, (genericOpenPolynomial c f).eval l ≠ 0 := by
  by_contra h
  push_neg at h
  apply genericOpenPolynomial_ne_zero c f hf
  apply Polynomial.funext
  intro l
  simpa only [Polynomial.eval_zero] using h l

theorem exists_generic_coefficient_point (c : ParameterIndex → ℂ) (f : ParameterRing)
    (hf : MvPolynomial.eval c f ≠ 0) :
    ∃ l : GenericParameterField,
      MvPolynomial.eval₂Hom genericConstants (genericCoefficientPoint c l) f ≠ 0 := by
  obtain ⟨l, hl⟩ := exists_generic_parameter c f hf
  exact ⟨l, by simpa only [genericOpenPolynomial_eval] using hl⟩

/-- The monomial X3^6 is an actual coefficient of the invariant family. -/
def separatingIndex : ParameterIndex := ⟨![0, 0, 0, 6, 0], by decide⟩

def baseCoefficient : ℂ :=
  (weightedPencil 0).coeff (fullExponentOf separatingIndex.val)

def separatingPolynomial : ParameterRing := X separatingIndex - C baseCoefficient

theorem separatingPolynomial_ne_zero : separatingPolynomial ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : ParameterIndex => baseCoefficient + 1)) h
  simp [separatingPolynomial] at he

/-- Every nonempty principal open contains an endpoint different from the
protected quotient, so the pre-existing Direction has no missing premise. -/
theorem exists_endpoint_in_principal_open (f : ParameterRing) (hf : f ≠ 0) :
    ∃ c : ParameterIndex → ℂ,
      MvPolynomial.eval c f ≠ 0 ∧ endpointDifference c ≠ 0 := by
  have hprod : f * separatingPolynomial ≠ 0 :=
    mul_ne_zero hf separatingPolynomial_ne_zero
  have hex : ∃ c : ParameterIndex → ℂ,
      MvPolynomial.eval c (f * separatingPolynomial) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hprod
    apply MvPolynomial.funext
    intro c
    simpa only [map_zero] using h c
  obtain ⟨c, hc⟩ := hex
  rw [map_mul, mul_ne_zero_iff] at hc
  refine ⟨c, hc.1, ?_⟩
  intro hz
  have hp : fullInvariantPolynomial 6 c = weightedPencil 0 := sub_eq_zero.mp hz
  have he := congrArg
    (fun p : WeightedPoly => p.coeff (fullExponentOf separatingIndex.val)) hp
  have hcoeff : c separatingIndex = baseCoefficient := by
    simpa only [fullInvariantPolynomial_coeff, baseCoefficient] using he
  apply hc.2
  simp only [separatingPolynomial, map_sub, MvPolynomial.eval_X,
    MvPolynomial.eval_C, hcoeff, sub_self]

/-- A nonempty principal open gives both a valid protected deformation
direction and a generic pencil meeting that open. The construction uses the
original full invariant coefficient space throughout. -/
theorem exists_direction_and_generic_open (f : ParameterRing) (hf : f ≠ 0) :
    ∃ (c : ParameterIndex → ℂ) (hc : endpointDifference c ≠ 0),
      (endpointDirection c hc).polynomial = affineLift (endpointDifference c) ∧
      MvPolynomial.eval c f ≠ 0 ∧ genericOpenPolynomial c f ≠ 0 ∧
      ∃ l : GenericParameterField, (genericOpenPolynomial c f).eval l ≠ 0 := by
  obtain ⟨c, hgood, hc⟩ := exists_endpoint_in_principal_open f hf
  exact ⟨c, hc, rfl, hgood, genericOpenPolynomial_ne_zero c f hgood,
    exists_generic_parameter c f hgood⟩

#print axioms universalDeformation_specialize
#print axioms genericOpenPolynomial_eval
#print axioms genericOpenPolynomial_ne_zero
#print axioms exists_direction_and_generic_open

end CycleQ2GenericPencilOpen

end
