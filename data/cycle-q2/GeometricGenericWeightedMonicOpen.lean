import Proposal.GeometricGenericWeightedOpen
import Proposal.GeometricGenericWeightedPencilEquation
import Proposal.GeometricNormalizedCartierClass

/-!
# The actual deformed pencil on the monic coefficient chart

At the chosen endpoint the coefficient of the cube of the weight-two variable
is one. Inverting it normalizes the full pencil to a monic sextic. Every
nonempty principal open of this chart admits a pencil whose generic point
lies in that open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GenericWeightedMonicOpen

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2GenericPencilLift CycleQ2GenericPencilOpen

/-- Extend a point of the monic chart to all 45 coefficients. -/
def monicPoint (y : FullSexticTailIndex → ℂ) (e : FullInvariantIndex 6) : ℂ :=
  if he : (e.val 4).val < 3 then y ⟨e, he⟩ else 1

@[simp] theorem monicPoint_tail (y : FullSexticTailIndex → ℂ) (e : FullSexticTailIndex) :
    monicPoint y e.val = y e := by simp only [monicPoint, dif_pos e.property]

@[simp] theorem monicPoint_leading (y : FullSexticTailIndex → ℂ) :
    monicPoint y fullSexticLeadingIndex = 1 := by
  have h := (fullSextic_tail_iff_ne fullSexticLeadingIndex).not.mpr (not_not.mpr rfl)
  simp only [monicPoint, dif_neg h]

private def separatingTail : FullSexticTailIndex := ⟨separatingIndex, by decide⟩

/-- Choose an endpoint of the normalized family where the open equation
holds and the deformation direction is nonzero. -/
theorem exists_monic_endpoint (f : MvPolynomial FullSexticTailIndex ℂ) (hf : f ≠ 0) :
    ∃ y : FullSexticTailIndex → ℂ, eval y f ≠ 0 ∧ endpointDifference (monicPoint y) ≠ 0 := by
  let s : MvPolynomial FullSexticTailIndex ℂ := X separatingTail - C baseCoefficient
  have hs : s ≠ 0 := by
    intro hz
    have h := congrArg (eval (fun _ : FullSexticTailIndex => baseCoefficient + 1)) hz
    simp [s] at h
  have he : ∃ y : FullSexticTailIndex → ℂ, eval y (f * s) ≠ 0 := by
    by_contra! h
    apply mul_ne_zero hf hs
    apply MvPolynomial.funext
    intro y
    simpa only [map_zero] using h y
  obtain ⟨y, hy⟩ := he
  rw [map_mul, mul_ne_zero_iff] at hy
  refine ⟨y, hy.1, ?_⟩
  intro hzero
  have h := congrArg (coeff (fullExponentOf separatingIndex.val))
    (show fullInvariantPolynomial 6 (monicPoint y) = weightedPencil 0 from sub_eq_zero.mp hzero)
  have hv : y separatingTail = baseCoefficient := by
    rw [fullInvariantPolynomial_coeff] at h
    exact (monicPoint_tail y separatingTail).symm.trans h
  apply hy.2
  simp only [s, map_sub, eval_X, eval_C, hv, sub_self]

/-- Clearing the common leading coefficient preserves all inequalities detected
by evaluation at a monic endpoint. -/
private theorem normalized_eval_ne_zero {K : Type*} [Field K]
    (φ : TwoParameterRing →+* K) (hφ : Function.Injective φ)
    (c : ParameterIndex → ℂ) (hmonic : c fullSexticLeadingIndex = 1)
    (f : MvPolynomial FullSexticTailIndex ℂ) (hf : eval (fun e : FullSexticTailIndex => c e.val) f ≠ 0) :
    φ (universalCoefficient c fullSexticLeadingIndex) ≠ 0 ∧
    eval₂Hom (φ.comp constantParameters)
        (fun e : FullSexticTailIndex => φ (universalCoefficient c e.val) /
          φ (universalCoefficient c fullSexticLeadingIndex)) f ≠ 0 := by
  let L := universalCoefficient c fullSexticLeadingIndex
  let Ψ := eval₂Hom (φ.comp constantParameters)
    (fun e : FullSexticTailIndex => φ (universalCoefficient c e.val) / φ L)
  let ψ := eval (fun e : FullSexticTailIndex => c e.val)
  have hL : specialize 1 0 L = 1 := (universalCoefficient_endpoint c _).trans hmonic
  have hL' : φ L ≠ 0 := by
    intro hz
    have h := hφ (hz.trans (map_zero φ).symm)
    rw [h, map_zero] at hL
    exact zero_ne_one hL
  have hc (p : MvPolynomial FullSexticTailIndex ℂ) : ∃ n d : TwoParameterRing,
      specialize 1 0 n = ψ p ∧ specialize 1 0 d = 1 ∧ φ n = Ψ p * φ d := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      exact ⟨constantParameters a, 1, by simp [ψ], map_one _, by simp [Ψ]⟩
    | add p q hp hq =>
      obtain ⟨n, d, hn, hd, hz⟩ := hp
      obtain ⟨n', d', hn', hd', hz'⟩ := hq
      exact ⟨n * d' + n' * d, d * d', by simp [hn, hd, hn', hd'],
        by simp [hd, hd'], by simp only [map_mul, map_add, hz, hz']; ring⟩
    | mul_X p i hp =>
      obtain ⟨n, d, hn, hd, hz⟩ := hp
      refine ⟨n * universalCoefficient c i.val, d * L, ?_, ?_, ?_⟩
      · simp only [map_mul, universalCoefficient_endpoint, hn, ψ, eval_X]
      · simp [hd, hL]
      · simp only [map_mul, hz]
        rw [show Ψ (X i) = φ (universalCoefficient c i.val) / φ L by simp [Ψ]]
        field_simp [hL']
  refine ⟨hL', ?_⟩
  intro hz
  change Ψ f = 0 at hz
  obtain ⟨n, d, hn, _, h⟩ := hc f
  rw [hz, zero_mul] at h
  have hn0 := hφ (h.trans (map_zero φ).symm)
  apply hf
  simpa only [hn0, map_zero] using hn.symm

private theorem universalPencil_leading :
    universalPencil.coeff (Finsupp.single 4 3) = 1 + CycleQ2GenericPencilOpen.lambda ^ 6 := by
  let l := CycleQ2GenericPencilOpen.lambda
  let k := constantParameters (1 / 2 : ℂ)
  have fac : universalPencil = X 0 * (X 0 ^ 5 + C k *
        (X 0 ^ 2 * X 1 * X 2 * X 3 + C l * X 2 * X 4 ^ 2)) +
      X 1 * (X 1 ^ 5 + C k * C l * X 1 ^ 2 * X 3 * X 4) +
      X 2 * X 2 ^ 5 + X 3 * X 3 ^ 5 + C (1 + l ^ 6) * X 4 ^ 3 := by
    dsimp only [universalPencil, k, l]
    ring
  rw [fac]
  simp only [coeff_add, coeff_X_mul', coeff_C_mul, coeff_X_pow,
    Finsupp.support_single _ (by decide : (3 : ℕ) ≠ 0), Finset.mem_singleton,
    (by decide : (0 : Fin 5) ≠ 4), (by decide : (1 : Fin 5) ≠ 4),
    (by decide : (2 : Fin 5) ≠ 4), (by decide : (3 : Fin 5) ≠ 4),
    ite_false, zero_add]
  norm_num [l]

/-- For a monic endpoint the direction has no pure weight-two cube term. -/
theorem universalCoefficient_leading (c : ParameterIndex → ℂ) (hm : c fullSexticLeadingIndex = 1) :
    universalCoefficient c fullSexticLeadingIndex = 1 + CycleQ2GenericPencilOpen.lambda ^ 6 := by
  have hb : (weightedPencil 0).coeff (Finsupp.single 4 3) = 1 := by
    rw [← universalPencil_specialize 1 0, coeff_map, universalPencil_leading]
    simp
  have h0 : (endpointDifference c).coeff (Finsupp.single 4 3) = 0 := by
    rw [endpointDifference, coeff_sub, hb, ← fullSexticLeadingIndex_exponent,
      fullInvariantPolynomial_coeff, hm, sub_self]
  simp only [universalCoefficient, fullSexticLeadingIndex_exponent, universalDeformation,
    coeff_add, universalPencil_leading, coeff_C_mul, coeff_map, h0, map_zero, mul_zero, add_zero]

private theorem parameter_ext {p q : TwoParameterRing}
    (h : ∀ t l : ℂ, specialize t l p = specialize t l q) : p = q := by
  apply Polynomial.ext
  intro n
  apply Polynomial.funext
  intro t
  have hr : p.map (Polynomial.evalRingHom t) = q.map (Polynomial.evalRingHom t) := by
    apply Polynomial.funext
    intro l
    simpa only [specialize, Polynomial.coe_eval₂RingHom, Polynomial.eval_map] using h t l
  simpa only [Polynomial.coeff_map, Polynomial.coe_evalRingHom] using
    congrArg (fun g : Polynomial ℂ => g.coeff n) hr

theorem universalDeformation_coefficients (c : ParameterIndex → ℂ) :
    universalDeformation c = fullInvariantPolynomial 6 (universalCoefficient c) := by
  apply MvPolynomial.ext
  intro m
  apply parameter_ext
  intro t l
  have hf : MvPolynomial.map (specialize t l) (fullInvariantPolynomial 6 (universalCoefficient c)) =
      quotientDeformation t l (endpointDifference c) := by
    rw [map_fullInvariantPolynomial]
    change fullInvariantPolynomial 6 (fun e => specialize t l (universalCoefficient c e)) = _
    simp only [universalCoefficient_specialize]
    exact fullInvariantPolynomial_of_homogeneous ((weightedPencil_homogeneous l).add
      ((endpointDifference_homogeneous c).C_mul t))
  simpa only [coeff_map] using congrArg (fun g : WeightedPoly => g.coeff m)
    ((universalDeformation_specialize c t l).trans hf.symm)

open CycleQ2GenericWeightedOpen CycleQ2GenericSpecialization

/-- The intrinsic pencil ratio determines the leading coefficient at each monic endpoint. -/
theorem coefficientPoint_leading (d : Direction) (c : ParameterIndex → ℂ)
    (hm : c fullSexticLeadingIndex = 1) :
    coefficientPoint d c fullSexticLeadingIndex = 1 + CycleQ2GenericWeightedCoordinates.lambda ^ 6 := by
  rw [coefficientPoint, universalCoefficient_leading c hm, map_add, map_one, map_pow, evaluation_lambda]

/-- The actual coefficients of the normalized weighted sextic. -/
def normalizedCoefficientPoint (d : Direction) (c : ParameterIndex → ℂ)
    (e : FullSexticTailIndex) : RF :=
  coefficientPoint d c e.val / coefficientPoint d c fullSexticLeadingIndex

/-- Evaluation of the universal equation gives the weighted equation in the deformed field. -/
theorem map_universalDeformation (d : Direction) (c : ParameterIndex → ℂ) :
    MvPolynomial.map (evaluation d) (universalDeformation c) =
      CycleQ2GenericWeightedPencilEquation.equation (parameter d)
        CycleQ2GenericWeightedCoordinates.lambda (endpointDifference c) := by
  have htwo : (algebraMap ℂ RF) (2 : ℂ) = 2 := map_ofNat _ 2
  simp [universalDeformation, universalPencil, CycleQ2GenericWeightedPencilEquation.equation,
    MvPolynomial.map_map, htwo]

theorem coefficientPoint_eq_coeff (d : Direction) (c : ParameterIndex → ℂ) (e : ParameterIndex) :
    coefficientPoint d c e =
      (CycleQ2GenericWeightedPencilEquation.equation (parameter d)
        CycleQ2GenericWeightedCoordinates.lambda (endpointDifference c)).coeff (fullExponentOf e.val) := by
  rw [← map_universalDeformation, coeff_map]
  rfl

/-- Dividing the actual deformed sextic by its leading coefficient puts it in the original
44-coordinate monic family. -/
theorem equation_eq_leading_mul_normalized (d : Direction) (c : ParameterIndex → ℂ)
    (h : coefficientPoint d c fullSexticLeadingIndex ≠ 0) :
    CycleQ2GenericWeightedPencilEquation.equation (parameter d)
        CycleQ2GenericWeightedCoordinates.lambda (endpointDifference c) =
      C (coefficientPoint d c fullSexticLeadingIndex) * normalizedFullSextic (normalizedCoefficientPoint d c) := by
  rw [← map_universalDeformation, universalDeformation_coefficients, map_fullInvariantPolynomial]
  change fullInvariantPolynomial 6 (coefficientPoint d c) = _
  rw [fullInvariantPolynomial_sextic]
  have hi : (↑(Units.mk0 _ h)⁻¹ : RF) = (coefficientPoint d c fullSexticLeadingIndex)⁻¹ := rfl
  have ht : (fun e : FullSexticTailIndex => (↑(Units.mk0 _ h)⁻¹ : RF) * coefficientPoint d c e.val) =
      normalizedCoefficientPoint d c := by
    funext e
    rw [hi, normalizedCoefficientPoint, div_eq_mul_inv, mul_comm]
  exact (rawFullSextic_eq_unit_mul (Units.mk0 _ h) (fun e : FullSexticTailIndex => coefficientPoint d c e.val)).trans
    (congrArg (fun b => C (coefficientPoint d c fullSexticLeadingIndex) * normalizedFullSextic b) ht)

/-- Every nonempty principal open of the monic coefficient chart contains an actual
generic weighted pencil with both parameters evaluated in its deformed function field. -/
theorem exists_direction_in_monic_open (f : MvPolynomial FullSexticTailIndex ℂ) (hf : f ≠ 0) :
    ∃ (c : ParameterIndex → ℂ) (hc : endpointDifference c ≠ 0),
      c fullSexticLeadingIndex = 1 ∧
      eval (fun e : FullSexticTailIndex => c e.val) f ≠ 0 ∧
      coefficientPoint (endpointDirection c hc) c fullSexticLeadingIndex ≠ 0 ∧
      eval₂Hom (algebraMap ℂ RF) (normalizedCoefficientPoint (endpointDirection c hc) c) f ≠ 0 := by
  obtain ⟨y, hy, hc⟩ := exists_monic_endpoint f hf
  let c := monicPoint y
  have hf' : eval (fun e : FullSexticTailIndex => c e.val) f ≠ 0 := by
    simpa only [c, monicPoint_tail] using hy
  refine ⟨c, hc, monicPoint_leading y, hf', ?_⟩
  have h := normalized_eval_ne_zero (evaluation (endpointDirection c hc))
    (evaluation_injective _) c (monicPoint_leading y) f hf'
  rw [evaluation_comp_constants] at h
  change evaluation (endpointDirection c hc) (universalCoefficient c fullSexticLeadingIndex) ≠ 0 ∧
    eval₂Hom (algebraMap ℂ RF) (fun e : FullSexticTailIndex =>
      evaluation (endpointDirection c hc) (universalCoefficient c e.val) /
        evaluation (endpointDirection c hc) (universalCoefficient c fullSexticLeadingIndex)) f ≠ 0
  exact h

end CycleQ2GenericWeightedMonicOpen
end

#print axioms CycleQ2GenericWeightedMonicOpen.equation_eq_leading_mul_normalized
#print axioms CycleQ2GenericWeightedMonicOpen.exists_direction_in_monic_open
