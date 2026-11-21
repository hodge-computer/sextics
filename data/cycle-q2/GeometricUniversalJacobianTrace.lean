import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Proposal.GeometricUniversalJacobianFrames

set_option autoImplicit false

/-!
# A polynomial socle functional for the universal weighted sextic

In degree 18 and character 2 the only Fermat-standard monomial is the socle.
For each other monomial choose a dividing Fermat gradient monomial. The
corresponding actual gradient multiples, normalized by their nonzero Fermat
leading scalars, give a square coefficient matrix after adjoining the socle
column. Its specialization is the identity. The socle row of its adjugate
evaluates triple products over the original coefficient ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

noncomputable section
namespace CycleQ2HiggsSocle

open MvPolynomial CycleQ2FermatHiggs CycleQ2FermatJacobian CycleQ2GenericSexticGradient

abbrev Row := {a : Fin 5 → Fin 19 //
  weightedDegree (fun i => (a i).val) = 18 ∧ character (fun i => (a i).val) = 2}

/-- The determinant only uses the finite indexing type abstractly. -/
noncomputable instance instFintypeRow : Fintype Row := Fintype.ofFinite Row

def exp (d : Row) : Exp := exponent (fun i => (d.val i).val)

theorem exp_injective : Function.Injective exp := by
  intro d e h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun z : Exp => z i) h

def rowOfExp (a : Exp) (hd : weightedDegree a = 18) (hc : character a = 2) : Row := by
  have hb (i : Fin 5) : a i < 19 := by
    have hh : a 0 + a 1 + a 2 + a 3 + 2 * a 4 = 18 := hd
    fin_cases i
    · change a 0 < 19
      omega
    · change a 1 < 19
      omega
    · change a 2 < 19
      omega
    · change a 3 < 19
      omega
    · change a 4 < 19
      omega
  exact ⟨fun i => ⟨a i, hb i⟩, hd, hc⟩

@[simp] theorem exp_rowOfExp (a : Exp) (hd : weightedDegree a = 18) (hc : character a = 2) :
    exp (rowOfExp a hd hc) = a := by ext i; rfl

def topRow : Row :=
  ⟨fun i => ⟨socle i, by fin_cases i <;> decide⟩, socle_weightedDegree_character⟩

@[simp] theorem exp_topRow : exp topRow = exponent socle := rfl

theorem exceeding (d : Row) (h : d ≠ topRow) : ∃ i : Fin 5, cutoff i ≤ exp d i := by
  by_contra! hn
  apply h
  apply exp_injective
  ext i
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  have h4 := hn 4
  have hd := d.property.1
  change (d.val 0).val + (d.val 1).val + (d.val 2).val + (d.val 3).val + 2 * (d.val 4).val = 18 at hd
  change (d.val 0).val < 5 at h0
  change (d.val 1).val < 5 at h1
  change (d.val 2).val < 5 at h2
  change (d.val 3).val < 5 at h3
  change (d.val 4).val < 2 at h4
  fin_cases i
  · change (d.val 0).val = 4
    omega
  · change (d.val 1).val = 4
    omega
  · change (d.val 2).val = 4
    omega
  · change (d.val 3).val = 4
    omega
  · change (d.val 4).val = 1
    omega

def chosen (d : Row) (h : d ≠ topRow) : Fin 5 := Classical.choose (exceeding d h)

theorem chosen_le (d : Row) (h : d ≠ topRow) : cutoff (chosen d h) ≤ exp d (chosen d h) :=
  Classical.choose_spec (exceeding d h)

abbrev FamilyPoly := MvPolynomial (Fin 5) CoeffRing

def multiple (d : Row) (i : Fin 5) : FamilyPoly :=
  monomial (exp d - Finsupp.single i (cutoff i)) 1 * pderiv i universalF

def column (d : Row) : FamilyPoly :=
  if h : d = topRow then monomial (exp topRow) 1
  else (C ((derivativeScalar (chosen d h))⁻¹) : CoeffRing) • multiple d (chosen d h)

def coefficients (R : Type*) [CommRing R] : MvPolynomial (Fin 5) R →ₗ[R] (Row → R) :=
  LinearMap.pi (fun d => lcoeff R (exp d))

def macaulay : Matrix Row Row CoeffRing := Matrix.of fun d e => coeff (exp d) (column e)

theorem multiple_seed (d : Row) (i : Fin 5) (hi : cutoff i ≤ exp d i) :
    MvPolynomial.map seedEvaluation (multiple d i) = monomial (exp d) (derivativeScalar i) := by
  have hle : Finsupp.single i (cutoff i) ≤ exp d := Finsupp.single_le_iff.mpr hi
  rw [multiple, map_mul, ← pderiv_map, universalF_seed, derivative_eq,
    generator, X_pow_eq_monomial, C_mul_monomial, map_monomial, map_one, monomial_mul,
    tsub_add_cancel_of_le hle, mul_one, one_mul]

theorem column_seed (d : Row) :
    MvPolynomial.map seedEvaluation (column d) = monomial (exp d) 1 := by
  classical
  by_cases h : d = topRow
  · subst d
    simp [column]
  · rw [column, dif_neg h, smul_eq_C_mul, map_mul, map_C, multiple_seed d _ (chosen_le d h)]
    simp [CycleQ2GenericSexticGradient.seedEvaluation, C_mul_monomial, derivativeScalar_ne_zero]

theorem macaulay_seed : macaulay.map seedEvaluation = (1 : Matrix Row Row ℂ) := by
  classical
  ext d e
  change seedEvaluation (coeff (exp d) (column e)) = _
  rw [← coeff_map, column_seed, coeff_monomial, Matrix.one_apply]
  by_cases h : d = e
  · simp [h]
  · rw [if_neg (fun he : exp e = exp d => h (exp_injective he.symm)), if_neg h]

theorem det_seed : seedEvaluation macaulay.det = 1 := by
  rw [RingHom.map_det]
  change (macaulay.map seedEvaluation).det = 1
  rw [macaulay_seed, Matrix.det_one]

section Cramer

variable {I V A B : Type*} [Fintype I] [DecidableEq I] [CommRing A] [CommRing B]
  [AddCommGroup V] [Module A V]

private def cramerRow (M : Matrix I I A) (v : V →ₗ[A] (I → A)) (k : I) : V →ₗ[A] A :=
  (LinearMap.proj k).comp (M.cramer.comp v)

private theorem cramerRow_apply (M : Matrix I I A) (v : V →ₗ[A] (I → A)) (k : I) (p : V) :
    cramerRow M v k p = M.cramer (v p) k := rfl

private theorem cramerRow_column (M : Matrix I I A) (v : V →ₗ[A] (I → A)) (k j : I) (p : V)
    (hp : ∀ e, v p e = M e j) : cramerRow M v k p = (Pi.single j M.det : I → A) k :=
  congrFun (Matrix.cramer_row_self M (v p) j hp) k

private theorem cramerRow_one (v : V →ₗ[A] (I → A)) (k : I) (p : V) :
    cramerRow 1 v k p = v p k := by
  rw [cramerRow_apply, Matrix.cramer_one]
  rfl

private theorem map_cramer (f : A →+* B) (M : Matrix I I A) (b : I → A) (k : I) :
    f (M.cramer b k) = (M.map f).cramer (f ∘ b) k := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply, RingHom.map_det]
  exact congrArg Matrix.det (Matrix.map_updateCol (M := M) (j := k) (c := b) f)

end Cramer

def traceAt {K : Type*} [CommRing K] (f : CoeffRing →+* K) :
    MvPolynomial (Fin 5) K →ₗ[K] K :=
  cramerRow (macaulay.map f) (coefficients K) topRow

def trace : FamilyPoly →ₗ[CoeffRing] CoeffRing :=
  cramerRow macaulay (coefficients CoeffRing) topRow

theorem traceAt_congr {K : Type*} [CommRing K] (f : CoeffRing →+* K)
    {p q : MvPolynomial (Fin 5) K} (h : coefficients K p = coefficients K q) :
    traceAt f p = traceAt f q := by
  rw [traceAt, cramerRow_apply, cramerRow_apply, h]

theorem map_trace {K : Type*} [CommRing K] (f : CoeffRing →+* K) (p : FamilyPoly) :
    f (trace p) = traceAt f (MvPolynomial.map f p) := by
  rw [trace, traceAt, cramerRow_apply, cramerRow_apply, map_cramer]
  apply congrArg (fun b => (macaulay.map f).cramer b topRow)
  funext d
  exact (coeff_map f p (exp d)).symm

theorem map_multiple {K : Type*} [CommRing K] (f : CoeffRing →+* K) (d : Row) (i : Fin 5) :
    MvPolynomial.map f (multiple d i) =
      monomial (exp d - Finsupp.single i (cutoff i)) 1 * pderiv i (MvPolynomial.map f universalF) := by
  simp only [multiple, map_mul, map_monomial, map_one, pderiv_map]

theorem traceAt_multiple {K : Type*} [CommRing K] (f : CoeffRing →+* K) (d : Row) (i : Fin 5) :
    traceAt f (monomial (exp d - Finsupp.single i (cutoff i)) 1 *
      pderiv i (MvPolynomial.map f universalF)) = f (trace (multiple d i)) := by
  rw [map_trace, map_multiple]

theorem seed_trace (p : FamilyPoly) :
    seedEvaluation (trace p) = coeff (exponent socle) (MvPolynomial.map seedEvaluation p) := by
  rw [map_trace, traceAt, macaulay_seed, cramerRow_one]
  rfl

theorem trace_column (d : Row) :
    trace (column d) = (Pi.single d macaulay.det : Row → CoeffRing) topRow :=
  cramerRow_column macaulay (coefficients CoeffRing) topRow d (column d) (fun _ => rfl)

theorem trace_chosen (d : Row) (h : d ≠ topRow) : trace (multiple d (chosen d h)) = 0 := by
  have hh := trace_column d
  rw [column, dif_neg h, map_smul, smul_eq_mul, Pi.single_eq_of_ne h.symm] at hh
  exact (mul_eq_zero.mp hh).resolve_left (C_ne_zero.mpr (inv_ne_zero (derivativeScalar_ne_zero _)))

theorem trace_socle : trace (monomial (exponent socle) 1) = macaulay.det := by
  simpa [column] using trace_column topRow

def triple (R : Type*) [CommRing R] (m : Fin 35) (i j : Fin 33) : MvPolynomial (Fin 5) R :=
  monomial (exponent (basisMonomial i)) 1 * monomial (exponent (basisMonomial j)) 1 *
    monomial (exponent (tangentMonomial m)) 1

def H (m : Fin 35) : Matrix (Fin 33) (Fin 33) CoeffRing :=
  Matrix.of fun i j => trace (triple CoeffRing m i j)

theorem H_seed (m : Fin 35) : (H m).map seedEvaluation = higgsMatrix ℂ m := by
  ext i j
  have h := seed_trace (triple CoeffRing m i j)
  apply h.trans
  simp only [triple, map_mul, map_monomial, map_one]
  simpa only [monomialClass, ← map_mul, socleTrace_mk] using
    socleTrace_triple_eq_higgsMatrix m i j

end CycleQ2HiggsSocle
end

#print axioms CycleQ2HiggsSocle.trace_chosen
#print axioms CycleQ2HiggsSocle.det_seed
#print axioms CycleQ2HiggsSocle.H_seed

/-!
# Koszul relations for the full degree-eighteen Jacobian matrix

Each repeated Fermat pivot gives a two-generator Koszul relation in the
universal Jacobian ideal. After adding a multiple of its chosen pivot,
the relation has exactly one nonzero coefficient at Fermat. The resulting
square relation matrix has nonzero determinant over the parameter ring.
Its adjugate transfers vanishing of the chosen columns to every Jacobian
column in the same degree and character.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

noncomputable section
namespace CycleQ2HiggsSocleSyzygies

open MvPolynomial CycleQ2FermatHiggs CycleQ2FermatJacobian CycleQ2GenericSexticGradient
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2HiggsSocle
open Finset
open scoped Classical

def pivot (i : Fin 5) : Exp := Finsupp.single i (cutoff i)

abbrev Slots (i : Fin 5) := {d : Row // pivot i ≤ exp d}
abbrev ColumnIndex := (i : Fin 5) × Slots i

def offset (i : Fin 5) (d : Slots i) : Exp := exp d.val - pivot i

theorem offset_add (i : Fin 5) (d : Slots i) : offset i d + pivot i = exp d.val :=
  tsub_add_cancel_of_le d.property

theorem offset_injective (i : Fin 5) : Function.Injective (offset i) := by
  intro d e h
  apply Subtype.ext
  apply exp_injective
  rw [← offset_add i d, ← offset_add i e, h]

private theorem notTop (i : Fin 5) (d : Slots i) : d.val ≠ topRow := by
  intro h
  have hh := Finsupp.single_le_iff.mp d.property
  rw [h, exp_topRow, exponent_apply] at hh
  exact Nat.not_succ_le_self _ hh

private def preferred (c : ColumnIndex) : Fin 5 := chosen c.2.val (notTop c.1 c.2)

private def preferredColumn (c : ColumnIndex) : ColumnIndex :=
  ⟨preferred c, c.2.val, Finsupp.single_le_iff.mpr (chosen_le _ _)⟩

private theorem rowWeight (d : Row) : Finsupp.weight fullGrading (exp d) = (18, 2) := by
  rw [fullGrading_weight]
  apply Prod.ext
  · exact d.property.1
  · apply ZMod.val_injective 3
    rw [ZMod.val_natCast]
    exact d.property.2

private def rowOfWeight (a : Exp) (h : Finsupp.weight fullGrading a = (18, 2)) : Row := by
  rw [fullGrading_weight] at h
  apply rowOfExp a (congrArg Prod.fst h)
  have hc := congrArg (fun p : ℕ × ZMod 3 => p.2.val) h
  change ((↑(2 * a 0 + 2 * a 1 + a 2) : ZMod 3).val) = (2 : ZMod 3).val at hc
  rw [ZMod.val_natCast] at hc
  exact hc

private theorem rowOfWeight_exp (a : Exp) (h : Finsupp.weight fullGrading a = (18, 2)) :
    exp (rowOfWeight a h) = a := by
  unfold rowOfWeight
  apply exp_rowOfExp

private theorem pivotWeight (i : Fin 5) :
    Finsupp.weight fullGrading (pivot i) = (6 - (fullGrading i).1, -(fullGrading i).2) := by
  rw [pivot, Finsupp.weight_single]
  fin_cases i <;> decide

private def gradMul (a : Exp) (j : Fin 5) : FamilyPoly :=
  monomial a 1 * pderiv j universalF

private theorem gradMul_homogeneous (a : Exp) (j : Fin 5) :
    HG (gradMul a j) (Finsupp.weight fullGrading a + Finsupp.weight fullGrading (pivot j)) := by
  have hg := CycleQ2HiggsJacobianMembership.partial_homogeneous (RingHom.id CoeffRing) j
  rw [MvPolynomial.map_id] at hg
  rw [pivotWeight]
  exact (isWeightedHomogeneous_monomial fullGrading a _ rfl).mul hg

private theorem expand (i : Fin 5) (H : FamilyPoly)
    (hH : ∀ a, coeff a H ≠ 0 → ∃ d : Slots i, offset i d = a) :
    ∑ d : Slots i, coeff (offset i d) H • multiple d.val i = H * pderiv i universalF := by
  classical
  have hpoly : ∑ d : Slots i, coeff (offset i d) H •
      (monomial (offset i d) 1 : FamilyPoly) = H := by
    ext a
    simp only [coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul]
    by_cases he : ∃ d : Slots i, offset i d = a
    · obtain ⟨d, rfl⟩ := he
      rw [Finset.sum_eq_single d]
      · simp
      · intro e _ hne
        have hh := (offset_injective i).ne hne
        simp [hh]
      · simp
    · have hzero : coeff a H = 0 := by by_contra h; exact he (hH _ h)
      rw [hzero]
      apply Finset.sum_eq_zero
      intro d _
      have hd : offset i d ≠ a := fun h => he ⟨d, h⟩
      simp [hd]
  change (∑ d : Slots i, coeff (offset i d) H •
    ((monomial (offset i d) 1 : FamilyPoly) * pderiv i universalF)) = _
  simp_rw [← smul_mul_assoc]
  rw [← Finset.sum_mul, hpoly]

private def columnValue (c : ColumnIndex) : CoeffRing := trace (multiple c.2.val c.1)

private def component (i : Fin 5) (H : FamilyPoly) (c : ColumnIndex) : CoeffRing :=
  if c.1 = i then coeff (offset c.1 c.2) H else 0

private theorem component_pairing (i : Fin 5) (H : FamilyPoly)
    (hH : ∀ a, coeff a H ≠ 0 → ∃ d : Slots i, offset i d = a) :
    ∑ c : ColumnIndex, columnValue c * component i H c = trace (H * pderiv i universalF) := by
  classical
  rw [← expand i H hH, map_sum, Fintype.sum_sigma]
  simp only [component, mul_ite, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp only [if_true, map_smul, smul_eq_mul, columnValue, mul_comm]
  · intro j _ hj
    simp only [if_neg hj, Finset.sum_const_zero]
  · simp

private def common (c : ColumnIndex) : Exp := offset c.1 c.2 - pivot (preferred c)

private theorem preferred_le_offset (c : ColumnIndex) (h : c.1 ≠ preferred c) :
    pivot (preferred c) ≤ offset c.1 c.2 := by
  apply Finsupp.single_le_iff.mpr
  have ht := chosen_le c.2.val (notTop c.1 c.2)
  change cutoff (preferred c) ≤ exp c.2.val (preferred c) at ht
  simpa [offset, pivot, Finsupp.tsub_apply, Finsupp.single_eq_of_ne h.symm] using ht

private theorem common_right (c : ColumnIndex) (h : c.1 ≠ preferred c) :
    common c + pivot (preferred c) = offset c.1 c.2 :=
  tsub_add_cancel_of_le (preferred_le_offset c h)

private theorem common_left (c : ColumnIndex) (h : c.1 ≠ preferred c) :
    common c + pivot c.1 = offset (preferredColumn c).1 (preferredColumn c).2 := by
  have hh : common c + pivot c.1 + pivot (preferred c) =
      offset (preferredColumn c).1 (preferredColumn c).2 + pivot (preferredColumn c).1 := by
    rw [add_right_comm, common_right c h, offset_add, offset_add]
    rfl
  exact add_right_cancel hh

private theorem supported (c : ColumnIndex) (a : Exp) (j : Fin 5)
    (h : a + pivot j = offset c.1 c.2) :
    ∀ b, coeff b (gradMul a j) ≠ 0 → ∃ d : Slots c.1, offset c.1 d = b := by
  intro b hb
  have hw := gradMul_homogeneous a j hb
  have ht : Finsupp.weight fullGrading (b + pivot c.1) = (18, 2) := by
    rw [map_add, hw, ← map_add, h, ← map_add, offset_add, rowWeight]
  let row := rowOfWeight (b + pivot c.1) ht
  have hv : exp row = b + pivot c.1 := rowOfWeight_exp _ ht
  have hd : pivot c.1 ≤ exp row := by rw [hv]; exact le_add_self
  exact ⟨⟨row, hd⟩, by simp [offset, hv]⟩

private def unitColumn (c k : ColumnIndex) : CoeffRing := if k = c then 1 else 0

/-- The two-generator relations, completed by chosen columns to a square matrix. -/
private def relation (k c : ColumnIndex) : CoeffRing := by
  classical
  exact if c.1 = preferred c then unitColumn c k else
    component c.1 (gradMul (common c) (preferred c)) k -
    component (preferred c) (gradMul (common c) c.1) k +
    C (derivativeScalar c.1) * unitColumn (preferredColumn c) k

private theorem trace_preferred (c : ColumnIndex) : columnValue (preferredColumn c) = 0 :=
  trace_chosen c.2.val (notTop c.1 c.2)

private theorem unit_pairing (x : ColumnIndex) :
    ∑ k : ColumnIndex, columnValue k * unitColumn x k = columnValue x := by
  classical
  simp [unitColumn, mul_ite]

private theorem relation_pairing (c : ColumnIndex) :
    ∑ k : ColumnIndex, columnValue k * relation k c = 0 := by
  classical
  by_cases h : c.1 = preferred c
  · have ht := trace_chosen c.2.val (notTop c.1 c.2)
    change trace (multiple c.2.val (preferred c)) = 0 at ht
    simp only [relation, if_pos h, unit_pairing]
    change trace (multiple c.2.val c.1) = 0
    exact (congrArg (fun i : Fin 5 => trace (multiple c.2.val i)) h).trans ht
  · simp only [relation, if_neg h, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp_rw [show ∀ k : ColumnIndex, columnValue k *
        (C (derivativeScalar c.1) * unitColumn (preferredColumn c) k) =
        C (derivativeScalar c.1) * (columnValue k * unitColumn (preferredColumn c) k)
      from fun _ => mul_left_comm ..]
    have ht := component_pairing _ _ (supported (preferredColumn c) _ _ (common_left c h))
    change (∑ k : ColumnIndex, columnValue k * component (preferred c) (gradMul (common c) c.1) k) =
      trace (gradMul (common c) c.1 * pderiv (preferred c) universalF) at ht
    rw [← Finset.mul_sum, unit_pairing, trace_preferred, mul_zero, add_zero,
      component_pairing _ _ (supported c _ _ (common_right c h)), ht]
    have hc : gradMul (common c) (preferred c) * pderiv c.1 universalF =
        gradMul (common c) c.1 * pderiv (preferred c) universalF := by
      unfold gradMul
      ring
    rw [hc, sub_self]

private theorem component_seed (c k : ColumnIndex) (a : Exp) (j : Fin 5)
    (h : a + pivot j = offset c.1 c.2) :
    seedEvaluation (component c.1 (gradMul a j) k) =
      if k = c then derivativeScalar j else 0 := by
  classical
  obtain ⟨i, d⟩ := c
  obtain ⟨l, e⟩ := k
  by_cases hil : l = i
  · subst l
    simp only [component, if_true]
    rw [← coeff_map, gradMul, map_mul, map_monomial, map_one, ← pderiv_map,
      universalF_seed, derivative_eq, generator, X_pow_eq_monomial, C_mul_monomial,
      monomial_mul, one_mul, mul_one, coeff_monomial]
    change (if a + pivot j = offset i e then derivativeScalar j else 0) = _
    rw [h]
    by_cases hd : d = e
    · subst e; simp
    · have hne := (offset_injective i).ne hd
      simp [hne, Ne.symm hd]
  · have hne : (⟨l, e⟩ : ColumnIndex) ≠ ⟨i, d⟩ := fun hh => hil (congrArg Sigma.fst hh)
    simp [component, hil, hne]

private def relationMatrix : Matrix ColumnIndex ColumnIndex CoeffRing := Matrix.of relation
private def diagonalValue (c : ColumnIndex) : ℂ :=
  if c.1 = preferred c then 1 else derivativeScalar (preferred c)

private theorem relation_seed (k c : ColumnIndex) :
    seedEvaluation (relation k c) = if k = c then diagonalValue c else 0 := by
  classical
  by_cases h : c.1 = preferred c
  · simp [relation, h, unitColumn, diagonalValue, apply_ite]
  · have h₂ := component_seed (preferredColumn c) k _ _ (common_left c h)
    change seedEvaluation (component (preferred c) (gradMul (common c) c.1) k) =
      (if k = preferredColumn c then derivativeScalar c.1 else 0) at h₂
    simp only [relation, if_neg h, diagonalValue, map_add, map_sub, map_mul,
      component_seed c k _ _ (common_right c h), h₂]
    change _ - (if k = preferredColumn c then derivativeScalar c.1 else 0) +
      seedEvaluation (C (derivativeScalar c.1)) * seedEvaluation (unitColumn (preferredColumn c) k) = _
    simp only [CycleQ2GenericSexticGradient.seedEvaluation, eval_C, unitColumn, apply_ite, map_one, map_zero]
    split_ifs <;> ring

private theorem relation_det_ne_zero : relationMatrix.det ≠ 0 := by
  classical
  have hs : relationMatrix.map seedEvaluation = Matrix.diagonal diagonalValue := by
    ext k c
    rw [Matrix.diagonal_apply]
    by_cases he : k = c
    · subst c; exact (relation_seed k k).trans (by simp)
    · exact (relation_seed k c).trans (by simp [he])
  intro hz
  have hh := congrArg seedEvaluation hz
  rw [RingHom.map_det, map_zero] at hh
  change (relationMatrix.map seedEvaluation).det = 0 at hh
  rw [hs, Matrix.det_diagonal] at hh
  exact (Finset.prod_ne_zero_iff.mpr (fun c _ => by
    dsimp [diagonalValue]
    split <;> first | exact one_ne_zero | apply derivativeScalar_ne_zero)) hh

/-- The universal socle functional vanishes on every actual monomial Jacobian
multiple of the prescribed weighted degree and character. -/
theorem trace_multiple (d : Row) (i : Fin 5) (h : cutoff i ≤ exp d i) :
    trace (multiple d i) = 0 := by
  classical
  have hz : Matrix.vecMul columnValue relationMatrix = 0 := funext relation_pairing
  have hh := congrArg (fun v : ColumnIndex → CoeffRing => Matrix.vecMul v relationMatrix.adjugate) hz
  change Matrix.vecMul (Matrix.vecMul _ _) _ = Matrix.vecMul 0 _ at hh
  rw [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one,
    Matrix.zero_vecMul] at hh
  have hc := congrFun hh (⟨i, d, Finsupp.single_le_iff.mpr h⟩ : ColumnIndex)
  exact (mul_eq_zero.mp hc).resolve_left relation_det_ne_zero

end CycleQ2HiggsSocleSyzygies

namespace CycleQ2HiggsSocle
open CycleQ2FermatJacobian
theorem trace_multiple (d : Row) (i : Fin 5) (h : cutoff i ≤ exp d i) :
    trace (multiple d i) = 0 := CycleQ2HiggsSocleSyzygies.trace_multiple d i h
end CycleQ2HiggsSocle
end

#print axioms CycleQ2HiggsSocleSyzygies.trace_multiple

/-!
# Complementary monomials in the universal weighted Jacobian ring

The socle functional pairs each bounded Fermat monomial with its unique
complement. This gives a determinant with Fermat value one. Wherever this
determinant is nonzero and the functional descends to the Jacobian quotient,
both monomial families in the quotient are linearly independent.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2HiggsGram

open MvPolynomial Matrix CycleQ2FermatHiggs CycleQ2FermatJacobian
open CycleQ2GenericSexticGradient CycleQ2HiggsSocle

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exponent of the unique complementary monomial in the Fermat socle box. -/
def complementExp (d : Exp) : Exp := exponent socle - d

omit [Fintype ι] [DecidableEq ι] in
theorem pair_exponents_eq_top_iff (e : ι → Exp) (hinj : Function.Injective e)
    (hbound : ∀ i, e i ≤ exponent socle) (i j : ι) :
    complementExp (e i) + e j = exponent socle ↔ i = j := by
  constructor
  · intro h
    apply hinj
    exact add_left_cancel ((tsub_add_cancel_of_le (hbound i)).trans h.symm)
  · rintro rfl
    exact tsub_add_cancel_of_le (hbound i)

/-- Entries and determinant are functions on the full coefficient space. -/
def gram (e : ι → Exp) : Matrix ι ι CoeffRing := Matrix.of fun i j =>
  CycleQ2HiggsSocle.trace
    (monomial (complementExp (e i)) 1 * monomial (e j) 1)

omit [Fintype ι] in
theorem gram_seed (e : ι → Exp) (hinj : Function.Injective e)
    (hbound : ∀ i, e i ≤ exponent socle) : (gram e).map seedEvaluation = 1 := by
  ext i j
  change seedEvaluation (CycleQ2HiggsSocle.trace _) = _
  rw [seed_trace]
  simp only [map_monomial, map_one, monomial_mul, one_mul, coeff_monomial,
    pair_exponents_eq_top_iff e hinj hbound, Matrix.one_apply]

theorem gram_det_seed (e : ι → Exp) (hinj : Function.Injective e)
    (hbound : ∀ i, e i ≤ exponent socle) : seedEvaluation (gram e).det = 1 := by
  rw [RingHom.map_det]
  change ((gram e).map seedEvaluation).det = 1
  rw [gram_seed e hinj hbound, Matrix.det_one]

omit [Fintype ι] [DecidableEq ι] in
theorem gram_map_entry {K : Type*} [CommRing K] (f : CoeffRing →+* K) (e : ι → Exp) (i j : ι) :
    (gram e).map f i j = traceAt f (monomial (complementExp (e i)) 1 * monomial (e j) 1) := by
  change f (CycleQ2HiggsSocle.trace _) = _
  rw [map_trace]
  simp only [map_mul, map_monomial, map_one]

/-- Every coefficient used by the universal functional has degree 18 and character 2. -/
theorem socle_row_weight (r : Row) :
    Finsupp.weight CycleQ2IncidenceNormalForm.fullGrading (CycleQ2HiggsSocle.exp r) = (18, 2) := by
  rw [CycleQ2IncidenceNormalForm.fullGrading_weight]
  apply Prod.ext
  · exact r.property.1
  · exact (ZMod.natCast_eq_natCast_iff' _ 2 3).mpr r.property.2

/-- Projecting an arbitrary polynomial onto the socle bidegree preserves its trace. -/
theorem traceAt_component {K : Type*} [CommRing K] (f : CoeffRing →+* K)
    (p : MvPolynomial (Fin 5) K) :
    traceAt f (weightedHomogeneousComponent CycleQ2IncidenceNormalForm.fullGrading (18, 2) p) =
      traceAt f p := by
  apply traceAt_congr
  funext r
  simp only [coefficients, LinearMap.pi_apply, lcoeff_apply, coeff_weightedHomogeneousComponent,
    if_pos (socle_row_weight r)]

private theorem independent_of_gram {K Q : Type*} [Field K] [CommRing Q] [Algebra K Q]
    (t : Q →ₗ[K] K) (x y : ι → Q) (M : Matrix ι ι K) (hdet : M.det ≠ 0)
    (hM : ∀ i j, M i j = t (y i * x j)) : LinearIndependent K x := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hzero : M.mulVec c = 0 := by
    funext j
    let L := t.comp (LinearMap.mulLeft K (y j))
    have h := congrArg L hc
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
    change ∑ k, M j k * c k = 0
    simpa only [hM, LinearMap.comp_apply, LinearMap.mulLeft_apply, L, mul_comm] using h
  exact congrFun (Matrix.mulVec_injective_of_det_ne_zero hdet (hzero.trans (M.mulVec_zero).symm)) i

/-- The same nonvanishing determinant detects both families of actual quotient classes. -/
theorem independent_mod_ideal {K : Type*} [Field K] (f : CoeffRing →+* K) (e : ι → Exp)
    (I : Ideal (MvPolynomial (Fin 5) K)) (hI : ∀ p ∈ I, traceAt f p = 0)
    (hd : f (gram e).det ≠ 0) :
    LinearIndependent K (fun i => Ideal.Quotient.mk I (monomial (e i) 1)) ∧
      LinearIndependent K (fun i => Ideal.Quotient.mk I (monomial (complementExp (e i)) 1)) := by
  let t : (MvPolynomial (Fin 5) K ⧸ I) →ₗ[K] K :=
    (I.restrictScalars K).liftQ (traceAt f) (fun p hp => hI p hp)
  let x (i : ι) := Ideal.Quotient.mk I (monomial (e i) 1)
  let y (i : ι) := Ideal.Quotient.mk I (monomial (complementExp (e i)) 1)
  let M := (gram e).map f
  have hM : ∀ i j, M i j = t (y i * x j) := fun i j => gram_map_entry f e i j
  have hdet : M.det ≠ 0 := by rwa [RingHom.map_det] at hd
  refine ⟨independent_of_gram t x y M hdet hM, independent_of_gram t y x M.transpose ?_ ?_⟩
  · simpa only [Matrix.det_transpose] using hdet
  · intro i j
    rw [Matrix.transpose_apply, hM, mul_comm]

end CycleQ2HiggsGram
end

#print axioms CycleQ2HiggsGram.gram_det_seed
#print axioms CycleQ2HiggsGram.independent_mod_ideal

/-!
# The socle trace on the actual specialized Jacobian ring

An arbitrary polynomial in the Jacobian ideal has homogeneous multipliers
for its degree-18, character-2 component. Every monomial of those multipliers
gives one of the columns annihilated by the universal Koszul relations. The
polynomial trace consequently descends to the entire Jacobian quotient after
every coefficient specialization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2HiggsSocle

open MvPolynomial CycleQ2FermatHiggs CycleQ2FermatJacobian CycleQ2GenericSexticGradient
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

variable {K : Type*} [CommRing K] (φ : CoeffRing →+* K)

abbrev specializedJacobian : Ideal (MvPolynomial (Fin 5) K) :=
  Ideal.span (Set.range fun i : Fin 5 => pderiv i (MvPolynomial.map φ universalF))

private theorem row_after_cutoff (i : Fin 5) (m : Exp)
    (hm : Finsupp.weight fullGrading m =
      (18 - (6 - (fullGrading i).1), 2 + (fullGrading i).2)) :
    ∃ d : Row, exp d = m + Finsupp.single i (cutoff i) := by
  let a := m + Finsupp.single i (cutoff i)
  have hg : Finsupp.weight fullGrading a = (18, 2) := by
    rw [show a = m + Finsupp.single i (cutoff i) from rfl, map_add, hm, Finsupp.weight_single]
    fin_cases i <;> decide
  rw [fullGrading_weight] at hg
  have hd : weightedDegree a = 18 := congrArg Prod.fst hg
  have hc := congrArg (fun z : ℕ × ZMod 3 => z.2.val) hg
  change ((2 * a 0 + 2 * a 1 + a 2 : ℕ) : ZMod 3).val = 2 at hc
  rw [ZMod.val_natCast] at hc
  exact ⟨rowOfExp a hd hc, exp_rowOfExp a hd hc⟩

private theorem monomial_partial_trace (i : Fin 5) (m : Exp) (c : K)
    (hm : Finsupp.weight fullGrading m =
      (18 - (6 - (fullGrading i).1), 2 + (fullGrading i).2)) :
    traceAt φ (monomial m c * pderiv i (MvPolynomial.map φ universalF)) = 0 := by
  obtain ⟨d, hd⟩ := row_after_cutoff i m hm
  have hi : cutoff i ≤ exp d i := by
    rw [hd, Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  have hz := traceAt_multiple φ d i
  rw [trace_multiple d i hi, map_zero, hd, add_tsub_cancel_right] at hz
  have hc : monomial m c = c • (monomial m 1 : MvPolynomial (Fin 5) K) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hc, smul_mul_assoc, map_smul, hz, smul_zero]

/-- All Jacobian-ideal elements have zero trace after arbitrary specialization. -/
theorem traceAt_mem_ideal (p : MvPolynomial (Fin 5) K) (hp : p ∈ specializedJacobian φ) :
    traceAt φ p = 0 := by
  classical
  obtain ⟨h, hh, _, hcomponent⟩ :=
    CycleQ2HiggsJacobianMembership.component_multipliers φ 18 2 p hp
  rw [← CycleQ2HiggsGram.traceAt_component φ p, hcomponent, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [(h i).as_sum, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro m hm
  exact monomial_partial_trace φ i m _ (hh i (mem_support_iff.mp hm))

def quotientTrace : (MvPolynomial (Fin 5) K ⧸ specializedJacobian φ) →ₗ[K] K :=
  ((specializedJacobian φ).restrictScalars K).liftQ (traceAt φ)
    (fun p hp => traceAt_mem_ideal φ p hp)

@[simp] theorem quotientTrace_mk (p : MvPolynomial (Fin 5) K) :
    quotientTrace φ (Ideal.Quotient.mk (specializedJacobian φ) p) = traceAt φ p := rfl

theorem quotientTrace_socle :
    quotientTrace φ (Ideal.Quotient.mk (specializedJacobian φ)
      (monomial (exponent socle) 1)) = φ macaulay.det := by
  have h := map_trace φ (monomial (exponent socle) 1)
  rw [trace_socle, map_monomial, map_one] at h
  exact h.symm

/-- The family Higgs matrix consists of trace values of actual Jacobian-quotient classes. -/
theorem H_quotientTrace (m : Fin 35) (i j : Fin 33) :
    (H m).map φ i j =
      quotientTrace φ (Ideal.Quotient.mk (specializedJacobian φ) (triple K m i j)) := by
  have h := map_trace φ (triple CoeffRing m i j)
  simp only [triple, map_mul, map_monomial, map_one] at h
  exact h

end CycleQ2HiggsSocle
end

#print axioms CycleQ2HiggsSocle.traceAt_mem_ideal
#print axioms CycleQ2HiggsSocle.quotientTrace_mk

#print axioms CycleQ2HiggsSocle.H_quotientTrace

/-!
# Monomial bases for the specialized weighted Jacobian components

The spanning determinant and the complementary Gram determinant give a
basis of each degree and character component of the full sextic Jacobian
quotient. Both determinants evaluate to one at the Fermat point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2HiggsJacobianFrames

open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation)
open CycleQ2HiggsGram

/-- Gram determinant for the Fermat-standard monomials of this bidegree. -/
def gramDet (n : ℕ) (χ : ZMod 3) : CoeffRing := by
  classical
  exact (gram (fun e : Bounded n χ => exp e.val)).det

theorem gramDet_seed (n : ℕ) (χ : ZMod 3) : seedEvaluation (gramDet n χ) = 1 := by
  classical
  apply gram_det_seed
  · exact exp_injective.comp Subtype.val_injective
  · intro e i
    exact Nat.le_of_lt_succ (e.property i)

variable {K : Type} [Field K] (φ : CoeffRing →+* K)

theorem boundedClass_independent {n : ℕ} {χ : ZMod 3} (hd : φ (gramDet n χ) ≠ 0) :
    LinearIndependent K (boundedClass φ (n := n) (χ := χ)) := by
  classical
  exact (independent_mod_ideal φ (fun e : Bounded n χ => exp e.val) (jacobian φ)
    (CycleQ2HiggsSocle.traceAt_mem_ideal φ) hd).1

/-- The basis lies in the image of actual weighted homogeneous polynomials in the quotient. -/
def basis (n : ℕ) (χ : ZMod 3) (hframe : IsUnit (φ (frameDet n χ))) (hgram : φ (gramDet n χ) ≠ 0) :
    Module.Basis (Bounded n χ) K (gradedPiece φ n χ) :=
  (Module.Basis.span (boundedClass_independent φ hgram)).map
    (LinearEquiv.ofEq _ _ (gradedPiece_eq_span φ hframe).symm)

@[simp] theorem basis_coe (n : ℕ) (χ : ZMod 3) (hframe : IsUnit (φ (frameDet n χ)))
    (hgram : φ (gramDet n χ) ≠ 0) (e : Bounded n χ) :
    (basis φ n χ hframe hgram e : QuotientRing φ) = boundedClass φ e := by
  simp [basis]

theorem gradedPiece_finrank (n : ℕ) (χ : ZMod 3) (hframe : IsUnit (φ (frameDet n χ)))
    (hgram : φ (gramDet n χ) ≠ 0) : Module.finrank K (gradedPiece φ n χ) = Nat.card (Bounded n χ) := by
  classical
  rw [Module.finrank_eq_card_basis (basis φ n χ hframe hgram), Nat.card_eq_fintype_card]

end CycleQ2HiggsJacobianFrames
end

#print axioms CycleQ2HiggsJacobianFrames.gramDet_seed
#print axioms CycleQ2HiggsJacobianFrames.basis_coe
#print axioms CycleQ2HiggsJacobianFrames.gradedPiece_finrank
