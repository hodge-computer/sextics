import Proposal.GeometricLiteralThreefoldLiftDifference

/-! Infinitesimal coordinate coefficients of the canonical lift on the full fixed chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldVolumeVariation

open MvPolynomial CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference

abbrev canonicalPoint (i : Fin 4) := canonical i (AlgHom.id ℂ (T i))

/-- Polynomial representatives of all four velocities of the fixed canonical lift. -/
def Represents (i : Fin 4) (V : Index → P) : Prop :=
  ∀ j, q i (V j) = ((canonicalPoint i).x j).snd

theorem exists_representatives (i : Fin 4) : ∃ V, Represents i V := by
  classical
  choose V h using fun j : Index => Ideal.Quotient.mk_surjective (((canonicalPoint i).x j).snd)
  exact ⟨V, h⟩

def action (V : Index → P) (p : P) : P := ∑ j, V j * pderiv j p

def divergence (V : Index → P) : P := ∑ j, pderiv j (V j)

private theorem action_sum (V : Index → P) (p : P) :
    (∑ j, V j • pderiv j : Derivation ℂ P P) p = action V p := by
  simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply, Derivation.smul_apply,
    smul_eq_mul, action] using
      congrFun (map_sum Derivation.coeFnAddMonoidHom (fun j => V j • pderiv j) Finset.univ) p

private theorem action_X (V : Index → P) (j : Index) : action V (X j) = V j := by
  classical
  simp [action, pderiv_X, Pi.single_apply, apply_ite]

private theorem canonical_eval_fst (i : Fin 4) (p : P) :
    (aeval (canonicalPoint i).x p).fst = q i p :=
  eval_fst _ _ (canonical_liesOver i (AlgHom.id ℂ (T i))) p

/-- The actual infinitesimal value of every polynomial is its derivative along
any polynomial representative of the four canonical velocities. -/
theorem canonical_eval_snd {i : Fin 4} {V : Index → P} (hV : Represents i V) (p : P) :
    (aeval (canonicalPoint i).x p).snd = q i (action V p) := by
  let D : Derivation ℂ P (T i) := jetDerivation (aeval (canonicalPoint i).x)
    (fun p => canonical_eval_fst i p)
  let E : Derivation ℂ P (T i) := (Algebra.ofId P (T i)).toLinearMap.compDer
    (∑ j, V j • pderiv j)
  have eq : D = E := by
    apply MvPolynomial.derivation_ext
    intro j
    change (aeval (canonicalPoint i).x (X j)).snd = q i ((∑ j, V j • pderiv j : Derivation ℂ P P) (X j))
    rw [aeval_X, action_sum, action_X, hV j]
  change D p = _
  rw [eq]
  change q i ((∑ j, V j • pderiv j : Derivation ℂ P P) p) = _
  rw [action_sum]

/-- The multiplier records the change in the chosen defining equation. -/
def IsMultiplier (i : Fin 4) (V : Index → P) (H : P) : Prop :=
  action V (seedF i) - test i = seedF i * H

theorem exists_multiplier {i : Fin 4} {V : Index → P} (hV : Represents i V) :
    ∃ H, IsMultiplier i V H := by
  have he := congrArg TrivSqZeroExt.snd (canonicalPoint i).equation
  change (aeval (canonicalPoint i).x (seedF i)).snd =
    0 * (aeval (canonicalPoint i).x (test i)).snd + 1 * (aeval (canonicalPoint i).x (test i)).fst at he
  rw [canonical_eval_snd hV, canonical_eval_fst, zero_mul, one_mul, zero_add] at he
  have hz : q i (action V (seedF i) - test i) = 0 := by rw [map_sub, he, sub_self]
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- The coefficient after dividing the ambient volume by the defining equation. -/
def residueCoefficient (i : Fin 4) (V : Index → P) (H : P) : T i :=
  q i (divergence V - H)


private theorem mixed_partials (j l : Index) (p : P) :
    pderiv j (pderiv l p) = pderiv l (pderiv j p) := by
  classical
  by_cases h : j = l
  · subst l; rfl
  ext m
  simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply,
    if_neg h, if_neg (Ne.symm h), add_zero]
  rw [show m + Finsupp.single j 1 + Finsupp.single l 1 =
    m + Finsupp.single l 1 + Finsupp.single j 1 by abel]
  ring

private theorem pderiv_action (j : Index) (V : Index → P) (p : P) :
    pderiv j (action V p) = action V (pderiv j p) + ∑ l, pderiv j (V l) * pderiv l p := by
  simp only [action, map_sum, pderiv_mul, Finset.sum_add_distrib]
  have hc : (∑ l, V l * pderiv j (pderiv l p)) = ∑ l, V l * pderiv l (pderiv j p) :=
    Finset.sum_congr rfl fun l _ => congrArg (V l * ·) (mixed_partials j l p)
  rw [hc, add_comm]

private theorem equation_zero (i : Fin 4) : q i (seedF i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The actual jet of a partial derivative of the deformed equation `F − ε B`. -/
def gradientJet (i : Fin 4) (j : Index) : Jet (T i) :=
  aeval (canonicalPoint i).x (pderiv j (seedF i)) -
    (TrivSqZeroExt.inr 1 : Jet (T i)) * aeval (canonicalPoint i).x (pderiv j (test i))

theorem gradientJet_snd {i : Fin 4} {V : Index → P} (hV : Represents i V) (j : Index) :
    (gradientJet i j).snd = q i (action V (pderiv j (seedF i)) - pderiv j (test i)) := by
  change (aeval (canonicalPoint i).x (pderiv j (seedF i))).snd -
    (0 * (aeval (canonicalPoint i).x (pderiv j (test i))).snd +
     1 * (aeval (canonicalPoint i).x (pderiv j (test i))).fst) = _
  rw [canonical_eval_snd hV, canonical_eval_fst, zero_mul, one_mul, zero_add, map_sub]

/-- First-order cofactor formula on the full chart. On the left the
deformed gradient multiplies the residue coefficient to first order.
The right side is the sum of the four coordinate-minor variations. -/
theorem cofactor_variation {i : Fin 4} {V : Index → P} {H : P}
    (hV : Represents i V) (hH : IsMultiplier i V H) (j : Index) :
    q i (pderiv j (seedF i)) * residueCoefficient i V H + (gradientJet i j).snd =
      q i (∑ l, (pderiv j (seedF i) * pderiv l (V l) -
        pderiv j (V l) * pderiv l (seedF i))) := by
  have hd := congrArg (fun p : P => q i (pderiv j p)) hH
  change q i (pderiv j (action V (seedF i) - test i)) =
    q i (pderiv j (seedF i * H)) at hd
  rw [map_sub, pderiv_action, pderiv_mul, map_sub, map_add, map_add, map_mul, map_mul,
    equation_zero, zero_mul, add_zero] at hd
  rw [gradientJet_snd hV, residueCoefficient, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← divergence, map_sub, map_sub, map_sub, map_mul]
  linear_combination hd

/-- Multiplication by the normalized residue jet recovers the entire first-order
coordinate cofactor, including its ordinary gradient as constant term. -/
theorem gradientJet_mul_residueJet {i : Fin 4} {V : Index → P} {H : P}
    (hV : Represents i V) (hH : IsMultiplier i V H) (j : Index) :
    gradientJet i j * (1 + TrivSqZeroExt.inr (residueCoefficient i V H) : Jet (T i)) =
      (TrivSqZeroExt.inl (q i (pderiv j (seedF i))) +
       TrivSqZeroExt.inr (q i (∑ l, (pderiv j (seedF i) * pderiv l (V l) -
        pderiv j (V l) * pderiv l (seedF i)))) : Jet (T i)) := by
  have hf : (gradientJet i j).fst = q i (pderiv j (seedF i)) := by
    change (aeval (canonicalPoint i).x (pderiv j (seedF i))).fst -
      0 * (aeval (canonicalPoint i).x (pderiv j (test i))).fst = _
    rw [canonical_eval_fst, zero_mul, sub_zero]
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_mul, hf]
  · simp only [DualNumber.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, TrivSqZeroExt.fst_inr,
      TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_inl, add_zero, zero_add,
      hf, mul_one]
    exact cofactor_variation hV hH j

private theorem equation_ne_zero (i : Fin 4) : seedF i ≠ 0 := by
  intro hf
  let : Nontrivial (T i) := Ideal.Quotient.nontrivial_iff.mpr (by
    simp [fixedIdeal, hf])
  have hn (j : Index) : CycleQ2LiteralAmbientChartJacobian.derivative i j = 0 := by
    change q i (pderiv j (seedF i)) = 0
    rw [hf, map_zero, map_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp
    ((Ideal.eq_top_iff_one _).mp (CycleQ2LiteralAmbientChartJacobian.derivatives_span_top i))
  simp [hn] at hc

/-- The corrected coefficient depends only on the canonical velocities and
is unchanged by any polynomial lifts or defining-equation multipliers. -/
theorem residueCoefficient_independent {i : Fin 4} {V W : Index → P} {H J : P}
    (hV : Represents i V) (hW : Represents i W) (hH : IsMultiplier i V H)
    (hJ : IsMultiplier i W J) : residueCoefficient i V H = residueCoefficient i W J := by
  have hz (l : Index) : ∃ z : P, W l = V l + seedF i * z := by
    have hq : q i (W l - V l) = 0 := by rw [map_sub, hW l, hV l, sub_self]
    obtain ⟨z, h⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hq)
    exact ⟨z, by linear_combination h⟩
  choose z hz using hz
  let Z := ∑ l, z l * pderiv l (seedF i)
  have ha : action W (seedF i) = action V (seedF i) + seedF i * Z := by
    change (∑ l, W l * _) = (∑ l, V l * _) + seedF i * ∑ l, z l * _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hz]; ring
  have hh : J = H + Z := by
    apply mul_left_cancel₀ (equation_ne_zero i)
    unfold IsMultiplier at hH hJ
    linear_combination -hJ + hH + ha
  have hdiv : divergence W = divergence V + Z + seedF i * divergence z := by
    unfold divergence Z
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hz, map_add, pderiv_mul]; ring
  simp only [residueCoefficient, hdiv, hh, map_add, map_sub, map_mul, equation_zero,
    zero_mul, add_zero]
  ring

/-- The canonical chart coefficient with no choice of ambient representatives in its statement. -/
theorem existsUnique_residueCoefficient (i : Fin 4) :
    ∃! c : T i, ∀ (V : Index → P) (H : P), Represents i V → IsMultiplier i V H →
      residueCoefficient i V H = c := by
  obtain ⟨V, hV⟩ := exists_representatives i
  obtain ⟨H, hH⟩ := exists_multiplier hV
  exact ⟨residueCoefficient i V H, fun _ _ hW hJ => residueCoefficient_independent hW hV hJ hH,
    fun c hc => (hc V H hV hH).symm⟩

end CycleQ2LiteralThreefoldVolumeVariation
end
