import Proposal.GeometricLiteralThreefoldTestEdges

/-!
# The determinant in the shifted coordinate of the fixed threefold

The first affine coordinate is the shifted weight-two variable. Its differential
can have off-diagonal entries, while each of the three remaining coordinate
differentials is scaled. Expansion along the first row computes the determinant.
The equation differential then identifies the change in the hypersurface
residue, using all four Jacobian pivots.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldOrbitVolume

open Module MvPolynomial CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralThreefoldResidueFrame
  CycleQ2LiteralThreefoldResidueMinors CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldResidueGluing CycleQ2LiteralThreefoldChartVolume
  CycleQ2ExteriorSectionNaturality
open scoped TensorProduct

private def basis (i : Fin 4) : Basis (Fin 4) (T i) (T i ⊗[P] KaehlerDifferential ℂ P) :=
  ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).baseChange (T i)).reindex coordIndex.symm

private def column (i : Fin 4) (p : P) : T i ⊗[P] KaehlerDifferential ℂ P :=
  (1 : T i) ⊗ₜ[P] KaehlerDifferential.D ℂ P p

private theorem basis_apply (i j : Fin 4) : basis i j = column i (X (coordIndex j)) := by
  simp only [basis, Basis.reindex_apply, Equiv.symm_symm, Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, column]

private theorem column_repr (i j : Fin 4) (p : P) :
    (basis i).repr (column i p) j = algebraMap P (T i) (pderiv (coordIndex j) p) := by
  simp only [basis, column, Basis.repr_reindex_apply, Equiv.symm_symm,
    Basis.baseChange_repr_tmul, KaehlerDifferential.mvPolynomialBasis_repr_apply,
    Algebra.smul_def, mul_one]

private theorem column_det (i : Fin 4) (y : Option (Fin 3) → P) (d : ℂ) (s : Fin 3 → ℂ)
    (h₀ : pderiv none (y none) = C d) (h : ∀ k, y (some k) = C (s k) * X (some k)) :
    (basis i).det (fun j => column i (y (coordIndex j))) =
      algebraMap ℂ (T i) (d * ∏ k, s k) := by
  let m := (basis i).toMatrix (fun j => column i (y (coordIndex j)))
  have hz (j : Fin 3) : m 0 j.succ = 0 := by
    simp [m, Basis.toMatrix_apply, column_repr, coordIndex, h, pderiv_X]
  have h00 : m 0 0 = algebraMap ℂ (T i) d := by
    change (basis i).repr (column i (y none)) 0 = _
    rw [column_repr]
    exact congrArg (algebraMap P (T i)) h₀
  have hdiag (j k : Fin 3) :
      m j.succ k.succ = if j = k then algebraMap ℂ (T i) (s k) else 0 := by
    by_cases he : j = k
    · subst k
      simp [m, Basis.toMatrix_apply, column_repr, coordIndex, h, pderiv_X]
      rfl
    · simp [m, Basis.toMatrix_apply, column_repr, coordIndex, h, pderiv_X, he, Ne.symm he]
  change m.det = _
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul, hz, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, h00, Matrix.submatrix_apply,
    Fin.succAbove_zero, Matrix.det_fin_three, hdiag, Fin.prod_univ_three, map_mul]
  simp

private abbrev mk (i : Fin 4) := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)

set_option maxHeartbeats 1100000 in
theorem chartVolume_triangular (i : Fin 4) (a : P →ₐ[ℂ] P) (f : T i →ₐ[ℂ] T i)
    (hf : ∀ p, f (mk i p) = mk i (a p)) (heq : a (seedF i) = seedF i)
    (d : ℂ) (s : Fin 3 → ℂ) (h₀ : pderiv none (a (X none)) = C d)
    (h : ∀ k, a (X (some k)) = C (s k) * X (some k)) :
    exteriorDifferentialMap f 3 (chartVolume i) =
      algebraMap ℂ (T i) (d * ∏ k, s k) • chartVolume i := by
  let y := fun k => a (X k)
  let x := fun k : Option (Fin 3) => (X k : P)
  have hy : aeval y = a := by
    apply MvPolynomial.algHom_ext
    intro k
    exact aeval_X y k
  have hx : aeval x = AlgHom.id ℂ P := by
    apply MvPolynomial.algHom_ext
    intro k
    exact aeval_X x k
  have hzero : mk i (seedF i) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hzy : algebraMap P (T i) (aeval y (seedF i)) = 0 := by rw [hy, heq]; exact hzero
  have hzx : algebraMap P (T i) (aeval x (seedF i)) = 0 := by rw [hx]; exact hzero
  have hfy : chartMapAlgHom (T i) i y hzy = f := by
    ext t
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective t
    change mk i (aeval y p) = f (mk i p)
    rw [hy, hf]
  have hfx : chartMapAlgHom (T i) i x hzx = AlgHom.id ℂ (T i) := by
    ext t
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective t
    change mk i (aeval x p) = mk i p
    rw [hx]
    rfl
  let b := basis i
  let v := fun j => column i (y (coordIndex j))
  let q := KaehlerDifferential.mapBaseChange ℂ P (T i)
  have hxq : q ∘ b = coordinateForm i (AlgHom.id ℂ (T i)) := by
    rw [← hfx]
    funext j
    dsimp only [Function.comp_apply, b, q]
    rw [basis_apply]
    exact map_restrictedDifferentials _ i x hzx j
  have hyq : q ∘ v = coordinateForm i f := by
    rw [← hfy]
    exact funext (map_restrictedDifferentials _ i y hzy)
  have hc : ∑ j, f (gradient i j) • v j = ∑ j, gradient i j • b j := by
    have A := chartConormal_gradient (T i) i x hzx
    have B := chartConormal_gradient (T i) i y hzy
    change _ = ∑ j, chartMapAlgHom _ i x hzx (gradient i j) • column i (x (coordIndex j)) at A
    change _ = ∑ j, chartMapAlgHom _ i y hzy (gradient i j) • v j at B
    rw [hfx, hx] at A
    rw [hfy, hy, heq] at B
    simpa only [b, x, AlgHom.id_apply, basis_apply] using B.symm.trans A
  have hqs : ∑ j, gradient i j • q (b j) = 0 := by
    change ∑ j, gradient i j • (q ∘ b) j = 0
    rw [hxq]
    exact gradient_relation i (AlgHom.id ℂ (T i))
  have hid : exteriorDifferentialMap (AlgHom.id ℂ (T i)) 3 (chartVolume i) = chartVolume i :=
    CycleQ2GeometricExteriorSheaf.exteriorMap_identity (AlgHom.id ℂ (T i)).toRingHom
      (differentialSemilinearMap (AlgHom.id ℂ (T i)))
      (fun _ => rfl) (fun ω => CycleQ2GeometricAffineOverlap.differentialMap_id ω) 3 (chartVolume i)
  obtain ⟨c, hc₁⟩ := chartBezout i
  have hc₂ : ∑ j, f (c j) * f (gradient i j) = 1 := by
    simpa only [map_one, map_sum, map_mul] using congrArg f hc₁
  have e := bezout_residue_change b q (gradient i) (fun j => f (gradient i j)) c (fun j => f (c j))
    hc₁ hc₂ v 1 (algebraMap ℂ (T i) (d * ∏ k, s k)) 1 isUnit_one
    (by simpa only [one_mul] using column_det i y d s h₀ h) (by simpa only [one_smul] using hc) hqs
    (chartVolume i) (exteriorDifferentialMap f 3 (chartVolume i))
    (fun j => by rw [hxq, ← hid]; exact gradient_smul_chartVolume i (AlgHom.id ℂ (T i)) j)
    (fun j => by rw [hyq]; exact gradient_smul_chartVolume i f j)
  simpa only [one_smul] using e

end CycleQ2LiteralThreefoldOrbitVolume
end

#print axioms CycleQ2LiteralThreefoldOrbitVolume.chartVolume_triangular
