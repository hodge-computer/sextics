import Proposal.GeometricLiteralAmbientSmooth
import Proposal.GeometricLiteralAbelJacobiContraction
import Proposal.GeometricIncidenceChartDerivatives
import Proposal.GeometricIncidenceChartSeedFiber

/-!
# The Jacobian cover of the fixed threefold charts

On each shifted four-variable chart of the literal threefold, the four
partials of the affine equation generate the unit ideal. The triangular
coordinate derivative formula transfers the homogeneous Jacobian criterion
to the same chart equation used in the curve presentation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAmbientChartJacobian

open MvPolynomial CycleQ2IncidenceEquations CycleQ2IncidenceDehomogenizedChart
  CycleQ2IncidenceChartDerivatives CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAmbientSmooth

/-- The actual derivative class in the fixed affine coordinate ring. -/
abbrev derivative (i : Fin 4) (a : Option (Fin 3)) : T i :=
  Ideal.Quotient.mk (fixedIdeal i) (pderiv a (seedF i))

/-- At least one chart derivative survives in every prime quotient. -/
theorem exists_derivative_not_mem (i : Fin 4) (M : Ideal (T i)) [M.IsPrime] :
    ∃ a : Option (Fin 3), derivative i a ∉ M := by
  let q := Ideal.Quotient.mk (fixedIdeal i)
  let J := M.comap (q.comp (dehomogenize (S := ℂ) i).toRingHom)
  let : J.IsPrime := inferInstance
  have hseed : dehomogenize i (smoothF (57 : ℂ) Complex.I) = seedF i := by
    unfold seedF
    rw [← CycleQ2IncidenceChartSeedFiber.literal_pointEquationF]
  have hF : smoothF (57 : ℂ) Complex.I ∈ J := by
    change q (dehomogenize i (smoothF (57 : ℂ) Complex.I)) ∈ M
    rw [hseed]
    have hz : q (seedF i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [hz]
    exact M.zero_mem
  have hi : (X i.castSucc - 1 : MvPolynomial (Fin 5) ℂ) ∈ J := by
    change q (dehomogenize i (X i.castSucc - 1)) ∈ M
    simp
  obtain ⟨⟨j, hj⟩, hδ⟩ := literal_exists_other_derivative 57 i J hF hi
    (literal_jacobian_cover J i hi hF)
  obtain ⟨a, rfl⟩ := exists_chartIndex_of_ne i j hj
  by_contra! h
  apply hδ
  change q (dehomogenize i (pderiv (chartIndex i a) (smoothF (57 : ℂ) Complex.I))) ∈ M
  rw [dehomogenize_pderiv_chartIndex, hseed, map_add, map_mul]
  exact M.add_mem (h a) (M.mul_mem_left _ (h none))

/-- The four chart partials generate the unit ideal in the fixed affine ring. -/
theorem derivatives_span_top (i : Fin 4) : Ideal.span (Set.range (derivative i)) = ⊤ := by
  by_contra h
  obtain ⟨M, hm, hle⟩ := Ideal.exists_le_maximal _ h
  let : M.IsPrime := hm.isPrime
  obtain ⟨a, ha⟩ := exists_derivative_not_mem i M
  exact ha (hle (Ideal.subset_span ⟨a, rfl⟩))

/-- The four derivative opens cover the full shifted chart. -/
theorem derivative_opens_cover (i : Fin 4) :
    (⨆ a : Option (Fin 3), PrimeSpectrum.basicOpen (derivative i a)) = ⊤ :=
  PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr (derivatives_span_top i)

end CycleQ2LiteralAmbientChartJacobian

end

#print axioms CycleQ2LiteralAmbientChartJacobian.derivatives_span_top
#print axioms CycleQ2LiteralAmbientChartJacobian.derivative_opens_cover
