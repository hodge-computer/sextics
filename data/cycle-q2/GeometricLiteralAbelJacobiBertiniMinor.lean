import Proposal.GeometricLiteralAbelJacobiBertini
import Proposal.GeometricLiteralAbelJacobiSeedLiftPoints
import Proposal.GeometricIncidenceChartMinorCover
import Proposal.GeometricIncidenceSeedChartMinorCover

/-!
# Smooth members of the original moving section system

At a prime of one of the four original seed curve charts, the surface
Jacobian has rank two. A nonzero matrix pivot and an algebraically
independent choice of the three complex coefficients supply a tangent
vector on which the corresponding row varies. Expansion by minors
then gives rank three for both surface equations and that same row.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

namespace CycleQ2LiteralAbelJacobiBertiniMinor

open scoped BigOperators

/-- If two equations have a nonsingular two-column minor and a tangent
vector to them makes a third equation vary, the three equations have a
nonsingular three-column minor. -/
theorem exists_embedding {ι K : Type*} [Fintype ι] [Field K]
    (A : Matrix (Fin 3) ι K) (v : ι → K) (j k : ι)
    (hminor : A 0 j * A 1 k - A 0 k * A 1 j ≠ 0)
    (h0 : ∑ a, A 0 a * v a = 0) (h1 : ∑ a, A 1 a * v a = 0)
    (h2 : ∑ a, A 2 a * v a ≠ 0) : ∃ q : Fin 3 ↪ ι, (A.submatrix id q).det ≠ 0 := by
  classical
  by_contra! h
  let c (x : ι) : Fin 3 → ι := ![j,k,x]
  have hz (x : ι) : (A.submatrix id (c x)).det = 0 := by
    by_cases hi : Function.Injective (c x)
    · exact h ⟨c x, hi⟩
    · obtain ⟨u, w, hw, hn⟩ := Function.not_injective_iff.mp hi
      exact Matrix.det_zero_of_column_eq hn (fun row => congrArg (A row) hw)
  let b0 := A 1 j * A 2 k - A 1 k * A 2 j
  let b1 := A 0 k * A 2 j - A 0 j * A 2 k
  let b2 := A 0 j * A 1 k - A 0 k * A 1 j
  have he (x : ι) : b0 * (A 0 x * v x) + b1 * (A 1 x * v x) + b2 * (A 2 x * v x) = 0 := by
    have hd := hz x
    simp [Matrix.det_fin_three, Matrix.submatrix_apply, c] at hd
    unfold b0 b1 b2
    linear_combination (v x) * hd
  have hh : ∑ x, (b0 * (A 0 x * v x) + b1 * (A 1 x * v x) + b2 * (A 2 x * v x)) = 0 :=
    Finset.sum_eq_zero (fun x _ => he x)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, h0, h1, mul_zero, zero_add] at hh
  exact (mul_ne_zero hminor h2) hh

end CycleQ2LiteralAbelJacobiBertiniMinor

#print axioms CycleQ2LiteralAbelJacobiBertiniMinor.exists_embedding

noncomputable section
namespace CycleQ2LiteralAbelJacobiBertiniMinor

open MvPolynomial CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceDehomogenizedChart
  CycleQ2RelativeCurveChart CycleQ2RelativeConstantSection CycleQ2IncidenceChartDimension
  CycleQ2IncidenceChartMinorCover CycleQ2IncidenceSeedChartMinorCover

private abbrev seed := seedPoint (57 : ℂ) Complex.I

abbrev chartRows (t : Fin 3 → ℂ) (i : Fin 4) (a : Fin 3) : Fin 3 → ChartPolynomial ℂ :=
  Fin.snoc (dehomogenizedEquations seed i) (dehomogenize i (relativeSectionPolynomial seed t a))

abbrev polynomialMap (t : Fin 3 → ℂ) (i : Fin 4) :
    ChartPolynomial ℂ →+* AffineCurveChart seed t i :=
  (Ideal.Quotient.mk _).comp (dehomogenizedMap seed i)

/-- For every field-valued point on the original curve, one transverse
vector to the two surface equations produces an invertible minor of the three
actual rows, using the verified smooth seed Jacobian cover. -/
theorem chart_minor_of_tangent (t : Fin 3 → ℂ) (i : Fin 4) (a : Fin 3)
    {K : Type*} [Field K] (φ : AffineCurveChart seed t i →+* K) (v : Option (Fin 3) → K)
    (hF : ∑ j, φ (polynomialMap t i (pderiv j (dehomogenizedEquations seed i 0))) * v j = 0)
    (hH : ∑ j, φ (polynomialMap t i (pderiv j (dehomogenizedEquations seed i 1))) * v j = 0)
    (hs : ∑ j, φ (polynomialMap t i (pderiv j (dehomogenize i
      (relativeSectionPolynomial seed t a)))) * v j ≠ 0) :
    ∃ q : Fin 3 ↪ Option (Fin 3), φ (polynomialMap t i
      ((Matrix.of fun u r : Fin 3 => pderiv (q u) (chartRows t i a r)).det)) ≠ 0 := by
  classical
  let ψ := φ.comp (Ideal.Quotient.mk (affineSectionIdeal seed t i))
  let P := RingHom.ker ψ
  let : P.IsPrime := RingHom.ker_isPrime ψ
  obtain ⟨j, k, _, hminor⟩ := seed_prime_normalizedMinor_cover i P
  obtain ⟨p, _, h⟩ := exists_chartMinor_not_mem seed i P j k hminor
  let A : Matrix (Fin 3) (Option (Fin 3)) K := Matrix.of fun r x =>
    φ (polynomialMap t i (pderiv x (chartRows t i a r)))
  have hz : ψ (chartMinor seed i p) ≠ 0 := h
  simp only [chartMinor, map_sub, map_mul] at hz
  have ha : A 0 (p 0) * A 1 (p 1) - A 0 (p 1) * A 1 (p 0) ≠ 0 := by
    simpa [A, chartRows, Fin.snoc, ψ, polynomialMap] using hz
  have h0 : ∑ j, A 0 j * v j = 0 := by simpa [A, chartRows, Fin.snoc] using hF
  have h1 : ∑ j, A 1 j * v j = 0 := by simpa [A, chartRows, Fin.snoc] using hH
  have h2 : ∑ j, A 2 j * v j ≠ 0 := by simpa [A, chartRows, Fin.snoc] using hs
  obtain ⟨q, hq⟩ := exists_embedding A v (p 0) (p 1) ha h0 h1 h2
  use q
  have hm : φ (polynomialMap t i ((Matrix.of fun u r : Fin 3 =>
      pderiv (q u) (chartRows t i a r)).det)) = (A.submatrix id q).transpose.det :=
    (φ.comp (polynomialMap t i)).map_det _
  rwa [hm, Matrix.det_transpose]

/-- Viewing an actual field-valued point as an evaluation in ambient coordinates. -/
def polynomialPoint {K : Type*} [Field K] [Algebra ℂ K]
    (t : Fin 3 → ℂ) (i : Fin 4) (φ : AffineCurveChart seed t i →ₐ[ℂ] K) :
    ChartPolynomial ℂ →ₐ[ℂ] K :=
  φ.comp ((Ideal.Quotient.mkₐ ℂ (affineSectionIdeal seed t i)).comp
    (Ideal.Quotient.mkₐ ℂ (chartIdeal (dehomogenizedEquations seed i))))

@[simp] theorem polynomialPoint_apply {K : Type*} [Field K] [Algebra ℂ K]
    (t : Fin 3 → ℂ) (i : Fin 4) (φ : AffineCurveChart seed t i →ₐ[ℂ] K)
    (p : ChartPolynomial ℂ) : polynomialPoint t i φ p = φ (polynomialMap t i p) := rfl

/-- The field evaluation satisfies exactly the two seed equations. -/
theorem surface_aeval {K : Type*} [Field K] [Algebra ℂ K]
    (t : Fin 3 → ℂ) (i : Fin 4) (φ : AffineCurveChart seed t i →ₐ[ℂ] K) (r : Fin 2) :
    aeval (polynomialPoint t i φ ∘ X) (dehomogenizedEquations seed i r) = 0 := by
  rw [← aeval_unique, polynomialPoint_apply]
  simp only [polynomialMap, RingHom.comp_apply, dehomogenizedMap_equation, map_zero]

/-- It also satisfies each of the original fixed-section rows. -/
theorem row_aeval {K : Type*} [Field K] [Algebra ℂ K]
    (t : Fin 3 → ℂ) (i : Fin 4) (φ : AffineCurveChart seed t i →ₐ[ℂ] K) (a : Fin 3) :
    aeval (polynomialPoint t i φ ∘ X) (dehomogenize i (relativeSectionPolynomial seed t a)) = 0 := by
  rw [← aeval_unique, polynomialPoint_apply]
  change φ (Ideal.Quotient.mk (affineSectionIdeal seed t i) (affineSectionEquation seed t i a)) = 0
  have he : affineSectionEquation seed t i a ∈ affineSectionIdeal seed t i :=
    Ideal.subset_span (Set.mem_range_self a)
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr he, map_zero]

/-- An algebraically independent choice of the original coefficients has an
invertible three-row minor at every field point where the selected matrix
entry is nonzero. -/
theorem point_minor_of_independent {K : Type} [Field K] [Algebra ℂ K] [CharZero K]
    (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (i : Fin 4) (a b : Fin 3)
    (φ : AffineCurveChart seed t i →ₐ[ℂ] K)
    (hentry : φ (polynomialMap t i (SmoothSeedTransverse.entry i a b)) ≠ 0) :
    ∃ q : Fin 3 ↪ Option (Fin 3), φ (polynomialMap t i
      ((Matrix.of fun u r : Fin 3 => pderiv (q u) (chartRows t i a r)).det)) ≠ 0 := by
  let x := polynomialPoint t i φ ∘ X
  obtain ⟨v, surf, row⟩ := SmoothSeedTransverse.transverse_at t ht i a b x
    (surface_aeval t i φ) (row_aeval t i φ a)
  have hx (f : ChartPolynomial ℂ) : aeval x f = φ (polynomialMap t i f) :=
    (congrArg (fun g : ChartPolynomial ℂ →ₐ[ℂ] K => g f) (aeval_unique (polynomialPoint t i φ))).symm
  simp only [SmoothSeedTransverse.direction, hx] at surf row
  exact chart_minor_of_tangent t i a φ.toRingHom v (surf 0) (surf 1)
    (row.trans_ne (neg_ne_zero.mpr hentry))

open CycleQ2FirstOrderCurveChartFlat CycleQ2LiteralAbelJacobiSeedLiftPoints

attribute [local instance] CycleQ2RelativeCurveChartFiber.seedCurveChartCommRing

/-- Every seed chart prime for the same independent vector lies in an
active matrix pivot with a nonvanishing minor for that pivot's own row. -/
theorem prime_minor_of_independent (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t)
    (i : Fin 4) (z : PrimeSpectrum (AffineCurveChart seed t i)) :
    ∃ (p : CycleQ2SegreCech.Chart) (q : Fin 3 ↪ Option (Fin 3)),
      Ideal.Quotient.mk (affineSectionIdeal seed t i) (seedPivot i p) ∉ z.asIdeal ∧
      curvePolynomialMap t i seed (jacobianMinor (chartRows t i p.1) q) ∉ z.asIdeal := by
  obtain ⟨p,hp⟩ := exists_seedPivot_notMem t i z
  let : z.asIdeal.IsPrime := z.isPrime
  let L := Ideal.ResidueField (R := AffineCurveChart seed t i) z.asIdeal
  let : CharZero L := charZero_of_injective_algebraMap (algebraMap ℂ L).injective
  let φ : AffineCurveChart seed t i →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ _ _
  have hentry : φ (polynomialMap t i (SmoothSeedTransverse.entry i p.1 p.2)) ≠ 0 := by
    intro he
    apply hp
    rw [seedPivot, affineMatrixEntry_polynomial]
    exact Ideal.algebraMap_residueField_eq_zero.mp he
  obtain ⟨q,hq⟩ := point_minor_of_independent t ht i p.1 p.2 φ hentry
  refine ⟨p,q,hp,fun hm => hq ?_⟩
  exact Ideal.algebraMap_residueField_eq_zero.mpr hm

/-- A single nonzero member of the original three-dimensional linear system
satisfies the scheme-theoretic Jacobian criterion on every chart. -/
theorem exists_nonzero_minor_cover : ∃ t : Fin 3 → ℂ, t ≠ 0 ∧
    ∀ (i : Fin 4) (z : PrimeSpectrum (AffineCurveChart seed t i)),
      ∃ (p : CycleQ2SegreCech.Chart) (q : Fin 3 ↪ Option (Fin 3)),
        Ideal.Quotient.mk (affineSectionIdeal seed t i) (seedPivot i p) ∉ z.asIdeal ∧
        curvePolynomialMap t i seed (jacobianMinor (chartRows t i p.1) q) ∉ z.asIdeal := by
  obtain ⟨t,ht⟩ := SmoothSeedGenericCoordinates.exists_complex_three_independent
  refine ⟨t, ?_, prime_minor_of_independent t ht⟩
  intro hz
  have he : t 0 = t 1 := by simp only [hz, Pi.zero_apply]
  exact (by decide : (0 : Fin 3) ≠ 1) (ht.injective he)

end CycleQ2LiteralAbelJacobiBertiniMinor
end
#print axioms CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent
#print axioms CycleQ2LiteralAbelJacobiBertiniMinor.exists_nonzero_minor_cover
