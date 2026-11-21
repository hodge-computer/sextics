import Proposal.GeometricSurfaceCoordinates

/-! Source-preserving extraction of the actual seed Jacobian certificates. -/

set_option Elab.async false

/- Component: continuation_3/SeedCoordinateCover.lean -/
section
/-! # The three base-coordinate opens cover every relevant seed prime -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCoordinateCover

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree

variable {R : Type*} [CommRing R]

theorem seedPrime_contains_all_of_base (r ι : R) (P : Ideal (Poly R)) [P.IsPrime]
    (hh : smoothH ι ∈ P) (hF : smoothF r ι ∈ P)
    (h1 : X 1 ∈ P) (h2 : X 2 ∈ P) (h3 : X 3 ∈ P) :
    ∀ i : Fin 5, X i ∈ P := by
  have hz1 : Ideal.Quotient.mk P (X 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h1
  have hz2 : Ideal.Quotient.mk P (X 2) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h2
  have hz3 : Ideal.Quotient.mk P (X 3) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h3
  have hzh : Ideal.Quotient.mk P (smoothH ι) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hh
  have hzF : Ideal.Quotient.mk P (smoothF r ι) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hF
  have hz0pow : Ideal.Quotient.mk P (X 0) ^ 3 = 0 := by
    simpa [smoothH, smoothB, smoothA, hz1, hz2, hz3] using hzh
  have hz0 : Ideal.Quotient.mk P (X 0) = 0 := eq_zero_of_pow_eq_zero hz0pow
  have hzG : Ideal.Quotient.mk P (seedG r) = 0 := by
    simpa only [smoothF, map_add, map_mul, hzh, zero_mul, add_zero] using hzF
  have hzwpow : Ideal.Quotient.mk P (X 4) ^ 3 = 0 := by
    simpa [seedG, CycleQ2SegreSeed.seedG_expanded, hz0, hz1, hz2, hz3] using hzG
  have hzw : Ideal.Quotient.mk P (X 4) = 0 := eq_zero_of_pow_eq_zero hzwpow
  intro i
  fin_cases i
  · exact Ideal.Quotient.eq_zero_iff_mem.mp hz0
  · exact h1
  · exact h2
  · exact h3
  · exact Ideal.Quotient.eq_zero_iff_mem.mp hzw

theorem seedPrime_coordinate_cover (r ι : R) (P : Ideal (Poly R)) [P.IsPrime]
    (hh : smoothH ι ∈ P) (hF : smoothF r ι ∈ P)
    (hrelevant : ∃ i : Fin 5, X i ∉ P) :
    X 1 ∉ P ∨ X 2 ∉ P ∨ X 3 ∉ P := by
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := hrelevant
  exact hi (seedPrime_contains_all_of_base r ι P hh hF h.1 h.2.1 h.2.2 i)

/-- The same cover criterion in the existing actual seed quotient. -/
theorem seedQuotient_coordinate_cover (r ι : R) (P : Ideal (SeedRing r ι)) [P.IsPrime]
    (hrelevant : ∃ i : Fin 5,
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (X i) ∉ P) :
    ∃ i : Fin 3, algebraMap (Base R) (SeedRing r ι) (X i) ∉ P := by
  let f := Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
  let Q := P.comap f
  have hh : smoothH ι ∈ Q := by
    change f (smoothH ι) ∈ P
    have hz : f (smoothH ι) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (by simp [equationsIdeal]))
    rw [hz]
    exact P.zero_mem
  have hF : smoothF r ι ∈ Q := by
    change f (smoothF r ι) ∈ P
    have hz : f (smoothF r ι) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (by simp [equationsIdeal]))
    rw [hz]
    exact P.zero_mem
  rcases seedPrime_coordinate_cover r ι Q hh hF hrelevant with h1 | h2 | h3
  · refine ⟨0, ?_⟩
    change f (X 1) ∉ P at h1
    change f (remainingInclusion R (X 0)) ∉ P
    simpa [remainingInclusion, remainingIndex] using h1
  · refine ⟨1, ?_⟩
    change f (X 2) ∉ P at h2
    change f (remainingInclusion R (X 1)) ∉ P
    simpa [remainingInclusion, remainingIndex] using h2
  · refine ⟨2, ?_⟩
    change f (X 3) ∉ P at h3
    change f (remainingInclusion R (X 2)) ∉ P
    simpa [remainingInclusion, remainingIndex] using h3

end CycleQ2SeedCoordinateCover

#print axioms CycleQ2SeedCoordinateCover.seedQuotient_coordinate_cover
end
end


/- End of source-preserving extraction. -/
