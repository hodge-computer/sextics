import WeightedPolynomialOrbitEnumeration
import WeightedPolynomialSymmetry

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace WeightedSupport.PolynomialModel

theorem table_complete (codes : Array ℕ) (n degree : ℕ) (minus : Bool)
    (hsize : codes.size = n) (htable : codes.toList = orbitCodes degree minus)
    (e : Exponent) (he : IsCapped e) (hd : weightedDegree e = degree)
    (hc : Canonical minus e) : ∃ i : Fin n, decodeExponent codes[i.val]! = e := by
  have hm : encodeExponent e ∈ codes.toList := by
    rw [htable]
    exact orbitCodes_complete degree minus e he hd hc
  obtain ⟨i, hi, hv⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hm)
  refine ⟨⟨i, by simpa only [hsize] using hi⟩, ?_⟩
  change decodeExponent codes[i]! = e
  rw [getElem!_pos codes i hi, hv]
  exact decode_encode e he

theorem source_orbit_complete (e : Exponent) (he : IsCapped e)
    (hd : weightedDegree e = 5) (hc : Canonical false e) :
    ∃ i : Fin 82, sourceExponent i = e :=
  table_complete sourceCodes 82 5 false (by decide) source_orbit_enumeration e he hd hc

theorem q_target_orbit_complete (e : Exponent) (he : IsCapped e)
    (hd : weightedDegree e = 16) (hc : Canonical true e) :
    ∃ i : Fin 120, qTargetExponent i = e :=
  table_complete qTargetCodes 120 16 true (by decide) q_target_orbit_enumeration e he hd hc

theorem hq_target_orbit_complete (e : Exponent) (he : IsCapped e)
    (hd : weightedDegree e = 17) (hc : Canonical true e) :
    ∃ i : Fin 74, hqTargetExponent i = e :=
  table_complete hqTargetCodes 74 17 true (by decide) hq_target_orbit_enumeration e he hd hc

theorem sigma_preserves_capped (e : Exponent) (he : IsCapped e) : IsCapped (sigma e) := by
  intro i
  fin_cases i
  · simpa [sigma, swapIndex] using he 1
  · simpa [sigma, swapIndex] using he 0
  · simpa [sigma, swapIndex] using he 3
  · simpa [sigma, swapIndex] using he 2
  · simpa [sigma, swapIndex] using he 4
  · simpa [sigma, swapIndex] using he 5

theorem sigma_preserves_degree (e : Exponent) : weightedDegree (sigma e) = weightedDegree e := by
  change e 1 + e 0 + e 3 + e 2 + e 4 + 2 * e 5 = e 0 + e 1 + e 2 + e 3 + e 4 + 2 * e 5
  omega

theorem sigma_fixed_iff (e : Exponent) : e = sigma e ↔ e 0 = e 1 ∧ e 2 = e 3 := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h2 := congrFun h 2
    exact ⟨h0, h2⟩
  · rintro ⟨h0, h2⟩
    funext i
    fin_cases i
    · exact h0
    · exact h0.symm
    · exact h2
    · exact h2.symm
    · rfl
    · rfl

theorem canonical_plus_or_sigma (e : Exponent) :
    Canonical false e ∨ Canonical false (sigma e) := by
  change (e 0 < e 1 ∨ e 0 = e 1 ∧ e 2 ≤ e 3) ∨
    (e 1 < e 0 ∨ e 1 = e 0 ∧ e 3 ≤ e 2)
  omega

theorem canonical_minus_or_sigma (e : Exponent) (he : e ≠ sigma e) :
    Canonical true e ∨ Canonical true (sigma e) := by
  have hn : ¬ (e 0 = e 1 ∧ e 2 = e 3) := fun h => he ((sigma_fixed_iff e).mpr h)
  change (e 0 < e 1 ∨ e 0 = e 1 ∧ e 2 < e 3) ∨
    (e 1 < e 0 ∨ e 1 = e 0 ∧ e 3 < e 2)
  omega

theorem source_orbit_cover (e : Exponent) (he : IsCapped e) (hd : weightedDegree e = 5) :
    ∃ i : Fin 82, sourceExponent i = e ∨ sourceExponent i = sigma e := by
  rcases canonical_plus_or_sigma e with hc | hc
  · obtain ⟨i, hi⟩ := source_orbit_complete e he hd hc
    exact ⟨i, Or.inl hi⟩
  · obtain ⟨i, hi⟩ := source_orbit_complete (sigma e) (sigma_preserves_capped e he)
      ((sigma_preserves_degree e).trans hd) hc
    exact ⟨i, Or.inr hi⟩

theorem q_target_orbit_cover (e : Exponent) (he : IsCapped e) (hd : weightedDegree e = 16)
    (hne : e ≠ sigma e) : ∃ i : Fin 120, qTargetExponent i = e ∨ qTargetExponent i = sigma e := by
  rcases canonical_minus_or_sigma e hne with hc | hc
  · obtain ⟨i, hi⟩ := q_target_orbit_complete e he hd hc
    exact ⟨i, Or.inl hi⟩
  · obtain ⟨i, hi⟩ := q_target_orbit_complete (sigma e) (sigma_preserves_capped e he)
      ((sigma_preserves_degree e).trans hd) hc
    exact ⟨i, Or.inr hi⟩

theorem hq_target_orbit_cover (e : Exponent) (he : IsCapped e) (hd : weightedDegree e = 17)
    (hne : e ≠ sigma e) : ∃ i : Fin 74, hqTargetExponent i = e ∨ hqTargetExponent i = sigma e := by
  rcases canonical_minus_or_sigma e hne with hc | hc
  · obtain ⟨i, hi⟩ := hq_target_orbit_complete e he hd hc
    exact ⟨i, Or.inl hi⟩
  · obtain ⟨i, hi⟩ := hq_target_orbit_complete (sigma e) (sigma_preserves_capped e he)
      ((sigma_preserves_degree e).trans hd) hc
    exact ⟨i, Or.inr hi⟩

#print axioms source_orbit_cover
#print axioms q_target_orbit_cover
#print axioms hq_target_orbit_cover

end WeightedSupport.PolynomialModel
