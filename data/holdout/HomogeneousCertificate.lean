import HodgeComputer.Verify
import Proposal.HomogeneousField
import Proposal.HypersurfaceCoordinates

/- Source component: HomogeneousNormalization -/
section
/-!
Changing a denominator modulo the hypersurface, then extracting homogeneous
data. Every identity below is finite polynomial arithmetic. These lemmas
accept a normalized rational certificate with arbitrary legal denominator;
they are not a certificate for any particular sextic by themselves.
-/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial
open scoped BigOperators

variable {R σ : Type*} [CommRing R] [Fintype σ]

theorem polynomialDirectional_add (p : MvPolynomial σ R)
    (N M : σ → MvPolynomial σ R) :
    polynomialDirectional p (fun i => N i + M i) =
      polynomialDirectional p N + polynomialDirectional p M := by
  simp only [polynomialDirectional, add_mul, Finset.sum_add_distrib]

theorem polynomialDirectional_add_source (p q : MvPolynomial σ R)
    (N : σ → MvPolynomial σ R) :
    polynomialDirectional (p+q) N =
      polynomialDirectional p N + polynomialDirectional q N := by
  simp only [polynomialDirectional, map_add, mul_add, Finset.sum_add_distrib]

theorem polynomialDivergence_add (N M : σ → MvPolynomial σ R) :
    polynomialDivergence (fun i => N i + M i) =
      polynomialDivergence N + polynomialDivergence M := by
  simp only [polynomialDivergence, map_add, Finset.sum_add_distrib]

theorem polynomialDirectional_single [DecidableEq σ]
    (p a : MvPolynomial σ R) (i : σ) :
    polynomialDirectional p (Pi.single i a) = a*pderiv i p := by
  simp [polynomialDirectional, Pi.single_apply]

theorem polynomialDivergence_single [DecidableEq σ]
    (a : MvPolynomial σ R) (i : σ) :
    polynomialDivergence (Pi.single i a) = pderiv i a := by
  simp [polynomialDivergence, Pi.single_apply, apply_ite]

/-- Moving a denominator by a multiple of `F` can be compensated by one
normal component, after multiplying every component by `∂ᵢF`. -/
theorem denominator_congruence_normal [DecidableEq σ]
    (F A D U : MvPolynomial σ R) (N : σ → MvPolynomial σ R) (i : σ)
    (normal : polynomialDirectional F N = A*D) :
    polynomialDirectional F
      (fun j => pderiv i F*N j + (Pi.single i (A*F*U) : σ → MvPolynomial σ R) j) =
      A*(pderiv i F*(D+F*U)) := by
  rw [polynomialDirectional_add, polynomialDirectional_scale,
    polynomialDirectional_single, normal]
  ring

/-- The correction of the divergence numerator is visibly divisible by
`F`. The original divergence quotient is allowed to be nonzero. -/
theorem denominator_congruence_divergence [DecidableEq σ]
    (F A D U : MvPolynomial σ R) (N : σ → MvPolynomial σ R) (i : σ)
    (normal : polynomialDirectional F N = A*D) :
    polynomialDivNum (pderiv i F*(D+F*U))
      (fun j => pderiv i F*N j + (Pi.single i (A*F*U) : σ → MvPolynomial σ R) j) =
      (pderiv i F)^2*polynomialDivNum D N + F*
        ((pderiv i F)^2*(U*polynomialDivergence N-polynomialDirectional U N) +
          pderiv i F*(D+F*U)*pderiv i A*U +
          pderiv i F*D*A*pderiv i U -
          A*U*(D+F*U)*pderiv i (pderiv i F) -
          A*U*pderiv i F*pderiv i D) := by
  simp only [polynomialDivNum, polynomialDivergence_add, polynomialDivergence_scale,
    polynomialDivergence_single, polynomialDirectional_add, polynomialDirectional_scale,
    polynomialDirectional_single, polynomialDirectional_mul,
    polynomialDirectional_add_source, pderiv_mul, map_add, normal]
  ring

/-- An arbitrary legal normalized denominator can be replaced by one whose
initial component is legal, with positive degree. This step does not use
residue fields, formal series, or a choice of representatives in a field. -/
theorem normalized_data_with_legal_initial [IsDomain R]
    (F A D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) (Q : MvPolynomial σ R)
    (hF : F.IsHomogeneous 6) (hprime : Prime F) (hlegal : ¬ F ∣ D)
    (normal : polynomialDirectional F N = A*D)
    (divergence : polynomialDivNum D N = F*Q)
    (i : σ) (hchart : ¬ F ∣ pderiv i F) :
    ∃ d : ℕ, ∃ D' : MvPolynomial σ R, ∃ N' : σ → MvPolynomial σ R,
      ∃ Q' : MvPolynomial σ R,
        0 < d ∧ HasOrder d D' ∧ ¬ F ∣ homogeneousComponent d D' ∧
        polynomialDirectional F N' = A*D' ∧ polynomialDivNum D' N' = F*Q' := by
  classical
  obtain ⟨d, q, hdifference, horder, hqlegal⟩ :=
    exists_legal_initial_representative F D hlegal
  have hdifference' : F ∣ q-D := by
    simpa only [neg_sub] using (dvd_neg.mpr hdifference)
  obtain ⟨U, hU⟩ := hdifference'
  have hq : q = D+F*U := by linear_combination hU
  let g := pderiv i F
  let D' := g*q
  let N' : σ → MvPolynomial σ R :=
    fun j => g*N j+(Pi.single i (A*F*U) : σ → MvPolynomial σ R) j
  let V := g^2*(U*polynomialDivergence N-polynomialDirectional U N) +
    g*(D+F*U)*pderiv i A*U+g*D*A*pderiv i U-
      A*U*(D+F*U)*pderiv i g-A*U*g*pderiv i D
  have hg : g.IsHomogeneous 5 := pderiv_isHomogeneous hF i
  have hinitial := legal_initial_mul_homogeneous hprime hg hchart horder hqlegal
  refine ⟨5+d, D', N', g^2*Q+V, by omega, hinitial.1, hinitial.2, ?_, ?_⟩
  · dsimp [D', N', g]
    rw [hq]
    exact denominator_congruence_normal F A D U N i normal
  · dsimp [D', N', g, V]
    rw [hq, denominator_congruence_divergence F A D U N i normal, divergence]
    ring

/-- Finite homogeneous extraction for every normalized pole-order-one
certificate on a homogeneous sextic, once a nonzero normal chart is given.
No bound on the initial denominator degree is assumed. -/
theorem homogeneous_data_of_normalized [IsDomain R]
    (F A D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) (Q : MvPolynomial σ R)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (hlegal : ¬ F ∣ D)
    (normal : polynomialDirectional F N = A*D)
    (divergence : polynomialDivNum D N = F*Q)
    (i : σ) (hchart : ¬ F ∣ pderiv i F) :
    ∃ d : ℕ, ∃ H : MvPolynomial σ R, ∃ M : σ → MvPolynomial σ R,
      ∃ Q' : MvPolynomial σ R,
        H ≠ 0 ∧ H.IsHomogeneous d ∧ (∀ j, (M j).IsHomogeneous (d+1)) ∧
        IsRelPrime F H ∧ polynomialDirectional F M = A*H ∧
        polynomialDivNum H M = F*Q' := by
  obtain ⟨d, D', N', Q', hd, horder, hlegal', hnormal, hdiv⟩ :=
    normalized_data_with_legal_initial F A D N Q hF hprime hlegal normal divergence i hchart
  obtain ⟨H, M, Q'', hH, hhom, hM, hcoprime, hnormal', hdiv'⟩ :=
    homogeneous_data_from_initial_denominator F A D' N' Q' hF hA hprime hnormal hdiv
      d hd horder hlegal' (d+2) (by omega)
  exact ⟨(d+2)*d, H, M, Q'', hH, hhom, hM, hcoprime, hnormal', hdiv'⟩

end HoldoutConstruction

#print axioms HoldoutConstruction.denominator_congruence_divergence
#print axioms HoldoutConstruction.homogeneous_data_of_normalized
end
end

/- Source component: HodgeHomogeneousBridge -/
section
/-!
The final homogeneous-data interface to the unchanged HodgeComputer verifier.
The exact holdout corollary is conditional on normalized polynomial data;
this file alone does not supply that data or solve the instance.
-/

noncomputable section

namespace HoldoutConstruction

open MvPolynomial

theorem polynomialDirectional_eq_directional
    {R σ : Type*} [CommRing R] [Fintype σ]
    (p : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    polynomialDirectional p N = HodgeTestbed.directional p N := by
  simp only [polynomialDirectional, HodgeTestbed.directional, mul_comm]

theorem polynomialDivNum_eq_divergenceNumerator
    {R σ : Type*} [CommRing R] [Fintype σ]
    (D : MvPolynomial σ R) (N : σ → MvPolynomial σ R) :
    polynomialDivNum D N = HodgeTestbed.divergenceNumerator D N := by
  simp only [polynomialDivNum, HodgeTestbed.divergenceNumerator,
    polynomialDivergence, HodgeTestbed.divergence, polynomialDirectional_eq_directional]

/-- Homogeneity imposes no extra obstruction once legal normalized
pole-order-one polynomial data have been obtained on this normal chart. -/
theorem hasCertificate_of_normalized
    (F A D : HodgeComputer.Poly) (N : Fin 6 → HodgeComputer.Poly)
    (Q : HodgeComputer.Poly)
    (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 6) (hprime : Prime F)
    (hlegal : IsRelPrime F D)
    (normal : HodgeTestbed.directional F N = A*D)
    (divergence : HodgeTestbed.divergenceNumerator D N = F*Q)
    (i : Fin 6) (hchart : ¬ F ∣ pderiv i F) :
    HodgeComputer.HasCertificate F A 1 := by
  have hnormal : polynomialDirectional F N = A*D := by
    exact (polynomialDirectional_eq_directional F N).trans normal
  have hdivergence : polynomialDivNum D N = F*Q := by
    exact (polynomialDivNum_eq_divergenceNumerator D N).trans divergence
  obtain ⟨d, H, M, Q', hH0, hH, hM, hcoprime, hnormal', hdiv'⟩ :=
    homogeneous_data_of_normalized F A D N Q hF hA hprime
      (hprime.irreducible.isRelPrime_iff_not_dvd.mp hlegal)
      hnormal hdivergence i hchart
  refine ⟨d, H, M, Q', ⟨hH0, hH, ?_, hcoprime, ?_⟩⟩
  · intro j
    simpa only [show d+6*1-5 = d+1 by omega] using hM j
  · apply HodgeComputer.normalized_identity
    · simpa only [Nat.cast_one, one_mul, polynomialDirectional_eq_directional] using hnormal'
    · simpa only [pow_one, polynomialDivNum_eq_divergenceNumerator] using hdiv'

/-- The protected holdout numerator in the original coordinate order. -/
def holdoutSource : HodgeComputer.Poly := MvPolynomial.X 0^3*MvPolynomial.X 3^3

theorem holdoutSextic_isHomogeneous :
    (holdoutSextic (R := ℂ)).IsHomogeneous 6 := by
  have hp (i : Fin 6) : (MvPolynomial.X (R := ℂ) i^6).IsHomogeneous 6 :=
    isHomogeneous_X_pow i 6
  have hc (i j k l : Fin 6) :
      (MvPolynomial.X (R := ℂ) i^3*MvPolynomial.X j*MvPolynomial.X k*MvPolynomial.X l).IsHomogeneous 6 :=
    (((isHomogeneous_X_pow i 3).mul (isHomogeneous_X ℂ j)).mul
      (isHomogeneous_X ℂ k)).mul (isHomogeneous_X ℂ l)
  exact (((((((hp 0).add (hc 0 1 3 4)).add (hp 1)).add
    (hc 1 2 4 5)).add (hp 2)).add (hp 3)).add (hp 4)).add (hp 5)

theorem holdoutSource_isHomogeneous : holdoutSource.IsHomogeneous 6 :=
  (isHomogeneous_X_pow (0 : Fin 6) 3).mul (isHomogeneous_X_pow (3 : Fin 6) 3)

/-- A closed normal-chart and homogeneity wrapper for the exact fixed
holdout sextic and numerator. The outstanding constructive input is precisely
the two normalized polynomial identities and denominator legality. -/
theorem holdout_hasCertificate_of_normalized
    (D : HodgeComputer.Poly) (N : Fin 6 → HodgeComputer.Poly) (Q : HodgeComputer.Poly)
    (hlegal : IsRelPrime (holdoutSextic (R := ℂ)) D)
    (normal : HodgeTestbed.directional holdoutSextic N = holdoutSource*D)
    (divergence : HodgeTestbed.divergenceNumerator D N = holdoutSextic*Q) :
    HodgeComputer.HasCertificate holdoutSextic holdoutSource 1 := by
  have hi : (Complex.I : ℂ)^6 = -1 := by
    rw [show (6 : ℕ) = 2*3 by decide, pow_mul, Complex.I_sq]
    norm_num
  exact hasCertificate_of_normalized holdoutSextic holdoutSource D N Q
    holdoutSextic_isHomogeneous holdoutSource_isHomogeneous
    (holdoutSextic_irreducible Complex.I hi).prime hlegal normal divergence 0
    holdoutSextic_not_dvd_pderiv_zero

end HoldoutConstruction

#print axioms HoldoutConstruction.hasCertificate_of_normalized
#print axioms HoldoutConstruction.holdout_hasCertificate_of_normalized
end
end
