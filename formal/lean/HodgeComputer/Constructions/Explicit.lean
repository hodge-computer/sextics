import HodgeComputer.Verify

/-!
Assembly of explicit polynomial witnesses. The early catalogue solves supply
normalized directional and divergence identities, homogeneous degree checks,
and a univariate specialization proving denominator legality. These lemmas
collect their common assembly without imposing a zero quotient or a degree bound.
-/
noncomputable section
namespace HodgeComputer
open MvPolynomial HodgeTestbed

/-- Build a certificate from normalized identities and natural-degree witnesses.
The balance equality is in the integers; a negative required degree cannot be
silently replaced by zero. For negative numerator degrees use `Verify` directly. -/
theorem Verify.of_normalized {n d q δ ν : ℕ} {F A D Q : AmbientPoly n}
    {N : Fin (n + 1) → AmbientPoly n}
    (hF : F ≠ 0) (hFd : F.IsHomogeneous d)
    (hA : Homogeneous A ((d : ℤ) * (q + 1) - (n + 1)))
    (hD : D ≠ 0) (hDδ : D.IsHomogeneous δ)
    (hN : ∀ i, (N i).IsHomogeneous ν)
    (hν : (ν : ℤ) = δ + (d : ℤ) * q - n)
    (hlegal : IsRelPrime F D)
    (h1 : (q : AmbientPoly n) * directional F N = A * D)
    (h2 : divergenceNumerator D N = F^q * Q) : Verify F A d q D N Q where
  hypersurface_ne_zero := hF
  hypersurface_homogeneous := hFd
  source_homogeneous := hA
  denominator_ne_zero := hD
  denominator_homogeneous := by rw [hDδ.totalDegree hD]; exact hDδ
  numerator_homogeneous := by
    intro i
    rw [hDδ.totalDegree hD, ← hν]
    exact Homogeneous.of_isHomogeneous (hN i)
  denominator_legal := hlegal
  identity := normalized_identity h1 h2

/-- A legal denominator can be certified in a univariate chart and then on one
fiber. The hypersurface must have unit leading coefficient before specialization;
no such restriction is imposed on the denominator. -/
theorem relPrime_of_chart_specialization {R S T : Type*}
    [CommRing R] [CommRing S] [IsDomain S] [CommRing T] [IsDomain T]
    (chart : R →+* Polynomial S) (back : Polynomial S →+* R)
    (retract : back.comp chart = RingHom.id R) (fiber : S →+* T)
    {F D : R} (hmonic : IsUnit (chart F).leadingCoeff)
    (hcoprime : IsCoprime ((chart F).map fiber) ((chart D).map fiber)) :
    IsRelPrime F D :=
  relPrime_of_retract chart back retract
    (relPrime_of_specialization fiber (chart F) (chart D) hmonic hcoprime.isRelPrime)

end HodgeComputer
