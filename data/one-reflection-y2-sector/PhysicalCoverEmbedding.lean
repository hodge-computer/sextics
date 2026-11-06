import HodgeComputer.Constructions.HoldoutCover.CommonCoverDomain
import HodgeComputer.Constructions.HoldoutCover.FermatFields
import Proposal.HypersurfaceCoordinates

/- Source component: PhysicalCoverEmbedding -/
section
/-!
The exact physical holdout coordinate domain embeds in the Fermat common
cover. The coefficient injection is proved by dense evaluations, and
monicity then gives the hypersurface injection. Prepared with OpenAI
ChatGPT assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

section CoefficientRing

variable {K : Type*} [CommRing K]

abbrev FermatCommonCoverRing (K : Type*) [CommRing K] :=
  AdjoinRoot (commonCoverPolynomial
    (baseAlpha (R := K)) (baseAlpha (R := K)))

/-- The exact holdout equation maps to the common-cover equation using
the defining Fermat relation, with every original coupling unchanged. -/
theorem holdoutPolynomial_commonCover :
    (holdoutPolynomial (R := K)).map physicalCoverCoefficientMap =
      commonCoverPolynomial (baseAlpha (R := K)) (baseAlpha (R := K)) := by
  have hY :
      (MvPolynomial.C (baseAlpha (R := K)) *
        (MvPolynomial.X 3 : MvPolynomial (Fin 4) (FermatBaseRing K)))^6 +
      (MvPolynomial.C (baseBeta (R := K)) * MvPolynomial.X 3)^6 =
        (MvPolynomial.X 3)^6 := by
    rw [mul_pow, mul_pow, ← add_mul, ← map_pow, ← map_pow, ← map_add,
      fermat_base_relation, map_one, one_mul]
  have hC := congrArg
    (Polynomial.C : MvPolynomial (Fin 4) (FermatBaseRing K) →
      Polynomial (MvPolynomial (Fin 4) (FermatBaseRing K))) hY
  simp only [map_add, map_pow, map_mul] at hC
  simp [holdoutPolynomial, commonCoverPolynomial, physicalCoverCoefficientMap]
  linear_combination hC

/-- Coordinate-domain map whose source is the exact monic presentation of
the protected holdout polynomial. -/
def physicalCommonCoverMap :
    AdjoinRoot (holdoutPolynomial (R := K)) →+* FermatCommonCoverRing K :=
  AdjoinRoot.map physicalCoverCoefficientMap
    (holdoutPolynomial (R := K))
    (commonCoverPolynomial (baseAlpha (R := K)) (baseAlpha (R := K)))
    (by rw [holdoutPolynomial_commonCover])

private theorem adjoinRoot_map_injective_of_eq
    {C D : Type*} [CommRing C] [CommRing D]
    (φ : C →+* D) (hφ : Function.Injective φ)
    (f : Polynomial C) (hf : f.Monic) (g : Polynomial D)
    (hfg : f.map φ = g) (hdiv : g ∣ f.map φ) :
    Function.Injective (AdjoinRoot.map φ f g hdiv) := by
  subst g
  exact adjoinRoot_map_injective φ hφ f hf

end CoefficientRing

section PhysicalInjectivity

variable {K : Type*} [Field K] [Infinite K] [IsAlgClosed K]

theorem physicalCommonCoverMap_injective :
    Function.Injective (physicalCommonCoverMap (K := K)) := by
  exact adjoinRoot_map_injective_of_eq physicalCoverCoefficientMap
    physicalCoverCoefficientMap_injective _ holdoutPolynomial_monic
    _ holdoutPolynomial_commonCover _

end PhysicalInjectivity

section Domain

variable {K : Type*} [CommRing K] [IsDomain K] [CharZero K]

/-- Domainhood of the common cover over the entire Fermat base. -/
theorem fermatCommonCover_isDomain
    (eta : K) (heta : eta^6 = -1) : IsDomain (FermatCommonCoverRing K) := by
  let : IsDomain (FermatBaseRing K) := fermatCurve_adjoinRoot_isDomain
  let : CharZero (FermatBaseRing K) := fermat_base_charZero
  apply commonCover_adjoinRoot_isDomain
    (baseAlpha (R := K)) (baseAlpha (R := K))
    (algebraMap K (FermatBaseRing K) eta)
  rw [← map_pow, heta, map_neg, map_one]

end Domain

end HoldoutConstruction

#print axioms HoldoutConstruction.holdoutPolynomial_commonCover
#print axioms HoldoutConstruction.physicalCommonCoverMap_injective
#print axioms HoldoutConstruction.fermatCommonCover_isDomain
end
end
