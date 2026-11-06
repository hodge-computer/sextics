import Proposal.PhysicalCoverEmbedding
import HodgeComputer.Constructions.HoldoutCover.QuotientCoverEmbedding

/- Source component: CommonCoverBaseChange -/
section
/-!
Injective base change of the common cover from the Fermat coordinate ring
to its fraction field. This lets the conic construction and cover transfer
use exactly the same coefficient field. Prepared with OpenAI ChatGPT
assistance for a contribution through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

section BaseChange

variable {R S : Type*} [CommRing R] [CommRing S]

def commonCoverBaseChange (φ : R →+* S) (a b : R) :
    AdjoinRoot (commonCoverPolynomial a b) →+*
      AdjoinRoot (commonCoverPolynomial (φ a) (φ b)) :=
  AdjoinRoot.map (MvPolynomial.map φ) (commonCoverPolynomial a b)
    (commonCoverPolynomial (φ a) (φ b))
    (by rw [commonCoverPolynomial_map])

private theorem map_injective_of_mapped_equation
    {C D : Type*} [CommRing C] [CommRing D]
    (φ : C →+* D) (hφ : Function.Injective φ)
    (f : Polynomial C) (hf : f.Monic) (g : Polynomial D)
    (hfg : f.map φ = g) (hdiv : g ∣ f.map φ) :
    Function.Injective (AdjoinRoot.map φ f g hdiv) := by
  subst g
  exact adjoinRoot_map_injective φ hφ f hf

theorem commonCoverBaseChange_injective (φ : R →+* S)
    (hφ : Function.Injective φ) (a b : R) :
    Function.Injective (commonCoverBaseChange φ a b) := by
  exact map_injective_of_mapped_equation (MvPolynomial.map φ)
    (MvPolynomial.map_injective φ hφ) _ (commonCoverPolynomial_monic a b)
    _ (commonCoverPolynomial_map φ a b) _

@[simp] theorem commonCoverBaseChange_root (φ : R →+* S) (a b : R) :
    commonCoverBaseChange φ a b (AdjoinRoot.root (commonCoverPolynomial a b)) =
      AdjoinRoot.root (commonCoverPolynomial (φ a) (φ b)) := by
  simp [commonCoverBaseChange]

@[simp] theorem commonCoverBaseChange_parameter
    (φ : R →+* S) (a b : R) (i : Fin 4) :
    commonCoverBaseChange φ a b (AdjoinRoot.of _ (MvPolynomial.X i)) =
      AdjoinRoot.of _ (MvPolynomial.X i) := by
  simp [commonCoverBaseChange]

@[simp] theorem commonCoverBaseChange_coefficient
    (φ : R →+* S) (a b r : R) :
    commonCoverBaseChange φ a b
      (algebraMap R (AdjoinRoot (commonCoverPolynomial a b)) r) =
      algebraMap S (AdjoinRoot (commonCoverPolynomial (φ a) (φ b))) (φ r) := by
  change commonCoverBaseChange φ a b (AdjoinRoot.of _ (MvPolynomial.C r)) =
    AdjoinRoot.of _ (MvPolynomial.C (φ r))
  simp [commonCoverBaseChange]

end BaseChange

section GenericBase

variable (K : Type*) [CommRing K]

abbrev FermatCoefficientField := FractionRing (FermatBaseRing K)

def genericBaseAlpha : FermatCoefficientField K :=
  algebraMap (FermatBaseRing K) (FermatCoefficientField K) baseAlpha

def genericBaseBeta : FermatCoefficientField K :=
  algebraMap (FermatBaseRing K) (FermatCoefficientField K) baseBeta

abbrev GenericCommonCoverRing :=
  AdjoinRoot (commonCoverPolynomial (genericBaseAlpha K) (genericBaseAlpha K))

def physicalGenericCoverMap :
    AdjoinRoot (holdoutPolynomial (R := K)) →+* GenericCommonCoverRing K :=
  (commonCoverBaseChange (algebraMap (FermatBaseRing K) (FermatCoefficientField K))
    baseAlpha baseAlpha).comp physicalCommonCoverMap

@[simp] theorem physicalGenericCoverMap_root :
    physicalGenericCoverMap K (AdjoinRoot.root (holdoutPolynomial (R := K))) =
      AdjoinRoot.root
        (commonCoverPolynomial (genericBaseAlpha K) (genericBaseAlpha K)) := by
  change commonCoverBaseChange
    (algebraMap (FermatBaseRing K) (FermatCoefficientField K)) baseAlpha baseAlpha
    (physicalCommonCoverMap (AdjoinRoot.root (holdoutPolynomial (R := K)))) = _
  rw [physicalCommonCoverMap, AdjoinRoot.map_root, commonCoverBaseChange_root]
  rfl

@[simp] theorem physicalGenericCoverMap_coefficient (r : K) :
    physicalGenericCoverMap K
      (algebraMap K (AdjoinRoot (holdoutPolynomial (R := K))) r) =
      algebraMap K (GenericCommonCoverRing K) r := by
  change commonCoverBaseChange
    (algebraMap (FermatBaseRing K) (FermatCoefficientField K)) baseAlpha baseAlpha
    (physicalCommonCoverMap (AdjoinRoot.of _ (MvPolynomial.C r))) = _
  rw [physicalCommonCoverMap, AdjoinRoot.map_of]
  simp only [physicalCoverCoefficientMap, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  change commonCoverBaseChange
    (algebraMap (FermatBaseRing K) (FermatCoefficientField K)) baseAlpha baseAlpha
    (algebraMap (FermatBaseRing K) (FermatCommonCoverRing K)
      (algebraMap K (FermatBaseRing K) r)) = _
  rw [commonCoverBaseChange_coefficient]
  exact (IsScalarTower.algebraMap_apply K (FermatBaseRing K)
    (GenericCommonCoverRing K) r).symm

end GenericBase

section GenericInjectivity

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

theorem physicalGenericCoverMap_injective :
    Function.Injective (physicalGenericCoverMap K) := by
  let : IsDomain (FermatBaseRing K) := fermatCurve_adjoinRoot_isDomain
  exact (commonCoverBaseChange_injective
    (algebraMap (FermatBaseRing K) (FermatCoefficientField K))
    (IsFractionRing.injective _ _) baseAlpha baseAlpha).comp
      physicalCommonCoverMap_injective

end GenericInjectivity

end HoldoutConstruction

#print axioms HoldoutConstruction.commonCoverBaseChange_injective
#print axioms HoldoutConstruction.physicalGenericCoverMap_injective
end
end
