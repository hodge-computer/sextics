import Proposal.DeformedQuotient
import HodgeComputer.Constructions.HoldoutCover.QuotientCoverEmbedding
import HodgeComputer.Constructions.HoldoutCover.PhysicalCoverEmbedding

/-!
Integral models for the physical sextic and its common Fermat cover.
The ternary deformation survives all generic maps and vanishes only in
the explicit Eisenstein specialization used to prove irreducibility.
Uses fqlx's shared specialization and coefficient-injectivity theorems.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedGeometry
open Polynomial HoldoutConstruction
variable {R : Type*} [CommRing R]

def ternaryCorrection {n : ℕ} (d : R) (x1 x2 : MvPolynomial (Fin n) R) :
    Polynomial (MvPolynomial (Fin n) R) :=
  C (MvPolynomial.C d*x1)*X^5+C (MvPolynomial.C d*x2^5)*X+
    C (2*MvPolynomial.C d*x1^5*x2)
def physicalPolynomial (d : R) : Polynomial (MvPolynomial (Fin 5) R) :=
  HoldoutConstruction.holdoutPolynomial+ternaryCorrection d (MvPolynomial.X 0) (MvPolynomial.X 1)
def coverPolynomial (d a b : R) : Polynomial (MvPolynomial (Fin 4) R) :=
  HoldoutConstruction.commonCoverPolynomial a b+
    ternaryCorrection d (MvPolynomial.X 0) (MvPolynomial.X 1)

lemma physicalPolynomial_monic (d : R) : (physicalPolynomial d).Monic := by
  unfold physicalPolynomial HoldoutConstruction.holdoutPolynomial ternaryCorrection
  rw [add_assoc]
  apply monic_X_pow_add
  compute_degree <;> norm_num
lemma coverPolynomial_monic (d a b : R) : (coverPolynomial d a b).Monic := by
  unfold coverPolynomial HoldoutConstruction.commonCoverPolynomial ternaryCorrection
  rw [add_assoc]
  apply monic_X_pow_add
  compute_degree <;> norm_num

lemma physicalPolynomial_specialization (d η : R) (hη : η^6 = -1) :
    (physicalPolynomial d).map (holdoutSpecialization η)=X^6+C ((X+1)^6-1) := by
  rw [physicalPolynomial,Polynomial.map_add,holdoutPolynomial_specialization η hη]
  simp [ternaryCorrection,holdoutSpecialization,map_ofNat]
lemma physicalPolynomial_irreducible [IsDomain R] [CharZero R] (d η : R) (hη : η^6 = -1) :
    Irreducible (physicalPolynomial d) := by
  apply (physicalPolynomial_monic d).irreducible_of_irreducible_map (holdoutSpecialization η)
  rw [physicalPolynomial_specialization d η hη]
  exact irreducible_power_add_constant ((X+1)^6-1 : R[X])
    (by simp [coeff_X_add_one_pow]) (by norm_num [coeff_X_add_one_pow,coeff_one]) 6 (by decide)
lemma coverPolynomial_specialization (d a b η : R) :
    (coverPolynomial d a b).map (commonCoverSpecialization η)=X^6+C ((X+C η)^6+1) := by
  rw [coverPolynomial,Polynomial.map_add,commonCoverPolynomial_specialization]
  simp [ternaryCorrection,commonCoverSpecialization,map_ofNat]
lemma coverPolynomial_irreducible [IsDomain R] [CharZero R] (d a b η : R) (hη : η^6 = -1) :
    Irreducible (coverPolynomial d a b) := by
  have hη0 : η ≠ 0 := by rintro rfl; norm_num at hη
  apply (coverPolynomial_monic d a b).irreducible_of_irreducible_map (commonCoverSpecialization η)
  rw [coverPolynomial_specialization]
  apply irreducible_power_add_constant ((X+C η)^6+1 : R[X])
  · simp [coeff_X_add_C_pow,hη]
  · have hc : ((X+C η)^6+1 : R[X]).coeff 1=6*η^5 := by
      simp [coeff_X_add_C_pow,coeff_one,mul_comm]
    rw [hc]
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hη0)
  · decide

lemma quotientPolynomial_cover (d a b : R) :
    (quotientPolynomial d a b).map quotientCoverCoefficientMap=coverPolynomial d a b := by
  simp [quotientPolynomial,coverPolynomial,HoldoutConstruction.commonCoverPolynomial,
    ternaryCorrection,quotientCoverCoefficientMap,-MvPolynomial.eval₂Hom_C_eq_bind₁,map_ofNat]
  ring
lemma physicalPolynomial_cover (d : R) :
    (physicalPolynomial d).map physicalCoverCoefficientMap=
      coverPolynomial (algebraMap R (FermatBaseRing R) d) baseAlpha baseBeta := by
  rw [physicalPolynomial,Polynomial.map_add,holdoutPolynomial_commonCover]
  simp [coverPolynomial,ternaryCorrection,physicalCoverCoefficientMap,map_ofNat]

lemma coverPolynomial_map {S : Type*} [CommRing S] (f : R →+* S) (d a b : R) :
    (coverPolynomial d a b).map (MvPolynomial.map f)=coverPolynomial (f d) (f a) (f b) := by
  simp [coverPolynomial,commonCoverPolynomial_map,ternaryCorrection,map_ofNat]

end DeformedGeometry
#print axioms DeformedGeometry.physicalPolynomial_irreducible
#print axioms DeformedGeometry.coverPolynomial_irreducible
#print axioms DeformedGeometry.physicalPolynomial_cover
