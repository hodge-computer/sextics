import Proposal.DeformedCoverDomains
import Proposal.ConicDimension
import HodgeComputer.Constructions.HoldoutCover.CoverFields

/-!
The common cover of the exact deformed physical sextic and weighted
quotient. The independent coefficient maps and monic equations give
injective maps first; dimension then proves both field extensions finite.
Uses fqlx's shared coefficient injections and dimension theorems.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedCover
open HoldoutConstruction Polynomial Algebra
open DeformedConic (FermatRing BaseField baseFieldAlpha baseFieldBeta TargetRing TargetField)

lemma complex_I_six : Complex.I^6=(-1 : ℂ) := by
  rw [show (6 : ℕ)=2*3 by decide,pow_mul,Complex.I_sq]
  norm_num
lemma base_I_six : (algebraMap ℂ BaseField Complex.I)^6=(-1 : BaseField) := by
  rw [← map_pow,complex_I_six,map_neg,map_one]
abbrev physicalPolynomial := DeformedGeometry.physicalPolynomial (14⁻¹ : ℂ)
abbrev coverPolynomial := DeformedGeometry.coverPolynomial (14⁻¹ : BaseField) baseFieldAlpha baseFieldBeta
abbrev PhysicalRing := AdjoinRoot physicalPolynomial
abbrev PhysicalField := FractionRing PhysicalRing
abbrev CoverRing := AdjoinRoot coverPolynomial
abbrev CoverField := FractionRing CoverRing
instance physicalRing_domain : IsDomain PhysicalRing :=
  AdjoinRoot.isDomain_of_prime (DeformedGeometry.physicalPolynomial_irreducible _ _ complex_I_six).prime
instance coverRing_domain : IsDomain CoverRing :=
  AdjoinRoot.isDomain_of_prime (DeformedGeometry.coverPolynomial_irreducible _ _ _ _ base_I_six).prime
noncomputable instance physicalField_field : Field PhysicalField := inferInstance
noncomputable instance coverField_field : Field CoverField := inferInstance
instance physicalRing_charZero : CharZero PhysicalRing :=
  charZero_of_injective_ringHom (f := algebraMap ℂ PhysicalRing) (algebraMap ℂ PhysicalRing).injective
instance coverRing_charZero : CharZero CoverRing :=
  charZero_of_injective_ringHom (f := algebraMap BaseField CoverRing) (algebraMap BaseField CoverRing).injective
instance physicalField_charZero : CharZero PhysicalField := inferInstance
instance coverField_charZero : CharZero CoverField := inferInstance

def physicalCoefficientMap : MvPolynomial (Fin 5) ℂ →+* MvPolynomial (Fin 4) BaseField :=
  (MvPolynomial.map (algebraMap FermatRing BaseField)).comp physicalCoverCoefficientMap
lemma physicalCoefficientMap_injective : Function.Injective physicalCoefficientMap :=
  (MvPolynomial.map_injective _ (IsFractionRing.injective FermatRing BaseField)).comp
    physicalCoverCoefficientMap_injective
lemma physicalPolynomial_map : physicalPolynomial.map physicalCoefficientMap=coverPolynomial := by
  rw [physicalCoefficientMap,← Polynomial.map_map,DeformedGeometry.physicalPolynomial_cover,
    DeformedGeometry.coverPolynomial_map]
  rw [← IsScalarTower.algebraMap_apply ℂ FermatRing BaseField,map_inv₀,map_ofNat]
  rfl

private lemma adjoinMap_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (p : Polynomial R) (hp : p.Monic)
    (q : Polynomial S) (h : p.map f=q) (hd : q ∣ p.map f) :
    Function.Injective (AdjoinRoot.map f p q hd) := by
  subst q
  exact adjoinRoot_map_injective f hf p hp

def physicalRingMap : PhysicalRing →+* CoverRing :=
  AdjoinRoot.map physicalCoefficientMap physicalPolynomial coverPolynomial (by rw [physicalPolynomial_map])
lemma physicalRingMap_injective : Function.Injective physicalRingMap :=
  adjoinMap_injective physicalCoefficientMap physicalCoefficientMap_injective physicalPolynomial
    (DeformedGeometry.physicalPolynomial_monic _) coverPolynomial physicalPolynomial_map _
def quotientRingMap : TargetRing →+* CoverRing :=
  AdjoinRoot.map quotientCoverCoefficientMap DeformedConic.targetPolynomial coverPolynomial
    (by rw [DeformedGeometry.quotientPolynomial_cover])
lemma quotientRingMap_injective : Function.Injective quotientRingMap :=
  adjoinMap_injective quotientCoverCoefficientMap quotientCoverCoefficientMap_injective
    DeformedConic.targetPolynomial (DeformedGeometry.quotientPolynomial_monic _ _ _)
    coverPolynomial (DeformedGeometry.quotientPolynomial_cover _ _ _) _

def physicalCoordinateFieldMap : PhysicalRing →+* CoverField :=
  (algebraMap CoverRing CoverField).comp physicalRingMap
lemma physicalCoordinateFieldMap_injective : Function.Injective physicalCoordinateFieldMap :=
  (IsFractionRing.injective CoverRing CoverField).comp physicalRingMap_injective
def physicalFieldMap : PhysicalField →+* CoverField := IsFractionRing.lift physicalCoordinateFieldMap_injective
@[simp] lemma physicalFieldMap_ring (r : PhysicalRing) :
    physicalFieldMap (algebraMap PhysicalRing PhysicalField r)=
      algebraMap CoverRing CoverField (physicalRingMap r) :=
  IsFractionRing.lift_algebraMap physicalCoordinateFieldMap_injective r
@[simp] lemma physicalFieldMap_base (r : ℂ) :
    physicalFieldMap (algebraMap ℂ PhysicalField r)=algebraMap ℂ CoverField r := by
  change physicalFieldMap (algebraMap PhysicalRing PhysicalField
    (AdjoinRoot.of physicalPolynomial (MvPolynomial.C r)))=_
  rw [physicalFieldMap_ring]
  simp only [physicalRingMap,AdjoinRoot.map_of,physicalCoefficientMap,RingHom.comp_apply,
    physicalCoverCoefficientMap,MvPolynomial.eval₂Hom_C,MvPolynomial.map_C]
  rfl
noncomputable instance coverField_physicalAlgebra : Algebra PhysicalField CoverField := physicalFieldMap.toAlgebra
instance coverField_physicalTower : IsScalarTower ℂ PhysicalField CoverField :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := PhysicalField) (A := CoverField)
    (fun r => (physicalFieldMap_base r).symm)

def quotientCoordinateFieldMap : TargetRing →+* CoverField :=
  (algebraMap CoverRing CoverField).comp quotientRingMap
lemma quotientCoordinateFieldMap_injective : Function.Injective quotientCoordinateFieldMap :=
  (IsFractionRing.injective CoverRing CoverField).comp quotientRingMap_injective
def quotientFieldMap : TargetField →+* CoverField := IsFractionRing.lift quotientCoordinateFieldMap_injective
@[simp] lemma quotientFieldMap_ring (r : TargetRing) :
    quotientFieldMap (algebraMap TargetRing TargetField r)=
      algebraMap CoverRing CoverField (quotientRingMap r) :=
  IsFractionRing.lift_algebraMap quotientCoordinateFieldMap_injective r
@[simp] lemma quotientFieldMap_base (r : BaseField) :
    quotientFieldMap (algebraMap BaseField TargetField r)=algebraMap BaseField CoverField r := by
  change quotientFieldMap (algebraMap TargetRing TargetField
    (AdjoinRoot.of DeformedConic.targetPolynomial (MvPolynomial.C r)))=_
  rw [quotientFieldMap_ring]
  simp only [quotientRingMap,AdjoinRoot.map_of,quotientCoverCoefficientMap,MvPolynomial.eval₂Hom_C]
  rfl
noncomputable instance coverField_targetAlgebra : Algebra TargetField CoverField := quotientFieldMap.toAlgebra
instance coverField_targetTower : IsScalarTower BaseField TargetField CoverField :=
  IsScalarTower.of_algebraMap_eq (R := BaseField) (S := TargetField) (A := CoverField)
    (fun r => (quotientFieldMap_base r).symm)

lemma physicalField_trdeg : trdeg ℂ PhysicalField=5 := by
  apply monic_hypersurface_field_trdeg physicalPolynomial (DeformedGeometry.physicalPolynomial_monic _)
  exact ne_of_gt ((DeformedGeometry.physicalPolynomial_monic _).degree_pos_of_not_isUnit
    (DeformedGeometry.physicalPolynomial_irreducible _ _ complex_I_six).not_isUnit)
lemma coverPolynomial_degree_ne_zero : coverPolynomial.degree ≠ 0 :=
  ne_of_gt ((DeformedGeometry.coverPolynomial_monic _ _ _).degree_pos_of_not_isUnit
    (DeformedGeometry.coverPolynomial_irreducible _ _ _ _ base_I_six).not_isUnit)
lemma coverField_trdeg : trdeg BaseField CoverField=4 :=
  monic_hypersurface_field_trdeg coverPolynomial (DeformedGeometry.coverPolynomial_monic _ _ _)
    coverPolynomial_degree_ne_zero
lemma coverField_complex_trdeg : trdeg ℂ CoverField=5 := by
  rw [monic_hypersurface_relative_trdeg coverPolynomial
    (DeformedGeometry.coverPolynomial_monic _ _ _) coverPolynomial_degree_ne_zero]
  have h : trdeg ℂ BaseField=1 := fermatCoefficientField_trdeg
  rw [h]
  norm_num
instance coverField_complexEssFiniteType : Algebra.EssFiniteType ℂ CoverField := by
  letI : Algebra.EssFiniteType ℂ BaseField := fractionRing_essFiniteType ℂ FermatRing
  exact monic_hypersurface_relative_essFiniteType coverPolynomial
instance coverField_baseEssFiniteType : Algebra.EssFiniteType BaseField CoverField :=
  monic_hypersurface_field_essFiniteType coverPolynomial
instance coverField_physicalFinite : Module.Finite PhysicalField CoverField := by
  apply finite_of_same_finite_trdeg (K := ℂ)
  · rw [physicalField_trdeg]; exact Cardinal.natCast_lt_aleph0
  · rw [physicalField_trdeg,coverField_complex_trdeg]
instance coverField_quotientFinite : Module.Finite TargetField CoverField := by
  apply finite_of_same_finite_trdeg (K := BaseField)
  · rw [DeformedConic.targetField_trdeg]; exact Cardinal.natCast_lt_aleph0
  · rw [DeformedConic.targetField_trdeg,coverField_trdeg]

end DeformedCover
#print axioms DeformedCover.coverField_physicalFinite
#print axioms DeformedCover.coverField_quotientFinite
