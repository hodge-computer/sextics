import Proposal.DeformedCoverCoordinates
import HodgeComputer.Constructions.HoldoutCover.CoverSourceBinding

/-!
Exact numerator and normal-derivative bindings for the deformed sextic.
The new ternary terms are retained in both first and second normals.
The scalar source identity and its proof are those of fqlx's shared
CoverScalars/CoverSourceBinding construction. Prepared with OpenAI Codex
assistance for hodgepodgeconjecture.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace DeformedCover
open HoldoutConstruction MvPolynomial
open DeformedConic (BaseField baseFieldAlpha baseFieldBeta targetResidueMap quotientEquation)

lemma physical_normal_polynomial : integerPartial 0 HodgeSubmission.F=
    6*X 0^5+3*X 0^2*X 1*X 3*X 4+C (1/14 : ℂ)*(5*X 0^4*X 1+X 2^5) := by
  norm_num [integerPartial_apply,HodgeSubmission.F,MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul,Pi.single_apply,Fin.ext_iff]
  ring
lemma physical_second_normal_polynomial : integerPartial 0 (integerPartial 0 HodgeSubmission.F)=
    30*X 0^4+6*X 0*X 1*X 3*X 4+C (1/14 : ℂ)*(20*X 0^3*X 1) := by
  rw [physical_normal_polynomial]
  have h2 : MvPolynomial.pderiv (0 : Fin 6) (2 : HodgeComputer.Poly)=0 :=
    Derivation.map_natCast _ 2
  have h3 : MvPolynomial.pderiv (0 : Fin 6) (3 : HodgeComputer.Poly)=0 :=
    Derivation.map_natCast _ 3
  have h5 : MvPolynomial.pderiv (0 : Fin 6) (5 : HodgeComputer.Poly)=0 :=
    Derivation.map_natCast _ 5
  have h6 : MvPolynomial.pderiv (0 : Fin 6) (6 : HodgeComputer.Poly)=0 :=
    Derivation.map_natCast _ 6
  norm_num [integerPartial_apply,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_mul,
    Pi.single_apply,Fin.ext_iff,h2,h3,h5,h6]
  ring
lemma quotient_normal_polynomial : integerPartial 0 quotientEquation=
    6*X 0^5+3*C baseFieldAlpha*X 0^2*X 1*X 4+C (14⁻¹ : BaseField)*(5*X 0^4*X 1+X 2^5) := by
  have h2 : MvPolynomial.pderiv (0 : Fin 5) (2 : MvPolynomial (Fin 5) BaseField)=0 :=
    Derivation.map_natCast _ 2
  have h3 : MvPolynomial.pderiv (0 : Fin 5) (3 : MvPolynomial (Fin 5) BaseField)=0 :=
    Derivation.map_natCast _ 3
  have h5 : MvPolynomial.pderiv (0 : Fin 5) (5 : MvPolynomial (Fin 5) BaseField)=0 :=
    Derivation.map_natCast _ 5
  have h6 : MvPolynomial.pderiv (0 : Fin 5) (6 : MvPolynomial (Fin 5) BaseField)=0 :=
    Derivation.map_natCast _ 6
  norm_num [integerPartial_apply,quotientEquation,DeformedGeometry.weightedEquation,
    MvPolynomial.pderiv_pow,MvPolynomial.pderiv_mul,Pi.single_apply,Fin.ext_iff,h2,h3,h5,h6]
  ring
lemma quotient_second_normal_polynomial : integerPartial 0 (integerPartial 0 quotientEquation)=
    30*X 0^4+6*C baseFieldAlpha*X 0*X 1*X 4+C (14⁻¹ : BaseField)*(20*X 0^3*X 1) := by
  rw [quotient_normal_polynomial]
  have h2 : MvPolynomial.pderiv (0 : Fin 5) (2 : MvPolynomial (Fin 5) BaseField)=0 :=
    Derivation.map_natCast _ 2
  have h3 : MvPolynomial.pderiv (0 : Fin 5) (3 : MvPolynomial (Fin 5) BaseField)=0 :=
    Derivation.map_natCast _ 3
  have h5 : MvPolynomial.pderiv (0 : Fin 5) (5 : MvPolynomial (Fin 5) BaseField)=0 :=
    Derivation.map_natCast _ 5
  have h6 : MvPolynomial.pderiv (0 : Fin 5) (6 : MvPolynomial (Fin 5) BaseField)=0 :=
    Derivation.map_natCast _ 6
  norm_num [integerPartial_apply,MvPolynomial.pderiv_pow,MvPolynomial.pderiv_mul,
    Pi.single_apply,Fin.ext_iff,h2,h3,h5,h6]
  ring
local notation "ρq" => targetResidueMap
local notation "G" => quotientEquation
local notation "ρp" => physicalResidueMap
local notation "F" => HodgeSubmission.F

def coverQuotientSource : MvPolynomial (Fin 5) BaseField :=
  scaledCoverQuotientSource (1/(2*baseFieldAlpha^2))

theorem cover_physical_normal_value :
    physicalFieldMap (ρp (integerPartial 0 F)) =
      6*coverX0^5+3*coverX0^2*coverX1*(coverAlpha*coverT)*coverY+
        (14⁻¹ : CoverField)*(5*coverX0^4*coverX1+coverX2^5) := by
  rw [physical_normal_polynomial]
  simp only [map_add, map_mul, map_pow, map_ofNat, physicalFieldMap_residue_X,physicalResidueMap_C,physicalFieldMap_base,map_div₀,map_one]
  norm_num [coverAlpha,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

theorem cover_physical_second_normal_value :
    physicalFieldMap (ρp (integerPartial 0 (integerPartial 0 F))) =
      30*coverX0^4+6*coverX0*coverX1*(coverAlpha*coverT)*coverY+
        (14⁻¹ : CoverField)*(20*coverX0^3*coverX1) := by
  rw [physical_second_normal_polynomial]
  simp only [map_add, map_mul, map_pow, map_ofNat, physicalFieldMap_residue_X,physicalResidueMap_C,physicalFieldMap_base,map_div₀,map_one]
  norm_num [coverAlpha,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

theorem cover_quotient_normal_value :
    quotientFieldMap (ρq (integerPartial 0 G)) =
      6*coverX0^5+3*coverAlpha*coverX0^2*coverX1*(coverY*coverT)+
        (14⁻¹ : CoverField)*(5*coverX0^4*coverX1+coverX2^5) := by
  rw [quotient_normal_polynomial]
  simp only [map_add, map_mul, map_pow, map_ofNat,
    quotientFieldMap_residue_X, quotientFieldMap_residue_C,map_inv₀,map_ofNat]
  norm_num [coverAlpha,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

theorem cover_quotient_second_normal_value :
    quotientFieldMap (ρq (integerPartial 0 (integerPartial 0 G))) =
      30*coverX0^4+6*coverAlpha*coverX0*coverX1*(coverY*coverT)+
        (14⁻¹ : CoverField)*(20*coverX0^3*coverX1) := by
  rw [quotient_second_normal_polynomial]
  simp only [map_add, map_mul, map_pow, map_ofNat,
    quotientFieldMap_residue_X, quotientFieldMap_residue_C,map_inv₀,map_ofNat]
  norm_num [coverAlpha,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

/-- Both coordinate maps fix the distinguished normal coordinate X0. -/
theorem cover_normal_binding :
    quotientFieldMap (ρq (integerPartial 0 G)) =
      physicalFieldMap (ρp (integerPartial 0 F)) := by
  rw [cover_quotient_normal_value, cover_physical_normal_value]
  ring

theorem cover_second_normal_binding :
    quotientFieldMap (ρq (integerPartial 0 (integerPartial 0 G))) =
      physicalFieldMap (ρp (integerPartial 0 (integerPartial 0 F))) := by
  rw [cover_quotient_second_normal_value, cover_physical_second_normal_value]
  ring

theorem cover_physical_normal_ne_zero :
    physicalFieldMap (ρp (integerPartial 0 F)) ≠ 0 := by
  exact (map_ne_zero physicalFieldMap).2 physical_normal_ne_zero

theorem cover_physical_source_value :
    physicalFieldMap (ρp HodgeSubmission.A) = coverX0^3*(coverAlpha*coverT)^3 := by
  simp only [HodgeSubmission.A, map_mul, map_pow, physicalFieldMap_residue_X,physicalResidueMap_C,physicalFieldMap_base,map_div₀,map_one]
  norm_num [coverAlpha,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

theorem cover_physical_source_partial_value :
    physicalFieldMap (ρp (integerPartial 0 HodgeSubmission.A)) =
      3*coverX0^2*(coverAlpha*coverT)^3 := by
  change physicalFieldMap (ρp (integerPartial 0 holdoutSource))=_
  rw [cover_holdoutSource_partial]
  simp only [map_mul, map_pow, map_ofNat, physicalFieldMap_residue_X,physicalResidueMap_C,physicalFieldMap_base,map_div₀,map_one]
  norm_num [coverAlpha,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons]

theorem cover_quotient_source_value :
    quotientFieldMap (ρq coverQuotientSource) =
      coverX0^3*(coverY^2+coverT^2)/(2*coverAlpha^2) := by
  simp only [coverQuotientSource, scaledCoverQuotientSource, map_mul, map_pow,
    quotientFieldMap_residue_X, quotientFieldMap_residue_C,
    map_div₀, map_one, map_ofNat]
  change (1/(2*coverAlpha^2))*coverX0^3*(coverY^2+coverT^2) = _
  ring

theorem cover_quotient_source_partial_value :
    quotientFieldMap (ρq (integerPartial 0 coverQuotientSource)) =
      3*coverX0^2*(coverY^2+coverT^2)/(2*coverAlpha^2) := by
  unfold coverQuotientSource
  rw [scaledCoverQuotientSource_partial]
  simp only [map_mul, map_pow, map_ofNat, quotientFieldMap_residue_X,
    quotientFieldMap_residue_C, map_div₀, map_one]
  change 3*(1/(2*coverAlpha^2))*coverX0^2*(coverY^2+coverT^2) = _
  ring

/-- The source multiplier is exactly the nontrivial deck-character correction
whose normalized trace vanishes. The denominator T is proved nonzero in the
actual common residue field. -/
theorem cover_source_binding :
    (2*coverAlpha^5*(coverT^2-coverY^2)/coverT) *
      quotientFieldMap (ρq coverQuotientSource) =
      physicalFieldMap (ρp HodgeSubmission.A) *
        (1-physicalFieldMap (ρp (X 4))^4*(coverT^4)⁻¹) := by
  rw [cover_quotient_source_value, cover_physical_source_value]
  have hy : physicalFieldMap (ρp (X 4)) = coverY := physicalFieldMap_residue_X 4
  rw [hy]
  simpa only [div_eq_mul_inv] using
    cover_source_identity coverAlpha coverX0 coverY coverT coverAlpha_ne_zero coverT_ne_zero

/-- The exact normal-divergence source required by finite residue clearing,
with the same physical numerator and the same physical normal derivative. -/
theorem cover_normal_source_binding :
    (2*coverAlpha^5*(coverT^2-coverY^2)/coverT) *
      quotientFieldMap
        ((ρq (integerPartial 0 coverQuotientSource)*ρq (integerPartial 0 G)-
          ρq coverQuotientSource*ρq (integerPartial 0 (integerPartial 0 G))) /
            (ρq (integerPartial 0 G))^2) =
      physicalFieldMap
        ((ρp (integerPartial 0 HodgeSubmission.A)*ρp (integerPartial 0 F)-
          ρp HodgeSubmission.A*ρp (integerPartial 0 (integerPartial 0 F))) /
            (ρp (integerPartial 0 F))^2) *
        (1-physicalFieldMap (ρp (X 4))^4*(coverT^4)⁻¹) := by
  simp only [map_div₀, map_sub, map_mul, map_pow]
  rw [cover_normal_binding, cover_second_normal_binding,
    cover_quotient_source_partial_value, cover_quotient_source_value,
    cover_physical_source_partial_value, cover_physical_source_value]
  have hy : physicalFieldMap (ρp (X 4)) = coverY := physicalFieldMap_residue_X 4
  rw [hy]
  simpa only [div_eq_mul_inv] using
    cover_normal_source_identity coverAlpha coverX0 coverY coverT
      (physicalFieldMap (ρp (integerPartial 0 F)))
      (physicalFieldMap (ρp (integerPartial 0 (integerPartial 0 F))))
      coverAlpha_ne_zero coverT_ne_zero

end DeformedCover
#print axioms DeformedCover.cover_normal_binding
#print axioms DeformedCover.cover_second_normal_binding
#print axioms DeformedCover.cover_normal_source_binding
