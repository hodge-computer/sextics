import Proposal.PhysicalModel
import Proposal.ConicResidue

/-!
Coordinates on the common cover of the deformed sextic. The maps here
are the injections proved for the exact new equations, not those of the
undeformed holdout. The coordinate argument follows fqlx's shared
CoverCoordinates construction. Prepared with OpenAI Codex assistance
for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedCover
open HoldoutConstruction Polynomial
open DeformedConic (BaseField FermatRing baseFieldAlpha baseFieldBeta TargetRing TargetField)

def coverCoefficientMap : MvPolynomial (Fin 4) BaseField →+* CoverField :=
  (algebraMap CoverRing CoverField).comp (AdjoinRoot.of coverPolynomial)
lemma coverCoefficientMap_injective : Function.Injective coverCoefficientMap :=
  (IsFractionRing.injective CoverRing CoverField).comp
    (AdjoinRoot.of.injective_of_degree_ne_zero coverPolynomial_degree_ne_zero)
@[simp] lemma coverCoefficientMap_C (c : BaseField) :
    coverCoefficientMap (MvPolynomial.C c)=algebraMap BaseField CoverField c := rfl

@[simp] lemma cover_of_C (c : BaseField) :
    algebraMap CoverRing CoverField (AdjoinRoot.of coverPolynomial (MvPolynomial.C c))=
      algebraMap BaseField CoverField c := rfl

def coverX0 : CoverField := algebraMap CoverRing CoverField (AdjoinRoot.root coverPolynomial)
def coverX1 : CoverField := coverCoefficientMap (MvPolynomial.X 0)
def coverX2 : CoverField := coverCoefficientMap (MvPolynomial.X 1)
def coverY : CoverField := coverCoefficientMap (MvPolynomial.X 2)
def coverT : CoverField := coverCoefficientMap (MvPolynomial.X 3)
def coverAlpha : CoverField := algebraMap BaseField CoverField baseFieldAlpha
def coverBeta : CoverField := algebraMap BaseField CoverField baseFieldBeta
lemma cover_fermat_relation : coverAlpha^6+coverBeta^6=1 := by
  have h := congrArg (algebraMap FermatRing CoverField) (fermat_base_relation (R := ℂ))
  simpa only [map_add,map_pow,map_one,coverAlpha,coverBeta,
    DeformedConic.baseFieldAlpha,DeformedConic.baseFieldBeta,
    ← IsScalarTower.algebraMap_apply] using h

@[simp] lemma physicalFieldMap_root : physicalFieldMap physicalRoot=coverX0 := by
  change physicalFieldMap (algebraMap PhysicalRing PhysicalField
    (AdjoinRoot.mk physicalPolynomial (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X 0))))=_
  rw [MvPolynomial.finSuccEquiv_X_zero]
  rw [physicalFieldMap_ring]
  simp only [physicalRingMap,AdjoinRoot.mk_X,AdjoinRoot.map_root,coverX0,Matrix.cons_val_zero]
@[simp] lemma physicalFieldMap_parameter (i : Fin 5) :
    physicalFieldMap (physicalParameter i)=
      ![coverX1,coverX2,coverAlpha*coverT,coverY,coverBeta*coverT] i := by
  change physicalFieldMap (algebraMap PhysicalRing PhysicalField
    (AdjoinRoot.mk physicalPolynomial (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X i.succ))))=_
  rw [MvPolynomial.finSuccEquiv_X_succ,physicalFieldMap_ring]
  change algebraMap CoverRing CoverField
    (physicalRingMap (AdjoinRoot.of physicalPolynomial (MvPolynomial.X i)))=_
  rw [physicalRingMap,AdjoinRoot.map_of]
  fin_cases i <;>
    simp [physicalCoefficientMap,physicalCoverCoefficientMap,coverCoefficientMap,
      coverX1,coverX2,coverY,coverT,coverAlpha,coverBeta,
      DeformedConic.baseFieldAlpha,DeformedConic.baseFieldBeta,cover_of_C,
      -MvPolynomial.eval₂Hom_C_eq_bind₁] <;> rfl
@[simp] lemma physicalFieldMap_residue_X (i : Fin 6) :
    physicalFieldMap (physicalResidueMap (MvPolynomial.X i))=
      ![coverX0,coverX1,coverX2,coverAlpha*coverT,coverY,coverBeta*coverT] i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact physicalFieldMap_root
  · exact physicalFieldMap_parameter j
@[simp] lemma quotientFieldMap_residue_X (i : Fin 5) :
    quotientFieldMap (DeformedConic.targetResidueMap (MvPolynomial.X i))=
      ![coverX0,coverX1,coverX2,coverY^2+coverT^2,coverY*coverT] i := by
  change quotientFieldMap (algebraMap TargetRing TargetField
    (AdjoinRoot.mk DeformedConic.targetPolynomial
      (MvPolynomial.finSuccEquiv BaseField 4 (MvPolynomial.X i))))=_
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [MvPolynomial.finSuccEquiv_X_zero,quotientFieldMap_ring]
    simp only [quotientRingMap,AdjoinRoot.mk_X,AdjoinRoot.map_root,coverX0,Matrix.cons_val_zero]
  · rw [MvPolynomial.finSuccEquiv_X_succ,quotientFieldMap_ring]
    change algebraMap CoverRing CoverField
      (quotientRingMap (AdjoinRoot.of DeformedConic.targetPolynomial (MvPolynomial.X j)))=_
    rw [quotientRingMap,AdjoinRoot.map_of]
    fin_cases j <;> simp [quotientCoverCoefficientMap,coverCoefficientMap,coverX1,coverX2,coverY,coverT]
@[simp] lemma quotientFieldMap_residue_C (c : BaseField) :
    quotientFieldMap (DeformedConic.targetResidueMap (MvPolynomial.C c))=
      algebraMap BaseField CoverField c := by
  rw [DeformedConic.targetResidueMap_C,quotientFieldMap_base]

lemma coverAlpha_ne_zero : coverAlpha ≠ 0 := by
  apply (map_ne_zero (algebraMap BaseField CoverField)).mpr
  have h := (IsFractionRing.injective FermatRing BaseField).ne (baseAlpha_ne_zero (R := ℂ))
  simpa only [baseFieldAlpha,map_zero] using h
lemma coverT_ne_zero : coverT ≠ 0 := by
  have hX : (MvPolynomial.X (3 : Fin 4) : MvPolynomial (Fin 4) BaseField) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ => (1 : BaseField))) h
    simp at he
  simpa only [map_zero,coverT] using coverCoefficientMap_injective.ne hX
lemma cover_square_difference_ne_zero : coverT^2-coverY^2 ≠ 0 := by
  have hp : ((MvPolynomial.X (3 : Fin 4))^2-(MvPolynomial.X 2)^2 :
      MvPolynomial (Fin 4) BaseField) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval ![0,0,0,(1 : BaseField)]) h
    simp at he
  simpa only [map_sub,map_pow,map_zero,coverT,coverY] using coverCoefficientMap_injective.ne hp
end DeformedCover
#print axioms DeformedCover.cover_fermat_relation
#print axioms DeformedCover.physicalFieldMap_residue_X
#print axioms DeformedCover.quotientFieldMap_residue_X
#print axioms DeformedCover.cover_square_difference_ne_zero
