import HodgeComputer.Constructions.EllipticCompanions.Residues
import Proposal.CompanionFields
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import HodgeComputer.Constructions.HoldoutCover.Piola
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/- Prepared with OpenAI Codex assistance for contributor 1337isnot1337.
See solution.md for the construction, provenance, and prior-work credit. -/

/- Source component: FanoRadialDifferentials. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace CrossedFanoRadial
open HoldoutConstruction CrossedRadialResidue
local instance : Algebra ℤ CrossedFano.FunctionField := Ring.toIntAlgebra _
local instance : Algebra ℤ AffineField := Ring.toIntAlgebra _
local instance : Algebra ℤ RadialField := Ring.toIntAlgebra _

@[simp] lemma coneFieldMap_ring (r : CrossedFano.CoordinateRing) :
    coneFieldMap (algebraMap CrossedFano.CoordinateRing CrossedFano.FunctionField r)=coneRingMap r :=
  IsFractionRing.lift_algebraMap coneRingMap_injective r

@[simp] lemma coneFieldMap_base (c : ℂ) : coneFieldMap (algebraMap ℂ CrossedFano.FunctionField c)=
    algebraMap ℂ RadialField c := by
  change coneFieldMap (algebraMap CrossedFano.CoordinateRing CrossedFano.FunctionField
    (AdjoinRoot.of CrossedFano.equation (MvPolynomial.C c)))=_
  rw [coneFieldMap_ring]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ _)=_
  rw [AdjoinRoot.lift_of,coefficientMap_C]

lemma coneFieldMap_independent (j : Fin 4) :
    coneFieldMap (CrossedFano.residueMap (MvPolynomial.X j.succ))=
      independentCoordinates CrossedFanoAffine.coordinate j := by
  rw [CrossedFano.residueMap,RingHom.comp_apply,CrossedFano.projection_X_succ,coneFieldMap_ring]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ _)=_
  rw [AdjoinRoot.lift_of,coefficientMap_X]
  fin_cases j <;> rfl

lemma coneFieldMap_normal : coneFieldMap (CrossedFano.residueMap (MvPolynomial.X 0))=coneCoordinate 1 := by
  rw [CrossedFano.residueMap,RingHom.comp_apply,CrossedFano.projection_X_zero,coneFieldMap_ring]
  exact AdjoinRoot.lift_root normal_root

lemma coneFieldMap_coordinate (j : Fin 5) :
    coneFieldMap (CrossedFano.residueMap (MvPolynomial.X j))=
      ![coneCoordinate 1,coneCoordinate 0,coneCoordinate 2,coneCoordinate 3,coneCoordinate 4] j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact coneFieldMap_normal
  · rw [coneFieldMap_independent]
    fin_cases i <;> rfl

def coneEvaluation : MvPolynomial (Fin 5) ℂ →+* RadialField :=
  coneFieldMap.comp CrossedFano.residueMap

lemma coneEvaluation_X (j : Fin 5) : coneEvaluation (MvPolynomial.X j)=
    ![coneCoordinate 1,coneCoordinate 0,coneCoordinate 2,coneCoordinate 3,coneCoordinate 4] j :=
  coneFieldMap_coordinate j

def radialDerivation (i : Fin 4) : Derivation ℤ RadialField RadialField :=
  coneDerivations CrossedFanoAffine.tangent CrossedFanoAffine.coordinate i

lemma radialDerivation_base (i : Fin 4) (c : ℂ) :
    radialDerivation i (algebraMap ℂ RadialField c)=0 := by
  change radialDerivation i (RatFunc.C (algebraMap ℂ AffineField c))=0
  exact coneDerivations_constant _ _ _ (fun j => CrossedFanoAffine.tangent_base j c) i

lemma radialDerivation_compatible (i : Fin 4) (z : CrossedFano.FunctionField) :
    radialDerivation i (coneFieldMap z)=coneFieldMap (CrossedFano.tangent i z) := by
  apply CrossedImplicitIntertwining.quotient_fraction_intertwines
    CrossedFano.projection CrossedFano.projection_surjective coneFieldMap CrossedFano.hypersurface
    ((CrossedFano.residueMap_kernel _).mpr (dvd_refl _)) CrossedFano.normal_ne_zero
    (CrossedFano.tangent i) (radialDerivation i)
  · intro c
    change CrossedFano.tangent i (CrossedFano.residueMap (MvPolynomial.C c))=0
    rw [CrossedFano.residueMap_C,CrossedFano.tangent_base]
  · intro c
    change radialDerivation i (coneFieldMap (CrossedFano.residueMap (MvPolynomial.C c)))=0
    rw [CrossedFano.residueMap_C,coneFieldMap_base,radialDerivation_base]
  · intro j
    change radialDerivation i (coneFieldMap (CrossedFano.residueMap (MvPolynomial.X j.succ)))=
      coneFieldMap (CrossedFano.tangent i (CrossedFano.residueMap (MvPolynomial.X j.succ)))
    rw [CrossedFano.tangent_parameter,coneFieldMap_independent]
    rw [radialDerivation,coneDerivations_coordinate _ _ CrossedFanoAffine.tangent_coordinate]
    split_ifs <;> simp

end CrossedFanoRadial
end
end
