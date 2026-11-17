import Proposal.GeometricRegularDeRham
import Proposal.GeometricAffineDerivations

/-!
# The protected top exterior differential on the Jacobian open

Use the regular tangent derivations of the original affine fourfold to
differentiate the four coefficients in the exterior basis of three-forms.
They act on every open of the Jacobian chart and commute with restriction.
The target of the resulting additive sheaf morphism is written in the
global volume frame of the fourth exterior power.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

noncomputable section
namespace CycleQ2LiteralResidueSheaf

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricRegularDeRham CycleQ2GeometricAffineDerivations
open CycleQ2AffineClearing HodgeComputer MvPolynomial
open scoped KaehlerDifferential

abbrev Jacobian := Spec (CommRingCat.of OpenRing)

abbrev Third := ⋀[OpenRing]^3 Ω[OpenRing⁄ℂ]

def thirdFrame : Module.Basis (Fin 4) OpenRing Third :=
  (CycleQ2GeometricAffineScheme.coordinateBasis.exteriorPower 3).reindex
    CycleQ2AffineExterior.omitEquiv.symm

abbrev threeForms := tilde (R := CommRingCat.of OpenRing) (ModuleCat.of OpenRing Third)

abbrev structureModule := SheafOfModules.unit.{0} Jacobian.ringCatSheaf

abbrev additiveForms := (SheafOfModules.toSheaf Jacobian.ringCatSheaf).obj threeForms

abbrev additiveFunctions := (SheafOfModules.toSheaf Jacobian.ringCatSheaf).obj structureModule

def coordinate (i : Fin 4) : threeForms ⟶ structureModule :=
  tilde.map (ModuleCat.ofHom (thirdFrame.coord i)) ≫ (tildeSelf (R := CommRingCat.of OpenRing)).hom

def derivative (i : Fin 4) : additiveFunctions ⟶ additiveFunctions where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom (sectionDerivativeAddHom (tangent i) U.unop)
      naturality := fun _ _ _ => rfl }

/-- Signed divergence in the global exterior coordinate frames of the smooth chart. -/
def topDifferential : additiveForms ⟶ additiveFunctions :=
  ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
    ((SheafOfModules.toSheaf Jacobian.ringCatSheaf).map (coordinate i) ≫ derivative i)

theorem topDifferential_apply (U : Jacobian.Opens) (w : additiveForms.obj.obj (op U)) :
    topDifferential.hom.app (op U) w =
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val •
        sectionDerivative (tangent i) U ((coordinate i).val.app (op U) w) := by
  unfold topDifferential
  simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, one_smul]
  norm_num
  rfl

theorem coordinate_toOpen (U : Jacobian.Opens) (i : Fin 4) (w : Third) :
    (coordinate i).val.app (op U) (tilde.toOpen (ModuleCat.of OpenRing Third) U w) =
      algebraMap OpenRing (AffineSections (A := OpenRing) U) (thirdFrame.coord i w) := by
  exact ConcreteCategory.congr_hom (C := ModuleCat (CommRingCat.of OpenRing))
    (tilde.toOpen_map_app (R := CommRingCat.of OpenRing)
      (ModuleCat.ofHom (thirdFrame.coord i)) U) w

def frameSection (U : Jacobian.Opens) (i : Fin 4) : threeForms.val.obj (op U) :=
  tilde.toOpen (ModuleCat.of OpenRing Third) U (thirdFrame i)

/-- A regular three-form with prescribed coefficients in the global third exterior frame. -/
def sectionOfCoordinates (U : Jacobian.Opens) (v : Fin 4 → AffineSections (A := OpenRing) U) :
    threeForms.val.obj (op U) :=
  ∑ i : Fin 4, (show Jacobian.ringCatSheaf.obj.obj (op U) from v i) • frameSection U i

theorem coordinate_sectionOfCoordinates (U : Jacobian.Opens)
    (v : Fin 4 → AffineSections (A := OpenRing) U) (i : Fin 4) :
    (coordinate i).val.app (op U) (sectionOfCoordinates U v) = v i := by
  classical
  change ((coordinate i).val.app (op U)).hom (sectionOfCoordinates U v) = v i
  simp only [sectionOfCoordinates, map_sum, map_smul]
  change (∑ j : Fin 4, v j * (show AffineSections (A := OpenRing) U from
    (coordinate i).val.app (op U) (tilde.toOpen (ModuleCat.of OpenRing Third) U (thirdFrame j)))) = _
  calc
    _ = ∑ j : Fin 4, v j * (algebraMap OpenRing (AffineSections (A := OpenRing) U)
        (thirdFrame.coord i (thirdFrame j))) := Finset.sum_congr rfl (fun j _ =>
          congrArg (v j * ·) (coordinate_toOpen U i (thirdFrame j)))
    _ = _ := by
      simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
        apply_ite]

/-- The regular coefficient of the protected residue in the original volume frame. -/
def protectedCoefficient : OpenRing :=
  algebraMap ℂ OpenRing (1 / 2 : ℂ) *
    (polynomialValue (pderiv 0 (pderiv 0 affineA)) * normalInverse ^ 3 -
      (3 * polynomialValue (pderiv 0 affineA) * polynomialValue (pderiv 0 (pderiv 0 affineF)) +
        polynomialValue affineA * polynomialValue (pderiv 0 (pderiv 0 (pderiv 0 affineF)))) *
          normalInverse ^ 4 +
      3 * polynomialValue affineA * polynomialValue (pderiv 0 (pderiv 0 affineF)) ^ 2 * normalInverse ^ 5)

theorem protectedCoefficient_local (s : OpenRing) :
    algebraMap OpenRing (LocalRing s) protectedCoefficient = residueCoefficient s affineA := by
  simp only [protectedCoefficient, residueCoefficient, localPolynomial, localNormalInverse,
    map_mul, map_sub, map_add, map_ofNat, map_pow, ← IsScalarTower.algebraMap_apply]

def protectedSection (U : Jacobian.Opens) : additiveFunctions.obj.obj (op U) :=
  algebraMap OpenRing (AffineSections (A := OpenRing) U) protectedCoefficient

theorem protectedSection_restrict {U V : Jacobian.Opens} (h : V ≤ U) :
    additiveFunctions.obj.map (homOfLE h).op (protectedSection U) = protectedSection V := rfl

end CycleQ2LiteralResidueSheaf
end

#print axioms CycleQ2LiteralResidueSheaf.topDifferential_apply
#print axioms CycleQ2LiteralResidueSheaf.protectedCoefficient_local
