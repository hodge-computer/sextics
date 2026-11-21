import Proposal.GeometricModuleLocalIso
import Proposal.GeometricTwistedModuleCore

/-!
# Identifying a framed module sheaf with the actual twisted sheaf

Two natural linear frames with generator transition `etaV = t • etaU`
determine an isomorphism with the existing twisted kernel sheaf, whose
coordinate transition is `a = t * b`. The coordinate identity is derived
from the generator identity. The global isomorphism is constructed by
actual sheaf gluing, without a global comparison premise.

A single equality of the two generators on the overlap suffices: naturality
of the frames and semilinearity of restrictions imply the identities on
all its subopens.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricCanonicalGluing

open CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricProjectiveCurve
open CycleQ2GeometricModuleLocalIso

/-- A generator identity determines the contravariant coordinate identity. -/
theorem coordinates_of_generator_relation
    {A L : Type*} [CommRing A] [AddCommGroup L] [Module A L]
    (eU eV : L ≃ₗ[A] A) (q : A)
    (h : eV.symm 1 = q • eU.symm 1) (s : L) :
    eU s = q * eV s := by
  have hs : s = eV s • eV.symm 1 := by
    apply eV.injective
    rw [eV.map_smul, LinearEquiv.apply_symm_apply]
    exact (mul_one (eV s)).symm
  calc
    eU s = eU (eV s • eV.symm 1) := congrArg eU hs
    _ = eV s * eU (eV.symm 1) := eU.map_smul _ _
    _ = eV s * q := by
      rw [h, eU.map_smul, LinearEquiv.apply_symm_apply]
      simp only [smul_eq_mul, mul_one]
    _ = q * eV s := mul_comm _ _

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})

/-- A frame is a natural linear equivalence with the actual structure module
on every subopen of the indicated open. -/
abbrev LocalFrame (M : SheafOfModules.{0} (TwistedModule.ringSheaf R)) (U : Opens X) :=
  PatchIso M (SheafOfModules.unit (TwistedModule.ringSheaf R)) U

variable {R}

/-- The frame coordinate, viewed in the actual commutative ring of sections. -/
def frameCoordinate {M : SheafOfModules.{0} (TwistedModule.ringSheaf R)}
    {U : Opens X} (e : LocalFrame R M U) (O : Opens X) (hO : O ≤ U)
    (s : M.val.obj (op O)) : R.obj.obj (op O) :=
  e.app O hO s

/-- The section whose coordinate in the chosen frame is one. -/
def frameGenerator {M : SheafOfModules.{0} (TwistedModule.ringSheaf R)}
    {U : Opens X} (e : LocalFrame R M U) (O : Opens X) (hO : O ≤ U) :
    M.val.obj (op O) :=
  (e.app O hO).symm (1 : R.obj.obj (op O))

/-- Frame generators commute with the actual module restriction maps. -/
theorem frameGenerator_naturality {M : SheafOfModules.{0} (TwistedModule.ringSheaf R)}
    {U O P : Opens X} (e : LocalFrame R M U) (hPO : P ≤ O) (hO : O ≤ U) :
    M.val.map (homOfLE hPO).op (frameGenerator e O hO) =
      frameGenerator e P (hPO.trans hO) := by
  have h := e.symm.naturality hPO hO
    (1 : R.obj.obj (op O))
  change M.val.map (homOfLE hPO).op (frameGenerator e O hO) =
    (e.app P (hPO.trans hO)).symm
      (R.obj.map (homOfLE hPO).op (1 : R.obj.obj (op O))) at h
  rw [map_one] at h
  exact h

variable (R)
variable (U V W : Opens X) (hW : W = U ⊓ V)
variable (t : (R.obj.obj (op W))ˣ)

/-- The first actual twisted-module coordinate is a natural linear frame. -/
def twistedFirstFrame : LocalFrame R (TwistedModule.moduleSheaf R U V W hW t) U where
  app O hO := TwistedModule.firstLocalSectionsLinearEquiv R U V W hW t O hO
  naturality hPO hO s :=
    (TwistedModule.firstLinearFrame_naturality R U V W hW t hPO hO s).symm

/-- The second actual twisted-module coordinate is a natural linear frame. -/
def twistedSecondFrame : LocalFrame R (TwistedModule.moduleSheaf R U V W hW t) V where
  app O hO := TwistedModule.secondLocalSectionsLinearEquiv R U V W hW t O hO
  naturality hPO hO s :=
    (TwistedModule.secondLinearFrame_naturality R U V W hW t hPO hO s).symm

private def patchTrans {S : X.Sheaf RingCat.{0}}
    {M N P : SheafOfModules.{0} S} {O : Opens X}
    (e : PatchIso M N O) (f : PatchIso N P O) : PatchIso M P O where
  app T hT := (e.app T hT).trans (f.app T hT)
  naturality hQT hT s := by
    change P.val.map (homOfLE hQT).op (f.app _ hT (e.app _ hT s)) =
      f.app _ (hQT.trans hT) (e.app _ (hQT.trans hT) (M.val.map (homOfLE hQT).op s))
    rw [f.naturality, e.naturality]

variable (M : SheafOfModules.{0} (TwistedModule.ringSheaf R))
variable (eU : LocalFrame R M U) (eV : LocalFrame R M V)

/-- The first local comparison uses the actual inverse twisted frame. -/
def firstComparison : PatchIso M (TwistedModule.moduleSheaf R U V W hW t) U :=
  patchTrans eU (twistedFirstFrame R U V W hW t).symm

/-- The second local comparison uses the actual inverse twisted frame. -/
def secondComparison : PatchIso M (TwistedModule.moduleSheaf R U V W hW t) V :=
  patchTrans eV (twistedSecondFrame R U V W hW t).symm

/-- The required generator transition on every overlap subopen. -/
def GeneratorTransition : Prop :=
  ∀ (O : Opens X) (hO : O ≤ W),
    frameGenerator eV O (hO.trans (hW.le.trans inf_le_right)) =
      Twisted.res R hO (t : _) •
        frameGenerator eU O (hO.trans (hW.le.trans inf_le_left))

/-- The single equality on W implies every subopen identity. -/
theorem generatorTransition_of_overlap
    (h : frameGenerator eV W (hW.le.trans inf_le_right) =
      (t : R.obj.obj (op W)) • frameGenerator eU W (hW.le.trans inf_le_left)) :
    GeneratorTransition R U V W hW t M eU eV := by
  intro O hO
  have hh := congrArg (M.val.map (homOfLE hO).op) h
  rw [frameGenerator_naturality, M.val.map_smul, frameGenerator_naturality] at hh
  exact hh

/-- The generator transition gives precisely the coordinate convention of
the existing twisted kernel: first coordinate equals t times the second. -/
theorem frame_coordinate_transition
    (h : GeneratorTransition R U V W hW t M eU eV)
    (O : Opens X) (hO : O ≤ W) (s : M.val.obj (op O)) :
    frameCoordinate eU O (hO.trans (hW.le.trans inf_le_left)) s =
      Twisted.res R hO (t : _) *
        frameCoordinate eV O (hO.trans (hW.le.trans inf_le_right)) s :=
  coordinates_of_generator_relation (A := R.obj.obj (op O))
    (eU.app O _) (eV.app O _) (Twisted.res R hO (t : _)) (h O hO) s

/-- The actual local comparison maps agree on common subopens. -/
theorem comparisons_compatible
    (h : GeneratorTransition R U V W hW t M eU eV) :
    (firstComparison R U V W hW t M eU).Compatible
      (secondComparison R U V W hW t M eV) := by
  intro O hU hV s
  have hO : O ≤ W := (le_inf hU hV).trans hW.ge
  apply (TwistedModule.firstLocalSectionsLinearEquiv R U V W hW t O hU).injective
  change (TwistedModule.firstLocalSectionsLinearEquiv R U V W hW t O hU)
      ((TwistedModule.firstLocalSectionsLinearEquiv R U V W hW t O hU).symm
        (eU.app O hU s)) =
    (TwistedModule.firstLocalSectionsLinearEquiv R U V W hW t O hU)
      ((TwistedModule.secondLocalSectionsLinearEquiv R U V W hW t O hV).symm
        (eV.app O hV s))
  rw [LinearEquiv.apply_symm_apply,
    TwistedModule.linearFrame_transition R U V W hW t O hO,
    LinearEquiv.apply_symm_apply]
  exact frame_coordinate_transition R U V W hW t M eU eV h O hO s

variable (hcover : U ⊔ V = ⊤)

/-- The global comparison is an actual module-sheaf isomorphism, constructed
from the compatible local frames by unique sheaf gluing. -/
def canonicalIso (h : GeneratorTransition R U V W hW t M eU eV) :
    M ≅ TwistedModule.moduleSheaf R U V W hW t :=
  glueIso M (TwistedModule.moduleSheaf R U V W hW t) U V hcover
    (firstComparison R U V W hW t M eU)
    (secondComparison R U V W hW t M eV)
    (comparisons_compatible R U V W hW t M eU eV h)

/-- A single concrete equality on the overlap is enough to construct the
actual global module-sheaf isomorphism. -/
def canonicalIsoOfOverlap
    (h : frameGenerator eV W (hW.le.trans inf_le_right) =
      (t : R.obj.obj (op W)) • frameGenerator eU W (hW.le.trans inf_le_left)) :
    M ≅ TwistedModule.moduleSheaf R U V W hW t :=
  canonicalIso R U V W hW t M eU eV hcover
    (generatorTransition_of_overlap R U V W hW t M eU eV h)

variable (h : GeneratorTransition R U V W hW t M eU eV)

/-- On the first patch, the comparison preserves the specified coordinate. -/
theorem canonicalIso_hom_first (O : Opens X) (hO : O ≤ U) (s : M.val.obj (op O)) :
    TwistedModule.firstLocalSectionsLinearEquiv R U V W hW t O hO
      ((canonicalIso R U V W hW t M eU eV hcover h).hom.val.app (op O) s) =
      eU.app O hO s := by
  rw [canonicalIso, glueIso_hom_app_of_leU]
  exact (TwistedModule.firstLocalSectionsLinearEquiv R U V W hW t O hO).apply_symm_apply _

/-- On the second patch, the comparison preserves the specified coordinate. -/
theorem canonicalIso_hom_second (O : Opens X) (hO : O ≤ V) (s : M.val.obj (op O)) :
    TwistedModule.secondLocalSectionsLinearEquiv R U V W hW t O hO
      ((canonicalIso R U V W hW t M eU eV hcover h).hom.val.app (op O) s) =
      eV.app O hO s := by
  rw [canonicalIso, glueIso_hom_app_of_leV]
  exact (TwistedModule.secondLocalSectionsLinearEquiv R U V W hW t O hO).apply_symm_apply _

/-- The inverse on the first patch is the prescribed inverse frame. -/
theorem canonicalIso_inv_first (O : Opens X) (hO : O ≤ U)
    (s : (TwistedModule.moduleSheaf R U V W hW t).val.obj (op O)) :
    (canonicalIso R U V W hW t M eU eV hcover h).inv.val.app (op O) s =
      (eU.app O hO).symm
        (TwistedModule.firstLocalSectionsLinearEquiv R U V W hW t O hO s) := by
  rw [canonicalIso, glueIso_inv_app_of_leU]
  rfl

/-- The inverse on the second patch is the prescribed inverse frame. -/
theorem canonicalIso_inv_second (O : Opens X) (hO : O ≤ V)
    (s : (TwistedModule.moduleSheaf R U V W hW t).val.obj (op O)) :
    (canonicalIso R U V W hW t M eU eV hcover h).inv.val.app (op O) s =
      (eV.app O hO).symm
        (TwistedModule.secondLocalSectionsLinearEquiv R U V W hW t O hO s) := by
  rw [canonicalIso, glueIso_inv_app_of_leV]
  rfl

#print axioms coordinates_of_generator_relation
#print axioms generatorTransition_of_overlap
#print axioms canonicalIso
#print axioms canonicalIsoOfOverlap
#print axioms canonicalIso_hom_first
#print axioms canonicalIso_inv_second

end CycleQ2GeometricCanonicalGluing
end
