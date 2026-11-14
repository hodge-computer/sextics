import Proposal.GeometricSurfaceAdjunction
import Proposal.GeometricIntrinsicNormal

/-!
# Residue of an arbitrary inverse-ideal-valued determinant on an actual chart

Status: source-only proof draft. An earlier version produced elaboration
errors and deterministic timeouts. The source corrections below have not
been compiled or independently replayed; verification is deferred at the
user's request. No new axioms or admissions are used.

The domain below is the actual module `Hom(I, Λ² Ω_A)` for the existing
localized surface-to-curve map `A → B`.  The residue is built from the
original conormal inclusion and universal differential quotient.  In
particular, it is not defined only for one distinguished cubic section.

`residue_eq_with_frame` proves that the construction agrees with reducing
the inverse-ideal coefficient in any determinant frame and then applying
the existing intrinsic normal adjunction.  Consequently two determinant
frames in the same localized presentation give the same residue on every
input homomorphism.  The conormal formulation below also removes the
choice of a normalized conormal generator within that presentation.

This supplies the local algebra underlying the actual canonical residue
sheaf map.  Global sheaf gluing and short exactness are separate
obligations; they are not asserted in this file.

The nonconstructive geometric strategy is due to Ben Diamond and the cited
work of Claire Voisin.  Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CanonicalRawResidue

open Module MvPolynomial
open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricIntrinsicNormal
open scoped TensorProduct

variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)

abbrev SurfaceRing := NormalSurfacePatch q h g₁ g₂ k i j
abbrev CurveRing := NormalCurvePatch q h g₁ g₂ k i j
abbrev CurveIdeal := NormalCurveIdeal q h g₁ g₂ k i j

abbrev SurfaceForms :=
  ⋀[SurfaceRing q h g₁ g₂ k i j]^2
    (KaehlerDifferential ℂ (SurfaceRing q h g₁ g₂ k i j))

abbrev RestrictedForms :=
  ⋀[CurveRing q h g₁ g₂ k i j]^2
    (RestrictedSurfaceDifferentials q h g₁ g₂ k i j)

abbrev InverseIdealForms :=
  CurveIdeal q h g₁ g₂ k i j →ₗ[SurfaceRing q h g₁ g₂ k i j]
    SurfaceForms q h g₁ g₂ k i j

/-- The actual ideal element whose class is the selected conormal basis. -/
def selectedEquation : CurveIdeal q h g₁ g₂ k i j :=
  ⟨algebraMap SurfacePoly (SurfaceRing q h g₁ g₂ k i j) (normalPolynomial q i),
    normalEquation_mem q h g₁ g₂ k i j i⟩

/-- The universal exterior scalar extension, characterized on every wedge. -/
def restrictForm : SurfaceForms q h g₁ g₂ k i j →ₛₗ[
    algebraMap (SurfaceRing q h g₁ g₂ k i j) (CurveRing q h g₁ g₂ k i j)]
      RestrictedForms q h g₁ g₂ k i j :=
  determinantBaseChange (R := CurveRing q h g₁ g₂ k i j)
    (localSurfaceKaehlerBasis ![surfaceEquation q h g₁ g₂ k, includeCurve h]
      (normalPolynomial q i) (includeCurve (X j)))

theorem restrictForm_smul (a : SurfaceRing q h g₁ g₂ k i j)
    (ω : SurfaceForms q h g₁ g₂ k i j) :
    restrictForm q h g₁ g₂ k i j (a • ω) =
      algebraMap (SurfaceRing q h g₁ g₂ k i j) (CurveRing q h g₁ g₂ k i j) a •
        restrictForm q h g₁ g₂ k i j ω :=
  (restrictForm q h g₁ g₂ k i j).map_smulₛₗ a ω

/-- The intrinsic normal coordinate is normalized on the original equation. -/
def normalCoordinate := (normalConormalEquiv q h g₁ g₂ k i j).toLinearMap

theorem normalFunctional_eq_coordinate
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[CurveRing q h g₁ g₂ k i j]
      CurveRing q h g₁ g₂ k i j) :
    φ = φ (normalEquationClass q h g₁ g₂ k i j i) •
      normalCoordinate q h g₁ g₂ k i j := by
  apply LinearMap.ext
  intro x
  change φ x = φ (normalEquationClass q h g₁ g₂ k i j i) *
    normalConormalEquiv q h g₁ g₂ k i j x
  calc
    φ x = normalConormalEquiv q h g₁ g₂ k i j x *
        φ (normalEquationClass q h g₁ g₂ k i j i) :=
      (congrArg φ (normalConormal_reconstruct q h g₁ g₂ k i j x)).symm.trans
        (φ.map_smul _ _)
    _ = _ := mul_comm _ _

/-- Reduction of an actual ideal functional followed by the canonical
conormal quotient and scalar extension. -/
def reduceFunctional
    (f : CurveIdeal q h g₁ g₂ k i j →ₗ[SurfaceRing q h g₁ g₂ k i j]
      SurfaceRing q h g₁ g₂ k i j) :
    NormalConormal q h g₁ g₂ k i j →ₗ[CurveRing q h g₁ g₂ k i j]
      CurveRing q h g₁ g₂ k i j :=
  normalFunctionalEquiv (CurveIdeal q h g₁ g₂ k i j) (fun _ ha => ha)
    ((Algebra.linearMap (SurfaceRing q h g₁ g₂ k i j)
      (CurveRing q h g₁ g₂ k i j)).comp f)

theorem reduceFunctional_toCotangent
    (f : CurveIdeal q h g₁ g₂ k i j →ₗ[SurfaceRing q h g₁ g₂ k i j]
      SurfaceRing q h g₁ g₂ k i j) (a : CurveIdeal q h g₁ g₂ k i j) :
    reduceFunctional q h g₁ g₂ k i j f
      ((1 : CurveRing q h g₁ g₂ k i j) ⊗ₜ[SurfaceRing q h g₁ g₂ k i j]
        (CurveIdeal q h g₁ g₂ k i j).toCotangent a) =
      algebraMap (SurfaceRing q h g₁ g₂ k i j) (CurveRing q h g₁ g₂ k i j) (f a) := by
  change (1 : CurveRing q h g₁ g₂ k i j) * _ = _
  exact one_mul _

@[simp] theorem reduceFunctional_selected
    (f : CurveIdeal q h g₁ g₂ k i j →ₗ[SurfaceRing q h g₁ g₂ k i j]
      SurfaceRing q h g₁ g₂ k i j) :
    reduceFunctional q h g₁ g₂ k i j f (normalEquationClass q h g₁ g₂ k i j i) =
      algebraMap (SurfaceRing q h g₁ g₂ k i j) (CurveRing q h g₁ g₂ k i j)
        (f (selectedEquation q h g₁ g₂ k i j)) := by
  change (1 : CurveRing q h g₁ g₂ k i j) * _ = _
  exact one_mul _

theorem reduceFunctional_eq
    (f : CurveIdeal q h g₁ g₂ k i j →ₗ[SurfaceRing q h g₁ g₂ k i j]
      SurfaceRing q h g₁ g₂ k i j) :
    reduceFunctional q h g₁ g₂ k i j f =
      algebraMap (SurfaceRing q h g₁ g₂ k i j) (CurveRing q h g₁ g₂ k i j)
        (f (selectedEquation q h g₁ g₂ k i j)) •
          normalCoordinate q h g₁ g₂ k i j := by
  calc
    _ = reduceFunctional q h g₁ g₂ k i j f
          (normalEquationClass q h g₁ g₂ k i j i) •
        normalCoordinate q h g₁ g₂ k i j :=
      normalFunctional_eq_coordinate q h g₁ g₂ k i j _
    _ = _ := by rw [reduceFunctional_selected]

theorem normalAdjunction_smul
    (a : CurveRing q h g₁ g₂ k i j)
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[CurveRing q h g₁ g₂ k i j]
      CurveRing q h g₁ g₂ k i j)
    (ω : RestrictedForms q h g₁ g₂ k i j) :
    normalAdjunction q h g₁ g₂ k i j (a • φ) ω =
      a • normalAdjunction q h g₁ g₂ k i j φ ω := by
  simp only [normalAdjunction, LinearMap.smulRight_apply, LinearMap.smul_apply,
    LinearEquiv.coe_coe, smul_eq_mul, smul_smul]
  congr 1
  ring

theorem normalAdjunction_form_smul (a : CurveRing q h g₁ g₂ k i j)
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[CurveRing q h g₁ g₂ k i j]
      CurveRing q h g₁ g₂ k i j)
    (ω : RestrictedForms q h g₁ g₂ k i j) :
    normalAdjunction q h g₁ g₂ k i j φ (a • ω) =
      a • normalAdjunction q h g₁ g₂ k i j φ ω :=
  (normalAdjunction q h g₁ g₂ k i j φ).map_smul a ω

/-- The residue on the actual inverse ideal with values in arbitrary
surface two-forms.  Its scalar map is the original surface-to-curve map. -/
def residue : InverseIdealForms q h g₁ g₂ k i j →ₛₗ[
    algebraMap (SurfaceRing q h g₁ g₂ k i j) (CurveRing q h g₁ g₂ k i j)]
      KaehlerDifferential ℂ (CurveRing q h g₁ g₂ k i j) where
  toFun H := normalAdjunction q h g₁ g₂ k i j (normalCoordinate q h g₁ g₂ k i j)
    (restrictForm q h g₁ g₂ k i j (H (selectedEquation q h g₁ g₂ k i j)))
  map_add' H H' := by simp only [LinearMap.add_apply, map_add]
  map_smul' a H := by
    change normalAdjunction q h g₁ g₂ k i j (normalCoordinate q h g₁ g₂ k i j)
      (restrictForm q h g₁ g₂ k i j (a • H (selectedEquation q h g₁ g₂ k i j))) = _
    rw [restrictForm_smul, normalAdjunction_form_smul]

/-- This is the local second square of the Cartier/residue diagram:
multiply an inverse-ideal functional by an arbitrary surface two-form,
then take its residue, or first reduce the functional to the actual normal
module and apply the intrinsic normal-first adjunction contraction. -/
theorem residue_smulRight
    (f : CurveIdeal q h g₁ g₂ k i j →ₗ[SurfaceRing q h g₁ g₂ k i j]
      SurfaceRing q h g₁ g₂ k i j)
    (ω : SurfaceForms q h g₁ g₂ k i j) :
    residue q h g₁ g₂ k i j (f.smulRight ω) =
      normalAdjunction q h g₁ g₂ k i j (reduceFunctional q h g₁ g₂ k i j f)
        (restrictForm q h g₁ g₂ k i j ω) := by
  change normalAdjunction q h g₁ g₂ k i j (normalCoordinate q h g₁ g₂ k i j)
    (restrictForm q h g₁ g₂ k i j
      (f (selectedEquation q h g₁ g₂ k i j) • ω)) = _
  rw [restrictForm_smul, normalAdjunction_form_smul,
    reduceFunctional_eq, normalAdjunction_smul]

/-- A regular two-form has zero residue after the canonical inclusion
`ω ↦ (a ↦ a • ω)`. -/
theorem residue_regular (ω : SurfaceForms q h g₁ g₂ k i j) :
    residue q h g₁ g₂ k i j
      ((CurveIdeal q h g₁ g₂ k i j).subtype.smulRight ω) = 0 := by
  change normalAdjunction q h g₁ g₂ k i j (normalCoordinate q h g₁ g₂ k i j)
    (restrictForm q h g₁ g₂ k i j
      ((selectedEquation q h g₁ g₂ k i j : SurfaceRing q h g₁ g₂ k i j) • ω)) = 0
  rw [restrictForm_smul]
  have hz : algebraMap (SurfaceRing q h g₁ g₂ k i j) (CurveRing q h g₁ g₂ k i j)
      (selectedEquation q h g₁ g₂ k i j) = 0 :=
    (selectedEquation q h g₁ g₂ k i j).property
  rw [hz, zero_smul, map_zero]

/-- Evaluation in any determinant frame followed by reconstruction returns
the original homomorphism, including inputs not represented by cubics. -/
theorem reconstruct_in_frame
    (e : SurfaceForms q h g₁ g₂ k i j ≃ₗ[SurfaceRing q h g₁ g₂ k i j]
      SurfaceRing q h g₁ g₂ k i j)
    (H : InverseIdealForms q h g₁ g₂ k i j) :
    (e.toLinearMap.comp H).smulRight (e.symm 1) = H := by
  apply LinearMap.ext
  intro a
  apply e.injective
  simp only [LinearMap.smulRight_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

/-- The residue is independent of the determinant frame used to express
`Hom(I, Ω²)` as the inverse ideal.  This is the formula used for sheaf gluing. -/
theorem residue_eq_with_frame
    (e : SurfaceForms q h g₁ g₂ k i j ≃ₗ[SurfaceRing q h g₁ g₂ k i j]
      SurfaceRing q h g₁ g₂ k i j)
    (H : InverseIdealForms q h g₁ g₂ k i j) :
    residue q h g₁ g₂ k i j H =
      normalAdjunction q h g₁ g₂ k i j
        (reduceFunctional q h g₁ g₂ k i j (e.toLinearMap.comp H))
        (restrictForm q h g₁ g₂ k i j (e.symm 1)) := by
  conv_lhs => rw [← reconstruct_in_frame q h g₁ g₂ k i j e H]
  exact residue_smulRight q h g₁ g₂ k i j (e.toLinearMap.comp H) (e.symm 1)

/-- Arbitrary two-forms obey the same cancellation on a change of local
determinant frame; no choice of a cubic or of its coefficient is needed. -/
theorem frame_independent
    (e₁ e₂ : SurfaceForms q h g₁ g₂ k i j ≃ₗ[SurfaceRing q h g₁ g₂ k i j]
      SurfaceRing q h g₁ g₂ k i j)
    (H : InverseIdealForms q h g₁ g₂ k i j) :
    normalAdjunction q h g₁ g₂ k i j
        (reduceFunctional q h g₁ g₂ k i j (e₁.toLinearMap.comp H))
        (restrictForm q h g₁ g₂ k i j (e₁.symm 1)) =
      normalAdjunction q h g₁ g₂ k i j
        (reduceFunctional q h g₁ g₂ k i j (e₂.toLinearMap.comp H))
        (restrictForm q h g₁ g₂ k i j (e₂.symm 1)) :=
  (residue_eq_with_frame q h g₁ g₂ k i j e₁ H).symm.trans
    (residue_eq_with_frame q h g₁ g₂ k i j e₂ H)

/-- The actual determinant coordinate on this Jacobian localization. -/
def surfaceCoordinate : SurfaceForms q h g₁ g₂ k i j ≃ₗ[
    SurfaceRing q h g₁ g₂ k i j] SurfaceRing q h g₁ g₂ k i j :=
  localSurfaceDeterminantEquiv ![surfaceEquation q h g₁ g₂ k, includeCurve h]
    (normalPolynomial q i) (includeCurve (X j))

/-- Reduction of an arbitrary ideal-valued form to the actual conormal.
Its intrinsic value on every original ideal element is proved next. -/
def reducedHom (H : InverseIdealForms q h g₁ g₂ k i j) :
    NormalConormal q h g₁ g₂ k i j →ₗ[CurveRing q h g₁ g₂ k i j]
      RestrictedForms q h g₁ g₂ k i j :=
  (reduceFunctional q h g₁ g₂ k i j
    ((surfaceCoordinate q h g₁ g₂ k i j).toLinearMap.comp H)).smulRight
      (restrictForm q h g₁ g₂ k i j ((surfaceCoordinate q h g₁ g₂ k i j).symm 1))

/-- The conormal map is induced by the actual exterior restriction of the
original homomorphism on ideal elements, rather than a chosen assignment. -/
theorem reducedHom_toCotangent (H : InverseIdealForms q h g₁ g₂ k i j)
    (a : CurveIdeal q h g₁ g₂ k i j) :
    reducedHom q h g₁ g₂ k i j H
      ((1 : CurveRing q h g₁ g₂ k i j) ⊗ₜ[SurfaceRing q h g₁ g₂ k i j]
        (CurveIdeal q h g₁ g₂ k i j).toCotangent a) =
      restrictForm q h g₁ g₂ k i j (H a) := by
  change reduceFunctional q h g₁ g₂ k i j
      ((surfaceCoordinate q h g₁ g₂ k i j).toLinearMap.comp H)
      ((1 : CurveRing q h g₁ g₂ k i j) ⊗ₜ[SurfaceRing q h g₁ g₂ k i j]
        (CurveIdeal q h g₁ g₂ k i j).toCotangent a) •
      restrictForm q h g₁ g₂ k i j ((surfaceCoordinate q h g₁ g₂ k i j).symm 1) = _
  rw [reduceFunctional_toCotangent]
  exact (restrictForm_smul q h g₁ g₂ k i j
    (surfaceCoordinate q h g₁ g₂ k i j (H a))
    ((surfaceCoordinate q h g₁ g₂ k i j).symm 1)).symm.trans
      (congrArg (restrictForm q h g₁ g₂ k i j)
        (LinearMap.congr_fun
          (reconstruct_in_frame q h g₁ g₂ k i j (surfaceCoordinate q h g₁ g₂ k i j) H) a))

/-- The value on actual ideal classes uniquely determines the descended
map on the entire conormal, since the original selected equation spans it. -/
theorem reducedHom_unique (H : InverseIdealForms q h g₁ g₂ k i j)
    (F : NormalConormal q h g₁ g₂ k i j →ₗ[CurveRing q h g₁ g₂ k i j]
      RestrictedForms q h g₁ g₂ k i j)
    (hF : ∀ a : CurveIdeal q h g₁ g₂ k i j,
      F ((1 : CurveRing q h g₁ g₂ k i j) ⊗ₜ[SurfaceRing q h g₁ g₂ k i j]
          (CurveIdeal q h g₁ g₂ k i j).toCotangent a) =
        restrictForm q h g₁ g₂ k i j (H a)) :
    F = reducedHom q h g₁ g₂ k i j H := by
  have he : F (normalEquationClass q h g₁ g₂ k i j i) =
      reducedHom q h g₁ g₂ k i j H (normalEquationClass q h g₁ g₂ k i j i) :=
    (hF (selectedEquation q h g₁ g₂ k i j)).trans
      (reducedHom_toCotangent q h g₁ g₂ k i j H
        (selectedEquation q h g₁ g₂ k i j)).symm
  apply LinearMap.ext
  intro x
  calc
    F x = normalConormalEquiv q h g₁ g₂ k i j x •
        F (normalEquationClass q h g₁ g₂ k i j i) :=
      (congrArg F (normalConormal_reconstruct q h g₁ g₂ k i j x)).symm.trans
        (F.map_smul _ _)
    _ = normalConormalEquiv q h g₁ g₂ k i j x •
        reducedHom q h g₁ g₂ k i j H (normalEquationClass q h g₁ g₂ k i j i) :=
      congrArg (fun z => normalConormalEquiv q h g₁ g₂ k i j x • z) he
    _ = reducedHom q h g₁ g₂ k i j H x :=
      ((reducedHom q h g₁ g₂ k i j H).map_smul _ _).symm.trans
        (congrArg (reducedHom q h g₁ g₂ k i j H)
          (normalConormal_reconstruct q h g₁ g₂ k i j x))

/-- The descended map itself, and not only its residue, is unchanged by
any choice of determinant frame. -/
theorem reducedHom_eq_with_frame
    (e : SurfaceForms q h g₁ g₂ k i j ≃ₗ[SurfaceRing q h g₁ g₂ k i j]
      SurfaceRing q h g₁ g₂ k i j)
    (H : InverseIdealForms q h g₁ g₂ k i j) :
    reducedHom q h g₁ g₂ k i j H =
      (reduceFunctional q h g₁ g₂ k i j (e.toLinearMap.comp H)).smulRight
        (restrictForm q h g₁ g₂ k i j (e.symm 1)) := by
  symm
  apply reducedHom_unique q h g₁ g₂ k i j H
  intro a
  change reduceFunctional q h g₁ g₂ k i j (e.toLinearMap.comp H)
      ((1 : CurveRing q h g₁ g₂ k i j) ⊗ₜ[SurfaceRing q h g₁ g₂ k i j]
        (CurveIdeal q h g₁ g₂ k i j).toCotangent a) •
      restrictForm q h g₁ g₂ k i j (e.symm 1) = _
  rw [reduceFunctional_toCotangent]
  exact (restrictForm_smul q h g₁ g₂ k i j (e (H a)) (e.symm 1)).symm.trans
    (congrArg (restrictForm q h g₁ g₂ k i j)
      (LinearMap.congr_fun (reconstruct_in_frame q h g₁ g₂ k i j e H) a))

/-- Contraction of a conormal-valued determinant; the next theorem
proves independence of the normalized generator used in this expression. -/
def conormalResidue
    (F : NormalConormal q h g₁ g₂ k i j →ₗ[CurveRing q h g₁ g₂ k i j]
      RestrictedForms q h g₁ g₂ k i j) :
    KaehlerDifferential ℂ (CurveRing q h g₁ g₂ k i j) :=
  normalAdjunction q h g₁ g₂ k i j (normalCoordinate q h g₁ g₂ k i j)
    (F (normalEquationClass q h g₁ g₂ k i j i))

/-- Any conormal generator and its normalized dual compute the same
residue.  Normalization `φ x = 1` suffices because the actual conormal
module is a line; no independent spanning premise is introduced. -/
theorem conormal_generator_independent
    (F : NormalConormal q h g₁ g₂ k i j →ₗ[CurveRing q h g₁ g₂ k i j]
      RestrictedForms q h g₁ g₂ k i j)
    (x : NormalConormal q h g₁ g₂ k i j)
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[CurveRing q h g₁ g₂ k i j]
      CurveRing q h g₁ g₂ k i j)
    (hφ : φ x = 1) :
    normalAdjunction q h g₁ g₂ k i j φ (F x) =
      conormalResidue q h g₁ g₂ k i j F := by
  have hx : F x = normalConormalEquiv q h g₁ g₂ k i j x •
      F (normalEquationClass q h g₁ g₂ k i j i) := by
    exact (congrArg F (normalConormal_reconstruct q h g₁ g₂ k i j x)).symm.trans
      (F.map_smul _ _)
  have hone : φ (normalEquationClass q h g₁ g₂ k i j i) *
      normalConormalEquiv q h g₁ g₂ k i j x = 1 := by
    calc
      _ = normalConormalEquiv q h g₁ g₂ k i j x *
          φ (normalEquationClass q h g₁ g₂ k i j i) := mul_comm _ _
      _ = φ x := (φ.map_smul _ _).symm.trans
        (congrArg φ (normalConormal_reconstruct q h g₁ g₂ k i j x))
      _ = 1 := hφ
  rw [hx, normalFunctional_eq_coordinate q h g₁ g₂ k i j φ,
    normalAdjunction_smul, normalAdjunction_form_smul, smul_smul, hone, one_smul]
  rfl

theorem residue_eq_conormal (H : InverseIdealForms q h g₁ g₂ k i j) :
    residue q h g₁ g₂ k i j H =
      conormalResidue q h g₁ g₂ k i j (reducedHom q h g₁ g₂ k i j H) := by
  change normalAdjunction q h g₁ g₂ k i j (normalCoordinate q h g₁ g₂ k i j)
    (restrictForm q h g₁ g₂ k i j (H (selectedEquation q h g₁ g₂ k i j))) =
      normalAdjunction q h g₁ g₂ k i j (normalCoordinate q h g₁ g₂ k i j)
        (reducedHom q h g₁ g₂ k i j H
          ((1 : CurveRing q h g₁ g₂ k i j) ⊗ₜ[SurfaceRing q h g₁ g₂ k i j]
            (CurveIdeal q h g₁ g₂ k i j).toCotangent
              (selectedEquation q h g₁ g₂ k i j)))
  exact congrArg
    (normalAdjunction q h g₁ g₂ k i j (normalCoordinate q h g₁ g₂ k i j))
    (reducedHom_toCotangent q h g₁ g₂ k i j H
      (selectedEquation q h g₁ g₂ k i j)).symm

/-- An arbitrary inverse-ideal-valued two-form may be evaluated with any
normalized conormal pair; both the form and the ideal class remain actual. -/
theorem residue_eq_with_conormal_generator
    (H : InverseIdealForms q h g₁ g₂ k i j)
    (x : NormalConormal q h g₁ g₂ k i j)
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[CurveRing q h g₁ g₂ k i j]
      CurveRing q h g₁ g₂ k i j)
    (hφ : φ x = 1) :
    residue q h g₁ g₂ k i j H =
      normalAdjunction q h g₁ g₂ k i j φ (reducedHom q h g₁ g₂ k i j H x) :=
  (residue_eq_conormal q h g₁ g₂ k i j H).trans
    (conormal_generator_independent q h g₁ g₂ k i j
      (reducedHom q h g₁ g₂ k i j H) x φ hφ).symm

#print axioms residue
#print axioms residue_smulRight
#print axioms residue_regular
#print axioms frame_independent
#print axioms reducedHom_toCotangent
#print axioms reducedHom_unique
#print axioms reducedHom_eq_with_frame
#print axioms conormal_generator_independent
#print axioms residue_eq_with_conormal_generator

end CycleQ2CanonicalRawResidue

end
