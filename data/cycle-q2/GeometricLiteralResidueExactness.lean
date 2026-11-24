import Proposal.GeometricLiteralResidueDifferential
import Proposal.GeometricLiteralResidueLocalImage
import Proposal.GeometricPrincipalRestriction

/-!
# Local sheaf criterion for the protected rational primitive

On the Jacobian chart, the top residue has a rational primitive exactly
when its section of the cokernel sheaf of exterior differentiation
vanishes on some nonempty Zariski open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralResidueExactness

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open CycleQ2LiteralResidueSheaf CycleQ2LiteralResidueLocalImage
open CycleQ2GeometricRegularDeRham CycleQ2AffineClearing

/-- The class of the fixed numerator in the additive cokernel sheaf. -/
def protectedCokernelSection (U : Jacobian.Opens) : (cokernel topDifferential).obj.obj (op U) :=
  (cokernel.π topDifferential).hom.app (op U) (protectedSection U)

theorem protectedCokernelSection_restrict {U V : Jacobian.Opens} (h : V ≤ U) :
    (cokernel topDifferential).obj.map (homOfLE h).op (protectedCokernelSection U) =
      protectedCokernelSection V := by
  rw [protectedCokernelSection, ← NatTrans.naturality_apply, protectedSection_restrict]
  rfl

/-- This equivalence uses the differential on the exterior cube sheaf and the original
four-form on the function field. Local vanishing on even one nonempty open suffices. -/
theorem protected_exact_iff_cokernel_zero_on_nonempty_open :
    (∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA) ↔
      ∃ U : Jacobian.Opens, U.carrier.Nonempty ∧ protectedCokernelSection U = 0 := by
  rw [CycleQ2GeometricRationalSpread.protected_exact_iff_exists_regular_zero]
  constructor
  · rintro ⟨s, hs, hω⟩
    obtain ⟨w, hw⟩ := (principal_exact_iff s hs).mpr ((classOf_eq_zero_iff s _).mp hω)
    refine ⟨PrimeSpectrum.basicOpen s, ⟨(⊥ : PrimeSpectrum OpenRing), ?_⟩, ?_⟩
    · exact (PrimeSpectrum.mem_basicOpen s _).mpr (by simpa using hs)
    · unfold protectedCokernelSection
      rw [← hw]
      exact congrArg (fun k : additiveForms ⟶ cokernel topDifferential => k.hom.app _ w)
        (cokernel.condition topDifferential)
  · rintro ⟨U, hU, hω⟩
    obtain ⟨s, hs, h, w, hw⟩ :=
      exists_nonzero_principal_preimage topDifferential U (protectedSection U) hω hU
    rw [protectedSection_restrict h] at hw
    exact ⟨s, hs, (classOf_eq_zero_iff s _).mpr ((principal_exact_iff s hs).mp ⟨w, hw⟩)⟩

abbrev residueCokernelPresheaf : TopCat.Presheaf AddCommGrpCat (PrimeSpectrum.Top OpenRing) :=
  (cokernel topDifferential).obj

/-- The germ of the protected residue class at the zero prime of the Jacobian chart. -/
def protectedGenericGerm :=
  residueCokernelPresheaf.Γgerm (⊥ : PrimeSpectrum OpenRing) (protectedCokernelSection ⊤)

theorem cokernel_zero_on_nonempty_open_iff_generic_germ :
    (∃ U : Jacobian.Opens, U.carrier.Nonempty ∧ protectedCokernelSection U = 0) ↔
      protectedGenericGerm = 0 := by
  let P : TopCat.Presheaf AddCommGrpCat (PrimeSpectrum.Top OpenRing) := residueCokernelPresheaf
  let x : PrimeSpectrum OpenRing := ⊥
  constructor
  · rintro ⟨U, ⟨y, hy⟩, hzero⟩
    have hx : x ∈ U := ((PrimeSpectrum.le_iff_specializes x y).mp bot_le).mem_open U.isOpen hy
    change P.Γgerm x (protectedCokernelSection ⊤) = 0
    rw [← P.Γgerm_res_apply (i := homOfLE (show U ≤ ⊤ from le_top)) x hx]
    change P.germ U x hx ((cokernel topDifferential).obj.map _ (protectedCokernelSection ⊤)) = 0
    rw [protectedCokernelSection_restrict, hzero, map_zero]
  · intro h
    have he : P.germ ⊤ x trivial (protectedCokernelSection ⊤) = P.germ ⊤ x trivial 0 := by
      rw [map_zero]
      exact h
    obtain ⟨U, hx, i, j, hu⟩ := P.germ_eq (U := ⊤) (V := ⊤) x trivial trivial _ _ he
    refine ⟨U, ⟨x, hx⟩, ?_⟩
    rw [map_zero] at hu
    exact (protectedCokernelSection_restrict (leOfHom i)).symm.trans hu

/-- The actual rational three-form exists exactly when the protected germ vanishes. -/
theorem protected_exact_iff_generic_germ_zero :
    (∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm affineA) ↔ protectedGenericGerm = 0 :=
  protected_exact_iff_cokernel_zero_on_nonempty_open.trans
    cokernel_zero_on_nonempty_open_iff_generic_germ

end CycleQ2LiteralResidueExactness

end

#print axioms CycleQ2LiteralResidueExactness.protected_exact_iff_cokernel_zero_on_nonempty_open

#print axioms CycleQ2LiteralResidueExactness.protected_exact_iff_generic_germ_zero
