import Proposal.GeometricAffineExactCotangentFrames

/-!
# Ordinary exterior forms in the actual differential sheaf

The identity map on the original section ring lifts ordinary Kähler
forms to the universal differential sheaf. Exterior powers followed by
the canonical sheafification unit give the genuine exterior-form
sections. These maps commute with every original restriction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2OrdinaryExteriorSections
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricSectionDifferentials
open CycleQ2GeometricDifferentialSheaf
open CycleQ2GeometricSheafKaehlerMap
open CycleQ2GeometricExteriorSheaf
open CycleQ2ExteriorSectionNaturality
variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0}) (c : ℂ →+* R.obj.obj (op ⊤))

abbrev One := differentialSheaf R c
abbrev Exterior (n : ℕ) := exteriorSheaf R (One R c).val n

def toExterior (U : Opens X) (n : ℕ) :
    letI := sectionAlgebra R c U
    (⋀[SectionRing R U]^n (SectionForms R c U)) →ₗ[SectionRing R U]
      (Exterior R c n).val.obj (op U) := by
  letI := sectionAlgebra R c U
  exact exteriorSectionLift R c (One R c) (universalDifferential R c) U
    (RingHom.id (SectionRing R U)) (fun _ => rfl) n

theorem lift_identity (U : Opens X) (ω : SectionForms R c U) :
    letI := sectionAlgebra R c U
    sectionLift R c (One R c) (universalDifferential R c) U
      (RingHom.id (SectionRing R U)) (fun _ => rfl) ω = toSheaf R c U ω := by
  letI := sectionAlgebra R c U
  have hω : ω ∈ Submodule.span (SectionRing R U)
      (Set.range (KaehlerDifferential.D ℂ (SectionRing R U))) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a,rfl⟩ := hx
    rw [sectionLift_D,toSheaf_D]
    rfl
  | zero => rw [map_zero,map_zero]
  | add x y _ _ hx hy => rw [map_add,map_add,hx,hy]
  | smul a x _ hx =>
    rw [sectionLift_smul,map_smul,hx]
    rfl

theorem toExterior_wedge (U : Opens X) (n : ℕ) (ω : Fin n → SectionForms R c U) :
    letI := sectionAlgebra R c U
    toExterior R c U n (exteriorPower.ιMulti (SectionRing R U) n ω) =
      wedgeSection R (One R c).val n U (fun j => toSheaf R c U (ω j)) := by
  letI := sectionAlgebra R c U
  rw [toExterior,exteriorSectionLift_wedge]
  apply congrArg (wedgeSection R (One R c).val n U)
  funext j
  exact lift_identity R c U (ω j)

theorem toExterior_restrict {U V : Opens X} (h : V ≤ U) (n : ℕ)
    (ω : letI := sectionAlgebra R c U
      ⋀[SectionRing R U]^n (SectionForms R c U)) :
    letI := sectionAlgebra R c U
    letI := sectionAlgebra R c V
    (Exterior R c n).val.map (homOfLE h).op (toExterior R c U n ω) =
      toExterior R c V n (exteriorDifferentialMap (sectionRestriction R c h) n ω) := by
  letI := sectionAlgebra R c U
  letI := sectionAlgebra R c V
  exact exteriorSectionLift_restriction R c (One R c) (universalDifferential R c) U
    (RingHom.id (SectionRing R U)) (fun _ => rfl) V h
    (RingHom.id (SectionRing R V)) (fun _ => rfl) (sectionRestriction R c h) (fun _ => rfl) n ω

end CycleQ2OrdinaryExteriorSections
end
#print axioms CycleQ2OrdinaryExteriorSections.toExterior_wedge
#print axioms CycleQ2OrdinaryExteriorSections.toExterior_restrict
