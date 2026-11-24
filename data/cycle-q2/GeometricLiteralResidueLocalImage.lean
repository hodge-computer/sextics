import Proposal.GeometricAffineCohomology

/-!
# Detecting boundaries in a cokernel sheaf on an affine scheme

A section dies in the sheaf cokernel of an additive map precisely when it
has preimages on principal neighborhoods of all points. The statement
applies to complex-linear exterior differentiation after forgetting to
additive groups.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralResidueLocalImage

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricAffineCohomology

variable {A : Type} [CommRing A] {F G : AbSheaf A} (d : F ⟶ G)
    (U : Opens (PrimeSpectrum.Top A)) (ω : G.obj.obj (op U))

/-- The restriction of a section vanishing in the sheaf cokernel comes
from the source on a principal neighborhood of each point. -/
theorem exists_principal_preimage
    (hω : (cokernel.π d).hom.app (op U) ω = 0)
    (x : PrimeSpectrum A) (hx : x ∈ U) :
    ∃ (s : A) (h : PrimeSpectrum.basicOpen s ≤ U), x ∈ PrimeSpectrum.basicOpen s ∧
      ∃ η : F.obj.obj (op (PrimeSpectrum.basicOpen s)),
        d.hom.app _ η = G.obj.map (homOfLE h).op ω := by
  let q := cokernel.π d
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  let E := sheafToPresheaf (Opens.grothendieckTopology (PrimeSpectrum.Top A)) AddCommGrpCat ⋙
    (evaluation _ AddCommGrpCat).obj (op U)
  have hS : S.Exact := ShortComplex.exact_kernel q
  have he := hS.map_of_mono_of_preservesKernel E (inferInstanceAs (Mono (kernel.ι q)))
    (by infer_instance)
  obtain ⟨v, hv⟩ := (ShortComplex.ab_exact_iff (S.map E)).mp he ω hω
  change (kernel.ι q).hom.app (op U) v = ω at hv
  let l := kernel.lift q d (cokernel.condition d)
  have : Epi l := (ShortComplex.exact_cokernel d).epi_kernelLift
  have : Sheaf.IsLocallySurjective l := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat l).mpr
    inferInstance
  obtain ⟨V, i, ⟨u, hu⟩, hxV⟩ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology (PrimeSpectrum.Top A)) l.hom v x hx
  obtain ⟨_, ⟨s, rfl⟩, hxs, hsV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxV V.isOpen
  refine ⟨s, hsV.trans (leOfHom i), hxs, F.obj.map (homOfLE hsV).op u, ?_⟩
  have hdu : d.hom.app (op V) u = G.obj.map i.op ω := by
    have hcomp : l ≫ kernel.ι q = d := kernel.lift_ι _ _ _
    calc
      d.hom.app (op V) u = (kernel.ι q).hom.app (op V) (l.hom.app (op V) u) :=
        congrArg (fun k : F ⟶ G => k.hom.app (op V) u) hcomp.symm
      _ = _ := by rw [hu, NatTrans.naturality_apply, hv]
  let j : (PrimeSpectrum.basicOpen s : Opens (PrimeSpectrum.Top A)) ⟶ V := homOfLE hsV
  calc
    _ = G.obj.map j.op (d.hom.app (op V) u) := NatTrans.naturality_apply d.hom j.op u
    _ = G.obj.map j.op (G.obj.map i.op ω) := congrArg (G.obj.map j.op) hdu
    _ = _ := (G.obj.map_comp_apply i.op j.op ω).symm

/-- On a nonempty open a vanishing cokernel section therefore admits a
primitive on a principal open with nonzero denominator. -/
theorem exists_nonzero_principal_preimage
    (hω : (cokernel.π d).hom.app (op U) ω = 0) (hU : U.carrier.Nonempty) :
    ∃ (s : A) (_ : s ≠ 0) (h : PrimeSpectrum.basicOpen s ≤ U)
      (η : F.obj.obj (op (PrimeSpectrum.basicOpen s))),
        d.hom.app _ η = G.obj.map (homOfLE h).op ω := by
  obtain ⟨x, hx⟩ := hU
  obtain ⟨s, h, hxs, η, he⟩ := exists_principal_preimage d U ω hω x hx
  have hs : s ≠ 0 := fun e => (PrimeSpectrum.mem_basicOpen _ _).mp hxs (e ▸ x.asIdeal.zero_mem)
  exact ⟨s, hs, h, η, he⟩

/-- A principal-local boundary and a section with zero image in the
actual cokernel sheaf are equivalent on any open. -/
theorem cokernel_section_zero_iff :
    (cokernel.π d).hom.app (op U) ω = 0 ↔
      ∀ x : PrimeSpectrum A, x ∈ U →
        ∃ (s : A) (h : PrimeSpectrum.basicOpen s ≤ U), x ∈ PrimeSpectrum.basicOpen s ∧
          ∃ η : F.obj.obj (op (PrimeSpectrum.basicOpen s)),
            d.hom.app _ η = G.obj.map (homOfLE h).op ω := by
  constructor
  · exact exists_principal_preimage d U ω
  · intro hlocal
    apply TopCat.Presheaf.IsSheaf.section_ext (cokernel d).property
    intro x hx
    obtain ⟨s, h, hxs, η, he⟩ := hlocal x hx
    refine ⟨PrimeSpectrum.basicOpen s, h, hxs, ?_⟩
    change (cokernel d).obj.map (homOfLE h).op ((cokernel.π d).hom.app _ ω) =
      (cokernel d).obj.map (homOfLE h).op 0
    rw [← NatTrans.naturality_apply, ← he, map_zero]
    exact congrArg (fun k : F ⟶ cokernel d => k.hom.app _ η) (cokernel.condition d)

end CycleQ2LiteralResidueLocalImage

end

#print axioms CycleQ2LiteralResidueLocalImage.exists_nonzero_principal_preimage
#print axioms CycleQ2LiteralResidueLocalImage.cokernel_section_zero_iff
