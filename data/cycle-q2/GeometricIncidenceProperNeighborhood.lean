import Proposal.GeometricIncidenceSurfaceProper
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# A uniform base neighborhood from the original proper surface family

Status: source-only proof draft. No elaboration or kernel replay was run.

For a proper morphism and an open subset U of its source, remove the
closed image of the complement of U. This gives the largest base open
whose full inverse image is contained in U. It contains a chosen base
point precisely when the entire fiber at that point lies in U.

The final theorem applies this construction to the original incidence
surface using its proved properness, rather than asking for properness
as a new premise. Containment of the seed fiber in an appropriate open
smooth locus remains a separate obligation; this module does not assert
that containment or infer relative smoothness from a smooth special fiber.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2IncidenceProperNeighborhood

open CategoryTheory AlgebraicGeometry

variable {X Y : Scheme}

/-- The complement of the closed image of the bad source locus. -/
def properBaseNeighborhood (f : X ⟶ Y) [IsProper f] (U : X.Opens) : Y.Opens :=
  ⟨(f '' (U : Set X)ᶜ)ᶜ, (f.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩

theorem mem_properBaseNeighborhood_iff (f : X ⟶ Y) [IsProper f]
    (U : X.Opens) (y : Y) :
    y ∈ properBaseNeighborhood f U ↔ ∀ x : X, f x = y → x ∈ U := by
  change (y ∉ f '' (U : Set X)ᶜ) ↔ _
  constructor
  · intro hy x hxy
    by_contra hx
    exact hy ⟨x, hx, hxy⟩
  · intro h
    rintro ⟨x, hx, hxy⟩
    exact hx (h x hxy)

/-- Every point of every fiber over the constructed open lies in U. -/
theorem properBaseNeighborhood_preimage_le (f : X ⟶ Y) [IsProper f]
    (U : X.Opens) :
    f ⁻¹ᵁ properBaseNeighborhood f U ≤ U := by
  intro x hx
  exact (mem_properBaseNeighborhood_iff f U (f x)).mp hx x rfl

/-- This is the largest base open with the required inverse-image inclusion. -/
theorem le_properBaseNeighborhood_iff (f : X ⟶ Y) [IsProper f]
    (U : X.Opens) (V : Y.Opens) :
    V ≤ properBaseNeighborhood f U ↔ f ⁻¹ᵁ V ≤ U := by
  constructor
  · intro h x hx
    exact (mem_properBaseNeighborhood_iff f U (f x)).mp (h hx) x rfl
  · intro h y hy
    apply (mem_properBaseNeighborhood_iff f U y).mpr
    intro x hxy
    apply h
    change f x ∈ V
    rwa [hxy]

open CycleQ2IncidenceUniversalChart CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceSurfaceProper

variable {S : Type} [CommRing S] [Algebra ℂ S]

/-- For the unchanged surface family, covering one whole fiber by a
source open gives one base neighborhood on which all fibers lie in it.
Only the fiber inclusion is left as a hypothesis. -/
theorem exists_surface_base_neighborhood (y : ParameterIndex → S)
    (s : Spec (CommRingCat.of S)) (U : (surface y).Opens)
    (hs : ∀ x : surface y, surfaceToBase y x = s → x ∈ U) :
    ∃ V : (Spec (CommRingCat.of S)).Opens,
      s ∈ V ∧ surfaceToBase y ⁻¹ᵁ V ≤ U := by
  letI := surfaceToBase_proper y
  exact ⟨properBaseNeighborhood (surfaceToBase y) U,
    (mem_properBaseNeighborhood_iff (surfaceToBase y) U s).mpr hs,
    properBaseNeighborhood_preimage_le (surfaceToBase y) U⟩

end CycleQ2IncidenceProperNeighborhood

#print axioms CycleQ2IncidenceProperNeighborhood.mem_properBaseNeighborhood_iff
#print axioms CycleQ2IncidenceProperNeighborhood.exists_surface_base_neighborhood

end
