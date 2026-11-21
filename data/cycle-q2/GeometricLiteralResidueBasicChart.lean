import Proposal.GeometricRegularDeRham
import Proposal.GeometricAffineDerivations

/-!
# Structure sheaf coordinates on principal opens of the normal chart

The localization equivalence identifies each of the four coordinate derivations on
the regular chart with its pointwise action on actual sections over a nonempty
principal open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralResidueBasicChart

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricRegularDeRham CycleQ2GeometricAffineDerivations

def basicSectionsEquiv (s : OpenRing) :
    LocalRing s ≃ₐ[OpenRing] AffineSections (PrimeSpectrum.basicOpen s) :=
  IsLocalization.algEquiv (Submonoid.powers s) (LocalRing s)
    (AffineSections (PrimeSpectrum.basicOpen s))

@[simp] theorem basicSectionsEquiv_algebraMap (s a : OpenRing) :
    basicSectionsEquiv s (algebraMap OpenRing (LocalRing s) a) =
      algebraMap OpenRing (AffineSections (PrimeSpectrum.basicOpen s)) a :=
  (basicSectionsEquiv s).commutes a

theorem tangentOn_algebraMap (s : OpenRing) (hs : s ≠ 0) (i : Fin 4) (a : OpenRing) :
    tangentOn s i (algebraMap OpenRing (LocalRing s) a) =
      algebraMap OpenRing (LocalRing s) (tangent i a) := by
  apply localFunctionFieldMap_injective s hs
  simp only [localFunctionFieldMap_tangent, localFunctionFieldMap_algebraMap,
    functionFieldMap_tangent]

theorem basicSectionsEquiv_tangentOn (s : OpenRing) (hs : s ≠ 0) (i : Fin 4)
    (b : LocalRing s) :
    basicSectionsEquiv s (tangentOn s i b) =
      sectionDerivative (tangent i) (PrimeSpectrum.basicOpen s) (basicSectionsEquiv s b) := by
  let U := PrimeSpectrum.basicOpen s
  obtain ⟨⟨a, m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) b
  have hm' : basicSectionsEquiv s b * algebraMap OpenRing (AffineSections U) (m : OpenRing) =
      algebraMap OpenRing (AffineSections U) a := by
    simpa only [map_mul, basicSectionsEquiv_algebraMap] using congrArg (basicSectionsEquiv s) hm
  have h₁ := congrArg (fun x => basicSectionsEquiv s (tangentOn s i x)) hm
  simp only [Derivation.leibniz, smul_eq_mul, tangentOn_algebraMap s hs, map_add, map_mul,
    basicSectionsEquiv_algebraMap] at h₁
  have h₂ := congrArg (sectionDerivative (tangent i) U) hm'
  simp only [sectionDerivative_mul, sectionDerivative_algebraMap] at h₂
  exact (IsLocalization.map_units (AffineSections U) m).mul_left_cancel
    (add_left_cancel (h₁.trans h₂.symm))

theorem basicSectionsEquiv_symm_derivative (s : OpenRing) (hs : s ≠ 0) (i : Fin 4)
    (x : AffineSections (PrimeSpectrum.basicOpen s)) :
    (basicSectionsEquiv s).symm (sectionDerivative (tangent i) (PrimeSpectrum.basicOpen s) x) =
      tangentOn s i ((basicSectionsEquiv s).symm x) := by
  apply (basicSectionsEquiv s).injective
  simp only [AlgEquiv.apply_symm_apply, basicSectionsEquiv_tangentOn s hs]

theorem basicSectionsEquiv_restrict_algebraMap (s a : OpenRing) :
    (Spec.structureSheaf OpenRing).obj.map
        (homOfLE (show PrimeSpectrum.basicOpen s ≤ ⊤ from le_top)).op
        (algebraMap OpenRing (AffineSections (⊤ : Opens (PrimeSpectrum.Top OpenRing))) a) =
      basicSectionsEquiv s (algebraMap OpenRing (LocalRing s) a) := by
  rw [basicSectionsEquiv_algebraMap]
  rfl

end CycleQ2LiteralResidueBasicChart
