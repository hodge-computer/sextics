import Proposal.GeometricLocalizedDerivations

/-!
# Arbitrary derivations of the actual affine structure sheaf

The localization extension of any complex derivation acts pointwise on
actual regular sections. The fraction rule proves regularity on every
open, and the resulting derivation commutes with the genuine restrictions.
This construction does not require a rank-one Kähler module.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricAffineDerivations

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricLocalizedDerivations

variable {A : Type} [CommRing A] [Algebra ℂ A]

abbrev AffineSections (U : Opens (PrimeSpectrum.Top A)) :=
  (Spec.structureSheaf A).obj.obj (op U)

theorem derivative_isLocallyFraction (δ : Derivation ℂ A A)
    (U : Opens (PrimeSpectrum.Top A)) (s : AffineSections U) :
    (StructureSheaf.isLocallyFraction A A).pred
      (fun x : U => localizedDerivation x.1.asIdeal.primeCompl
        (StructureSheaf.Localizations A x.1) δ (s.1 x)) := by
  intro x
  obtain ⟨V, hxV, i, a, b, hab⟩ := s.2 x
  refine ⟨V, hxV, i, b * δ a - a * δ b, b * b, ?_⟩
  intro y
  obtain ⟨hb, hy⟩ := hab y
  refine ⟨y.1.asIdeal.primeCompl.mul_mem hb hb, ?_⟩
  change localizedDerivation y.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A y.1) δ (s.1 (i y)) = _
  exact (congrArg (localizedDerivation y.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A y.1) δ) hy).trans
      (localizedDerivation_mk y.1.asIdeal.primeCompl δ a ⟨b, hb⟩)

def sectionDerivative (δ : Derivation ℂ A A)
    (U : Opens (PrimeSpectrum.Top A)) (s : AffineSections U) : AffineSections U :=
  ⟨fun x => localizedDerivation x.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A x.1) δ (s.1 x), derivative_isLocallyFraction δ U s⟩

theorem sectionDerivative_add (δ : Derivation ℂ A A)
    (U : Opens (PrimeSpectrum.Top A)) (s t : AffineSections U) :
    sectionDerivative δ U (s + t) = sectionDerivative δ U s + sectionDerivative δ U t := by
  apply Subtype.ext
  funext x
  exact map_add (localizedDerivation x.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A x.1) δ) (s.1 x) (t.1 x)

theorem sectionDerivative_mul (δ : Derivation ℂ A A)
    (U : Opens (PrimeSpectrum.Top A)) (s t : AffineSections U) :
    sectionDerivative δ U (s * t) = s * sectionDerivative δ U t + t * sectionDerivative δ U s := by
  apply Subtype.ext
  funext x
  exact (localizedDerivation x.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A x.1) δ).leibniz (s.1 x) (t.1 x)

theorem sectionDerivative_algebraMap (δ : Derivation ℂ A A)
    (U : Opens (PrimeSpectrum.Top A)) (a : A) :
    sectionDerivative δ U (algebraMap A (AffineSections U) a) =
      algebraMap A (AffineSections U) (δ a) := by
  apply Subtype.ext
  funext x
  exact localizedDerivation_algebraMap x.1.asIdeal.primeCompl
    (StructureSheaf.Localizations A x.1) δ a

theorem sectionDerivative_restrict (δ : Derivation ℂ A A)
    {U V : Opens (PrimeSpectrum.Top A)} (i : V ⟶ U) (s : AffineSections U) :
    sectionDerivative δ V ((Spec.structureSheaf A).obj.map i.op s) =
      (Spec.structureSheaf A).obj.map i.op (sectionDerivative δ U s) := rfl

def sectionDerivativeAddHom (δ : Derivation ℂ A A)
    (U : Opens (PrimeSpectrum.Top A)) : AffineSections U →+ AffineSections U :=
  AddMonoidHom.mk' (sectionDerivative δ U) (sectionDerivative_add δ U)

def structureSheafDerivation (δ : Derivation ℂ A A) :
    (SheafOfModules.unit (ringSheaf (Spec.structureSheaf A))).val.Derivation'
      (coefficientMap (Spec.structureSheaf A)
        (CycleQ2GeometricAffineDifferentialSheaf.affineCoefficient A)) where
  d {U} := sectionDerivativeAddHom δ U.unop
  d_mul {U} a b := sectionDerivative_mul δ U.unop a b
  d_map {_ _} i s := rfl
  d_app {U} c := by
    change sectionDerivative δ U.unop
      (algebraMap A (AffineSections U.unop) (algebraMap ℂ A c)) = 0
    rw [sectionDerivative_algebraMap, Derivation.map_algebraMap, map_zero]

theorem structureSheafDerivation_algebraMap (δ : Derivation ℂ A A)
    (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) (a : A) :
    (structureSheafDerivation δ).d (X := U) (algebraMap A (AffineSections U.unop) a) =
      algebraMap A (AffineSections U.unop) (δ a) := sectionDerivative_algebraMap δ U.unop a

end CycleQ2GeometricAffineDerivations

end

#print axioms CycleQ2GeometricAffineDerivations.derivative_isLocallyFraction
#print axioms CycleQ2GeometricAffineDerivations.structureSheafDerivation
