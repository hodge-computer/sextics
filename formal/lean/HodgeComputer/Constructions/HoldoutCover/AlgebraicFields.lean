import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.GaussLemma
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain

/- Source component: FiniteTranscendence -/
section
/-!
Finiteness of a dominant map between function fields of the same finite
transcendence degree. This replaces a second coefficient-incidence
construction: the finite curve family already has the correct dimension.
The essential finite-type hypothesis is retained explicitly.
-/

noncomputable section

namespace HoldoutConstruction

open Cardinal Algebra

universe u

variable {K F L : Type u} [Field K] [Field F] [Field L]
variable [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]

theorem finite_of_same_finite_trdeg [Algebra.EssFiniteType K L]
    (hfinite : trdeg K F < Cardinal.aleph0)
    (hsame : trdeg K F = trdeg K L) : Module.Finite F L := by
  have hadd := trdeg_add_eq K F (A := L)
  rw [← hsame] at hadd
  have hz : trdeg F L = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hadd with h | h
    · exact False.elim ((not_le_of_gt hfinite) ((le_max_left _ _).trans h))
    · exact h
  let : Algebra.IsAlgebraic F L := trdeg_eq_zero_iff.mp hz
  let : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp K F L
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end HoldoutConstruction

#print axioms HoldoutConstruction.finite_of_same_finite_trdeg
end
end

/- Source component: FunctionFieldDimension -/
section
/-!
Dimension and finite generation for the concrete function fields used by
the holdout conic construction. All fraction fields are taken only after
the corresponding polynomial quotient has been proved to be a domain.
-/

noncomputable section

namespace HoldoutConstruction

open Cardinal Algebra Polynomial

universe u

section FractionDimension

variable (K R : Type u) [Field K] [CommRing R] [IsDomain R] [Algebra K R]

theorem fractionRing_trdeg : trdeg K (FractionRing R) = trdeg K R := by
  let : Algebra.IsAlgebraic R (FractionRing R) :=
    IsLocalization.isAlgebraic (FractionRing R) (nonZeroDivisors R)
  have h := trdeg_add_eq K R (A := FractionRing R)
  simpa only [trdeg_eq_zero, add_zero] using h.symm

omit [IsDomain R] in
theorem fractionRing_essFiniteType [Algebra.EssFiniteType K R] :
    Algebra.EssFiniteType K (FractionRing R) := by
  let : Algebra.EssFiniteType R (FractionRing R) :=
    Algebra.EssFiniteType.of_isLocalization (FractionRing R) (nonZeroDivisors R)
  exact Algebra.EssFiniteType.comp K R (FractionRing R)

end FractionDimension

section MonicHypersurface

variable {K : Type u} [Field K] {n : ℕ}
variable (p : Polynomial (MvPolynomial (Fin n) K)) (hp : p.Monic)
variable [IsDomain (AdjoinRoot p)]

include hp in
theorem monic_hypersurface_field_trdeg (hdeg : p.degree ≠ 0) :
    trdeg K (FractionRing (AdjoinRoot p)) = n := by
  let : FaithfulSMul (MvPolynomial (Fin n) K) (AdjoinRoot p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (AdjoinRoot.of.injective_of_degree_ne_zero hdeg)
  let : Module.Finite (MvPolynomial (Fin n) K) (AdjoinRoot p) :=
    Polynomial.Monic.finite_adjoinRoot hp
  have h := trdeg_add_eq K (MvPolynomial (Fin n) K) (A := AdjoinRoot p)
  rw [fractionRing_trdeg]
  simpa only [trdeg_eq_zero, add_zero, MvPolynomial.trdeg_of_isDomain,
    Cardinal.mk_fin, Cardinal.lift_natCast] using h.symm

omit [IsDomain (AdjoinRoot p)] in
theorem monic_hypersurface_field_essFiniteType :
    Algebra.EssFiniteType K (FractionRing (AdjoinRoot p)) :=
  fractionRing_essFiniteType K (AdjoinRoot p)

end MonicHypersurface

section RelativeMonicHypersurface

variable {K R : Type u} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {n : ℕ}
variable (p : Polynomial (MvPolynomial (Fin n) R)) (hp : p.Monic)
variable [IsDomain (AdjoinRoot p)]

include hp in
theorem monic_hypersurface_relative_trdeg (hdeg : p.degree ≠ 0) :
    trdeg K (FractionRing (AdjoinRoot p)) = trdeg K R + n := by
  let : FaithfulSMul (MvPolynomial (Fin n) R) (AdjoinRoot p) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (AdjoinRoot.of.injective_of_degree_ne_zero hdeg)
  let : Module.Finite (MvPolynomial (Fin n) R) (AdjoinRoot p) :=
    Polynomial.Monic.finite_adjoinRoot hp
  have h := trdeg_add_eq K (MvPolynomial (Fin n) R) (A := AdjoinRoot p)
  have hbase := trdeg_add_eq K R (A := MvPolynomial (Fin n) R)
  have hz : trdeg (MvPolynomial (Fin n) R) (AdjoinRoot p) = 0 := trdeg_eq_zero
  rw [fractionRing_trdeg, ← h, hz, add_zero, ← hbase]
  simp [MvPolynomial.trdeg_of_isDomain]

omit [IsDomain R] [IsDomain (AdjoinRoot p)] in
theorem monic_hypersurface_relative_essFiniteType [Algebra.EssFiniteType K R] :
    Algebra.EssFiniteType K (FractionRing (AdjoinRoot p)) := by
  let : Algebra.EssFiniteType K (MvPolynomial (Fin n) R) :=
    Algebra.EssFiniteType.comp K R (MvPolynomial (Fin n) R)
  let : Algebra.EssFiniteType K (AdjoinRoot p) :=
    Algebra.EssFiniteType.comp K (MvPolynomial (Fin n) R) (AdjoinRoot p)
  exact fractionRing_essFiniteType K (AdjoinRoot p)

end RelativeMonicHypersurface

section FiniteExtension

variable (K F E : Type u) [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [Module.Finite F E]

theorem finite_extension_trdeg : trdeg K E = trdeg K F := by
  have h := trdeg_add_eq K F (A := E)
  simpa only [trdeg_eq_zero, add_zero] using h.symm

theorem polynomial_fractionRing_trdeg :
    trdeg K (FractionRing (Polynomial E)) = trdeg K F + 1 := by
  rw [fractionRing_trdeg]
  have h := trdeg_add_eq K E (A := Polynomial E)
  rw [Polynomial.trdeg_of_isDomain, finite_extension_trdeg K F E] at h
  exact h.symm

theorem polynomial_fractionRing_essFiniteType [Algebra.EssFiniteType K F] :
    Algebra.EssFiniteType K (FractionRing (Polynomial E)) := by
  let : Algebra.EssFiniteType K E := Algebra.EssFiniteType.comp K F E
  let : Algebra.EssFiniteType K (Polynomial E) :=
    Algebra.EssFiniteType.comp K E (Polynomial E)
  exact fractionRing_essFiniteType K (Polynomial E)

end FiniteExtension

end HoldoutConstruction

#print axioms HoldoutConstruction.monic_hypersurface_field_trdeg
#print axioms HoldoutConstruction.polynomial_fractionRing_trdeg
end
end

/- Source component: MonicFieldEmbedding -/
section
/-!
An injective coefficient map and a root of a monic irreducible polynomial
give an injective map of its coordinate domain into a field. This supplies
the function-field embedding for the anchored curve family.
-/

noncomputable section

namespace HoldoutConstruction

open Polynomial

variable {R L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field L]

theorem monic_root_embedding_injective (p : Polynomial R) (hp : p.Monic)
    (hirr : Irreducible p) (φ : R →+* L) (hφ : Function.Injective φ)
    (x : L) (hx : p.eval₂ φ x = 0) :
    Function.Injective (AdjoinRoot.lift (f := p) φ x hx) := by
  let F := FractionRing R
  let ψ : F →+* L := IsFractionRing.lift hφ
  have hψ : ψ.comp (algebraMap R F) = φ := by
    ext r
    exact IsFractionRing.lift_algebraMap hφ r
  have hroot : (p.map (algebraMap R F)).eval₂ ψ x = 0 := by
    rw [Polynomial.eval₂_map, hψ]
    exact hx
  let : Fact (Irreducible (p.map (algebraMap R F))) :=
    ⟨(hp.irreducible_iff_irreducible_map_fraction_map (K := F)).mp hirr⟩
  let g : AdjoinRoot (p.map (algebraMap R F)) →+* L :=
    AdjoinRoot.lift (f := p.map (algebraMap R F)) ψ x hroot
  let m : AdjoinRoot p →+* AdjoinRoot (p.map (algebraMap R F)) :=
    AdjoinRoot.map (algebraMap R F) p (p.map (algebraMap R F)) (dvd_refl _)
  have hmap : g.comp m = AdjoinRoot.lift (f := p) φ x hx := by
    apply AdjoinRoot.ringHom_ext
    · ext r
      simp [g, m, ψ, IsFractionRing.lift_algebraMap]
    · simp [g, m]
  have hi := g.injective.comp
    (adjoinRoot_map_injective (algebraMap R F) (IsFractionRing.injective R F) p hp)
  change Function.Injective (g.comp m) at hi
  rwa [hmap] at hi

end HoldoutConstruction

#print axioms HoldoutConstruction.monic_root_embedding_injective
end
end
