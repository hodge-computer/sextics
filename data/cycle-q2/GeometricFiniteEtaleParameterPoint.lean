import Proposal.GeometricProperParameterSpecialization
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Field

/-!
# Finite etale parameter points in the actual specialized fiber

The previous proper-image construction gives a nonempty parameter fiber
above any field-valued base point. This file chooses a closed point of
that actual fiber, proves its residue extension finite, and proves that
its spectrum is finite, etale, and surjective over the original field
when that field has characteristic zero. The resulting map to the original
parameter space retains the actual pullback square.

The residue field is constructed from the selected point; neither a finite
extension nor a lift over it is assumed. In particular the field may be the
function field of the exact pencil, rather than the complex ground field.

This supplies the generic finite-etale point needed before spreading out
a multisection. It does not extend that point over an open of the pencil,
construct the flag-Hilbert space, identify specialized cycle classes, or
prove the protected residue exactness. The original theorem is unchanged.
Prepared for fqlx with OpenAI ChatGPT assistance, 15 November 2026.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CycleQ2FiniteEtaleParameterPoint

section FieldPoints

variable {K L : Type u} [Field K] [Field L]

/-- A finite extension of characteristic-zero fields gives an etale
morphism of their actual spectra. The field map is not replaced. -/
theorem etale_of_finite_field_map [CharZero K]
    (f : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) [IsFinite f] :
    Etale f := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have hfinite : φ.hom.Finite := (IsFinite.SpecMap_iff φ).mp inferInstance
  letI : Algebra K L := φ.hom.toAlgebra
  haveI : Module.Finite K L := hfinite
  haveI : Algebra.IsSeparable K L :=
    ⟨fun x => (minpoly.irreducible (Algebra.IsIntegral.isIntegral x)).separable⟩
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  change Algebra.Etale K L
  exact ⟨Algebra.FormallyEtale.of_isSeparable K L,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))

/-- The exact field morphism underlying a point over the base field. -/
def pointFieldMap (x : X) : CommRingCat.of K ⟶ X.residueField x :=
  Spec.preimage (X.fromSpecResidueField x ≫ f)

@[simp]
theorem pointFieldMap_spec (x : X) :
    Spec.map (pointFieldMap f x) = X.fromSpecResidueField x ≫ f :=
  Spec.map_preimage _

/-- A closed point of an actual locally finite-type field scheme has a
finite residue extension, with the original structural map. -/
theorem closedPoint_isFinite [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed {x}) :
    IsFinite (X.fromSpecResidueField x ≫ f) := by
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  apply isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.mpr
  infer_instance

/-- Ring-level finiteness of the very same residue extension. -/
theorem pointFieldMap_finite [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed {x}) : (pointFieldMap f x).hom.Finite := by
  rw [← IsFinite.SpecMap_iff, pointFieldMap_spec]
  exact closedPoint_isFinite f x hx

/-- The point is chosen inside any prescribed nonempty locally closed
locus, not in a substituted parameter scheme. -/
theorem exists_finite_etale_closedPoint_in [CharZero K] [LocallyOfFiniteType f]
    (W : Set X) (hW : W.Nonempty) (hWlc : IsLocallyClosed W) :
    ∃ x : X, x ∈ W ∧ IsClosed {x} ∧
      (pointFieldMap f x).hom.Finite ∧
      IsFinite (X.fromSpecResidueField x ≫ f) ∧
      Etale (X.fromSpecResidueField x ≫ f) ∧
      Surjective (X.fromSpecResidueField x ≫ f) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, hxW, hx⟩ := nonempty_inter_closedPoints hW hWlc
  have hfinite := closedPoint_isFinite f x hx
  have hetale : Etale (X.fromSpecResidueField x ≫ f) :=
    etale_of_finite_field_map (K := K) (L := X.residueField x) _
  exact ⟨x, hxW, hx, pointFieldMap_finite f x hx,
    hfinite, hetale, inferInstance⟩

/-- A nonempty finite-type fiber supplies its own finite etale point. -/
theorem exists_finite_etale_closedPoint [CharZero K] [LocallyOfFiniteType f]
    [Nonempty X] :
    ∃ x : X, IsClosed {x} ∧
      (pointFieldMap f x).hom.Finite ∧
      IsFinite (X.fromSpecResidueField x ≫ f) ∧
      Etale (X.fromSpecResidueField x ≫ f) ∧
      Surjective (X.fromSpecResidueField x ≫ f) := by
  obtain ⟨x, _, hx, hf, hfin, he, hs⟩ :=
    exists_finite_etale_closedPoint_in f Set.univ Set.univ_nonempty
      isOpen_univ.isLocallyClosed
  exact ⟨x, hx, hf, hfin, he, hs⟩

end FieldPoints

section ActualParameterFiber

open CycleQ2ProperParameterSpecialization

variable {S P V : Scheme.{u}} (p : P ⟶ S) (s : V ⟶ P)
variable {K : Type u} [Field K] [CharZero K]
variable (b : Spec (CommRingCat.of K) ⟶ S)

/-- The finite point's map to the original parameter space, through the
actual pullback rather than an unrelated abstract field point. -/
def finitePointToParameter (x : specializedParameters p s b) :
    Spec ((specializedParameters p s b).residueField x) ⟶ P :=
  (specializedParameters p s b).fromSpecResidueField x ≫
    specializationToParameter p s b

/-- The same field extension is the structural map to the original base. -/
@[reassoc]
theorem finitePoint_over_base (x : specializedParameters p s b) :
    finitePointToParameter p s b x ≫ p =
      Spec.map (pointFieldMap (specializationToBase p s b) x) ≫ b := by
  rw [finitePointToParameter, Category.assoc, specialization_over_base,
    pointFieldMap_spec, Category.assoc]

/-- Properness and dominance provide a finite etale field extension and
an actual parameter over it. The extension and the parameter are both
conclusions. No density condition on the selected field-valued point is
needed, so this applies to the generic point of a special pencil. -/
theorem exists_finite_etale_parameter [IsProper p] [IsDominant (s ≫ p)] :
    ∃ x : specializedParameters p s b, IsClosed {x} ∧
      (pointFieldMap (specializationToBase p s b) x).hom.Finite ∧
      IsFinite (Spec.map (pointFieldMap (specializationToBase p s b) x)) ∧
      Etale (Spec.map (pointFieldMap (specializationToBase p s b) x)) ∧
      Surjective (Spec.map (pointFieldMap (specializationToBase p s b) x)) ∧
      finitePointToParameter p s b x ≫ p =
        Spec.map (pointFieldMap (specializationToBase p s b) x) ≫ b := by
  have : Surjective (specializationToBase p s b) :=
    specializationToBase_surjective p s b
  obtain ⟨x₀, _⟩ := (specializationToBase p s b).surjective
    (IsLocalRing.closedPoint K)
  have : Nonempty (specializedParameters p s b) := ⟨x₀⟩
  obtain ⟨x, hx, hf, hfin, he, hs⟩ :=
    exists_finite_etale_closedPoint (specializationToBase p s b)
  refine ⟨x, hx, hf, ?_, ?_, ?_, finitePoint_over_base p s b x⟩
  · simpa only [pointFieldMap_spec] using hfin
  · simpa only [pointFieldMap_spec] using he
  · simpa only [pointFieldMap_spec] using hs

/-- Closed incidence conditions from the original section are retained by
the actual finite field-valued parameter. This does not identify cycle
classes or scheme-theoretic multiplicities. -/
theorem finitePoint_mem_of_closed [QuasiCompact s]
    (Z : Set P) (hZ : IsClosed Z) (hs : Set.range s ⊆ Z)
    (x : specializedParameters p s b)
    (a : Spec ((specializedParameters p s b).residueField x)) :
    finitePointToParameter p s b x a ∈ Z := by
  exact specialized_parameter_mem_of_closed p s b Z hZ hs
    ((specializedParameters p s b).fromSpecResidueField x a)

/-- The closed endpoint attached to an original dense-open section. -/
theorem denseOpenSection_finite_etale_parameter [IsProper p]
    (U : S.Opens) (σ : U.toScheme ⟶ P)
    (hU : Dense (U : Set S)) (hσ : σ ≫ p = U.ι) :
    ∃ x : specializedParameters p σ b, IsClosed {x} ∧
      (pointFieldMap (specializationToBase p σ b) x).hom.Finite ∧
      IsFinite (Spec.map (pointFieldMap (specializationToBase p σ b) x)) ∧
      Etale (Spec.map (pointFieldMap (specializationToBase p σ b) x)) ∧
      Surjective (Spec.map (pointFieldMap (specializationToBase p σ b) x)) ∧
      finitePointToParameter p σ b x ≫ p =
        Spec.map (pointFieldMap (specializationToBase p σ b) x) ≫ b := by
  have : IsDominant (σ ≫ p) := section_isDominant p U σ hU hσ
  exact exists_finite_etale_parameter p σ b

end ActualParameterFiber

end CycleQ2FiniteEtaleParameterPoint

end

#print axioms CycleQ2FiniteEtaleParameterPoint.etale_of_finite_field_map
#print axioms CycleQ2FiniteEtaleParameterPoint.exists_finite_etale_closedPoint_in
#print axioms CycleQ2FiniteEtaleParameterPoint.denseOpenSection_finite_etale_parameter
#print axioms CycleQ2FiniteEtaleParameterPoint.finitePoint_mem_of_closed
