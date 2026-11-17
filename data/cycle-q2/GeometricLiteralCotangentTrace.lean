import Proposal.GeometricLiteralCotangentConnecting
import Proposal.GeometricLiteralCanonicalH2Surjective
import Proposal.GeometricLiteralCanonicalTraceInjective
import Proposal.GeometricLiteralCanonicalResidueGenerator

/-!
# The algebraic residue trace on the canonical cohomology of the original surface

Every class in H²(K_D) is represented on the triple coordinate intersection.
Its residue is the Laurent coefficient with basis index (2,2) and exponent
(-1,-1,-1). Its kernel on sections consists exactly of the Čech boundaries.
The class with coefficient x₀²w²/(x₁x₂x₃) has residue one. These facts determine
a complex-linear trace isomorphism and give a nonzero value on the retained
cubic times the Chern connecting class.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentTrace

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2CanonicalCoordinateH2 CycleQ2CanonicalResidueNonzero CycleQ2CanonicalCubicDiagram
  CycleQ2IncidenceFirstOrderCanonicalH2 CycleQ2LiteralSheafOneClasses
  CycleQ2LiteralCotangentShortExact CycleQ2LiteralCotangentConnecting
  CycleQ2LiteralCanonicalTraceLinearity CycleQ2LiteralCanonicalTraceInjective
  CycleQ2LiteralCanonicalResidueGenerator CycleQ2LiteralCanonicalH2Surjective

local instance additiveHasExt : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (CycleQ2LiteralProjectiveCotangent.ClosedSurface : TopCat)) := HasExt.standard _

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

abbrev TripleSections := CanonicalSheaf.obj.obj (op TripleOpen)
abbrev CanonicalH2 := CanonicalSheaf.H' 2 ⊤

private def residue (x : CanonicalH2) : ℂ :=
  canonicalSectionTrace (Classical.choose (canonicalConnecting_surjective x))

private theorem residue_eq (x : CanonicalH2) (s : TripleSections)
    (h : canonicalConnecting s = x) : residue x = canonicalSectionTrace s := by
  let t := Classical.choose (canonicalConnecting_surjective x)
  have ht : canonicalConnecting t = x := Classical.choose_spec (canonicalConnecting_surjective x)
  have hk : canonicalConnecting (t - s) = 0 := by rw [map_sub, ht, h, sub_self]
  have he := canonicalSectionTrace_zero_of_connecting_zero (t - s) hk
  rwa [map_sub, sub_eq_zero] at he

/-- The normalized Laurent residue on every derived degree-two canonical class. -/
def algebraicTrace : CanonicalH2 →ₗ[ℂ] ℂ where
  toFun := residue
  map_add' x y := by
    obtain ⟨a,ha⟩ := canonicalConnecting_surjective x
    obtain ⟨b,hb⟩ := canonicalConnecting_surjective y
    rw [residue_eq (x+y) (a+b) ((map_add canonicalConnecting a b).trans (congrArg₂ (·+·) ha hb)),
      residue_eq x a ha, residue_eq y b hb, map_add]
  map_smul' c x := by
    obtain ⟨a,ha⟩ := canonicalConnecting_surjective x
    rw [residue_eq (c • x) (sectionScalar c a) ((canonicalConnecting_smul c a).trans (congrArg (c • ·) ha)),
      canonicalSectionTrace_smul, residue_eq x a ha]
    rfl

/-- Evaluation on every coordinate representative is the fixed Laurent coefficient. -/
theorem algebraicTrace_eq (s : TripleSections) :
    algebraicTrace (canonicalConnecting s) = canonicalSectionTrace s := residue_eq _ s rfl

theorem algebraicTrace_eq_zero_iff (x : CanonicalH2) : algebraicTrace x = 0 ↔ x = 0 := by
  obtain ⟨s,rfl⟩ := canonicalConnecting_surjective x
  rw [algebraicTrace_eq, canonicalSectionTrace_eq_zero_iff]

theorem algebraicTrace_injective : Function.Injective algebraicTrace := by
  intro x y h
  apply sub_eq_zero.mp
  exact (algebraicTrace_eq_zero_iff _).mp (by rw [map_sub, h, sub_self])

theorem algebraicTrace_generator :
    algebraicTrace (canonicalConnecting canonicalResidueGenerator) = 1 :=
  (algebraicTrace_eq _).trans canonicalSectionTrace_residueGenerator

/-- The residue with value one on the explicit monomial class identifies H²(K_D) with ℂ. -/
def algebraicTraceEquiv : CanonicalH2 ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective algebraicTrace ⟨algebraicTrace_injective, by
    intro c
    exact ⟨c • canonicalConnecting canonicalResidueGenerator, by
      rw [map_smul, algebraicTrace_generator, smul_eq_mul, mul_one]⟩⟩

theorem eq_trace_smul_generator (x : CanonicalH2) :
    x = algebraicTrace x • canonicalConnecting canonicalResidueGenerator := by
  apply algebraicTrace_injective
  rw [map_smul, algebraicTrace_generator, smul_eq_mul, mul_one]

/-- A linear functional agrees with the residue when it has the same normalization. -/
theorem eq_algebraicTrace_of_generator (f : CanonicalH2 →ₗ[ℂ] ℂ)
    (hf : f (canonicalConnecting canonicalResidueGenerator) = 1) : f = algebraicTrace := by
  apply LinearMap.ext
  intro x
  calc f x = f (algebraicTrace x • canonicalConnecting canonicalResidueGenerator) :=
          congrArg f (eq_trace_smul_generator x)
       _ = algebraicTrace x := by rw [map_smul, hf, smul_eq_mul, mul_one]

/-- The original Chern boundary paired with the retained cubic has nonzero algebraic residue. -/
theorem chernCubic_trace_ne_zero :
    algebraicTrace (cubicH2 firstOrderWeightedCubic
      (chernDerivedClass.comp cotangentAdditiveShortExact.extClass rfl)) ≠ 0 :=
  fun h => firstOrderCubic_connecting_ne_zero ((algebraicTrace_eq_zero_iff _).mp h)

end CycleQ2LiteralCotangentTrace

end

#print axioms CycleQ2LiteralCotangentTrace.algebraicTraceEquiv
#print axioms CycleQ2LiteralCotangentTrace.chernCubic_trace_ne_zero
