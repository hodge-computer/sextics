import Proposal.GeometricProjectiveCanonical
import Proposal.GeometricProjectiveNonzero

/-!
# The normalized class in actual differential-sheaf cohomology

The constructed canonical-sheaf isomorphism transports the existing
Mayer-Vietoris injection into genuine derived first cohomology of the
projective differential sheaf. The normalized class remains nonzero, and
the checked trace criterion for the degree-nine representatives is retained.

These are consequences of an actual sheaf isomorphism and functorial
derived cohomology. No surjectivity of the Cech comparison or geometric
Serre-duality trace is asserted here.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveCanonicalH1

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveCanonical CycleQ2GeometricProjectiveNonzero
  CycleQ2GeometricCechPoleReduction CycleQ2GeometricCechTrace CycleQ2SeedTrace

local instance projectiveSheavesHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve r θ))
      AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Forgetting only the module structure of the actual differential sheaf. -/
def differentialAdditiveSheaf (r θ : ℂ) :
    Sheaf (Opens.grothendieckTopology (projectiveCurve r θ)) AddCommGrpCat.{0} :=
  (SheafOfModules.toSheaf (ringSheaf (projectiveCurve r θ).sheaf)).obj
    (projectiveDifferentialSheaf r θ)

abbrev DifferentialSheafH1 (r θ : ℂ) := (differentialAdditiveSheaf r θ).H' 1 ⊤

/-- The actual canonical module isomorphism induces this additive sheaf
isomorphism, with the same degree-one sheaf used by Mayer-Vietoris. -/
def canonicalAdditiveIso (r : ℂ) (hr : r ^ 3 = 2) :
    differentialAdditiveSheaf r 0 ≅ degreeOneSheaf r 0 :=
  (SheafOfModules.toSheaf (ringSheaf (projectiveCurve r 0).sheaf)).mapIso
    (projectiveCanonicalIso r hr)

/-- The equivalence on genuine derived first cohomology is induced by
the constructed sheaf isomorphism. -/
def canonicalH1Equiv (r : ℂ) (hr : r ^ 3 = 2) :
    ProjectiveSheafH1 r 0 ≃+ DifferentialSheafH1 r 0 :=
  (((Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology (projectiveCurve r 0)) 1).mapIso
        (canonicalAdditiveIso r hr)).app (op ⊤)).addCommGroupIsoToAddEquiv.symm

private theorem root_ne_zero (r : ℂ) (hr : r ^ 3 = 2) : r ≠ 0 := by
  intro hz
  simp [hz] at hr

private def cechThroughEquiv (r θ : ℂ) (hr : r ≠ 0)
    {H : Type*} [AddCommGroup H] (e : ProjectiveSheafH1 r θ ≃+ H) :
    DegreeOneCech r θ →+ H :=
  e.toAddMonoidHom.comp (degreeOneToProjectiveH1 r θ hr)

/-- The existing actual Cech quotient maps injectively into H¹ of Ω. -/
def degreeOneToCanonicalH1 (r : ℂ) (hr : r ^ 3 = 2) :=
  cechThroughEquiv r 0 (root_ne_zero r hr) (canonicalH1Equiv r hr)

theorem degreeOneToCanonicalH1_injective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Injective (degreeOneToCanonicalH1 r hr) :=
  (canonicalH1Equiv r hr).injective.comp
    (degreeOneToProjectiveH1_injective r 0 (root_ne_zero r hr))

/-- The degree-nine residue representative in the actual differential sheaf. -/
def degreeNineCanonicalClass (r : ℂ) (hr : r ^ 3 = 2)
    (p : Poly) (hp : p.IsHomogeneous 9) : DifferentialSheafH1 r 0 :=
  canonicalH1Equiv r hr (degreeNineProjectiveClass r hr p hp)

theorem degreeNineCanonicalClass_eq_zero_iff_trace_zero
    (r : ℂ) (hr : r ^ 3 = 2) (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineCanonicalClass r hr p hp = 0 ↔ traceLinear r p = 0 := by
  have h : degreeNineCanonicalClass r hr p hp = 0 ↔
      degreeNineProjectiveClass r hr p hp = 0 := by
    constructor
    · intro hz
      apply (canonicalH1Equiv r hr).injective
      simpa only [degreeNineCanonicalClass, map_zero] using hz
    · intro hz
      simp only [degreeNineCanonicalClass, hz, map_zero]
  exact h.trans (degreeNineProjectiveClass_eq_zero_iff_trace_zero r hr p hp)

/-- Complex multiples of the fixed normalization numerator, now in H¹(Ω). -/
def normalizedCanonicalClass (r : ℂ) (hr : r ^ 3 = 2) (z : ℂ) :
    DifferentialSheafH1 r 0 :=
  canonicalH1Equiv r hr (normalizedProjectiveClass r hr z)

theorem normalizedCanonicalClass_injective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Injective (normalizedCanonicalClass r hr) :=
  (canonicalH1Equiv r hr).injective.comp (normalizedProjectiveClass_injective r hr)

@[simp] theorem normalizedCanonicalClass_zero (r : ℂ) (hr : r ^ 3 = 2) :
    normalizedCanonicalClass r hr 0 = 0 := by
  simp only [normalizedCanonicalClass, normalizedProjectiveClass_zero, map_zero]

theorem normalizedCanonicalClass_eq_zero_iff (r : ℂ) (hr : r ^ 3 = 2) (z : ℂ) :
    normalizedCanonicalClass r hr z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply normalizedCanonicalClass_injective r hr
    simpa only [normalizedCanonicalClass_zero] using hz
  · rintro rfl
    exact normalizedCanonicalClass_zero r hr

theorem normalizationCanonicalClass_ne_zero (r : ℂ) (hr : r ^ 3 = 2) :
    normalizedCanonicalClass r hr 1 ≠ 0 := by
  intro hz
  exact one_ne_zero ((normalizedCanonicalClass_eq_zero_iff r hr 1).mp hz)

theorem differentialSheafH1_nontrivial (r : ℂ) (hr : r ^ 3 = 2) :
    Nontrivial (DifferentialSheafH1 r 0) :=
  ⟨⟨normalizedCanonicalClass r hr 1, 0, normalizationCanonicalClass_ne_zero r hr⟩⟩

#print axioms canonicalH1Equiv
#print axioms degreeOneToCanonicalH1_injective
#print axioms degreeNineCanonicalClass_eq_zero_iff_trace_zero
#print axioms normalizationCanonicalClass_ne_zero
#print axioms differentialSheafH1_nontrivial

end CycleQ2GeometricProjectiveCanonicalH1
end
