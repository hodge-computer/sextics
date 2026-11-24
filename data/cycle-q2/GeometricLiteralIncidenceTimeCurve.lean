import Proposal.GeometricGenericTimeDerivation
import Proposal.GeometricIncidenceFirstOrder

/-!
# The actual pointed parameter curve for the fixed complex threefold

Take the fibre of the smooth relative time curve at the original complex
sextic. The retained dual-number motion factors through this fibre, at its
original seed point, with nonzero time derivative. This realizes the
first-order direction on an algebraic curve in the fixed-sextic locus.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceTimeCurve

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve CycleQ2IncidenceFirstOrder
  CycleQ2IncidenceTraceFamily
open scoped DualNumber

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

def seedSextic : Spec (CommRingCat.of ℂ) ⟶ sexticBase :=
  seedPointMorphism ≫ parameterToSextics

abbrev Curve := pullback seedSextic parameterToSextics

def toComplex : Curve ⟶ Spec (CommRingCat.of ℂ) := pullback.fst _ _
def toIncidence : Curve ⟶ parameterScheme := pullback.snd _ _

theorem smooth_parameter_curve : SmoothOfRelativeDimension 1 toComplex := by
  let _ : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  exact MorphismProperty.pullback_fst _ _ parameterToSextics_smooth_relative_one

def seed : Spec (CommRingCat.of ℂ) ⟶ Curve :=
  pullback.lift (𝟙 _) seedPointMorphism (by simp [seedSextic])

@[simp] theorem seed_to_incidence : seed ≫ toIncidence = seedPointMorphism :=
  pullback.lift_snd _ _ _

theorem curve_nonempty : Nonempty Curve := ⟨seed default⟩

def structureDual : Spec (CommRingCat.of ℂ[ε]) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ[ε]))

theorem firstOrder_constant_sextic :
    firstOrderMap.toRingHom.comp sexticToParameter =
      (algebraMap ℂ ℂ[ε]).comp (seedMap.comp sexticToParameter) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [CycleQ2GenericTimeDerivation.sexticToParameter_C, CycleQ2IncidenceSeedFiber.seedMap_complex]
  · intro j
    change firstOrderMap (sexticToParameter (X j)) =
      algebraMap ℂ ℂ[ε] (seedMap (sexticToParameter (X j)))
    rw [sexticToParameter_X, ← incidence_sextic_fixed j, seedMap_incidencePoint]
    exact firstOrderIncidencePoint_sextic j

private theorem firstOrder_over_sextic :
    structureDual ≫ seedSextic = firstOrderParameterPoint ≫ parameterToSextics := by
  simp only [structureDual, seedSextic, seedPointMorphism, parameterToSextics,
    firstOrderParameterPoint, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact firstOrder_constant_sextic.symm

def timeTangent : Spec (CommRingCat.of ℂ[ε]) ⟶ Curve :=
  pullback.lift structureDual firstOrderParameterPoint firstOrder_over_sextic

@[simp] theorem timeTangent_to_incidence :
    timeTangent ≫ toIncidence = firstOrderParameterPoint := pullback.lift_snd _ _ _

theorem timeTangent_at_seed : firstOrderClosedPoint ≫ timeTangent = seed := by
  apply pullback.hom_ext
  · simp only [Category.assoc, timeTangent, seed, pullback.lift_fst,
      firstOrderClosedPoint, structureDual, ← Spec.map_comp]
    rw [← Spec.map_id]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    rfl
  · simpa only [Category.assoc, timeTangent, seed, pullback.lift_snd] using
      firstOrderParameterPoint_at_seed

theorem timeTangent_nonconstant : timeTangent ≠ structureDual ≫ seed := by
  intro he
  have h := congrArg (fun f => f ≫ toIncidence) he
  change timeTangent ≫ toIncidence = (structureDual ≫ seed) ≫ toIncidence at h
  rw [timeTangent_to_incidence, Category.assoc, seed_to_incidence] at h
  simp only [firstOrderParameterPoint, structureDual, seedPointMorphism, ← Spec.map_comp] at h
  have hx := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_inj.mp h))
    (algebraMap TraceRing ParameterAlgebra traceParameter)
  change firstOrderMap (algebraMap TraceRing ParameterAlgebra traceParameter) =
    algebraMap ℂ ℂ[ε] _ at hx
  rw [firstOrderMap_traceParameter] at hx
  have hs := congrArg TrivSqZeroExt.snd hx
  exact one_ne_zero (show (1 : ℂ) = 0 from hs)

end CycleQ2LiteralIncidenceTimeCurve
end

#print axioms CycleQ2LiteralIncidenceTimeCurve.smooth_parameter_curve
#print axioms CycleQ2LiteralIncidenceTimeCurve.timeTangent_at_seed
#print axioms CycleQ2LiteralIncidenceTimeCurve.timeTangent_nonconstant
