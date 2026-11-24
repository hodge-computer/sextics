import Proposal.GeometricLiteralProjectiveDeformationCover
import Proposal.GeometricDualNumberFlatness
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The original projective deformation is flat over the dual-number base

The actual degree-zero epsilon defines the dual-number coefficient map.
On every one of the twelve original native charts, its annihilator is
its principal ideal, by the already proved original kernel identities.
The dual-number flatness criterion therefore proves genuine flatness of
each chart ring and hence of the actual projective structure morphism.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveDualFamily

open scoped DualNumber
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
  CycleQ2LiteralGradedDeformation CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveKernel CycleQ2LiteralProjectiveDeformationCover

def zeroEpsilon : deformationGrade 0 := ⟨epsilonElement,epsilonElement_mem_grade⟩

theorem zeroEpsilon_square : zeroEpsilon * zeroEpsilon = 0 :=
  Subtype.ext epsilonElement_square

/-- Both the complex coefficients and epsilon are the actual degree-zero
coefficients of the original graded presentation. -/
def dualCoefficient : ℂ[ε] →ₐ[ℂ] deformationGrade 0 :=
  TrivSqZeroExt.lift (Algebra.ofId ℂ (deformationGrade 0))
    (zeroEpsilon • (Algebra.ofId ℂ (deformationGrade 0)).toLinearMap)
    (by
      intro x y
      change (zeroEpsilon * algebraMap ℂ (deformationGrade 0) x) *
        (zeroEpsilon * algebraMap ℂ (deformationGrade 0) y) = 0
      calc
        _ = (zeroEpsilon * zeroEpsilon) *
            (algebraMap ℂ (deformationGrade 0) x * algebraMap ℂ (deformationGrade 0) y) := by ring
        _ = 0 := by rw [zeroEpsilon_square, zero_mul])
    (by
      intro x y
      change zeroEpsilon * algebraMap ℂ (deformationGrade 0) (x * y) =
        algebraMap ℂ (deformationGrade 0) x * (zeroEpsilon * algebraMap ℂ (deformationGrade 0) y)
      rw [map_mul]
      ring)
    (by
      intro x y
      change zeroEpsilon * algebraMap ℂ (deformationGrade 0) (y * x) =
        (zeroEpsilon * algebraMap ℂ (deformationGrade 0) y) * algebraMap ℂ (deformationGrade 0) x
      rw [map_mul]
      ring)

theorem dualCoefficient_apply (z : ℂ[ε]) :
    dualCoefficient z = algebraMap ℂ (deformationGrade 0) z.fst +
      zeroEpsilon * algebraMap ℂ (deformationGrade 0) z.snd := rfl

theorem dualCoefficient_epsilon : dualCoefficient (ε : ℂ[ε]) = zeroEpsilon := by
  rw [dualCoefficient_apply]
  simp only [DualNumber.fst_eps, DualNumber.snd_eps, map_zero, map_one, mul_one, zero_add]

def chartDualCoefficient (a : Fin 4) (l : Fin 3) : ℂ[ε] →+* ChartRing a l :=
  (fromZeroRingHom deformationGrade (Submonoid.powers (chartDenominator a l))).comp
    dualCoefficient.toRingHom

theorem chartDualCoefficient_epsilon (a : Fin 4) (l : Fin 3) :
    chartDualCoefficient a l (ε : ℂ[ε]) = chartEpsilon a l := by
  change fromZeroRingHom deformationGrade _ (dualCoefficient (ε : ℂ[ε])) = _
  rw [dualCoefficient_epsilon]
  rfl

local instance chartDualAlgebra (a : Fin 4) (l : Fin 3) : Algebra ℂ[ε] (ChartRing a l) :=
  (chartDualCoefficient a l).toAlgebra

/-- The faithful epsilon condition is proved for this original chart;
there is no supplied flatness hypothesis. -/
theorem chart_flat (a : Fin 4) (l : Fin 3) : Module.Flat ℂ[ε] (ChartRing a l) := by
  apply CycleQ2DualNumberFlatness.flat_of_eps_smul
  intro x hx
  change chartDualCoefficient a l (ε : ℂ[ε]) * x = 0 at hx
  rw [chartDualCoefficient_epsilon] at hx
  have hk : x ∈ Ideal.span ({chartEpsilon a l} : Set (ChartRing a l)) := by
    rw [← chartKernel_principal]
    exact (chartEpsilon_mul_eq_zero_iff a l x).mp hx
  obtain ⟨y,hy⟩ := Ideal.mem_span_singleton'.mp hk
  refine ⟨y, ?_⟩
  change x = chartDualCoefficient a l (ε : ℂ[ε]) * y
  rw [chartDualCoefficient_epsilon, mul_comm]
  exact hy.symm

/-- The actual original epsilon parameter on the whole projectivization. -/
def firstOrderStructure : projectiveDeformation ⟶ Spec (CommRingCat.of ℂ[ε]) :=
  Proj.toSpecZero deformationGrade ≫ Spec.map (CommRingCat.ofHom dualCoefficient.toRingHom)

/-- Forgetting the original epsilon parameter gives precisely the
already constructed complex structure morphism of this same scheme. -/
theorem firstOrderStructure_overComplex :
    firstOrderStructure ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ ℂ[ε])) =
      CycleQ2LiteralProjectiveComplexSplittings.deformationToComplex := by
  have hc : CommRingCat.ofHom (algebraMap ℂ ℂ[ε]) ≫ CommRingCat.ofHom dualCoefficient.toRingHom =
      CommRingCat.ofHom (algebraMap ℂ (deformationGrade 0)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    exact dualCoefficient.commutes c
  rw [firstOrderStructure, Category.assoc, ← Spec.map_comp, hc]
  rfl

@[reassoc] theorem chart_firstOrderStructure (a : Fin 4) (l : Fin 3) :
    Proj.awayι deformationGrade (chartDenominator a l) (chartDenominator_homogeneous a l)
        (by omega) ≫ firstOrderStructure = Spec.map (CommRingCat.ofHom (chartDualCoefficient a l)) := by
  rw [firstOrderStructure, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

theorem chartSpec_flat (a : Fin 4) (l : Fin 3) :
    AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom (chartDualCoefficient a l))) := by
  apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Flat)).mpr
  exact RingHom.flat_algebraMap_iff.mpr (chart_flat a l)

theorem chartOpen_flat (a : Fin 4) (l : Fin 3) :
    AlgebraicGeometry.Flat ((chartOpen a l).ι ≫ firstOrderStructure) := by
  apply (MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.Flat)
    (Proj.basicOpenIsoSpec deformationGrade (chartDenominator a l)
      (chartDenominator_homogeneous a l) (by omega)).inv
    ((chartOpen a l).ι ≫ firstOrderStructure)).mp
  change AlgebraicGeometry.Flat (Proj.awayι deformationGrade (chartDenominator a l)
    (chartDenominator_homogeneous a l) (by omega) ≫ firstOrderStructure)
  rw [chart_firstOrderStructure]
  exact chartSpec_flat a l

/-- Flatness is established on the proved twelve-chart atlas of the
actual scheme with its original epsilon parameter. -/
theorem firstOrderStructure_flat : AlgebraicGeometry.Flat firstOrderStructure :=
  IsZariskiLocalAtSource.of_iSup_eq_top (P := @AlgebraicGeometry.Flat)
    (fun i : Fin 4 × Fin 3 => chartOpen i.1 i.2)
    (by simpa only [iSup_prod] using deformation_chartOpen_cover)
    (fun i => chartOpen_flat i.1 i.2)

end CycleQ2LiteralProjectiveDualFamily

end

#print axioms CycleQ2LiteralProjectiveDualFamily.chartDualCoefficient_epsilon
#print axioms CycleQ2LiteralProjectiveDualFamily.chart_flat
#print axioms CycleQ2LiteralProjectiveDualFamily.firstOrderStructure_overComplex
#print axioms CycleQ2LiteralProjectiveDualFamily.firstOrderStructure_flat
