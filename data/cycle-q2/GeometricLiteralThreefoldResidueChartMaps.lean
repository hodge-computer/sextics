import Proposal.GeometricLiteralThreefoldResidueMinors
import Proposal.GeometricLiteralThreefoldResidueCoordinates

/-!
# The two hypersurface chart maps on a fixed-sextic overlap

Both ambient coordinate evaluations descend to the fixed sextic on the
same overlap algebra. The ambient differential of each equation is the
sum of its actual partial derivatives times the restricted coordinate
differentials. The weighted chart change scales this conormal by the
sixth power of the inverse overlap coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldResidueChartMaps

open MvPolynomial CycleQ2LiteralAbelJacobiMovingNormal CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralThreefoldResidueFrame
  CycleQ2LiteralThreefoldResidueCoordinates
open scoped TensorProduct

variable {R : Type} [CommRing R] [Algebra ℂ R]
variable (S : Type) [CommRing S] [Algebra R S]

/-- Polynomial evaluation modulo the original sextic equation, followed by
restriction of coefficients to the overlap algebra. -/
def chartMap (i : Fin 4) (x : Option (Fin 3) → R)
    (hx : algebraMap R S (aeval x (seedF i)) = 0) : T i →+* S :=
  Ideal.Quotient.lift (fixedIdeal i) ((algebraMap R S).comp (aeval x).toRingHom)
    (fun _ hp => ((Ideal.span_singleton_le_iff_mem (RingHom.ker ((algebraMap R S).comp (aeval x).toRingHom))).mpr hx) hp)

@[simp] theorem chartMap_mk (i : Fin 4) (x : Option (Fin 3) → R)
    (hx : algebraMap R S (aeval x (seedF i)) = 0) (p : P) :
    chartMap S i x hx (Ideal.Quotient.mk _ p) = algebraMap R S (aeval x p) := rfl

@[simp] theorem chartMap_coordinate (i : Fin 4) (x : Option (Fin 3) → R)
    (hx : algebraMap R S (aeval x (seedF i)) = 0) (a : Option (Fin 3)) :
    chartMap S i x hx (Ideal.Quotient.mk _ (X a)) = algebraMap R S (x a) := by
  rw [chartMap_mk, aeval_X]

@[simp] theorem chartMap_gradient (i : Fin 4) (x : Option (Fin 3) → R)
    (hx : algebraMap R S (aeval x (seedF i)) = 0) (l : Fin 4) :
    chartMap S i x hx (gradient i l) =
      algebraMap R S (aeval x (pderiv ((_root_.finSuccEquiv 3) l) (seedF i))) := rfl

/-- The same map with its compatibility with the complex coefficients. -/
def chartMapAlgHom [Algebra ℂ S] [IsScalarTower ℂ R S] (i : Fin 4) (x : Option (Fin 3) → R)
    (hx : algebraMap R S (aeval x (seedF i)) = 0) : T i →ₐ[ℂ] S where
  __ := chartMap S i x hx
  commutes' c := by
    change algebraMap R S ((aeval x) (algebraMap ℂ P c)) = algebraMap ℂ S c
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/-- The four ambient differentials restricted to the fixed hypersurface.
These live in the scalar extension of the ambient module. -/
def restrictedDifferentials (x : Option (Fin 3) → R) (l : Fin 4) :
    S ⊗[R] KaehlerDifferential ℂ R :=
  (1 : S) ⊗ₜ[R] KaehlerDifferential.D ℂ R (x ((_root_.finSuccEquiv 3) l))

/-- Passing to the intrinsic cotangent module recovers the differential
of the actual quotient-chart coordinate. -/
theorem map_restrictedDifferentials [Algebra ℂ S] [IsScalarTower ℂ R S] (i : Fin 4)
    (x : Option (Fin 3) → R) (hx : algebraMap R S (aeval x (seedF i)) = 0) (l : Fin 4) :
    KaehlerDifferential.mapBaseChange ℂ R S (restrictedDifferentials S x l) =
      CycleQ2LiteralThreefoldResidueMinors.coordinateForm i (chartMapAlgHom S i x hx) l := by
  rw [restrictedDifferentials, KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  apply congrArg (KaehlerDifferential.D ℂ S)
  exact (chartMap_coordinate S i x hx _).symm

theorem chartConormal_gradient (i : Fin 4) (x : Option (Fin 3) → R)
    (hx : algebraMap R S (aeval x (seedF i)) = 0) :
    (1 : S) ⊗ₜ[R] KaehlerDifferential.D ℂ R (aeval x (seedF i)) =
      ∑ l : Fin 4, chartMap S i x hx (gradient i l) • restrictedDifferentials S x l := by
  rw [CycleQ2LiteralThreefoldResidueMinors.differential_polynomial (aeval x), TensorProduct.tmul_sum]
  rw [← Equiv.sum_comp (_root_.finSuccEquiv 3) (fun j => (1 : S) ⊗ₜ[R]
    ((aeval x (pderiv j (seedF i))) • KaehlerDifferential.D ℂ R (aeval x (X j))))]
  apply Finset.sum_congr rfl
  intro j _
  rw [TensorProduct.tmul_smul, chartMap_gradient]
  simp only [restrictedDifferentials, aeval_X, IsScalarTower.algebraMap_smul]

variable (i : Fin 4) (k : Fin 3) (B : Type) [CommRing B] [Algebra (AmbientOverlap k) B]

/-- Vanishing of the source equation gives vanishing of the target equation
in the very same algebra. -/
theorem targetEquation_zero (hf : algebraMap (AmbientOverlap k) B
    (aeval (overlapCoordinates k) (seedF i)) = 0) :
    algebraMap (AmbientOverlap k) B (aeval
      (changedCoordinate i (i.succAbove k) (overlapCoordinates k) (overlapInverse k))
      (seedF (i.succAbove k))) = 0 := by
  have he := seedF_change i (i.succAbove k) (overlapCoordinates k) (overlapInverse k)
    (by simpa only [Fin.insertNth_apply_succAbove] using overlapInverse_mul k)
  change aeval (changedCoordinate i (i.succAbove k) (overlapCoordinates k) (overlapInverse k))
      (seedF (i.succAbove k)) = (overlapInverse k)^6 * aeval (overlapCoordinates k) (seedF i) at he
  rw [he, map_mul, hf, mul_zero]

/-- The gradient rows in the coordinate orders of the two original affine
charts represent ambient conormals differing by the chart factor. -/
theorem overlap_gradient_change (hf : algebraMap (AmbientOverlap k) B
    (aeval (overlapCoordinates k) (seedF i)) = 0) :
    let j := i.succAbove k
    let x := overlapCoordinates k
    let t := overlapInverse k
    let y := changedCoordinate i j x t
    (∑ l : Fin 4, chartMap B j y (targetEquation_zero i k B hf) (gradient j l) •
      restrictedDifferentials B y l) =
      (algebraMap (AmbientOverlap k) B t)^6 •
        (∑ l : Fin 4, chartMap B i x hf (gradient i l) • restrictedDifferentials B x l) := by
  dsimp only
  rw [← chartConormal_gradient, ← chartConormal_gradient]
  exact conormal_change i (i.succAbove k) (overlapCoordinates k) (overlapInverse k)
    (by simpa only [Fin.insertNth_apply_succAbove] using overlapInverse_mul k)
    _ (CycleQ2GeometricIncidenceProj.pointEquationF_homogeneous _) hf

section FixedOverlap
attribute [local instance] CycleQ2LiteralThreefoldResidueCoordinates.fixedAmbientAlgebra

/-- The localized ambient map respects the original complex scalar actions
on both the projective-coordinate overlap and the hypersurface chart. -/
local instance fixedAmbientTower (i : Fin 4) (k : Fin 3) :
    IsScalarTower ℂ (AmbientOverlap k) (FixedOverlap i k) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap ℂ (FixedOverlap i k) c = ambientToFixed i k (algebraMap ℂ (AmbientOverlap k) c)
    rw [IsScalarTower.algebraMap_apply ℂ P (AmbientOverlap k), ambientToFixed, IsLocalization.Away.lift_eq]
    rfl

local instance sourceFixedAlgebra (i : Fin 4) (k : Fin 3) : Algebra (T i) (FixedOverlap i k) :=
  inferInstanceAs (Algebra (P ⧸ Ideal.span {literalEquation i}) (FixedOverlap i k))

local instance sourceFixedTower (i : Fin 4) (k : Fin 3) : IsScalarTower ℂ (T i) (FixedOverlap i k) :=
  inferInstanceAs (IsScalarTower ℂ (P ⧸ Ideal.span {literalEquation i}) (FixedOverlap i k))

/-- Map from the target hypersurface chart to the original fixed overlap,
using the weighted change of affine coordinates. -/
def fixedTargetMap (i : Fin 4) (k : Fin 3) : T (i.succAbove k) →ₐ[ℂ] FixedOverlap i k :=
  chartMapAlgHom _ (i.succAbove k)
    (changedCoordinate i (i.succAbove k) (overlapCoordinates k) (overlapInverse k))
    (targetEquation_zero i k _ (equation_zero i k))

/-- The source evaluation is exactly the canonical localization map. -/
theorem fixedSourceMap_eq (i : Fin 4) (k : Fin 3) :
    chartMapAlgHom (FixedOverlap i k) i (overlapCoordinates k) (equation_zero i k) =
      IsScalarTower.toAlgHom ℂ (T i) (FixedOverlap i k) := by
  ext z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  have he : aeval (overlapCoordinates k) = IsScalarTower.toAlgHom ℂ P (AmbientOverlap k) := by
    apply MvPolynomial.algHom_ext
    intro l
    rw [aeval_X]
    rfl
  change ambientToFixed i k (aeval (overlapCoordinates k) p) =
    algebraMap (T i) (FixedOverlap i k) (Ideal.Quotient.mk _ p)
  rw [he]
  change ambientToFixed i k (algebraMap P (AmbientOverlap k) p) = _
  rw [ambientToFixed, IsLocalization.Away.lift_eq]
  rfl

end FixedOverlap

end CycleQ2LiteralThreefoldResidueChartMaps
end

#print axioms CycleQ2LiteralThreefoldResidueChartMaps.chartMapAlgHom
#print axioms CycleQ2LiteralThreefoldResidueChartMaps.chartConormal_gradient
#print axioms CycleQ2LiteralThreefoldResidueChartMaps.overlap_gradient_change
#print axioms CycleQ2LiteralThreefoldResidueChartMaps.fixedSourceMap_eq
