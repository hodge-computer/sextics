import Proposal.GeometricLiteralThreefoldCartanLift
import Proposal.GeometricLiteralThreefoldNativeMixedEdge

/-!
# Localized Cartan contraction equals the native oriented test edge

The intrinsic derivation on the localization and the covector used to
evaluate the native edge agree on each polynomial representative. Thus
inserting the localized derivation after pullback gives exactly the existing
oriented two-form of the two lifts.

Prepared for `fqlx` with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldCartanEdge

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldCartanLift
  CycleQ2LiteralThreefoldNativeMixedEdge CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralThreefoldTestGauge CycleQ2ThreefoldContractionAlongMap
  CycleQ2LiteralThreefoldResidueContraction CycleQ2LiteralThreefoldSurfaceNormal
  CycleQ2ExteriorSectionNaturality

variable {i : Fin 4} {S : Type} [CommRing S] [Algebra ℂ S] [Algebra (T i) S]
  [IsScalarTower ℂ (T i) S] (M : Submonoid (T i)) [IsLocalization M S]

theorem contraction_eq_value (x y : Lift i S) (hx : LiesOver x chartPoint) (hy : LiesOver y chartPoint) :
    interior 2 (localizedTangent M x y hx hy).liftKaehlerDifferential
        (exteriorDifferentialMap chartPoint 3 (orientedVolume i)) =
      value x y (fun a => (hx a).trans (hy a).symm) := by
  rw [value_as_along chartPoint x y hx hy]
  symm
  apply along_from_target
  intro a
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  change liftCovector chartPoint x y hx hy (KaehlerDifferential.D ℂ (T i) (q i p)) = _
  rw [liftCovector_D, Derivation.liftKaehlerDifferential_comp_D]
  exact (localizedTangent_polynomial M x y hx hy p).symm

end CycleQ2LiteralThreefoldCartanEdge

end

#print axioms CycleQ2LiteralThreefoldCartanEdge.contraction_eq_value
