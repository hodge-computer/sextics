import Proposal.GeometricHodgeCotangentEulerSheaf
import Proposal.GeometricHodgeCotangentEulerTransition
import Proposal.GeometricTwistedDifferential
import Proposal.GeometricAffineChartSections

/-!
# Ordinary cotangent forms from the actual Euler kernel

On every subopen of a weight-one chart, a section of the actual negative
twist kernel gives a sum of ordinary coordinate differentials. On common
subopens these Kähler forms agree before sheafification. The formulas
commute with the original restriction maps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentAtlasForms

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricHodgeThreefold
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2HodgeCotangentEulerSheaf (ambient coefficient pieceMap coefficient_radial_zero)
open CycleQ2GeometricSectionDifferentials
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricAffineOverlap (differentialMap differentialMap_D differentialMap_smul)
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)

variable (φ : CoeffRing →+* ℂ)

@[instance_reducible] def complexOn (V : (threefold φ).Opens) :
    Algebra ℂ Γ(threefold φ,V) :=
  sectionAlgebra (threefold φ).sheaf (schemeCoefficient (toBase φ)) V

attribute [local instance] complexOn

abbrev Form (V : (threefold φ).Opens) :=
  KaehlerDifferential ℂ Γ(threefold φ,V)

abbrev coordinate (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (j : Fin 5) :=
  normalized φ i (coord φ j) (coord_mem_grade φ j) V hi

def nativeForm (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (a : Γ(ambient φ,V)) : Form φ V := by
  letI : Algebra ℂ Γ(threefold φ,V) :=
    sectionAlgebra (threefold φ).sheaf (schemeCoefficient (toBase φ)) V
  exact ∑ j : Fin 5, coefficient φ i V hi a j • KaehlerDifferential.D ℂ Γ(threefold φ,V)
    (coordinate φ i V hi j)

theorem transition_reverse (i k : Fin 4) (V : (threefold φ).Opens)
    (hi : V ≤ U φ i) (hk : V ≤ U φ k) :
    transition φ i k V hi hk = (transition φ k i V hk hi)⁻¹ :=
  eq_inv_of_mul_eq_one_left ((transition_comp φ i k i V hi hk hi).trans (transition_self φ i V hi))

theorem coordinate_change (i k : Fin 4) (V : (threefold φ).Opens)
    (hi : V ≤ U φ i) (hk : V ≤ U φ k) (j : Fin 5) :
    coordinate φ i V hi j =
      ((↑((transition φ k i V hk hi)⁻¹) : Γ(threefold φ,V)) ^ geometricWeight j) *
        coordinate φ k V hk j := by
  have hc := normalized_change φ i k (coord φ j) (coord_mem_grade φ j) V hi hk
  change coordinate φ i V hi j =
    ((transition φ i k V hi hk : Γ(threefold φ,V)) ^ geometricWeight j) * coordinate φ k V hk j at hc
  rw [transition_reverse] at hc
  exact hc

theorem coefficient_change (i k : Fin 4) (V : (threefold φ).Opens)
    (hi : V ≤ U φ i) (hk : V ≤ U φ k) (a : Γ(ambient φ,V)) (j : Fin 5) :
    coefficient φ i V hi a j = (transition φ k i V hk hi : Γ(threefold φ,V)) ^ geometricWeight j *
      coefficient φ k V hk a j := by
  have hc := chartFrame_transition φ (-(geometricWeight j : ℤ)) i k V hi hk ((pieceMap φ j).app V a)
  change coefficient φ i V hi a j =
    (transition φ i k V hi hk ^ (-(geometricWeight j : ℤ)) : Γ(threefold φ,V)ˣ).val *
      coefficient φ k V hk a j at hc
  rw [transition_reverse] at hc
  simpa only [inv_zpow,zpow_neg,zpow_natCast,inv_pow,inv_inv,Units.val_pow_eq_pow_val] using hc

/-- The actual ordinary Kähler form is anchor-independent on each common open. -/
theorem nativeForm_change (i k : Fin 4) (V : (threefold φ).Opens)
    (hi : V ≤ U φ i) (hk : V ≤ U φ k) (a : Γ(ambient φ,V)) :
    nativeForm φ i V hi a = nativeForm φ k V hk a := by
  letI : Algebra ℂ Γ(threefold φ,V) :=
    sectionAlgebra (threefold φ).sheaf (schemeCoefficient (toBase φ)) V
  have hz : (∑ j : Fin 5, (geometricWeight j : Γ(threefold φ,V)) *
      coefficient φ k V hk a j * coordinate φ k V hk j) = 0 := by
    calc
      _ = ∑ j : Fin 5, (geometricWeight j : Γ(threefold φ,V)) *
          coordinate φ k V hk j * coefficient φ k V hk a j := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := coefficient_radial_zero φ k V hk a
  have he := CycleQ2HodgeCotangentEulerTransition.original_weights
    (KaehlerDifferential.D ℂ Γ(threefold φ,V)) (transition φ k i V hk hi)
    (coordinate φ k V hk) (coefficient φ k V hk a) hz
  unfold nativeForm
  simp_rw [coordinate_change φ i k V hi hk,coefficient_change φ i k V hi hk]
  exact he

theorem coefficient_restrict (i : Fin 4) {V W : (threefold φ).Opens}
    (hi : V ≤ U φ i) (hW : W ≤ V) (a : Γ(ambient φ,V)) (j : Fin 5) :
    coefficient φ i W (hW.trans hi) (moduleRes (ambient φ) hW a) j =
      (threefold φ).presheaf.map (homOfLE hW).op (coefficient φ i V hi a j) := by
  unfold CycleQ2HodgeCotangentEulerSheaf.coefficient
  rw [← moduleRes_app]
  exact CycleQ2HodgeAtlasLine.coordinate_restrict (cocycle φ (-(geometricWeight j : ℤ))) i hi hW _

theorem coefficient_add (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (a b : Γ(ambient φ,V)) (j : Fin 5) :
    coefficient φ i V hi (a+b) j = coefficient φ i V hi a j + coefficient φ i V hi b j := by
  unfold CycleQ2HodgeCotangentEulerSheaf.coefficient
  rw [map_add,map_add]

theorem coefficient_smul (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (c : Γ(threefold φ,V)) (a : Γ(ambient φ,V)) (j : Fin 5) :
    coefficient φ i V hi (c • a) j = c * coefficient φ i V hi a j := by
  unfold CycleQ2HodgeCotangentEulerSheaf.coefficient
  rw [Scheme.Modules.Hom.app_smul,map_smul]
  rfl

theorem nativeForm_add (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (a b : Γ(ambient φ,V)) :
    nativeForm φ i V hi (a+b) = nativeForm φ i V hi a + nativeForm φ i V hi b := by
  unfold nativeForm
  simp only [coefficient_add,add_smul,Finset.sum_add_distrib]

theorem nativeForm_smul (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (c : Γ(threefold φ,V)) (a : Γ(ambient φ,V)) :
    nativeForm φ i V hi (c • a) = c • nativeForm φ i V hi a := by
  unfold nativeForm
  simp only [coefficient_smul,mul_smul,Finset.smul_sum]

abbrev Cotangent : (threefold φ).Modules := CycleQ2GeometricDifferentialSheaf.differentialSheaf
  (threefold φ).sheaf (schemeCoefficient (toBase φ))

abbrev D := CycleQ2GeometricDifferentialSheaf.universalDifferential
  (threefold φ).sheaf (schemeCoefficient (toBase φ))

def localForm (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (a : Γ(ambient φ,V)) : Γ(Cotangent φ,V) :=
  ∑ j : Fin 5, coefficient φ i V hi a j • (D φ).d (X := op V) (coordinate φ i V hi j)

theorem localForm_eq_toSheaf (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (a : Γ(ambient φ,V)) :
    localForm φ i V hi a = toSheaf (threefold φ).sheaf (schemeCoefficient (toBase φ)) V
      (nativeForm φ i V hi a) := by
  unfold localForm nativeForm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact ((toSheaf (threefold φ).sheaf (schemeCoefficient (toBase φ)) V).map_smul
    (coefficient φ i V hi a j) (KaehlerDifferential.D ℂ Γ(threefold φ,V)
      (coordinate φ i V hi j))).symm

/-- The ordinary anchor identity gives equality in the actual differential sheaf. -/
theorem localForm_change (i k : Fin 4) (V : (threefold φ).Opens)
    (hi : V ≤ U φ i) (hk : V ≤ U φ k) (a : Γ(ambient φ,V)) :
    localForm φ i V hi a = localForm φ k V hk a := by
  rw [localForm_eq_toSheaf,localForm_eq_toSheaf,nativeForm_change φ i k V hi hk]

theorem localForm_add (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (a b : Γ(ambient φ,V)) :
    localForm φ i V hi (a+b) = localForm φ i V hi a + localForm φ i V hi b := by
  unfold localForm
  simp only [coefficient_add,add_smul,Finset.sum_add_distrib]

theorem localForm_smul (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (c : Γ(threefold φ,V)) (a : Γ(ambient φ,V)) :
    localForm φ i V hi (c • a) = c • localForm φ i V hi a := by
  unfold localForm
  simp only [coefficient_smul,mul_smul,Finset.smul_sum]

/-- Actual sheaf restriction agrees with the local differential formula. -/
theorem localForm_restrict (i : Fin 4) {V W : (threefold φ).Opens}
    (hi : V ≤ U φ i) (hW : W ≤ V) (a : Γ(ambient φ,V)) :
    moduleRes (Cotangent φ) hW (localForm φ i V hi a) =
      localForm φ i W (hW.trans hi) (moduleRes (ambient φ) hW a) := by
  unfold localForm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (Cotangent φ).val.map (homOfLE hW).op
    (coefficient φ i V hi a j • (D φ).d (coordinate φ i V hi j)) = _
  rw [PresheafOfModules.map_smul]
  change (threefold φ).presheaf.map (homOfLE hW).op (coefficient φ i V hi a j) •
    (Cotangent φ).val.map (homOfLE hW).op ((D φ).d (coordinate φ i V hi j)) = _
  rw [← coefficient_restrict]
  have hc := normalized_restrict φ i (coord φ j) (coord_mem_grade φ j) hi hW
  have hd := (D φ).d_map (homOfLE hW).op (coordinate φ i V hi j)
  exact congrArg (fun x => coefficient φ i W (hW.trans hi) (moduleRes (ambient φ) hW a) j • x)
    (hd.symm.trans (congrArg ((D φ).d (X := op W)) hc))

end CycleQ2HodgeCotangentAtlasForms
end

#print axioms CycleQ2HodgeCotangentAtlasForms.nativeForm_change
#print axioms CycleQ2HodgeCotangentAtlasForms.localForm_change
#print axioms CycleQ2HodgeCotangentAtlasForms.localForm_restrict
