import Proposal.GeometricHodgeEulerContraction
import Proposal.GeometricLiteralThreefoldChartVolume
import Proposal.GeometricLiteralThreefoldLiftTransition
import Mathlib.Algebra.DualNumber

/-!
# Cartan's formula on the gradient charts of the fixed threefold

In a frame of exact coordinate differentials, an exterior two-form has three
signed complementary coefficients. Its exterior derivative is the sum of their
corresponding coordinate derivatives times the ordered three-form. For two
first-order coordinate lifts, the coefficient of the volume is multiplied by
the determinant of their respective dual-number Jacobians. The difference of
these coefficients is the exterior derivative of the contraction by the
difference vector field.

Prepared for `fqlx` with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldCartan

open CycleQ2HodgeEulerContraction CycleQ2LiteralThreefoldResidueContraction
open scoped DualNumber

variable {A : Type} [CommRing A] [Algebra ℂ A]

abbrev OneForms (A : Type) [CommRing A] [Algebra ℂ A] := KaehlerDifferential ℂ A
abbrev Forms (A : Type) [CommRing A] [Algebra ℂ A] (n : ℕ) := ⋀[A]^n (OneForms A)

variable (b : Module.Basis (Fin 3) A (OneForms A))

def coordinateDerivation (i : Fin 3) : Derivation ℂ A A :=
  (b.coord i).compDer (KaehlerDifferential.D ℂ A)

def orderedVolume : Forms A 3 := exteriorPower.ιMulti A 3 b

/-- Exterior differentiation in an exact frame, using the complementary
coordinates of the native exterior square. -/
def exteriorD2 (η : Forms A 2) : Forms A 3 :=
  (∑ i, coordinateDerivation b i (((contractionEquiv b).symm η) (b i))) • orderedVolume b

theorem exteriorD2_signed_basis (i : Fin 3) (f : A) :
    exteriorD2 b (f • interior 2 (b.coord i) (orderedVolume b)) =
      coordinateDerivation b i f • orderedVolume b := by
  unfold exteriorD2 orderedVolume
  rw [← contractionEquiv_apply, map_smul, LinearEquiv.symm_apply_apply]
  simp [LinearMap.smul_apply, Module.Basis.coord_apply, Finsupp.single_apply, apply_ite]

private theorem directional (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i))
    (v : Derivation ℂ A A) (f : A) :
    ∑ i, v (u i) * coordinateDerivation b i f = v f := by
  have h := congrArg v.liftKaehlerDifferential (b.sum_repr (KaehlerDifferential.D ℂ A f))
  simp only [map_sum, map_smul, hu, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul] at h
  change ∑ i, v (u i) * b.repr (KaehlerDifferential.D ℂ A f) i = _
  simpa only [mul_comm] using h

theorem exteriorD2_contraction (u : Fin 3 → A)
    (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i)) (v : Derivation ℂ A A) (f : A) :
    exteriorD2 b (interior 2 v.liftKaehlerDifferential (f • orderedVolume b)) =
      (v f + f * ∑ i, coordinateDerivation b i (v (u i))) • orderedVolume b := by
  unfold exteriorD2
  rw [map_smul, show interior 2 v.liftKaehlerDifferential (orderedVolume b) =
    contractionEquiv b v.liftKaehlerDifferential from (contractionEquiv_apply _ _).symm,
    map_smul, LinearEquiv.symm_apply_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul, hu, Derivation.liftKaehlerDifferential_comp_D,
    Derivation.leibniz, Finset.sum_add_distrib, Finset.mul_sum]
  rw [directional b u hu v f, add_comm]

/-- The Jacobian of three dual coordinates, computed relative to the dual
base so that the parameter ε is constant. Rows index the basis differentials. -/
def jetJacobian (x : Fin 3 → A[ε]) : Matrix (Fin 3) (Fin 3) A[ε] := fun i j =>
  ⟨coordinateDerivation b i (x j).fst, coordinateDerivation b i (x j).snd⟩

private theorem jacobian_entry_fst (u : Fin 3 → A)
    (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i)) (x : Fin 3 → A[ε])
    (hx : ∀ j, (x j).fst = u j) (i j : Fin 3) :
    (jetJacobian b x i j).fst = if j = i then 1 else 0 := by
  change b.repr (KaehlerDifferential.D ℂ A (x j).fst) i = _
  simp [hx, ← hu, Finsupp.single_apply]

omit [Algebra ℂ A] in
private theorem jet_snd_mul (p q : A[ε]) :
    TrivSqZeroExt.snd (p * q) = p.fst * q.snd + p.snd * q.fst := rfl

private theorem jacobian_det (u : Fin 3 → A)
    (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i)) (x : Fin 3 → A[ε])
    (hx : ∀ j, (x j).fst = u j) :
    (jetJacobian b x).det = (⟨1, ∑ i, coordinateDerivation b i (x i).snd⟩ : A[ε]) := by
  have he := jacobian_entry_fst b u hu x hx
  apply TrivSqZeroExt.ext
  · simp [Matrix.det_fin_three, TrivSqZeroExt.fst_mul, he]
  · have hs (i j : Fin 3) :
        (jetJacobian b x i j).snd = coordinateDerivation b i (x j).snd := rfl
    have h01 : (0 : Fin 3) ≠ 1 := by decide
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    have h12 : (1 : Fin 3) ≠ 2 := by decide
    simp [Matrix.det_fin_three, TrivSqZeroExt.fst_mul, he, hs, Fin.sum_univ_three,
      h01, h01.symm, h02, h02.symm, h12, h12.symm]
    ring

/-- Extend a coordinate partial to dual coefficients while keeping ε constant. -/
def jetPartial (i : Fin 3) : Derivation ℂ A[ε] A[ε] where
  toFun x := ⟨coordinateDerivation b i x.fst, coordinateDerivation b i x.snd⟩
  map_add' x y := TrivSqZeroExt.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' c x := TrivSqZeroExt.ext ((coordinateDerivation b i).toLinearMap.map_smul c x.fst)
    ((coordinateDerivation b i).toLinearMap.map_smul c x.snd)
  map_one_eq_zero' := TrivSqZeroExt.ext (coordinateDerivation b i).map_one_eq_zero (map_zero _)
  leibniz' x y := by
    apply TrivSqZeroExt.ext
    · change coordinateDerivation b i (x.fst * y.fst) =
        x.fst * coordinateDerivation b i y.fst + y.fst * coordinateDerivation b i x.fst
      exact (coordinateDerivation b i).leibniz _ _
    · change coordinateDerivation b i (x.fst * y.snd + x.snd * y.fst) =
        x.fst * coordinateDerivation b i y.snd + x.snd * coordinateDerivation b i y.fst +
        (y.fst * coordinateDerivation b i x.snd + y.snd * coordinateDerivation b i x.fst)
      simp only [map_add, Derivation.leibniz, smul_eq_mul]
      ring

/-- The base dual numbers act on both coefficients through the original
complex algebra structure. -/
@[instance_reducible] def dualScalarAlgebra (A : Type) [CommRing A] [Algebra ℂ A] :
    Algebra ℂ[ε] A[ε] :=
  (CycleQ2LiteralThreefoldLiftTransition.jetMap (Algebra.ofId ℂ A)).toRingHom.toAlgebra

attribute [local instance] dualScalarAlgebra

def relativeJetPartial (i : Fin 3) : Derivation ℂ[ε] A[ε] A[ε] where
  toFun := jetPartial b i
  map_add' := map_add _
  map_smul' c z := by
    have hz : jetPartial b i (algebraMap ℂ[ε] A[ε] c) = 0 := by
      apply TrivSqZeroExt.ext
      · change coordinateDerivation b i (algebraMap ℂ A c.fst) = 0
        exact Derivation.map_algebraMap _ _
      · change coordinateDerivation b i (algebraMap ℂ A c.snd) = 0
        exact Derivation.map_algebraMap _ _
    change jetPartial b i (algebraMap ℂ[ε] A[ε] c * z) =
      algebraMap ℂ[ε] A[ε] c * jetPartial b i z
    rw [Derivation.leibniz, hz, smul_zero, add_zero, smul_eq_mul]
  map_one_eq_zero' := (jetPartial b i).map_one_eq_zero
  leibniz' := (jetPartial b i).leibniz

abbrev JetForms (A : Type) [CommRing A] [Algebra ℂ A] (n : ℕ) :=
  ⋀[A[ε]]^n (KaehlerDifferential ℂ[ε] A[ε])

/-- Evaluate an actual Kähler three-form on the three extended coordinate
partials. This computes the relative volume coefficient of a dual point. -/
def evaluateJetVolume : JetForms A 3 →ₗ[A[ε]] A[ε] :=
  exteriorPower.alternatingMapLinearEquiv ((Pi.basisFun A[ε] (Fin 3)).det.compLinearMap
    (LinearMap.pi fun i => (relativeJetPartial b i).liftKaehlerDifferential))

def liftedVolume (c : A[ε]) (x : Fin 3 → A[ε]) : JetForms A 3 :=
  c • exteriorPower.ιMulti A[ε] 3 (fun j => KaehlerDifferential.D ℂ[ε] A[ε] (x j))

theorem evaluate_liftedVolume (c : A[ε]) (x : Fin 3 → A[ε]) :
    evaluateJetVolume b (liftedVolume c x) = c * (jetJacobian b x).det := by
  rw [liftedVolume, map_smul, smul_eq_mul]
  congr 1
  rw [evaluateJetVolume, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply, Module.Basis.det_apply]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  change (relativeJetPartial b i).liftKaehlerDifferential (KaehlerDifferential.D ℂ[ε] A[ε] (x j)) = _
  exact Derivation.liftKaehlerDifferential_comp_D _ _

/-- The scalar first-order top coefficient is the coefficient velocity plus
the trace of the differentiated coordinate velocities times the base coefficient. -/
theorem evaluate_liftedVolume_snd (u : Fin 3 → A)
    (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i)) (c : A[ε]) (x : Fin 3 → A[ε])
    (hx : ∀ j, (x j).fst = u j) :
    (evaluateJetVolume b (liftedVolume c x)).snd =
      c.fst * (∑ i, coordinateDerivation b i (x i).snd) + c.snd := by
  rw [evaluate_liftedVolume, jacobian_det b u hu x hx, jet_snd_mul]
  change c.fst * (∑ i, coordinateDerivation b i (x i).snd) + c.snd * 1 = _
  rw [mul_one]

/-- The infinitesimal coefficient of the pulled-back ordered volume. -/
def volumeVariation (c : A[ε]) (x : Fin 3 → A[ε]) : Forms A 3 :=
  (evaluateJetVolume b (liftedVolume c x)).snd • orderedVolume b

/-- Difference of the first-order determinant pullbacks for two splittings.
The two splittings may be defined on a moving hypersurface: only their
reductions and the differences of their first-order coefficients enter. -/
theorem variation_difference (u : Fin 3 → A)
    (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i))
    (v : Derivation ℂ A A) (c c' : A[ε]) (x y : Fin 3 → A[ε])
    (hc : c.fst = c'.fst) (hx : ∀ i, (x i).fst = u i) (hy : ∀ i, (y i).fst = u i)
    (hv : c.snd - c'.snd = v c.fst) (hxy : ∀ i, (x i).snd - (y i).snd = v (u i)) :
    volumeVariation b c x - volumeVariation b c' y =
      exteriorD2 b (interior 2 v.liftKaehlerDifferential (c.fst • orderedVolume b)) := by
  rw [exteriorD2_contraction b u hu, volumeVariation, volumeVariation,
    evaluate_liftedVolume_snd b u hu c x hx, evaluate_liftedVolume_snd b u hu c' y hy]
  let a : A := c.fst * ∑ i, coordinateDerivation b i (x i).snd
  let a' : A := c'.fst * ∑ i, coordinateDerivation b i (y i).snd
  have he : (a + c.snd) - (a' + c'.snd) =
      v c.fst + c.fst * ∑ i, coordinateDerivation b i (v (u i)) := by
    dsimp only [a, a']
    rw [← hv, ← hc]
    simp_rw [← hxy, map_sub, Finset.sum_sub_distrib]
    ring
  exact (sub_smul (a + c.snd) (a' + c'.snd) (orderedVolume b)).symm.trans
    (congrArg (fun t : A => t • orderedVolume b) he)

section LiteralGradientCharts

open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldResidueFrame
  CycleQ2LiteralThreefoldResidueMinors CycleQ2LiteralThreefoldChartVolume

/-- The three affine coordinates retained by the actual gradient presentation. -/
def patchCoordinate (i j : Fin 4) (k : Fin 3) : Patch i j :=
  algebraMap (T i) (Patch i j) (coord i (j.succAbove k))

def residueCoefficient (i j : Fin 4) : Patch i j :=
  (↑((IsLocalization.Away.algebraMap_isUnit (S := Patch i j) (gradient i j)).unit⁻¹) : Patch i j) *
    (-1) ^ j.val

theorem patchResidue_eq (i j : Fin 4) :
    patchResidue i j = residueCoefficient i j • orderedVolume (basis i j) := by
  rw [patchResidue, CycleQ2LiteralThreefoldResidueMinors.residue, signedOmitted, residueCoefficient, mul_smul]
  congr 2
  change exteriorPower.ιMulti (Patch i j) 3 _ = exteriorPower.ιMulti (Patch i j) 3 _
  apply congrArg (exteriorPower.ιMulti (Patch i j) 3)
  funext k
  exact (basis_apply i j k).symm

/-- Cartan's identity for the actual localized volume of the fixed sextic. -/
theorem patch_volume_variation (i j : Fin 4) (v : Derivation ℂ (Patch i j) (Patch i j))
    (c c' : (Patch i j)[ε]) (x y : Fin 3 → (Patch i j)[ε])
    (hc : c.fst = residueCoefficient i j) (hc' : c'.fst = residueCoefficient i j)
    (hx : ∀ k, (x k).fst = patchCoordinate i j k) (hy : ∀ k, (y k).fst = patchCoordinate i j k)
    (hv : c.snd - c'.snd = v (residueCoefficient i j))
    (hxy : ∀ k, (x k).snd - (y k).snd = v (patchCoordinate i j k)) :
    volumeVariation (basis i j) c x - volumeVariation (basis i j) c' y =
      exteriorD2 (basis i j) (interior 2 v.liftKaehlerDifferential
        (CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap
          (IsScalarTower.toAlgHom ℂ (T i) (Patch i j)) 3 (chartVolume i))) := by
  rw [chartVolume_on_patch, patchResidue_eq, ← hc]
  exact variation_difference _ (patchCoordinate i j) (basis_apply i j) v c c' x y
    (hc.trans hc'.symm) hx hy (hc.symm ▸ hv) hxy

end LiteralGradientCharts

end CycleQ2LiteralThreefoldCartan

end

#print axioms CycleQ2LiteralThreefoldCartan.exteriorD2_signed_basis
#print axioms CycleQ2LiteralThreefoldCartan.variation_difference

#print axioms CycleQ2LiteralThreefoldCartan.patch_volume_variation
