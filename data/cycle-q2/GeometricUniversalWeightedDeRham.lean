import Proposal.GeometricUniversalWeightedClosure
import Proposal.GeometricTarget01Part01
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Derivation.Lie
import Proposal.GeometricExteriorSheaf
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Relative exterior forms on the universal weighted function field

The coefficient field is the fraction field of the 44 parameter
coefficients. The three free coordinate derivations give a dual frame
for the genuine relative Kähler cotangent space. In this frame the
protected source density gives the universal rational three-form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2WeightedCoordinateExterior

open scoped BigOperators

private def omittedIndex (i : Fin 3) : Set.powersetCard (Fin 3) 2 :=
  ⟨{i}ᶜ, by simp [Finset.card_compl]⟩

private def omittedEquiv : Fin 3 ≃ Set.powersetCard (Fin 3) 2 := Equiv.ofBijective omittedIndex (by
  constructor
  · intro i j hij
    have h := congrArg (fun s : Set.powersetCard (Fin 3) 2 => (s : Finset (Fin 3))ᶜ) hij
    simpa only [omittedIndex, compl_compl, Finset.singleton_inj] using h
  · intro s
    have hc : ((s : Finset (Fin 3))ᶜ).card = 1 := by simp [Finset.card_compl]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    refine ⟨i, Subtype.ext ?_⟩
    change {i}ᶜ = (s : Finset (Fin 3))
    rw [← hi, compl_compl])

section Coordinates

variable {L W : Type*} [CommRing L] [CommRing W] [Algebra L W]

abbrev Form (L W : Type*) [CommRing L] [CommRing W] [Algebra L W] (p : ℕ) := ⋀[W]^p Ω[W⁄L]

variable (B : Module.Basis (Fin 3) W Ω[W⁄L]) (D : Fin 3 → Derivation L W W)

/-- The two-form basis indexed by the omitted coordinate in the ordered volume. -/
def twoBasis : Module.Basis (Fin 3) W (Form L W 2) :=
  (B.exteriorPower 2).reindex omittedEquiv.symm

private theorem twoBasis_apply (i : Fin 3) :
    twoBasis B i = exteriorPower.ιMulti W 2 (i.removeNth B) := by
  rw [twoBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change B.exteriorPower 2 (omittedIndex i) = _
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  simp only [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply, omittedIndex,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb, Fin.removeNth]
  rfl

private theorem twoBasis_repr_wedge (u : Fin 2 → Ω[W⁄L]) (i : Fin 3) :
    (twoBasis B).repr (exteriorPower.ιMulti W 2 u) i =
      (Matrix.of fun j k => B.repr (u j) (i.succAbove k)).det := by
  rw [twoBasis, Module.Basis.repr_reindex_apply, Equiv.symm_symm]
  change (B.exteriorPower 2).repr _ (omittedIndex i) = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  simp only [Set.powersetCard.ofFinEmbEquiv_symm_apply, omittedIndex,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb, Module.Basis.coord_apply]
  rfl

/-- The ordered coordinate volume. -/
def volume : Form L W 3 := exteriorPower.ιMulti W 3 B

private def topIndex : Set.powersetCard (Fin 3) 3 := ⟨Finset.univ, by simp⟩

private theorem topIndex_unique (s : Set.powersetCard (Fin 3) 3) : s = topIndex := by
  apply Subtype.ext
  exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp)

private theorem top_order (j : Fin 3) : Set.powersetCard.ofFinEmbEquiv.symm topIndex j = j := by
  have h : (fun i : Fin 3 => i) = (Finset.univ : Finset (Fin 3)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique _ (fun _ => Finset.mem_univ _) strictMono_id
  exact (congrFun h j).symm

private theorem topBasis_apply : B.exteriorPower 3 topIndex = volume B := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family volume
  congr 1
  funext j
  simp only [Function.comp_apply, top_order]

private def volumeCoefficient : Form L W 3 →ₗ[W] W := (B.exteriorPower 3).coord topIndex

private theorem volumeCoefficient_volume : volumeCoefficient B (volume B) = 1 := by
  rw [← topBasis_apply]
  simp [volumeCoefficient]

private theorem wedge_three (u : Fin 3 → Ω[W⁄L]) :
    exteriorPower.ιMulti W 3 u = (Matrix.of fun j k => B.repr (u j) k).det • volume B := by
  calc
    _ = ∑ s, (B.exteriorPower 3).repr (exteriorPower.ιMulti W 3 u) s • (B.exteriorPower 3) s :=
      ((B.exteriorPower 3).sum_repr _).symm
    _ = _ := by
      rw [Finset.sum_eq_single topIndex]
      · rw [topBasis_apply, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
        simp only [top_order, Module.Basis.coord_apply]
      · intro i _ hi
        exact (hi (topIndex_unique i)).elim
      · simp

/-- Exterior differentiation from degree two to degree three in the exact coordinate basis. -/
def exteriorD2 : Form L W 2 →ₗ[L] Form L W 3 :=
  ∑ i : Fin 3,
    ((LinearMap.toSpanSingleton W _ ((-1 : W) ^ i.val • volume B)).restrictScalars L).comp
      ((D i).toLinearMap.comp (((twoBasis B).coord i).restrictScalars L))

private theorem exteriorD2_apply (η : Form L W 2) :
    exteriorD2 B D η = (∑ i, (-1 : W) ^ i.val * D i ((twoBasis B).repr η i)) • volume B := by
  simp only [exteriorD2, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply, Module.Basis.coord_apply,
    Derivation.coeFn_coe, smul_smul, ← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The sign includes the position of the omitted coordinate. -/
def signedCoefficients (η : Form L W 2) (i : Fin 3) : W :=
  (-1 : W) ^ i.val * (twoBasis B).repr η i

theorem exteriorD2_divergence (η : Form L W 2) :
    exteriorD2 B D η = (∑ i, D i (signedCoefficients B η i)) • volume B := by
  rw [exteriorD2_apply]
  simp only [signedCoefficients, Derivation.leibniz, Derivation.leibniz_pow, map_neg,
    Derivation.map_one_eq_zero, neg_zero, smul_eq_mul, mul_zero, smul_zero, add_zero]

theorem exact_volume_iff_divergence (ρ : W) :
    (∃ η : Form L W 2, exteriorD2 B D η = ρ • volume B) ↔ ∃ v : Fin 3 → W, ∑ i, D i (v i) = ρ := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨signedCoefficients B η, ?_⟩
    have h := congrArg (volumeCoefficient B) hη
    simpa only [exteriorD2_divergence, map_smul, volumeCoefficient_volume, smul_eq_mul, mul_one] using h
  · rintro ⟨v, hv⟩
    let η := (twoBasis B).equivFun.symm (fun i => (-1 : W) ^ i.val * v i)
    refine ⟨η, ?_⟩
    have he (i : Fin 3) : signedCoefficients B η i = v i := by
      have hrepr : (twoBasis B).repr η i = (-1 : W) ^ i.val * v i :=
        Module.Basis.coord_equivFun_symm (twoBasis B) i _
      rw [signedCoefficients, hrepr, ← mul_assoc, ← pow_add, show i.val + i.val = 2 * i.val by omega, pow_mul]
      simp
    simp only [exteriorD2_divergence, he, hv]

/-- The derivative of a scalar times the signed minor vector is the
Jacobian determinant. The mixed second-derivative terms cancel in pairs. -/
private theorem divergence_minors {L W : Type*} [CommRing L] [CommRing W] [Algebra L W]
    (D : Fin 3 → Derivation L W W) (hD : ∀ i j, Function.Commute (D i) (D j)) (a b c : W) :
    (∑ i : Fin 3, (-1 : W) ^ i.val *
      D i (a * (Matrix.of fun s t : Fin 2 => D (i.succAbove t) (![b, c] s)).det)) =
      (Matrix.of fun s t : Fin 3 => D t (![a, b, c] s)).det := by
  rw [Fin.sum_univ_three, Matrix.det_fin_three]
  simp only [Matrix.det_fin_two, Matrix.of_apply]
  change (-1 : W) ^ 0 *
        D 0 (a * (D 1 b * D 2 c - D 2 b * D 1 c)) +
      (-1 : W) ^ 1 * D 1 (a * (D 0 b * D 2 c - D 2 b * D 0 c)) +
      (-1 : W) ^ 2 * D 2 (a * (D 0 b * D 1 c - D 1 b * D 0 c)) =
      D 0 a * D 1 b * D 2 c - D 0 a * D 2 b * D 1 c -
      D 1 a * D 0 b * D 2 c + D 1 a * D 2 b * D 0 c +
      D 2 a * D 0 b * D 1 c - D 2 a * D 1 b * D 0 c
  simp only [map_sub, Derivation.leibniz, smul_eq_mul]
  rw [hD 1 0 b, hD 1 0 c, hD 2 0 b, hD 2 0 c, hD 2 1 b, hD 2 1 c]
  ring

/-- The exterior differential takes a scalar times a wedge of two exact forms
to the wedge of the three corresponding Kähler differentials. -/
theorem exteriorD2_smul_exact_pair
    (hB : ∀ x i, B.repr (KaehlerDifferential.D L W x) i = D i x)
    (hD : ∀ i j, Function.Commute (D i) (D j)) (a b c : W) :
    exteriorD2 B D (a • exteriorPower.ιMulti W 2 (KaehlerDifferential.D L W ∘ ![b,c])) =
      exteriorPower.ιMulti W 3 (KaehlerDifferential.D L W ∘ ![a,b,c]) := by
  rw [exteriorD2_apply, wedge_three B]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, twoBasis_repr_wedge, Function.comp_apply,
    hB]
  rw [divergence_minors D hD]

/-- The dual derivations of an exact Kähler frame over any ground ring. -/
def exactFrameDirection (i : Fin 3) : Derivation L W W :=
  (KaehlerDifferential.linearMapEquivDerivation L W) (B.coord i)

theorem exactFrameDirection_apply (x : W) (i : Fin 3) :
    exactFrameDirection B i x = B.repr (KaehlerDifferential.D L W x) i := rfl

theorem exactFrameDirections_commute (u : Fin 3 → W)
    (hu : ∀ i, B i = KaehlerDifferential.D L W (u i)) (i j : Fin 3) :
    Function.Commute (exactFrameDirection B i) (exactFrameDirection B j) := by
  intro f
  let δ := ⁅exactFrameDirection B i, exactFrameDirection B j⁆
  have hδ : δ.liftKaehlerDifferential = 0 := by
    apply B.ext
    intro k
    rw [hu, Derivation.liftKaehlerDifferential_comp_D]
    have he (m n : Fin 3) : exactFrameDirection B m (u n) = if n = m then 1 else 0 := by
      rw [exactFrameDirection_apply, ← hu, Module.Basis.repr_self, Finsupp.single_apply]
    simp only [δ, Derivation.commutator_apply, he, LinearMap.zero_apply]
    split <;> split <;> simp
  apply sub_eq_zero.mp
  change δ f = 0
  rw [← Derivation.liftKaehlerDifferential_comp_D δ, hδ]
  rfl

theorem exteriorD2_exactFrame (u : Fin 3 → W)
    (hu : ∀ i, B i = KaehlerDifferential.D L W (u i)) (a b c : W) :
    exteriorD2 B (exactFrameDirection B) (a • exteriorPower.ιMulti W 2 (KaehlerDifferential.D L W ∘ ![b,c])) =
      exteriorPower.ιMulti W 3 (KaehlerDifferential.D L W ∘ ![a,b,c]) :=
  exteriorD2_smul_exact_pair B (exactFrameDirection B) (fun x i => (exactFrameDirection_apply B x i).symm)
    (exactFrameDirections_commute B u hu) a b c

/-- The top form on a rank-three exact frame is a single scalar
multiple of the ordered volume. -/
theorem topForm_scalar (ω : Form L W 3) :
    ∃ r : W, ω = r • volume B := by
  refine ⟨(B.exteriorPower 3).repr ω topIndex, ?_⟩
  calc
    _ = ∑ s, (B.exteriorPower 3).repr ω s • (B.exteriorPower 3) s :=
      ((B.exteriorPower 3).sum_repr ω).symm
    _ = _ := by
      rw [Finset.sum_eq_single topIndex]
      · rw [topBasis_apply]
      · intro s _ hs
        exact (hs (topIndex_unique s)).elim
      · simp

/-- A fixed exact frame generates all two-forms by scalar multiples
of pairs of exact differentials. Equality on those generators suffices
for equality of the additive maps. -/
theorem twoFormMap_ext {N : Type*} [AddCommMonoid N] (u : Fin 3 → W)
    (hu : ∀ i, B i = KaehlerDifferential.D L W (u i))
    (f g : Form L W 2 →+ N)
    (h : ∀ a b c : W,
      f (a • exteriorPower.ιMulti W 2 (KaehlerDifferential.D L W ∘ ![b,c])) =
      g (a • exteriorPower.ιMulti W 2 (KaehlerDifferential.D L W ∘ ![b,c]))) :
    f = g := by
  apply AddMonoidHom.ext
  intro η
  rw [← (twoBasis B).sum_repr η, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.removeNth B = KaehlerDifferential.D L W ∘ ![u (j.succAbove 0), u (j.succAbove 1)] := by
    funext i
    fin_cases i <;> apply hu
  rw [twoBasis_apply, hj]
  apply h

end Coordinates

end CycleQ2WeightedCoordinateExterior

namespace CycleQ2UniversalWeightedDeRham

open MvPolynomial
open CycleQ2MonicWeightedAffineEquation CycleQ2GenericWeightedSpatialDenominator
open CycleQ2MonicWeightedPrimitiveSpecialization
open CycleQ2UniversalWeightedTransfer CycleQ2WeightedCoordinateExterior
open CycleQ2MonicWeightedPrimitiveIdentity (Pol normal density)
open scoped BigOperators

abbrev K := FractionRing Coeff
abbrev W := Fld universalAffine

local instance intAlgebra : Algebra ℤ W := Ring.toIntAlgebra W

private abbrev v := fieldValue universalAffine
private abbrev F := universalAffine
private abbrev d := direction universalAffine universal_normal_ne_zero

private def coefficientValue : Coeff →+* W := v.comp MvPolynomial.C

private theorem coefficientValue_injective : Function.Injective coefficientValue := by
  have hdeg : (separate F).degree ≠ 0 := by
    rw [separate_universal]
    intro h
    have hz := Polynomial.natDegree_eq_of_degree_eq_some h
    have h3 : universalEquation.natDegree = 3 := CycleQ2MonicWeightedAffineEquation.natDegree _
    rw [h3] at hz
    exact (by decide : (3 : ℕ) ≠ 0) hz
  have inj :
      Function.Injective ((algebraMap (ChartRing F) W).comp
        ((AdjoinRoot.of (separate F)).comp (MvPolynomial.C : Coeff →+* Coords Coeff))) :=
    (IsFractionRing.injective (ChartRing F) W).comp
      ((AdjoinRoot.of.injective_of_degree_ne_zero hdeg).comp (MvPolynomial.C_injective (Fin 3) Coeff))
  have hEq : coefficientValue = (algebraMap (ChartRing F) W).comp
      ((AdjoinRoot.of (separate F)).comp (MvPolynomial.C : Coeff →+* Coords Coeff)) := by
    apply RingHom.ext
    intro c
    change algebraMap (ChartRing F) W (AdjoinRoot.mk _ (separate (MvPolynomial.C c))) = _
    have hc : separate (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) :=
      separate.commutes c
    rw [hc]
    rfl
  exact hEq ▸ inj

/-- The actual coefficient field embeds by interpreting coefficients as constants on the chart. -/
def coefficients : K →+* W := IsFractionRing.lift coefficientValue_injective

instance coefficientAlgebra : Algebra K W := coefficients.toAlgebra

private theorem coefficient_algebraMap (a : Coeff) :
    algebraMap K W (algebraMap Coeff K a) = v (MvPolynomial.C a) :=
  IsFractionRing.lift_algebraMap coefficientValue_injective a

private theorem direction_polynomial (j : Fin 3) (p : Pol Coeff) :
    d j (v p) = v (pderiv j.succ p) - v (pderiv j.succ F) / v (normal F) * v (normal p) :=
  CycleQ2MonicWeightedPrimitiveIdentity.tangent_apply
    (projection F) (projection_surjective F) F (projection_kernel F) universal_normal_ne_zero j p

private theorem direction_kills_coefficients (j : Fin 3) (a : K) :
    d j (algebraMap K W a) = 0 := by
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective Coeff a
  have hj (b : Coeff) : d j (v (MvPolynomial.C b)) = 0 := by
    rw [direction_polynomial]
    simp [normal]
  rw [map_div₀, coefficient_algebraMap, coefficient_algebraMap, Derivation.leibniz_div]
  simp only [hj, smul_zero, sub_zero]

/-- The checked tangent derivations over the full parameter fraction field. -/
def coordinateDerivation (j : Fin 3) : Derivation K W W where
  toFun := d j
  map_add' := (d j).map_add
  map_smul' a x := by
    change d j (a • x) = a • d j x
    rw [Algebra.smul_def, Derivation.leibniz, direction_kills_coefficients, smul_zero, add_zero]
    exact (Algebra.smul_def a (d j x)).symm
  map_one_eq_zero' := (d j).map_one_eq_zero
  leibniz' := (d j).leibniz

abbrev coordinate (j : Fin 3) := v (X j.succ)

theorem coordinateDerivation_coordinate (i j : Fin 3) :
    coordinateDerivation i (coordinate j) = if i = j then 1 else 0 := by
  classical
  change d i (v (X j.succ)) = _
  rw [direction_polynomial]
  simp [normal, pderiv_X, Pi.single_apply, eq_comm]

private theorem polynomial_chain (D : Derivation K W W) (p : Pol Coeff) :
    D (v p) = ∑ i, v (pderiv i p) * D (v (X i)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    exact (coefficient_algebraMap a) ▸ D.map_algebraMap (algebraMap Coeff K a)
  | add p q hp hq =>
    simp only [map_add, add_mul, Finset.sum_add_distrib, hp, hq]
  | mul_X p j hp =>
    have hx : D (v (X j)) = ∑ i, v (pderiv i (X j)) * D (v (X i)) := by
      simp [pderiv_X, Pi.single_apply, apply_ite, eq_comm (a := j)]
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add,
      add_mul, Finset.sum_add_distrib, Finset.mul_sum, hp, hx]
    apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intros <;> ring

private theorem value_equation : v F = 0 := by
  change algebraMap (ChartRing F) W (projection F F) = 0
  rw [(projection_kernel F F).mpr (dvd_refl F), map_zero]

/-- A relative derivation is uniquely determined by the three free coordinates. -/
theorem derivation_eq_zero (D : Derivation K W W) (h : ∀ j, D (coordinate j) = 0) : D = 0 := by
  have hrest (i : Fin 4) (hi : i ≠ 0) : D (v (X i)) = 0 :=
    Fin.cases (fun contra => (contra rfl).elim) (fun j _ => h j) i hi
  have hd := polynomial_chain D F
  rw [value_equation, map_zero, Finset.sum_eq_single (0 : Fin 4)
    (fun i _ hi => by rw [hrest i hi, mul_zero]) (by simp)] at hd
  have hzero : D (v (X 0)) = 0 := (mul_eq_zero.mp hd.symm).resolve_left universal_normal_ne_zero
  have hp (p : Pol Coeff) : D (v p) = 0 := by
    rw [polynomial_chain]
    exact Finset.sum_eq_zero (fun i _ => by
      rw [show D (v (X i)) = 0 from Fin.cases hzero h i, mul_zero])
  apply Derivation.ext
  intro x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (ChartRing F) x
  obtain ⟨p, rfl⟩ := projection_surjective F a
  obtain ⟨q, rfl⟩ := projection_surjective F b
  change D (v p / v q) = 0
  rw [Derivation.leibniz_div, hp, hp, smul_zero, smul_zero, sub_zero, smul_zero]

theorem coordinateDerivation_commutes (i j : Fin 3) :
    Function.Commute (coordinateDerivation i) (coordinateDerivation j) := by
  have hb : ⁅coordinateDerivation i, coordinateDerivation j⁆ = 0 := by
    apply derivation_eq_zero
    intro k
    rw [Derivation.commutator_apply, coordinateDerivation_coordinate, coordinateDerivation_coordinate]
    split_ifs <;> simp
  intro a
  have h := congrArg (fun D : Derivation K W W => D a) hb
  exact sub_eq_zero.mp h

private abbrev dx (j : Fin 3) := KaehlerDifferential.D K W (coordinate j)

private theorem dual_dx (i j : Fin 3) :
    (coordinateDerivation i).liftKaehlerDifferential (dx j) = if i = j then 1 else 0 :=
  (Derivation.liftKaehlerDifferential_comp_D _ _).trans (coordinateDerivation_coordinate i j)

private theorem independent_dx : LinearIndependent W dx := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg j
  have h := congrArg ((coordinateDerivation j).liftKaehlerDifferential) hg
  simp only [map_sum, map_smul, dual_dx, map_zero, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  simpa using h

private theorem span_dx : Submodule.span W (Set.range dx) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro l hl
  change l = 0
  apply Derivation.liftKaehlerDifferential_unique
  exact derivation_eq_zero (l.compDer (KaehlerDifferential.D K W))
    (fun j => (Submodule.mem_dualAnnihilator l).mp hl _ (Submodule.subset_span ⟨j, rfl⟩))

def coordinateBasis : Module.Basis (Fin 3) W Ω[W⁄K] :=
  Module.Basis.mk independent_dx span_dx.ge

theorem coordinateBasis_apply (j : Fin 3) : coordinateBasis j = dx j :=
  Module.Basis.mk_apply _ _ _

theorem coordinateBasis_repr_D (x : W) (j : Fin 3) :
    coordinateBasis.repr (KaehlerDifferential.D K W x) j = coordinateDerivation j x := by
  classical
  have h : coordinateBasis.coord j = (coordinateDerivation j).liftKaehlerDifferential := by
    apply coordinateBasis.ext
    intro i
    rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    rw [coordinateBasis_apply]
    change (if i = j then 1 else 0) = (coordinateDerivation j).liftKaehlerDifferential (dx i)
    rw [dual_dx]
    simp only [eq_comm]
  change coordinateBasis.coord j _ = _
  rw [h, Derivation.liftKaehlerDifferential_comp_D]

/-- Rational exterior differentiation on the universal relative cotangent space. -/
def exteriorDerivative := exteriorD2 coordinateBasis coordinateDerivation

theorem exteriorDerivative_exact_pair (a b c : W) :
    let df := KaehlerDifferential.D K W
    exteriorDerivative (a • exteriorPower.ιMulti W 2 (df ∘ ![b,c])) =
      exteriorPower.ιMulti W 3 (df ∘ ![a,b,c]) :=
  exteriorD2_smul_exact_pair coordinateBasis coordinateDerivation coordinateBasis_repr_D
    coordinateDerivation_commutes a b c

def sourceForm : Form K W 3 := density v F • volume coordinateBasis

theorem source_exact_iff :
    (∃ η : Form K W 2, exteriorDerivative η = sourceForm) ↔ UniversalWeightedPrimitiveExists :=
  exact_volume_iff_divergence coordinateBasis coordinateDerivation (density v F)

section FiniteExtension

variable (L : Type*) [Field L] [Algebra W L] [FiniteDimensional W L]

/-- Canonical extension of each spatial derivation to any finite field used
to construct a rational primitive. -/
def liftedDirection (i : Fin 3) : Derivation ℤ L L :=
  CycleQ2FiniteDifferentialDescent.extend (d i)

theorem liftedDirection_algebraMap (i : Fin 3) (x : W) :
    liftedDirection L i (algebraMap W L x) = algebraMap W L (d i x) :=
  CycleQ2FiniteDifferentialDescent.extend_algebraMap _ x

/-- Normalized trace descends a primitive from a finite extension of
the universal weighted function field, with canonical lifted derivations. -/
theorem primitive_of_finite_extension (u : Fin 3 → L)
    (hu : ∑ j, liftedDirection L j (u j) = algebraMap W L (density v F)) :
    UniversalWeightedPrimitiveExists := by
  refine ⟨fun j => Algebra.normalizedTrace W L (u j), ?_⟩
  have ht := HoldoutConstruction.finiteNormalizedTrace_firstOrder d (liftedDirection L)
    (liftedDirection_algebraMap L) (fun _ => (0 : W)) (density v F) u
    (by simpa only [map_zero, mul_zero, add_zero] using hu)
  simpa only [mul_zero, add_zero] using ht

end FiniteExtension

theorem protected_exact_of_source_exact
    (h : ∃ η : Form K W 2, exteriorDerivative η = sourceForm) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA :=
  exact_form_of_universal_weighted_primitive (source_exact_iff.mp h)

end CycleQ2UniversalWeightedDeRham

#print axioms CycleQ2UniversalWeightedDeRham.exteriorDerivative_exact_pair
#print axioms CycleQ2UniversalWeightedDeRham.source_exact_iff
#print axioms CycleQ2UniversalWeightedDeRham.primitive_of_finite_extension
#print axioms CycleQ2UniversalWeightedDeRham.protected_exact_of_source_exact

section

noncomputable section

/-!
# The actual de Rham complex on an exact rank-three affine frame

The coordinate construction of exterior differentiation is valid over
the coefficient field of the generic threefold. The ordinary
Kähler evaluation on every pair of exact frames is a cochain map.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2ExactFrameThreeDeRham

open CategoryTheory CategoryTheory.Limits Module
open CycleQ2WeightedCoordinateExterior
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

def wedge (α β : Ω[A⁄K]) : Form K A 2 := exteriorPower.ιMulti A 2 ![α,β]

def wedgeLeft (β : Ω[A⁄K]) : Ω[A⁄K] →ₗ[A] Form K A 2 where
  toFun α := wedge α β
  map_add' α γ := (exteriorPower.ιMulti A 2).map_vecCons_add ![β] α γ
  map_smul' a α := (exteriorPower.ιMulti A 2).map_vecCons_smul ![β] a α

def wedgeRight (α : Ω[A⁄K]) : Ω[A⁄K] →ₗ[A] Form K A 2 where
  toFun β := wedge α β
  map_add' β γ := ((exteriorPower.ιMulti A 2).curryLeft α).map_vecCons_add ![] β γ
  map_smul' a β := ((exteriorPower.ιMulti A 2).curryLeft α).map_vecCons_smul ![] a β

theorem wedge_self (α : Ω[A⁄K]) : wedge α α = 0 :=
  (exteriorPower.ιMulti A 2).map_eq_zero_of_eq ![α,α] (by rfl : ![α,α] (0 : Fin 2) = ![α,α] 1) (by decide)

theorem wedge_swap (α β : Ω[A⁄K]) : wedge β α = -wedge α β := by
  have he : ![β,α] = ![α,β] ∘ Equiv.swap (0 : Fin 2) 1 := by funext i; fin_cases i <;> rfl
  unfold wedge
  rw [he,AlternatingMap.map_swap _ _ (by decide : (0 : Fin 2) ≠ 1)]

variable (b : Basis (Fin 3) A (Ω[A⁄K]))

def differential : Ω[A⁄K] →+ Form K A 2 :=
  ∑ i : Fin 3, (wedgeLeft (b i)).toAddMonoidHom.comp
    ((KaehlerDifferential.D K A).toLinearMap.toAddMonoidHom.comp (b.coord i).toAddMonoidHom)

theorem differential_apply (ω : Ω[A⁄K]) :
    differential b ω = ∑ i : Fin 3, wedge (KaehlerDifferential.D K A (b.coord i ω)) (b i) := by
  simp [differential,wedgeLeft]
  rfl

private theorem derivative_expansion (f : A) :
    KaehlerDifferential.D K A f = ∑ i : Fin 3, exactFrameDirection b i f • b i :=
  (b.sum_repr _).symm

theorem differential_D (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D K A (u i)) (f : A) :
    differential b (KaehlerDifferential.D K A f) = 0 := by
  rw [differential_apply]
  change (∑ i : Fin 3, wedge (KaehlerDifferential.D K A (exactFrameDirection b i f)) (b i)) = 0
  simp_rw [derivative_expansion b]
  change (∑ i : Fin 3, wedgeLeft (b i) (∑ j : Fin 3,
    exactFrameDirection b j (exactFrameDirection b i f) • b j)) = 0
  simp only [map_sum,map_smul]
  change (∑ i : Fin 3, ∑ j : Fin 3,
    exactFrameDirection b j (exactFrameDirection b i f) • wedge (b j) (b i)) = 0
  simp only [Fin.sum_univ_three,wedge_self,smul_zero,zero_add,add_zero]
  rw [wedge_swap (b 1) (b 0),wedge_swap (b 2) (b 0),wedge_swap (b 2) (b 1),
    exactFrameDirections_commute b u hu 1 0,exactFrameDirections_commute b u hu 2 0,exactFrameDirections_commute b u hu 2 1]
  simp only [smul_neg]
  abel

theorem differential_smul (a : A) (ω : Ω[A⁄K]) :
    differential b (a • ω) = a • differential b ω + wedge (KaehlerDifferential.D K A a) ω := by
  rw [differential_apply]
  simp only [map_smul,smul_eq_mul,Derivation.leibniz]
  change (∑ i : Fin 3, wedgeLeft (b i)
    (a • KaehlerDifferential.D K A (b.coord i ω) + b.coord i ω • KaehlerDifferential.D K A a)) = _
  simp only [map_add,map_smul,Finset.sum_add_distrib,← Finset.smul_sum]
  change a • differential b ω + (∑ i : Fin 3, b.coord i ω • wedgeRight (KaehlerDifferential.D K A a) (b i)) = _
  simp only [← map_smul,← map_sum]
  have he : (∑ i : Fin 3, b.coord i ω • b i) = ω := b.sum_repr ω
  rw [he]
  rfl

theorem differential_symbol (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D K A (u i)) (a f : A) :
    differential b (a • KaehlerDifferential.D K A f) =
      wedge (KaehlerDifferential.D K A a) (KaehlerDifferential.D K A f) := by
  rw [differential_smul,differential_D b u hu,smul_zero,zero_add]

theorem differential_log (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D K A (u i)) (v : Aˣ) :
    differential b ((v⁻¹ : Aˣ).val • KaehlerDifferential.D K A (v : A)) = 0 := by
  rw [differential_symbol b u hu]
  have hv : KaehlerDifferential.D K A ((v⁻¹ : Aˣ).val) =
      -((v⁻¹ : Aˣ).val ^ 2) • KaehlerDifferential.D K A (v : A) :=
    (KaehlerDifferential.D K A).leibniz_of_mul_eq_one (by simp)
  rw [hv]
  change wedgeLeft (KaehlerDifferential.D K A (v : A))
    (-((v⁻¹ : Aˣ).val ^ 2) • KaehlerDifferential.D K A (v : A)) = 0
  rw [map_smul]
  change -((v⁻¹ : Aˣ).val ^ 2) • wedge (KaehlerDifferential.D K A (v : A)) (KaehlerDifferential.D K A (v : A)) = 0
  rw [wedge_self,smul_zero]

/-- Consecutive exterior differentials vanish on the actual forms. -/
theorem differential_two_one (u : Fin 3 → A)
    (hu : ∀ i, b i = KaehlerDifferential.D K A (u i)) (ω : Ω[A⁄K]) :
    exteriorD2 b (exactFrameDirection b) (differential b ω) = 0 := by
  rw [← b.sum_repr ω, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [hu, differential_symbol b u hu]
  have he := exteriorD2_exactFrame b u hu 1 (b.coord i ω) (u i)
  rw [one_smul] at he
  change exteriorD2 b (exactFrameDirection b)
    (exteriorPower.ιMulti A 2 (KaehlerDifferential.D K A ∘ ![b.coord i ω, u i])) = _
  refine he.trans ?_
  apply (exteriorPower.ιMulti A 3).map_coord_zero 0
  exact (KaehlerDifferential.D K A).map_one_eq_zero

variable {B : Type} [CommRing B] [Algebra K B]

/-- The native ordinary Kähler pullback for any algebra map between charts. -/
def onePullback (φ : A →ₐ[K] B) : Ω[A⁄K] →ₛₗ[φ.toRingHom] Ω[B⁄K] := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower K A B := IsScalarTower.of_algHom φ
  let l := KaehlerDifferential.map K K A B
  exact
    { toFun := l
      map_add' := l.map_add
      map_smul' := fun a x => (l.map_smul a x).trans (IsScalarTower.algebraMap_smul B a (l x)).symm }

theorem onePullback_d (φ : A →ₐ[K] B) (a : A) :
    onePullback φ (KaehlerDifferential.D K A a) = KaehlerDifferential.D K B (φ a) := by
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : IsScalarTower K A B := IsScalarTower.of_algHom φ
  exact KaehlerDifferential.map_D K K A B a

def exteriorPullback (φ : A →ₐ[K] B) (p : ℕ) :
    Form K A p →ₛₗ[φ.toRingHom] Form K B p :=
  exteriorMap φ.toRingHom (onePullback φ) p

theorem exteriorPullback_d (φ : A →ₐ[K] B) (p : ℕ) (a : Fin p → A) :
    exteriorPullback φ p (exteriorPower.ιMulti A p (KaehlerDifferential.D K A ∘ a)) =
      exteriorPower.ιMulti B p (KaehlerDifferential.D K B ∘ (φ ∘ a)) := by
  rw [exteriorPullback, exteriorMap_wedge]
  exact congrArg (exteriorPower.ιMulti B p) (funext fun i => onePullback_d φ (a i))

variable (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D K A (u i))
variable (φ : A →ₐ[K] B) (c : Basis (Fin 3) B Ω[B⁄K])
variable (v : Fin 3 → B) (hv : ∀ i, c i = KaehlerDifferential.D K B (v i))

include hu hv in
theorem differential_natural (ω : Ω[A⁄K]) :
    exteriorPullback φ 2 (differential b ω) = differential c (onePullback φ ω) := by
  rw [← b.sum_repr ω]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hu, differential_symbol b u hu, map_smulₛₗ, onePullback_d,
    differential_symbol c v hv]
  exact exteriorPullback_d φ 2 ![b.coord i ω, u i]

include hu hv in
theorem topDifferential_natural (ω : Form K A 2) :
    exteriorPullback φ 3 (exteriorD2 b (exactFrameDirection b) ω) =
      exteriorD2 c (exactFrameDirection c) (exteriorPullback φ 2 ω) := by
  let f := (exteriorPullback φ 3).toAddMonoidHom.comp (exteriorD2 b (exactFrameDirection b)).toAddMonoidHom
  let g := (exteriorD2 c (exactFrameDirection c)).toAddMonoidHom.comp (exteriorPullback φ 2).toAddMonoidHom
  have he : f = g := by
    apply twoFormMap_ext b u hu
    intro a p q
    change exteriorPullback φ 3 (exteriorD2 b (exactFrameDirection b) _) =
      exteriorD2 c (exactFrameDirection c) (exteriorPullback φ 2 _)
    rw [exteriorD2_exactFrame b u hu, exteriorPullback_d, map_smulₛₗ, exteriorPullback_d]
    exact (exteriorD2_exactFrame c v hv (φ a) (φ p) (φ q)).symm
  exact DFunLike.congr_fun he ω

end CycleQ2ExactFrameThreeDeRham

#print axioms CycleQ2ExactFrameThreeDeRham.differential_two_one
#print axioms CycleQ2ExactFrameThreeDeRham.differential_natural
#print axioms CycleQ2ExactFrameThreeDeRham.topDifferential_natural

end

end

section

noncomputable section

/-!
# Exact differential frames from standard smooth presentations

The complement of the relation variables in a submersive presentation provides
actual functions whose differentials give a basis of the relative cotangent
module. Its cardinality is the specified relative dimension.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2SmoothRelativeFrames

open Algebra Module AlgebraicGeometry CategoryTheory

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

theorem exists_exact_basis (n : ℕ) [IsStandardSmoothOfRelativeDimension n K A] :
    ∃ (x : Fin n → A) (b : Basis (Fin n) A Ω[A⁄K]),
      ∀ i, b i = KaehlerDifferential.D K A (x i) := by
  classical
  obtain ⟨ι, σ, hσ, hι, P, hn⟩ :=
    (inferInstance : IsStandardSmoothOfRelativeDimension n K A).out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  let J := (↥((Set.range P.map)ᶜ : Set ι))
  letI : Fintype J := Fintype.ofFinite _
  have hj : Fintype.card J = n := by
    change Fintype.card ((Set.range P.map)ᶜ : Set ι) = n
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
    simpa only [Presentation.dimension, Nat.card_eq_fintype_card] using hn
  let e : J ≃ Fin n := Fintype.equivFinOfCardEq hj
  refine ⟨fun i => P.val (e.symm i), P.basisKaehler.reindex e, ?_⟩
  intro i
  rw [Basis.reindex_apply, Algebra.SubmersivePresentation.basisKaehler_apply]

section Schemes

variable {F : Type} [Field F] {X : Scheme.{0}}
variable (f : X ⟶ Spec (CommRingCat.of F))

/-- The coefficient algebra on the original sections of an open of a scheme over a field. -/
def sectionCoefficients (V : X.Opens) : F →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of F)).inv ≫ f.appLE ⊤ V
    (by rw [Scheme.Hom.preimage_top]; exact le_top)).hom

/-- Each point of a smooth scheme over a field has an affine neighborhood on
which exact relative differentials give a basis of the stated dimension. -/
theorem exists_exact_affine_neighborhood (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (V : X.Opens), IsAffineOpen V ∧ x ∈ V ∧
      letI : Algebra F Γ(X, V) := (sectionCoefficients f V).toAlgebra
      ∃ (u : Fin n → Γ(X, V)) (b : Basis (Fin n) Γ(X, V) (KaehlerDifferential F Γ(X, V))),
        ∀ i, b i = KaehlerDifferential.D F Γ(X, V) (u i) := by
  obtain ⟨U, _, V, hV, hx, hle, hs⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    have e : y = f x := Subsingleton.elim _ _
    rw [e]
    exact hle hx
  subst U
  refine ⟨V, hV, hx, ?_⟩
  letI : Algebra F Γ(X, V) := (sectionCoefficients f V).toAlgebra
  have hIso : RingHom.IsStandardSmoothOfRelativeDimension 0
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom := by
    exact RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (asIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).commRingCatIsoToRingEquiv
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension n (sectionCoefficients f V) := by
    change RingHom.IsStandardSmoothOfRelativeDimension n
      ((f.appLE ⊤ V hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom)
    simpa only [Nat.add_zero] using hs.comp hIso
  letI : IsStandardSmoothOfRelativeDimension n F Γ(X, V) := hstd.toAlgebra
  exact exists_exact_basis n

end Schemes

end CycleQ2SmoothRelativeFrames

#print axioms CycleQ2SmoothRelativeFrames.exists_exact_basis
#print axioms CycleQ2SmoothRelativeFrames.exists_exact_affine_neighborhood

end

end

section

noncomputable section

/-!
# Exact frames on the native affine overlaps

Restriction along an inclusion of affine opens is étale. The canonical
Kähler base-change isomorphism carries the coordinate differentials to
the differentials of the restricted functions. Thus the affine overlap
complexes use the original restriction maps and the native relative
exterior differential.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2RelativeAffineOverlap

open AlgebraicGeometry CategoryTheory Opposite Module KaehlerDifferential
open CycleQ2SmoothRelativeFrames

variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]

section Algebra
variable [Algebra.FormallyEtale A B] {n : ℕ} (b : Basis (Fin n) A Ω[A⁄K])

def baseChangeFrame : Basis (Fin n) B Ω[B⁄K] :=
  (b.baseChange B).map (tensorKaehlerEquivOfFormallyEtale K A B)

theorem baseChangeFrame_apply (u : Fin n → A) (h : ∀ i, b i = D K A (u i)) (i : Fin n) :
    baseChangeFrame b i = D K B (algebraMap A B (u i)) := by
  rw [baseChangeFrame, Basis.map_apply, Basis.baseChange_apply, h,
    ← LinearEquiv.eq_symm_apply]
  exact (tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap K A B (u i)).symm

end Algebra

section Schemes

variable {F : Type} [Field F] {X : Scheme.{0}}
variable (f : X ⟶ Spec (CommRingCat.of F))

/-- Restriction of sections over the given base field. -/
def restrict {U V : X.Opens} (h : V ≤ U) :
    letI : Algebra F Γ(X, U) := (sectionCoefficients f U).toAlgebra
    letI : Algebra F Γ(X, V) := (sectionCoefficients f V).toAlgebra
    Γ(X, U) →ₐ[F] Γ(X, V) := by
  letI : Algebra F Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra F Γ(X, V) := (sectionCoefficients f V).toAlgebra
  refine { toRingHom := (X.presheaf.map (homOfLE h).op).hom, commutes' := ?_ }
  intro a
  change (X.presheaf.map (homOfLE h).op) (sectionCoefficients f U a) = sectionCoefficients f V a
  unfold sectionCoefficients
  change (((Scheme.ΓSpecIso _).inv ≫ f.appLE ⊤ U _) ≫ X.presheaf.map (homOfLE h).op) a =
    ((Scheme.ΓSpecIso _).inv ≫ f.appLE ⊤ V _) a
  rw [Category.assoc, Scheme.Hom.appLE_map]

theorem restrict_etale {U V : X.Opens} (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    (X.presheaf.map (homOfLE h).op).hom.Etale := by
  let e := X.homOfLE h
  letI : IsAffine U.toScheme := hU
  letI : IsAffine V.toScheme := hV
  have he : Etale e := inferInstance
  have htop := HasRingHomProperty.appTop (P := @Etale) e he
  let k := U.topIso.inv ≫ e.appTop ≫ V.topIso.hom
  have hk : k.hom.Etale :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso U.topIso.inv))
      (RingHom.Etale.stableUnderComposition _ _ htop
        (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso V.topIso.hom)))
  have eq : X.presheaf.map (homOfLE h).op = k := by
    change X.presheaf.map (homOfLE h).op = U.topIso.inv ≫ e.appTop ≫ V.topIso.hom
    dsimp only [e]
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.topIso_hom, Scheme.homOfLE_appTop]
    erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    exact congrArg X.presheaf.map (Subsingleton.elim _ _)
  have eq' := congrArg CommRingCat.Hom.hom eq
  rw [eq']
  exact hk

/-- Keep the same coordinate functions after restriction to any affine subopen. -/
theorem exact_on_affine_subopen {U V : X.Opens} (h : V ≤ U) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    {n : ℕ} (u : Fin n → Γ(X, U)) :
    letI : Algebra F Γ(X, U) := (sectionCoefficients f U).toAlgebra
    letI : Algebra F Γ(X, V) := (sectionCoefficients f V).toAlgebra
    ∀ (b : Basis (Fin n) Γ(X, U) (KaehlerDifferential F Γ(X, U))),
      (∀ i, b i = D F Γ(X, U) (u i)) →
      ∃ c : Basis (Fin n) Γ(X, V) (KaehlerDifferential F Γ(X, V)),
        ∀ i, c i = D F Γ(X, V) (restrict f h (u i)) := by
  letI : Algebra F Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra F Γ(X, V) := (sectionCoefficients f V).toAlgebra
  intro b hb
  letI : Algebra Γ(X, U) Γ(X, V) := (restrict f h).toRingHom.toAlgebra
  letI : IsScalarTower F Γ(X, U) Γ(X, V) := IsScalarTower.of_algHom (restrict f h)
  let : Algebra.Etale Γ(X, U) Γ(X, V) := (restrict_etale h hU hV).toAlgebra
  exact ⟨baseChangeFrame (B := Γ(X, V)) b, baseChangeFrame_apply b u hb⟩

end Schemes

end CycleQ2RelativeAffineOverlap

#print axioms CycleQ2RelativeAffineOverlap.exact_on_affine_subopen

end

end

section

noncomputable section

/-!
# Lifting coefficient derivations on actual smooth affine charts

Formal smoothness splits the relative cotangent sequence. This extends each
derivation of the coefficient algebra to the chart. Subtracting its three
coordinate values gives the unique lift fixing an exact coordinate frame.
This lift commutes with all three spatial derivations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2RelativeDerivationLift

open Algebra Module KaehlerDifferential
open CycleQ2WeightedCoordinateExterior
open scoped TensorProduct

variable {k K A : Type} [CommRing k] [CommRing K] [CommRing A]
  [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]

theorem exists_lift [FormallySmooth K A] (δ : Derivation k K K) :
    ∃ d : Derivation k A A, ∀ x, d (algebraMap K A x) = algebraMap K A (δ x) := by
  let α := KaehlerDifferential.mapBaseChange k K A
  let β := KaehlerDifferential.map k K A A
  have hs : Function.Exact α β := KaehlerDifferential.exact_mapBaseChange_map k K A
  have hi : Function.Injective α := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k K A x).mp hx
    rw [Subsingleton.elim y 0, map_zero]
  have hb : Function.Surjective β := KaehlerDifferential.map_surjective k K A
  obtain ⟨s, hs'⟩ := Module.projective_lifting_property β LinearMap.id hb
  obtain ⟨r, hr⟩ := ((hs.split_tfae').out 0 1 rfl rfl).mp ⟨hi, s, hs'⟩ |>.2
  let baseDerivation := (Algebra.linearMap K A).comp δ.liftKaehlerDifferential
  refine ⟨((baseDerivation.liftBaseChange A).comp r).compDer (D k A), ?_⟩
  intro x
  change (baseDerivation.liftBaseChange A) (r (D k A (algebraMap K A x))) = _
  have hα : α (1 ⊗ₜ D k K x) = D k A (algebraMap K A x) := by
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rw [← hα]
  have hr' : r (α (1 ⊗ₜ D k K x)) = 1 ⊗ₜ D k K x := DFunLike.congr_fun hr _
  rw [hr', LinearMap.liftBaseChange_tmul, one_smul]
  exact congrArg (algebraMap K A) (Derivation.liftKaehlerDifferential_comp_D δ x)

/-- A base derivation vanishing on all coefficients is relative. -/
def asRelative (d : Derivation k A A) (hd : ∀ x : K, d (algebraMap K A x) = 0) :
    Derivation K A A where
  toFun := d
  map_one_eq_zero' := d.map_one_eq_zero
  map_add' := d.map_add
  leibniz' := d.leibniz
  map_smul' a x := by
    rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, d.leibniz, hd, smul_zero, add_zero]
    rfl

theorem exact_coordinate_unique (b : Basis (Fin 3) A Ω[A⁄K])
    (u : Fin 3 → A) (hu : ∀ i, b i = D K A (u i))
    (d : Derivation K A A) (hd : ∀ i, d (u i) = 0) : d = 0 := by
  have h : d.liftKaehlerDifferential = 0 := by
    apply b.ext
    intro i
    rw [hu, Derivation.liftKaehlerDifferential_comp_D, LinearMap.zero_apply]
    exact hd i
  ext a
  have e := DFunLike.congr_fun h (D K A a)
  rwa [Derivation.liftKaehlerDifferential_comp_D, LinearMap.zero_apply] at e

private theorem sum_apply (f : Fin 3 → Derivation k A A) (a : A) :
    (∑ i, f i) a = ∑ i, f i a := by
  have h := congrFun (map_sum (Derivation.coeFnAddMonoidHom : Derivation k A A →+ A → A)
    f Finset.univ) a
  simpa only [Derivation.coeFnAddMonoidHom_apply, Finset.sum_apply] using h

theorem exact_lift [FormallySmooth K A] (δ : Derivation k K K)
    (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hu : ∀ i, b i = D K A (u i)) :
    ∃! d : Derivation k A A,
      (∀ x, d (algebraMap K A x) = algebraMap K A (δ x)) ∧ ∀ i, d (u i) = 0 := by
  obtain ⟨l, hl⟩ := exists_lift (A := A) δ
  let d := l - ∑ i : Fin 3, l (u i) • (exactFrameDirection b i).restrictScalars k
  have hc : ∀ x, d (algebraMap K A x) = algebraMap K A (δ x) := by
    intro x
    simp [d, hl, sum_apply]
  have hd : ∀ i, d (u i) = 0 := by
    intro i
    simp only [d, Derivation.sub_apply, sum_apply]
    change l (u i) - ∑ j : Fin 3, l (u j) * exactFrameDirection b j (u i) = 0
    simp [exactFrameDirection_apply, ← hu, Finsupp.single_apply]
  refine ⟨d, ⟨hc, hd⟩, ?_⟩
  rintro e ⟨he, heu⟩
  let rel := asRelative (K := K) (e - d) (by intro x; simp [he, hc])
  have zero : rel = 0 := exact_coordinate_unique b u hu rel (by
    intro i
    change e (u i) - d (u i) = 0
    rw [heu, hd, sub_zero])
  ext x
  have h := DFunLike.congr_fun zero x
  change e x - d x = 0 at h
  exact sub_eq_zero.mp h

theorem commutes_spatial (δ : Derivation k K K) (d : Derivation k A A)
    (hc : ∀ x, d (algebraMap K A x) = algebraMap K A (δ x))
    (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hu : ∀ i, b i = D K A (u i))
    (hd : ∀ i, d (u i) = 0) (i : Fin 3) :
    Function.Commute d (exactFrameDirection b i) := by
  let p := (exactFrameDirection b i).restrictScalars k
  let e := ⁅d,p⁆
  have eA : ∀ x : K, e (algebraMap K A x) = 0 := by
    intro x
    change d (p (algebraMap K A x)) - p (d (algebraMap K A x)) = 0
    simp [p,hc]
  let E := asRelative (K := K) e eA
  have eU : ∀ j, E (u j) = 0 := by
    intro j
    change d (exactFrameDirection b i (u j)) - exactFrameDirection b i (d (u j)) = 0
    rw [hd, map_zero]
    have coord : exactFrameDirection b i (u j) = if j = i then 1 else 0 := by
      change b.coord i (D K A (u j)) = _
      rw [← hu j, Basis.coord_apply, Basis.repr_self_apply]
    rw [coord]
    split <;> simp
  have h := exact_coordinate_unique b u hu E eU
  intro x
  have hx := DFunLike.congr_fun h x
  change d (exactFrameDirection b i x) - exactFrameDirection b i (d x) = 0 at hx
  exact sub_eq_zero.mp hx

end CycleQ2RelativeDerivationLift

#print axioms CycleQ2RelativeDerivationLift.exact_lift
#print axioms CycleQ2RelativeDerivationLift.commutes_spatial

end

end

section

noncomputable section

/-!
# The coefficient connection on the actual relative de Rham chart

A lift fixing the exact coordinates differentiates each basis coefficient.
The Leibniz rule and commutation with spatial derivations make it commute
with the first and top ordinary de Rham differentials. This is the
local coefficient operator before the overlap homotopies are introduced.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2RelativeChartConnection

open Module KaehlerDifferential
open CycleQ2RelativeDerivationLift CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham

variable {k K A : Type} [CommRing k] [CommRing K] [CommRing A]
  [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]

section Basis
variable {I M : Type} [Fintype I] [AddCommGroup M] [Module A M]
  (d : Derivation k A A) (B : Basis I A M)

/-- Apply the lifted coefficient derivation to every coordinate. -/
def onBasis : M →+ M :=
  ∑ i, (LinearMap.toSpanSingleton A M (B i)).toAddMonoidHom.comp
    (d.toLinearMap.toAddMonoidHom.comp (B.coord i).toAddMonoidHom)

theorem onBasis_apply (w : M) :
    onBasis d B w = ∑ i, d (B.repr w i) • B i := by
  simp [onBasis, LinearMap.toSpanSingleton_apply]

theorem onBasis_repr (w : M) (i : I) :
    B.repr (onBasis d B w) i = d (B.repr w i) := by
  classical
  rw [onBasis_apply]
  simp [Finsupp.single_apply]

/-- The output has the connection Leibniz rule for every chart function. -/
theorem onBasis_smul (a : A) (w : M) :
    onBasis d B (a • w) = a • onBasis d B w + d a • w := by
  apply B.repr.injective
  ext i
  simp only [onBasis_repr, map_smul, map_add, Finsupp.smul_apply, Finsupp.add_apply,
    smul_eq_mul, Derivation.leibniz, mul_comm]

theorem onBasis_reindex {J : Type} [Fintype J] (e : I ≃ J) :
    onBasis d (B.reindex e) = onBasis d B := by
  ext w
  rw [onBasis_apply, onBasis_apply]
  simp only [Basis.repr_reindex_apply, Basis.reindex_apply]
  exact e.symm.sum_comp (fun i => d (B.repr w i) • B i)

end Basis

variable (δ : Derivation k K K) (d : Derivation k A A)
  (hc : ∀ a, d (algebraMap K A a) = algebraMap K A (δ a))
variable (B : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A)
  (hu : ∀ i, B i = D K A (u i)) (hd : ∀ i, d (u i) = 0)

include hc hu hd in
/-- On exact one-forms, the local coefficient connection differentiates the
function before taking the relative differential. -/
theorem onOne_D (a : A) : onBasis d B (D K A a) = D K A (d a) := by
  apply B.repr.injective
  ext i
  rw [onBasis_repr]
  change d (exactFrameDirection B i a) = exactFrameDirection B i (d a)
  exact commutes_spatial δ d hc B u hu hd i a

include hc hu hd in
theorem onOne_symbol (a x : A) :
    onBasis d B (a • D K A x) = a • D K A (d x) + d a • D K A x := by
  rw [onBasis_smul, onOne_D δ d hc B u hu hd]

include hc hu hd in
/-- Differentiating a logarithmic one-form in a coefficient direction is an
ordinary exact relative one-form. -/
theorem onOne_logarithm (v : Aˣ) :
    onBasis d B ((↑v⁻¹ : A) • D K A (v : A)) =
      D K A ((↑v⁻¹ : A) * d (v : A)) := by
  rw [onOne_symbol δ d hc B u hu hd, Derivation.leibniz]
  have hinv : d (↑v⁻¹ : A) = -((↑v⁻¹ : A) ^ 2) • d (v : A) :=
    d.leibniz_of_mul_eq_one (by simp)
  have hrel : D K A (↑v⁻¹ : A) = -((↑v⁻¹ : A) ^ 2) • D K A (v : A) :=
    (D K A).leibniz_of_mul_eq_one (by simp)
  simp only [hinv, hrel, smul_smul, smul_eq_mul, mul_comm (d (v : A))]

private theorem wedge_repr (α β : Ω[A⁄K]) (j : Set.powersetCard (Fin 3) 2) :
    (B.exteriorPower 2).repr (wedge α β) j =
      (Matrix.of (fun i k => B.repr (![α,β] i) (Set.powersetCard.ofFinEmbEquiv.symm j k))).det := by
  rw [wedge, exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  rfl

/-- Coefficient differentiation on the two-form basis obeys the wedge rule. -/
theorem onTwo_wedge (α β : Ω[A⁄K]) :
    onBasis d (twoBasis B) (wedge α β) =
      wedge (onBasis d B α) β + wedge α (onBasis d B β) := by
  simp only [twoBasis, onBasis_reindex]
  apply (B.exteriorPower 2).repr.injective
  ext j
  rw [onBasis_repr, map_add, Finsupp.add_apply, wedge_repr, wedge_repr, wedge_repr]
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    onBasis_repr, map_sub, Derivation.leibniz, smul_eq_mul]
  ring

include hc hu hd in
theorem differential_onOne (ω : Ω[A⁄K]) :
    differential B (onBasis d B ω) = onBasis d (twoBasis B) (differential B ω) := by
  rw [← B.sum_repr ω]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h : onBasis d B (B i) = 0 := by
    rw [hu, onOne_D δ d hc B u hu hd, hd, map_zero]
  rw [onBasis_smul, h, smul_zero, zero_add, hu, differential_symbol B u hu,
    differential_symbol B u hu, onTwo_wedge, onOne_D δ d hc B u hu hd]
  rw [← hu i, h]
  change _ = _ + wedgeRight (D K A (B.repr ω i)) 0
  rw [map_zero, add_zero, hu]

include hc hu hd in
/-- The coefficient variation of the two-equation logarithmic form has an
explicit ordinary one-form primitive in the double localization. -/
theorem onTwo_logarithms (f g : Aˣ) :
    let l (v : Aˣ) := (↑v⁻¹ : A) • D K A (v : A)
    let a (v : Aˣ) := (↑v⁻¹ : A) * d (v : A)
    onBasis d (twoBasis B) (wedge (l f) (l g)) =
      differential B (a f • l g - a g • l f) := by
  dsimp only
  have h (x : A) (v : Aˣ) :
      differential B (x • ((↑v⁻¹ : A) • D K A (v : A))) =
        wedge (D K A x) ((↑v⁻¹ : A) • D K A (v : A)) := by
    calc
      _ = x • differential B ((↑v⁻¹ : A) • D K A (v : A)) +
          wedge (D K A x) ((↑v⁻¹ : A) • D K A (v : A)) := differential_smul B x _
      _ = _ := by rw [differential_log B u hu v, smul_zero, zero_add]
  rw [onTwo_wedge, onOne_logarithm δ d hc B u hu hd,
    onOne_logarithm δ d hc B u hu hd, map_sub, h, h,
    wedge_swap (D K A ((↑g⁻¹ : A) * d (g : A))), sub_eq_add_neg]

/-- On top forms, the ordered volume identifies the connection with the
lifted derivation of its scalar. -/
def onVolume (a : A) : Form K A 3 := d a • volume B

include hc hu hd in
theorem exteriorD2_onBasis (η : Form K A 2) :
    exteriorD2 B (exactFrameDirection B) (onBasis d (twoBasis B) η) =
      onVolume d B (∑ i, exactFrameDirection B i (signedCoefficients B η i)) := by
  rw [exteriorD2_divergence, onVolume, map_sum]
  apply congrArg (fun a : A => a • volume B)
  apply Finset.sum_congr rfl
  intro i _
  have e : signedCoefficients B (onBasis d (twoBasis B) η) i =
      d (signedCoefficients B η i) := by
    simp only [signedCoefficients, onBasis_repr, Derivation.leibniz, Derivation.leibniz_pow,
      map_neg, Derivation.map_one_eq_zero, neg_zero, nsmul_zero, smul_eq_mul, mul_zero, add_zero]
  rw [e]
  exact (commutes_spatial δ d hc B u hu hd i (signedCoefficients B η i)).symm

end CycleQ2RelativeChartConnection

#print axioms CycleQ2RelativeChartConnection.onOne_D
#print axioms CycleQ2RelativeChartConnection.exteriorD2_onBasis
#print axioms CycleQ2RelativeChartConnection.onOne_logarithm
#print axioms CycleQ2RelativeChartConnection.differential_onOne
#print axioms CycleQ2RelativeChartConnection.onTwo_logarithms

end

end

section

noncomputable section

/-!
# The native affine de Rham cochain complex in dimension three

Over the coefficient field the ordinary Kähler forms and the actual
exterior derivatives form a cochain complex. An algebra map between
two exact affine frames induces the ordinary pullback as a cochain map.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2AffineDeRhamComplex

open CategoryTheory CategoryTheory.Limits Module KaehlerDifferential
open CycleQ2ExactFrameThreeDeRham CycleQ2WeightedCoordinateExterior

variable (K A : Type) [CommRing K] [CommRing A] [Algebra K A]

def degree : ℕ → AddCommGrpCat.{0}
  | 0 => AddCommGrpCat.of A
  | 1 => AddCommGrpCat.of Ω[A⁄K]
  | 2 => AddCommGrpCat.of (Form K A 2)
  | 3 => AddCommGrpCat.of (Form K A 3)
  | _ + 4 => AddCommGrpCat.of PUnit

variable {K A} (b : Basis (Fin 3) A Ω[A⁄K])

def next : ∀ p, degree K A p ⟶ degree K A (p + 1)
  | 0 => AddCommGrpCat.ofHom (D K A).toLinearMap.toAddMonoidHom
  | 1 => AddCommGrpCat.ofHom (differential b)
  | 2 => AddCommGrpCat.ofHom (CycleQ2WeightedCoordinateExterior.exteriorD2 b (exactFrameDirection b)).toAddMonoidHom
  | _ + 3 => 0

variable (u : Fin 3 → A) (hu : ∀ i, b i = D K A (u i))

include hu in
theorem square : ∀ p, next b p ≫ next b (p + 1) = 0
  | 0 => by
    ext a
    exact differential_D b u hu a
  | 1 => by
    ext ω
    exact differential_two_one b u hu ω
  | 2 => by
    ext a
    rfl
  | _ + 3 => by simp only [next, zero_comp]

def complex : CochainComplex AddCommGrpCat.{0} ℕ :=
  CochainComplex.of (degree K A) (next b) (square b u hu)

variable {B : Type} [CommRing B] [Algebra K B] (φ : A →ₐ[K] B)

def pullDegree : ∀ p, degree K A p ⟶ degree K B p
  | 0 => AddCommGrpCat.ofHom φ.toRingHom.toAddMonoidHom
  | 1 => AddCommGrpCat.ofHom (onePullback φ).toAddMonoidHom
  | 2 => AddCommGrpCat.ofHom (exteriorPullback φ 2).toAddMonoidHom
  | 3 => AddCommGrpCat.ofHom (exteriorPullback φ 3).toAddMonoidHom
  | _ + 4 => 0

variable (c : Basis (Fin 3) B Ω[B⁄K]) (v : Fin 3 → B) (hv : ∀ i, c i = D K B (v i))

include hu hv in
theorem pull_comm : ∀ p, pullDegree φ p ≫ next c p = next b p ≫ pullDegree φ (p + 1)
  | 0 => by
    ext a
    exact (onePullback_d φ a).symm
  | 1 => by
    ext ω
    exact (differential_natural b u hu φ c v hv ω).symm
  | 2 => by
    ext ω
    exact (topDifferential_natural b u hu φ c v hv ω).symm
  | 3 => by simp only [next, comp_zero, zero_comp]
  | _ + 4 => by simp only [next, pullDegree, comp_zero]

/-- The cochain map is induced by the actual Kähler pullback in every degree. -/
def pullComplex : complex b u hu ⟶ complex c v hv :=
  CochainComplex.ofHom (pullDegree φ) (by
    intro p
    simp only [complex, CochainComplex.of_d]
    exact pull_comm b u hu φ c v hv p)

end CycleQ2AffineDeRhamComplex

#print axioms CycleQ2AffineDeRhamComplex.square
#print axioms CycleQ2AffineDeRhamComplex.pullComplex

end

end

section

noncomputable section

/-!
# Principal residue class on actual functions

In a localization where the equation f is invertible, a function on
the divisor maps to its lift multiplied by df/f, modulo regular
one-forms. Multiples of f map to regular forms. Changing f by a unit
adds a regular logarithmic differential and gives the same class.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2PrincipalGysinFunctions

variable {K A T : Type} [CommRing K] [CommRing A] [CommRing T]
  [Algebra K A] [Algebra K T] [Algebra A T] [IsScalarTower K A T]

local notation "dA" => KaehlerDifferential.D K A
local notation "dT" => KaehlerDifferential.D K T

abbrev regular : Ω[A⁄K] →ₗ[A] Ω[T⁄K] := KaehlerDifferential.map K K A T

abbrev poleQuotient :=
  Ω[T⁄K] ⧸ LinearMap.range (regular (K := K) (A := A) (T := T))

abbrev toPole :=
  (LinearMap.range (regular (K := K) (A := A) (T := T))).mkQ

def logarithm (u : Tˣ) : Ω[T⁄K] := (↑u⁻¹ : T) • dT (u : T)

theorem logarithm_mul (u v : Tˣ) : logarithm (K := K) (u * v) = logarithm u + logarithm v := by
  unfold logarithm
  rw [mul_inv_rev, Units.val_mul, Units.val_mul, Derivation.leibniz, smul_add, smul_smul, smul_smul]
  have hu : (↑v⁻¹ : T) * (↑u⁻¹ : T) * (u : T) = (↑v⁻¹ : T) := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  have hv : (↑v⁻¹ : T) * (↑u⁻¹ : T) * (v : T) = (↑u⁻¹ : T) := by
    rw [mul_comm (↑v⁻¹ : T), mul_assoc, Units.inv_mul, mul_one]
  rw [hu,hv,add_comm]

theorem logarithm_regular (u : Aˣ) :
    logarithm (K := K) (Units.map (algebraMap A T) u) =
      regular (K := K) (A := A) (T := T) ((↑u⁻¹ : A) • dA (u : A)) := by
  unfold logarithm
  rw [map_smul, KaehlerDifferential.map_D]
  change (algebraMap A T (↑u⁻¹ : A)) • dT (algebraMap A T (u : A)) =
    (↑u⁻¹ : A) • dT (algebraMap A T (u : A))
  exact IsScalarTower.algebraMap_smul T (↑u⁻¹ : A) _

variable (f : A) (hf : IsUnit (algebraMap A T f))

private def lift : A →ₗ[A] Ω[T⁄K] :=
  LinearMap.toSpanSingleton A _ (logarithm (K := K) hf.unit)

private theorem lift_f : lift (K := K) f hf f = regular (K := K) (T := T) (dA f) := by
  change f • ((↑hf.unit⁻¹ : T) • dT (hf.unit : T)) = _
  have hs : algebraMap A T f * (↑hf.unit⁻¹ : T) = 1 :=
    (congrArg (fun a : T => a * (↑hf.unit⁻¹ : T)) hf.unit_spec.symm).trans (Units.mul_inv hf.unit)
  rw [← IsScalarTower.algebraMap_smul T, smul_smul, hs, one_smul, hf.unit_spec,
    KaehlerDifferential.map_D]

/-- The principal equation cuts out the actual quotient of functions.
Its image modulo regular forms is independent of the chosen lift. -/
def classMap :
    (A ⧸ (Ideal.span {f} : Ideal A)) →ₗ[A] poleQuotient (K := K) (A := A) (T := T) :=
  (show Submodule A A from Ideal.span {f}).liftQ
    ((toPole (K := K) (A := A) (T := T)).comp (lift (K := K) f hf)) (by
    change Submodule.span A ({f} : Set A) ≤ _
    apply Submodule.span_le.mpr
    intro a ha
    have h : a = f := Set.mem_singleton_iff.mp ha
    subst a
    apply LinearMap.mem_ker.mpr
    change toPole (K := K) (A := A) (T := T) (lift (K := K) f hf f) = 0
    rw [lift_f]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _))

theorem classMap_apply (a : A) :
    classMap (K := K) f hf ((Ideal.Quotient.mk (Ideal.span {f})) a) =
      toPole (a • logarithm (K := K) hf.unit) := rfl

/-- Replacing the equation by an invertible multiple changes a lifted
principal residue by a regular one-form. -/
theorem same_lifted_class (u : Aˣ) (a : A) :
    toPole (K := K) (A := A) (T := T) (a • logarithm (K := K) (Units.map (algebraMap A T) u * hf.unit)) =
      toPole (K := K) (A := A) (T := T) (a • logarithm (K := K) hf.unit) := by
  rw [logarithm_mul, smul_add, map_add, logarithm_regular]
  have hz : toPole (K := K) (A := A) (T := T) (a • regular (K := K) (T := T) ((↑u⁻¹ : A) • dA (u : A))) = 0 := by
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)
  rw [hz, zero_add]

end CycleQ2PrincipalGysinFunctions

#print axioms CycleQ2PrincipalGysinFunctions.classMap
#print axioms CycleQ2PrincipalGysinFunctions.same_lifted_class

end

end

section

noncomputable section

/-!
# Principal residue class on the conormal quotient of one-forms

The map from a divisor one-form to its logarithmic lift modulo regular
two-forms kills the equation and the conormal differential. It is
compatible with the actual exterior differentials with the sign
required by the degree-one shift.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2PrincipalGysinOneForms

open CycleQ2PrincipalGysinFunctions CycleQ2ExactFrameThreeDeRham
open CycleQ2WeightedCoordinateExterior
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)
open Module

variable {K A T : Type} [CommRing K] [CommRing A] [CommRing T]
  [Algebra K A] [Algebra K T] [Algebra A T] [IsScalarTower K A T]

local notation "dA" => KaehlerDifferential.D K A
local notation "dT" => KaehlerDifferential.D K T

private abbrev φ : A →ₐ[K] T := IsScalarTower.toAlgHom K A T

def regularTwo : Form K A 2 →ₗ[A] Form K T 2 :=
  let map := exteriorPullback (φ (K := K) (A := A) (T := T)) 2
  { toFun := map
    map_add' := map.map_add
    map_smul' := fun a x => (map.map_smulₛₗ a x).trans (IsScalarTower.algebraMap_smul T a _).symm }

abbrev poleTwo := Form K T 2 ⧸ LinearMap.range (regularTwo (K := K) (A := A) (T := T))

abbrev toPoleTwo := (LinearMap.range (regularTwo (K := K) (A := A) (T := T))).mkQ

private theorem onePullback_regular (ω : Ω[A⁄K]) :
    onePullback (φ (K := K) (A := A) (T := T)) ω = regular (K := K) (T := T) ω := by
  let map := onePullback (φ (K := K) (A := A) (T := T))
  let l : Ω[A⁄K] →ₗ[A] Ω[T⁄K] :=
    { toFun := map
      map_add' := map.map_add
      map_smul' := fun a x => by
        have h : map (a • x) = (algebraMap A T a) • map x := map.map_smulₛₗ a x
        exact h.trans (IsScalarTower.algebraMap_smul T a (map x)) }
  have h : l = regular (K := K) (T := T) := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    exact (onePullback_d φ a).trans (KaehlerDifferential.map_D K K A T a).symm
  exact DFunLike.congr_fun h ω

private theorem regularTwo_wedge (ω η : Ω[A⁄K]) :
    regularTwo (K := K) (A := A) (T := T) (wedge ω η) =
      wedge (regular (K := K) (T := T) ω) (regular (K := K) (T := T) η) := by
  change exteriorPullback (φ (K := K) (A := A) (T := T)) 2 (exteriorPower.ιMulti A 2 ![ω,η]) = _
  rw [exteriorPullback, exteriorMap_wedge]
  apply congrArg (exteriorPower.ιMulti T 2)
  funext i
  fin_cases i
  · exact onePullback_regular ω
  · exact onePullback_regular η

variable (f : A) (hf : IsUnit (algebraMap A T f))

abbrev conormal : Submodule A Ω[A⁄K] :=
  LinearMap.range (f • LinearMap.id : Ω[A⁄K] →ₗ[A] Ω[A⁄K]) ⊔ Submodule.span A {dA f}

private def lift : Ω[A⁄K] →ₗ[A] Form K T 2 :=
  ((wedgeRight (logarithm (K := K) hf.unit)).restrictScalars A).comp (regular (K := K))

private theorem f_log : f • logarithm (K := K) hf.unit = regular (K := K) (T := T) (dA f) := by
  change f • ((↑hf.unit⁻¹ : T) • dT (hf.unit : T)) = _
  have hs : algebraMap A T f * (↑hf.unit⁻¹ : T) = 1 :=
    (congrArg (fun a : T => a * (↑hf.unit⁻¹ : T)) hf.unit_spec.symm).trans (Units.mul_inv hf.unit)
  rw [← IsScalarTower.algebraMap_smul T, smul_smul, hs, one_smul, hf.unit_spec,
    KaehlerDifferential.map_D]

private theorem lift_f_smul (ω : Ω[A⁄K]) :
    lift (K := K) f hf (f • ω) = regularTwo (K := K) (T := T) (wedge (dA f) ω) := by
  rw [map_smul]
  change f • wedgeLeft (regular (K := K) (T := T) ω) (logarithm (K := K) hf.unit) = _
  rw [← LinearMap.map_smul_of_tower, f_log f hf, regularTwo_wedge]
  rfl

private theorem lift_df : lift (K := K) f hf (dA f) = 0 := by
  have hD : regular (K := K) (T := T) (dA f) = dT (hf.unit : T) := by
    rw [KaehlerDifferential.map_D, hf.unit_spec]
  change wedge (logarithm (K := K) hf.unit) (regular (K := K) (T := T) (dA f)) = 0
  rw [hD, logarithm]
  change wedgeLeft (dT (hf.unit : T)) ((↑hf.unit⁻¹ : T) • dT (hf.unit : T)) = 0
  rw [map_smul]
  change (↑hf.unit⁻¹ : T) • wedge (dT (hf.unit : T)) (dT (hf.unit : T)) = 0
  rw [wedge_self, smul_zero]

def classMapOne :
    (Ω[A⁄K] ⧸ conormal (K := K) f) →ₗ[A] poleTwo (K := K) (A := A) (T := T) :=
  (conormal (K := K) f).liftQ ((toPoleTwo (K := K) (A := A) (T := T)).comp (lift (K := K) f hf)) (by
    rw [conormal, sup_le_iff, Submodule.span_le]
    constructor
    · rintro _ ⟨ω, rfl⟩
      apply LinearMap.mem_ker.mpr
      change toPoleTwo (K := K) (A := A) (T := T) (lift f hf (f • ω)) = 0
      rw [lift_f_smul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)
    · intro ω hω
      rw [Set.mem_singleton_iff.mp hω]
      apply LinearMap.mem_ker.mpr
      change toPoleTwo (K := K) (A := A) (T := T) (lift f hf (dA f)) = 0
      rw [lift_df, map_zero])

theorem classMapOne_apply (ω : Ω[A⁄K]) :
    classMapOne (K := K) f hf ((conormal (K := K) f).mkQ ω) =
      toPoleTwo (wedge (logarithm (K := K) hf.unit) (regular (K := K) ω)) := rfl

def divisorD : (A ⧸ (Ideal.span {f} : Ideal A)) →+ (Ω[A⁄K] ⧸ conormal (K := K) f) :=
  QuotientAddGroup.lift (show Submodule A A from Ideal.span {f}).toAddSubgroup
    (((conormal (K := K) f).mkQ).toAddMonoidHom.comp (dA).toLinearMap.toAddMonoidHom) (by
    intro a ha
    have ha' : a ∈ Submodule.span A ({f} : Set A) := ha
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha'
    change (conormal (K := K) f).mkQ (dA a) = 0
    rw [← hc, smul_eq_mul, Derivation.leibniz, add_comm]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.add_mem_sup
      (LinearMap.mem_range_self (f • LinearMap.id) (dA c))
      ((Submodule.span A {dA f}).smul_mem c (Submodule.subset_span (by simp))))

theorem divisorD_apply (a : A) :
    divisorD (K := K) f ((Ideal.Quotient.mk (Ideal.span {f})) a) =
      (conormal (K := K) f).mkQ (dA a) := rfl

variable (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A)
  (hu : ∀ i, b i = KaehlerDifferential.D K A (u i))
  (c : Basis (Fin 3) T Ω[T⁄K]) (v : Fin 3 → T)
  (hv : ∀ i, c i = KaehlerDifferential.D K T (v i))

def poleD (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A)
    (hu : ∀ i, b i = KaehlerDifferential.D K A (u i))
    (c : Basis (Fin 3) T Ω[T⁄K]) (v : Fin 3 → T)
    (hv : ∀ i, c i = KaehlerDifferential.D K T (v i)) : poleQuotient (K := K) (A := A) (T := T) →+ poleTwo (K := K) (A := A) (T := T) :=
  QuotientAddGroup.lift (LinearMap.range (regular (K := K) (A := A) (T := T))).toAddSubgroup
    ((toPoleTwo (K := K) (A := A) (T := T)).toAddMonoidHom.comp (differential c)) (by
    rintro _ ⟨ω, rfl⟩
    change toPoleTwo (K := K) (A := A) (T := T) (differential c (regular (K := K) ω)) = 0
    have he := differential_natural b u hu (φ (K := K) (A := A) (T := T)) c v hv ω
    rw [onePullback_regular] at he
    have ea : regularTwo (K := K) (A := A) (T := T) (differential b ω) =
        differential c (regular (K := K) ω) := he
    rw [← ea]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _))

include hu hv in
theorem poleD_apply (ω : Ω[T⁄K]) :
    poleD (K := K) (A := A) (T := T) b u hu c v hv (toPole (K := K) (A := A) (T := T) ω) =
      toPoleTwo (K := K) (A := A) (T := T) (differential c ω) := rfl

include hu hv in
theorem differential_classMap (a : A ⧸ (Ideal.span {f} : Ideal A)) :
    poleD (K := K) (A := A) (T := T) b u hu c v hv (classMap (K := K) f hf a) =
      - classMapOne (K := K) f hf (divisorD f a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [classMap_apply, divisorD_apply, classMapOne_apply, poleD_apply b u hu c v hv]
  rw [← IsScalarTower.algebraMap_smul T, differential_smul]
  have hz : differential c (logarithm (K := K) hf.unit) = 0 := differential_log c v hv hf.unit
  rw [hz, smul_zero, zero_add, wedge_swap (logarithm (K := K) hf.unit), map_neg,
    KaehlerDifferential.map_D]

end CycleQ2PrincipalGysinOneForms

#print axioms CycleQ2PrincipalGysinOneForms.classMapOne
#print axioms CycleQ2PrincipalGysinOneForms.differential_classMap

end

end

section

noncomputable section

/-!
# The actual Kähler module of the principal divisor

The quotient by the equation and its differential is identified with the
ordinary Kähler module of the quotient ring. The map from functions used
in the local logarithmic class is its universal derivation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2PrincipalConormalQuotient

open CycleQ2PrincipalGysinOneForms KaehlerDifferential

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A] (f : A)

abbrev Q := A ⧸ (Ideal.span {f} : Ideal A)
abbrev M := Ω[A⁄K] ⧸ conormal (K := K) f

private abbrev toQ := Ideal.Quotient.mk (Ideal.span {f} : Ideal A)
private abbrev toM := (conormal (K := K) f).mkQ

private theorem torsion : Module.IsTorsionBySet A (M (K := K) f) (Ideal.span {f} : Ideal A) := by
  apply (Module.isTorsionBySet_span_singleton_iff f).mpr
  apply (Module.isTorsionBy_quotient_iff _ f).mpr
  intro x
  exact (show LinearMap.range (f • LinearMap.id : Ω[A⁄K] →ₗ[A] Ω[A⁄K]) ≤ conormal (K := K) f
    from le_sup_left) (LinearMap.mem_range_self _ x)

local instance : Module (Q f) (M (K := K) f) := (torsion (K := K) f).module

local instance : IsScalarTower A (Q f) (M (K := K) f) := (torsion (K := K) f).isScalarTower

local instance : IsScalarTower K (Q f) (M (K := K) f) := (torsion (K := K) f).isScalarTower

private theorem quotient_smul (c : A) (x : M (K := K) f) :
    toQ f c • x = c • x := rfl

/-- The principal quotient derivation on the original cotangent quotient. -/
def derivation : Derivation K (Q f) (M (K := K) f) where
  toFun := divisorD f
  map_add' := (divisorD f).map_add
  map_one_eq_zero' := by
    change divisorD (K := K) f (toQ f 1) = 0
    rw [divisorD_apply, Derivation.map_one_eq_zero, map_zero]
  map_smul' c x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have eq : c • toQ f a = toQ f (c • a) :=
      ((Ideal.Quotient.mkₐ K (Ideal.span {f})).toLinearMap.map_smul c a).symm
    rw [RingHom.id_apply, eq, divisorD_apply, divisorD_apply, (D K A).map_smul,
      (toM (K := K) f).map_smul_of_tower]
  leibniz' x y := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change divisorD (K := K) f (toQ f a * toQ f b) =
      toQ f a • divisorD (K := K) f (toQ f b) + toQ f b • divisorD (K := K) f (toQ f a)
    rw [← map_mul, divisorD_apply, divisorD_apply, divisorD_apply, Derivation.leibniz, map_add,
      quotient_smul, quotient_smul, map_smul, map_smul]

private abbrev ordinaryMap : Ω[A⁄K] →ₗ[A] Ω[Q f⁄K] := KaehlerDifferential.map K K A (Q f)

private theorem ordinaryMap_conormal : conormal (K := K) f ≤ LinearMap.ker (ordinaryMap (K := K) f) := by
  have hz : algebraMap A (Q f) f = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span (by simp))
  rw [conormal, sup_le_iff, Submodule.span_le]
  constructor
  · rintro _ ⟨x,rfl⟩
    apply LinearMap.mem_ker.mpr
    change ordinaryMap (K := K) f (f • x) = 0
    rw [map_smul, ← IsScalarTower.algebraMap_smul (Q f), hz, zero_smul]
  · intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact LinearMap.mem_ker.mpr (by rw [KaehlerDifferential.map_D, hz, map_zero])

def fromQuotient : M (K := K) f →ₗ[A] Ω[Q f⁄K] :=
  (conormal (K := K) f).liftQ (ordinaryMap f) (ordinaryMap_conormal f)

private def inverse : Ω[Q f⁄K] →ₗ[A] M (K := K) f :=
  (derivation (K := K) f).liftKaehlerDifferential.restrictScalars A

private theorem inverse_comp_mk :
    (inverse (K := K) f).comp (ordinaryMap f) = toM f := by
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change inverse (K := K) f (ordinaryMap f (D K A a)) = _
  rw [KaehlerDifferential.map_D]
  change (derivation (K := K) f).liftKaehlerDifferential (D K (Q f) (toQ f a)) = _
  rw [Derivation.liftKaehlerDifferential_comp_D]
  exact divisorD_apply f a

/-- The conormal quotient is the actual module of relative one-forms on the divisor. -/
def cotangentEquiv : M (K := K) f ≃ₗ[A] Ω[Q f⁄K] := by
  apply LinearEquiv.ofBijective (fromQuotient (K := K) f)
  constructor
  · apply Function.LeftInverse.injective (g := inverse f)
    intro x
    obtain ⟨ω, rfl⟩ := (conormal (K := K) f).mkQ_surjective x
    change (inverse f).comp (ordinaryMap f) ω = (toM f) ω
    rw [inverse_comp_mk]
  · have hs : Function.Surjective (ordinaryMap (K := K) f) :=
      KaehlerDifferential.map_surjective_of_surjective K K A (Q f) Ideal.Quotient.mk_surjective
    intro ω
    obtain ⟨α, rfl⟩ := hs ω
    exact ⟨(toM f) α, rfl⟩

theorem cotangentEquiv_divisorD (q : Q f) :
    cotangentEquiv (K := K) f (divisorD f q) = D K (Q f) q := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [divisorD_apply]
  exact KaehlerDifferential.map_D K K A (Q f) a

end CycleQ2PrincipalConormalQuotient

#print axioms CycleQ2PrincipalConormalQuotient.cotangentEquiv
#print axioms CycleQ2PrincipalConormalQuotient.cotangentEquiv_divisorD

end

end

section

noncomputable section

/-!
# The local two-equation class in the localization quotient

The logarithmic wedge is closed. In the quotient by the two single-open
images, multiplying one equation by a unit of the original chart leaves
the class unchanged. Swapping the equations changes its sign.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2DoubleLogarithmicClass

open CycleQ2PrincipalGysinFunctions CycleQ2ExactFrameThreeDeRham
open CycleQ2WeightedCoordinateExterior
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)
open Module KaehlerDifferential

variable {K A U V T : Type} [CommRing K] [CommRing A] [CommRing U] [CommRing V] [CommRing T]
  [Algebra K A] [Algebra K U] [Algebra K V] [Algebra K T]

/-- The wedge of the logarithmic derivatives of two units. -/
def twoLog (f g : Tˣ) : Form K T 2 :=
  wedge (logarithm (K := K) f) (logarithm (K := K) g)

theorem onePullback_log {B : Type} [CommRing B] [Algebra K B] (φ : B →ₐ[K] T) (f : Bˣ) :
    onePullback φ (logarithm (K := K) f) = logarithm (K := K) (Units.map φ.toRingHom f) := by
  rw [logarithm, map_smulₛₗ, onePullback_d, logarithm]
  rfl

theorem pullback_twoLog {B : Type} [CommRing B] [Algebra K B] (φ : B →ₐ[K] T) (f g : Bˣ) :
    exteriorPullback φ 2 (twoLog (K := K) f g) =
      twoLog (K := K) (Units.map φ.toRingHom f) (Units.map φ.toRingHom g) := by
  unfold twoLog wedge
  rw [exteriorPullback, exteriorMap_wedge]
  apply congrArg (exteriorPower.ιMulti T 2)
  funext i
  fin_cases i
  · exact onePullback_log φ f
  · exact onePullback_log φ g

theorem twoLog_swap (f g : Tˣ) :
    twoLog (K := K) g f = -twoLog (K := K) f g :=
  wedge_swap _ _

theorem twoLog_mul_left (f₁ f₂ g : Tˣ) :
    twoLog (K := K) (f₁ * f₂) g = twoLog (K := K) f₁ g + twoLog (K := K) f₂ g := by
  rw [twoLog,logarithm_mul]
  exact (wedgeLeft (logarithm (K := K) g)).map_add _ _

theorem twoLog_mul_right (f g₁ g₂ : Tˣ) :
    twoLog (K := K) f (g₁ * g₂) = twoLog (K := K) f g₁ + twoLog (K := K) f g₂ := by
  rw [twoLog,logarithm_mul]
  exact (wedgeRight (logarithm (K := K) f)).map_add _ _

/-- The two-log cochain itself is closed in the actual relative complex. -/
theorem closed (b : Basis (Fin 3) T Ω[T⁄K])
    (u : Fin 3 → T) (hu : ∀ i, b i = D K T (u i)) (f g : Tˣ) :
    exteriorD2 b (exactFrameDirection b) (twoLog (K := K) f g) = 0 := by
  have h : twoLog (K := K) f g = ((↑f⁻¹ : T) * (↑g⁻¹ : T)) •
      exteriorPower.ιMulti T 2 (D K T ∘ ![(f : T),(g : T)]) := by
    change wedgeLeft ((↑g⁻¹ : T) • D K T (g : T)) ((↑f⁻¹ : T) • D K T (f : T)) = _
    rw [map_smul]
    change (↑f⁻¹ : T) • wedgeRight (D K T (f : T)) ((↑g⁻¹ : T) • D K T (g : T)) = _
    rw [map_smul, smul_smul]
    rfl
  rw [h, exteriorD2_exactFrame b u hu]
  have hdF : D K T (↑f⁻¹ : T) = -((↑f⁻¹ : T) ^ 2) • D K T (f : T) :=
    (D K T).leibniz_of_mul_eq_one (by simp)
  have hdG : D K T (↑g⁻¹ : T) = -((↑g⁻¹ : T) ^ 2) • D K T (g : T) :=
    (D K T).leibniz_of_mul_eq_one (by simp)
  let e : (Ω[T⁄K]) [⋀^Fin 3]→ₗ[T] Form K T 3 := exteriorPower.ιMulti T 3
  change e ![D K T ((↑f⁻¹ : T) * (↑g⁻¹ : T)), D K T (f : T), D K T (g : T)] = 0
  rw [Derivation.leibniz, hdF, hdG, smul_smul, smul_smul]
  rw [e.map_vecCons_add ![D K T (f : T),D K T (g : T)], e.map_vecCons_smul,
    e.map_vecCons_smul]
  have hg : e ![D K T (g : T),D K T (f : T),D K T (g : T)] = 0 :=
    e.map_eq_zero_of_eq _ (by rfl : ![D K T (g : T),D K T (f : T),D K T (g : T)] (0 : Fin 3) =
      ![D K T (g : T),D K T (f : T),D K T (g : T)] 2) (by decide)
  have hf : e ![D K T (f : T),D K T (f : T),D K T (g : T)] = 0 :=
    e.map_eq_zero_of_eq _ (by rfl : ![D K T (f : T),D K T (f : T),D K T (g : T)] (0 : Fin 3) =
      ![D K T (f : T),D K T (f : T),D K T (g : T)] 1) (by decide)
  rw [hg,hf,smul_zero,smul_zero,add_zero]

variable (φ : U →ₐ[K] T) (ψ : V →ₐ[K] T)

private abbrev images : AddSubgroup (Form K T 2) :=
  (exteriorPullback φ 2).toAddMonoidHom.range ⊔ (exteriorPullback ψ 2).toAddMonoidHom.range

/-- The degree-two localization quotient by the two single-open images. -/
abbrev supportQuotient := Form K T 2 ⧸ images φ ψ

def localClass (f g : Tˣ) : supportQuotient φ ψ :=
  QuotientAddGroup.mk' (images φ ψ) (twoLog (K := K) f g)

theorem localClass_first_unit (f : Tˣ) (g q : Vˣ) :
    localClass φ ψ (Units.map ψ.toRingHom q * f) (Units.map ψ.toRingHom g) =
      localClass φ ψ f (Units.map ψ.toRingHom g) := by
  unfold localClass
  rw [twoLog_mul_left,map_add]
  have hz : QuotientAddGroup.mk' (images φ ψ)
      (twoLog (K := K) (Units.map ψ.toRingHom q) (Units.map ψ.toRingHom g)) = 0 := by
    rw [← pullback_twoLog]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact (show (exteriorPullback ψ 2).toAddMonoidHom.range ≤ images φ ψ from le_sup_right)
      ⟨twoLog (K := K) q g, rfl⟩
  rw [hz,zero_add]

theorem localClass_second_unit (f q : Uˣ) (g : Tˣ) :
    localClass φ ψ (Units.map φ.toRingHom f) (Units.map φ.toRingHom q * g) =
      localClass φ ψ (Units.map φ.toRingHom f) g := by
  unfold localClass
  rw [twoLog_mul_right,map_add]
  have hz : QuotientAddGroup.mk' (images φ ψ)
      (twoLog (K := K) (Units.map φ.toRingHom f) (Units.map φ.toRingHom q)) = 0 := by
    rw [← pullback_twoLog]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact (show (exteriorPullback φ 2).toAddMonoidHom.range ≤ images φ ψ from le_sup_left)
      ⟨twoLog (K := K) f q, rfl⟩
  rw [hz,zero_add]

end CycleQ2DoubleLogarithmicClass

#print axioms CycleQ2DoubleLogarithmicClass.closed
#print axioms CycleQ2DoubleLogarithmicClass.localClass_first_unit
#print axioms CycleQ2DoubleLogarithmicClass.localClass_second_unit

end

end

section

noncomputable section

/-!
# Binding the local two-equation class to the original localizations

For actual equations f and g, the two restriction maps are those of
localization away from f and g into localization away from fg.
The logarithmic class is the image of a closed ordinary two-form
on the double localization. Units on the original affine chart
give the checked equation-change identities in this quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2NativeDoubleLocalization

open CycleQ2DoubleLogarithmicClass CycleQ2RelativeAffineOverlap
open CycleQ2WeightedCoordinateExterior Module KaehlerDifferential

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A] (f g : A)

abbrev U := Localization.Away f
abbrev V := Localization.Away g
abbrev T := Localization.Away (f * g)

private theorem fUnit : IsUnit (algebraMap A (T f g) f) :=
  IsLocalization.Away.isUnit_of_dvd (f * g) (dvd_mul_right f g)

private theorem gUnit : IsUnit (algebraMap A (T f g) g) :=
  IsLocalization.Away.isUnit_of_dvd (f * g) (dvd_mul_left g f)

def fromU : U f →ₐ[K] T f g :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom K A (T f g)) f (fUnit f g)

def fromV : V g →ₐ[K] T f g :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom K A (T f g)) g (gUnit f g)

private theorem fromU_algebraMap (a : A) :
    fromU (K := K) f g (algebraMap A (U f) a) = algebraMap A (T f g) a :=
  IsLocalization.Away.lift_eq (S := U f) (g := algebraMap A (T f g)) f (fUnit f g) a

private theorem fromV_algebraMap (a : A) :
    fromV (K := K) f g (algebraMap A (V g) a) = algebraMap A (T f g) a :=
  IsLocalization.Away.lift_eq (S := V g) (g := algebraMap A (T f g)) g (gUnit f g) a

private def uf : (U f)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit f).unit

private def ug : (V g)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit g).unit

def localizedF : (T f g)ˣ := Units.map (fromU (K := K) f g).toRingHom (uf f)
def localizedG : (T f g)ˣ := Units.map (fromV (K := K) f g).toRingHom (ug g)

theorem localizedF_val : (localizedF (K := K) f g : T f g) = algebraMap A (T f g) f := by
  change fromU (K := K) f g (↑(uf f) : U f) = _
  rw [uf, IsUnit.unit_spec]
  exact fromU_algebraMap f g _

theorem localizedG_val : (localizedG (K := K) f g : T f g) = algebraMap A (T f g) g := by
  change fromV (K := K) f g (↑(ug g) : V g) = _
  rw [ug, IsUnit.unit_spec]
  exact fromV_algebraMap f g _

def cochain : Form K (T f g) 2 := twoLog (K := K) (localizedF (K := K) f g) (localizedG (K := K) f g)

def supportClass : supportQuotient (fromU (K := K) f g) (fromV (K := K) f g) :=
  localClass (fromU (K := K) f g) (fromV (K := K) f g) (localizedF (K := K) f g) (localizedG (K := K) f g)

local instance : Algebra.FormallyEtale A (T f g) :=
  Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (f * g))

theorem cochain_closed (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hu : ∀ i, b i = D K A (u i)) :
    exteriorD2 (baseChangeFrame b) (exactFrameDirection (baseChangeFrame b)) (cochain (K := K) f g) = 0 :=
  closed (baseChangeFrame b) (fun i => algebraMap A (T f g) (u i)) (baseChangeFrame_apply b u hu) _ _

theorem first_equation_unit (a : Aˣ) :
    localClass (fromU (K := K) f g) (fromV (K := K) f g)
      (Units.map (algebraMap A (T f g)).toMonoidHom a * localizedF (K := K) f g) (localizedG (K := K) f g) =
      supportClass (K := K) f g := by
  have he : Units.map (fromV (K := K) f g).toRingHom (Units.map (algebraMap A (V g)).toMonoidHom a) =
      Units.map (algebraMap A (T f g)).toMonoidHom a := by
    apply Units.ext
    exact fromV_algebraMap f g _
  rw [← he]
  exact localClass_first_unit _ _ _ _ _

theorem second_equation_unit (a : Aˣ) :
    localClass (fromU (K := K) f g) (fromV (K := K) f g)
      (localizedF (K := K) f g) (Units.map (algebraMap A (T f g)).toMonoidHom a * localizedG (K := K) f g) =
      supportClass (K := K) f g := by
  have he : Units.map (fromU (K := K) f g).toRingHom (Units.map (algebraMap A (U f)).toMonoidHom a) =
      Units.map (algebraMap A (T f g)).toMonoidHom a := by
    apply Units.ext
    exact fromU_algebraMap f g _
  rw [← he]
  exact localClass_second_unit _ _ _ _ _

end CycleQ2NativeDoubleLocalization

#print axioms CycleQ2NativeDoubleLocalization.cochain_closed
#print axioms CycleQ2NativeDoubleLocalization.first_equation_unit
#print axioms CycleQ2NativeDoubleLocalization.second_equation_unit

end

end

section

/-!
# The exact correction for changing a coefficient lift on top forms

For a relative derivation, the contraction of the volume is the signed
two-form with its coordinate velocities. Its ordinary differential is
the Lie derivative of a top form. Consequently two coefficient lifts
of the same base derivation differ on top forms by an explicit
ordinary boundary.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2RelativeTopCartan

open Module KaehlerDifferential
open CycleQ2WeightedCoordinateExterior CycleQ2RelativeDerivationLift

variable {k K A : Type} [CommRing k] [CommRing K] [CommRing A]
  [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
variable (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A)
  (hu : ∀ i, b i = D K A (u i))

variable (v : Derivation K A A)

def contraction (a : A) : Form K A 2 :=
  (twoBasis b).equivFun.symm (fun i => (-1 : A) ^ i.val * (a * v (u i)))

theorem signedCoefficients_contraction (a : A) (i : Fin 3) :
    signedCoefficients b (contraction b u v a) i = a * v (u i) := by
  have he : (twoBasis b).repr (contraction b u v a) i = (-1 : A) ^ i.val * (a * v (u i)) :=
    Basis.coord_equivFun_symm (twoBasis b) i _
  rw [signedCoefficients, he, ← mul_assoc, ← pow_add,
    show i.val + i.val = 2 * i.val by omega, pow_mul]
  simp

include hu in
theorem relative_direction_decompose (a : A) :
    v a = ∑ i, v (u i) * exactFrameDirection b i a := by
  have h := congrArg v.liftKaehlerDifferential (b.sum_repr (D K A a))
  simp only [map_sum, map_smul, hu, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [exactFrameDirection_apply, mul_comm]

include hu in
theorem derivative_contraction (a : A) :
    exteriorD2 b (exactFrameDirection b) (contraction b u v a) =
      (v a + a * ∑ i, exactFrameDirection b i (v (u i))) • volume b := by
  rw [exteriorD2_divergence, relative_direction_decompose b u hu v a]
  apply congrArg (fun z : A => z • volume b)
  simp only [signedCoefficients_contraction, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ac_rfl

/-- Lie differentiation of a top form in an exact frame along a
derivation lifting a coefficient derivation. -/
def topLie (d : Derivation k A A) (a : A) : Form K A 3 :=
  (d a + a * ∑ i, exactFrameDirection b i (d (u i))) • volume b

theorem topLie_fixed_coordinates (d : Derivation k A A) (h : ∀ i, d (u i) = 0) (a : A) :
    topLie b u d a = d a • volume b := by
  simp [topLie,h]

include hu in
theorem difference_is_boundary (d e : Derivation k A A)
    (h : ∀ x : K, d (algebraMap K A x) = e (algebraMap K A x)) (a : A) :
    topLie b u d a - topLie b u e a =
      exteriorD2 b (exactFrameDirection b)
        (contraction b u (asRelative (d-e) (by intro x; change d _ - e _ = 0; rw [h,sub_self])) a) := by
  rw [derivative_contraction b u hu]
  unfold topLie
  erw [← sub_smul]
  apply congrArg (fun z : A => z • volume b)
  change (d a + a * ∑ i, exactFrameDirection b i (d (u i))) -
      (e a + a * ∑ i, exactFrameDirection b i (e (u i))) =
    d a - e a + a * ∑ i, exactFrameDirection b i (d (u i) - e (u i))
  simp only [map_sub, Finset.sum_sub_distrib, mul_sub]
  ring

end CycleQ2RelativeTopCartan

#print axioms CycleQ2RelativeTopCartan.derivative_contraction
#print axioms CycleQ2RelativeTopCartan.difference_is_boundary

end

section

/-!
# Functoriality and independence of the exact frame

The cochain maps on affine de Rham complexes compose as their original
algebra maps do. The identity algebra map gives the canonical comparison
between two presentations by exact coordinates of the same ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2AffineDeRhamFunctorial

open CategoryTheory Module
open CycleQ2ExactFrameThreeDeRham CycleQ2AffineDeRhamComplex
open CycleQ2GeometricExteriorSheaf
open CycleQ2WeightedCoordinateExterior

variable {K A B C : Type} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]

theorem onePullback_id (ω : Ω[A⁄K]) :
    onePullback (AlgHom.id K A) ω = ω := by
  have h : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction h using Submodule.span_induction with
  | mem ω h =>
    obtain ⟨a,rfl⟩ := h
    exact onePullback_d _ a
  | zero => exact map_zero _
  | add a b _ _ ha hb => rw [map_add,ha,hb]
  | smul a ω _ h => rw [map_smulₛₗ,h]; rfl

theorem onePullback_comp (f : A →ₐ[K] B) (g : B →ₐ[K] C) (ω : Ω[A⁄K]) :
    onePullback (g.comp f) ω = onePullback g (onePullback f ω) := by
  have h : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D K A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction h using Submodule.span_induction with
  | mem ω h =>
    obtain ⟨a,rfl⟩ := h
    rw [onePullback_d, onePullback_d, onePullback_d]
    rfl
  | zero => simp only [map_zero]
  | add a b _ _ ha hb => simp only [map_add,ha,hb]
  | smul a ω _ h => rw [map_smulₛₗ,map_smulₛₗ,map_smulₛₗ,h]; rfl

theorem exteriorPullback_id (p : ℕ) (ω : Form K A p) :
    exteriorPullback (AlgHom.id K A) p ω = ω :=
  exteriorMap_identity _ _ (fun _ => rfl) onePullback_id p ω

theorem exteriorPullback_comp (f : A →ₐ[K] B) (g : B →ₐ[K] C) (p : ℕ) (ω : Form K A p) :
    exteriorPullback (g.comp f) p ω = exteriorPullback g p (exteriorPullback f p ω) :=
  exteriorMap_composition _ _ _ _ _ _ (fun _ => rfl) (onePullback_comp f g) p ω

theorem pullDegree_id : ∀ p, pullDegree (AlgHom.id K A) p = 𝟙 (degree K A p)
  | 0 => rfl
  | 1 => by
    ext ω
    exact onePullback_id ω
  | 2 => by
    ext ω
    exact exteriorPullback_id 2 ω
  | 3 => by
    ext ω
    exact exteriorPullback_id 3 ω
  | _ + 4 => by
    ext ω
    change (_ : PUnit) = _
    exact Subsingleton.elim _ _

theorem pullDegree_comp (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    ∀ p, pullDegree (g.comp f) p = pullDegree f p ≫ pullDegree g p
  | 0 => rfl
  | 1 => by
    ext ω
    exact onePullback_comp f g ω
  | 2 => by
    ext ω
    exact exteriorPullback_comp f g 2 ω
  | 3 => by
    ext ω
    exact exteriorPullback_comp f g 3 ω
  | _ + 4 => by
    ext ω
    change (_ : PUnit) = _
    exact Subsingleton.elim _ _

variable (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A)
  (hu : ∀ i, b i = KaehlerDifferential.D K A (u i))
variable (c : Basis (Fin 3) B Ω[B⁄K]) (v : Fin 3 → B)
  (hv : ∀ i, c i = KaehlerDifferential.D K B (v i))
variable (d : Basis (Fin 3) C Ω[C⁄K]) (w : Fin 3 → C)
  (hw : ∀ i, d i = KaehlerDifferential.D K C (w i))

include hu in
theorem pullComplex_id :
    pullComplex b u hu (AlgHom.id K A) b u hu = 𝟙 (complex b u hu) := by
  ext p : 1
  exact pullDegree_id p

include hu hv hw in
theorem pullComplex_comp (f : A →ₐ[K] B) (g : B →ₐ[K] C) :
    pullComplex b u hu (g.comp f) d w hw =
      pullComplex b u hu f c v hv ≫ pullComplex c v hv g d w hw := by
  ext p : 1
  exact pullDegree_comp f g p

variable (b' : Basis (Fin 3) A Ω[A⁄K]) (u' : Fin 3 → A)
  (hu' : ∀ i, b' i = KaehlerDifferential.D K A (u' i))

/-- Both directions are induced by the identity on the actual functions. -/
def frameIso : complex b u hu ≅ complex b' u' hu' where
  hom := pullComplex b u hu (AlgHom.id K A) b' u' hu'
  inv := pullComplex b' u' hu' (AlgHom.id K A) b u hu
  hom_inv_id := by
    rw [← pullComplex_comp, AlgHom.comp_id, pullComplex_id]
  inv_hom_id := by
    rw [← pullComplex_comp, AlgHom.comp_id, pullComplex_id]

end CycleQ2AffineDeRhamFunctorial

#print axioms CycleQ2AffineDeRhamFunctorial.pullComplex_comp
#print axioms CycleQ2AffineDeRhamFunctorial.frameIso

end

section

/-!
# A triangular change in an actual two-equation residue

On the common refinement, replacing g by g + af changes the two-log
cochain by a form defined where g and g + af are both invertible.
Thus the change is a boundary in the localization quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2LogarithmicGeneratorChange

open CycleQ2DoubleLogarithmicClass CycleQ2PrincipalGysinFunctions
open CycleQ2ExactFrameThreeDeRham CycleQ2WeightedCoordinateExterior
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)
open KaehlerDifferential

variable {K T : Type} [CommRing K] [CommRing T] [Algebra K T]

local notation "dT" => D K T

private theorem scaledWedge (x y : Ω[T⁄K]) (a b : T) :
    wedge (a • x) (b • y) = (a * b) • wedge x y := by
  change wedgeLeft (b • y) (a • x) = _
  rw [map_smul]
  change a • wedgeRight x (b • y) = _
  rw [map_smul, smul_smul]
  rfl

private theorem wedge_add_right (x y z : Ω[T⁄K]) :
    wedge x (y+z) = wedge x y + wedge x z := (wedgeRight x).map_add y z

private theorem wedge_smul_right (x y : Ω[T⁄K]) (a : T) :
    wedge x (a • y) = a • wedge x y := (wedgeRight x).map_smul a y

private theorem coefficients (f g h : Tˣ) (a : T) (he : (h : T) = (g : T) + a * (f : T)) :
    (↑f⁻¹ : T) * (↑h⁻¹ : T) - (↑f⁻¹ : T) * (↑g⁻¹ : T) =
      -(a * (↑g⁻¹ : T) * (↑h⁻¹ : T)) := by
  have e₁ : (↑g⁻¹ : T) * (↑h⁻¹ : T) * (h : T) = (↑g⁻¹ : T) := by
    rw [mul_assoc, Units.inv_mul, mul_one]
  have e₂ : (↑g⁻¹ : T) * (↑h⁻¹ : T) * (g : T) = (↑h⁻¹ : T) := by
    rw [mul_comm (↑g⁻¹ : T), mul_assoc, Units.inv_mul, mul_one]
  have e₃ : (↑f⁻¹ : T) * (f : T) = 1 := Units.inv_mul f
  linear_combination (↑f⁻¹ : T) * e₁ - (↑f⁻¹ : T) * e₂ -
    (↑f⁻¹ : T) * (↑g⁻¹ : T) * (↑h⁻¹ : T) * he - a * (↑g⁻¹ : T) * (↑h⁻¹ : T) * e₃

/-- The change uses no inverse of the unchanged equation on its right. -/
theorem twoLog_shear (f g h : Tˣ) (a : T) (he : (h : T) = (g : T) + a * (f : T)) :
    twoLog (K := K) f h - twoLog (K := K) f g =
      (↑h⁻¹ : T) • wedge (dT (f : T)) (dT a) -
      (a * (↑g⁻¹ : T) * (↑h⁻¹ : T)) • wedge (dT (f : T)) (dT (g : T)) := by
  let x := dT (f : T)
  let y := dT (g : T)
  let z := dT a
  have hd : dT (h : T) = y + (a • x + (f : T) • z) := by
    rw [he, map_add, Derivation.leibniz]
  have hc : (↑f⁻¹ : T) * (↑h⁻¹ : T) * (f : T) = (↑h⁻¹ : T) := by
    rw [mul_comm (↑f⁻¹ : T), mul_assoc, Units.inv_mul, mul_one]
  rw [twoLog, twoLog, logarithm, logarithm, logarithm,
    scaledWedge, scaledWedge, hd, wedge_add_right, wedge_add_right,
    wedge_smul_right, wedge_smul_right]
  change ((↑f⁻¹ : T) * (↑h⁻¹ : T)) •
      (wedge x y + (a • wedge x x + (f : T) • wedge x z)) -
    ((↑f⁻¹ : T) * (↑g⁻¹ : T)) • wedge x y = _
  rw [wedge_self, smul_zero, zero_add, smul_add, smul_smul, hc, add_comm,
    add_sub_assoc, ← sub_smul, coefficients f g h a he, neg_smul, sub_eq_add_neg]

private theorem pullback_wedge {B : Type} [CommRing B] [Algebra K B] (φ : B →ₐ[K] T)
    (x y : Ω[B⁄K]) :
    exteriorPullback φ 2 (wedge x y) = wedge (onePullback φ x) (onePullback φ y) := by
  unfold exteriorPullback wedge
  rw [exteriorMap_wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

variable {B C : Type} [CommRing B] [CommRing C] [Algebra K B] [Algebra K C]
  (φ : B →ₐ[K] T) (ψ : C →ₐ[K] T)

/-- The two Čech representatives agree on a common refinement whose
second open inverts both old and new second equations. -/
theorem localClass_shear (f g h : Tˣ) (a₀ f₀ : C) (g₀ h₀ : Cˣ)
    (hf : ψ f₀ = (f : T)) (hg : Units.map ψ.toRingHom g₀ = g)
    (hh : Units.map ψ.toRingHom h₀ = h)
    (he : (h : T) = (g : T) + ψ a₀ * (f : T)) :
    localClass φ ψ f h = localClass φ ψ f g := by
  let dC := D K C
  let correction : Form K C 2 :=
    (↑h₀⁻¹ : C) • wedge (dC f₀) (dC a₀) -
    (a₀ * (↑g₀⁻¹ : C) * (↑h₀⁻¹ : C)) • wedge (dC f₀) (dC (g₀ : C))
  have hc : exteriorPullback ψ 2 correction = twoLog (K := K) f h - twoLog (K := K) f g := by
    rw [twoLog_shear f g h (ψ a₀) he]
    have hg' : ψ (g₀ : C) = (g : T) := congrArg Units.val hg
    have hg'' : ψ (↑g₀⁻¹ : C) = (↑g⁻¹ : T) := congrArg (fun u : Tˣ => (↑u⁻¹ : T)) hg
    have hh'' : ψ (↑h₀⁻¹ : C) = (↑h⁻¹ : T) := congrArg (fun u : Tˣ => (↑u⁻¹ : T)) hh
    dsimp only [correction, dC]
    rw [map_sub, map_smulₛₗ, map_smulₛₗ, pullback_wedge, pullback_wedge]
    simp only [onePullback_d]
    change ψ (↑h₀⁻¹ : C) • wedge (dT (ψ f₀)) (dT (ψ a₀)) -
      ψ (a₀ * (↑g₀⁻¹ : C) * (↑h₀⁻¹ : C)) • wedge (dT (ψ f₀)) (dT (ψ (g₀ : C))) = _
    rw [map_mul, map_mul, hf, hg', hg'', hh'']
  rw [← sub_eq_zero]
  change QuotientAddGroup.mk' _ (twoLog (K := K) f h) - QuotientAddGroup.mk' _ (twoLog (K := K) f g) = 0
  rw [← map_sub, ← hc]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact (show (exteriorPullback ψ 2).toAddMonoidHom.range ≤ _ from le_sup_right) ⟨correction, rfl⟩

end CycleQ2LogarithmicGeneratorChange

#print axioms CycleQ2LogarithmicGeneratorChange.twoLog_shear
#print axioms CycleQ2LogarithmicGeneratorChange.localClass_shear

end

section

/-!
# The triangular change on the original localization intersections

The two original cocycles compare after restriction from D(fg) and
D(fh) to D(fgh). Their correction comes from D(gh), so the comparison
uses the ordinary Čech localization maps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2NativeGeneratorChange

open CycleQ2DoubleLogarithmicClass CycleQ2NativeDoubleLocalization
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2LogarithmicGeneratorChange

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A] (f g h : A)

private abbrev R := Localization.Away (g * h)
private abbrev S := Localization.Away (f * (g * h))
private abbrev φ := fromU (K := K) f (g * h)
private abbrev ψ := fromV (K := K) f (g * h)

private def gR : (R g h)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := R g h) (g * h) (dvd_mul_right g h)).unit

private def hR : (R g h)ˣ :=
  (IsLocalization.Away.isUnit_of_dvd (S := R g h) (g * h) (dvd_mul_left h g)).unit

private theorem ψ_algebra (a : A) : ψ (K := K) f g h (algebraMap A (R g h) a) = algebraMap A (S f g h) a :=
  IsLocalization.Away.lift_eq (S := R g h) (g := algebraMap A (S f g h)) (g * h)
    (IsLocalization.Away.isUnit_of_dvd (f * (g * h)) (dvd_mul_left (g * h) f)) a

private abbrev F : (S f g h)ˣ := localizedF (K := K) f (g * h)
private abbrev G : (S f g h)ˣ := Units.map (ψ (K := K) f g h).toRingHom (gR g h)
private abbrev H : (S f g h)ˣ := Units.map (ψ (K := K) f g h).toRingHom (hR g h)

private theorem F_val : (F (K := K) f g h : S f g h) = algebraMap A (S f g h) f :=
  localizedF_val f (g * h)

private theorem G_val : (G (K := K) f g h : S f g h) = algebraMap A (S f g h) g := by
  change ψ (K := K) f g h (↑(gR g h) : R g h) = _
  rw [gR, IsUnit.unit_spec, ψ_algebra]

private theorem H_val : (H (K := K) f g h : S f g h) = algebraMap A (S f g h) h := by
  change ψ (K := K) f g h (↑(hR g h) : R g h) = _
  rw [hR, IsUnit.unit_spec, ψ_algebra]

def refinement (q : A) (hq : q ∣ g * h) :
    Localization.Away (f * q) →ₐ[K] S f g h :=
  IsLocalization.Away.liftAlgHom (f := IsScalarTower.toAlgHom K A (S f g h)) (f * q)
    (IsLocalization.Away.isUnit_of_dvd (f * (g * h))
      (mul_dvd_mul_left f hq))

private theorem refinement_algebra (q : A) (hq : q ∣ g * h) (a : A) :
    refinement (K := K) f g h q hq (algebraMap A (Localization.Away (f * q)) a) =
      algebraMap A (S f g h) a :=
  IsLocalization.Away.lift_eq (S := Localization.Away (f * q))
    (g := algebraMap A (S f g h)) (f * q)
    (IsLocalization.Away.isUnit_of_dvd (f * (g * h)) (mul_dvd_mul_left f hq)) a

private theorem refine_cochain (q : A) (hq : q ∣ g * h) (u : (S f g h)ˣ)
    (hu : (u : S f g h) = algebraMap A (S f g h) q) :
    exteriorPullback (refinement (K := K) f g h q hq) 2 (cochain (K := K) f q) =
      twoLog (K := K) (F (K := K) f g h) u := by
  let r := refinement (K := K) f g h q hq
  have e₁ : Units.map r.toRingHom (localizedF (K := K) f q) = F (K := K) f g h := by
    apply Units.ext
    change r (localizedF (K := K) f q : Localization.Away (f*q)) = (F (K := K) f g h : S f g h)
    rw [localizedF_val, refinement_algebra, F_val]
  have e₂ : Units.map r.toRingHom (localizedG (K := K) f q) = u := by
    apply Units.ext
    change r (localizedG (K := K) f q : Localization.Away (f*q)) = (u : S f g h)
    rw [localizedG_val, refinement_algebra, hu]
  unfold cochain
  rw [pullback_twoLog, show refinement (K := K) f g h q hq = r from rfl, e₁, e₂]

/-- The restrictions of the original cochains yield equal classes
modulo the two single-open images in the common refinement. -/
theorem same_class (a : A) (he : h = g + a * f) :
    let Q := supportQuotient (φ (K := K) f g h) (ψ (K := K) f g h)
    (↑(exteriorPullback (refinement (K := K) f g h h (dvd_mul_left h g)) 2 (cochain (K := K) f h)) : Q) =
      (↑(exteriorPullback (refinement (K := K) f g h g (dvd_mul_right g h)) 2 (cochain (K := K) f g)) : Q) := by
  dsimp only
  rw [refine_cochain f g h h _ (H (K := K) f g h) (H_val f g h),
    refine_cochain f g h g _ (G (K := K) f g h) (G_val f g h)]
  apply localClass_shear (φ (K := K) f g h) (ψ (K := K) f g h)
    (F (K := K) f g h) (G (K := K) f g h) (H (K := K) f g h)
    (algebraMap A (R g h) a) (algebraMap A (R g h) f) (gR g h) (hR g h)
  · rw [ψ_algebra, F_val]
  · rfl
  · rfl
  · rw [ψ_algebra, F_val, G_val, H_val, ← map_mul, ← map_add, ← he]

end CycleQ2NativeGeneratorChange

#print axioms CycleQ2NativeGeneratorChange.same_class

end

section

/-!
# Frame-independent contraction on ordinary relative forms

Contraction with a relative derivation is defined by the alternating
universal property. Its two- and three-form values therefore commute
with restriction and do not require any choice of coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2CartanContraction

open KaehlerDifferential CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]

private abbrev M := Ω[A⁄K]
variable (v : Derivation K A A)

abbrev one : Ω[A⁄K] →ₗ[A] A := v.liftKaehlerDifferential

private theorem wedge_add_left (x y z : Ω[A⁄K]) : wedge (x+y) z = wedge x z + wedge y z :=
  (wedgeLeft z).map_add x y
private theorem wedge_add_right (x y z : Ω[A⁄K]) : wedge x (y+z) = wedge x y + wedge x z :=
  (wedgeRight x).map_add y z
private theorem wedge_smul_left (a : A) (x y : Ω[A⁄K]) : wedge (a • x) y = a • wedge x y :=
  (wedgeLeft y).map_smul a x
private theorem wedge_smul_right (a : A) (x y : Ω[A⁄K]) : wedge x (a • y) = a • wedge x y :=
  (wedgeRight x).map_smul a y

private def twoAlt : (M (K := K) (A := A)) [⋀^Fin 2]→ₗ[A] M (K := K) (A := A) where
  toFun t := one v (t 0) • t 1 - one v (t 1) • t 0
  map_update_add' t i x y := by
    fin_cases i <;>
      simp [add_smul, smul_add] <;> abel
  map_update_smul' t i a x := by
    fin_cases i <;> simp [smul_sub, smul_smul, mul_comm]
  map_eq_zero_of_eq' t i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change t 0 = t 1 at hij
      rw [hij, sub_self]
    · change t 1 = t 0 at hij
      rw [hij, sub_self]
    · exact (hne rfl).elim

def two : Form K A 2 →ₗ[A] Ω[A⁄K] := exteriorPower.alternatingMapLinearEquiv (twoAlt v)

theorem two_wedge (x y : Ω[A⁄K]) : two v (wedge x y) = one v x • y - one v y • x := by
  rw [wedge, two, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

private theorem three_values (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

private def threeAlt : (M (K := K) (A := A)) [⋀^Fin 3]→ₗ[A] Form K A 2 where
  toFun t := one v (t 0) • wedge (t 1) (t 2) - one v (t 1) • wedge (t 0) (t 2) +
    one v (t 2) • wedge (t 0) (t 1)
  map_update_add' t i x y := by
    have h01 : (0 : Fin 3) ≠ 1 := by omega
    have h02 : (0 : Fin 3) ≠ 2 := by omega
    have h12 : (1 : Fin 3) ≠ 2 := by omega
    obtain rfl | rfl | rfl := three_values i <;>
      simp only [Function.update_self, Function.update_of_ne h01, Function.update_of_ne h01.symm,
        Function.update_of_ne h02, Function.update_of_ne h02.symm,
        Function.update_of_ne h12, Function.update_of_ne h12.symm,
        map_add, add_smul, smul_add, wedge_add_left, wedge_add_right] <;> abel
  map_update_smul' t i a x := by
    have h01 : (0 : Fin 3) ≠ 1 := by omega
    have h02 : (0 : Fin 3) ≠ 2 := by omega
    have h12 : (1 : Fin 3) ≠ 2 := by omega
    obtain rfl | rfl | rfl := three_values i <;>
      simp only [Function.update_self, Function.update_of_ne h01, Function.update_of_ne h01.symm,
        Function.update_of_ne h02, Function.update_of_ne h02.symm,
        Function.update_of_ne h12, Function.update_of_ne h12.symm,
        map_smul, smul_eq_mul, smul_sub, smul_add, smul_smul, mul_comm,
        wedge_smul_left,wedge_smul_right]
  map_eq_zero_of_eq' t i j hij hne := by
    fin_cases i <;> fin_cases j
    · exact (hne rfl).elim
    · change t 0 = t 1 at hij
      rw [hij, wedge_self, smul_zero, sub_self, add_zero]
    · change t 0 = t 2 at hij
      rw [hij, wedge_self, smul_zero, sub_zero, wedge_swap (t 1) (t 2), smul_neg, add_neg_cancel]
    · change t 1 = t 0 at hij
      rw [hij, wedge_self, smul_zero, sub_self, add_zero]
    · exact (hne rfl).elim
    · change t 1 = t 2 at hij
      rw [hij, wedge_self, smul_zero, zero_sub, neg_add_cancel]
    · change t 2 = t 0 at hij
      rw [hij, wedge_self, smul_zero, sub_zero, wedge_swap (t 0) (t 1), smul_neg, neg_add_cancel]
    · change t 2 = t 1 at hij
      rw [hij, wedge_self, smul_zero, zero_sub, neg_add_cancel]
    · exact (hne rfl).elim

def three : Form K A 3 →ₗ[A] Form K A 2 := exteriorPower.alternatingMapLinearEquiv (threeAlt v)

theorem three_wedge (x y z : Ω[A⁄K]) :
    three v (exteriorPower.ιMulti A 3 ![x,y,z]) =
      one v x • wedge y z - one v y • wedge x z + one v z • wedge x y := by
  rw [three, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

end CycleQ2CartanContraction

#print axioms CycleQ2CartanContraction.two_wedge
#print axioms CycleQ2CartanContraction.three_wedge

end

section

/-!
# The Cartan homotopy in the ordinary affine complex

The two lower Lie derivatives are computed on scalar multiples of
exact wedges. These are the identities needed to compare changes of
coefficient lifts on affine intersections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2CartanHomotopy

open KaehlerDifferential Module
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2CartanContraction

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
  (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hu : ∀ i, b i = D K A (u i))
  (v : Derivation K A A)

local notation "d₀" => D K A
local notation "d₁" => differential b
local notation "d₂" => exteriorD2 b (exactFrameDirection b)

def lieOne : Ω[A⁄K] →+ Ω[A⁄K] :=
  (d₀).toLinearMap.toAddMonoidHom.comp (one v).toAddMonoidHom + (two v).toAddMonoidHom.comp d₁

def lieTwo : Form K A 2 →+ Form K A 2 :=
  (d₁).comp (two v).toAddMonoidHom + (three v).toAddMonoidHom.comp (d₂).toAddMonoidHom

def lieThree : Form K A 3 →+ Form K A 3 :=
  (d₂).toAddMonoidHom.comp (three v).toAddMonoidHom

include hu in
theorem lieOne_symbol (a c : A) :
    lieOne b v (a • d₀ c) = v a • d₀ c + a • d₀ (v c) := by
  change d₀ (one v (a • d₀ c)) + two v (d₁ (a • d₀ c)) = _
  rw [map_smul, Derivation.liftKaehlerDifferential_comp_D, differential_symbol b u hu,
    two_wedge, Derivation.liftKaehlerDifferential_comp_D, Derivation.liftKaehlerDifferential_comp_D]
  change d₀ (a * v c) + (v a • d₀ c - v c • d₀ a) = _
  rw [Derivation.leibniz]
  abel

private theorem wedge_add_left (x y z : Ω[A⁄K]) : wedge (x+y) z = wedge x z + wedge y z :=
  (wedgeLeft z).map_add x y
private theorem wedge_smul_left (a : A) (x y : Ω[A⁄K]) : wedge (a • x) y = a • wedge x y :=
  (wedgeLeft y).map_smul a x

include hu in
theorem lieTwo_symbol (a c e : A) :
    lieTwo b v (a • wedge (d₀ c) (d₀ e)) = v a • wedge (d₀ c) (d₀ e) +
      a • wedge (d₀ (v c)) (d₀ e) + a • wedge (d₀ c) (d₀ (v e)) := by
  have hex : d₂ (a • wedge (d₀ c) (d₀ e)) = exteriorPower.ιMulti A 3 ![d₀ a, d₀ c, d₀ e] :=
    exteriorD2_exactFrame b u hu a c e
  change d₁ (two v (a • wedge (d₀ c) (d₀ e))) + three v (d₂ (a • wedge (d₀ c) (d₀ e))) = _
  rw [hex, map_smul, two_wedge, three_wedge]
  simp only [Derivation.liftKaehlerDifferential_comp_D, smul_sub, smul_smul, map_sub,
    differential_symbol b u hu, Derivation.leibniz, wedge_add_left, wedge_smul_left]
  rw [wedge_swap (d₀ c) (d₀ (v e)), smul_neg]
  abel

include hu in
theorem lieOne_d (a : A) : lieOne b v (d₀ a) = d₀ (v a) := by
  simpa only [one_smul, Derivation.map_one_eq_zero, zero_smul, zero_add] using lieOne_symbol b u hu v 1 a

include hu in
theorem lieTwo_d (ω : Ω[A⁄K]) : lieTwo b v (d₁ ω) = d₁ (lieOne b v ω) := by
  change d₁ (two v (d₁ ω)) + three v (d₂ (d₁ ω)) =
    d₁ (d₀ (one v ω) + two v (d₁ ω))
  rw [differential_two_one b u hu, map_zero, add_zero, map_add,
    differential_D b u hu, zero_add]

include hu in
theorem lieThree_d (ω : Form K A 2) : lieThree b v (d₂ ω) = d₂ (lieTwo b v ω) := by
  change d₂ (three v (d₂ ω)) = d₂ (d₁ (two v ω) + three v (d₂ ω))
  rw [map_add, differential_two_one b u hu, zero_add]

end CycleQ2CartanHomotopy

#print axioms CycleQ2CartanHomotopy.lieOne_symbol
#print axioms CycleQ2CartanHomotopy.lieTwo_symbol
#print axioms CycleQ2CartanHomotopy.lieThree_d

end

section

/-!
# Restriction and additivity of the Cartan corrections

Compatible relative derivations give the same contractions after
restriction. Contraction is additive in the derivation in each of the
three degrees, which supplies the triple-overlap identity for
successive changes of a coefficient lift.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2CartanNaturality

open KaehlerDifferential
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2CartanContraction
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)

variable {K A B : Type} [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
  (φ : A →ₐ[K] B) (v : Derivation K A A) (w : Derivation K B B)
  (h : ∀ a, w (φ a) = φ (v a))

include h in
theorem one_natural (α : Ω[A⁄K]) : one w (onePullback φ α) = φ (one v α) := by
  have ha : α ∈ Submodule.span A (Set.range (D K A)) := by
    rw [span_range_derivation]
    trivial
  induction ha using Submodule.span_induction with
  | mem α hα =>
    obtain ⟨a,rfl⟩ := hα
    rw [onePullback_d, Derivation.liftKaehlerDifferential_comp_D, Derivation.liftKaehlerDifferential_comp_D]
    exact h a
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
    rw [map_smulₛₗ, map_smul, map_smul]
    change φ a * one w (onePullback φ x) = φ (a * one v x)
    rw [hx, map_mul]

private theorem wedge_natural (x y : Ω[A⁄K]) :
    exteriorPullback φ 2 (wedge x y) = wedge (onePullback φ x) (onePullback φ y) := by
  unfold exteriorPullback wedge
  rw [exteriorMap_wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem triple_natural (x y z : Ω[A⁄K]) :
    exteriorPullback φ 3 (exteriorPower.ιMulti A 3 ![x,y,z]) =
      exteriorPower.ιMulti B 3 ![onePullback φ x, onePullback φ y, onePullback φ z] := by
  unfold exteriorPullback
  rw [exteriorMap_wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

include h in
theorem two_natural (α : Form K A 2) :
    two w (exteriorPullback φ 2 α) = onePullback φ (two v α) := by
  have ha : α ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction ha using Submodule.span_induction with
  | mem α hα =>
    obtain ⟨a,rfl⟩ := hα
    have e : a = ![a 0,a 1] := by funext i; fin_cases i <;> rfl
    rw [e]
    change two w (exteriorPullback φ 2 (wedge (a 0) (a 1))) =
      onePullback φ (two v (wedge (a 0) (a 1)))
    rw [wedge_natural, two_wedge, two_wedge, map_sub, map_smulₛₗ, map_smulₛₗ,
      one_natural φ v w h, one_natural φ v w h]
    rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => rw [map_smulₛₗ, map_smul, map_smul, map_smulₛₗ, hx]

include h in
theorem three_natural (α : Form K A 3) :
    three w (exteriorPullback φ 3 α) = exteriorPullback φ 2 (three v α) := by
  have ha : α ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 3)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction ha using Submodule.span_induction with
  | mem α hα =>
    obtain ⟨a,rfl⟩ := hα
    have e : a = ![a 0,a 1,a 2] := by funext i; fin_cases i <;> rfl
    rw [e, triple_natural, three_wedge, three_wedge]
    simp only [map_add, map_sub, map_smulₛₗ, wedge_natural, one_natural φ v w h]
    rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => rw [map_smulₛₗ, map_smul, map_smul, map_smulₛₗ, hx]

variable (e : Derivation K A A)

theorem one_add : one (v + e) = one v + one e := by
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change one (v + e) (D K A a) = (one v + one e) (D K A a)
  simp only [LinearMap.add_apply, Derivation.liftKaehlerDifferential_comp_D, Derivation.add_apply]

theorem two_add : two (v + e) = two v + two e := by
  apply exteriorPower.linearMap_ext
  ext a : 1
  have he : a = ![a 0,a 1] := by funext i; fin_cases i <;> rfl
  rw [he]
  change two (v + e) (wedge (a 0) (a 1)) = (two v + two e) (wedge (a 0) (a 1))
  simp only [LinearMap.add_apply, two_wedge, one_add, add_smul]
  abel

theorem three_add : three (v + e) = three v + three e := by
  apply exteriorPower.linearMap_ext
  ext a : 1
  have he : a = ![a 0,a 1,a 2] := by funext i; fin_cases i <;> rfl
  rw [he]
  change three (v + e) (exteriorPower.ιMulti A 3 ![a 0,a 1,a 2]) =
    (three v + three e) (exteriorPower.ιMulti A 3 ![a 0,a 1,a 2])
  simp only [LinearMap.add_apply, three_wedge, one_add, add_smul]
  abel

end CycleQ2CartanNaturality

#print axioms CycleQ2CartanNaturality.three_natural
#print axioms CycleQ2CartanNaturality.three_add

end

section

/-!
# The canonical contraction in the ordered exact volume frame

The frame-independent alternating contraction agrees with the signed
coordinate expression on the volume. Its Lie derivative has the
coefficient Leibniz rule, as do the lower Cartan operators.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2CartanTopComparison

open Module KaehlerDifferential
open CycleQ2CartanContraction CycleQ2CartanHomotopy CycleQ2RelativeTopCartan
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
  (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hu : ∀ i, b i = D K A (u i))
  (v : Derivation K A A)

private theorem omittedBasis (i : Fin 3) : twoBasis b i = exteriorPower.ιMulti A 2 (i.removeNth b) := by
  rw [twoBasis, Basis.reindex_apply, Equiv.symm_symm]
  change b.exteriorPower 2 (⟨{i}ᶜ, by simp [Finset.card_compl]⟩ : Set.powersetCard (Fin 3) 2) = _
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  simp only [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb, Fin.removeNth]
  rfl

include hu in
theorem contraction_volume (a : A) : three v (a • volume b) = contraction b u v a := by
  have hb : (b : Fin 3 → Ω[A⁄K]) = ![b 0,b 1,b 2] := by
    funext i
    fin_cases i <;> rfl
  have h₀ : wedge (b 1) (b 2) = twoBasis b 0 := by rw [omittedBasis]; rfl
  have h₁ : wedge (b 0) (b 2) = twoBasis b 1 := by rw [omittedBasis]; rfl
  have h₂ : wedge (b 0) (b 1) = twoBasis b 2 := by rw [omittedBasis]; rfl
  have hi (i : Fin 3) : one v (b i) = v (u i) := by rw [hu, Derivation.liftKaehlerDifferential_comp_D]
  rw [map_smul, volume]
  conv_lhs => rw [hb, three_wedge]
  rw [h₀,h₁,h₂,hi,hi,hi]
  apply (twoBasis b).repr.injective
  ext i
  have h : (twoBasis b).repr ((twoBasis b).equivFun.symm
      (fun i => (-1 : A) ^ i.val * (a * v (u i)))) i = (-1 : A) ^ i.val * (a * v (u i)) :=
    Basis.coord_equivFun_symm (twoBasis b) i _
  change (twoBasis b).repr (a • _) i = (twoBasis b).repr ((twoBasis b).equivFun.symm _) i
  rw [h]
  fin_cases i <;>
    simp [Finsupp.single_apply, smul_eq_mul]

include hu in
theorem lieThree_volume (a : A) : lieThree b v (a • volume b) =
    (v a + a * ∑ i, exactFrameDirection b i (v (u i))) • volume b := by
  change exteriorD2 b (exactFrameDirection b) (three v (a • volume b)) = _
  rw [contraction_volume b u hu, derivative_contraction b u hu]

include hu in
theorem lieThree_smul (a : A) (ω : Form K A 3) :
    lieThree b v (a • ω) = v a • ω + a • lieThree b v ω := by
  obtain ⟨r,rfl⟩ := topForm_scalar b ω
  simp only [smul_smul, lieThree_volume b u hu v, Derivation.leibniz, smul_eq_mul, ← add_smul]
  congr 1
  ring

end CycleQ2CartanTopComparison

#print axioms CycleQ2CartanTopComparison.contraction_volume
#print axioms CycleQ2CartanTopComparison.lieThree_smul

end

section

/-!
# Extending a coefficient lift to an étale overlap

Étale base change of the absolute Kähler module extends the derivation
uniquely. The extension agrees on all original functions, including
the exact coordinates and the ground-field coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2EtaleCoefficientTransport

open KaehlerDifferential CycleQ2RelativeDerivationLift
open scoped TensorProduct

variable {k K A B : Type} [CommRing k] [CommRing K] [CommRing A] [CommRing B]
  [Algebra k K] [Algebra K A] [Algebra K B] [Algebra k A] [Algebra k B] [Algebra A B]
  [IsScalarTower k K A] [IsScalarTower k K B] [IsScalarTower K A B] [IsScalarTower k A B]
  [Algebra.FormallyEtale A B]

/-- The canonical extension along the actual étale restriction. -/
def extend (d : Derivation k A A) : Derivation k B B :=
  ((((Algebra.linearMap A B).comp d.liftKaehlerDifferential).liftBaseChange B).comp
    (tensorKaehlerEquivOfFormallyEtale k A B).symm.toLinearMap).compDer (D k B)

theorem extend_apply (d : Derivation k A A) (a : A) :
    extend (B := B) d (algebraMap A B a) = algebraMap A B (d a) := by
  change ((Algebra.linearMap A B).comp d.liftKaehlerDifferential).liftBaseChange B
    ((tensorKaehlerEquivOfFormallyEtale k A B).symm (D k B (algebraMap A B a))) = _
  rw [tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap, LinearMap.liftBaseChange_tmul,
    one_smul, LinearMap.comp_apply, Derivation.liftKaehlerDifferential_comp_D]
  rfl

private theorem same_extension (d e : Derivation k B B)
    (h : ∀ a : A, d (algebraMap A B a) = e (algebraMap A B a)) : d = e := by
  let v := asRelative (K := A) (d-e) (by intro a; change d _ - e _ = 0; rw [h, sub_self])
  have hz : v = 0 := by
    ext b
    have he : D A B b = 0 := Subsingleton.elim _ _
    rw [← Derivation.liftKaehlerDifferential_comp_D v, he, map_zero, Derivation.zero_apply]
  ext b
  exact sub_eq_zero.mp (DFunLike.congr_fun hz b)

theorem extend_unique (d : Derivation k A A) (e : Derivation k B B)
    (h : ∀ a, e (algebraMap A B a) = algebraMap A B (d a)) : extend d = e :=
  same_extension (extend d) e (fun a => (extend_apply d a).trans (h a).symm)

theorem extend_coefficients (δ : Derivation k K K) (d : Derivation k A A)
    (h : ∀ a, d (algebraMap K A a) = algebraMap K A (δ a)) (a : K) :
    extend (B := B) d (algebraMap K B a) = algebraMap K B (δ a) := by
  rw [IsScalarTower.algebraMap_apply K A B, extend_apply, h, ← IsScalarTower.algebraMap_apply K A B]

theorem extend_fixes (d : Derivation k A A) (a : A) (h : d a = 0) :
    extend (B := B) d (algebraMap A B a) = 0 := by rw [extend_apply, h, map_zero]

end CycleQ2EtaleCoefficientTransport

#print axioms CycleQ2EtaleCoefficientTransport.extend_unique
#print axioms CycleQ2EtaleCoefficientTransport.extend_coefficients

end

section

/-!
# Lie differentiation for an arbitrary coefficient lift

A lift of a fixed base derivation is a coordinate-fixing lift plus
an ordinary relative derivation. Add its Cartan operator to the local
coefficient derivative. The resulting operators have the intrinsic
exact-symbol formulas and the correct change-of-lift homotopies.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2CoefficientLieLift

open KaehlerDifferential Module
open CycleQ2RelativeDerivationLift CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2RelativeChartConnection CycleQ2CartanHomotopy CycleQ2CartanTopComparison

variable {k K A : Type} [CommRing k] [CommRing K] [CommRing A]
  [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
  (δ : Derivation k K K) (d e : Derivation k A A)
  (hd : ∀ a, d (algebraMap K A a) = algebraMap K A (δ a))
  (he : ∀ a, e (algebraMap K A a) = algebraMap K A (δ a))
  (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hb : ∀ i, b i = D K A (u i))
  (hfix : ∀ i, e (u i) = 0)

abbrev correction : Derivation K A A :=
  asRelative (d-e) (by intro x; change d _ - e _ = 0; rw [hd,he,sub_self])

def onOne : Ω[A⁄K] →+ Ω[A⁄K] := onBasis e b + lieOne b (correction δ d e hd he)
def onTwo : Form K A 2 →+ Form K A 2 := onBasis e (twoBasis b) + lieTwo b (correction δ d e hd he)
def onThree : Form K A 3 →+ Form K A 3 := onBasis e (b.exteriorPower 3) + lieThree b (correction δ d e hd he)

local notation "∂" => D K A

include hb hfix in
theorem onOne_symbol (a c : A) :
    onOne δ d e hd he b (a • ∂ c) = d a • ∂ c + a • ∂ (d c) := by
  let v := correction δ d e hd he
  change onBasis e b (a • ∂ c) + lieOne b v (a • ∂ c) = _
  rw [CycleQ2RelativeChartConnection.onOne_symbol δ e he b u hb hfix, lieOne_symbol b u hb]
  change a • ∂ (e c) + e a • ∂ c + ((d a - e a) • ∂ c + a • ∂ (d c - e c)) = _
  simp only [map_sub, sub_smul, smul_sub]
  abel

private theorem wedge_sub_left (x y z : Ω[A⁄K]) : wedge (x-y) z = wedge x z - wedge y z :=
  (wedgeLeft z).map_sub x y
private theorem wedge_sub_right (x y z : Ω[A⁄K]) : wedge x (y-z) = wedge x y - wedge x z :=
  (wedgeRight x).map_sub y z

include hb hfix in
theorem onTwo_symbol (a c f : A) :
    onTwo δ d e hd he b (a • wedge (∂ c) (∂ f)) = d a • wedge (∂ c) (∂ f) +
      a • wedge (∂ (d c)) (∂ f) + a • wedge (∂ c) (∂ (d f)) := by
  let v := correction δ d e hd he
  change onBasis e (twoBasis b) (a • wedge (∂ c) (∂ f)) + lieTwo b v (a • wedge (∂ c) (∂ f)) = _
  rw [onBasis_smul, onTwo_wedge, onOne_D δ e he b u hb hfix, onOne_D δ e he b u hb hfix,
    lieTwo_symbol b u hb]
  change a • (wedge (∂ (e c)) (∂ f) + wedge (∂ c) (∂ (e f))) + e a • wedge (∂ c) (∂ f) +
    ((d a - e a) • wedge (∂ c) (∂ f) + a • wedge (∂ (d c - e c)) (∂ f) +
      a • wedge (∂ c) (∂ (d f - e f))) = _
  have hsub (x y : A) : ∂ (x-y) = ∂ x - ∂ y := map_sub (D K A) x y
  rw [hsub, hsub, wedge_sub_left, wedge_sub_right]
  simp only [sub_eq_add_neg, add_smul, neg_smul, smul_add, smul_neg]
  abel

private def fullIndex : Set.powersetCard (Fin 3) 3 := ⟨Finset.univ, by simp⟩

private theorem volume_basis : b.exteriorPower 3 fullIndex = volume b := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family volume
  congr 1
  funext j
  apply congrArg b
  have h : (fun i : Fin 3 => i) = (Finset.univ : Finset (Fin 3)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique _ (fun _ => Finset.mem_univ _) strictMono_id
  exact (congrFun h j).symm

private theorem coefficient_on_volume (a : A) :
    onBasis e (b.exteriorPower 3) (a • volume b) = e a • volume b := by
  rw [← volume_basis, onBasis_smul]
  suffices h : onBasis e (b.exteriorPower 3) (b.exteriorPower 3 fullIndex) = 0 by
    rw [h, smul_zero, zero_add]
  apply (b.exteriorPower 3).repr.injective
  ext i
  rw [onBasis_repr, Basis.repr_self, Finsupp.single_apply]
  split <;> simp

include hb hfix in
theorem onTwo_d (ω : Ω[A⁄K]) :
    onTwo δ d e hd he b (differential b ω) = differential b (onOne δ d e hd he b ω) := by
  change onBasis e (twoBasis b) (differential b ω) + lieTwo b (correction δ d e hd he) (differential b ω) =
    differential b (onBasis e b ω + lieOne b (correction δ d e hd he) ω)
  rw [lieTwo_d b u hb, map_add, differential_onOne δ e he b u hb hfix]

include hb hfix in
theorem onThree_d (ω : Form K A 2) :
    onThree δ d e hd he b (exteriorD2 b (exactFrameDirection b) ω) =
      exteriorD2 b (exactFrameDirection b) (onTwo δ d e hd he b ω) := by
  change onBasis e (b.exteriorPower 3) (exteriorD2 b (exactFrameDirection b) ω) +
    lieThree b (correction δ d e hd he) (exteriorD2 b (exactFrameDirection b) ω) =
    exteriorD2 b (exactFrameDirection b)
      (onBasis e (twoBasis b) ω + lieTwo b (correction δ d e hd he) ω)
  rw [lieThree_d b u hb, map_add, exteriorD2_onBasis δ e he b u hb hfix]
  congr 1
  rw [exteriorD2_divergence, coefficient_on_volume]
  rfl

include hb in
theorem onThree_smul (a : A) (ω : Form K A 3) :
    onThree δ d e hd he b (a • ω) = a • onThree δ d e hd he b ω + d a • ω := by
  change onBasis e (b.exteriorPower 3) (a • ω) + lieThree b (correction δ d e hd he) (a • ω) =
    a • (onBasis e (b.exteriorPower 3) ω + lieThree b (correction δ d e hd he) ω) + d a • ω
  rw [onBasis_smul, lieThree_smul b u hb]
  change a • onBasis e (b.exteriorPower 3) ω + e a • ω +
    ((d a - e a) • ω + a • lieThree b (correction δ d e hd he) ω) = _
  simp only [sub_eq_add_neg, add_smul, neg_smul, smul_add]
  abel

include hb hfix in
/-- On a triple of exact forms, Lie differentiation substitutes the
coefficient derivative in each slot. -/
theorem onThree_symbol (a c f : A) :
    onThree δ d e hd he b (exteriorPower.ιMulti A 3 ![∂ a, ∂ c, ∂ f]) =
      exteriorPower.ιMulti A 3 ![∂ (d a), ∂ c, ∂ f] +
      exteriorPower.ιMulti A 3 ![∂ a, ∂ (d c), ∂ f] +
      exteriorPower.ιMulti A 3 ![∂ a, ∂ c, ∂ (d f)] := by
  have h (x y z : A) : exteriorD2 b (exactFrameDirection b) (x • wedge (∂ y) (∂ z)) =
      exteriorPower.ιMulti A 3 ![∂ x, ∂ y, ∂ z] := exteriorD2_exactFrame b u hb x y z
  rw [← h a c f, onThree_d δ d e hd he b u hb hfix, onTwo_symbol δ d e hd he b u hb hfix,
    map_add, map_add, h, h, h]

end CycleQ2CoefficientLieLift

#print axioms CycleQ2CoefficientLieLift.onOne_symbol
#print axioms CycleQ2CoefficientLieLift.onThree_smul
#print axioms CycleQ2CoefficientLieLift.onThree_symbol

end

section

/-!
# The intrinsic overlap correction for changing a coefficient lift

In one common exact frame the difference of two local coefficient
operators is the Cartan homotopy for their relative difference. The
contractions add on triple overlaps and commute with restriction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2CoefficientOverlapHomotopy

open KaehlerDifferential Module
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2CartanContraction CycleQ2CartanHomotopy CycleQ2CartanNaturality
open CycleQ2CoefficientLieLift

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
  (b : Basis (Fin 3) A Ω[A⁄K])

private theorem lieOne_add (v w : Derivation K A A) :
    lieOne b (v+w) = lieOne b v + lieOne b w := by
  ext ω
  change D K A (one (v+w) ω) + two (v+w) (differential b ω) =
    (D K A (one v ω) + two v (differential b ω)) + (D K A (one w ω) + two w (differential b ω))
  simp only [one_add, two_add, LinearMap.add_apply, map_add]
  abel

private theorem lieTwo_add (v w : Derivation K A A) :
    lieTwo b (v+w) = lieTwo b v + lieTwo b w := by
  ext ω : 1
  change differential b (two (v+w) ω) + three (v+w) (exteriorD2 b (exactFrameDirection b) ω) =
    (differential b (two v ω) + three v (exteriorD2 b (exactFrameDirection b) ω)) +
      (differential b (two w ω) + three w (exteriorD2 b (exactFrameDirection b) ω))
  simp only [two_add, three_add, LinearMap.add_apply, map_add]
  abel

private theorem lieThree_add (v w : Derivation K A A) :
    lieThree b (v+w) = lieThree b v + lieThree b w := by
  ext ω : 1
  change exteriorD2 b (exactFrameDirection b) (three (v+w) ω) =
    exteriorD2 b (exactFrameDirection b) (three v ω) + exteriorD2 b (exactFrameDirection b) (three w ω)
  simp only [three_add, LinearMap.add_apply, map_add]

variable {k : Type} [CommRing k] [Algebra k K] [Algebra k A] [IsScalarTower k K A]
  (δ : Derivation k K K) (d₁ d₂ e : Derivation k A A)
  (h₁ : ∀ a, d₁ (algebraMap K A a) = algebraMap K A (δ a))
  (h₂ : ∀ a, d₂ (algebraMap K A a) = algebraMap K A (δ a))
  (he : ∀ a, e (algebraMap K A a) = algebraMap K A (δ a))

/-- At a triple overlap the three relative corrections add exactly. -/
theorem correction_trans : correction δ d₁ e h₁ he =
    correction δ d₁ d₂ h₁ h₂ + correction δ d₂ e h₂ he := by
  ext a
  change d₁ a - e a = (d₁ a - d₂ a) + (d₂ a - e a)
  abel

theorem onOne_difference : onOne δ d₁ e h₁ he b - onOne δ d₂ e h₂ he b =
    lieOne b (correction δ d₁ d₂ h₁ h₂) := by
  unfold onOne
  rw [correction_trans δ d₁ d₂ e h₁ h₂ he, lieOne_add]
  abel

theorem onTwo_difference : onTwo δ d₁ e h₁ he b - onTwo δ d₂ e h₂ he b =
    lieTwo b (correction δ d₁ d₂ h₁ h₂) := by
  unfold onTwo
  rw [correction_trans δ d₁ d₂ e h₁ h₂ he, lieTwo_add]
  abel

theorem onThree_difference : onThree δ d₁ e h₁ he b - onThree δ d₂ e h₂ he b =
    lieThree b (correction δ d₁ d₂ h₁ h₂) := by
  unfold onThree
  rw [correction_trans δ d₁ d₂ e h₁ h₂ he, lieThree_add]
  abel

end CycleQ2CoefficientOverlapHomotopy

#print axioms CycleQ2CoefficientOverlapHomotopy.correction_trans
#print axioms CycleQ2CoefficientOverlapHomotopy.onThree_difference

end

section

/-!
# The arbitrary coefficient operators commute with ordinary pullback

Each operator is characterized by its exact-wedge formula. A
restriction that intertwines the chosen derivations therefore
intertwines the induced operators in all positive degrees, even when
its two charts use different exact coordinate frames.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2CoefficientLiftNaturality

open KaehlerDifferential Module
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham CycleQ2CoefficientLieLift
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)

variable {k K A B : Type} [CommRing k] [CommRing K] [CommRing A] [CommRing B]
  [Algebra k K] [Algebra k A] [Algebra k B] [Algebra K A] [Algebra K B]
  [IsScalarTower k K A] [IsScalarTower k K B]
  (δ : Derivation k K K) (φ : A →ₐ[K] B)
  (d e : Derivation k A A) (r s : Derivation k B B)
  (hd : ∀ x, d (algebraMap K A x) = algebraMap K A (δ x))
  (he : ∀ x, e (algebraMap K A x) = algebraMap K A (δ x))
  (hr : ∀ x, r (algebraMap K B x) = algebraMap K B (δ x))
  (hs : ∀ x, s (algebraMap K B x) = algebraMap K B (δ x))
  (h : ∀ a, r (φ a) = φ (d a))
  (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hb : ∀ i, b i = D K A (u i))
  (hu : ∀ i, e (u i) = 0)
  (c : Basis (Fin 3) B Ω[B⁄K]) (v : Fin 3 → B) (hc : ∀ i, c i = D K B (v i))
  (hv : ∀ i, s (v i) = 0)

private abbrev A₁ := onOne δ d e hd he b
private abbrev B₁ := onOne δ r s hr hs c
private abbrev A₂ := onTwo δ d e hd he b
private abbrev B₂ := onTwo δ r s hr hs c
private abbrev A₃ := onThree δ d e hd he b
private abbrev B₃ := onThree δ r s hr hs c

include h hb hu hc hv in
theorem one_natural (ω : Ω[A⁄K]) :
    onePullback φ (A₁ δ d e hd he b ω) = B₁ δ r s hr hs c (onePullback φ ω) := by
  rw [← b.sum_repr ω, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hb, onOne_symbol δ d e hd he b u hb hu, map_add, map_smulₛₗ, map_smulₛₗ,
    map_smulₛₗ, onePullback_d, onePullback_d]
  change φ (d (b.repr ω i)) • D K B (φ (u i)) + φ (b.repr ω i) • D K B (φ (d (u i))) =
    B₁ δ r s hr hs c (φ (b.repr ω i) • D K B (φ (u i)))
  rw [onOne_symbol δ r s hr hs c v hc hv, h, h]

private theorem wedge_natural (x y : Ω[A⁄K]) :
    exteriorPullback φ 2 (wedge x y) = wedge (onePullback φ x) (onePullback φ y) := by
  unfold exteriorPullback wedge
  rw [exteriorMap_wedge]
  congr 1
  funext i
  fin_cases i <;> rfl

include h hb hu hc hv in
theorem two_natural (ω : Form K A 2) :
    exteriorPullback φ 2 (A₂ δ d e hd he b ω) = B₂ δ r s hr hs c (exteriorPullback φ 2 ω) := by
  let l := (exteriorPullback φ 2).toAddMonoidHom.comp (A₂ δ d e hd he b)
  let t := (B₂ δ r s hr hs c).comp (exteriorPullback φ 2).toAddMonoidHom
  have e₀ : l = t := by
    apply twoFormMap_ext b u hb
    intro a x y
    change exteriorPullback φ 2 (A₂ δ d e hd he b (a • wedge (D K A x) (D K A y))) =
      B₂ δ r s hr hs c (exteriorPullback φ 2 (a • wedge (D K A x) (D K A y)))
    rw [onTwo_symbol δ d e hd he b u hb hu, map_add, map_add, map_smulₛₗ,
      map_smulₛₗ, map_smulₛₗ, map_smulₛₗ]
    simp only [wedge_natural, onePullback_d]
    change φ (d a) • wedge (D K B (φ x)) (D K B (φ y)) +
      φ a • wedge (D K B (φ (d x))) (D K B (φ y)) +
      φ a • wedge (D K B (φ x)) (D K B (φ (d y))) =
      B₂ δ r s hr hs c (φ a • wedge (D K B (φ x)) (D K B (φ y)))
    rw [onTwo_symbol δ r s hr hs c v hc hv, h, h, h]
  exact DFunLike.congr_fun e₀ ω

private def triple {C : Type} [CommRing C] [Algebra K C] (x y z : C) : Form K C 3 :=
  exteriorPower.ιMulti C 3 ![D K C x,D K C y,D K C z]

private theorem triple_natural (x y z : A) :
    exteriorPullback φ 3 (triple (K := K) x y z) = triple (K := K) (φ x) (φ y) (φ z) := by
  unfold triple
  rw [exteriorPullback, exteriorMap_wedge]
  apply congrArg (exteriorPower.ιMulti B 3)
  funext i
  fin_cases i <;> apply onePullback_d

include h hb hu hc hv in
theorem three_natural (ω : Form K A 3) :
    exteriorPullback φ 3 (A₃ δ d e hd he b ω) = B₃ δ r s hr hs c (exteriorPullback φ 3 ω) := by
  obtain ⟨a,rfl⟩ := topForm_scalar b ω
  have hvol : volume b = triple (K := K) (u 0) (u 1) (u 2) := by
    unfold volume triple
    apply congrArg (exteriorPower.ιMulti A 3)
    funext i
    fin_cases i <;> apply hb
  have sy (x y z : A) : A₃ δ d e hd he b (triple (K := K) x y z) =
      triple (K := K) (d x) y z + triple (K := K) x (d y) z + triple (K := K) x y (d z) :=
    onThree_symbol δ d e hd he b u hb hu x y z
  have sz (x y z : B) : B₃ δ r s hr hs c (triple (K := K) x y z) =
      triple (K := K) (r x) y z + triple (K := K) x (r y) z + triple (K := K) x y (r z) :=
    onThree_symbol δ r s hr hs c v hc hv x y z
  rw [hvol, onThree_smul δ d e hd he b u hb, sy, map_add, map_smulₛₗ,
    map_smulₛₗ, map_smulₛₗ, onThree_smul δ r s hr hs c v hc]
  simp only [map_add, triple_natural, h, sz]
  rw [show r (φ.toRingHom a) = φ.toRingHom (d a) from h a]

end CycleQ2CoefficientLiftNaturality

#print axioms CycleQ2CoefficientLiftNaturality.one_natural
#print axioms CycleQ2CoefficientLiftNaturality.two_natural
#print axioms CycleQ2CoefficientLiftNaturality.three_natural

end

section

/-!
# The Čech Cartan correction on local overlap equations

Use the coefficient lift at the first vertex of an ordered face.
The correction contracts the tail cochain with the difference of
its first two lifts. With total differential δ + (-1)^p d, the pair
and triple equations are preserved by the resulting signed terms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2CechCartanCorrection

open KaehlerDifferential Module
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2CartanContraction CycleQ2CartanHomotopy CycleQ2CartanNaturality
open CycleQ2CoefficientLieLift CycleQ2CoefficientOverlapHomotopy

variable {k K A I : Type} [CommRing k] [CommRing K] [CommRing A]
  [Algebra k K] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
  (δ : Derivation k K K) (l : I → Derivation k A A) (e : Derivation k A A)
  (hl : ∀ i x, l i (algebraMap K A x) = algebraMap K A (δ x))
  (he : ∀ x, e (algebraMap K A x) = algebraMap K A (δ x))
  (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hb : ∀ i, b i = D K A (u i))
  (hu : ∀ i, e (u i) = 0)

private abbrev L₁ (i : I) := onOne δ (l i) e (hl i) he b
private abbrev L₂ (i : I) := onTwo δ (l i) e (hl i) he b
private abbrev L₃ (i : I) := onThree δ (l i) e (hl i) he b
private abbrev v (i j : I) := correction δ (l i) (l j) (hl i) (hl j)

local notation "L₁[" i "]" => L₁ δ l e hl he b i
local notation "L₂[" i "]" => L₂ δ l e hl he b i
local notation "L₃[" i "]" => L₃ δ l e hl he b i
local notation "v[" i "," j "]" => v δ l hl i j
local notation "d₀" => D K A
local notation "d₁" => differential b
local notation "d₂" => exteriorD2 b (exactFrameDirection b)

private theorem difference₃ (i j : I) (ω : Form K A 3) :
    L₃[i] ω - L₃[j] ω = d₂ (three v[i,j] ω) :=
  DFunLike.congr_fun (onThree_difference b δ (l i) (l j) e (hl i) (hl j) he) ω

private theorem difference₂ (i j : I) (η : Form K A 2) :
    L₂[i] η - L₂[j] η = d₁ (two v[i,j] η) + three v[i,j] (d₂ η) :=
  DFunLike.congr_fun (onTwo_difference b δ (l i) (l j) e (hl i) (hl j) he) η

private theorem difference₁ (i j : I) (θ : Ω[A⁄K]) :
    L₁[i] θ - L₁[j] θ = d₀ (one v[i,j] θ) + two v[i,j] (d₁ θ) :=
  DFunLike.congr_fun (onOne_difference b δ (l i) (l j) e (hl i) (hl j) he) θ

private theorem one_trans (i j k : I) (θ : Ω[A⁄K]) :
    one v[i,k] θ = one v[i,j] θ + one v[j,k] θ := by
  unfold v
  rw [correction_trans δ (l i) (l j) (l k) (hl i) (hl j) (hl k), one_add, LinearMap.add_apply]

private theorem two_trans (i j k : I) (η : Form K A 2) :
    two v[i,k] η = two v[i,j] η + two v[j,k] η := by
  unfold v
  rw [correction_trans δ (l i) (l j) (l k) (hl i) (hl j) (hl k), two_add, LinearMap.add_apply]

private theorem three_trans (i j k : I) (ω : Form K A 3) :
    three v[i,k] ω = three v[i,j] ω + three v[j,k] ω := by
  unfold v
  rw [correction_trans δ (l i) (l j) (l k) (hl i) (hl j) (hl k), three_add, LinearMap.add_apply]

abbrev correctedEdge (i j : I) (ωj : Form K A 3) (ηij : Form K A 2) :=
  L₂[i] ηij - three v[i,j] ωj

abbrev correctedFace (i j : I) (ηjk : Form K A 2) (θijk : Ω[A⁄K]) :=
  L₁[i] θijk + two v[i,j] ηjk

abbrev correctedTetrahedron (i j : I) (θjkl : Ω[A⁄K]) (ζijkl : A) :=
  l i ζijkl - one v[i,j] θjkl

include hb hu in
theorem pair (i j : I) (ωi ωj : Form K A 3) (ηij : Form K A 2) (hη : ωj - ωi = d₂ ηij) :
    L₃[j] ωj - L₃[i] ωi = d₂ (correctedEdge δ l e hl he b i j ωj ηij) := by
  calc
    _ = (L₃[i] ωj - L₃[i] ωi) - (L₃[i] ωj - L₃[j] ωj) := by abel
    _ = L₃[i] (ωj - ωi) - d₂ (three v[i,j] ωj) := by
      rw [map_sub, difference₃ δ l e hl he b]
    _ = _ := by
      rw [hη, onThree_d δ (l i) e (hl i) he b u hb hu, correctedEdge, map_sub]

include hb hu in
theorem triple (i j k : I) (ωj ωk : Form K A 3)
    (ηij ηik ηjk : Form K A 2) (θ : Ω[A⁄K])
    (hη : ωk - ωj = d₂ ηjk) (hθ : ηjk - ηik + ηij + d₁ θ = 0) :
    correctedEdge δ l e hl he b j k ωk ηjk - correctedEdge δ l e hl he b i k ωk ηik +
      correctedEdge δ l e hl he b i j ωj ηij + d₁ (correctedFace δ l e hl he b i j ηjk θ) = 0 := by
  have hL : L₂[j] ηjk = L₂[i] ηjk - (d₁ (two v[i,j] ηjk) + three v[i,j] (d₂ ηjk)) := by
    rw [← difference₂ δ l e hl he b]
    abel
  have hC : three v[i,j] (d₂ ηjk) = three v[i,j] ωk - three v[i,j] ωj := by rw [← hη, map_sub]
  have hD : d₁ (L₁[i] θ) = L₂[i] (d₁ θ) := (onTwo_d δ (l i) e (hl i) he b u hb hu θ).symm
  calc
    _ = L₂[i] (ηjk - ηik + ηij + d₁ θ) := by
      unfold correctedEdge correctedFace
      rw [map_add, hD, hL, hC, three_trans δ l hl i j k]
      simp only [map_add, map_sub]
      abel
    _ = 0 := by rw [hθ, map_zero]

include hb hu in
theorem quadruple (i j k : I)
    (ηjk ηjm ηkm : Form K A 2) (θjkm θikm θijm θijk : Ω[A⁄K]) (ζ : A)
    (hθ : ηkm - ηjm + ηjk + d₁ θjkm = 0)
    (hζ : θjkm - θikm + θijm - θijk - d₀ ζ = 0) :
    correctedFace δ l e hl he b j k ηkm θjkm - correctedFace δ l e hl he b i k ηkm θikm +
      correctedFace δ l e hl he b i j ηjm θijm - correctedFace δ l e hl he b i j ηjk θijk -
      d₀ (correctedTetrahedron δ l hl i j θjkm ζ) = 0 := by
  have hL : L₁[j] θjkm = L₁[i] θjkm - (d₀ (one v[i,j] θjkm) + two v[i,j] (d₁ θjkm)) := by
    rw [← difference₁ δ l e hl he b]
    abel
  have E : d₁ θjkm = -(ηkm - ηjm + ηjk) := eq_neg_of_add_eq_zero_right hθ
  have hD : L₁[i] (d₀ ζ) = d₀ (l i ζ) := by
    simpa only [one_smul, Derivation.map_one_eq_zero, zero_smul, zero_add] using
      onOne_symbol δ (l i) e (hl i) he b u hb hu 1 ζ
  calc
    _ = L₁[i] (θjkm - θikm + θijm - θijk - d₀ ζ) := by
      unfold correctedFace correctedTetrahedron
      rw [hL, E, two_trans δ l hl i j k]
      simp only [map_sub, map_add, map_neg, hD]
      abel
    _ = 0 := by rw [hζ, map_zero]

/-- The fifth-vertex equation has only function values in its target. -/
theorem quintuple (i j k : I)
    (θklm θjlm θjkm θjkl : Ω[A⁄K]) (ζjklm ζiklm ζijlm ζijkm ζijkl : A)
    (hθ : θklm - θjlm + θjkm - θjkl = d₀ ζjklm)
    (hζ : ζjklm - ζiklm + ζijlm - ζijkm + ζijkl = 0) :
    correctedTetrahedron δ l hl j k θklm ζjklm - correctedTetrahedron δ l hl i k θklm ζiklm +
      correctedTetrahedron δ l hl i j θjlm ζijlm - correctedTetrahedron δ l hl i j θjkm ζijkm +
      correctedTetrahedron δ l hl i j θjkl ζijkl = 0 := by
  have hV : v[i,j] ζjklm = one v[i,j] θklm - one v[i,j] θjlm +
      one v[i,j] θjkm - one v[i,j] θjkl := by
    calc
      _ = one v[i,j] (d₀ ζjklm) := (Derivation.liftKaehlerDifferential_comp_D v[i,j] ζjklm).symm
      _ = _ := by rw [← hθ, map_sub, map_add, map_sub]
  have hL : l j ζjklm = l i ζjklm - v[i,j] ζjklm := by
    change l j ζjklm = l i ζjklm - (l i ζjklm - l j ζjklm)
    abel
  calc
    _ = l i (ζjklm - ζiklm + ζijlm - ζijkm + ζijkl) := by
      unfold correctedTetrahedron
      rw [hL, hV, one_trans δ l hl i j k]
      simp only [map_sub, map_add]
      abel
    _ = 0 := by rw [hζ, map_zero]


abbrev correctedEdgeTwo (i j : I) (αj : Form K A 2) (βij : Ω[A⁄K]) :=
  L₁[i] βij - two v[i,j] αj

abbrev correctedFaceTwo (i j : I) (βjk : Ω[A⁄K]) (γijk : A) :=
  l i γijk + one v[i,j] βjk

include hb hu in
/-- The pair component commutes with taking the boundary of a degree-two cochain. -/
theorem boundary_pair (i j : I) (αi αj : Form K A 2) (βij : Ω[A⁄K]) :
    L₂[j] αj - L₂[i] αi - d₁ (correctedEdgeTwo δ l e hl he b i j αj βij) =
      correctedEdge δ l e hl he b i j (d₂ αj) (αj - αi - d₁ βij) := by
  have hL : L₂[j] αj = L₂[i] αj - (d₁ (two v[i,j] αj) + three v[i,j] (d₂ αj)) := by
    rw [← difference₂ δ l e hl he b]
    abel
  have hD := onTwo_d δ (l i) e (hl i) he b u hb hu βij
  unfold correctedEdgeTwo correctedEdge
  rw [hL, map_sub]
  simp only [map_sub, hD]
  abel

include hb hu in
/-- The triple component commutes with taking the boundary of a degree-two cochain. -/
theorem boundary_triple (i j k : I) (αj αk : Form K A 2) (βij βik βjk : Ω[A⁄K]) (γ : A) :
    correctedEdgeTwo δ l e hl he b j k αk βjk - correctedEdgeTwo δ l e hl he b i k αk βik +
      correctedEdgeTwo δ l e hl he b i j αj βij + d₀ (correctedFaceTwo δ l hl i j βjk γ) =
    correctedFace δ l e hl he b i j (αk - αj - d₁ βjk) (βjk - βik + βij + d₀ γ) := by
  have hL : L₁[j] βjk = L₁[i] βjk - (d₀ (one v[i,j] βjk) + two v[i,j] (d₁ βjk)) := by
    rw [← difference₁ δ l e hl he b]
    abel
  have hD : L₁[i] (d₀ γ) = d₀ (l i γ) := by
    simpa only [one_smul, Derivation.map_one_eq_zero, zero_smul, zero_add] using
      onOne_symbol δ (l i) e (hl i) he b u hb hu 1 γ
  unfold correctedEdgeTwo correctedFaceTwo correctedFace
  rw [hL, two_trans δ l hl i j k]
  simp only [map_sub, map_add, hD]
  abel

/-- The four-vertex component commutes with the degree-two boundary. -/
theorem boundary_quadruple (i j k : I) (βjk βjm βkm : Ω[A⁄K])
    (γjkm γikm γijm γijk : A) :
    correctedFaceTwo δ l hl j k βkm γjkm - correctedFaceTwo δ l hl i k βkm γikm +
      correctedFaceTwo δ l hl i j βjm γijm - correctedFaceTwo δ l hl i j βjk γijk =
    correctedTetrahedron δ l hl i j (βkm - βjm + βjk + d₀ γjkm) (γjkm - γikm + γijm - γijk) := by
  have hL : l j γjkm = l i γjkm - v[i,j] γjkm := by
    change l j γjkm = l i γjkm - (l i γjkm - l j γjkm)
    abel
  have hD : one v[i,j] (d₀ γjkm) = v[i,j] γjkm :=
    Derivation.liftKaehlerDifferential_comp_D v[i,j] γjkm
  unfold correctedFaceTwo correctedTetrahedron
  rw [hL, one_trans δ l hl i j k]
  simp only [map_sub, map_add, hD]
  abel

end CycleQ2CechCartanCorrection

#print axioms CycleQ2CechCartanCorrection.pair
#print axioms CycleQ2CechCartanCorrection.triple
#print axioms CycleQ2CechCartanCorrection.quadruple
#print axioms CycleQ2CechCartanCorrection.quintuple
#print axioms CycleQ2CechCartanCorrection.boundary_pair
#print axioms CycleQ2CechCartanCorrection.boundary_triple
#print axioms CycleQ2CechCartanCorrection.boundary_quadruple

end

section

/-!
# The local cycle class under an arbitrary coefficient lift

A relative change in the lift contributes the Cartan contraction of
the closed double logarithmic form. Together with the coordinate-fixing
formula this gives an explicit primitive for the coefficient derivative
for every lift on the actual double localization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2LogarithmicLieNaturality

open KaehlerDifferential Module
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2PrincipalGysinFunctions CycleQ2DoubleLogarithmicClass
open CycleQ2CartanContraction CycleQ2CartanHomotopy CycleQ2CoefficientLieLift
open CycleQ2RelativeChartConnection (onBasis onTwo_logarithms)

variable {k K A : Type} [CommRing k] [CommRing K] [CommRing A]
  [Algebra k K] [Algebra K A] [Algebra k A] [IsScalarTower k K A]
  (δ : Derivation k K K) (d e : Derivation k A A)
  (hd : ∀ a, d (algebraMap K A a) = algebraMap K A (δ a))
  (he : ∀ a, e (algebraMap K A a) = algebraMap K A (δ a))
  (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hb : ∀ i, b i = D K A (u i))
  (hu : ∀ i, e (u i) = 0)

private def logCorrection (d : Derivation k A A) (f g : Aˣ) : Ω[A⁄K] :=
  ((↑f⁻¹ : A) * d (f : A)) • logarithm (K := K) g -
    ((↑g⁻¹ : A) * d (g : A)) • logarithm (K := K) f

include hb hu in
theorem exact_lie_twoLog (f g : Aˣ) :
    onTwo δ d e hd he b (twoLog (K := K) f g) = differential b (logCorrection (K := K) d f g) := by
  let v := correction δ d e hd he
  let ω := twoLog (K := K) f g
  have he₂ : onBasis e (twoBasis b) ω = differential b (logCorrection (K := K) e f g) :=
    onTwo_logarithms δ e he b u hb hu f g
  have hv₂ : lieTwo b v ω = differential b (two v ω) := by
    change differential b (two v ω) + three v (exteriorD2 b (exactFrameDirection b) ω) = _
    rw [closed b u hb f g, map_zero, add_zero]
  have contraction (a : Aˣ) : one v (logarithm (K := K) a) = (↑a⁻¹ : A) * (d (a : A) - e (a : A)) := by
    unfold logarithm
    rw [map_smul, Derivation.liftKaehlerDifferential_comp_D]
    rfl
  have hC : logCorrection (K := K) e f g + two v ω = logCorrection (K := K) d f g := by
    change logCorrection (K := K) e f g + two v (wedge (logarithm (K := K) f) (logarithm (K := K) g)) = _
    rw [two_wedge, contraction, contraction]
    simp only [logCorrection, sub_eq_add_neg, mul_add, mul_neg, add_smul, neg_smul]
    abel
  change onBasis e (twoBasis b) ω + lieTwo b v ω = _
  rw [he₂, hv₂, ← map_add, hC]

end CycleQ2LogarithmicLieNaturality

#print axioms CycleQ2LogarithmicLieNaturality.exact_lie_twoLog

end

section

/-!
# Closedness of the triangular Čech correction before further localization

The correction for replacing g by g + af is already closed on the
single open where the two second equations are invertible. Hence it is
a correction in the Čech–de Rham total differential itself.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2ClosedGeneratorCorrection

open KaehlerDifferential Module
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
  (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hu : ∀ i, b i = D K A (u i))

local notation "∂" => D K A
local notation "J" => exteriorPower.ιMulti A 3

private def front (y z : Ω[A⁄K]) : Ω[A⁄K] →ₗ[A] Form K A 3 where
  toFun x := J ![x,y,z]
  map_add' x w := (J).map_vecCons_add ![y,z] x w
  map_smul' a x := (J).map_vecCons_smul ![y,z] a x

private theorem front_same₁ (y z : Ω[A⁄K]) : front y z y = 0 :=
  (J).map_eq_zero_of_eq _ (by rfl : ![y,y,z] (0 : Fin 3) = ![y,y,z] 1) (by decide)
private theorem front_same₂ (y z : Ω[A⁄K]) : front y z z = 0 :=
  (J).map_eq_zero_of_eq _ (by rfl : ![z,y,z] (0 : Fin 3) = ![z,y,z] 2) (by decide)
private theorem front_swap (x y z : Ω[A⁄K]) : front y z x = -front y x z := by
  have h : ![x,y,z] = ![z,y,x] ∘ Equiv.swap (0 : Fin 3) 2 := by
    funext i
    fin_cases i <;> rfl
  unfold front
  change J ![x,y,z] = -J ![z,y,x]
  rw [h, AlternatingMap.map_swap _ _ (by decide : (0 : Fin 3) ≠ 2)]

include hu in
theorem closed (f a : A) (g h : Aˣ) (he : (h : A) = (g : A) + a * f) :
    exteriorD2 b (exactFrameDirection b)
      ((↑h⁻¹ : A) • wedge (∂ f) (∂ a) -
        (a * (↑g⁻¹ : A) * (↑h⁻¹ : A)) • wedge (∂ f) (∂ (g : A))) = 0 := by
  have hdiff : ∂ (h : A) = ∂ (g : A) + (a • ∂ f + f • ∂ a) := by
    rw [he, map_add, Derivation.leibniz]
  have hinvH : ∂ (↑h⁻¹ : A) = -((↑h⁻¹ : A)^2) • ∂ (h : A) :=
    (∂).leibniz_of_mul_eq_one (by simp)
  have hinvG : ∂ (↑g⁻¹ : A) = -((↑g⁻¹ : A)^2) • ∂ (g : A) :=
    (∂).leibniz_of_mul_eq_one (by simp)
  have H (r x y : A) : exteriorD2 b (exactFrameDirection b) (r • wedge (∂ x) (∂ y)) =
      front (∂ x) (∂ y) (∂ r) := exteriorD2_exactFrame b u hu r x y
  rw [map_sub, H, H, hinvH, hdiff]
  have hfirst : front (∂ f) (∂ a) (-((↑h⁻¹ : A)^2) • (∂ (g : A) + (a • ∂ f + f • ∂ a))) =
      ((↑h⁻¹ : A)^2) • front (∂ f) (∂ (g : A)) (∂ a) := by
    rw [map_smul, map_add, map_add, map_smul, map_smul, front_same₁, front_same₂,
      smul_zero, smul_zero, add_zero, add_zero, front_swap]
    simp only [neg_smul, smul_neg, neg_neg]
  rw [hfirst]
  have hsecond : front (∂ f) (∂ (g : A)) (∂ (a * (↑g⁻¹ : A) * (↑h⁻¹ : A))) =
      ((↑g⁻¹ : A) * (↑h⁻¹ : A) - a * (↑g⁻¹ : A) * ((↑h⁻¹ : A)^2) * f) •
        front (∂ f) (∂ (g : A)) (∂ a) := by
    rw [Derivation.leibniz, Derivation.leibniz, hinvH, hinvG, hdiff]
    simp only [map_add, map_smul, map_neg, front_same₁, front_same₂, smul_zero, add_zero, zero_add,
      smul_neg, neg_zero, smul_smul, sub_eq_add_neg, add_smul, neg_smul]
    module
  rw [hsecond]
  suffices hcoef : (↑g⁻¹ : A) * (↑h⁻¹ : A) - a * (↑g⁻¹ : A) * ((↑h⁻¹ : A)^2) * f = (↑h⁻¹ : A)^2 by
    rw [hcoef, sub_self]
  have h₁ : (↑h⁻¹ : A)^2 * (h : A) = (↑h⁻¹ : A) := by
    rw [pow_two, mul_assoc, Units.inv_mul, mul_one]
  have h₂ : (↑g⁻¹ : A) * (g : A) = 1 := Units.inv_mul g
  linear_combination - (↑g⁻¹ : A) * h₁ + (↑g⁻¹ : A) * (↑h⁻¹ : A)^2 * he + (↑h⁻¹ : A)^2 * h₂

end CycleQ2ClosedGeneratorCorrection

#print axioms CycleQ2ClosedGeneratorCorrection.closed

end

section

/-!
# The closed correction witnessing equality of the local cycle cochains

The triangular change in the second equation has a closed correction
on the single open D(gh). Its ordinary pullback to D(fgh) is exactly
the difference of the two logarithmic cochains.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2ClosedGeneratorWitness

open KaehlerDifferential Module
open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2DoubleLogarithmicClass CycleQ2LogarithmicGeneratorChange

variable {K A T : Type} [CommRing K] [CommRing A] [CommRing T] [Algebra K A] [Algebra K T]
  (φ : A →ₐ[K] T)
  (b : Basis (Fin 3) A Ω[A⁄K]) (u : Fin 3 → A) (hu : ∀ i, b i = D K A (u i))

private theorem pull_exact_wedge (x y : A) :
    exteriorPullback φ 2 (wedge (D K A x) (D K A y)) =
      wedge (D K T (φ x)) (D K T (φ y)) := by
  have l : (D K A ∘ ![x,y]) = ![D K A x,D K A y] := by
    funext i
    fin_cases i <;> rfl
  have r : (D K T ∘ (φ ∘ ![x,y])) = ![D K T (φ x),D K T (φ y)] := by
    funext i
    fin_cases i <;> rfl
  have e := exteriorPullback_d φ 2 ![x,y]
  rw [l, r] at e
  exact e

include hu in
theorem exists_closed_correction (f a : A) (g h : Aˣ) (F : Tˣ)
    (hf : φ f = (F : T)) (he : (h : A) = (g : A) + a * f) :
    ∃ η : Form K A 2,
      exteriorD2 b (exactFrameDirection b) η = 0 ∧
      exteriorPullback φ 2 η =
        twoLog (K := K) F (Units.map φ.toRingHom h) - twoLog (K := K) F (Units.map φ.toRingHom g) := by
  refine ⟨(↑h⁻¹ : A) • wedge (D K A f) (D K A a) -
        (a * (↑g⁻¹ : A) * (↑h⁻¹ : A)) • wedge (D K A f) (D K A (g : A)),
    CycleQ2ClosedGeneratorCorrection.closed b u hu f a g h he, ?_⟩
  have hφ : ((Units.map φ.toRingHom h : Tˣ) : T) = ((Units.map φ.toRingHom g : Tˣ) : T) + φ a * (F : T) := by
    change φ (h : A) = φ (g : A) + φ a * (F : T)
    rw [he, map_add, map_mul, hf]
  rw [twoLog_shear F _ _ (φ a) hφ, map_sub, map_smulₛₗ, map_smulₛₗ,
    pull_exact_wedge, pull_exact_wedge, hf, map_mul, map_mul]
  rfl

end CycleQ2ClosedGeneratorWitness

#print axioms CycleQ2ClosedGeneratorWitness.exists_closed_correction

end

section

noncomputable section

namespace CycleQ2NativeGeneratorChange

open CycleQ2WeightedCoordinateExterior CycleQ2ExactFrameThreeDeRham
open CycleQ2NativeDoubleLocalization KaehlerDifferential Module
open CycleQ2ClosedGeneratorWitness

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A] (f g h : A)

/-- The two original cochains differ, on their common refinement, by the
horizontal restriction of a closed two-form on the single open `D(gh)`.
Its vertical contribution to the total differential is zero. -/
theorem closed_correction_on_refinement (a : A) (he : h = g + a * f)
    (b : Basis (Fin 3) (R g h) Ω[R g h⁄K])
    (u : Fin 3 → R g h) (hu : ∀ i, b i = D K (R g h) (u i)) :
    ∃ η : Form K (R g h) 2,
      exteriorD2 b (exactFrameDirection b) η = 0 ∧
      exteriorPullback (ψ (K := K) f g h) 2 η =
        exteriorPullback (refinement (K := K) f g h h (dvd_mul_left h g)) 2 (cochain (K := K) f h) -
        exteriorPullback (refinement (K := K) f g h g (dvd_mul_right g h)) 2 (cochain (K := K) f g) := by
  have hrel : (hR g h : R g h) = (gR g h : R g h) +
      algebraMap A (R g h) a * algebraMap A (R g h) f := by
    rw [hR, gR, IsUnit.unit_spec, IsUnit.unit_spec, ← map_mul, ← map_add, ← he]
  have hF : ψ (K := K) f g h (algebraMap A (R g h) f) = (F (K := K) f g h : S f g h) :=
    (ψ_algebra f g h f).trans (F_val f g h).symm
  obtain ⟨η, hη, hEq⟩ := exists_closed_correction (ψ (K := K) f g h) b u hu
    (algebraMap A (R g h) f) (algebraMap A (R g h) a) (gR g h) (hR g h) (F (K := K) f g h) hF hrel
  refine ⟨η,hη,?_⟩
  rw [refine_cochain f g h h _ (H (K := K) f g h) (H_val f g h),
    refine_cochain f g h g _ (G (K := K) f g h) (G_val f g h)]
  exact hEq

end CycleQ2NativeGeneratorChange

#print axioms CycleQ2NativeGeneratorChange.closed_correction_on_refinement

end

end
