import Proposal.GeometricUniversalWeightedClosure
import Proposal.GeometricTarget01Part01
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Derivation.Lie

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
