import Proposal.GeometricTarget11Part03

/-! Continuation of GeometricTarget11.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: continuation_20261112/AffineFiniteTopCohomology.lean -/
section Q2UncompiledFiniteTopDeRham

/-!
# Finite field trace on the actual generic-point top de Rham quotient

DEVELOPMENT CONTINUATION. Compilation status is recorded in solution.md.

For a finite extension of the protected affine function field, this file
constructs its actual relative Kähler module, the pulled-back coordinate
basis, genuine exterior forms, the degree-three exterior differential, and
normalized trace on three-forms and four-forms. Trace commutes with that
differential and is a left inverse to exterior pullback. Consequently the
pullback on the existing `CycleQ2AffineTopCohomology.TopDeRham` is injective.

The complex algebra structure on the extension is required to be the one
compatible with the given tower. Finite separability follows from the base
field's characteristic zero; no geometric existence hypothesis is added.

This constructs finite-cover descent. It does not prove that the protected
residue class vanishes, and does not replace `missing_geometric_existence`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace CycleQ2AffineFiniteTopCohomology

open scoped BigOperators TensorProduct

abbrev K := CycleQ2AffineHypersurface.AffineFunctionField

local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

local instance coefficientIntAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra ℂ L] [IsScalarTower ℂ K L]

abbrev Omega := Ω[L⁄ℂ]
abbrev d : Derivation ℂ L (Omega L) := KaehlerDifferential.D ℂ L

theorem tangent_complex_constant (j : Fin 4) (c : ℂ) :
    CycleQ2AffineFiniteDescent.tangent L j (algebraMap ℂ L c) = 0 := by
  rw [IsScalarTower.algebraMap_apply ℂ K L]
  exact CycleQ2AffineFiniteDescent.tangent_complex_constant L j c

theorem tangent_complex_smul (j : Fin 4) (c : ℂ) (z : L) :
    CycleQ2AffineFiniteDescent.tangent L j (c • z) =
      c • CycleQ2AffineFiniteDescent.tangent L j z := by
  simp only [Algebra.smul_def, Derivation.leibniz, smul_eq_mul,
    tangent_complex_constant, mul_zero, add_zero]
  simp

/-- The already constructed finite-extension tangent, with its actual
complex linearity included in the type. -/
def complexTangent (j : Fin 4) : Derivation ℂ L L where
  toFun := CycleQ2AffineFiniteDescent.tangent L j
  map_add' := (CycleQ2AffineFiniteDescent.tangent L j).map_add
  map_smul' := tangent_complex_smul L j
  map_one_eq_zero' := (CycleQ2AffineFiniteDescent.tangent L j).map_one_eq_zero
  leibniz' := (CycleQ2AffineFiniteDescent.tangent L j).leibniz

@[simp] theorem complexTangent_apply (j : Fin 4) (z : L) :
    complexTangent L j z = CycleQ2AffineFiniteDescent.tangent L j z := rfl

/-- The canonical pullback of universal one-forms, rather than an abstract
vector space supplied with a coordinate label. -/
def oneFormPullback : CycleQ2AffineDifferentials.Omega →ₗ[K] Omega L :=
  KaehlerDifferential.map ℂ ℂ K L

def coordinateDifferential (j : Fin 4) : Omega L :=
  d L (algebraMap K L
    (CycleQ2AffineHypersurface.affineMap (MvPolynomial.X j.succ)))

@[simp] theorem oneFormPullback_coordinateBasis (j : Fin 4) :
    oneFormPullback L (CycleQ2AffineDifferentials.coordinateBasis j) =
      coordinateDifferential L j := by
  rw [CycleQ2AffineDifferentials.coordinateBasis_apply]
  exact KaehlerDifferential.map_D ℂ ℂ K L _

def coordinateMap : Omega L →ₗ[L] (Fin 4 → L) :=
  LinearMap.pi fun j => (complexTangent L j).liftKaehlerDifferential

@[simp] theorem coordinateMap_d (z : L) (j : Fin 4) :
    coordinateMap L (d L z) j = CycleQ2AffineFiniteDescent.tangent L j z :=
  Derivation.liftKaehlerDifferential_comp_D (complexTangent L j) z

@[simp] theorem coordinateMap_coordinateDifferential (i j : Fin 4) :
    coordinateMap L (coordinateDifferential L i) j =
      if i = j then 1 else 0 := by
  rw [coordinateDifferential, coordinateMap_d,
    CycleQ2AffineFiniteDescent.tangent_algebraMap,
    CycleQ2AffineHypersurface.affineTangent_coordinate]
  split_ifs <;> simp

def coordinateExpansion : (Fin 4 → L) →ₗ[L] Omega L :=
  Fintype.linearCombination L (coordinateDifferential L)

@[simp] theorem coordinateExpansion_apply (v : Fin 4 → L) :
    coordinateExpansion L v = ∑ j, v j • coordinateDifferential L j := rfl

/-- Finite separability makes the relative module Ω[L/K] zero. The
transitivity sequence therefore says that actual base one-forms span Ω[L/ℂ]. -/
theorem oneFormBaseChange_surjective :
    Function.Surjective (KaehlerDifferential.mapBaseChange ℂ K L) := by
  letI : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_isSeparable K L
  rw [← LinearMap.range_eq_top, KaehlerDifferential.range_mapBaseChange]
  apply top_unique
  intro ω _
  change KaehlerDifferential.map ℂ K L L ω = 0
  exact Subsingleton.elim _ _

private theorem coordinateExpansion_coordinateMap_pullback
    (ω : CycleQ2AffineDifferentials.Omega) :
    coordinateExpansion L (coordinateMap L (oneFormPullback L ω)) =
      oneFormPullback L ω := by
  have h : (((coordinateExpansion L).comp (coordinateMap L)).restrictScalars K).comp
      (oneFormPullback L) = oneFormPullback L := by
    apply CycleQ2AffineDifferentials.coordinateBasis.ext
    intro i
    change coordinateExpansion L
        (coordinateMap L
          (oneFormPullback L (CycleQ2AffineDifferentials.coordinateBasis i))) =
      oneFormPullback L (CycleQ2AffineDifferentials.coordinateBasis i)
    rw [oneFormPullback_coordinateBasis]
    simp [coordinateExpansion_apply, eq_comm]
  exact LinearMap.congr_fun h ω

theorem coordinateExpansion_coordinateMap :
    (coordinateExpansion L).comp (coordinateMap L) = LinearMap.id := by
  apply LinearMap.ext
  intro ω
  obtain ⟨u, rfl⟩ := oneFormBaseChange_surjective L ω
  change coordinateExpansion L
      (coordinateMap L (KaehlerDifferential.mapBaseChange ℂ K L u)) =
    KaehlerDifferential.mapBaseChange ℂ K L u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a η =>
      simp only [KaehlerDifferential.mapBaseChange_tmul]
      change coordinateExpansion L (coordinateMap L (a • oneFormPullback L η)) =
        a • oneFormPullback L η
      rw [map_smul, map_smul, coordinateExpansion_coordinateMap_pullback]
  | add u v hu hv => simp only [map_add, hu, hv]

theorem coordinateMap_coordinateExpansion :
    (coordinateMap L).comp (coordinateExpansion L) = LinearMap.id := by
  ext v j
  simp [coordinateExpansion_apply, coordinateMap_coordinateDifferential,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, eq_comm]

def differentialCoordinates : Omega L ≃ₗ[L] (Fin 4 → L) where
  toLinearMap := coordinateMap L
  invFun := coordinateExpansion L
  left_inv z := LinearMap.congr_fun (coordinateExpansion_coordinateMap L) z
  right_inv v := LinearMap.congr_fun (coordinateMap_coordinateExpansion L) v

/-- This basis is derived from universal differentials and separability.
It is not a chosen basis of an unrelated four-dimensional space. -/
def coordinateBasis : Module.Basis (Fin 4) L (Omega L) :=
  Module.Basis.ofEquivFun (differentialCoordinates L)

@[simp] theorem coordinateBasis_apply (j : Fin 4) :
    coordinateBasis L j = coordinateDifferential L j := by
  rw [coordinateBasis, Module.Basis.coe_ofEquivFun]
  change coordinateExpansion L (Pi.single j 1) = coordinateDifferential L j
  simp [coordinateExpansion]

@[simp] theorem coordinateBasis_repr_d (z : L) (j : Fin 4) :
    (coordinateBasis L).repr (d L z) j =
      CycleQ2AffineFiniteDescent.tangent L j z := by
  rw [coordinateBasis, Module.Basis.ofEquivFun_repr_apply]
  exact coordinateMap_d L z j

theorem differential_coordinates (z : L) :
    d L z = ∑ j, CycleQ2AffineFiniteDescent.tangent L j z •
      coordinateDifferential L j := by
  have h := LinearMap.congr_fun (coordinateExpansion_coordinateMap L) (d L z)
  simpa only [LinearMap.comp_apply, LinearMap.id_apply,
    coordinateExpansion_apply, coordinateMap_d] using h.symm

abbrev Form (p : ℕ) := ⋀[L]^p (Omega L)

def thirdBasis : Module.Basis (Fin 4) L (Form L 3) :=
  ((coordinateBasis L).exteriorPower 3).reindex CycleQ2AffineExterior.omitEquiv.symm

theorem thirdBasis_apply (i : Fin 4) :
    thirdBasis L i = exteriorPower.ιMulti L 3
      (i.removeNth (coordinateDifferential L)) := by
  rw [thirdBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change (coordinateBasis L).exteriorPower 3 (CycleQ2AffineExterior.omitIndex i) = _
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  simp only [Function.comp_apply, coordinateBasis_apply,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, CycleQ2AffineExterior.omitIndex,
    Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb, Fin.removeNth]
  rfl

def volume : Form L 4 := exteriorPower.ιMulti L 4 (coordinateDifferential L)

theorem topBasis_apply :
    (coordinateBasis L).exteriorPower 4 CycleQ2AffineExterior.topIndex = volume L := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family volume
  congr 1
  funext j
  rw [Function.comp_apply, coordinateBasis_apply]
  have ho : (fun i : Fin 4 => i) =
      (Finset.univ : Finset (Fin 4)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique _ (fun _ => Finset.mem_univ _) strictMono_id
  exact congrArg (coordinateDifferential L) (congrFun ho j).symm

def volumeCoefficient : Form L 4 →ₗ[L] L :=
  ((coordinateBasis L).exteriorPower 4).coord CycleQ2AffineExterior.topIndex

@[simp] theorem volumeCoefficient_volume : volumeCoefficient L (volume L) = 1 := by
  rw [← topBasis_apply]
  simp [volumeCoefficient]

theorem topForm_eq_coefficient (ω : Form L 4) :
    ω = volumeCoefficient L ω • volume L := by
  calc
    ω = ∑ s, ((coordinateBasis L).exteriorPower 4).repr ω s •
        (coordinateBasis L).exteriorPower 4 s :=
      (((coordinateBasis L).exteriorPower 4).sum_repr ω).symm
    _ = _ := by
      rw [Finset.sum_eq_single CycleQ2AffineExterior.topIndex]
      · rw [topBasis_apply]
        rfl
      · intro i hi hne
        exact (hne (CycleQ2AffineExterior.topIndex_unique i)).elim
      · simp

def wedgeOneThree : Omega L →ₗ[L] (Form L 3 →ₗ[L] Form L 4) :=
  exteriorPower.alternatingMapLinearEquiv.toLinearMap.comp
    (exteriorPower.ιMulti L 4).curryLeft

@[simp] theorem wedgeOneThree_wedge (a : Omega L) (v : Fin 3 → Omega L) :
    wedgeOneThree L a (exteriorPower.ιMulti L 3 v) =
      exteriorPower.ιMulti L 4 (Matrix.vecCons a v) := by
  simp [wedgeOneThree]

@[simp] theorem wedgeOneThree_basis (a : Omega L) (i : Fin 4) :
    wedgeOneThree L a (thirdBasis L i) =
      exteriorPower.ιMulti L 4
        (Matrix.vecCons a (i.removeNth (coordinateDifferential L))) := by
  rw [thirdBasis_apply, wedgeOneThree_wedge]

theorem wedge_coordinate_basis (j i : Fin 4) :
    wedgeOneThree L (coordinateDifferential L j) (thirdBasis L i) =
      (if j = i then (-1 : L) ^ i.val else 0) • volume L := by
  rw [wedgeOneThree_basis]
  by_cases h : j = i
  · subst j
    rw [if_pos rfl]
    have hh := (exteriorPower.ιMulti L 4).neg_one_pow_smul_map_insertNth i
      (coordinateDifferential L i) (i.removeNth (coordinateDifferential L))
    rw [Fin.insertNth_self_removeNth] at hh
    simpa only [volume, ← Int.cast_smul_eq_zsmul L, Int.cast_pow,
      Int.cast_neg, Int.cast_one] using hh.symm
  · rw [if_neg h, zero_smul]
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq h
    apply (exteriorPower.ιMulti L 4).map_eq_zero_of_eq (i := 0) (j := k.succ)
    · simp [Fin.removeNth, hk]
    · exact (Fin.succ_ne_zero k).symm

theorem wedge_d_basis (a : L) (i : Fin 4) :
    wedgeOneThree L (d L a) (thirdBasis L i) =
      ((-1 : L) ^ i.val * CycleQ2AffineFiniteDescent.tangent L i a) • volume L := by
  rw [differential_coordinates, map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    wedge_coordinate_basis, smul_smul]
  simp [mul_comm]

/-- The usual differential in the pulled-back basis of exact coordinate
wedges. Its equality to `da ∧ basis` is proved below. -/
def exteriorD3 : Form L 3 →ₗ[ℂ] Form L 4 :=
  ∑ i : Fin 4,
    ((LinearMap.toSpanSingleton L (Form L 4)
      ((-1 : L) ^ i.val • volume L)).restrictScalars ℂ).comp
      ((complexTangent L i).toLinearMap.comp
        (((thirdBasis L).coord i).restrictScalars ℂ))

theorem exteriorD3_apply (η : Form L 3) :
    exteriorD3 L η =
      (∑ i : Fin 4, (-1 : L) ^ i.val *
        CycleQ2AffineFiniteDescent.tangent L i ((thirdBasis L).repr η i)) • volume L := by
  simp only [exteriorD3, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply,
    Module.Basis.coord_apply, Derivation.coeFn_coe, complexTangent_apply,
    smul_smul, ← Finset.sum_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem exteriorD3_smul_basis (a : L) (i : Fin 4) :
    exteriorD3 L (a • thirdBasis L i) =
      wedgeOneThree L (d L a) (thirdBasis L i) := by
  rw [exteriorD3_apply, wedge_d_basis]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, hji, Ne.symm hji]
  · simp

theorem exteriorD3_eq_sum_wedge (η : Form L 3) :
    exteriorD3 L η = ∑ i : Fin 4,
      wedgeOneThree L (d L ((thirdBasis L).repr η i)) (thirdBasis L i) := by
  rw [exteriorD3_apply]
  simp only [wedge_d_basis, Finset.sum_smul]

theorem exteriorD3_leibniz (a : L) (η : Form L 3) :
    exteriorD3 L (a • η) =
      wedgeOneThree L (d L a) η + a • exteriorD3 L η := by
  have hh := congrArg (wedgeOneThree L (d L a)) ((thirdBasis L).sum_repr η)
  simp only [map_sum, map_smul] at hh
  rw [exteriorD3_eq_sum_wedge]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Derivation.leibniz,
    map_add, LinearMap.add_apply, LinearMap.smul_apply, Finset.sum_add_distrib]
  rw [← Finset.smul_sum, ← exteriorD3_eq_sum_wedge, hh]
  exact add_comm _ _

private def targetWedgeOverBase (p : ℕ) :
    (Omega L) [⋀^Fin p]→ₗ[K] (Form L p) where
  toMultilinearMap := (exteriorPower.ιMulti L p).toMultilinearMap.restrictScalars K
  map_eq_zero_of_eq' := (exteriorPower.ιMulti L p).map_eq_zero_of_eq

/-- Pullback on genuine exterior powers, induced by the canonical map on
universal one-forms and the universal alternating property. -/
def exteriorPullback (p : ℕ) :
    CycleQ2AffineExterior.Form p →ₗ[K] Form L p :=
  exteriorPower.alternatingMapLinearEquiv
    ((targetWedgeOverBase L p).compLinearMap (oneFormPullback L))

@[simp] theorem exteriorPullback_ιMulti (p : ℕ)
    (v : Fin p → CycleQ2AffineDifferentials.Omega) :
    exteriorPullback L p (exteriorPower.ιMulti K p v) =
      exteriorPower.ιMulti L p (fun i => oneFormPullback L (v i)) := by
  rw [exteriorPullback, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  rfl

theorem exteriorPullback_basis (p : ℕ) (s : Set.powersetCard (Fin 4) p) :
    exteriorPullback L p (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p s) =
      (coordinateBasis L).exteriorPower p s := by
  simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPullback_ιMulti]
  congr 1
  funext j
  exact (oneFormPullback_coordinateBasis L _).trans (coordinateBasis_apply L _).symm

@[simp] theorem exteriorPullback_thirdBasis (i : Fin 4) :
    exteriorPullback L 3 (CycleQ2AffineExterior.thirdBasis i) = thirdBasis L i := by
  simpa only [CycleQ2AffineExterior.thirdBasis, thirdBasis,
    Module.Basis.reindex_apply, Equiv.symm_symm] using
    exteriorPullback_basis L 3 (CycleQ2AffineExterior.omitEquiv i)

@[simp] theorem exteriorPullback_volume :
    exteriorPullback L 4 CycleQ2AffineExterior.volume = volume L := by
  rw [← CycleQ2AffineExterior.topBasis_apply, ← topBasis_apply]
  exact exteriorPullback_basis L 4 CycleQ2AffineExterior.topIndex

theorem exteriorPullback_three_repr (η : CycleQ2AffineExterior.Form 3) (i : Fin 4) :
    (thirdBasis L).repr (exteriorPullback L 3 η) i =
      algebraMap K L (CycleQ2AffineExterior.thirdBasis.repr η i) := by
  have h : (((thirdBasis L).coord i).restrictScalars K).comp (exteriorPullback L 3) =
      (Algebra.linearMap K L).comp (CycleQ2AffineExterior.thirdBasis.coord i) := by
    apply CycleQ2AffineExterior.thirdBasis.ext
    intro j
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars,
      exteriorPullback_thirdBasis, Module.Basis.coord_apply,
      Module.Basis.repr_self, Finsupp.single_apply, Algebra.linearMap_apply]
    split_ifs <;> simp
  exact LinearMap.congr_fun h η

theorem exteriorPullback_top (ω : CycleQ2AffineExterior.Form 4) :
    exteriorPullback L 4 ω =
      algebraMap K L (CycleQ2AffineExterior.volumeCoefficient ω) • volume L := by
  calc
    exteriorPullback L 4 ω = exteriorPullback L 4
        (CycleQ2AffineExterior.volumeCoefficient ω • CycleQ2AffineExterior.volume) :=
      congrArg (exteriorPullback L 4) (CycleQ2AffineExterior.topForm_eq_coefficient ω)
    _ = CycleQ2AffineExterior.volumeCoefficient ω • volume L := by
      rw [map_smul, exteriorPullback_volume]
    _ = _ := by simp only [IsScalarTower.algebraMap_smul]

/-- Pullback commutes with the actual degree-three exterior differential. -/
theorem exteriorD3_pullback (η : CycleQ2AffineExterior.Form 3) :
    exteriorD3 L (exteriorPullback L 3 η) =
      exteriorPullback L 4 (CycleQ2AffineExterior.exteriorD3 η) := by
  calc
    exteriorD3 L (exteriorPullback L 3 η) =
        (∑ i : Fin 4, (-1 : L) ^ i.val * algebraMap K L
          (CycleQ2AffineHypersurface.affineTangent i
            (CycleQ2AffineExterior.thirdBasis.repr η i))) • volume L := by
      rw [exteriorD3_apply]
      simp only [exteriorPullback_three_repr, CycleQ2AffineFiniteDescent.tangent_algebraMap]
    _ = algebraMap K L (∑ i : Fin 4, (-1 : K) ^ i.val *
        CycleQ2AffineHypersurface.affineTangent i
          (CycleQ2AffineExterior.thirdBasis.repr η i)) • volume L := by
      simp only [map_sum, map_mul, map_pow, map_neg, map_one]
    _ = (∑ i : Fin 4, (-1 : K) ^ i.val *
        CycleQ2AffineHypersurface.affineTangent i
          (CycleQ2AffineExterior.thirdBasis.repr η i)) • volume L := by
      simp only [IsScalarTower.algebraMap_smul]
    _ = exteriorPullback L 4 (CycleQ2AffineExterior.exteriorD3 η) := by
      rw [CycleQ2AffineExterior.exteriorD3_apply, map_smul, exteriorPullback_volume]

private def traceCoefficients : (Fin 4 → L) →ₗ[K] (Fin 4 → K) :=
  LinearMap.pi fun i => (Algebra.normalizedTrace K L).comp (LinearMap.proj i)

/-- Normalized trace of the actual three-form coefficients, in the
pulled-back exact-coordinate wedge basis. -/
def traceThree : Form L 3 →ₗ[K] CycleQ2AffineExterior.Form 3 :=
  CycleQ2AffineExterior.thirdBasis.equivFun.symm.toLinearMap.comp
    ((traceCoefficients L).comp
      ((thirdBasis L).equivFun.toLinearMap.restrictScalars K))

@[simp] theorem traceThree_repr (η : Form L 3) (i : Fin 4) :
    CycleQ2AffineExterior.thirdBasis.repr (traceThree L η) i =
      Algebra.normalizedTrace K L ((thirdBasis L).repr η i) := by
  change CycleQ2AffineExterior.thirdBasis.coord i
      (CycleQ2AffineExterior.thirdBasis.equivFun.symm
        (fun j => Algebra.normalizedTrace K L ((thirdBasis L).repr η j))) = _
  exact Module.Basis.coord_equivFun_symm CycleQ2AffineExterior.thirdBasis i _

/-- Normalized trace of the coefficient of the actual pulled-back top
volume. This is K-linear on forms; its induced cohomology map is C-linear. -/
def traceFour : Form L 4 →ₗ[K] CycleQ2AffineExterior.Form 4 :=
  (LinearMap.toSpanSingleton K (CycleQ2AffineExterior.Form 4)
    CycleQ2AffineExterior.volume).comp
      ((Algebra.normalizedTrace K L).comp ((volumeCoefficient L).restrictScalars K))

@[simp] theorem traceFour_apply (ω : Form L 4) :
    traceFour L ω =
      Algebra.normalizedTrace K L (volumeCoefficient L ω) • CycleQ2AffineExterior.volume :=
  rfl

private theorem trace_signed_tangent (i : Fin 4) (x : L) :
    Algebra.normalizedTrace K L
        ((-1 : L) ^ i.val * CycleQ2AffineFiniteDescent.tangent L i x) =
      (-1 : K) ^ i.val * CycleQ2AffineHypersurface.affineTangent i
        (Algebra.normalizedTrace K L x) := by
  calc
    Algebra.normalizedTrace K L
        ((-1 : L) ^ i.val * CycleQ2AffineFiniteDescent.tangent L i x) =
        Algebra.normalizedTrace K L
          (((-1 : K) ^ i.val) • CycleQ2AffineFiniteDescent.tangent L i x) := by
      simp only [Algebra.smul_def, map_pow, map_neg, map_one]
    _ = (-1 : K) ^ i.val *
        Algebra.normalizedTrace K L (CycleQ2AffineFiniteDescent.tangent L i x) := by
      rw [map_smul, smul_eq_mul]
    _ = _ := by
      rw [HoldoutConstruction.finiteNormalizedTrace_derivation
        (CycleQ2AffineHypersurface.affineTangent i)
        (CycleQ2AffineFiniteDescent.tangent L i)
        (CycleQ2AffineFiniteDescent.tangent_algebraMap L i)]

/-- The chain identity follows from the actual finite-field trace theorem,
with the exterior signs retained. No commutation assumption is supplied. -/
theorem traceFour_exteriorD3 (η : Form L 3) :
    traceFour L (exteriorD3 L η) =
      CycleQ2AffineExterior.exteriorD3 (traceThree L η) := by
  rw [traceFour_apply, exteriorD3_apply, map_smul, volumeCoefficient_volume,
    smul_eq_mul, mul_one, map_sum, CycleQ2AffineExterior.exteriorD3_apply]
  simp only [traceThree_repr]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => trace_signed_tangent L i _)

@[simp] theorem traceThree_pullback (η : CycleQ2AffineExterior.Form 3) :
    traceThree L (exteriorPullback L 3 η) = η := by
  apply CycleQ2AffineExterior.thirdBasis.repr.injective
  ext i
  rw [traceThree_repr, exteriorPullback_three_repr,
    Algebra.normalizedTrace_algebraMap_apply_eq_self]

@[simp] theorem traceFour_pullback (ω : CycleQ2AffineExterior.Form 4) :
    traceFour L (exteriorPullback L 4 ω) = ω := by
  rw [traceFour_apply, exteriorPullback_top, map_smul,
    volumeCoefficient_volume, smul_eq_mul, mul_one,
    Algebra.normalizedTrace_algebraMap_apply_eq_self]
  exact (CycleQ2AffineExterior.topForm_eq_coefficient ω).symm

instance formFiveSubsingleton : Subsingleton (Form L 5) := by
  refine ⟨?_⟩
  intro η ξ
  apply ((coordinateBasis L).exteriorPower 5).repr.injective
  apply Finsupp.ext
  intro s
  have hcard : (s : Finset (Fin 4)).card ≤ 4 := by
    simpa using Finset.card_le_univ (s : Finset (Fin 4))
  have hs : (s : Finset (Fin 4)).card = 5 := s.property
  exact False.elim (by omega)

def exactTopForms : Submodule ℂ (Form L 4) := LinearMap.range (exteriorD3 L)
abbrev TopDeRham := (Form L 4) ⧸ exactTopForms L
def classOf : Form L 4 →ₗ[ℂ] TopDeRham L := (exactTopForms L).mkQ

theorem classOf_eq_zero_iff (ω : Form L 4) :
    classOf L ω = 0 ↔ ∃ η : Form L 3, exteriorD3 L η = ω := by
  change (Submodule.Quotient.mk ω : TopDeRham L) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change ω ∈ LinearMap.range (exteriorD3 L) ↔ _
  exact LinearMap.mem_range

@[simp] theorem classOf_exteriorD3 (η : Form L 3) :
    classOf L (exteriorD3 L η) = 0 :=
  (classOf_eq_zero_iff L _).mpr ⟨η, rfl⟩

/-- Canonical pullback from the existing, unchanged protected TopDeRham. -/
def pullbackClass : CycleQ2AffineTopCohomology.TopDeRham →ₗ[ℂ] TopDeRham L :=
  CycleQ2AffineTopCohomology.descend
    ((classOf L).comp ((exteriorPullback L 4).restrictScalars ℂ)) (by
      intro η
      change classOf L (exteriorPullback L 4 (CycleQ2AffineExterior.exteriorD3 η)) = 0
      rw [← exteriorD3_pullback, classOf_exteriorD3])

/-- Constructed normalized trace on the actual quotient by exact forms. -/
def traceClass : TopDeRham L →ₗ[ℂ] CycleQ2AffineTopCohomology.TopDeRham :=
  (exactTopForms L).liftQ
    (CycleQ2AffineTopCohomology.classOf.comp ((traceFour L).restrictScalars ℂ)) (by
      rintro ω ⟨η, rfl⟩
      change CycleQ2AffineTopCohomology.classOf (traceFour L (exteriorD3 L η)) = 0
      rw [traceFour_exteriorD3, CycleQ2AffineTopCohomology.classOf_exteriorD3])

@[simp] theorem pullbackClass_classOf (ω : CycleQ2AffineExterior.Form 4) :
    pullbackClass L (CycleQ2AffineTopCohomology.classOf ω) =
      classOf L (exteriorPullback L 4 ω) := rfl

@[simp] theorem traceClass_classOf (ω : Form L 4) :
    traceClass L (classOf L ω) =
      CycleQ2AffineTopCohomology.classOf (traceFour L ω) := rfl

/-- Trace is a left inverse on actual top de Rham classes. -/
@[simp] theorem traceClass_pullbackClass (c : CycleQ2AffineTopCohomology.TopDeRham) :
    traceClass L (pullbackClass L c) = c := by
  obtain ⟨ω, rfl⟩ := CycleQ2AffineTopCohomology.exactTopForms.mkQ_surjective c
  change CycleQ2AffineTopCohomology.classOf
      (traceFour L (exteriorPullback L 4 ω)) = CycleQ2AffineTopCohomology.classOf ω
  rw [traceFour_pullback]

theorem pullbackClass_injective : Function.Injective (pullbackClass L) := by
  have h : Function.LeftInverse (traceClass L) (pullbackClass L) :=
    traceClass_pullbackClass L
  exact h.injective

theorem pullbackClass_eq_zero_iff (c : CycleQ2AffineTopCohomology.TopDeRham) :
    pullbackClass L c = 0 ↔ c = 0 := by
  constructor
  · intro h
    apply pullbackClass_injective L
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- A primitive on the finite field descends to an actual rational
three-form on the protected field by the explicitly constructed trace. -/
theorem exact_pullback_iff (ω : CycleQ2AffineExterior.Form 4) :
    (∃ η : Form L 3, exteriorD3 L η = exteriorPullback L 4 ω) ↔
      ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η = ω := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨traceThree L η, ?_⟩
    rw [← traceFour_exteriorD3, hη, traceFour_pullback]
  · rintro ⟨η, hη⟩
    exact ⟨exteriorPullback L 3 η, by rw [exteriorD3_pullback, hη]⟩

/-- Binding of the constructed finite-cover pullback to the original
positive residue source class. It proves preservation and reflection of
vanishing, without asserting that the protected class vanishes. -/
theorem residueClass_pullback_eq_zero_iff (A : HodgeComputer.AmbientPoly 4) :
    classOf L (exteriorPullback L 4 (CycleQ2AffineExactness.residueSourceForm A)) = 0 ↔
      CycleQ2AffineTopCohomology.residueClass A = 0 :=
  pullbackClass_eq_zero_iff L (CycleQ2AffineTopCohomology.residueClass A)

end CycleQ2AffineFiniteTopCohomology

end

end Q2UncompiledFiniteTopDeRham
