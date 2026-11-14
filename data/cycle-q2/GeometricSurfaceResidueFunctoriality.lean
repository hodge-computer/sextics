import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Proposal.GeometricSurfaceAdjunction
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.TensorProduct.Tower

section

/-! A determinant identity in genuine exterior powers, used to compare
literal ambient differential volumes in residue constructions. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ResidueWedgeLinear

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem topWedge_eq_det_smul {n : ℕ} (b : Basis (Fin n) R M) (v : Fin n → M) :
    exteriorPower.ιMulti R n v =
      (b.toMatrix v).det • exteriorPower.ιMulti R n b := by
  have he : exteriorPower.ιMulti R n =
      b.det.smulRight (exteriorPower.ιMulti R n b) := by
    apply Basis.ext_alternating b
    intro i hi
    let σ : Equiv.Perm (Fin n) :=
      Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change exteriorPower.ιMulti R n (b ∘ σ) =
      (b.det.smulRight (exteriorPower.ιMulti R n b)) (b ∘ σ)
    simp [AlternatingMap.map_perm, Basis.det_self]
  simpa only [AlternatingMap.smulRight_apply, Basis.det_apply] using
    DFunLike.congr_fun he v

end CycleQ2ResidueWedgeLinear
end

end


section

/-! The conormal-first four-fold wedge factors through the actual rank-two
quotient. The two displayed bases and the actual map determine every coefficient. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ResidueQuotientWedge

open Module CycleQ2ResidueWedgeLinear

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

abbrev BlockIndex := Fin 2 ⊕ Fin 2

def pairFamily (b : Basis BlockIndex R M) (v : Fin 2 → M) : BlockIndex → M :=
  Sum.elim (fun j => b (Sum.inl j)) v

theorem quotient_coordinates (b : Basis BlockIndex R M) (c : Basis (Fin 2) R N)
    (g : M →ₗ[R] N) (hleft : ∀ j, g (b (Sum.inl j)) = 0)
    (hright : ∀ j, g (b (Sum.inr j)) = c j) (x : M) (i : Fin 2) :
    c.repr (g x) i = b.repr x (Sum.inr i) := by
  have he : (c.coord i).comp g = b.coord (Sum.inr i) := by
    apply b.ext
    intro j
    rcases j with j | j <;> simp [hleft, hright, Basis.coord_apply, Finsupp.single_apply]
  exact LinearMap.congr_fun he x

theorem pair_matrix_det (b : Basis BlockIndex R M) (c : Basis (Fin 2) R N)
    (g : M →ₗ[R] N) (hleft : ∀ j, g (b (Sum.inl j)) = 0)
    (hright : ∀ j, g (b (Sum.inr j)) = c j) (v : Fin 2 → M) :
    (b.toMatrix (pairFamily b v)).det = (c.toMatrix (g ∘ v)).det := by
  let upper : Matrix (Fin 2) (Fin 2) R := fun i j => b.repr (v j) (Sum.inl i)
  have hm : b.toMatrix (pairFamily b v) =
      Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) R)
        upper 0 (c.toMatrix (g ∘ v)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Basis.toMatrix_apply, pairFamily, Matrix.one_apply, Matrix.fromBlocks,
        Finsupp.single_apply,
        Function.comp_def, upper,
        quotient_coordinates b c g hleft hright, eq_comm]
  rw [hm, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

/-- In the order (conormal₀,conormal₁,free₀,free₁), the wedge depends only
on the images of its last two entries in the actual quotient module. -/
theorem pair_wedge (b : Basis BlockIndex R M) (c : Basis (Fin 2) R N)
    (g : M →ₗ[R] N) (hleft : ∀ j, g (b (Sum.inl j)) = 0)
    (hright : ∀ j, g (b (Sum.inr j)) = c j) (v : Fin 2 → M) :
    exteriorPower.ιMulti R 4
        (pairFamily b v ∘ (finSumFinEquiv : BlockIndex ≃ Fin 4).symm) =
      (c.toMatrix (g ∘ v)).det •
        exteriorPower.ιMulti R 4 (b.reindex (finSumFinEquiv : BlockIndex ≃ Fin 4)) := by
  rw [topWedge_eq_det_smul (b.reindex (finSumFinEquiv : BlockIndex ≃ Fin 4))]
  have hd : ((b.reindex (finSumFinEquiv : BlockIndex ≃ Fin 4)).toMatrix
      (pairFamily b v ∘ (finSumFinEquiv : BlockIndex ≃ Fin 4).symm)).det =
        (b.toMatrix (pairFamily b v)).det := by
    change (b.reindex (finSumFinEquiv : BlockIndex ≃ Fin 4)).det
      (pairFamily b v ∘ (finSumFinEquiv : BlockIndex ≃ Fin 4).symm) =
        b.det (pairFamily b v)
    rw [Basis.det_reindex]
    congr 1
    funext j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [hd, pair_matrix_det b c g hleft hright]

end CycleQ2ResidueQuotientWedge
end

end


section

/-! Scalar extension of actual top exterior powers. The formula on every
wedge uses the literal tensor map x ↦ 1 ⊗ x and makes the resulting map
independent of the basis used to construct it. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ExteriorTopBaseChange

open Module CycleQ2ResidueWedgeLinear
open scoped TensorProduct

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] {n : ℕ}

def topCoordinate (b : Basis (Fin n) R M) : (⋀[R]^n M) →ₗ[R] R :=
  exteriorPower.alternatingMapLinearEquiv b.det

@[simp] theorem topCoordinate_wedge (b : Basis (Fin n) R M) (v : Fin n → M) :
    topCoordinate b (exteriorPower.ιMulti R n v) = (b.toMatrix v).det := by
  simp only [topCoordinate, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Basis.det_apply]

@[simp] theorem topCoordinate_basis (b : Basis (Fin n) R M) :
    topCoordinate b (exteriorPower.ιMulti R n b) = 1 := by
  simp only [topCoordinate, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    Basis.det_self]

theorem topCoordinate_smul_wedge (b : Basis (Fin n) R M) (w : ⋀[R]^n M) :
    topCoordinate b w • exteriorPower.ιMulti R n b = w := by
  have he : (topCoordinate b).smulRight (exteriorPower.ιMulti R n b) =
      LinearMap.id := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change topCoordinate b (exteriorPower.ιMulti R n v) •
      exteriorPower.ιMulti R n b = exteriorPower.ιMulti R n v
    rw [topCoordinate_wedge]
    exact (topWedge_eq_det_smul b v).symm
  exact LinearMap.congr_fun he w

def topCoordinateEquiv (b : Basis (Fin n) R M) : (⋀[R]^n M) ≃ₗ[R] R :=
  { topCoordinate b with
    invFun := fun a => a • exteriorPower.ιMulti R n b
    left_inv := topCoordinate_smul_wedge b
    right_inv := by
      intro a
      change topCoordinate b (a • exteriorPower.ιMulti R n b) = a
      rw [map_smul, topCoordinate_basis, smul_eq_mul, mul_one] }

def topBaseChange (b : Basis (Fin n) R M) :
    (⋀[R]^n M) →ₛₗ[algebraMap R S] (⋀[S]^n (S ⊗[R] M)) where
  toFun w := algebraMap R S (topCoordinate b w) •
    exteriorPower.ιMulti S n (b.baseChange S)
  map_add' x y := by simp only [map_add, add_smul]
  map_smul' a x := by
    simp only [map_smul, smul_eq_mul, map_mul, mul_smul]

theorem baseChange_matrix (b : Basis (Fin n) R M) (v : Fin n → M) :
    (b.baseChange S).toMatrix (fun j => (1 : S) ⊗ₜ[R] v j) =
      (b.toMatrix v).map (algebraMap R S) := by
  ext i j
  simp [Basis.toMatrix_apply, Basis.baseChange_repr_tmul, Algebra.smul_def]

/-- The map sends every actual wedge to the wedge of the actual tensor images. -/
@[simp] theorem topBaseChange_wedge (b : Basis (Fin n) R M) (v : Fin n → M) :
    topBaseChange (S := S) b (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun j => (1 : S) ⊗ₜ[R] v j) := by
  change algebraMap R S (topCoordinate b (exteriorPower.ιMulti R n v)) •
    exteriorPower.ιMulti S n (b.baseChange S) = _
  rw [topCoordinate_wedge, topWedge_eq_det_smul (b.baseChange S)
    (fun j => (1 : S) ⊗ₜ[R] v j), baseChange_matrix]
  change algebraMap R S ((b.toMatrix v).det) • _ =
    ((algebraMap R S).mapMatrix (b.toMatrix v)).det • _
  rw [← RingHom.map_det]

@[simp] theorem topBaseChange_coordinate (b : Basis (Fin n) R M) (w : ⋀[R]^n M) :
    topCoordinate (b.baseChange S) (topBaseChange (S := S) b w) =
      algebraMap R S (topCoordinate b w) := by
  change topCoordinate (b.baseChange S)
    (algebraMap R S (topCoordinate b w) • exteriorPower.ιMulti S n (b.baseChange S)) = _
  rw [map_smul, topCoordinate_basis, smul_eq_mul, mul_one]

/-- The construction uses no choice of a preferred top-form coordinate. -/
theorem topBaseChange_independent (b c : Basis (Fin n) R M) :
    topBaseChange (S := S) b = topBaseChange (S := S) c := by
  ext w
  conv_lhs => rw [← topCoordinate_smul_wedge b w]
  conv_rhs => rw [← topCoordinate_smul_wedge b w]
  rw [map_smulₛₗ, map_smulₛₗ, topBaseChange_wedge, topBaseChange_wedge]

end CycleQ2ExteriorTopBaseChange
end

end


section

/-! The genuine tensor/exterior scalar-extension equivalence in top rank.
The construction is fixed on actual tensor-wedge generators and independent
of the temporary basis used to prove it is an equivalence. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ExteriorTopTensor

open Module CycleQ2ExteriorTopBaseChange
open scoped TensorProduct

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] {n : ℕ}

@[simp] theorem topCoordinateEquiv_apply (b : Basis (Fin n) R M) (w : ⋀[R]^n M) :
    topCoordinateEquiv b w = topCoordinate b w := rfl

def topTensorEquiv (b : Basis (Fin n) R M) :
    (S ⊗[R] (⋀[R]^n M)) ≃ₗ[S] (⋀[S]^n (S ⊗[R] M)) :=
  ((topCoordinateEquiv b).baseChange R S _ _).trans
    ((TensorProduct.AlgebraTensorModule.rid R S S).trans
      (topCoordinateEquiv (b.baseChange S)).symm)

theorem topTensorEquiv_tmul (b : Basis (Fin n) R M) (s : S) (w : ⋀[R]^n M) :
    topTensorEquiv (S := S) b (s ⊗ₜ[R] w) =
      s • topBaseChange (S := S) b w := by
  apply (topCoordinateEquiv (b.baseChange S)).injective
  simp only [topTensorEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul,
    map_smul, topCoordinateEquiv_apply, topBaseChange_coordinate]
  simp [Algebra.smul_def, mul_comm]

@[simp] theorem topTensorEquiv_wedge (b : Basis (Fin n) R M) (v : Fin n → M) :
    topTensorEquiv (S := S) b
        ((1 : S) ⊗ₜ[R] exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun j => (1 : S) ⊗ₜ[R] v j) := by
  rw [topTensorEquiv_tmul, one_smul, topBaseChange_wedge]

theorem topTensorEquiv_independent (b c : Basis (Fin n) R M) :
    topTensorEquiv (S := S) b = topTensorEquiv (S := S) c := by
  apply LinearEquiv.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro s w
  change topTensorEquiv (S := S) b (s ⊗ₜ[R] w) =
    topTensorEquiv (S := S) c (s ⊗ₜ[R] w)
  rw [topTensorEquiv_tmul, topTensorEquiv_tmul, topBaseChange_independent b c]

end CycleQ2ExteriorTopTensor
end

end


section

/-! Canonical scalar extension of an equivalence between top exterior
powers, with its formula on every actual tensor-wedge generator. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ExteriorTopTransport

open Module CycleQ2ExteriorTopBaseChange CycleQ2ExteriorTopTensor
open scoped TensorProduct

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {m n : ℕ}

def topTensorTransport (b : Basis (Fin m) R M) (c : Basis (Fin n) R N)
    (e : (⋀[R]^m M) ≃ₗ[R] (⋀[R]^n N)) :
    (⋀[S]^m (S ⊗[R] M)) ≃ₗ[S] (⋀[S]^n (S ⊗[R] N)) :=
  (topTensorEquiv (S := S) b).symm.trans
    ((e.baseChange R S _ _).trans (topTensorEquiv (S := S) c))

theorem topTensorTransport_tensor (b : Basis (Fin m) R M) (c : Basis (Fin n) R N)
    (e : (⋀[R]^m M) ≃ₗ[R] (⋀[R]^n N)) (s : S) (w : ⋀[R]^m M) :
    topTensorTransport (S := S) b c e (topTensorEquiv b (s ⊗ₜ[R] w)) =
      topTensorEquiv c (s ⊗ₜ[R] e w) := by
  simp only [topTensorTransport, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]

theorem topTensorTransport_baseChange (b : Basis (Fin m) R M) (c : Basis (Fin n) R N)
    (e : (⋀[R]^m M) ≃ₗ[R] (⋀[R]^n N)) (w : ⋀[R]^m M) :
    topTensorTransport (S := S) b c e (topBaseChange (S := S) b w) =
      topBaseChange (S := S) c (e w) := by
  simpa only [topTensorEquiv_tmul, one_smul] using
    topTensorTransport_tensor b c e (1 : S) w

theorem topTensorTransport_wedge (b : Basis (Fin m) R M) (c : Basis (Fin n) R N)
    (e : (⋀[R]^m M) ≃ₗ[R] (⋀[R]^n N)) (v : Fin m → M) (w : Fin n → N)
    (he : e (exteriorPower.ιMulti R m v) = exteriorPower.ιMulti R n w) :
    topTensorTransport (S := S) b c e
        (exteriorPower.ιMulti S m (fun i => (1 : S) ⊗ₜ[R] v i)) =
      exteriorPower.ιMulti S n (fun i => (1 : S) ⊗ₜ[R] w i) := by
  rw [← topBaseChange_wedge b v, topTensorTransport_baseChange, he,
    topBaseChange_wedge]

end CycleQ2ExteriorTopTransport
end

end


section

/-! The actual local residue is characterized by its conormal-first wedge
in the localized ambient cotangent module. Defining equations have zero
differential in the surface module, so the four-fold wedge lives in the
ambient module restricted to the surface throughout. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceResidueWedge

open Module CycleQ2GeometricSurfaceAdjunction CycleQ2ResidueWedgeLinear
  CycleQ2ResidueQuotientWedge
open scoped TensorProduct

section Determinant

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem determinantEquiv_family (b : Basis (Fin 2) R M) (w : Fin 2 → M) :
    determinantEquiv b (exteriorPower.ιMulti R 2 w) = (b.toMatrix w).det := by
  rw [topWedge_eq_det_smul b, map_smul, determinantEquiv_wedge,
    smul_eq_mul, mul_one]

theorem reordered_basis_det (b c : Basis (Fin 2 ⊕ Fin 2) R M) :
    (((b.reindex (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4)).toMatrix
      (c.reindex (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4)))).det =
        (b.toMatrix c).det := by
  change (b.reindex (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4)).det
      (c.reindex (finSumFinEquiv : (Fin 2 ⊕ Fin 2) ≃ Fin 4)) = b.det c
  rw [Basis.det_reindex]
  apply congrArg b.det
  funext j
  simp only [Basis.coe_reindex, Function.comp_apply, Equiv.symm_apply_apply]

end Determinant

/-- The actual ambient volume in the fixed coordinate order (z,a,b,c). -/
def ambientVolume (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    ⋀[AdjunctionPatch v n t]^4 (LocalAmbientDifferentials v n t) :=
  exteriorPower.ιMulti (AdjunctionPatch v n t) 4
    ((localAmbientBasis v n t).reindex
      (finSumFinEquiv : AmbientIndex ≃ Fin 4))

/-- Its actual determinant coordinate, constructed by the exterior universal property. -/
def ambientVolumeCoordinate (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    (⋀[AdjunctionPatch v n t]^4 (LocalAmbientDifferentials v n t)) →ₗ[
      AdjunctionPatch v n t] AdjunctionPatch v n t :=
  exteriorPower.alternatingMapLinearEquiv
    ((localAmbientBasis v n t).reindex
      (finSumFinEquiv : AmbientIndex ≃ Fin 4)).det

@[simp] theorem ambientVolumeCoordinate_volume (v : Fin 2 → SurfacePoly)
    (n t : SurfacePoly) :
    ambientVolumeCoordinate v n t (ambientVolume v n t) = 1 := by
  simp only [ambientVolumeCoordinate, ambientVolume,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Basis.det_self]

theorem compactAugmented_wedge (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    exteriorPower.ιMulti (AdjunctionPatch v n t) 4
        ((compactAugmentedBasis v n t).reindex
          (finSumFinEquiv : AmbientIndex ≃ Fin 4)) =
      algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)
        (augmentedJacobian v n t) • ambientVolume v n t := by
  have hd : (((localAmbientBasis v n t).reindex
      (finSumFinEquiv : AmbientIndex ≃ Fin 4)).toMatrix
      ((compactAugmentedBasis v n t).reindex
        (finSumFinEquiv : AmbientIndex ≃ Fin 4))).det =
      algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)
        (augmentedJacobian v n t) := by
    have hc : (compactAugmentedBasis v n t :
        AmbientIndex → LocalAmbientDifferentials v n t) = localAugmentedFamily v n t :=
      funext (compactAugmentedBasis_apply v n t)
    calc
      _ = ((localAmbientBasis v n t).toMatrix (compactAugmentedBasis v n t)).det :=
        reordered_basis_det (localAmbientBasis v n t) (compactAugmentedBasis v n t)
      _ = ((localAmbientBasis v n t).toMatrix (localAugmentedFamily v n t)).det :=
        congrArg (fun w : AmbientIndex → LocalAmbientDifferentials v n t =>
          ((localAmbientBasis v n t).toMatrix w).det) hc
      _ = (((ambientBasis v).toMatrix (augmentedFamily v n t)).map
          (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t))).det :=
        congrArg Matrix.det (localAugmentedMatrix v n t)
      _ = _ := (RingHom.map_det (algebraMap (SurfaceChartRing v)
        (AdjunctionPatch v n t)) ((ambientBasis v).toMatrix (augmentedFamily v n t))).symm
  exact (topWedge_eq_det_smul ((localAmbientBasis v n t).reindex
    (finSumFinEquiv : AmbientIndex ≃ Fin 4))
    ((compactAugmentedBasis v n t).reindex
      (finSumFinEquiv : AmbientIndex ≃ Fin 4))).trans
    (congrArg (fun a : AdjunctionPatch v n t => a • ambientVolume v n t) hd)

theorem localSurfaceDeterminantEquiv_apply (v : Fin 2 → SurfacePoly)
    (n t : SurfacePoly)
    (w : ⋀[AdjunctionPatch v n t]^2
      (KaehlerDifferential ℂ (AdjunctionPatch v n t))) :
    localSurfaceDeterminantEquiv v n t w =
      algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)
        (augmentedJacobian v n t) *
        determinantEquiv (localSurfaceKaehlerBasis v n t) w := by
  change (↑(IsLocalization.Away.algebraMap_isUnit
    (S := AdjunctionPatch v n t) (augmentedJacobian v n t)).unit :
      AdjunctionPatch v n t) * _ = _
  rw [IsUnit.unit_spec]
  rfl

/-- The actual conormal-first wedge map on the surface determinant.
The lift formula below binds it to the ambient cotangent exact sequence. -/
def residueWedgeMap (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    (⋀[AdjunctionPatch v n t]^2
      (KaehlerDifferential ℂ (AdjunctionPatch v n t))) →ₗ[AdjunctionPatch v n t]
      (⋀[AdjunctionPatch v n t]^4 (LocalAmbientDifferentials v n t)) :=
  (localSurfaceDeterminantEquiv v n t).toLinearMap.smulRight
    (ambientVolume v n t)

theorem residueWedgeMap_lifts (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
    (w : Fin 2 → LocalAmbientDifferentials v n t) :
    residueWedgeMap v n t
        (exteriorPower.ιMulti (AdjunctionPatch v n t) 2
          (localToKaehler v n t ∘ w)) =
      exteriorPower.ιMulti (AdjunctionPatch v n t) 4
        (pairFamily (compactAugmentedBasis v n t) w ∘
          (finSumFinEquiv : AmbientIndex ≃ Fin 4).symm) := by
  have hl (j : Fin 2) : localToKaehler v n t
      (compactAugmentedBasis v n t (Sum.inl j)) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [localToKaehler_kernel_compact]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hr (j : Fin 2) : localToKaehler v n t
      (compactAugmentedBasis v n t (Sum.inr j)) =
      localSurfaceKaehlerBasis v n t j := by
    rw [localSurfaceKaehlerBasis, quotientBasis_apply]
  have hw := pair_wedge (compactAugmentedBasis v n t)
    (localSurfaceKaehlerBasis v n t) (localToKaehler v n t) hl hr w
  have ha := compactAugmented_wedge v n t
  let d : AdjunctionPatch v n t :=
    ((localSurfaceKaehlerBasis v n t).toMatrix (localToKaehler v n t ∘ w)).det
  let j : AdjunctionPatch v n t := algebraMap (SurfaceChartRing v)
    (AdjunctionPatch v n t) (augmentedJacobian v n t)
  have hd : localSurfaceDeterminantEquiv v n t
      (exteriorPower.ιMulti (AdjunctionPatch v n t) 2
        (localToKaehler v n t ∘ w)) = j * d :=
    (localSurfaceDeterminantEquiv_apply v n t _).trans
      (congrArg (fun a : AdjunctionPatch v n t => j * a)
        (determinantEquiv_family (localSurfaceKaehlerBasis v n t)
          (localToKaehler v n t ∘ w)))
  change localSurfaceDeterminantEquiv v n t
    (exteriorPower.ιMulti (AdjunctionPatch v n t) 2
      (localToKaehler v n t ∘ w)) • ambientVolume v n t = _
  calc
    _ = (j * d) • ambientVolume v n t :=
      congrArg (fun a : AdjunctionPatch v n t => a • ambientVolume v n t) hd
    _ = d • (j • ambientVolume v n t) :=
      (congrArg (fun a : AdjunctionPatch v n t => a • ambientVolume v n t)
        (mul_comm j d)).trans (mul_smul d j (ambientVolume v n t))
    _ = d • exteriorPower.ιMulti (AdjunctionPatch v n t) 4
        ((compactAugmentedBasis v n t).reindex
          (finSumFinEquiv : AmbientIndex ≃ Fin 4)) :=
      congrArg (fun x : ⋀[AdjunctionPatch v n t]^4 (LocalAmbientDifferentials v n t) =>
        d • x) ha.symm
    _ = _ := hw.symm

theorem residueWedgeMap_actual_lifts (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
    (w : Fin 2 → LocalAmbientDifferentials v n t) :
    residueWedgeMap v n t
        (exteriorPower.ιMulti (AdjunctionPatch v n t) 2
          (localToKaehler v n t ∘ w)) =
      exteriorPower.ιMulti (AdjunctionPatch v n t) 4
        (Sum.elim (fun j => (1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v]
          ambientDifferential v (v j)) w ∘
          (finSumFinEquiv : AmbientIndex ≃ Fin 4).symm) := by
  simpa only [pairFamily, compactAugmentedBasis_apply,
    localAugmentedFamily, augmentedFamily, Sum.elim_inl] using
    residueWedgeMap_lifts v n t w

theorem residueWedgeMap_injective (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    Function.Injective (residueWedgeMap v n t) := by
  intro x y h
  apply (localSurfaceDeterminantEquiv v n t).injective
  have hh := congrArg (ambientVolumeCoordinate v n t) h
  change ambientVolumeCoordinate v n t
      (localSurfaceDeterminantEquiv v n t x • ambientVolume v n t) =
    ambientVolumeCoordinate v n t
      (localSurfaceDeterminantEquiv v n t y • ambientVolume v n t) at hh
  simpa only [map_smul, ambientVolumeCoordinate_volume, smul_eq_mul, mul_one] using hh

@[simp] theorem residueWedgeMap_residue (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    residueWedgeMap v n t (localSurfaceResidueForm v n t) = ambientVolume v n t := by
  change localSurfaceDeterminantEquiv v n t (localSurfaceResidueForm v n t) •
    ambientVolume v n t = ambientVolume v n t
  rw [localSurfaceResidueForm_normalization, one_smul]

/-- The normalization determines the actual residue uniquely. -/
theorem residueWedgeMap_eq_volume_iff (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
    (w : ⋀[AdjunctionPatch v n t]^2
      (KaehlerDifferential ℂ (AdjunctionPatch v n t))) :
    residueWedgeMap v n t w = ambientVolume v n t ↔
      w = localSurfaceResidueForm v n t := by
  rw [← residueWedgeMap_residue v n t]
  exact (residueWedgeMap_injective v n t).eq_iff

end CycleQ2SurfaceResidueWedge
end

end


section

/-! Naturality of the genuine conormal-first exterior map. The statements
retain the actual quotient maps and the ambient linear map. A later chart
specialization must prove those maps and the conormal/volume factors. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ResidueWedgeNaturality

open Module CycleQ2ResidueQuotientWedge

variable {R M N Q : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q]

def conormalFamily (c w : Fin 2 → M) : Fin 4 → M :=
  ![c 0, c 1, w 0, w 1]

theorem conormalFamily_pair (b : Basis BlockIndex R M) (w : Fin 2 → M) :
    pairFamily b w ∘ (finSumFinEquiv : BlockIndex ≃ Fin 4).symm =
      conormalFamily (fun j => b (Sum.inl j)) w := by
  funext j
  fin_cases j <;> rfl

theorem conormalFamily_map (f : M →ₗ[R] N) (c w : Fin 2 → M) :
    f ∘ conormalFamily c w = conormalFamily (f ∘ c) (f ∘ w) := by
  funext j
  fin_cases j <;> rfl

theorem conormalFamily_wedge_smul (a b : R) (c w : Fin 2 → M) :
    exteriorPower.ιMulti R 4
        (conormalFamily (fun j => ![a,b] j • c j) w) =
      (a * b) • exteriorPower.ιMulti R 4 (conormalFamily c w) := by
  have he : (fun j : Fin 4 => ![a,b,1,1] j • conormalFamily c w j) =
      conormalFamily (fun j => ![a,b] j • c j) w := by
    funext j
    fin_cases j <;> simp [conormalFamily]
  have h := (exteriorPower.ιMulti R 4 (M := M)).map_smul_univ
    (![a,b,1,1] : Fin 4 → R) (conormalFamily c w)
  rw [he] at h
  simpa [Fin.prod_univ_four] using h

/-- The two quotient diagrams and their literal lift formulas force
the exterior transition. No chosen coordinates on the quotient are needed. -/
theorem conormal_wedge_naturality
    (q : M →ₗ[R] Q) (q' : N →ₗ[R] Q) (f : M →ₗ[R] N)
    (c : Fin 2 → M) (c' : Fin 2 → N) (a b : R)
    (W : (⋀[R]^2 Q) →ₗ[R] (⋀[R]^4 M))
    (W' : (⋀[R]^2 Q) →ₗ[R] (⋀[R]^4 N))
    (hq : Function.Surjective q) (hcomm : ∀ x, q' (f x) = q x)
    (hc : ∀ j, f (c j) = ![a,b] j • c' j)
    (hW : ∀ w : Fin 2 → M,
      W (exteriorPower.ιMulti R 2 (q ∘ w)) =
        exteriorPower.ιMulti R 4 (conormalFamily c w))
    (hW' : ∀ w : Fin 2 → N,
      W' (exteriorPower.ιMulti R 2 (q' ∘ w)) =
        exteriorPower.ιMulti R 4 (conormalFamily c' w)) :
    (exteriorPower.map 4 f).comp W = (a * b) • W' := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro z
  choose w hw using fun i : Fin 2 => hq (z i)
  have hz : q ∘ w = z := funext hw
  have hz' : q' ∘ (f ∘ w) = z :=
    funext (fun i => (hcomm (w i)).trans (hw i))
  have hfc : f ∘ c = fun j => ![a,b] j • c' j := funext hc
  change exteriorPower.map 4 f (W (exteriorPower.ιMulti R 2 z)) =
    (a * b) • W' (exteriorPower.ιMulti R 2 z)
  calc
    _ = exteriorPower.ιMulti R 4 (f ∘ conormalFamily c w) := by
      rw [← hz, hW, exteriorPower.map_apply_ιMulti]
    _ = exteriorPower.ιMulti R 4
        (conormalFamily (fun j => ![a,b] j • c' j) (f ∘ w)) := by
      rw [conormalFamily_map, hfc]
    _ = (a * b) • exteriorPower.ιMulti R 4 (conormalFamily c' (f ∘ w)) :=
      conormalFamily_wedge_smul a b c' (f ∘ w)
    _ = (a * b) • W' (exteriorPower.ιMulti R 2 z) := by
      rw [← hW' (f ∘ w), hz']

section Normalization

variable {E V V' : Type*} [AddCommGroup E] [Module R E]
  [AddCommGroup V] [Module R V] [AddCommGroup V'] [Module R V']

/-- The transition coefficient is forced by the conormal factor and
ambient-volume factor once both actual residue normalizations are fixed. -/
theorem normalized_transition
    (W : E →ₗ[R] V) (W' : E →ₗ[R] V') (f : V →ₗ[R] V')
    (a d k : R) (hd : d * a = 1)
    (η η' : E) (volume : V) (volume' : V')
    (hinj : Function.Injective W')
    (hη : W η = volume) (hη' : W' η' = volume')
    (hmap : f.comp W = a • W') (hvolume : f volume = k • volume') :
    η = (d * k) • η' := by
  apply hinj
  rw [map_smul]
  have h : a • W' η = k • W' η' := by
    calc
      _ = f (W η) := (LinearMap.congr_fun hmap η).symm
      _ = f volume := congrArg f hη
      _ = k • volume' := hvolume
      _ = k • W' η' := congrArg (fun x : V' => k • x) hη'.symm
  have hh := congrArg (fun x : V' => d • x) h
  simpa only [smul_smul, hd, one_smul] using hh

end Normalization

end CycleQ2ResidueWedgeNaturality
end

end


section

/-! The actual conormal wedge equivalence and its canonical scalar
extension. The four-fold forms remain in the surface-restricted ambient
cotangent module. The tensor-lift formula binds the transported map to
the literal conormal differentials and the original cotangent quotient. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceResidueScalarExtension

open Module CycleQ2GeometricSurfaceAdjunction CycleQ2SurfaceResidueWedge
  CycleQ2ExteriorTopBaseChange CycleQ2ExteriorTopTensor CycleQ2ResidueQuotientWedge
  CycleQ2ExteriorTopTransport
open scoped TensorProduct

section ExteriorEquiv

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

def exteriorLinearEquiv (d : ℕ) (e : M ≃ₗ[R] N) :
    (⋀[R]^d M) ≃ₗ[R] (⋀[R]^d N) :=
  LinearEquiv.ofBijective (exteriorPower.map d e.toLinearMap)
    ⟨exteriorPower.map_injective e.symm.toLinearMap (by
      ext x
      exact e.symm_apply_apply x), exteriorPower.map_surjective e.surjective⟩

@[simp] theorem exteriorLinearEquiv_apply (d : ℕ) (e : M ≃ₗ[R] N)
    (w : ⋀[R]^d M) :
    exteriorLinearEquiv d e w = exteriorPower.map d e.toLinearMap w := rfl

end ExteriorEquiv

def ambientOrderedBasis (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :=
  (localAmbientBasis v n t).reindex (finSumFinEquiv : AmbientIndex ≃ Fin 4)

theorem residueWedgeMap_surjective (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    Function.Surjective (residueWedgeMap v n t) := by
  intro x
  refine ⟨(localSurfaceDeterminantEquiv v n t).symm
    (ambientVolumeCoordinate v n t x), ?_⟩
  change localSurfaceDeterminantEquiv v n t
    ((localSurfaceDeterminantEquiv v n t).symm
      (ambientVolumeCoordinate v n t x)) • ambientVolume v n t = x
  rw [LinearEquiv.apply_symm_apply]
  exact topCoordinate_smul_wedge (ambientOrderedBasis v n t) x

/-- Adjunction on the actual local determinant modules, obtained from the
proved wedge formula and the actual unit augmented determinant. -/
def residueWedgeEquiv (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    (⋀[AdjunctionPatch v n t]^2
      (KaehlerDifferential ℂ (AdjunctionPatch v n t))) ≃ₗ[AdjunctionPatch v n t]
      (⋀[AdjunctionPatch v n t]^4 (LocalAmbientDifferentials v n t)) :=
  LinearEquiv.ofBijective (residueWedgeMap v n t)
    ⟨residueWedgeMap_injective v n t, residueWedgeMap_surjective v n t⟩

@[simp] theorem residueWedgeEquiv_apply (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
    (w : ⋀[AdjunctionPatch v n t]^2
      (KaehlerDifferential ℂ (AdjunctionPatch v n t))) :
    residueWedgeEquiv v n t w = residueWedgeMap v n t w := rfl

variable (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
variable (S : Type*) [CommRing S] [Algebra (AdjunctionPatch v n t) S]

/-- Both exterior-power identifications are the canonical tensor-wedge maps.
No flatness assumption is needed, because the original wedge map is an equivalence. -/
def scalarWedgeEquiv :
    (⋀[S]^2 (S ⊗[AdjunctionPatch v n t]
      KaehlerDifferential ℂ (AdjunctionPatch v n t))) ≃ₗ[S]
    (⋀[S]^4 (S ⊗[AdjunctionPatch v n t] LocalAmbientDifferentials v n t)) :=
  topTensorTransport (localSurfaceKaehlerBasis v n t)
    (ambientOrderedBasis v n t) (residueWedgeEquiv v n t)

theorem scalarWedgeEquiv_baseChange
    (w : ⋀[AdjunctionPatch v n t]^2
      (KaehlerDifferential ℂ (AdjunctionPatch v n t))) :
    scalarWedgeEquiv v n t S
        (topBaseChange (S := S) (localSurfaceKaehlerBasis v n t) w) =
      topBaseChange (S := S) (ambientOrderedBasis v n t) (residueWedgeMap v n t w) :=
  topTensorTransport_baseChange (localSurfaceKaehlerBasis v n t)
    (ambientOrderedBasis v n t) (residueWedgeEquiv v n t) w

theorem scalarWedgeEquiv_lifts (w : Fin 2 → LocalAmbientDifferentials v n t) :
    scalarWedgeEquiv v n t S
        (exteriorPower.ιMulti S 2
          (fun j => (1 : S) ⊗ₜ[AdjunctionPatch v n t] localToKaehler v n t (w j))) =
      exteriorPower.ιMulti S 4
        (fun j => (1 : S) ⊗ₜ[AdjunctionPatch v n t]
          pairFamily (compactAugmentedBasis v n t) w
            ((finSumFinEquiv : AmbientIndex ≃ Fin 4).symm j)) :=
  topTensorTransport_wedge (localSurfaceKaehlerBasis v n t)
    (ambientOrderedBasis v n t) (residueWedgeEquiv v n t)
    (localToKaehler v n t ∘ w)
    (pairFamily (compactAugmentedBasis v n t) w ∘
      (finSumFinEquiv : AmbientIndex ≃ Fin 4).symm)
    (residueWedgeMap_lifts v n t w)

@[simp] theorem scalarWedgeEquiv_residue :
    scalarWedgeEquiv v n t S
        (topBaseChange (S := S) (localSurfaceKaehlerBasis v n t)
          (localSurfaceResidueForm v n t)) =
      topBaseChange (S := S) (ambientOrderedBasis v n t) (ambientVolume v n t) :=
  (scalarWedgeEquiv_baseChange v n t S (localSurfaceResidueForm v n t)).trans
    (congrArg (topBaseChange (S := S) (ambientOrderedBasis v n t))
      (residueWedgeMap_residue v n t))

theorem scalarWedgeEquiv_eq_volume_iff
    (w : ⋀[S]^2 (S ⊗[AdjunctionPatch v n t]
      KaehlerDifferential ℂ (AdjunctionPatch v n t))) :
    scalarWedgeEquiv v n t S w =
        topBaseChange (S := S) (ambientOrderedBasis v n t) (ambientVolume v n t) ↔
      w = topBaseChange (S := S) (localSurfaceKaehlerBasis v n t)
        (localSurfaceResidueForm v n t) := by
  constructor
  · intro h
    exact (scalarWedgeEquiv v n t S).injective
      (h.trans (scalarWedgeEquiv_residue v n t S).symm)
  · intro h
    exact (congrArg (scalarWedgeEquiv v n t S) h).trans
      (scalarWedgeEquiv_residue v n t S)

section Etale

variable [Algebra ℂ S] [IsScalarTower ℂ (AdjunctionPatch v n t) S]
  [Algebra.FormallyEtale (AdjunctionPatch v n t) S]

/-- On an actual formally étale extension, the surface source is the
genuine Kähler module over the extended ring. The ambient target is retained. -/
def etaleSurfaceExteriorEquiv :
    (⋀[S]^2 (S ⊗[AdjunctionPatch v n t]
      KaehlerDifferential ℂ (AdjunctionPatch v n t))) ≃ₗ[S]
      (⋀[S]^2 (KaehlerDifferential ℂ S)) :=
  exteriorLinearEquiv 2
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      ℂ (AdjunctionPatch v n t) S)

def etaleWedgeEquiv :
    (⋀[S]^2 (KaehlerDifferential ℂ S)) ≃ₗ[S]
      (⋀[S]^4 (S ⊗[AdjunctionPatch v n t] LocalAmbientDifferentials v n t)) :=
  (etaleSurfaceExteriorEquiv v n t S).symm.trans (scalarWedgeEquiv v n t S)

def etaleResidue : ⋀[S]^2 (KaehlerDifferential ℂ S) :=
  etaleSurfaceExteriorEquiv v n t S
    (topBaseChange (S := S) (localSurfaceKaehlerBasis v n t)
      (localSurfaceResidueForm v n t))

@[simp] theorem etaleWedgeEquiv_residue :
    etaleWedgeEquiv v n t S (etaleResidue v n t S) =
      topBaseChange (S := S) (ambientOrderedBasis v n t) (ambientVolume v n t) := by
  simp only [etaleWedgeEquiv, etaleResidue, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, scalarWedgeEquiv_residue]

theorem etaleWedgeEquiv_eq_volume_iff (w : ⋀[S]^2 (KaehlerDifferential ℂ S)) :
    etaleWedgeEquiv v n t S w =
        topBaseChange (S := S) (ambientOrderedBasis v n t) (ambientVolume v n t) ↔
      w = etaleResidue v n t S := by
  constructor
  · intro h
    exact (etaleWedgeEquiv v n t S).injective
      (h.trans (etaleWedgeEquiv_residue v n t S).symm)
  · intro h
    exact (congrArg (etaleWedgeEquiv v n t S) h).trans
      (etaleWedgeEquiv_residue v n t S)

end Etale

end CycleQ2SurfaceResidueScalarExtension
end

end


section

/-! The scalar-extended adjunction formula for every ambient lift, not
only tensors of lifts from the original chart. All conormal factors stay
in the retained ambient cotangent module. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceResidueAllLifts

open Module CycleQ2GeometricSurfaceAdjunction CycleQ2SurfaceResidueWedge
  CycleQ2SurfaceResidueScalarExtension CycleQ2ResidueQuotientWedge
  CycleQ2ResidueWedgeNaturality
open scoped TensorProduct

section Generic

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

def conormalExteriorMap (c : Fin 2 → M) :
    (⋀[R]^2 M) →ₗ[R] (⋀[R]^4 M) :=
  exteriorPower.alternatingMapLinearEquiv
    (((exteriorPower.ιMulti R 4).curryLeft (c 0)).curryLeft (c 1))

@[simp] theorem conormalExteriorMap_wedge (c w : Fin 2 → M) :
    conormalExteriorMap (R := R) c (exteriorPower.ιMulti R 2 w) =
      exteriorPower.ιMulti R 4 (conormalFamily c w) := by
  simp only [conormalExteriorMap, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.curryLeft_apply_apply]
  apply congrArg (exteriorPower.ιMulti R 4)
  funext j
  fin_cases j <;> rfl

theorem tensor_pair_family (b : Basis BlockIndex R M) (w : Fin 2 → M) :
    (fun j : Fin 4 => (1 : S) ⊗ₜ[R]
      pairFamily b w ((finSumFinEquiv : BlockIndex ≃ Fin 4).symm j)) =
      conormalFamily (fun j => (1 : S) ⊗ₜ[R] b (Sum.inl j))
        (fun j => (1 : S) ⊗ₜ[R] w j) := by
  funext j
  fin_cases j <;> rfl

end Generic

variable (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (S : Type*) [CommRing S] [Algebra (AdjunctionPatch v n t) S]

theorem scalarWedgeEquiv_quotient :
    (scalarWedgeEquiv v n t S).toLinearMap.comp
        (exteriorPower.map 2 ((localToKaehler v n t).baseChange S)) =
      conormalExteriorMap (R := S)
        (fun j => (1 : S) ⊗ₜ[AdjunctionPatch v n t]
          compactAugmentedBasis v n t (Sum.inl j)) := by
  apply exteriorPower.linearMap_ext
  apply ((localAmbientBasis v n t).baseChange S).ext_alternating
  intro a _
  have h := scalarWedgeEquiv_lifts v n t S
    (fun j => localAmbientBasis v n t (a j))
  have hh := h.trans (congrArg (exteriorPower.ιMulti S 4)
    (tensor_pair_family (S := S) (compactAugmentedBasis v n t)
      (fun j => localAmbientBasis v n t (a j))))
  simpa only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, exteriorPower.map_apply_ιMulti,
    conormalExteriorMap_wedge, Basis.baseChange_apply, Function.comp_def,
    LinearMap.baseChange_tmul] using hh

/-- The actual quotient map after arbitrary scalar extension obeys the
conormal-first formula for arbitrary lifts in the extended ambient module. -/
theorem scalarWedgeEquiv_all_lifts
    (w : Fin 2 → S ⊗[AdjunctionPatch v n t] LocalAmbientDifferentials v n t) :
    scalarWedgeEquiv v n t S
        (exteriorPower.ιMulti S 2
          (((localToKaehler v n t).baseChange S) ∘ w)) =
      exteriorPower.ιMulti S 4
        (conormalFamily
          (fun j => (1 : S) ⊗ₜ[AdjunctionPatch v n t]
            compactAugmentedBasis v n t (Sum.inl j)) w) := by
  have h := LinearMap.congr_fun (scalarWedgeEquiv_quotient v n t S)
    (exteriorPower.ιMulti S 2 w)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    exteriorPower.map_apply_ιMulti, conormalExteriorMap_wedge] using h

theorem scalarWedgeEquiv_actual_all_lifts
    (w : Fin 2 → S ⊗[AdjunctionPatch v n t] LocalAmbientDifferentials v n t) :
    scalarWedgeEquiv v n t S
        (exteriorPower.ιMulti S 2
          (((localToKaehler v n t).baseChange S) ∘ w)) =
      exteriorPower.ιMulti S 4
        (conormalFamily
          (fun j => (1 : S) ⊗ₜ[AdjunctionPatch v n t]
            ((1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v]
              ambientDifferential v (v j))) w) := by
  simpa only [compactAugmentedBasis_apply, localAugmentedFamily,
    augmentedFamily, Sum.elim_inl] using scalarWedgeEquiv_all_lifts v n t S w

end CycleQ2SurfaceResidueAllLifts
end

end


section

/-! Exact agreement with the previously constructed surface restriction.
The actual residue and cubic forms used by normal adjunction are retained. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ResidueBaseChangeBinding

open Module CycleQ2GeometricSurfaceAdjunction CycleQ2SurfaceResidueWedge
  CycleQ2ExteriorTopBaseChange CycleQ2SurfaceResidueScalarExtension

section Generic

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

theorem topCoordinate_eq_determinantEquiv (b : Basis (Fin 2) R M) :
    topCoordinate b = (determinantEquiv b).toLinearMap := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  exact (topCoordinate_wedge b w).trans (determinantEquiv_family b w).symm

theorem topBaseChange_eq_determinantBaseChange (b : Basis (Fin 2) R M)
    (w : ⋀[R]^2 M) :
    topBaseChange (S := S) b w = determinantBaseChange (R := S) b w := by
  change algebraMap R S (topCoordinate b w) • exteriorPower.ιMulti S 2 (b.baseChange S) =
    algebraMap R S (determinantEquiv b w) • exteriorPower.ιMulti S 2 (b.baseChange S)
  rw [topCoordinate_eq_determinantEquiv]
  rfl

end Generic

variable (q h : MvPolynomial (Fin 3) ℂ) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)

/-- This is exactly the old restricted surface residue, not a new choice
of a normalized form on the curve. -/
theorem restrictedSurfaceResidueForm_eq_topBaseChange :
    restrictedSurfaceResidueForm q h g₁ g₂ k i j =
      topBaseChange (S := NormalCurvePatch q h g₁ g₂ k i j)
        (localSurfaceKaehlerBasis ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (normalPolynomial q i) (includeCurve (MvPolynomial.X j)))
        (localSurfaceResidueForm ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (normalPolynomial q i) (includeCurve (MvPolynomial.X j))) :=
  (topBaseChange_eq_determinantBaseChange _ _).symm

theorem restrictedSurfaceResidueForm_wedge :
    scalarWedgeEquiv ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (normalPolynomial q i) (includeCurve (MvPolynomial.X j))
        (NormalCurvePatch q h g₁ g₂ k i j)
        (restrictedSurfaceResidueForm q h g₁ g₂ k i j) =
      topBaseChange (S := NormalCurvePatch q h g₁ g₂ k i j)
        (ambientOrderedBasis ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (normalPolynomial q i) (includeCurve (MvPolynomial.X j)))
        (ambientVolume ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (normalPolynomial q i) (includeCurve (MvPolynomial.X j))) := by
  exact (congrArg
    (scalarWedgeEquiv ![surfaceEquation q h g₁ g₂ k, includeCurve h]
      (normalPolynomial q i) (includeCurve (MvPolynomial.X j))
      (NormalCurvePatch q h g₁ g₂ k i j))
    (restrictedSurfaceResidueForm_eq_topBaseChange q h g₁ g₂ k i j)).trans
      (scalarWedgeEquiv_residue _ _ _ _)

theorem restrictedCubicSurfaceForm_eq_topBaseChange :
    restrictedCubicSurfaceForm q h g₁ g₂ k i j =
      topBaseChange (S := NormalCurvePatch q h g₁ g₂ k i j)
        (localSurfaceKaehlerBasis ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (normalPolynomial q i) (includeCurve (MvPolynomial.X j)))
        (localCubicSurfaceForm q h g₁ g₂ k i j) :=
  (topBaseChange_eq_determinantBaseChange _ _).symm

theorem restrictedCubicSurfaceForm_wedge :
    scalarWedgeEquiv ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (normalPolynomial q i) (includeCurve (MvPolynomial.X j))
        (NormalCurvePatch q h g₁ g₂ k i j)
        (restrictedCubicSurfaceForm q h g₁ g₂ k i j) =
      (normalCoefficientMap q h g₁ g₂ k i j
          (includeCurve (MvPolynomial.X 0))) ^ 3 •
        topBaseChange (S := NormalCurvePatch q h g₁ g₂ k i j)
          (ambientOrderedBasis ![surfaceEquation q h g₁ g₂ k, includeCurve h]
            (normalPolynomial q i) (includeCurve (MvPolynomial.X j)))
          (ambientVolume ![surfaceEquation q h g₁ g₂ k, includeCurve h]
            (normalPolynomial q i) (includeCurve (MvPolynomial.X j))) := by
  let W := scalarWedgeEquiv ![surfaceEquation q h g₁ g₂ k, includeCurve h]
    (normalPolynomial q i) (includeCurve (MvPolynomial.X j))
    (NormalCurvePatch q h g₁ g₂ k i j)
  let a : NormalCurvePatch q h g₁ g₂ k i j :=
    (normalCoefficientMap q h g₁ g₂ k i j (includeCurve (MvPolynomial.X 0))) ^ 3
  exact (congrArg W (restrictedCubicSurfaceForm_eq q h g₁ g₂ k i j)).trans
    ((map_smul W a (restrictedSurfaceResidueForm q h g₁ g₂ k i j)).trans
      (congrArg (fun x => a • x) (restrictedSurfaceResidueForm_wedge q h g₁ g₂ k i j)))

end CycleQ2ResidueBaseChangeBinding
end

end


section

/-! The conormal wedge formula on the genuine Kähler module of a further
formally étale chart. The quotient map is the actual composite of universal
cotangent maps, and is proved surjective rather than assumed. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceEtaleResidueLifts

open Module CycleQ2GeometricSurfaceAdjunction CycleQ2SurfaceResidueScalarExtension
  CycleQ2SurfaceResidueAllLifts CycleQ2ResidueWedgeNaturality
open scoped TensorProduct

variable (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (S : Type*) [CommRing S] [Algebra (AdjunctionPatch v n t) S]
  [Algebra ℂ S] [IsScalarTower ℂ (AdjunctionPatch v n t) S]
  [Algebra.FormallyEtale (AdjunctionPatch v n t) S]

/-- The actual ambient-to-surface quotient after a formally étale extension. -/
def etaleToKaehler :
    S ⊗[AdjunctionPatch v n t] LocalAmbientDifferentials v n t →ₗ[S]
      KaehlerDifferential ℂ S :=
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
    ℂ (AdjunctionPatch v n t) S).toLinearMap.comp
      ((localToKaehler v n t).baseChange S)

theorem etaleToKaehler_surjective :
    Function.Surjective (etaleToKaehler v n t S) :=
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
    ℂ (AdjunctionPatch v n t) S).surjective.comp
      (LinearMap.baseChange_surjective S (localToKaehler_surjective v n t))

@[simp] theorem etaleToKaehler_polynomial (s : S) (p : SurfacePoly) :
    etaleToKaehler v n t S
        (s ⊗ₜ[AdjunctionPatch v n t]
          ((1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v] ambientDifferential v p)) =
      s • KaehlerDifferential.D ℂ S
        (algebraMap (AdjunctionPatch v n t) S
          (algebraMap SurfacePoly (AdjunctionPatch v n t) p)) := by
  simp only [etaleToKaehler, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul, localToKaehler_polynomial,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]

theorem etaleSurfaceExteriorEquiv_lifts
    (w : Fin 2 → S ⊗[AdjunctionPatch v n t] LocalAmbientDifferentials v n t) :
    etaleSurfaceExteriorEquiv v n t S
        (exteriorPower.ιMulti S 2 (((localToKaehler v n t).baseChange S) ∘ w)) =
      exteriorPower.ιMulti S 2 ((etaleToKaehler v n t S) ∘ w) := by
  rw [etaleSurfaceExteriorEquiv, exteriorLinearEquiv_apply,
    exteriorPower.map_apply_ιMulti]
  rfl

/-- Every ambient lift satisfies the same conormal-first wedge identity
in the actual differential module of the extended surface ring. -/
theorem etaleWedgeEquiv_actual_all_lifts
    (w : Fin 2 → S ⊗[AdjunctionPatch v n t] LocalAmbientDifferentials v n t) :
    etaleWedgeEquiv v n t S
        (exteriorPower.ιMulti S 2 ((etaleToKaehler v n t S) ∘ w)) =
      exteriorPower.ιMulti S 4
        (conormalFamily
          (fun j => (1 : S) ⊗ₜ[AdjunctionPatch v n t]
            ((1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v]
              ambientDifferential v (v j))) w) := by
  calc
    _ = etaleWedgeEquiv v n t S
        (etaleSurfaceExteriorEquiv v n t S
          (exteriorPower.ιMulti S 2 (((localToKaehler v n t).baseChange S) ∘ w))) :=
      congrArg (etaleWedgeEquiv v n t S)
        (etaleSurfaceExteriorEquiv_lifts v n t S w).symm
    _ = scalarWedgeEquiv v n t S
        (exteriorPower.ιMulti S 2 (((localToKaehler v n t).baseChange S) ∘ w)) := by
      simp only [etaleWedgeEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    _ = _ := scalarWedgeEquiv_actual_all_lifts v n t S w

end CycleQ2SurfaceEtaleResidueLifts
end

end


section

/-! The genuine cotangent quotient commutes with canonical cancellation
of the augmented-chart tensor factors. This binds the actual local
residue construction to the unlocalized presentation maps. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfacePatchCotangentBinding

open Module MvPolynomial TensorProduct CycleQ2GeometricSurfaceAdjunction
  CycleQ2SurfaceEtaleResidueLifts
open scoped TensorProduct

variable (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (S : Type*) [CommRing S] [Algebra (SurfaceChartRing v) S]
  [Algebra (AdjunctionPatch v n t) S]
  [IsScalarTower (SurfaceChartRing v) (AdjunctionPatch v n t) S]

/-- Canonical cancellation of the actual augmented-chart scalar extension. -/
def patchPresentationEquiv :
    S ⊗[AdjunctionPatch v n t] LocalAmbientDifferentials v n t ≃ₗ[S]
      S ⊗[SurfaceChartRing v] AmbientDifferentials v :=
  AlgebraTensorModule.cancelBaseChange (SurfaceChartRing v) (AdjunctionPatch v n t)
    S S (AmbientDifferentials v)

@[simp] theorem patchPresentationEquiv_tmul_D (s : S) (p : SurfacePoly) :
    patchPresentationEquiv v n t S
        (s ⊗ₜ[AdjunctionPatch v n t]
          ((1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v] ambientDifferential v p)) =
      s ⊗ₜ[SurfaceChartRing v] ambientDifferential v p := by
  simp only [patchPresentationEquiv, AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

/-- The two literal polynomial-to-surface ring maps agree by the actual
scalar tower, without identifying unrelated polynomial actions. -/
theorem polynomial_scalar_tower (p : SurfacePoly) :
    algebraMap (AdjunctionPatch v n t) S
        (algebraMap SurfacePoly (AdjunctionPatch v n t) p) =
      algebraMap (SurfaceChartRing v) S
        (algebraMap SurfacePoly (SurfaceChartRing v) p) := by
  rw [IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing v) (AdjunctionPatch v n t),
    ← IsScalarTower.algebraMap_apply (SurfaceChartRing v) (AdjunctionPatch v n t) S]

variable [Algebra ℂ S] [IsScalarTower ℂ (SurfaceChartRing v) S]
  [IsScalarTower ℂ (AdjunctionPatch v n t) S]
  [Algebra.FormallyEtale (AdjunctionPatch v n t) S]

/-- The actual cotangent quotient square, proved on the ambient polynomial
basis after both genuine scalar extensions. -/
theorem etaleToKaehler_eq_presentation :
    etaleToKaehler v n t S =
      (KaehlerDifferential.mapBaseChange ℂ (SurfaceChartRing v) S).comp
        (((presentation v).toExtension.toKaehler.baseChange S).comp
          (patchPresentationEquiv v n t S).toLinearMap) := by
  apply ((localAmbientBasis v n t).baseChange S).ext
  intro j
  simp only [Basis.baseChange_apply, localAmbientBasis, ambientBasis,
    Basis.reindex_apply, Algebra.Generators.cotangentSpaceBasis_apply]
  change etaleToKaehler v n t S
      ((1 : S) ⊗ₜ[AdjunctionPatch v n t]
        ((1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v]
          ambientDifferential v (X (ambientIndexEquiv j)))) =
    (KaehlerDifferential.mapBaseChange ℂ (SurfaceChartRing v) S)
      (((presentation v).toExtension.toKaehler.baseChange S)
        (patchPresentationEquiv v n t S
          ((1 : S) ⊗ₜ[AdjunctionPatch v n t]
            ((1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v]
              ambientDifferential v (X (ambientIndexEquiv j))))))
  simp only [etaleToKaehler_polynomial,
    patchPresentationEquiv_tmul_D, LinearMap.baseChange_tmul,
    ambientToKaehler_polynomial, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D, one_smul]
  exact congrArg (KaehlerDifferential.D ℂ S) (polynomial_scalar_tower v n t S _)

end CycleQ2SurfacePatchCotangentBinding
end

end


section

/-! A transition criterion for the actual local residues. Only the ambient
coordinate map and its concrete quotient, conormal and volume identities
remain as inputs; the wedge maps, their surjectivity and their residue
normalizations are the previously constructed genuine maps. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceResidueTransitionCriterion

open Module CycleQ2GeometricSurfaceAdjunction CycleQ2SurfaceResidueWedge
  CycleQ2SurfaceResidueScalarExtension CycleQ2SurfaceEtaleResidueLifts
  CycleQ2ExteriorTopBaseChange CycleQ2ResidueWedgeNaturality
open scoped TensorProduct

variable (v₁ v₂ : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly)
  (S : Type*) [CommRing S] [Algebra ℂ S]
  [Algebra (AdjunctionPatch v₁ n₁ t₁) S] [Algebra (AdjunctionPatch v₂ n₂ t₂) S]
  [IsScalarTower ℂ (AdjunctionPatch v₁ n₁ t₁) S]
  [IsScalarTower ℂ (AdjunctionPatch v₂ n₂ t₂) S]
  [Algebra.FormallyEtale (AdjunctionPatch v₁ n₁ t₁) S]
  [Algebra.FormallyEtale (AdjunctionPatch v₂ n₂ t₂) S]

theorem actual_residue_transition
    (f : S ⊗[AdjunctionPatch v₂ n₂ t₂] LocalAmbientDifferentials v₂ n₂ t₂ →ₗ[S]
      S ⊗[AdjunctionPatch v₁ n₁ t₁] LocalAmbientDifferentials v₁ n₁ t₁)
    (a b k d : S) (hd : d * (a * b) = 1)
    (hcomm : ∀ x, etaleToKaehler v₁ n₁ t₁ S (f x) = etaleToKaehler v₂ n₂ t₂ S x)
    (hc : ∀ j : Fin 2,
      f ((1 : S) ⊗ₜ[AdjunctionPatch v₂ n₂ t₂]
          ((1 : AdjunctionPatch v₂ n₂ t₂) ⊗ₜ[SurfaceChartRing v₂]
            ambientDifferential v₂ (v₂ j))) =
        ![a,b] j • ((1 : S) ⊗ₜ[AdjunctionPatch v₁ n₁ t₁]
          ((1 : AdjunctionPatch v₁ n₁ t₁) ⊗ₜ[SurfaceChartRing v₁]
            ambientDifferential v₁ (v₁ j))))
    (hvolume : exteriorPower.map 4 f
        (topBaseChange (S := S) (ambientOrderedBasis v₂ n₂ t₂) (ambientVolume v₂ n₂ t₂)) =
      k • topBaseChange (S := S) (ambientOrderedBasis v₁ n₁ t₁) (ambientVolume v₁ n₁ t₁)) :
    etaleResidue v₂ n₂ t₂ S = (d * k) • etaleResidue v₁ n₁ t₁ S := by
  have hmap := conormal_wedge_naturality
    (etaleToKaehler v₂ n₂ t₂ S) (etaleToKaehler v₁ n₁ t₁ S) f
    (fun j => (1 : S) ⊗ₜ[AdjunctionPatch v₂ n₂ t₂]
      ((1 : AdjunctionPatch v₂ n₂ t₂) ⊗ₜ[SurfaceChartRing v₂]
        ambientDifferential v₂ (v₂ j)))
    (fun j => (1 : S) ⊗ₜ[AdjunctionPatch v₁ n₁ t₁]
      ((1 : AdjunctionPatch v₁ n₁ t₁) ⊗ₜ[SurfaceChartRing v₁]
        ambientDifferential v₁ (v₁ j))) a b
    (etaleWedgeEquiv v₂ n₂ t₂ S).toLinearMap
    (etaleWedgeEquiv v₁ n₁ t₁ S).toLinearMap
    (etaleToKaehler_surjective v₂ n₂ t₂ S) hcomm hc
    (etaleWedgeEquiv_actual_all_lifts v₂ n₂ t₂ S)
    (etaleWedgeEquiv_actual_all_lifts v₁ n₁ t₁ S)
  exact normalized_transition
    (etaleWedgeEquiv v₂ n₂ t₂ S).toLinearMap
    (etaleWedgeEquiv v₁ n₁ t₁ S).toLinearMap (exteriorPower.map 4 f)
    (a * b) d k hd (etaleResidue v₂ n₂ t₂ S) (etaleResidue v₁ n₁ t₁ S)
    (topBaseChange (S := S) (ambientOrderedBasis v₂ n₂ t₂) (ambientVolume v₂ n₂ t₂))
    (topBaseChange (S := S) (ambientOrderedBasis v₁ n₁ t₁) (ambientVolume v₁ n₁ t₁))
    (etaleWedgeEquiv v₁ n₁ t₁ S).injective
    (etaleWedgeEquiv_residue v₂ n₂ t₂ S) (etaleWedgeEquiv_residue v₁ n₁ t₁ S)
    hmap hvolume

end CycleQ2SurfaceResidueTransitionCriterion
end

end


section

/-! Compare actual residues through a single retained ambient module.
The first comparison is an equivalence; the second is the genuine changed
coordinate map. This form of the criterion avoids changing scalar actions
on the common ring. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceResidueComparisonCriterion

open Module CycleQ2GeometricSurfaceAdjunction CycleQ2SurfaceResidueWedge
  CycleQ2SurfaceResidueScalarExtension CycleQ2SurfaceEtaleResidueLifts
  CycleQ2ExteriorTopBaseChange CycleQ2SurfaceResidueTransitionCriterion
open scoped TensorProduct

section Linear
variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

theorem exterior_conjugate_apply (n : ℕ) (e : M ≃ₗ[R] N) (f : P →ₗ[R] N)
    (w : ⋀[R]^n P) :
    exteriorPower.map n e.toLinearMap
        (exteriorPower.map n (e.symm.toLinearMap.comp f) w) =
      exteriorPower.map n f w := by
  have hf : e.toLinearMap.comp (e.symm.toLinearMap.comp f) = f := by
    ext x
    exact e.apply_symm_apply (f x)
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, hf]

end Linear

variable (v₁ v₂ : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly)
  (S : Type*) [CommRing S] [Algebra ℂ S]
  [Algebra (AdjunctionPatch v₁ n₁ t₁) S] [Algebra (AdjunctionPatch v₂ n₂ t₂) S]
  [IsScalarTower ℂ (AdjunctionPatch v₁ n₁ t₁) S]
  [IsScalarTower ℂ (AdjunctionPatch v₂ n₂ t₂) S]
  [Algebra.FormallyEtale (AdjunctionPatch v₁ n₁ t₁) S]
  [Algebra.FormallyEtale (AdjunctionPatch v₂ n₂ t₂) S]

theorem compared_residue_transition
    (N : Type*) [AddCommGroup N] [Module S N]
    (e : S ⊗[AdjunctionPatch v₁ n₁ t₁] LocalAmbientDifferentials v₁ n₁ t₁ ≃ₗ[S] N)
    (f : S ⊗[AdjunctionPatch v₂ n₂ t₂] LocalAmbientDifferentials v₂ n₂ t₂ →ₗ[S] N)
    (q : N →ₗ[S] KaehlerDifferential ℂ S)
    (a b k d : S) (hd : d * (a * b) = 1)
    (hfirst : ∀ x, q (e x) = etaleToKaehler v₁ n₁ t₁ S x)
    (hsecond : ∀ x, q (f x) = etaleToKaehler v₂ n₂ t₂ S x)
    (hc : ∀ j : Fin 2,
      f ((1 : S) ⊗ₜ[AdjunctionPatch v₂ n₂ t₂]
          ((1 : AdjunctionPatch v₂ n₂ t₂) ⊗ₜ[SurfaceChartRing v₂]
            ambientDifferential v₂ (v₂ j))) =
        ![a,b] j • e ((1 : S) ⊗ₜ[AdjunctionPatch v₁ n₁ t₁]
          ((1 : AdjunctionPatch v₁ n₁ t₁) ⊗ₜ[SurfaceChartRing v₁]
            ambientDifferential v₁ (v₁ j))))
    (hvolume : exteriorPower.map 4 f
        (topBaseChange (S := S) (ambientOrderedBasis v₂ n₂ t₂) (ambientVolume v₂ n₂ t₂)) =
      k • exteriorPower.map 4 e.toLinearMap
        (topBaseChange (S := S) (ambientOrderedBasis v₁ n₁ t₁) (ambientVolume v₁ n₁ t₁))) :
    etaleResidue v₂ n₂ t₂ S = (d * k) • etaleResidue v₁ n₁ t₁ S := by
  apply actual_residue_transition v₁ v₂ n₁ t₁ n₂ t₂ S
    (e.symm.toLinearMap.comp f) a b k d hd
  · intro x
    exact (hfirst (e.symm (f x))).symm.trans
      ((congrArg q (e.apply_symm_apply (f x))).trans (hsecond x))
  · intro j
    apply e.injective
    change e (e.symm (f _)) = e (_ • _)
    rw [LinearEquiv.apply_symm_apply, map_smul]
    exact hc j
  · apply (exteriorLinearEquiv 4 e).injective
    change exteriorPower.map 4 e.toLinearMap
        (exteriorPower.map 4 (e.symm.toLinearMap.comp f) _) =
      exteriorPower.map 4 e.toLinearMap (k • _)
    exact (exterior_conjugate_apply 4 e f _).trans
      (hvolume.trans (map_smul (exteriorPower.map 4 e.toLinearMap) k _).symm)

end CycleQ2SurfaceResidueComparisonCriterion
end

end
