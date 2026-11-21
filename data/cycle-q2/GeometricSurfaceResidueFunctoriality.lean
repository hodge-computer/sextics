import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Proposal.GeometricSurfaceAdjunction
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Proposal.GeometricExteriorSheaf
import Proposal.GeometricIntrinsicNormal
import Proposal.GeometricSheafHZero
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Proposal.GeometricCanonicalCechBoundary
import Proposal.GeometricSurfaceDifferentialCharts
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Proposal.GeometricCanonicalGluing
import Proposal.GeometricProjectiveNormalClass
import Proposal.GeometricCartierDerivedClass

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


section

/-! Scalar extension of the genuine normal-first adjunction contraction.
The surface factor remains the scalar extension of B tensor Omega(A),
where A is the actual surface chart and B its actual curve quotient. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalAdjunctionBaseChange

open Module CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricExteriorSheaf
open scoped TensorProduct

section RankTwo

variable {R Q M N : Type} [CommRing R]
  [AddCommGroup Q] [Module R Q] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A linear map out of a rank-two module which kills its first basis
vector is determined by the actual second coordinate. -/
theorem lastCoordinate_image (b : Basis (Fin 2) R M) (g : M →ₗ[R] N)
    (hzero : g (b 0) = 0) (m : M) :
    g m = b.repr m 1 • g (b 1) := by
  have hm : b.repr m 0 • b 0 + b.repr m 1 • b 1 = m := by
    simpa only [Fin.sum_univ_two] using b.sum_repr m
  conv_lhs => rw [← hm]
  rw [map_add, map_smul, map_smul, hzero, smul_zero, zero_add]

/-- The normal-first determinant formula depends on the actual conormal
inclusion and quotient map, rather than on the choice of a coordinate. -/
theorem determinantContraction_intrinsic
    (b : Basis (Fin 2) R M) (e : Q ≃ₗ[R] R) (d : Q →ₗ[R] M)
    (hd : ∀ x, d x = e x • b 0) (g : M →ₗ[R] N) (hg : g (b 0) = 0)
    (φ : Q →ₗ[R] R) (x : Q) (m : M) :
    ((determinantEquiv b).toLinearMap.smulRight
      (φ (e.symm 1) • g (b 1)))
        (exteriorPower.ιMulti R 2 ![d x,m]) = φ x • g m := by
  have hx : e x • e.symm 1 = x := by
    apply e.injective
    rw [map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  have hφ : φ x = e x * φ (e.symm 1) := by
    conv_lhs => rw [← hx]
    rw [map_smul, smul_eq_mul]
  simp only [LinearMap.smulRight_apply, LinearEquiv.coe_coe,
    determinantEquiv_pair, hd, map_smul, Finsupp.smul_apply,
    Basis.repr_self, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
    smul_eq_mul, mul_one, mul_zero, zero_mul, sub_zero]
  rw [lastCoordinate_image b g hg m, hφ, smul_smul, smul_smul]
  congr 1
  ring

end RankTwo

section TensorRestriction

variable {R S T M : Type} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [AddCommGroup M] [Module R M]

/-- The actual scalar-extension restriction sends s tensor m to its
coefficient image tensor the same original module element. -/
def tensorRestriction : (S ⊗[R] M) →ₛₗ[algebraMap S T] (T ⊗[R] M) where
  toFun := TensorProduct.AlgebraTensorModule.map (Algebra.linearMap S T)
    (LinearMap.id (R := R) (M := M))
  map_add' := map_add _
  map_smul' s x := by
    rw [map_smul, IsScalarTower.algebraMap_smul]

@[simp] theorem tensorRestriction_tmul (s : S) (m : M) :
    tensorRestriction (R := R) (T := T) (s ⊗ₜ[R] m) =
      algebraMap S T s ⊗ₜ[R] m := rfl

@[simp] theorem tensorRestriction_basis (b : Basis (Fin 2) R M) (i : Fin 2) :
    tensorRestriction (R := R) (T := T) (b.baseChange S i) = b.baseChange T i := by
  simp only [Basis.baseChange_apply, tensorRestriction_tmul, map_one]

end TensorRestriction

section TensorDual

variable {R S Q : Type} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup Q] [Module R Q]

/-- The genuine scalar extension of a linear functional, with the
canonical multiplication map on its coefficient tensor factor. -/
def dualBaseChange (φ : Q →ₗ[R] R) : (S ⊗[R] Q) →ₗ[S] S :=
  (TensorProduct.AlgebraTensorModule.rid R S S).toLinearMap.comp (φ.baseChange S)

@[simp] theorem dualBaseChange_tmul (φ : Q →ₗ[R] R) (s : S) (q : Q) :
    dualBaseChange φ (s ⊗ₜ[R] q) = algebraMap R S (φ q) * s := by
  simp only [dualBaseChange, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]

end TensorDual

section ActualNormalChart

variable (q h : CycleQ2GeometricAffineCurveCharts.AffinePoly)
  (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)


variable (S : Type) [CommRing S] [Algebra (NormalCurvePatch q h g₁ g₂ k i j) S]

/-- The conormal on a scalar extension of this actual curve chart. -/
abbrev extendedConormal := S ⊗[(NormalCurvePatch q h g₁ g₂ k i j)] (NormalConormal q h g₁ g₂ k i j)

/-- The pulled-back surface module is retained before taking its exterior
square: S tensor (B tensor Omega(A)). -/
abbrev extendedSurfaceDifferentials := S ⊗[(NormalCurvePatch q h g₁ g₂ k i j)] (RestrictedSurfaceDifferentials q h g₁ g₂ k i j)

def extendedConormalEquiv : extendedConormal q h g₁ g₂ k i j S ≃ₗ[S] S :=
  ((normalConormalEquiv q h g₁ g₂ k i j).baseChange (NormalCurvePatch q h g₁ g₂ k i j) S _ _).trans
    (TensorProduct.AlgebraTensorModule.rid (NormalCurvePatch q h g₁ g₂ k i j) S S)

def extendedSurfaceBasis : Basis (Fin 2) S
    (extendedSurfaceDifferentials q h g₁ g₂ k i j S) :=
  (restrictedSurfaceBasis q h g₁ g₂ k i j).baseChange S

def extendedConormalDifferential : extendedConormal q h g₁ g₂ k i j S →ₗ[S]
    extendedSurfaceDifferentials q h g₁ g₂ k i j S :=
  (normalConormalDifferential q h g₁ g₂ k i j).baseChange S

@[simp] theorem extendedConormalEquiv_selected :
    extendedConormalEquiv q h g₁ g₂ k i j S
      ((1 : S) ⊗ₜ[(NormalCurvePatch q h g₁ g₂ k i j)] normalEquationClass q h g₁ g₂ k i j i) = 1 := by
  simp only [extendedConormalEquiv, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, normalConormalEquiv_selected,
    TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]

theorem extendedConormalEquiv_symm_one :
    (extendedConormalEquiv q h g₁ g₂ k i j S).symm 1 =
      (1 : S) ⊗ₜ[(NormalCurvePatch q h g₁ g₂ k i j)] normalEquationClass q h g₁ g₂ k i j i :=
  (LinearEquiv.symm_apply_eq _).mpr
    (extendedConormalEquiv_selected q h g₁ g₂ k i j S).symm

@[simp] theorem extendedConormalDifferential_selected :
    extendedConormalDifferential q h g₁ g₂ k i j S
      ((1 : S) ⊗ₜ[(NormalCurvePatch q h g₁ g₂ k i j)] normalEquationClass q h g₁ g₂ k i j i) =
      extendedSurfaceBasis q h g₁ g₂ k i j S 0 := by
  simp only [extendedConormalDifferential, LinearMap.baseChange_tmul,
    normalConormalDifferential_selected, extendedSurfaceBasis, Basis.baseChange_apply]

theorem extendedConormalDifferential_eq
    (x : extendedConormal q h g₁ g₂ k i j S) :
    extendedConormalDifferential q h g₁ g₂ k i j S x =
      extendedConormalEquiv q h g₁ g₂ k i j S x •
        extendedSurfaceBasis q h g₁ g₂ k i j S 0 := by
  have hx : extendedConormalEquiv q h g₁ g₂ k i j S x •
      ((1 : S) ⊗ₜ[(NormalCurvePatch q h g₁ g₂ k i j)] normalEquationClass q h g₁ g₂ k i j i) = x := by
    apply (extendedConormalEquiv q h g₁ g₂ k i j S).injective
    rw [map_smul, extendedConormalEquiv_selected, smul_eq_mul, mul_one]
  conv_lhs => rw [← hx]
  rw [map_smul, extendedConormalDifferential_selected]

variable [Algebra ℂ S] [IsScalarTower ℂ (NormalCurvePatch q h g₁ g₂ k i j) S]

def extendedToCurve : extendedSurfaceDifferentials q h g₁ g₂ k i j S →ₗ[S]
    KaehlerDifferential ℂ S :=
  (KaehlerDifferential.mapBaseChange ℂ (NormalCurvePatch q h g₁ g₂ k i j) S).comp
    ((normalToCurveKaehler q h g₁ g₂ k i j).baseChange S)

@[simp] theorem extendedToCurve_selected :
    extendedToCurve q h g₁ g₂ k i j S
      (extendedSurfaceBasis q h g₁ g₂ k i j S 0) = 0 := by
  simp only [extendedToCurve, LinearMap.comp_apply, extendedSurfaceBasis,
    Basis.baseChange_apply, LinearMap.baseChange_tmul, normalToCurveKaehler_selected,
    TensorProduct.tmul_zero, map_zero]

/-- The actual adjunction contraction after coefficient extension. Its
target map is the universal Kaehler map, not an assigned frame transport. -/
def extendedAdjunction
    (φ : extendedConormal q h g₁ g₂ k i j S →ₗ[S] S) :
    (⋀[S]^2 (extendedSurfaceDifferentials q h g₁ g₂ k i j S)) →ₗ[S]
      KaehlerDifferential ℂ S :=
  (determinantEquiv (extendedSurfaceBasis q h g₁ g₂ k i j S)).toLinearMap.smulRight
    (φ ((1 : S) ⊗ₜ[(NormalCurvePatch q h g₁ g₂ k i j)] normalEquationClass q h g₁ g₂ k i j i) •
      extendedToCurve q h g₁ g₂ k i j S
        (extendedSurfaceBasis q h g₁ g₂ k i j S 1))

theorem extendedAdjunction_intrinsic
    (φ : extendedConormal q h g₁ g₂ k i j S →ₗ[S] S)
    (x : extendedConormal q h g₁ g₂ k i j S)
    (m : extendedSurfaceDifferentials q h g₁ g₂ k i j S) :
    extendedAdjunction q h g₁ g₂ k i j S φ
      (exteriorPower.ιMulti S 2
        ![extendedConormalDifferential q h g₁ g₂ k i j S x,m]) =
      φ x • extendedToCurve q h g₁ g₂ k i j S m := by
  simpa only [extendedAdjunction, extendedConormalEquiv_symm_one] using
    determinantContraction_intrinsic
      (extendedSurfaceBasis q h g₁ g₂ k i j S)
      (extendedConormalEquiv q h g₁ g₂ k i j S)
      (extendedConormalDifferential q h g₁ g₂ k i j S)
      (extendedConormalDifferential_eq q h g₁ g₂ k i j S)
      (extendedToCurve q h g₁ g₂ k i j S)
      (extendedToCurve_selected q h g₁ g₂ k i j S) φ x m

/-- On every original determinant form and actual normal functional, the
extended contraction equals the original adjunction followed by its
genuine universal differential restriction. -/
theorem extendedAdjunction_baseChange
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j)
    (w : ⋀[NormalCurvePatch q h g₁ g₂ k i j]^2
      (RestrictedSurfaceDifferentials q h g₁ g₂ k i j)) :
    extendedAdjunction q h g₁ g₂ k i j S (dualBaseChange φ)
      (determinantBaseChange (R := S) (restrictedSurfaceBasis q h g₁ g₂ k i j) w) =
      KaehlerDifferential.map ℂ ℂ (NormalCurvePatch q h g₁ g₂ k i j) S
        (normalAdjunction q h g₁ g₂ k i j φ w) := by
  simp only [extendedAdjunction, normalAdjunction, LinearMap.smulRight_apply,
    LinearEquiv.coe_coe, extendedSurfaceBasis, determinantBaseChange_coordinate,
    dualBaseChange_tmul, mul_one, extendedToCurve, LinearMap.comp_apply,
    Basis.baseChange_apply, LinearMap.baseChange_tmul,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, map_smul,
    IsScalarTower.algebraMap_smul]

end ActualNormalChart

#print axioms determinantContraction_intrinsic
#print axioms tensorRestriction
#print axioms extendedAdjunction_intrinsic
#print axioms extendedAdjunction_baseChange

end CycleQ2NormalAdjunctionBaseChange
end

end


section

/-! Naturality of the actual normal-first adjunction under coefficient
restriction. Surface forms remain in the pulled-back surface module. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2NormalAdjunctionNaturality

open Module CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricExteriorSheaf
  CycleQ2NormalAdjunctionBaseChange
open scoped TensorProduct

section ScalarTowers

variable {R S T M : Type} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [AddCommGroup M] [Module R M]

/-- Restriction on the actual tensor module induces the canonical map on
top exterior powers; its determinant coordinate transforms by the ring map. -/
theorem determinant_tensorRestriction (b : Basis (Fin 2) R M)
    (w : ⋀[S]^2 (S ⊗[R] M)) :
    determinantEquiv (b.baseChange T)
      (exteriorMap (algebraMap S T) (tensorRestriction (R := R) (T := T)) 2 w) =
      algebraMap S T (determinantEquiv (b.baseChange S) w) := by
  have hw : determinantEquiv (b.baseChange S) w •
      exteriorPower.ιMulti S 2 (b.baseChange S) = w := by
    apply (determinantEquiv (b.baseChange S)).injective
    rw [map_smul, determinantEquiv_wedge, smul_eq_mul, mul_one]
  conv_lhs => rw [← hw]
  rw [map_smulₛₗ, map_smul, exteriorMap_wedge]
  have hb : (fun a => tensorRestriction (R := R) (T := T) (b.baseChange S a)) =
      b.baseChange T := funext (tensorRestriction_basis b)
  rw [hb, determinantEquiv_wedge, smul_eq_mul, mul_one]

end ScalarTowers

section DifferentialTowers

variable (R S T : Type) [CommRing R] [CommRing S] [CommRing T]
  [Algebra ℂ R] [Algebra ℂ S] [Algebra ℂ T]
  [Algebra R S] [Algebra R T] [Algebra S T]
  [IsScalarTower ℂ R S] [IsScalarTower ℂ R T] [IsScalarTower ℂ S T]
  [IsScalarTower R S T]

/-- The genuine universal differential map with its actual semilinear
coefficient action. -/
def differentialRestriction :
    KaehlerDifferential ℂ S →ₛₗ[algebraMap S T] KaehlerDifferential ℂ T where
  toFun := KaehlerDifferential.map ℂ ℂ S T
  map_add' := map_add _
  map_smul' s x := by
    rw [map_smul, IsScalarTower.algebraMap_smul]

theorem differentialRestriction_tower (ω : KaehlerDifferential ℂ R) :
    differentialRestriction S T (KaehlerDifferential.map ℂ ℂ R S ω) =
      KaehlerDifferential.map ℂ ℂ R T ω := by
  have hc : ((KaehlerDifferential.map ℂ ℂ S T).restrictScalars R).comp
      (KaehlerDifferential.map ℂ ℂ R S) = KaehlerDifferential.map ℂ ℂ R T := by
    apply Derivation.liftKaehlerDifferential_unique
    ext r
    change KaehlerDifferential.map ℂ ℂ S T
      (KaehlerDifferential.map ℂ ℂ R S (KaehlerDifferential.D ℂ R r)) =
      KaehlerDifferential.map ℂ ℂ R T (KaehlerDifferential.D ℂ R r)
    rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D,
      KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply]
  exact LinearMap.congr_fun hc ω

end DifferentialTowers

section ActualNormalChart

variable (q h : CycleQ2GeometricAffineCurveCharts.AffinePoly)
  (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)
  (S T : Type) [CommRing S] [CommRing T]
  [Algebra (NormalCurvePatch q h g₁ g₂ k i j) S]
  [Algebra (NormalCurvePatch q h g₁ g₂ k i j) T]
  [Algebra S T] [IsScalarTower (NormalCurvePatch q h g₁ g₂ k i j) S T]
  [Algebra ℂ S] [Algebra ℂ T]
  [IsScalarTower ℂ (NormalCurvePatch q h g₁ g₂ k i j) S]
  [IsScalarTower ℂ (NormalCurvePatch q h g₁ g₂ k i j) T]
  [IsScalarTower ℂ S T]

theorem extendedToCurve_tmul (s : S)
    (m : RestrictedSurfaceDifferentials q h g₁ g₂ k i j) :
    extendedToCurve q h g₁ g₂ k i j S (s ⊗ₜ m) =
      s • KaehlerDifferential.map ℂ ℂ (NormalCurvePatch q h g₁ g₂ k i j) S
        (normalToCurveKaehler q h g₁ g₂ k i j m) := by
  rw [extendedToCurve, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    KaehlerDifferential.mapBaseChange_tmul]

/-- Restriction of the quotient differential is induced by the actual
universal differential maps in the original algebra tower. -/
theorem extendedToCurve_restriction
    (m : extendedSurfaceDifferentials q h g₁ g₂ k i j S) :
    differentialRestriction S T (extendedToCurve q h g₁ g₂ k i j S m) =
      extendedToCurve q h g₁ g₂ k i j T
        (tensorRestriction (R := NormalCurvePatch q h g₁ g₂ k i j) (T := T) m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s m =>
      rw [extendedToCurve_tmul, map_smulₛₗ, tensorRestriction_tmul,
        extendedToCurve_tmul, differentialRestriction_tower]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The unique dual restriction on the actual extended conormal. Its
defining evaluation property is proved below on every conormal element. -/
def normalDualRestriction
    (φ : extendedConormal q h g₁ g₂ k i j S →ₗ[S] S) :
    extendedConormal q h g₁ g₂ k i j T →ₗ[T] T :=
  (extendedConormalEquiv q h g₁ g₂ k i j T).toLinearMap.smulRight
    (algebraMap S T (φ ((1 : S) ⊗ₜ
      normalEquationClass q h g₁ g₂ k i j i)))

omit [IsScalarTower (NormalCurvePatch q h g₁ g₂ k i j) S T]
  [Algebra ℂ S] [Algebra ℂ T]
  [IsScalarTower ℂ (NormalCurvePatch q h g₁ g₂ k i j) S]
  [IsScalarTower ℂ (NormalCurvePatch q h g₁ g₂ k i j) T]
  [IsScalarTower ℂ S T] in
@[simp] theorem normalDualRestriction_selected
    (φ : extendedConormal q h g₁ g₂ k i j S →ₗ[S] S) :
    normalDualRestriction q h g₁ g₂ k i j S T φ
      ((1 : T) ⊗ₜ normalEquationClass q h g₁ g₂ k i j i) =
      algebraMap S T (φ ((1 : S) ⊗ₜ normalEquationClass q h g₁ g₂ k i j i)) := by
  simp only [normalDualRestriction, LinearMap.smulRight_apply, LinearEquiv.coe_coe,
    extendedConormalEquiv_selected, one_smul]

omit [Algebra ℂ S] [Algebra ℂ T]
  [IsScalarTower ℂ (NormalCurvePatch q h g₁ g₂ k i j) S]
  [IsScalarTower ℂ (NormalCurvePatch q h g₁ g₂ k i j) T]
  [IsScalarTower ℂ S T] in
theorem normalDualRestriction_evaluate
    (φ : extendedConormal q h g₁ g₂ k i j S →ₗ[S] S)
    (x : extendedConormal q h g₁ g₂ k i j S) :
    normalDualRestriction q h g₁ g₂ k i j S T φ
      (tensorRestriction (R := NormalCurvePatch q h g₁ g₂ k i j) (T := T) x) =
      algebraMap S T (φ x) := by
  let e := extendedConormalEquiv q h g₁ g₂ k i j S
  let nS : extendedConormal q h g₁ g₂ k i j S :=
    (1 : S) ⊗ₜ normalEquationClass q h g₁ g₂ k i j i
  let nT : extendedConormal q h g₁ g₂ k i j T :=
    (1 : T) ⊗ₜ normalEquationClass q h g₁ g₂ k i j i
  let l : extendedConormal q h g₁ g₂ k i j S →ₛₗ[algebraMap S T]
      extendedConormal q h g₁ g₂ k i j T := tensorRestriction
  let ψ := normalDualRestriction q h g₁ g₂ k i j S T φ
  have hx : e x • nS = x := by
    apply e.injective
    rw [map_smul, extendedConormalEquiv_selected, smul_eq_mul, mul_one]
  have hl : l nS = nT := by
    change tensorRestriction ((1 : S) ⊗ₜ normalEquationClass q h g₁ g₂ k i j i) = _
    rw [tensorRestriction_tmul, map_one]
  have hp : ψ (l nS) = algebraMap S T (φ nS) :=
    (congrArg ψ hl).trans (normalDualRestriction_selected q h g₁ g₂ k i j S T φ)
  have hφ : φ x = e x * φ nS :=
    (congrArg φ hx.symm).trans (φ.map_smul (e x) nS)
  change ψ (l x) = algebraMap S T (φ x)
  calc
    ψ (l x) = ψ (l (e x • nS)) := congrArg (fun z => ψ (l z)) hx.symm
    _ = algebraMap S T (e x) * ψ (l nS) := by
      rw [l.map_smulₛₗ, ψ.map_smul, smul_eq_mul]
    _ = algebraMap S T (e x) * algebraMap S T (φ nS) :=
      congrArg (fun z => algebraMap S T (e x) * z) hp
    _ = algebraMap S T (e x * φ nS) := (map_mul (algebraMap S T) _ _).symm
    _ = algebraMap S T (φ x) := congrArg (algebraMap S T) hφ.symm

/-- The complete contraction commutes with genuine coefficient and
exterior restriction. The underlying surface factor is still the
extension of the original B tensor Omega(A) module. -/
theorem extendedAdjunction_restriction
    (φ : extendedConormal q h g₁ g₂ k i j S →ₗ[S] S)
    (w : ⋀[S]^2 (extendedSurfaceDifferentials q h g₁ g₂ k i j S)) :
    differentialRestriction S T (extendedAdjunction q h g₁ g₂ k i j S φ w) =
      extendedAdjunction q h g₁ g₂ k i j T
        (normalDualRestriction q h g₁ g₂ k i j S T φ)
        (exteriorMap (algebraMap S T)
          (tensorRestriction (R := NormalCurvePatch q h g₁ g₂ k i j) (T := T)) 2 w) := by
  have hg : differentialRestriction S T
      (extendedToCurve q h g₁ g₂ k i j S
        (extendedSurfaceBasis q h g₁ g₂ k i j S 1)) =
      extendedToCurve q h g₁ g₂ k i j T
        (extendedSurfaceBasis q h g₁ g₂ k i j T 1) :=
    (extendedToCurve_restriction q h g₁ g₂ k i j S T _).trans
      (congrArg (extendedToCurve q h g₁ g₂ k i j T)
        (tensorRestriction_basis (restrictedSurfaceBasis q h g₁ g₂ k i j) 1))
  change differentialRestriction S T
      (extendedToCurve q h g₁ g₂ k i j S
        ((restrictedSurfaceBasis q h g₁ g₂ k i j).baseChange S 1)) =
      extendedToCurve q h g₁ g₂ k i j T
        ((restrictedSurfaceBasis q h g₁ g₂ k i j).baseChange T 1) at hg
  simp only [extendedAdjunction, LinearMap.smulRight_apply, LinearEquiv.coe_coe,
    map_smulₛₗ, normalDualRestriction_selected, extendedSurfaceBasis,
    determinant_tensorRestriction, hg]

end ActualNormalChart

#print axioms determinant_tensorRestriction
#print axioms differentialRestriction_tower
#print axioms extendedToCurve_restriction
#print axioms normalDualRestriction_evaluate
#print axioms extendedAdjunction_restriction

end CycleQ2NormalAdjunctionNaturality
end

end


section

/-!
# Normal functionals are determined by original ideal generators

On an affine scheme, the actual kernel ideal sheaf is its tilde module.
The genuine open restriction adjunction therefore determines a local
functional by its values on restricted original global sections. This
is the local uniqueness input for comparing normal vectors on overlaps.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2AffineNormalGeneratorExt

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open CycleQ2GeometricIntrinsicNormal

variable {A : CommRingCat.{0}} (M N : (Spec A).Modules) (U : (Spec A).Opens)

/-- Extend a genuine local linear map by the actual restriction adjunction. -/
def extendLocalHomEquiv :
    LocalLinearHom (Spec A).sheaf M N U ≃
      (M ⟶ (Scheme.Modules.pushforward U.ι).obj (N.restrict U.ι)) :=
  (localLinearHomRestrictEquiv M N U).trans
    ((Scheme.Modules.restrictAdjunction U.ι).homEquiv M (N.restrict U.ι))

/-- At the affine top, the adjunction unit is the original section restriction. -/
theorem extendLocalHomEquiv_top
    (f : LocalLinearHom (Spec A).sheaf M N U) (m : M.val.obj (op ⊤)) :
    ((extendLocalHomEquiv M N U f).val.app (op ⊤)).hom m =
      f.val.app (op (Over.mk (homOfLE (U.ι_image_le (U.ι ⁻¹ᵁ ⊤)))))
        (M.presheaf.map (homOfLE (U.ι.image_preimage_le ⊤)).op m) := by
  change (localLinearHomRestrictEquiv M N U f).app (U.ι ⁻¹ᵁ ⊤)
    (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app ⊤ m) = _
  rw [Scheme.Modules.restrictAdjunction_unit_app_app]
  exact localLinearHomRestrictEquiv_app M N U f (U.ι ⁻¹ᵁ ⊤) _

/-- A local map on each subopen commutes with restriction of an original
global section. No localization representation is chosen. -/
theorem localLinearHom_global_restriction
    (f : LocalLinearHom (Spec A).sheaf M N U) (V : Over U)
    (m : M.val.obj (op ⊤)) :
    f.val.app (op V)
        (M.presheaf.map (homOfLE (show V.left ≤ ⊤ from le_top)).op m) =
      N.presheaf.map V.hom.op
        (localLinearHomEvaluate (Spec A).sheaf M N U f
          (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op m)) := by
  let v : V ⟶ Over.mk (𝟙 U) := Over.homMk V.hom
  have hn := ConcreteCategory.congr_hom (f.val.naturality v.op)
    (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op m)
  change f.val.app (op V)
      (M.presheaf.map V.hom.op
        (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op m)) =
    N.presheaf.map V.hom.op
      (localLinearHomEvaluate (Spec A).sheaf M N U f
        (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op m)) at hn
  have hm : M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫
      M.presheaf.map V.hom.op =
    M.presheaf.map (homOfLE (show V.left ≤ ⊤ from le_top)).op := by
    rw [← Functor.map_comp]
    rfl
  exact (congrArg (f.val.app (op V)) (ConcreteCategory.congr_hom hm m)).symm.trans hn

variable [IsIso M.fromTildeΓ]

/-- The actual affine tilde adjunction detects every local linear map
from its values on restrictions of original global sections. -/
theorem localLinearHom_ext_of_global_restrictions
    (f g : LocalLinearHom (Spec A).sheaf M N U)
    (hfg : ∀ (V : Over U) (m : M.val.obj (op ⊤)),
      f.val.app (op V) (M.presheaf.map (homOfLE (show V.left ≤ ⊤ from le_top)).op m) =
        g.val.app (op V) (M.presheaf.map (homOfLE (show V.left ≤ ⊤ from le_top)).op m)) :
    f = g := by
  apply (extendLocalHomEquiv M N U).injective
  apply (affineModule_top_app_bijective M
    ((Scheme.Modules.pushforward U.ι).obj (N.restrict U.ι))).injective
  apply LinearMap.ext
  intro m
  exact (extendLocalHomEquiv_top M N U f m).trans
    ((hfg (Over.mk (homOfLE (U.ι_image_le (U.ι ⁻¹ᵁ ⊤)))) m).trans
      (extendLocalHomEquiv_top M N U g m).symm)

/-- It suffices to compare those values on the given open: actual
naturality then compares them on every smaller open. -/
theorem localLinearHom_ext_on_global
    (f g : LocalLinearHom (Spec A).sheaf M N U)
    (hfg : ∀ m : M.val.obj (op ⊤),
      localLinearHomEvaluate (Spec A).sheaf M N U f
          (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op m) =
        localLinearHomEvaluate (Spec A).sheaf M N U g
          (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op m)) : f = g := by
  apply localLinearHom_ext_of_global_restrictions M N U f g
  intro V m
  exact (localLinearHom_global_restriction M N U f V m).trans
    ((congrArg (N.presheaf.map V.hom.op) (hfg m)).trans
      (localLinearHom_global_restriction M N U g V m).symm)

/-- A generating family in any genuine semilinear model of the original
module also detects a local morphism. Keeping this argument generic
retains the actual affine adjunction without unfolding a concrete kernel. -/
theorem localLinearHom_ext_on_generators
    {R P : Type*} [Semiring R] [AddCommMonoid P] [Module R P]
    {σ : R →+* Γ(Spec A, ⊤)}
    (e : P →ₛₗ[σ] M.val.obj (op ⊤)) (he : Function.Surjective e)
    {ι : Type*} (v : ι → P) (hv : Submodule.span R (Set.range v) = ⊤)
    (f g : LocalLinearHom (Spec A).sheaf M N U)
    (hfg : ∀ i,
      localLinearHomEvaluate (Spec A).sheaf M N U f
          (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (e (v i))) =
        localLinearHomEvaluate (Spec A).sheaf M N U g
          (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (e (v i)))) :
    f = g := by
  let F := extendLocalHomEquiv M N U f
  let G := extendLocalHomEquiv M N U g
  let lF := (F.val.app (op ⊤)).hom.comp e
  let lG := (G.val.app (op ⊤)).hom.comp e
  have hlin : lF = lG := by
    apply LinearMap.ext_on_range hv
    intro i
    change (F.val.app (op ⊤)).hom (e (v i)) = (G.val.app (op ⊤)).hom (e (v i))
    let V : Over U := Over.mk (homOfLE (U.ι_image_le (U.ι ⁻¹ᵁ ⊤)))
    have hn := congrArg (N.presheaf.map V.hom.op) (hfg i)
    exact (extendLocalHomEquiv_top M N U f _).trans
      ((localLinearHom_global_restriction M N U f V _).trans
        (hn.trans ((localLinearHom_global_restriction M N U g V _).symm.trans
          (extendLocalHomEquiv_top M N U g _).symm)))
  apply (extendLocalHomEquiv M N U).injective
  apply (affineModule_top_app_bijective M
    ((Scheme.Modules.pushforward U.ι).obj (N.restrict U.ι))).injective
  apply LinearMap.ext
  intro m
  obtain ⟨a, rfl⟩ := he m
  exact LinearMap.congr_fun hlin a

section IdealGenerators

variable {B : CommRingCat.{0}} (φ : A ⟶ B)

/-- The original affine kernel is the global module of the actual ideal
sheaf, through the canonical Spec section maps. -/
def originalIdealSectionEquiv :
    RingHom.ker φ.hom ≃ₛₗ[(specTopRingEquiv A).symm.toRingHom]
      (kernelIdealSheaf (Spec.map φ)).val.obj (op ⊤) :=
  (affineKernelSectionSemilinearEquiv φ).symm.trans
    (kernelIdealSectionEquiv (Spec.map φ) ⊤).symm

/-- Restrict an original ideal element as an actual section of the
intrinsic ideal on an arbitrary affine subopen. -/
def restrictedOriginalIdeal (U : (Spec A).Opens) (a : RingHom.ker φ.hom) :
    RingHom.ker ((Spec.map φ).app U).hom :=
  kernelSectionRestrict (Spec.map φ) (homOfLE (show U ≤ ⊤ from le_top))
    ((affineKernelSectionSemilinearEquiv φ).symm a)

theorem normalSectionEvaluate_original (U : (Spec A).Opens)
    (f : (normalDirectImageSheaf (Spec.map φ)).val.obj (op U))
    (a : RingHom.ker φ.hom) :
    normalSectionEvaluate (Spec.map φ) U f (restrictedOriginalIdeal φ U a) =
      localLinearHomEvaluate (Spec A).sheaf
        (kernelIdealSheaf (Spec.map φ)) (imageStructureModule (Spec.map φ)) U f
        ((show (Spec A).Modules from kernelIdealSheaf (Spec.map φ)).presheaf.map
          (homOfLE (show U ≤ ⊤ from le_top)).op (originalIdealSectionEquiv φ a)) := by
  change localLinearHomEvaluate (Spec A).sheaf
      (kernelIdealSheaf (Spec.map φ)) (imageStructureModule (Spec.map φ)) U f
      ((kernelIdealSectionEquiv (Spec.map φ) U).symm
        ((kernelIdealSectionEquiv (Spec.map φ) U)
          ((show (Spec A).Modules from kernelIdealSheaf (Spec.map φ)).presheaf.map
            (homOfLE (show U ≤ ⊤ from le_top)).op (originalIdealSectionEquiv φ a)))) = _
  exact congrArg (localLinearHomEvaluate (Spec A).sheaf
    (kernelIdealSheaf (Spec.map φ)) (imageStructureModule (Spec.map φ)) U f)
      ((kernelIdealSectionEquiv (Spec.map φ) U).symm_apply_apply _)

/-- Agreement on restricted original ideal elements detects an actual
normal section on every subopen of the affine scheme. -/
theorem affineNormal_ext_on_originalIdeal (U : (Spec A).Opens)
    (f g : (normalDirectImageSheaf (Spec.map φ)).val.obj (op U))
    (hfg : ∀ a : RingHom.ker φ.hom,
      normalSectionEvaluate (Spec.map φ) U f (restrictedOriginalIdeal φ U a) =
        normalSectionEvaluate (Spec.map φ) U g (restrictedOriginalIdeal φ U a)) :
    f = g := by
  apply localLinearHom_ext_on_global
    (show (Spec A).Modules from kernelIdealSheaf (Spec.map φ))
    (show (Spec A).Modules from imageStructureModule (Spec.map φ)) U f g
  intro m
  obtain ⟨a, rfl⟩ := (originalIdealSectionEquiv φ).surjective m
  exact (normalSectionEvaluate_original φ U f a).symm.trans
    ((hfg a).trans (normalSectionEvaluate_original φ U g a))

/-- For a generating family of the original kernel, only its equation
values need to be compared. The proof uses the genuine restriction
adjunction and affine tilde theorem, with no local freeness premise. -/
theorem affineNormal_ext_on_generators {ι : Type*}
    (v : ι → RingHom.ker φ.hom)
    (hv : Submodule.span A (Set.range v) = ⊤) (U : (Spec A).Opens)
    (f g : (normalDirectImageSheaf (Spec.map φ)).val.obj (op U))
    (hfg : ∀ i,
      normalSectionEvaluate (Spec.map φ) U f (restrictedOriginalIdeal φ U (v i)) =
        normalSectionEvaluate (Spec.map φ) U g (restrictedOriginalIdeal φ U (v i))) :
    f = g := by
  apply localLinearHom_ext_on_generators
    (show (Spec A).Modules from kernelIdealSheaf (Spec.map φ))
    (show (Spec A).Modules from imageStructureModule (Spec.map φ)) U
    (originalIdealSectionEquiv φ).toLinearMap (originalIdealSectionEquiv φ).surjective
    v hv f g
  intro i
  exact (normalSectionEvaluate_original φ U f (v i)).symm.trans
    ((hfg i).trans (normalSectionEvaluate_original φ U g (v i)))

end IdealGenerators

end CycleQ2AffineNormalGeneratorExt

namespace CycleQ2AffineNormalPatchExt

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricAffineCurveCharts CycleQ2AffineNormalGeneratorExt

variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)

abbrev patchMap := CommRingCat.ofHom (normalChartMap q h g₁ g₂ k i j).toRingHom

/-- The two literal equations generate the original kernel as a module,
including on every possibly degenerate augmented-Jacobian chart. -/
theorem equationGenerators_span :
    Submodule.span (NormalSurfacePatch q h g₁ g₂ k i j)
      (Set.range (fun a : Fin 2 =>
        (⟨algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j)
          (normalPolynomial q a), normalEquation_mem q h g₁ g₂ k i j a⟩ :
            RingHom.ker (patchMap q h g₁ g₂ k i j).hom))) = ⊤ :=
  (Submodule.span_range_subtype_eq_top_iff
    (NormalCurveIdeal q h g₁ g₂ k i j)
    (normalEquation_mem q h g₁ g₂ k i j)).mpr
      (normalEquations_span q h g₁ g₂ k i j)

/-- The original defining equation as an actual ideal section on any
subopen of the affine normal patch. -/
def equationOn
    (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).Opens)
    (a : Fin 2) : RingHom.ker ((Spec.map (patchMap q h g₁ g₂ k i j)).app U).hom :=
  restrictedOriginalIdeal (patchMap q h g₁ g₂ k i j) U
    ⟨algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j)
      (normalPolynomial q a), normalEquation_mem q h g₁ g₂ k i j a⟩

/-- Every actual intrinsic normal section on every subopen of an
augmented-Jacobian chart is determined by the two defining-equation values.
All generation hypotheses are discharged by the original chart equations. -/
theorem normalSection_ext
    (U : (Spec (CommRingCat.of (NormalSurfacePatch q h g₁ g₂ k i j))).Opens)
    (f g : (normalDirectImageSheaf (Spec.map (patchMap q h g₁ g₂ k i j))).val.obj (op U))
    (hfg : ∀ a : Fin 2,
      normalSectionEvaluate (Spec.map (patchMap q h g₁ g₂ k i j)) U f
        (equationOn q h g₁ g₂ k i j U a) =
      normalSectionEvaluate (Spec.map (patchMap q h g₁ g₂ k i j)) U g
        (equationOn q h g₁ g₂ k i j U a)) : f = g :=
  affineNormal_ext_on_generators (patchMap q h g₁ g₂ k i j)
    (fun a : Fin 2 => ⟨algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j)
      (normalPolynomial q a), normalEquation_mem q h g₁ g₂ k i j a⟩)
    (equationGenerators_span q h g₁ g₂ k i j) U f g hfg

end CycleQ2AffineNormalPatchExt
end

end


section

/-! Genuine local module morphisms on an affine scheme are determined by
the original global module and the actual target sections on the open.
The equivalence uses the restriction adjunction and affine tilde theorem. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2AffineLocalHom

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricIntrinsicNormal CycleQ2AffineNormalGeneratorExt

variable {A : CommRingCat.{0}} (M N : (Spec A).Modules) (U : (Spec A).Opens)

def openExtension : (Spec A).Modules :=
  (Scheme.Modules.pushforward U.ι).obj (N.restrict U.ι)

/-- The global sections of the genuine open pushforward are the original
sections on that open, through the canonical equality of opens. -/
def openExtensionTopIso : Γ(openExtension N U, ⊤) ≅ Γ(N, U) :=
  N.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

theorem openExtensionTopIso_smul (a : A) (x : Γ(openExtension N U, ⊤)) :
    (openExtensionTopIso N U).hom (a • x) =
      a • (openExtensionTopIso N U).hom x := by
  let W : (Spec A).Opens := U.ι ''ᵁ ⊤
  let e : U ⟶ W := eqToHom U.ι_image_top.symm
  let x' : Γ(N, W) := x
  let a₀ : Γ(Spec A, ⊤) := (Scheme.ΓSpecIso A).inv a
  let b : Γ(Spec A, W) := (U.ι.appIso ⊤).inv (U.ι.app ⊤ a₀)
  change N.presheaf.map e.op (b • x') =
    (Spec A).presheaf.map U.leTop.op a₀ • N.presheaf.map e.op x'
  rw [N.map_smul]
  apply congrArg (fun c : Γ(Spec A, U) => c • N.presheaf.map e.op x')
  have hb : b = (Spec A).presheaf.map
      (homOfLE (U.ι.image_preimage_le ⊤)).op a₀ :=
    ConcreteCategory.congr_hom (U.ι.app_appIso_inv ⊤) a₀
  have hc : (Spec A).presheaf.map
      (homOfLE (U.ι.image_preimage_le ⊤)).op ≫
        (Spec A).presheaf.map e.op = (Spec A).presheaf.map U.leTop.op := by
    let p : W ⟶ ⊤ := homOfLE (U.ι.image_preimage_le ⊤)
    exact ((Spec A).presheaf.map_comp p.op e.op).symm.trans
      (congrArg (fun z : op (⊤ : (Spec A).Opens) ⟶ op U =>
        (Spec A).presheaf.map z) (Subsingleton.elim _ _))
  exact (congrArg ((Spec A).presheaf.map e.op) hb).trans
    (ConcreteCategory.congr_hom hc a₀)

/-- This comparison retains the original affine coefficient action. -/
def openExtensionTopEquiv : Γ(openExtension N U, ⊤) ≃ₗ[A] Γ(N, U) :=
  LinearEquiv.ofBijective
    { toFun := (openExtensionTopIso N U).hom.hom
      map_add' := (openExtensionTopIso N U).hom.hom.map_add
      map_smul' := openExtensionTopIso_smul N U }
    (ConcreteCategory.bijective_of_isIso (openExtensionTopIso N U).hom)

variable [IsIso M.fromTildeΓ]

/-- Local morphisms have exactly the original affine-module linear
functionals into actual sections of the target on the open. -/
def localHomOriginalEquiv :
    LocalLinearHom (Spec A).sheaf M N U ≃ (Γ(M, ⊤) →ₗ[A] Γ(N, U)) :=
  (extendLocalHomEquiv M N U).trans
    ((affineModuleHomEquiv M (openExtension N U)).trans
      (ModuleCat.homEquiv.trans
        (((LinearEquiv.refl A Γ(M, ⊤)).arrowCongr
          (openExtensionTopEquiv N U)).toEquiv)))

/-- Its underlying map is evaluation on restricted original sections. -/
theorem localHomOriginalEquiv_apply
    (f : LocalLinearHom (Spec A).sheaf M N U) (m : Γ(M, ⊤)) :
    localHomOriginalEquiv M N U f m =
      (localLinearHomEvaluate (Spec A).sheaf M N U f).toFun
        (M.presheaf.map U.leTop.op m) := by
  let W : (Spec A).Opens := U.ι ''ᵁ ⊤
  let e : U ⟶ W := eqToHom U.ι_image_top.symm
  let V : Over U := Over.mk (homOfLE (U.ι_image_le ⊤))
  let l : Γ(N, U) → Γ(N, W) := N.presheaf.map V.hom.op
  have he := extendLocalHomEquiv_top M N U f m
  have hn := localLinearHom_global_restriction M N U f V m
  have hi : N.presheaf.map V.hom.op ≫ N.presheaf.map e.op = 𝟙 _ := by
    rw [← Functor.map_comp]
    exact N.presheaf.map_id (op U)
  change (openExtensionTopIso N U).hom
    (((affineModuleHomEquiv M (openExtension N U))
      (extendLocalHomEquiv M N U f)).hom m) = _
  have ha := affineModuleHomEquiv_apply M (openExtension N U)
    (extendLocalHomEquiv M N U f)
  have hm := congrArg (fun F : (affineEvaluation A ⊤).obj M ⟶
      (affineEvaluation A ⊤).obj (openExtension N U) => F.hom m) ha
  exact (congrArg ((openExtensionTopIso N U).hom) (hm.trans (he.trans hn))).trans
    (ConcreteCategory.congr_hom hi
      ((localLinearHomEvaluate (Spec A).sheaf M N U f).toFun
        (M.presheaf.map U.leTop.op m)))

#print axioms openExtensionTopEquiv
#print axioms localHomOriginalEquiv
#print axioms localHomOriginalEquiv_apply

end CycleQ2AffineLocalHom
end

end


section

/-! Genuine two-open cohomology classes survive closed direct image.
The opens on the target are explicit complements of closed images. The
comparison uses the actual pushforward restrictions and Mayer--Vietoris
kernel, with no general direct-image cohomology theorem assumed. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ClosedSupportCohomology

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology Opposite
  CycleQ2GeometricConeCech.HZero

universe u w
variable {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : IsClosedEmbedding f)

/-- Extend an open of the closed subspace by the whole complement. -/
def extendedOpen (U : Opens X) : Opens Y :=
  ⟨(f '' (U : Set X)ᶜ)ᶜ, (hf.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩

theorem preimage_extendedOpen (U : Opens X) :
    (Opens.map f).obj (extendedOpen f hf U) = U := by
  classical
  ext x
  change (f x ∉ f '' (U : Set X)ᶜ) ↔ x ∈ U
  simp only [Set.mem_image, hf.injective.eq_iff, exists_eq_right,
    Set.mem_compl_iff, not_not]
  rfl

theorem extendedOpen_mono {U V : Opens X} (hUV : U ≤ V) :
    extendedOpen f hf U ≤ extendedOpen f hf V := by
  intro y hy hyV
  apply hy
  obtain ⟨x,hx,hxy⟩ := hyV
  exact ⟨x, fun hxU => hx (hUV hxU), hxy⟩

theorem extendedOpen_top : extendedOpen f hf ⊤ = ⊤ := by
  ext y
  simp [extendedOpen]

theorem extendedOpen_inf (U V : Opens X) :
    extendedOpen f hf (U ⊓ V) = extendedOpen f hf U ⊓ extendedOpen f hf V := by
  ext y
  change (y ∉ f '' ((U : Set X) ∩ (V : Set X))ᶜ) ↔
    (y ∉ f '' (U : Set X)ᶜ ∧ y ∉ f '' (V : Set X)ᶜ)
  rw [Set.compl_inter, Set.image_union, Set.mem_union, not_or]

theorem extendedOpen_sup (U V : Opens X) :
    extendedOpen f hf (U ⊔ V) = extendedOpen f hf U ⊔ extendedOpen f hf V := by
  classical
  ext y
  change (y ∉ f '' ((U : Set X) ∪ (V : Set X))ᶜ) ↔
    (y ∉ f '' (U : Set X)ᶜ ∨ y ∉ f '' (V : Set X)ᶜ)
  rw [Set.compl_union, Set.image_inter hf.injective, Set.mem_inter_iff, not_and_or]

theorem extendedOpen_cover (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    extendedOpen f hf U ⊔ extendedOpen f hf V = ⊤ := by
  rw [← extendedOpen_sup, hUV, extendedOpen_top]

variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

def sectionsEq {U V : Opens X} (h : U = V) :
    F.obj.obj (op U) ≃+ F.obj.obj (op V) :=
  (F.obj.mapIso (eqToIso h).symm.op).addCommGroupIsoToAddEquiv

theorem sectionsEq_restrict {U V U' V' : Opens X} (hU : U = U') (hV : V = V')
    (hVU : V ≤ U) (hVU' : V' ≤ U') (a : F.obj.obj (op U)) :
    sectionsEq F hV (F.obj.map (homOfLE hVU).op a) =
      F.obj.map (homOfLE hVU').op (sectionsEq F hU a) := by
  subst U'
  subst V'
  simp [sectionsEq]

abbrev directImage := (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F

def pushedSectionsEquiv (U : Opens X) :
    (directImage f F).obj.obj (op (extendedOpen f hf U)) ≃+ F.obj.obj (op U) :=
  sectionsEq F (preimage_extendedOpen f hf U)

theorem pushedSectionsEquiv_restrict {U V : Opens X} (hVU : V ≤ U)
    (a : (directImage f F).obj.obj (op (extendedOpen f hf U))) :
    pushedSectionsEquiv f hf F V
        ((directImage f F).obj.map (homOfLE (extendedOpen_mono f hf hVU)).op a) =
      F.obj.map (homOfLE hVU).op (pushedSectionsEquiv f hf F U a) :=
  sectionsEq_restrict F (preimage_extendedOpen f hf U) (preimage_extendedOpen f hf V)
    (fun _ hx => extendedOpen_mono f hf hVU hx) hVU a

def coverSquare (U V W : Opens X) (hW : W = U ⊓ V) (hUV : U ⊔ V = ⊤) :
    (Opens.grothendieckTopology X).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := W
      X₂ := U
      X₃ := V
      X₄ := ⊤
      f₁₂ := homOfLE (hW.le.trans inf_le_left)
      f₁₃ := homOfLE (hW.le.trans inf_le_right)
      f₂₄ := homOfLE le_top
      f₃₄ := homOfLE le_top
      fac := Subsingleton.elim _ _ }
    hUV.symm hW

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

def sectionBoundary (S : (Opens.grothendieckTopology X).MayerVietorisSquare) :
    F.obj.obj (op S.X₁) →+ F.H' 1 S.X₄ :=
  (S.δ F 0 1 rfl).hom.comp (sectionsEquiv F S.X₁).symm.toAddMonoidHom

theorem sectionBoundary_zero_iff
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (z : F.obj.obj (op S.X₁)) :
    sectionBoundary F S z = 0 ↔
      ∃ (a : F.obj.obj (op S.X₂)) (b : F.obj.obj (op S.X₃)),
        F.obj.map S.f₁₂.op a - F.obj.map S.f₁₃.op b = z := by
  change S.δ F 0 1 rfl ((sectionsEquiv F S.X₁).symm z) = 0 ↔ _
  constructor
  · intro hz
    obtain ⟨y,hy⟩ := (ShortComplex.ab_exact_iff _).mp
      ((S.sequence_exact F 0 1 rfl).exact 1) ((sectionsEquiv F S.X₁).symm z) hz
    have hy' : S.fromBiprod F 0 y = (sectionsEquiv F S.X₁).symm z := hy
    obtain ⟨⟨a,b⟩,rfl⟩ :=
      (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective y
    rw [Iso.addCommGroupIsoToAddEquiv_symm_apply,
      S.fromBiprod_biprodIsoProd_inv_apply] at hy'
    refine ⟨sectionsEquiv F S.X₂ a, sectionsEquiv F S.X₃ b, ?_⟩
    have hh := congrArg (sectionsEquiv F S.X₁) hy'
    simpa only [map_sub, sectionsEquiv_naturality, AddEquiv.apply_symm_apply] using hh
  · rintro ⟨a,b,h⟩
    let a' := (sectionsEquiv F S.X₂).symm a
    let b' := (sectionsEquiv F S.X₃).symm b
    have h' : (F.cohomologyPresheaf 0).map S.f₁₂.op a' -
        (F.cohomologyPresheaf 0).map S.f₁₃.op b' = (sectionsEquiv F S.X₁).symm z := by
      apply (sectionsEquiv F S.X₁).injective
      simpa only [map_sub, sectionsEquiv_naturality, AddEquiv.apply_symm_apply,
        a', b'] using h
    rw [← h', ← S.fromBiprod_biprodIsoProd_inv_apply]
    exact congrArg
      (fun k : (F.H' 0 S.X₂ ⊞ F.H' 0 S.X₃) ⟶ F.H' 1 S.X₄ =>
        k ((AddCommGrpCat.biprodIsoProd _ _).inv (a',b')))
      (S.fromBiprod_δ F 0 1 rfl)

end CycleQ2ClosedSupportCohomology
end

end


section

/-! The actual target-space Mayer--Vietoris boundary for a closed
immersion has exactly the same kernel on the original overlap sections.
It is functorial in the original sheaf. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ClosedSupportBoundary

open CategoryTheory TopologicalSpace Topology Opposite
  CycleQ2GeometricConeCech.HZero CycleQ2ClosedSupportCohomology
  CycleQ2GeometricCanonicalCechBoundary

universe u w
variable {X Y : TopCat.{u}} (f : X ⟶ Y) (hf : IsClosedEmbedding f)
variable (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

def targetCoverSquare (U V W : Opens X) (hW : W = U ⊓ V) (hUV : U ⊔ V = ⊤) :
    (Opens.grothendieckTopology Y).MayerVietorisSquare :=
  coverSquare (extendedOpen f hf U) (extendedOpen f hf V) (extendedOpen f hf W)
    ((congrArg (extendedOpen f hf) hW).trans (extendedOpen_inf f hf U V))
    (extendedOpen_cover f hf U V hUV)

section FirstCohomology
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]

def pushforwardBoundary (U V W : Opens X) (hW : W = U ⊓ V) (hUV : U ⊔ V = ⊤) :
    F.obj.obj (op W) →+ (directImage f F).H' 1 ⊤ :=
  (sectionBoundary (directImage f F) (targetCoverSquare f hf U V W hW hUV)).comp
    (pushedSectionsEquiv f hf F W).symm.toAddMonoidHom

theorem pushforwardBoundary_zero_iff (U V W : Opens X)
    (hW : W = U ⊓ V) (hUV : U ⊔ V = ⊤) (z : F.obj.obj (op W)) :
    pushforwardBoundary f hf F U V W hW hUV z = 0 ↔
      sectionBoundary F (coverSquare U V W hW hUV) z = 0 := by
  have hl (a : (directImage f F).obj.obj (op (extendedOpen f hf U))) :
      pushedSectionsEquiv f hf F W
        ((directImage f F).obj.map (targetCoverSquare f hf U V W hW hUV).f₁₂.op a) =
        F.obj.map (coverSquare U V W hW hUV).f₁₂.op (pushedSectionsEquiv f hf F U a) :=
    pushedSectionsEquiv_restrict f hf F (hW.le.trans inf_le_left) a
  have hr (b : (directImage f F).obj.obj (op (extendedOpen f hf V))) :
      pushedSectionsEquiv f hf F W
        ((directImage f F).obj.map (targetCoverSquare f hf U V W hW hUV).f₁₃.op b) =
        F.obj.map (coverSquare U V W hW hUV).f₁₃.op (pushedSectionsEquiv f hf F V b) :=
    pushedSectionsEquiv_restrict f hf F (hW.le.trans inf_le_right) b
  apply (sectionBoundary_zero_iff (directImage f F) (targetCoverSquare f hf U V W hW hUV)
    ((pushedSectionsEquiv f hf F W).symm z)).trans
  apply Iff.trans ?_ (sectionBoundary_zero_iff F (coverSquare U V W hW hUV) z).symm
  constructor
  · rintro ⟨a,b,h⟩
    refine ⟨pushedSectionsEquiv f hf F U a, pushedSectionsEquiv f hf F V b, ?_⟩
    have hh := congrArg (pushedSectionsEquiv f hf F W) h
    simpa only [map_sub, hl, hr, AddEquiv.apply_symm_apply] using hh
  · rintro ⟨a,b,h⟩
    refine ⟨(pushedSectionsEquiv f hf F U).symm a,
      (pushedSectionsEquiv f hf F V).symm b, ?_⟩
    apply (pushedSectionsEquiv f hf F W).injective
    simpa only [map_sub, hl, hr, AddEquiv.apply_symm_apply] using h

end FirstCohomology

variable {F} {G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (α : F ⟶ G)

theorem sectionsEq_map {U V : Opens X} (h : U = V) (z : F.obj.obj (op U)) :
    sectionsEq G h (α.hom.app (op U) z) = α.hom.app (op V) (sectionsEq F h z) := by
  subst V
  simp [sectionsEq]

theorem pushedSectionsEquiv_map (U : Opens X)
    (z : (directImage f F).obj.obj (op (extendedOpen f hf U))) :
    pushedSectionsEquiv f hf G U
      (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map α).hom.app
        (op (extendedOpen f hf U)) z) =
      α.hom.app (op U) (pushedSectionsEquiv f hf F U z) :=
  sectionsEq_map α (preimage_extendedOpen f hf U) z

theorem pushedSectionsEquiv_symm_map (U : Opens X) (z : F.obj.obj (op U)) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map α).hom.app
        (op (extendedOpen f hf U)) ((pushedSectionsEquiv f hf F U).symm z) =
      (pushedSectionsEquiv f hf G U).symm (α.hom.app (op U) z) := by
  apply (pushedSectionsEquiv f hf G U).injective
  rw [pushedSectionsEquiv_map, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

theorem sectionBoundary_map (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (z : F.obj.obj (op S.X₁)) :
    ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) 1).map α).app
        (op S.X₄) (sectionBoundary F S z) =
      sectionBoundary G S (α.hom.app (op S.X₁) z) := by
  exact (mayerVietoris_delta_naturality α S 0 1 rfl
    ((sectionsEquiv F S.X₁).symm z)).trans
      (congrArg (S.δ G 0 1 rfl) (sectionsEquiv_symm_map α S.X₁ z))

variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]

omit [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})] in
theorem pushforwardBoundary_map (U V W : Opens X)
    (hW : W = U ⊓ V) (hUV : U ⊔ V = ⊤) (z : F.obj.obj (op W)) :
    ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) 1).map
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map α)).app (op ⊤)
        (pushforwardBoundary f hf F U V W hW hUV z) =
      pushforwardBoundary f hf G U V W hW hUV (α.hom.app (op W) z) := by
  exact (sectionBoundary_map ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map α)
    (targetCoverSquare f hf U V W hW hUV) ((pushedSectionsEquiv f hf F W).symm z)).trans
      (congrArg (sectionBoundary (directImage f G) (targetCoverSquare f hf U V W hW hUV))
        (pushedSectionsEquiv_symm_map f hf α W z))

theorem pushforwardBoundary_map_zero_iff (U V W : Opens X)
    (hW : W = U ⊓ V) (hUV : U ⊔ V = ⊤) (z : F.obj.obj (op W)) :
    ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Y) 1).map
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).map α)).app (op ⊤)
        (pushforwardBoundary f hf F U V W hW hUV z) = 0 ↔
      ((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) 1).map α).app
        (op ⊤) (sectionBoundary F (coverSquare U V W hW hUV) z) = 0 := by
  have ht := pushforwardBoundary_map f hf α U V W hW hUV z
  have hs := sectionBoundary_map α (coverSquare U V W hW hUV) z
  have hzero := pushforwardBoundary_zero_iff f hf G U V W hW hUV (α.hom.app (op W) z)
  constructor
  · intro h
    exact hs.trans (hzero.mp (ht.symm.trans h))
  · intro h
    exact ht.trans (hzero.mpr (hs.symm.trans h))

end CycleQ2ClosedSupportBoundary
end

end


section

/-! Actual rank-two differential frames and their genuine module-sheaf
pullbacks. The surface differential module is retained under scalar
extension to the curve and to every open of its affine chart. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2SurfacePullbackFrame

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2GeometricFunctionalDifferentials
open scoped TensorProduct

abbrev structureModule (X : Scheme.{0}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

local instance affineSectionsAlgebra {B : Type} [CommRing B]
    (V : (Spec (CommRingCat.of B)).Opens) : Algebra B Γ(Spec (CommRingCat.of B),V) := by
  change Algebra B ((Spec.structureSheaf B).obj.obj (op V))
  infer_instance

local instance affineSectionsSMul {B : Type} [CommRing B]
    (V : (Spec (CommRingCat.of B)).Opens) : SMul B Γ(Spec (CommRingCat.of B),V) :=
  (affineSectionsAlgebra V).toSMul

local instance affineSectionsModule {B : Type} [CommRing B]
    (V : (Spec (CommRingCat.of B)).Opens) : Module B Γ(Spec (CommRingCat.of B),V) :=
  @Algebra.toModule B Γ(Spec (CommRingCat.of B),V) _ _ (affineSectionsAlgebra V)

abbrev affineDifferentialModule (A : Type) [CommRing A] [Algebra ℂ A] :
    (Spec (CommRingCat.of A)).Modules := affineDifferentialSheaf A

/-- A genuine frame consists of actual module-sheaf morphisms with the
two inverse identities. The affine differential frame below constructs
this data from the original Kähler basis. -/
structure TwoFrame {X : Scheme.{0}} (M : X.Modules) where
  coordinate : Fin 2 → (M ⟶ structureModule X)
  vector : Fin 2 → (structureModule X ⟶ M)
  vector_coordinate : ∀ i j, vector i ≫ coordinate j =
    if j = i then 𝟙 (structureModule X) else 0
  reconstruction : coordinate 0 ≫ vector 0 + coordinate 1 ≫ vector 1 = 𝟙 M

namespace TwoFrame

variable {X : Scheme.{0}} {M : X.Modules} (b : TwoFrame M)

theorem coordinate_vector_value (U : X.Opens) (i j : Fin 2) (c : Γ(X,U)) :
    (b.coordinate j).app U ((b.vector i).app U c) = if j = i then c else 0 := by
  have h := congrArg (fun f : structureModule X ⟶ structureModule X =>
    f.app U c) (b.vector_coordinate i j)
  by_cases hji : j = i
  · rw [if_pos hji] at h ⊢
    exact h
  · rw [if_neg hji] at h ⊢
    exact h

def sectionEquiv (U : X.Opens) : Γ(M,U) ≃ₗ[Γ(X,U)] (Fin 2 → Γ(X,U)) where
  toFun x i := (b.coordinate i).app U x
  invFun c := (b.vector 0).app U (c 0) + (b.vector 1).app U (c 1)
  left_inv x := by
    exact congrArg (fun f : M ⟶ M => f.app U x) b.reconstruction
  right_inv c := by
    funext i
    change (b.coordinate i).app U ((b.vector 0).app U (c 0) +
      (b.vector 1).app U (c 1)) = c i
    rw [map_add]
    rw [coordinate_vector_value, coordinate_vector_value]
    fin_cases i
    · change c 0 + (0 : Γ(X,U)) = c 0
      exact add_zero _
    · change (0 : Γ(X,U)) + c 1 = c 1
      exact zero_add _
  map_add' x y := by funext i; exact map_add _ _ _
  map_smul' r x := by funext i; exact Scheme.Modules.Hom.app_smul _ _ _

def sectionBasis (U : X.Opens) : Basis (Fin 2) Γ(X,U) Γ(M,U) :=
  Basis.ofEquivFun (b.sectionEquiv U)

theorem sectionBasis_apply (U : X.Opens) (i : Fin 2) :
    b.sectionBasis U i = (b.vector i).app U (1 : Γ(X,U)) := by
  apply (b.sectionEquiv U).injective
  have hi := congrFun (Basis.coe_ofEquivFun (b.sectionEquiv U)) i
  change b.sectionEquiv U (b.sectionBasis U i) = _
  rw [show b.sectionBasis U i = (b.sectionEquiv U).symm (Pi.single i 1) from hi,
    LinearEquiv.apply_symm_apply]
  funext j
  change (Pi.single i 1 : Fin 2 → Γ(X,U)) j =
    (b.coordinate j).app U ((b.vector i).app U (1 : Γ(X,U)))
  rw [coordinate_vector_value]
  simp only [Pi.single_apply, eq_comm]

theorem sectionEquiv_restrict {U V : X.Opens} (a : V ⟶ U) (x : Γ(M,U)) (i : Fin 2) :
    b.sectionEquiv V (M.presheaf.map a.op x) i =
      X.presheaf.map a.op (b.sectionEquiv U x i) := by
  exact ConcreteCategory.congr_hom ((b.coordinate i).mapPresheaf.naturality a.op) x

theorem sectionBasis_restrict {U V : X.Opens} (a : V ⟶ U) (i : Fin 2) :
    M.presheaf.map a.op (b.sectionBasis U i) = b.sectionBasis V i := by
  rw [sectionBasis_apply, sectionBasis_apply]
  have h := ConcreteCategory.congr_hom ((b.vector i).mapPresheaf.naturality a.op)
    (1 : Γ(X,U))
  have hm : X.presheaf.map a.op (1 : Γ(X,U)) = (1 : Γ(X,V)) := map_one _
  exact h.symm.trans (congrArg ((b.vector i).app V) hm)

end TwoFrame

section Pullback

variable {X Y : Scheme.{0}} (j : X ⟶ Y)

local instance : (SheafOfModules.pushforward.{0} j.toRingCatSheafHom).IsRightAdjoint := by
  exact inferInstanceAs (Scheme.Modules.pushforward j).IsRightAdjoint

local instance : (Opens.map j.base).Final := by
  let : (Functor.fromPUnit.{0} (⊤ : Y.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal CategoryTheory.Limits.isTerminalTop
  let : (Functor.fromPUnit.{0} (⊤ : X.Opens)).Final :=
    Functor.final_fromPUnit_of_isTerminal CategoryTheory.Limits.isTerminalTop
  let : (Functor.fromPUnit.{0} (⊤ : Y.Opens) ⋙ Opens.map j.base).Final :=
    Functor.final_of_natIso (F := Functor.fromPUnit.{0} (⊤ : X.Opens))
      (Discrete.natIso fun _ => Iso.refl _)
  exact Functor.final_of_final_comp (Functor.fromPUnit.{0} (⊤ : Y.Opens)) (Opens.map j.base)

/-- The canonical pullback of the structure module, characterized by the
original ring-sheaf morphism and the pullback adjunction. -/
private def rawPullbackUnitIso :
    CategoryTheory.Iso (C := SheafOfModules.{0} X.ringCatSheaf)
      ((SheafOfModules.pullback.{0} j.toRingCatSheafHom).obj
        (SheafOfModules.unit Y.ringCatSheaf)) (SheafOfModules.unit X.ringCatSheaf) :=
  asIso (C := SheafOfModules.{0} X.ringCatSheaf)
    (SheafOfModules.pullbackObjUnitToUnit.{0} j.toRingCatSheafHom)

def pullbackUnitIso :
    (Scheme.Modules.pullback j).obj (structureModule Y) ≅ structureModule X where
  hom := (rawPullbackUnitIso j).hom
  inv := (rawPullbackUnitIso j).inv
  hom_inv_id := (rawPullbackUnitIso j).hom_inv_id
  inv_hom_id := (rawPullbackUnitIso j).inv_hom_id

variable {M : Y.Modules} (b : TwoFrame M)

def TwoFrame.pullback : TwoFrame ((Scheme.Modules.pullback j).obj M) where
  coordinate i := (Scheme.Modules.pullback j).map (b.coordinate i) ≫ (pullbackUnitIso j).hom
  vector i := (pullbackUnitIso j).inv ≫ (Scheme.Modules.pullback j).map (b.vector i)
  vector_coordinate i k := by
    simp only [Category.assoc, ← Functor.map_comp_assoc, b.vector_coordinate]
    split_ifs
    · simp
    · simp
  reconstruction := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
      ← Functor.map_add, b.reconstruction]
    exact (Scheme.Modules.pullback j).map_id M

/-- The canonical unit-to-unit map is the actual scheme structure map. -/
theorem pullbackUnitIso_unit :
    (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app (structureModule Y) ≫
      (Scheme.Modules.pushforward j).map (pullbackUnitIso j).hom =
      SheafOfModules.unitToPushforwardObjUnit.{0} j.toRingCatSheafHom := by
  change (SheafOfModules.pullbackPushforwardAdjunction.{0} j.toRingCatSheafHom).unit.app _ ≫
    (SheafOfModules.pushforward.{0} j.toRingCatSheafHom).map
      (SheafOfModules.pullbackObjUnitToUnit.{0} j.toRingCatSheafHom) = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    j.toRingCatSheafHom

/-- Coordinates of the genuine adjunction unit are pulled back by the
actual structure-sheaf map. -/
theorem pullback_coordinate_unit (U : Y.Opens) (x : Γ(M,U)) (i : Fin 2) :
    ((b.pullback j).coordinate i).app (j ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M).app U x) =
      j.app U ((b.coordinate i).app U x) := by
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality (b.coordinate i)
  have hm : (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M ≫
      (Scheme.Modules.pushforward j).map ((b.pullback j).coordinate i) =
      b.coordinate i ≫ SheafOfModules.unitToPushforwardObjUnit j.toRingCatSheafHom := by
    change (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M ≫
      (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.pullback j).map (b.coordinate i) ≫ (pullbackUnitIso j).hom) = _
    rw [Functor.map_comp, ← Category.assoc]
    change ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M ≫
      (Scheme.Modules.pullback j ⋙ Scheme.Modules.pushforward j).map (b.coordinate i)) ≫ _ = _
    rw [← hn]
    change (b.coordinate i ≫ (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
      (structureModule Y)) ≫ _ = _
    rw [Category.assoc, pullbackUnitIso_unit]
  exact congrArg (fun f : M ⟶ (Scheme.Modules.pushforward j).obj (structureModule X) =>
    f.app U x) hm

end Pullback

section AffineFrame

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The original algebraic differential as an actual global sheaf section. -/
def affineDifferentialSection :
    KaehlerDifferential ℂ A →ₗ[A] (affineDifferentialSheaf A).val.obj (op ⊤) :=
  globalKaehlerMap (affineDifferentialSheaf A) (affineUniversalDifferential A)

def affineCoordinate (l : KaehlerDifferential ℂ A →ₗ[A] A) :
    (affineDifferentialModule A) ⟶
      structureModule (Spec (CommRingCat.of A)) :=
  coefficientSheafMap (regularSectionDerivation l)

private def functionalSection (l : KaehlerDifferential ℂ A →ₗ[A] A) :
    KaehlerDifferential ℂ A →ₗ[A] (affineStructureModule A).val.obj (op ⊤) where
  toFun ω := algebraMap A (AffineSections A ⊤) (l ω)
  map_add' ω η := by
    change algebraMap A (AffineSections A ⊤) (l (ω + η)) = _
    rw [map_add, map_add]
  map_smul' a ω := by
    change algebraMap A (AffineSections A ⊤) (l (a • ω)) =
      algebraMap A (AffineSections A ⊤) a * algebraMap A (AffineSections A ⊤) (l ω)
    rw [map_smul, smul_eq_mul, map_mul]

/-- The coefficient map evaluates the original Kähler functional, not a
chosen coordinate functional on a replacement module. -/
theorem affineCoordinate_original (l : KaehlerDifferential ℂ A →ₗ[A] A)
    (ω : KaehlerDifferential ℂ A) :
    (affineCoordinate l).app ⊤ (affineDifferentialSection ω) =
      algebraMap A (AffineSections A ⊤) (l ω) := by
  have h : (globalModuleMap (affineCoordinate l)).comp affineDifferentialSection =
      functionalSection l := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change (coefficientSheafMap (regularSectionDerivation l)).val.app (op ⊤)
      (globalKaehlerMap (affineDifferentialSheaf A) (affineUniversalDifferential A)
        (KaehlerDifferential.D ℂ A a)) =
      algebraMap A (AffineSections A ⊤) (l (KaehlerDifferential.D ℂ A a))
    rw [globalKaehlerMap_D, coefficientSheafMap_D]
    exact sectionDerivative_algebraMap l ⊤ a
  exact LinearMap.congr_fun h ω

def affineVector (b : Basis (Fin 2) A (KaehlerDifferential ℂ A)) (i : Fin 2) :
    structureModule (Spec (CommRingCat.of A)) ⟶
      (affineDifferentialModule A) :=
  unitMapFromGlobal (affineDifferentialSheaf A) (affineDifferentialSection (b i))

private theorem affineVector_coordinate
    (b : Basis (Fin 2) A (KaehlerDifferential ℂ A)) (i j : Fin 2) :
    affineVector b i ≫ affineCoordinate (b.coord j) =
      if j = i then 𝟙 (structureModule (Spec (CommRingCat.of A))) else 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro a
  change (affineCoordinate (b.coord j)).val.app (op U)
    ((unitMapFromGlobal (affineDifferentialSheaf A)
      (affineDifferentialSection (b i))).val.app (op U) a) = _
  rw [unitMapFromGlobal_apply, map_smul]
  have hres := PresheafOfModules.naturality_apply
    (coefficientSheafMap (regularSectionDerivation (b.coord j))).val
    U.leTop.op (affineDifferentialSection (b i))
  have hc := affineCoordinate_original (b.coord j) (b i)
  change (affineCoordinate (b.coord j)).val.app (op ⊤)
    (affineDifferentialSection (b i)) = _ at hc
  by_cases hji : j = i
  · subst j
    have ht : (affineCoordinate (b.coord i)).val.app (op ⊤)
        (affineDifferentialSection (b i)) = (1 : AffineSections A ⊤) :=
      hc.trans (by simp only [Basis.coord_apply, Basis.repr_self,
        Finsupp.single_eq_same, map_one])
    have hu := hres.trans ((congrArg ((Spec.structureSheaf A).obj.map U.leTop.op) ht).trans
      (map_one _))
    rw [if_pos rfl]
    exact (congrArg (fun z : AffineSections A U =>
      (show AffineSections A U from a) * z) hu).trans
        (mul_one (show AffineSections A U from a))
  · have ht : (affineCoordinate (b.coord j)).val.app (op ⊤)
        (affineDifferentialSection (b i)) = (0 : AffineSections A ⊤) :=
      hc.trans (by simp only [Basis.coord_apply, Basis.repr_self,
        Finsupp.single_eq_of_ne hji, map_zero])
    have hu := hres.trans ((congrArg ((Spec.structureSheaf A).obj.map U.leTop.op) ht).trans
      (map_zero _))
    rw [if_neg hji]
    exact (congrArg (fun z : AffineSections A U =>
      (show AffineSections A U from a) * z) hu).trans
        (mul_zero (show AffineSections A U from a))

private theorem affineReconstruction
    (b : Basis (Fin 2) A (KaehlerDifferential ℂ A)) :
    affineCoordinate (b.coord 0) ≫ affineVector b 0 +
      affineCoordinate (b.coord 1) ≫ affineVector b 1 =
        𝟙 (affineDifferentialModule A) := by
  apply differentialLift_unique (Spec.structureSheaf A) (affineCoefficient A)
  apply affineDerivation_ext
  intro a
  change (unitMapFromGlobal (affineDifferentialSheaf A)
      (affineDifferentialSection (b 0))).val.app (op ⊤)
      ((coefficientSheafMap (regularSectionDerivation (b.coord 0))).val.app (op ⊤)
        ((affineUniversalDifferential A).d (algebraMap A (AffineSections A ⊤) a))) +
    (unitMapFromGlobal (affineDifferentialSheaf A)
      (affineDifferentialSection (b 1))).val.app (op ⊤)
      ((coefficientSheafMap (regularSectionDerivation (b.coord 1))).val.app (op ⊤)
        ((affineUniversalDifferential A).d (algebraMap A (AffineSections A ⊤) a))) =
    (affineUniversalDifferential A).d (algebraMap A (AffineSections A ⊤) a)
  rw [coefficientSheafMap_D, coefficientSheafMap_D]
  change (unitMapFromGlobal (affineDifferentialSheaf A)
      (affineDifferentialSection (b 0))).val.app (op ⊤)
      (sectionDerivative (b.coord 0) ⊤ (algebraMap A (AffineSections A ⊤) a)) +
    (unitMapFromGlobal (affineDifferentialSheaf A)
      (affineDifferentialSection (b 1))).val.app (op ⊤)
      (sectionDerivative (b.coord 1) ⊤ (algebraMap A (AffineSections A ⊤) a)) = _
  rw [CycleQ2GeometricFunctionalDifferentials.sectionDerivative_algebraMap,
    CycleQ2GeometricFunctionalDifferentials.sectionDerivative_algebraMap,
    unitMapFromGlobal_top, unitMapFromGlobal_top]
  change b.coord 0 (KaehlerDifferential.D ℂ A a) • affineDifferentialSection (b 0) +
    b.coord 1 (KaehlerDifferential.D ℂ A a) • affineDifferentialSection (b 1) = _
  rw [← (affineDifferentialSection (A := A)).map_smul,
    ← (affineDifferentialSection (A := A)).map_smul,
    ← (affineDifferentialSection (A := A)).map_add]
  have hb : b.coord 0 (KaehlerDifferential.D ℂ A a) • b 0 +
      b.coord 1 (KaehlerDifferential.D ℂ A a) • b 1 = KaehlerDifferential.D ℂ A a := by
    simpa only [Basis.coord_apply, Fin.sum_univ_two] using
      b.sum_repr (KaehlerDifferential.D ℂ A a)
  rw [hb]
  exact globalKaehlerMap_D (affineDifferentialSheaf A) (affineUniversalDifferential A) a

/-- A rank-two basis of the actual affine Kähler module gives a genuine
frame of its sheaf on all opens of the affine scheme. -/
def affineFrame (b : Basis (Fin 2) A (KaehlerDifferential ℂ A)) :
    TwoFrame (affineDifferentialModule A) where
  coordinate i := affineCoordinate (b.coord i)
  vector i := affineVector b i
  vector_coordinate := affineVector_coordinate b
  reconstruction := affineReconstruction b

end AffineFrame

section AffinePullback

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra A B]
  (b : Basis (Fin 2) A (KaehlerDifferential ℂ A))

abbrev affineMap : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

abbrev affinePullbackModule : (Spec (CommRingCat.of B)).Modules :=
  (Scheme.Modules.pullback (affineMap (A := A) (B := B))).obj
    (affineDifferentialModule A)

abbrev retainedSurfaceModule (V : (Spec (CommRingCat.of B)).Opens) :=
  Γ(Spec (CommRingCat.of B),V) ⊗[B] (B ⊗[A] KaehlerDifferential ℂ A)

def retainedBasis (V : (Spec (CommRingCat.of B)).Opens) :
    Basis (Fin 2) Γ(Spec (CommRingCat.of B),V) (retainedSurfaceModule (A := A) V) :=
  (b.baseChange B).baseChange Γ(Spec (CommRingCat.of B),V)

/-- On every curve-chart open, actual sections of the genuine pullback
surface differential sheaf are the retained surface tensor module. -/
def pullbackSectionsEquiv (V : (Spec (CommRingCat.of B)).Opens) :
    Γ(affinePullbackModule (A := A) (B := B),V) ≃ₗ[Γ(Spec (CommRingCat.of B),V)]
      retainedSurfaceModule (A := A) V :=
  ((affineFrame b).pullback (affineMap (A := A) (B := B))).sectionEquiv V |>.trans
    (retainedBasis b V).equivFun.symm

/-- The original differential is carried through the actual adjunction
unit and the actual restriction to this open. -/
def pullbackOriginalSection (V : (Spec (CommRingCat.of B)).Opens)
    (ω : KaehlerDifferential ℂ A) : Γ(affinePullbackModule (A := A) (B := B),V) :=
  (affinePullbackModule (A := A) (B := B)).presheaf.map V.leTop.op
    (((Scheme.Modules.pullbackPushforwardAdjunction (affineMap (A := A) (B := B))).unit.app
      (affineDifferentialModule A)).app ⊤
        (affineDifferentialSection ω))

omit [Algebra ℂ A] in
private theorem affineMap_original (a : A) :
    (affineMap (A := A) (B := B)).app ⊤ (algebraMap A (AffineSections A ⊤) a) =
      algebraMap B (AffineSections B ⊤) (algebraMap A B a) := by
  exact ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))).symm a

private theorem pullbackOriginal_coordinate
    (V : (Spec (CommRingCat.of B)).Opens) (ω : KaehlerDifferential ℂ A) (i : Fin 2) :
    ((affineFrame b).pullback (affineMap (A := A) (B := B))).sectionEquiv V
      (pullbackOriginalSection V ω) i =
      algebraMap B Γ(Spec (CommRingCat.of B),V) (algebraMap A B (b.coord i ω)) := by
  rw [pullbackOriginalSection, TwoFrame.sectionEquiv_restrict]
  have hu := pullback_coordinate_unit (affineMap (A := A) (B := B))
    (affineFrame b) ⊤ (affineDifferentialSection ω) i
  have ht := hu.trans ((congrArg ((affineMap (A := A) (B := B)).app ⊤)
    (affineCoordinate_original (b.coord i) ω)).trans
      (affineMap_original (B := B) (b.coord i ω)))
  exact congrArg ((Spec (CommRingCat.of B)).presheaf.map V.leTop.op) ht

/-- The comparison preserves every original surface differential. -/
theorem pullbackSectionsEquiv_original
    (V : (Spec (CommRingCat.of B)).Opens) (ω : KaehlerDifferential ℂ A) :
    pullbackSectionsEquiv b V (pullbackOriginalSection V ω) =
      (1 : Γ(Spec (CommRingCat.of B),V)) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] ω) := by
  apply (retainedBasis b V).equivFun.injective
  rw [pullbackSectionsEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  funext i
  rw [pullbackOriginal_coordinate]
  simp only [retainedBasis, Basis.equivFun_apply, Basis.baseChange_repr_tmul,
    Algebra.smul_def, mul_one, Basis.coord_apply]

/-- In particular, the actual unit images of the two original basis
vectors give the tensor basis on every curve open. -/
theorem pullbackSectionsEquiv_basis (V : (Spec (CommRingCat.of B)).Opens) (i : Fin 2) :
    pullbackSectionsEquiv b V (pullbackOriginalSection V (b i)) = retainedBasis b V i := by
  rw [pullbackSectionsEquiv_original]
  simp only [retainedBasis, Basis.baseChange_apply]

end AffinePullback

section Restriction

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra A B]
  (b : Basis (Fin 2) A (KaehlerDifferential ℂ A))
  {U V : (Spec (CommRingCat.of B)).Opens}

def affineSectionRestriction (a : V ⟶ U) :
    Γ(Spec (CommRingCat.of B),U) →ₗ[B] Γ(Spec (CommRingCat.of B),V) where
  toFun := (Spec (CommRingCat.of B)).presheaf.map a.op
  map_add' := map_add _
  map_smul' _ _ := rfl

/-- The tensor restriction changes only the actual section coefficient;
its original restricted surface differential factor remains unchanged. -/
def retainedRestriction (a : V ⟶ U) :
    retainedSurfaceModule (A := A) U →ₗ[B] retainedSurfaceModule (A := A) V :=
  TensorProduct.map (affineSectionRestriction a)
    (LinearMap.id (R := B) (M := B ⊗[A] KaehlerDifferential ℂ A))

@[simp] theorem retainedRestriction_tmul (a : V ⟶ U)
    (s : Γ(Spec (CommRingCat.of B),U)) (ω : B ⊗[A] KaehlerDifferential ℂ A) :
    retainedRestriction a (s ⊗ₜ[B] ω) =
      (Spec (CommRingCat.of B)).presheaf.map a.op s ⊗ₜ[B] ω := rfl

theorem retainedRestriction_smul (a : V ⟶ U)
    (s : Γ(Spec (CommRingCat.of B),U)) (ω : retainedSurfaceModule (A := A) U) :
    retainedRestriction a (s • ω) =
      (Spec (CommRingCat.of B)).presheaf.map a.op s • retainedRestriction a ω := by
  induction ω using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul c m =>
      simp only [TensorProduct.smul_tmul', retainedRestriction_tmul, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

@[simp] theorem retainedRestriction_basis (a : V ⟶ U) (i : Fin 2) :
    retainedRestriction a (retainedBasis b U i) = retainedBasis b V i := by
  simp only [retainedBasis, Basis.baseChange_apply, retainedRestriction_tmul, map_one]

/-- The comparison is natural for every inclusion of curve-chart opens. -/
theorem pullbackSectionsEquiv_restrict (a : V ⟶ U)
    (ω : Γ(affinePullbackModule (A := A) (B := B),U)) :
    pullbackSectionsEquiv b V
        ((affinePullbackModule (A := A) (B := B)).presheaf.map a.op ω) =
      retainedRestriction a (pullbackSectionsEquiv b U ω) := by
  simp only [pullbackSectionsEquiv, LinearEquiv.trans_apply,
    Basis.equivFun_symm_apply, Fin.sum_univ_two, map_add,
    retainedRestriction_smul, retainedRestriction_basis,
    TwoFrame.sectionEquiv_restrict]

end Restriction

section NormalSurface

open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineCurveCharts

variable (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3)

/-- The all-open comparison for the actual normal surface chart and its
actual curve quotient, with no freeness or comparison hypothesis. -/
def normalPullbackSectionsEquiv
    (V : (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).Opens) :
    Γ(affinePullbackModule (A := NormalSurfacePatch q h g₁ g₂ k i j)
      (B := NormalCurvePatch q h g₁ g₂ k i j),V) ≃ₗ[
      Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)),V)]
      Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)),V) ⊗[
        NormalCurvePatch q h g₁ g₂ k i j] (RestrictedSurfaceDifferentials q h g₁ g₂ k i j) :=
  pullbackSectionsEquiv (localSurfaceKaehlerBasis
    ![surfaceEquation q h g₁ g₂ k,includeCurve h]
    (normalPolynomial q i) (includeCurve (MvPolynomial.X j))) V

/-- Every original surface differential has its literal double-tensor
image, including the actual normal and tangent equation differentials. -/
theorem normalPullbackSectionsEquiv_original
    (V : (Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j))).Opens)
    (ω : KaehlerDifferential ℂ (NormalSurfacePatch q h g₁ g₂ k i j)) :
    normalPullbackSectionsEquiv q h g₁ g₂ k i j V (pullbackOriginalSection V ω) =
      (1 : Γ(Spec (CommRingCat.of (NormalCurvePatch q h g₁ g₂ k i j)),V)) ⊗ₜ[
        NormalCurvePatch q h g₁ g₂ k i j]
        ((1 : NormalCurvePatch q h g₁ g₂ k i j) ⊗ₜ[NormalSurfacePatch q h g₁ g₂ k i j] ω) :=
  pullbackSectionsEquiv_original _ V ω

end NormalSurface

end CycleQ2SurfacePullbackFrame
end

end


section

/-! Compatible genuine local frames glue over an arbitrary indexed open
cover. Both maps and their inverse identities come from actual sheaf
unique gluing. Agreement of the inverse-one generators on the pairwise
intersections is sufficient; no global generator is assumed. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LocalFrameGluing

open CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricModuleLocalIso
open CycleQ2GeometricSheafLocalIso (res res_comp)
open CycleQ2GeometricCanonicalGluing

namespace Cover

variable {X : TopCat.{0}} {R : X.Sheaf RingCat.{0}} {ι : Type}
  (M N : SheafOfModules.{0} R) (U : Opens X) (V : ι → Opens X)
  (hcover : U ≤ ⨆ i, V i)
  (e : ∀ i, PatchIso M N (V i))
  (hc : ∀ i j, (e i).Compatible (e j))

private theorem restrict_app {W O P : Opens X} (f : PatchIso M N W)
    (hPO : P ≤ O) (hO : O ≤ W) (s : M.val.obj (op O)) :
    res (addSheaf N) hPO (f.app O hO s) =
      f.app P (hPO.trans hO) (res (addSheaf M) hPO s) :=
  f.naturality hPO hO s

include hcover in
private theorem cover_on (O : Opens X) (hO : O ≤ U) :
    O ≤ ⨆ i, O ⊓ V i := by
  rw [← inf_iSup_eq]
  exact le_inf le_rfl (hO.trans hcover)

include hc in
private theorem image_compatible (O : Opens X) (s : M.val.obj (op O))
    (i j : ι) (P : Opens X) (hPi : P ≤ O ⊓ V i) (hPj : P ≤ O ⊓ V j) :
    res (addSheaf N) hPi ((e i).app (O ⊓ V i) inf_le_right
      (res (addSheaf M) inf_le_left s)) =
    res (addSheaf N) hPj ((e j).app (O ⊓ V j) inf_le_right
      (res (addSheaf M) inf_le_left s)) := by
  rw [restrict_app, restrict_app, res_comp, res_comp]
  exact hc i j P _ _ _

include hcover hc in
private theorem image_exists (O : Opens X) (hO : O ≤ U) (s : M.val.obj (op O)) :
    ∃! t : N.val.obj (op O), ∀ i,
      res (addSheaf N) (show O ⊓ V i ≤ O from inf_le_left) t =
        (e i).app (O ⊓ V i) inf_le_right (res (addSheaf M) inf_le_left s) := by
  apply (addSheaf N).existsUnique_gluing' (fun i => O ⊓ V i) O
    (fun _ => homOfLE inf_le_left) (cover_on U V hcover O hO)
    (fun i => (e i).app (O ⊓ V i) inf_le_right (res (addSheaf M) inf_le_left s))
  intro i j
  exact image_compatible M N V e hc O s i j _ inf_le_left inf_le_right

def mapSection (O : Opens X) (hO : O ≤ U) (s : M.val.obj (op O)) : N.val.obj (op O) :=
  Classical.choose (image_exists M N U V hcover e hc O hO s)

theorem mapSection_restrict (O : Opens X) (hO : O ≤ U)
    (s : M.val.obj (op O)) (i : ι) :
    res (addSheaf N) (show O ⊓ V i ≤ O from inf_le_left)
        (mapSection M N U V hcover e hc O hO s) =
      (e i).app (O ⊓ V i) inf_le_right (res (addSheaf M) inf_le_left s) :=
  (Classical.choose_spec (image_exists M N U V hcover e hc O hO s)).1 i

include hcover in
private theorem local_ext (F : CycleQ2GeometricSheafLocalIso.AddSheaf X)
    (O : Opens X) (hO : O ≤ U) (s t : F.obj.obj (op O))
    (h : ∀ i, res F (show O ⊓ V i ≤ O from inf_le_left) s = res F inf_le_left t) : s = t :=
  F.eq_of_locally_eq' (fun i => O ⊓ V i) O (fun _ => homOfLE inf_le_left)
    (cover_on U V hcover O hO) s t h

theorem mapSection_of_le (O : Opens X) (hO : O ≤ U) (i : ι) (hOi : O ≤ V i)
    (s : M.val.obj (op O)) :
    mapSection M N U V hcover e hc O hO s = (e i).app O hOi s := by
  apply local_ext U V hcover (addSheaf N) O hO
  intro j
  rw [mapSection_restrict, restrict_app]
  exact hc j i _ inf_le_right (inf_le_left.trans hOi) _

theorem mapSection_restrict_patch {O P : Opens X} (hO : O ≤ U)
    (hPO : P ≤ O) (i : ι) (hPi : P ≤ V i) (s : M.val.obj (op O)) :
    res (addSheaf N) hPO (mapSection M N U V hcover e hc O hO s) =
      (e i).app P hPi (res (addSheaf M) hPO s) := by
  calc
    _ = res (addSheaf N) (le_inf hPO hPi)
        (res (addSheaf N) (show O ⊓ V i ≤ O from inf_le_left)
          (mapSection M N U V hcover e hc O hO s)) := by rw [res_comp]
    _ = _ := by
      rw [mapSection_restrict, restrict_app, res_comp]

theorem mapSection_naturality {O P : Opens X} (hPO : P ≤ O) (hO : O ≤ U)
    (s : M.val.obj (op O)) :
    res (addSheaf N) hPO (mapSection M N U V hcover e hc O hO s) =
      mapSection M N U V hcover e hc P (hPO.trans hO) (res (addSheaf M) hPO s) := by
  apply local_ext U V hcover (addSheaf N) P (hPO.trans hO)
  intro i
  rw [res_comp, mapSection_restrict_patch M N U V hcover e hc hO
    (inf_le_left.trans hPO) i inf_le_right, mapSection_restrict, res_comp]

theorem mapSection_add (O : Opens X) (hO : O ≤ U) (s t : M.val.obj (op O)) :
    mapSection M N U V hcover e hc O hO (s + t) =
      mapSection M N U V hcover e hc O hO s + mapSection M N U V hcover e hc O hO t := by
  apply local_ext U V hcover (addSheaf N) O hO
  intro i
  simp only [mapSection_restrict, map_add]

theorem mapSection_smul (O : Opens X) (hO : O ≤ U)
    (a : R.obj.obj (op O)) (s : M.val.obj (op O)) :
    mapSection M N U V hcover e hc O hO (a • s) =
      a • mapSection M N U V hcover e hc O hO s := by
  apply local_ext U V hcover (addSheaf N) O hO
  intro i
  rw [mapSection_restrict, res_smul, res_smul, mapSection_restrict]
  exact ((e i).app (O ⊓ V i) inf_le_right).map_smul _ _

theorem inverse_apply (O : Opens X) (hO : O ≤ U) (s : M.val.obj (op O)) :
    mapSection N M U V hcover (fun i => (e i).symm) (fun i j => (hc i j).symm) O hO
      (mapSection M N U V hcover e hc O hO s) = s := by
  apply local_ext U V hcover (addSheaf M) O hO
  intro i
  rw [mapSection_restrict, mapSection_restrict]
  exact ((e i).app (O ⊓ V i) inf_le_right).symm_apply_apply _

theorem apply_inverse (O : Opens X) (hO : O ≤ U) (s : N.val.obj (op O)) :
    mapSection M N U V hcover e hc O hO
      (mapSection N M U V hcover (fun i => (e i).symm) (fun i j => (hc i j).symm) O hO s) = s := by
  apply local_ext U V hcover (addSheaf N) O hO
  intro i
  rw [mapSection_restrict, mapSection_restrict]
  exact ((e i).app (O ⊓ V i) inf_le_right).apply_symm_apply _

/-- The local inverse maps glue as well, yielding a genuine natural
linear equivalence on every subopen of the covered open. -/
def gluePatchIso : PatchIso M N U where
  app O hO :=
    { toFun := mapSection M N U V hcover e hc O hO
      invFun := mapSection N M U V hcover (fun i => (e i).symm)
        (fun i j => (hc i j).symm) O hO
      left_inv := inverse_apply M N U V hcover e hc O hO
      right_inv := apply_inverse M N U V hcover e hc O hO
      map_add' := mapSection_add M N U V hcover e hc O hO
      map_smul' := mapSection_smul M N U V hcover e hc O hO }
  naturality hPO hO s := mapSection_naturality M N U V hcover e hc hPO hO s

end Cover

section Frames

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (M : SheafOfModules.{0} (CycleQ2GeometricProjectiveCurve.TwistedModule.ringSheaf R))
  (U : Opens X) {ι : Type} (V : ι → Opens X)
  (hVU : ∀ i, V i ≤ U) (hcover : U ≤ ⨆ i, V i)
  (e : ∀ i, LocalFrame R M (V i))
  (hcompat : ∀ i j,
    frameGenerator (e i) (V i ⊓ V j) inf_le_left =
      frameGenerator (e j) (V i ⊓ V j) inf_le_right)

include hcompat in
theorem generator_agreement (i j : ι) (O : Opens X) (hOi : O ≤ V i) (hOj : O ≤ V j) :
    frameGenerator (e i) O hOi = frameGenerator (e j) O hOj := by
  have h := congrArg (M.val.map (homOfLE (le_inf hOi hOj)).op) (hcompat i j)
  rw [frameGenerator_naturality, frameGenerator_naturality] at h
  exact h

include hcompat in
theorem frames_compatible (i j : ι) : (e i).Compatible (e j) := by
  intro O hOi hOj s
  have hg := generator_agreement R M V e hcompat i j O hOi hOj
  have h : ((e j).app O hOj).symm (1 : R.obj.obj (op O)) =
      (1 : R.obj.obj (op O)) • ((e i).app O hOi).symm (1 : R.obj.obj (op O)) :=
    hg.symm.trans (one_smul _ _).symm
  exact (coordinates_of_generator_relation
    (A := R.obj.obj (op O)) ((e i).app O hOi) ((e j).app O hOj) 1 h s).trans (one_mul _)

/-- Compatible actual frames over an indexed open cover glue without a
global freeness assumption. The inverse is glued from the actual local inverses. -/
def glueLocalFrames : LocalFrame R M U :=
  Cover.gluePatchIso M (SheafOfModules.unit
    (CycleQ2GeometricProjectiveCurve.TwistedModule.ringSheaf R)) U V
    (show U ≤ ⨆ i, V i from (le_antisymm hcover (iSup_le hVU)).le) e
    (frames_compatible R M V e hcompat)

/-- Every local coordinate is exactly preserved on every subopen of its patch. -/
theorem glueLocalFrames_app (i : ι) (O : Opens X) (hOi : O ≤ V i)
    (s : M.val.obj (op O)) :
    (glueLocalFrames R M U V hVU hcover e hcompat).app O (hOi.trans (hVU i)) s =
      (e i).app O hOi s :=
  Cover.mapSection_of_le M (SheafOfModules.unit
    (CycleQ2GeometricProjectiveCurve.TwistedModule.ringSheaf R)) U V hcover e
    (frames_compatible R M V e hcompat) O (hOi.trans (hVU i)) i hOi s

/-- The whole inverse coordinate map, and not just its generator, is preserved. -/
theorem glueLocalFrames_symm_app (i : ι) (O : Opens X) (hOi : O ≤ V i)
    (a : R.obj.obj (op O)) :
    ((glueLocalFrames R M U V hVU hcover e hcompat).app O
      (hOi.trans (hVU i))).symm a = ((e i).app O hOi).symm a := by
  apply ((e i).app O hOi).injective
  rw [← glueLocalFrames_app R M U V hVU hcover e hcompat i O hOi,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The glued inverse-one generator is the specified generator on every patch subopen. -/
theorem glueLocalFrames_generator (i : ι) (O : Opens X) (hOi : O ≤ V i) :
    frameGenerator (glueLocalFrames R M U V hVU hcover e hcompat) O (hOi.trans (hVU i)) =
      frameGenerator (e i) O hOi :=
  glueLocalFrames_symm_app R M U V hVU hcover e hcompat i O hOi 1

end Frames

end CycleQ2LocalFrameGluing
end

end


section

/-! The original normal-frame classes as genuine surface cohomology
classes of their actual closed direct image. The selected cubic detection
and all seven vanishing tests survive the closed immersion. Identification
with the intrinsic normal sheaf is a separate proved-sheaf-isomorphism step. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2SurfaceNormalCohomology

open CategoryTheory TopologicalSpace Topology Opposite AlgebraicGeometry
  CycleQ2ClosedSupportCohomology CycleQ2ClosedSupportBoundary
  CycleQ2ProjectiveCurveSurface CycleQ2ProjectiveClosedImmersion
  CycleQ2CartierProjectiveCover CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricProjectiveNormalClass CycleQ2GeometricLiteralCanonicalClass
  CycleQ2GeometricLiteralDirection CycleQ2SeedTrace

theorem curveClosedEmbedding (r θ : ℂ) : IsClosedEmbedding (curveToSurface r θ).base := by
  let := curveToSurface_isClosedImmersion r θ
  exact (curveToSurface r θ).isClosedEmbedding

abbrev pushedNormalSheaf (r θ : ℂ) :=
  directImage (curveToSurface r θ).base (normalAdditiveSheaf r θ)

abbrev pushedDegreeOneSheaf (r θ : ℂ) :=
  directImage (curveToSurface r θ).base (degreeOneSheaf r θ)

local instance curveHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve r θ)) AddCommGrpCat.{0}) :=
  HasExt.standard _

local instance surfaceHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveSurface r θ)) AddCommGrpCat.{0}) :=
  HasExt.standard _

abbrev NormalH1OnSurface (r θ : ℂ) := (pushedNormalSheaf r θ).H' 1 ⊤

def normalClassOnSurface (r θ : ℂ) (hr : r ≠ 0) (p : Poly) (hp : p.IsHomogeneous 6) :
    NormalH1OnSurface r θ :=
  pushforwardBoundary (curveToSurface r θ).base (curveClosedEmbedding r θ)
    (normalAdditiveSheaf r θ) (firstProjectivePatch r θ) (secondProjectivePatch r θ)
    (overlapProjectivePatch r θ) (overlapProjectivePatch_eq r θ)
    (projective_twoOpen_cover r θ hr) (normalOverlapSection r θ p hp)

theorem normalClassOnSurface_zero_iff (r θ : ℂ) (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 6) :
    normalClassOnSurface r θ hr p hp = 0 ↔ normalClass r θ hr p hp = 0 :=
  pushforwardBoundary_zero_iff (curveToSurface r θ).base (curveClosedEmbedding r θ)
    (normalAdditiveSheaf r θ) (firstProjectivePatch r θ) (secondProjectivePatch r θ)
    (overlapProjectivePatch r θ) (overlapProjectivePatch_eq r θ)
    (projective_twoOpen_cover r θ hr) (normalOverlapSection r θ p hp)

def cubicH1OnSurface (r θ : ℂ) (hr : r ≠ 0) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    NormalH1OnSurface r θ →+ (pushedDegreeOneSheaf r θ).H' 1 ⊤ :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology (projectiveSurface r θ)) 1).map
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} (curveToSurface r θ).base).map
      (cubicAdditiveMorphism r θ hr σ hσ))).app (op ⊤)).hom

theorem cubicH1OnSurface_normalClass_zero_iff (r θ : ℂ) (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 6) (σ : Poly) (hσ : σ.IsHomogeneous 3) :
    cubicH1OnSurface r θ hr σ hσ (normalClassOnSurface r θ hr p hp) = 0 ↔
      cubicH1Map r θ hr σ hσ (normalClass r θ hr p hp) = 0 :=
  pushforwardBoundary_map_zero_iff (curveToSurface r θ).base (curveClosedEmbedding r θ)
    (cubicAdditiveMorphism r θ hr σ hσ)
    (firstProjectivePatch r θ) (secondProjectivePatch r θ)
    (overlapProjectivePatch r θ) (overlapProjectivePatch_eq r θ)
    (projective_twoOpen_cover r θ hr) (normalOverlapSection r θ p hp)

def literalNormalClassOnSurface : NormalH1OnSurface 57 1 :=
  normalClassOnSurface 57 1 (by norm_num) ambientNormalNumerator ambientNormalNumerator_homogeneous

theorem literalNormalClassOnSurface_ne_zero : literalNormalClassOnSurface ≠ 0 := by
  intro hz
  apply literalNormalClass_ne_zero
  exact (normalClassOnSurface_zero_iff 57 1 (by norm_num)
    ambientNormalNumerator ambientNormalNumerator_homogeneous).mp hz

theorem literal_selected_cubic_image_ne_zero :
    cubicH1OnSurface 57 1 (by norm_num) selectedCubic selectedCubic_homogeneous
      literalNormalClassOnSurface ≠ 0 := by
  intro hz
  have hcurve := (cubicH1OnSurface_normalClass_zero_iff 57 1 (by norm_num)
    ambientNormalNumerator ambientNormalNumerator_homogeneous
    selectedCubic selectedCubic_homogeneous).mp hz
  apply selectedAmbientClass_ne_zero
  rw [← selectedCubicPairing_literalNormalClass]
  change literalCanonicalH1Equiv
    (cubicH1Map 57 1 (by norm_num) selectedCubic selectedCubic_homogeneous
      (normalClass 57 1 (by norm_num) ambientNormalNumerator ambientNormalNumerator_homogeneous)) = 0
  rw [hcurve, map_zero]

def selectedIncidenceNormalClassOnSurface : NormalH1OnSurface 57 1 :=
  normalClassOnSurface 57 1 (by norm_num) incidenceNormalNumerator incidenceNormalNumerator_homogeneous

theorem selectedIncidenceNormalClassOnSurface_in_seven_kernels (j : Fin 7) :
    cubicH1OnSurface 57 1 (by norm_num) (testCubic j) (testCubic_homogeneous j)
      selectedIncidenceNormalClassOnSurface = 0 := by
  apply (cubicH1OnSurface_normalClass_zero_iff 57 1 (by norm_num)
    incidenceNormalNumerator incidenceNormalNumerator_homogeneous
    (testCubic j) (testCubic_homogeneous j)).mpr
  apply literalCanonicalH1Equiv.injective
  have hz := selectedIncidenceNormalClass_in_seven_kernels j
  change literalCanonicalH1Equiv
    (cubicH1Map 57 1 (by norm_num) (testCubic j) (testCubic_homogeneous j)
      (normalClass 57 1 (by norm_num) incidenceNormalNumerator
        incidenceNormalNumerator_homogeneous)) = 0 at hz
  exact hz.trans (map_zero literalCanonicalH1Equiv).symm

end CycleQ2SurfaceNormalCohomology
end

end


section

/-!
# Transporting an actual module frame through an open immersion

The coordinate map uses the original restriction comparison of a scheme
module and the original structure-sheaf isomorphism of the open immersion.
Its scalar action and naturality are inherited from those actual maps.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2OpenImmersionFrame

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricCanonicalGluing

variable {X' X : Scheme.{0}} (u : X' ⟶ X) [IsOpenImmersion u]
  (M : X.Modules)
  (e : M.restrict u ≅ SheafOfModules.unit X'.ringCatSheaf)

def imageCoordinate (W : X'.Opens) : Γ(M, u ''ᵁ W) →ₗ[Γ(X, u ''ᵁ W)] Γ(X, u ''ᵁ W) where
  toFun x := (u.appIso W).inv (e.hom.app W ((M.restrictAppIso u W).inv x))
  map_add' x y := by
    simp only [map_add]
    exact (u.appIso W).inv.hom.map_add _ _
  map_smul' r x := by
    have hs := ConcreteCategory.congr_hom (Scheme.Modules.smul_restrictAppIso_inv u M W r) x
    have he := (congrArg (e.hom.app W) hs).trans
      (e.hom.app_smul ((u.appIso W).hom r) ((M.restrictAppIso u W).inv x))
    have he' : (show Γ(X', W) from e.hom.app W ((M.restrictAppIso u W).inv (r • x))) =
        (u.appIso W).hom r *
          (show Γ(X', W) from e.hom.app W ((M.restrictAppIso u W).inv x)) := he
    have ht := congrArg ((u.appIso W).inv) he'
    let b : Γ(X', W) := e.hom.app W ((M.restrictAppIso u W).inv x)
    have hi : (u.appIso W).inv ((u.appIso W).hom r) = r :=
      ConcreteCategory.congr_hom (u.appIso W).hom_inv_id r
    exact ht.trans (((u.appIso W).inv.hom.map_mul ((u.appIso W).hom r) b).trans
      (congrArg (fun a : Γ(X, u ''ᵁ W) => a * (u.appIso W).inv b) hi))

theorem imageCoordinate_bijective (W : X'.Opens) :
    Function.Bijective (imageCoordinate u M e W) := by
  have he : Function.Bijective (e.hom.app W) :=
    ConcreteCategory.bijective_of_isIso (((Scheme.Modules.toPresheaf X').mapIso e).app (op W)).hom
  exact (ConcreteCategory.bijective_of_isIso (u.appIso W).inv).comp
    (he.comp
      (ConcreteCategory.bijective_of_isIso (M.restrictAppIso u W).inv))

def imageFrameEquiv (W : X'.Opens) :
    Γ(M, u ''ᵁ W) ≃ₗ[Γ(X, u ''ᵁ W)] Γ(X, u ''ᵁ W) :=
  LinearEquiv.ofBijective (imageCoordinate u M e W) (imageCoordinate_bijective u M e W)

theorem imageFrameEquiv_apply (W : X'.Opens) (x : Γ(M, u ''ᵁ W)) :
    imageFrameEquiv u M e W x =
      (u.appIso W).inv (e.hom.app W ((M.restrictAppIso u W).inv x)) := rfl

theorem imageFrameEquiv_naturality {V W : X'.Opens} (h : V ⟶ W)
    (x : Γ(M, u ''ᵁ W)) :
    X.presheaf.map (homOfLE (u.image_mono (leOfHom h))).op (imageFrameEquiv u M e W x) =
      imageFrameEquiv u M e V
        (M.presheaf.map (homOfLE (u.image_mono (leOfHom h))).op x) := by
  let y := (M.restrictAppIso u W).inv x
  have hr := ConcreteCategory.congr_hom (u.appIso_inv_naturality h.op) (e.hom.app W y)
  have he := ConcreteCategory.congr_hom (e.hom.mapPresheaf.naturality h.op) y
  have hm := ConcreteCategory.congr_hom (Scheme.Modules.restrictAppIso_inv_map u M h.op) x
  exact hr.symm.trans (congrArg ((u.appIso V).inv)
    (he.symm.trans (congrArg (e.hom.app V) hm)))

theorem image_preimage (V : X.Opens) (hV : V ≤ u.opensRange) :
    u ''ᵁ (u ⁻¹ᵁ V) = V := by
  rw [u.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]

def frameEquiv (V : X.Opens) (hV : V ≤ u.opensRange) :
    Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  image_preimage u V hV ▸ imageFrameEquiv u M e (u ⁻¹ᵁ V)

private theorem dependent_heq {I : Type*} {P : I → Type*}
    (f : (i : I) → P i) {i j : I} (h : i = j) : HEq (f i) (f j) := by
  cases h
  rfl

theorem frameEquiv_image (W : X'.Opens) (hW : u ''ᵁ W ≤ u.opensRange) :
    frameEquiv u M e (u ''ᵁ W) hW = imageFrameEquiv u M e W := by
  have hh : HEq (frameEquiv u M e (u ''ᵁ W) hW)
      (imageFrameEquiv u M e (u ⁻¹ᵁ (u ''ᵁ W))) :=
    eqRec_heq (φ := fun V : X.Opens => Γ(M, V) ≃ₗ[Γ(X, V)] Γ(X, V))
      (image_preimage u (u ''ᵁ W) hW) (imageFrameEquiv u M e (u ⁻¹ᵁ (u ''ᵁ W)))
  exact eq_of_heq (hh.trans
    (dependent_heq (imageFrameEquiv u M e) (u.preimage_image_eq W)))

theorem frameEquiv_naturality {V W : X.Opens} (h : V ≤ W)
    (hW : W ≤ u.opensRange) (x : Γ(M, W)) :
    X.presheaf.map (homOfLE h).op (frameEquiv u M e W hW x) =
      frameEquiv u M e V (h.trans hW) (M.presheaf.map (homOfLE h).op x) := by
  obtain ⟨W', rfl⟩ : ∃ W' : X'.Opens, u ''ᵁ W' = W :=
    ⟨u ⁻¹ᵁ W, image_preimage u W hW⟩
  obtain ⟨V', rfl⟩ : ∃ V' : X'.Opens, u ''ᵁ V' = V :=
    ⟨u ⁻¹ᵁ V, image_preimage u V (h.trans hW)⟩
  have hvw : V' ≤ W' := by
    have hh := leOfHom ((Opens.map u.base).map (homOfLE h))
    simpa only [u.preimage_image_eq] using hh
  rw [frameEquiv_image, frameEquiv_image]
  exact imageFrameEquiv_naturality u M e (homOfLE hvw) x

/-- Every actual frame after restriction supplies a natural linear frame
on every subopen of the original image, with its original section ring. -/
def localFrame : LocalFrame X.sheaf M u.opensRange where
  app V hV := frameEquiv u M e V hV
  naturality hVW hW x := frameEquiv_naturality u M e hVW hW x

theorem localFrame_image (W : X'.Opens) (hW : u ''ᵁ W ≤ u.opensRange)
    (x : Γ(M, u ''ᵁ W)) :
    frameCoordinate (localFrame u M e) (u ''ᵁ W) hW x =
      (u.appIso W).inv (e.hom.app W ((M.restrictAppIso u W).inv x)) := by
  change frameEquiv u M e (u ''ᵁ W) hW x = _
  rw [frameEquiv_image]
  rfl

/-- A section normalized by the actual affine coordinate is normalized by
the transported frame on the whole image. -/
theorem localFrame_normalized (x : Γ(M, u.opensRange))
    (hx : e.hom.app ⊤
      ((M.restrictAppIso u ⊤).inv
        (M.presheaf.map (homOfLE (u.image_le_opensRange ⊤)).op x)) =
      (1 : Γ(X', ⊤))) :
    frameCoordinate (localFrame u M e) u.opensRange le_rfl x = 1 := by
  let k : u ''ᵁ (⊤ : X'.Opens) ⟶ u.opensRange := homOfLE (u.image_le_opensRange ⊤)
  have hk : k = eqToHom u.image_top_eq_opensRange := Subsingleton.elim _ _
  let : IsIso k := by rw [hk]; infer_instance
  apply (ConcreteCategory.bijective_of_isIso (X.presheaf.map k.op)).injective
  have hn := frameEquiv_naturality u M e (u.image_le_opensRange ⊤) le_rfl x
  have hv : frameEquiv u M e (u ''ᵁ (⊤ : X'.Opens)) (u.image_le_opensRange ⊤)
      (M.presheaf.map k.op x) = 1 := by
    rw [frameEquiv_image, imageFrameEquiv_apply]
    exact (congrArg ((u.appIso ⊤).inv) hx).trans ((u.appIso ⊤).inv.hom.map_one)
  exact (hn.trans hv).trans (X.presheaf.map k.op).hom.map_one.symm

theorem frameGenerator_eq_normalized (x : Γ(M, u.opensRange))
    (hx : e.hom.app ⊤
      ((M.restrictAppIso u ⊤).inv
        (M.presheaf.map (homOfLE (u.image_le_opensRange ⊤)).op x)) =
      (1 : Γ(X', ⊤))) :
    frameGenerator (localFrame u M e) u.opensRange le_rfl = x := by
  apply (frameEquiv u M e u.opensRange le_rfl).injective
  exact ((frameEquiv u M e u.opensRange le_rfl).apply_symm_apply
    (1 : Γ(X, u.opensRange))).trans (localFrame_normalized u M e x hx).symm

end CycleQ2OpenImmersionFrame
end

end
