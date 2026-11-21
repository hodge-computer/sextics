import Proposal.GeometricSurfaceResidueOverlap
import Proposal.GeometricIncidenceDehomogenizedChart

/-!
# Change of anticanonical coordinates on the fixed weighted sextic

On each weight-one chart the coordinate order starts with
z=(w+X₂²)/Xᵢ² and continues with the other three linear coordinates in
increasing order. On each overlap of distinct charts, the original fixed
degree-six equation and the oriented four-form both acquire the sixth
power of the inverse coordinate. After restriction to the threefold the
same equality holds for its conormal in the ambient cotangent module.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldResidueCoordinates
open Module MvPolynomial CycleQ2IncidenceDehomogenizedChart CycleQ2GeometricIncidenceProj
  CycleQ2IncidencePolynomialJacobianBinding
variable {R : Type*} [CommRing R]

def linearValues (i : Fin 4) (x : Option (Fin 3) → R) : Fin 4 → R :=
  Fin.insertNth i 1 (fun a => x (some a))

def linearDirections (i : Fin 4) : Fin 4 → Fin 4 → R :=
  Fin.insertNth i 0 (fun a => Pi.basisFun R (Fin 4) a.succ)

def jacobianColumns (i : Fin 4) (k : Fin 3) (x : Option (Fin 3) → R) (t : R) :
    Fin 4 → Fin 4 → R :=
  let b := Pi.basisFun R (Fin 4)
  let j := i.succAbove k
  Fin.cons (t^2 • b 0 - (2*x none*t^3) • b k.succ)
    (fun a => t • linearDirections i (j.succAbove a) -
      (linearValues i x (j.succAbove a)*t^2) • b k.succ)

private theorem det_first_row (m : Matrix (Fin 4) (Fin 4) R)
    (hz : ∀ n : Fin 3, m 0 n.succ = 0) :
    m.det = m 0 0 * (m.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, hz, Matrix.det_fin_three]

private theorem zero_first_row (i : Fin 4) (k n : Fin 3) (x : Option (Fin 3) → R) (t : R) :
    ((Pi.basisFun R (Fin 4)).toMatrix (jacobianColumns i k x t)) 0 n.succ = 0 := by
  have hd (a : Fin 4) : linearDirections (R := R) i a 0 = 0 := by
    obtain rfl | ⟨b, rfl⟩ := i.eq_self_or_eq_succAbove a
    · simp [linearDirections]
    · simp [linearDirections, Pi.basisFun_apply]
  simp [Module.Basis.toMatrix_apply, jacobianColumns, hd, Pi.basisFun_apply]

private theorem first_entry (i : Fin 4) (k : Fin 3) (x : Option (Fin 3) → R) (t : R) :
    ((Pi.basisFun R (Fin 4)).toMatrix (jacobianColumns i k x t)) 0 0 = t^2 := by
  simp [Module.Basis.toMatrix_apply, jacobianColumns, Pi.basisFun_apply]

private theorem direction_entry (i h : Fin 4) (r : Fin 3) :
    linearDirections (R := R) i h r.succ = if h = i.succAbove r then 1 else 0 := by
  obtain rfl | ⟨a, rfl⟩ := i.eq_self_or_eq_succAbove h
  · simp [linearDirections, Fin.ne_succAbove]
  · simp [linearDirections, Pi.basisFun_apply, Pi.single_apply, eq_comm]

private theorem minor_entry (i : Fin 4) (k r c : Fin 3) (x : Option (Fin 3) → R) (t : R) :
    ((Pi.basisFun R (Fin 4)).toMatrix (jacobianColumns i k x t)) r.succ c.succ =
      (if (i.succAbove k).succAbove c = i.succAbove r then t else 0) -
      (if r = k then (if (i.succAbove k).succAbove c = i then 1
                      else linearValues i x ((i.succAbove k).succAbove c)) * t^2 else 0) := by
  rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  simp only [jacobianColumns, Fin.cons_succ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    direction_entry, Pi.basisFun_apply, Pi.single_apply, Fin.succ_inj]
  split_ifs <;> simp_all [linearValues]

set_option maxHeartbeats 500000 in
theorem jacobianColumns_det (i : Fin 4) (k : Fin 3) (x : Option (Fin 3) → R) (t : R) :
    ((Pi.basisFun R (Fin 4)).toMatrix (jacobianColumns i k x t)).det =
      (-1 : R)^(i.val+(i.succAbove k).val)*t^6 := by
  rw [det_first_row _ (zero_first_row i k · x t), first_entry, Matrix.det_fin_three]
  simp only [Matrix.submatrix_apply, minor_entry]
  fin_cases i <;> fin_cases k <;>
    simp (disch := decide) only [if_pos, if_neg, zero_mul, mul_zero, sub_zero, zero_sub,
      add_zero, zero_add, one_mul] <;>
    simp (disch := decide) only [Fin.succAbove, if_pos, if_neg, Fin.val_castSucc, Fin.val_succ] <;> ring


variable [Algebra ℂ R]

/-- The target chart values expressed in the source chart. -/
def changedCoordinate (i j : Fin 4) (x : Option (Fin 3) → R) (t : R) :
    Option (Fin 3) → R
  | none => x none * t ^ 2
  | some a => Fin.insertNth (α := fun _ => R) i 1 (fun h => x (some h)) (j.succAbove a) * t

theorem eval_linearCoordinate (i : Fin 4) (x : Option (Fin 3) → R) (k : Fin 4) :
    aeval x (linearCoordinate (S := ℂ) i k) = Fin.insertNth (α := fun _ => R) i 1 (fun h => x (some h)) k := by
  refine Fin.succAboveCases i ?_ (fun a => ?_) k <;> simp

theorem changed_linear (i j : Fin 4) (x : Option (Fin 3) → R) (t : R)
    (ht : t * Fin.insertNth (α := fun _ => R) i 1 (fun h => x (some h)) j = 1) (k : Fin 4) :
    aeval (changedCoordinate i j x t) (linearCoordinate (S := ℂ) j k) =
      t * aeval x (linearCoordinate (S := ℂ) i k) := by
  refine Fin.succAboveCases j ?_ (fun a => ?_) k
  · rw [linearCoordinate_self, map_one, eval_linearCoordinate, ht]
  · rw [linearCoordinate_succAbove, aeval_X, eval_linearCoordinate]
    exact mul_comm _ _

/-- Restriction of a weighted-homogeneous equation to any two weight-one
charts, including the shifted weight-two coordinate. -/
theorem homogeneous_change (i j : Fin 4) (x : Option (Fin 3) → R) (t : R)
    (ht : t * Fin.insertNth (α := fun _ => R) i 1 (fun h => x (some h)) j = 1)
    (p : MvPolynomial (Fin 5) ℂ) {n : ℕ} (hp : p.IsWeightedHomogeneous geometricWeight n) :
    aeval (changedCoordinate i j x t) (dehomogenize j p) =
      t^n * aeval x (dehomogenize i p) := by
  let f : MvPolynomial (Fin 5) ℂ →ₐ[ℂ] R := (aeval x).comp (dehomogenize i)
  let y : Fin 5 → R := fun l => f (X l)
  have hf : aeval y = f := by ext k; exact aeval_X y k
  have hg : (aeval (changedCoordinate i j x t)).comp (dehomogenize (S := ℂ) j) =
      aeval (fun l => t ^ geometricWeight l * y l) := by
    apply MvPolynomial.algHom_ext
    intro l
    rw [aeval_X]
    change aeval (changedCoordinate i j x t) (dehomogenize (S := ℂ) j (X l)) =
        t ^ geometricWeight l * aeval x (dehomogenize (S := ℂ) i (X l))
    refine Fin.lastCases ?_ (fun k => ?_) l
    · rw [dehomogenize_last, dehomogenize_last, map_sub, map_sub, map_pow, map_pow,
        aeval_X, aeval_X, weight_last, changed_linear i j x t ht]
      change x none * t ^ 2 - _ = _
      ring
    · rw [dehomogenize_castSucc, dehomogenize_castSucc, weight_castSucc, pow_one,
        changed_linear i j x t ht]
  change ((aeval (changedCoordinate i j x t)).comp (dehomogenize (S := ℂ) j)) p =
      t ^ n * f p
  rw [hg, ← hf]
  exact weighted_homogeneous_eval_scale (algebraMap ℂ R) y t p n hp

/-- Specialization to the literal fixed threefold sextic in the seed charts. -/
theorem seedF_change (i j : Fin 4) (x : Option (Fin 3) → R) (t : R)
    (ht : t * Fin.insertNth (α := fun _ => R) i 1 (fun h => x (some h)) j = 1) :
    aeval (changedCoordinate i j x t)
      (dehomogenize j (pointEquationF (seedPoint (57 : ℂ) Complex.I))) =
      t^6 * aeval x
        (dehomogenize i (pointEquationF (seedPoint (57 : ℂ) Complex.I))) :=
  homogeneous_change i j x t ht _ (pointEquationF_homogeneous _)

open scoped TensorProduct

private theorem tensor_scale {S : Type*} [CommRing S] [Algebra R S]
    (a : R) (m : KaehlerDifferential ℂ R) :
    (1 : S) ⊗ₜ[R] (a • m) = algebraMap R S a • ((1 : S) ⊗ₜ[R] m) := by
  rw [TensorProduct.tmul_smul]
  exact (IsScalarTower.algebraMap_smul S a _).symm

/-- The restrictions of the ambient equation differentials have the same
factor. The extra Leibniz term vanishes after restricting coefficients to
the hypersurface. -/
theorem conormal_change {S : Type*} [CommRing S] [Algebra R S]
    (i j : Fin 4) (x : Option (Fin 3) → R) (t : R)
    (ht : t * Fin.insertNth (α := fun _ => R) i 1 (fun h => x (some h)) j = 1)
    (p : MvPolynomial (Fin 5) ℂ) {n : ℕ} (hp : p.IsWeightedHomogeneous geometricWeight n)
    (hz : algebraMap R S (aeval x (dehomogenize i p)) = 0) :
    (1 : S) ⊗ₜ[R] KaehlerDifferential.D ℂ R (aeval (changedCoordinate i j x t) (dehomogenize j p)) =
      (algebraMap R S t)^n • ((1 : S) ⊗ₜ[R] KaehlerDifferential.D ℂ R (aeval x (dehomogenize i p))) := by
  rw [homogeneous_change i j x t ht p hp, Derivation.leibniz, TensorProduct.tmul_add,
    tensor_scale, tensor_scale, hz, zero_smul, add_zero, map_pow]


/-- The exterior product in the incidence chart order (dz, dxₐ, dxᵦ, dx𝒸). -/
def coordinateVolume (x : Option (Fin 3) → R) : ⋀[R]^4 (KaehlerDifferential ℂ R) :=
  exteriorPower.ιMulti R 4 (fun l => KaehlerDifferential.D ℂ R (x (finSuccEquiv 3 l)))

private def differentialRealization (x : Option (Fin 3) → R) :
    (Fin 4 → R) →ₗ[R] KaehlerDifferential ℂ R :=
  (Pi.basisFun R (Fin 4)).constr R (fun l => KaehlerDifferential.D ℂ R (x (finSuccEquiv 3 l)))

private theorem realization_basis (x : Option (Fin 3) → R) (l : Fin 4) :
    differentialRealization x (Pi.basisFun R (Fin 4) l) =
      KaehlerDifferential.D ℂ R (x (finSuccEquiv 3 l)) :=
  Basis.constr_basis _ _ _ _

private theorem realization_direction (i : Fin 4) (x : Option (Fin 3) → R) (l : Fin 4) :
    differentialRealization x (linearDirections (R := R) i l) =
      KaehlerDifferential.D ℂ R (linearValues i x l) := by
  refine Fin.succAboveCases i ?_ (fun a => ?_) l
  · simp [linearDirections, linearValues]
  · simp only [linearDirections, linearValues, Fin.insertNth_apply_succAbove, realization_basis, finSuccEquiv_succ]

private theorem realizedColumn (i : Fin 4) (k : Fin 3) (x : Option (Fin 3) → R) (t : R)
    (ht : t * x (some k) = 1) (l : Fin 4) :
    differentialRealization x (jacobianColumns i k x t l) =
      KaehlerDifferential.D ℂ R (changedCoordinate i (i.succAbove k) x t (finSuccEquiv 3 l)) := by
  have hinv := (KaehlerDifferential.D ℂ R).leibniz_of_mul_eq_one ht
  induction l using Fin.cases with
  | zero =>
    simp only [jacobianColumns, Fin.cons_zero, map_sub, map_smul, realization_basis,
      finSuccEquiv_zero, finSuccEquiv_succ, changedCoordinate, Derivation.leibniz,
      Derivation.leibniz_pow, hinv, Nat.reduceSub, pow_one]
    rw [← Nat.cast_smul_eq_nsmul R]
    simp only [Nat.cast_ofNat, smul_smul]
    module
  | succ l =>
    simp only [jacobianColumns, Fin.cons_succ, map_sub, map_smul, realization_direction,
      realization_basis, finSuccEquiv_succ, changedCoordinate, Derivation.leibniz, hinv,
      linearValues, smul_smul]
    module

/-- The change of the actual ordered four-differential in every algebra
receiving a point of the ambient overlap. -/
theorem coordinateVolume_change (i : Fin 4) (k : Fin 3) (x : Option (Fin 3) → R) (t : R)
    (ht : t * x (some k) = 1) :
    coordinateVolume (changedCoordinate i (i.succAbove k) x t) =
      ((-1 : R) ^ (i.val + (i.succAbove k).val) * t^6) • coordinateVolume x := by
  let b := Pi.basisFun R (Fin 4)
  have h := congrArg (exteriorPower.map 4 (differentialRealization x))
    (CycleQ2ResidueWedgeLinear.topWedge_eq_det_smul b (jacobianColumns i k x t))
  simpa only [exteriorPower.map_apply_ιMulti, map_smul, Function.comp_def, realizedColumn i k x t ht,
    b, realization_basis, coordinateVolume, jacobianColumns_det] using h

open scoped TensorProduct

/-- The ambient overlap of the original source and target weight-one charts. -/
abbrev AmbientOverlap (k : Fin 3) :=
  Localization.Away (X (some k) : ChartPolynomial ℂ)

def overlapCoordinates (k : Fin 3) (a : Option (Fin 3)) : AmbientOverlap k :=
  algebraMap (ChartPolynomial ℂ) (AmbientOverlap k) (X a)

def overlapInverse (k : Fin 3) : AmbientOverlap k :=
  IsLocalization.Away.invSelf (X (some k) : ChartPolynomial ℂ)

theorem overlapInverse_mul (k : Fin 3) :
    overlapInverse k * overlapCoordinates k (some k) = 1 := by
  rw [mul_comm]
  exact IsLocalization.Away.mul_invSelf _

/-- The ordered four-coordinate differential basis before taking the hypersurface quotient. -/
def overlapBasis (k : Fin 3) :
    Basis (Fin 4) (AmbientOverlap k) (KaehlerDifferential ℂ (AmbientOverlap k)) := by
  letI : Algebra.FormallyEtale (ChartPolynomial ℂ) (AmbientOverlap k) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := AmbientOverlap k)
      (Submonoid.powers (X (some k) : ChartPolynomial ℂ))
  exact ((((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).baseChange (AmbientOverlap k)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ (ChartPolynomial ℂ) (AmbientOverlap k))).reindex
      (finSuccEquiv 3).symm)

@[simp] theorem overlapBasis_apply (k : Fin 3) (j : Fin 4) :
    overlapBasis k j = KaehlerDifferential.D ℂ (AmbientOverlap k)
      (overlapCoordinates k (finSuccEquiv 3 j)) := by
  simp only [overlapBasis, Basis.reindex_apply, Equiv.symm_symm, Basis.map_apply,
    Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply]
  change KaehlerDifferential.mapBaseChange ℂ (ChartPolynomial ℂ) (AmbientOverlap k) _ = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

/-- An ambient four-form restricted as a tensor to an arbitrary algebra over
the overlap, including its fixed hypersurface quotient. -/
def restrictedVolume (k : Fin 3) (S : Type) [CommRing S] [Algebra (AmbientOverlap k) S]
    (x : Option (Fin 3) → AmbientOverlap k) :=
  exteriorPower.ιMulti S 4 (fun l => (1 : S) ⊗ₜ[AmbientOverlap k]
    KaehlerDifferential.D ℂ (AmbientOverlap k) (x (finSuccEquiv 3 l)))

theorem restrictedVolume_change (i : Fin 4) (k : Fin 3) (S : Type) [CommRing S]
    [Algebra (AmbientOverlap k) S] :
    restrictedVolume k S (changedCoordinate i (i.succAbove k) (overlapCoordinates k)
      (overlapInverse k)) = ((-1 : S) ^ (i.val + (i.succAbove k).val) *
        (algebraMap (AmbientOverlap k) S (overlapInverse k))^6) •
      restrictedVolume k S (overlapCoordinates k) := by
  have he := congrArg (CycleQ2ExteriorTopBaseChange.topBaseChange (S := S) (overlapBasis k))
    (coordinateVolume_change i k (overlapCoordinates k) (overlapInverse k) (overlapInverse_mul k))
  simpa only [coordinateVolume, restrictedVolume, CycleQ2ExteriorTopBaseChange.topBaseChange_wedge,
    map_smulₛₗ, map_mul, map_pow, map_neg, map_one] using he


/-- The projective orientation removes the permutation sign, leaving precisely
the degree-six factor of the fixed hypersurface equation. -/
theorem orientedRestrictedVolume_change (i : Fin 4) (k : Fin 3) (S : Type) [CommRing S]
    [Algebra (AmbientOverlap k) S] :
    (-1 : S) ^ (i.succAbove k).val • restrictedVolume k S
      (changedCoordinate i (i.succAbove k) (overlapCoordinates k) (overlapInverse k)) =
      (algebraMap (AmbientOverlap k) S (overlapInverse k))^6 •
        ((-1 : S)^i.val • restrictedVolume k S (overlapCoordinates k)) := by
  rw [restrictedVolume_change i k S, smul_smul, smul_smul]
  congr 1
  rw [pow_add]
  have h : (-1 : S)^(i.succAbove k).val * (-1 : S)^(i.succAbove k).val = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = ((-1 : S)^(i.succAbove k).val * (-1 : S)^(i.succAbove k).val) *
        ((algebraMap (AmbientOverlap k) S (overlapInverse k))^6 * (-1 : S)^i.val) := by ring
    _ = _ := by rw [h, one_mul]


open CycleQ2GeometricIncidenceProj CycleQ2IncidencePolynomialJacobianBinding

abbrev literalEquation (i : Fin 4) : ChartPolynomial ℂ :=
  dehomogenize i (pointEquationF (seedPoint (57 : ℂ) Complex.I))

/-- The localized chart of the fixed threefold, obtained by imposing the
original sextic on chart i and then inverting its j-th projective coordinate. -/
abbrev FixedOverlap (i : Fin 4) (k : Fin 3) :=
  Localization.Away (Ideal.Quotient.mk (Ideal.span {literalEquation i}) (X (some k)))

def ambientToFixed (i : Fin 4) (k : Fin 3) : AmbientOverlap k →+* FixedOverlap i k :=
  let q := Ideal.Quotient.mk (Ideal.span {literalEquation i})
  let g := (algebraMap _ (FixedOverlap i k)).comp q
  IsLocalization.Away.lift (X (some k) : ChartPolynomial ℂ)
    (g := g) (IsLocalization.Away.algebraMap_isUnit (q (X (some k))))

local instance fixedAmbientAlgebra (i : Fin 4) (k : Fin 3) :
    Algebra (AmbientOverlap k) (FixedOverlap i k) := (ambientToFixed i k).toAlgebra

theorem equation_zero (i : Fin 4) (k : Fin 3) :
    algebraMap (AmbientOverlap k) (FixedOverlap i k)
      (aeval (overlapCoordinates k) (literalEquation i)) = 0 := by
  have he : aeval (overlapCoordinates k) =
      IsScalarTower.toAlgHom ℂ (ChartPolynomial ℂ) (AmbientOverlap k) := by
    apply MvPolynomial.algHom_ext
    intro s
    rw [aeval_X]
    rfl
  rw [he]
  change ambientToFixed i k (algebraMap (ChartPolynomial ℂ) (AmbientOverlap k) (literalEquation i)) = _
  rw [ambientToFixed, IsLocalization.Away.lift_eq]
  change algebraMap _ (FixedOverlap i k)
    (Ideal.Quotient.mk (Ideal.span {literalEquation i}) (literalEquation i)) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero]

/-- The common multiplier remains invertible after further base change. -/
theorem overlapFactor_isUnit (k : Fin 3) (S : Type) [CommRing S] [Algebra (AmbientOverlap k) S] :
    IsUnit ((algebraMap (AmbientOverlap k) S (overlapInverse k))^6) := by
  have hu : IsUnit (overlapInverse k) :=
    isUnit_of_dvd_one ⟨overlapCoordinates k (some k), (overlapInverse_mul k).symm⟩
  exact (hu.map (algebraMap (AmbientOverlap k) S)).pow 6

/-- On the literal fixed-sextic chart overlaps both the oriented ambient
volume and the ambient conormal to the fixed sextic acquire exactly t^6. -/
theorem fixedOverlap_transition (i : Fin 4) (k : Fin 3) :
    let j := i.succAbove k
    let x := overlapCoordinates k
    let t := overlapInverse k
    let S := FixedOverlap i k
    let target := changedCoordinate i j x t
    let factor := (algebraMap (AmbientOverlap k) S t)^6
    ((-1 : S)^j.val • restrictedVolume k S target =
        factor • ((-1 : S)^i.val • restrictedVolume k S x)) ∧
      ((1 : S) ⊗ₜ[AmbientOverlap k] KaehlerDifferential.D ℂ (AmbientOverlap k)
        (aeval target (literalEquation j)) =
        factor • ((1 : S) ⊗ₜ[AmbientOverlap k] KaehlerDifferential.D ℂ (AmbientOverlap k)
          (aeval x (literalEquation i)))) := by
  dsimp only
  refine ⟨orientedRestrictedVolume_change i k _, ?_⟩
  exact conormal_change i (i.succAbove k) (overlapCoordinates k) (overlapInverse k)
    (by simpa only [Fin.insertNth_apply_succAbove] using overlapInverse_mul k)
    _ (pointEquationF_homogeneous _) (equation_zero i k)

end CycleQ2LiteralThreefoldResidueCoordinates
end

#print axioms CycleQ2LiteralThreefoldResidueCoordinates.fixedOverlap_transition
