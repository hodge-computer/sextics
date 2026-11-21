import Proposal.GeometricLiteralThreefoldResidueChartMaps
import Proposal.GeometricLiteralThreefoldChartVolume
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The oriented hypersurface three-form on weight-one chart overlaps

The chart change rescales both the oriented ambient volume and the conormal
to the fixed sextic by the sixth power of the same invertible coordinate.
Exterior algebra then identifies the actual normalized Kähler three-forms
even when the two gradient pivots are different.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LiteralThreefoldResidueGluing

open Module
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

private theorem scalar_determinant (b : Basis (Fin 4) R M)
    (F : M [⋀^Fin 4]→ₗ[R] N) (v : Fin 4 → M) :
    F v = b.det v • F b := by
  have he : F = b.det.smulRight (F b) := by
    apply b.ext_alternating
    intro i hi
    let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change F (b ∘ σ) = (b.det.smulRight (F b)) (b ∘ σ)
    simp [AlternatingMap.map_perm, Basis.det_self]
  exact DFunLike.congr_fun he v

private def alternateCoord (b : Basis (Fin 4) R M) (j : Fin 4) (q : M →ₗ[R] N) :
    M [⋀^Fin 4]→ₗ[R] (⋀[R]^3 N) :=
  AlternatingMap.alternatizeUncurryFin
    ((b.coord j).smulRight ((exteriorPower.ιMulti R 3).compLinearMap q))

private theorem alternateCoord_basis (b : Basis (Fin 4) R M) (j : Fin 4) (q : M →ₗ[R] N) :
    alternateCoord b j q b =
      (-1 : R)^j.val • exteriorPower.ιMulti R 3 ((q ∘ b) ∘ j.succAbove) := by
  rw [alternateCoord, AlternatingMap.alternatizeUncurryFin_apply, Finset.sum_eq_single j]
  · simp only [LinearMap.smulRight_apply, Basis.coord_apply, Basis.repr_self,
      Finsupp.single_eq_same, one_smul, AlternatingMap.compLinearMap_apply]
    change ((-1 : ℤ)^j.val) • _ = _
    rw [← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rfl
  · intro k _ hk
    simp [Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hk)]
  · simp

private theorem alternateCoord_first (b : Basis (Fin 4) R M) (j : Fin 4) (q : M →ₗ[R] N)
    (n : M) (hn : q n = 0) (u : Fin 3 → M) :
    alternateCoord b j q (Fin.cons n u) =
      b.coord j n • exteriorPower.ιMulti R 3 (q ∘ u) := by
  rw [alternateCoord, AlternatingMap.alternatizeUncurryFin_apply, Finset.sum_eq_single 0]
  · simp [AlternatingMap.compLinearMap_apply, Function.comp_def]
  · intro k _ hk
    let t : Fin 4 → M := Fin.cons n u
    have hz : exteriorPower.ιMulti R 3 (fun i => q (t (k.succAbove i))) = 0 := by
      apply (exteriorPower.ιMulti R 3).map_coord_zero (i := 0)
      fin_cases k <;> simp_all [t, Fin.succAbove]
    change (-1 : ℤ)^k.val • (b.coord j (t k) • exteriorPower.ιMulti R 3 (fun i => q (t (k.succAbove i)))) = 0
    rw [hz, smul_zero, smul_zero]
  · simp

theorem wedge_conormal_det (b : Basis (Fin 4) R M) (j : Fin 4) (q : M →ₗ[R] N)
    (n : M) (hn : q n = 0) (u : Fin 3 → M) :
    b.coord j n • exteriorPower.ιMulti R 3 (q ∘ u) =
      b.det (Fin.cons n u) • ((-1 : R)^j.val •
        exteriorPower.ιMulti R 3 ((q ∘ b) ∘ j.succAbove)) := by
  rw [← alternateCoord_first b j q n hn u, ← alternateCoord_basis b j q]
  exact scalar_determinant b _ _

theorem det_coeff_omitted (b : Basis (Fin 4) R M) (j : Fin 4) (y : Fin 4 → M) (a : Fin 4 → R) :
    b.det (Fin.cons (∑ k, a k • y k) (y ∘ j.succAbove)) = a j * (-1 : R)^j.val * b.det y := by
  let d := b.det.curryLeft
  let D : M →ₗ[R] R :=
    { toFun := fun x => d x (j.removeNth y)
      map_add' := fun x z => congrArg (fun g : M [⋀^Fin 3]→ₗ[R] R => g (j.removeNth y)) (d.map_add x z)
      map_smul' := fun r x => congrArg (fun g : M [⋀^Fin 3]→ₗ[R] R => g (j.removeNth y)) (d.map_smul r x) }
  change D (∑ k, a k • y k) = _
  simp only [map_sum, map_smul]
  rw [Finset.sum_eq_single j]
  · have h := b.det.neg_one_pow_smul_map_insertNth j (y j) (j.removeNth y)
    rw [Fin.insertNth_self_removeNth] at h
    change a j • b.det (Matrix.vecCons (y j) (j.removeNth y)) = _
    rw [← h, ← Int.cast_smul_eq_zsmul R, Int.cast_pow, Int.cast_neg, Int.cast_one]
    simp only [smul_eq_mul, mul_assoc]
  · intro k _ hk
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hk
    have hz : b.det (Fin.cons (y k) (j.removeNth y)) = 0 := by
      apply b.det.map_eq_zero_of_eq _ (i := 0) (j := l.succ) _ (Ne.symm (Fin.succ_ne_zero _))
      simp [Fin.removeNth, hl]
    change a k • b.det (Fin.cons (y k) (j.removeNth y)) = 0
    rw [hz, smul_zero]
  · simp

open CycleQ2LiteralThreefoldResidueMinors CycleQ2ExteriorTopBaseChange
private theorem orientation_det (b : Basis (Fin 4) R M) (v : Fin 4 → M) (o o' t : R)
    (hw : o' • exteriorPower.ιMulti R 4 v = t • (o • exteriorPower.ιMulti R 4 b)) :
    o' * b.det v = t * o := by
  have h := congrArg (topCoordinate b) hw
  simp only [map_smul, smul_eq_mul] at h
  rw [topCoordinate_basis, mul_one, topCoordinate_wedge] at h
  exact h

section Bezout

open Module CycleQ2LiteralThreefoldResidueMinors

variable {R M N L : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]

private theorem eq_of_bezout (a c : Fin 4 → R) (h : ∑ j, c j * a j = 1)
    (u v : L) (H : ∀ j, a j • u = a j • v) : u = v := by
  calc
    u = (∑ j, c j * a j) • u := by rw [h, one_smul]
    _ = (∑ j, c j * a j) • v := by
      simp only [Finset.sum_smul, mul_smul, H]
    _ = _ := by rw [h, one_smul]

/-- Changing all four coordinates preserves an oriented hypersurface three-form
when the changes of conormal and oriented volume have the same invertible
factor. The two gradient rows need only generate the unit ideal. -/
theorem bezout_residue_change (b : Basis (Fin 4) R M) (q : M →ₗ[R] N)
    (a a' c c' : Fin 4 → R) (h : ∑ j, c j * a j = 1) (h' : ∑ j, c' j * a' j = 1)
    (y : Fin 4 → M) (g o o' : R) (hg : IsUnit g)
    (hv : o' * b.det y = g * o)
    (hn : ∑ j, a' j • y j = g • ∑ j, a j • b j)
    (hq : ∑ j, a j • q (b j) = 0)
    (z z' : ⋀[R]^3 N)
    (hz : ∀ j, a j • z = signedOmitted R (q ∘ b) j)
    (hz' : ∀ j, a' j • z' = signedOmitted R (q ∘ y) j) :
    o' • z' = o • z := by
  let n := ∑ j, a j • b j
  have hzero : q n = 0 := by simpa only [n, map_sum, map_smul] using hq
  have hc (j : Fin 4) : b.coord j n = a j := by
    simp only [n, map_sum, map_smul, Basis.coord_apply, Basis.repr_self]
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      simp [Finsupp.single_eq_of_ne (Ne.symm hk)]
    · simp
  apply eq_of_bezout a' c' h'
  intro k
  let u := y ∘ k.succAbove
  let d := b.det (Fin.cons n u)
  have hw : exteriorPower.ιMulti R 3 (q ∘ u) = d • z := by
    apply eq_of_bezout a c h
    intro j
    rw [smul_comm (a j) d, hz j, ← hc j]
    exact wedge_conormal_det b j q n hzero u
  have hd : g * d = a' k * (-1 : R)^k.val * b.det y := by
    have he := det_coeff_omitted b k y a'
    rw [hn] at he
    change b.det.curryLeft (g • n) u = _ at he
    change g * (b.det.curryLeft n) u = _
    simpa only [map_smul, AlternatingMap.smul_apply, smul_eq_mul] using he
  have he : o' * (-1 : R)^k.val * d = a' k * o := by
    apply hg.mul_left_cancel
    have hs : (-1 : R)^k.val * (-1 : R)^k.val = 1 := by rw [← mul_pow]; simp
    calc
      _ = o' * (-1 : R)^k.val * (g * d) := by ring
      _ = a' k * ((-1 : R)^k.val * (-1 : R)^k.val) * (o' * b.det y) := by rw [hd]; ring
      _ = _ := by rw [hs, mul_one, hv]; ring
  rw [smul_comm (a' k) o', hz']
  change o' • ((-1 : R)^k.val • exteriorPower.ιMulti R 3 (q ∘ u)) = _
  rw [hw, smul_smul, smul_smul, he, smul_smul]

end Bezout

section FixedSextic

open Module MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldChartVolume CycleQ2ExteriorSectionNaturality
open scoped TensorProduct

variable (i : Fin 4) (k : Fin 3) (S : Type) [CommRing S] [Algebra (AmbientOverlap k) S]
  [Algebra ℂ S] [IsScalarTower ℂ (AmbientOverlap k) S]

set_option maxHeartbeats 800000 in
/-- The actual three-forms of the two entire affine fixed-sextic charts agree,
with their projective orientations, after restriction to any algebra of the overlap. -/
theorem chartVolume_overlap
    (hf : algebraMap (AmbientOverlap k) S (aeval (overlapCoordinates k) (seedF i)) = 0) :
    (-1 : S)^(i.succAbove k).val •
      exteriorDifferentialMap (chartMapAlgHom S (i.succAbove k)
        (changedCoordinate i (i.succAbove k) (overlapCoordinates k) (overlapInverse k))
        (targetEquation_zero i k S hf)) 3 (chartVolume (i.succAbove k)) =
    (-1 : S)^i.val • exteriorDifferentialMap
      (chartMapAlgHom S i (overlapCoordinates k) hf) 3 (chartVolume i) := by
  let m := i.succAbove k
  let x := overlapCoordinates k
  let y := changedCoordinate i m x (overlapInverse k)
  let fx := chartMapAlgHom S i x hf
  let fy := chartMapAlgHom S m y (targetEquation_zero i k S hf)
  let b := (overlapBasis k).baseChange S
  let v := restrictedDifferentials S y
  let q := KaehlerDifferential.mapBaseChange ℂ (AmbientOverlap k) S
  let g := (overlapFactor_isUnit k S).unit
  let a : Fin 4 → S := fun h => fx (gradient i h)
  let a' : Fin 4 → S := fun h => fy (gradient m h)
  have hb : ⇑b = restrictedDifferentials S x := by
    funext h
    simp only [b, Module.Basis.baseChange_apply, overlapBasis_apply]
    rfl
  have hx : q ∘ b = coordinateForm i fx := by
    rw [hb]
    exact funext (map_restrictedDifferentials S i x hf)
  have hy : q ∘ v = coordinateForm m fy :=
    funext (map_restrictedDifferentials S m y (targetEquation_zero i k S hf))
  have hz : ∑ h, a h • q (b h) = 0 := by
    simpa only [Function.comp_apply] using
      (show ∑ h, a h • (q ∘ b) h = 0 by rw [hx]; exact gradient_relation i fx)
  have hn : ∑ h, a' h • v h = (g : S) • ∑ h, a h • b h := by
    rw [hb, IsUnit.unit_spec]
    exact overlap_gradient_change i k S hf
  have hv : (-1 : S)^m.val * b.det v = (g : S) * (-1)^i.val := by
    have hw : (-1 : S)^m.val • exteriorPower.ιMulti S 4 v =
        (g : S) • ((-1 : S)^i.val • exteriorPower.ιMulti S 4 b) := by
      rw [hb, IsUnit.unit_spec]
      exact orientedRestrictedVolume_change i k S
    exact orientation_det b v _ _ _ hw
  obtain ⟨c, hc⟩ := chartBezout i
  obtain ⟨c', hc'⟩ := chartBezout m
  have hcx : ∑ h, fx (c h) * a h = 1 := by
    simpa only [a, map_sum, map_mul, map_one] using congrArg fx hc
  have hcy : ∑ h, fy (c' h) * a' h = 1 := by
    simpa only [a', map_sum, map_mul, map_one] using congrArg fy hc'
  apply bezout_residue_change b q a a' _ _ hcx hcy v (g : S) _ _ g.isUnit hv hn hz
  · intro l
    rw [hx]
    exact gradient_smul_chartVolume i fx l
  · intro l
    rw [hy]
    exact gradient_smul_chartVolume m fy l

/-- Both oriented hypersurface residues restrict to the same regular three-form
on any common algebra of the original chart overlap inverting the selected
source and target derivatives. The pivots can be chosen independently. -/
theorem orientedResidue_overlap
    (hf : algebraMap (AmbientOverlap k) S (aeval (overlapCoordinates k) (seedF i)) = 0)
    (j l : Fin 4)
    (hj : IsUnit (chartMap S i (overlapCoordinates k) hf (gradient i j)))
    (hl : IsUnit (chartMap S (i.succAbove k)
      (changedCoordinate i (i.succAbove k) (overlapCoordinates k) (overlapInverse k))
      (targetEquation_zero i k S hf) (gradient (i.succAbove k) l))) :
    (-1 : S)^(i.succAbove k).val • residue (i.succAbove k)
      (chartMapAlgHom S (i.succAbove k)
        (changedCoordinate i (i.succAbove k) (overlapCoordinates k) (overlapInverse k))
        (targetEquation_zero i k S hf)) l hl =
    (-1 : S)^i.val • residue i (chartMapAlgHom S i (overlapCoordinates k) hf) j hj := by
  let m := i.succAbove k
  let fx := chartMapAlgHom S i (overlapCoordinates k) hf
  let fy := chartMapAlgHom S m
    (changedCoordinate i m (overlapCoordinates k) (overlapInverse k)) (targetEquation_zero i k S hf)
  exact (congrArg ((-1 : S)^m.val • ·) (chartVolume_eq_residue m fy l hl).symm).trans
    ((chartVolume_overlap i k S hf).trans (congrArg ((-1 : S)^i.val • ·)
      (chartVolume_eq_residue i fx j hj)))

section Canonical

attribute [local instance] CycleQ2LiteralThreefoldResidueCoordinates.fixedAmbientAlgebra
  CycleQ2LiteralThreefoldResidueChartMaps.fixedAmbientTower
  CycleQ2LiteralThreefoldResidueChartMaps.sourceFixedAlgebra
  CycleQ2LiteralThreefoldResidueChartMaps.sourceFixedTower

set_option maxHeartbeats 800000 in
/-- Equality on the fixed threefold's actual coordinate overlap with no additional localization. -/
theorem fixedChartVolume_overlap (i : Fin 4) (k : Fin 3) :
    (-1 : FixedOverlap i k)^(i.succAbove k).val •
      exteriorDifferentialMap (fixedTargetMap i k) 3 (chartVolume (i.succAbove k)) =
    (-1 : FixedOverlap i k)^i.val •
      exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ (T i) (FixedOverlap i k)) 3 (chartVolume i) := by
  exact (chartVolume_overlap i k (FixedOverlap i k) (equation_zero i k)).trans
    (congrArg (fun f : T i →ₐ[ℂ] FixedOverlap i k =>
      (-1 : FixedOverlap i k)^i.val • exteriorDifferentialMap f 3 (chartVolume i)) (fixedSourceMap_eq i k))

end Canonical
end FixedSextic
end CycleQ2LiteralThreefoldResidueGluing
end

#print axioms CycleQ2LiteralThreefoldResidueGluing.chartVolume_overlap
#print axioms CycleQ2LiteralThreefoldResidueGluing.orientedResidue_overlap
#print axioms CycleQ2LiteralThreefoldResidueGluing.fixedChartVolume_overlap
