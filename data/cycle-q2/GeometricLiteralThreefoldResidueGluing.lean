import Proposal.GeometricLiteralThreefoldResidueChartMaps
import Proposal.GeometricLiteralThreefoldChartVolume
import Proposal.GeometricLiteralThreefoldChartVolumeFrame
import Proposal.GeometricLiteralThreefoldGradientAtlas
import Proposal.GeometricLiteralThreefoldDifferentialFrame
import Proposal.GeometricLiteralThreefoldHodgeCech
import Proposal.GeometricSurfaceCoordinateCubicFrames
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

/-!
# The actual canonical sheaf of the fixed threefold is trivial

The affine residue equivalences extend to genuine sheaf frames by the
proved Kähler bases on the gradient opens. Their inverse-one sections are
the original oriented chart residues. The overlap identity above therefore
glues the four chart frames to a frame on the whole fixed threefold. This
construction concerns `IncidenceFiber 57`; no relative or generic
trivialization is substituted for the fixed geometric data.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldCanonicalFrame

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricCanonicalGluing
  CycleQ2GeometricModuleOverFrame CycleQ2ChartExteriorBinding
  CycleQ2LiteralThreefoldDifferentialFrame CycleQ2ExteriorTopBaseChange
  CycleQ2LocalFrameGluing

section ScaledBasis

variable {X : Scheme.{0}} {U : X.Opens} {A : Type}
  [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential ℂ A)) (u : Aˣ)

/-- Multiplying the basis wedge by the specified affine unit changes its
actual sheaf coordinate by the inverse unit on every subopen. -/
def scaledBasisFrame : LocalFrame X.sheaf
    (exteriorSheaf X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val n) U where
  app O hO :=
    ((patchIsoOfOverFrame (frameIso e f h b)).app O hO).trans
      (LinearEquiv.smulOfUnit
        (Units.map (chartSection e (Over.mk (homOfLE hO))).toMonoidHom u⁻¹))
  naturality {O P} hPO hO s := by
    let a : Over.mk (homOfLE (hPO.trans hO)) ⟶ Over.mk (homOfLE hO) :=
      Over.homMk (homOfLE hPO)
    change X.presheaf.map (homOfLE hPO).op
        (chartSection e (Over.mk (homOfLE hO)) (↑u⁻¹ : A) *
          (patchIsoOfOverFrame (frameIso e f h b)).app O hO s) =
      chartSection e (Over.mk (homOfLE (hPO.trans hO))) (↑u⁻¹ : A) *
        (patchIsoOfOverFrame (frameIso e f h b)).app P (hPO.trans hO)
          ((exteriorSheaf X.sheaf
            (differentialSheaf X.sheaf (schemeCoefficient f)).val n).val.map
              (homOfLE hPO).op s)
    rw [map_mul, chartSection_naturality e a,
      (patchIsoOfOverFrame (frameIso e f h b)).naturality]

theorem scaledBasisFrame_native (O : X.Opens) (hO : O ≤ U)
    (ω : ⋀[A]^n (KaehlerDifferential ℂ A)) :
    (scaledBasisFrame e f h b u).app O hO
      (chartExteriorSheafSection e f h n (Over.mk (homOfLE hO)) ω) =
      chartSection e (Over.mk (homOfLE hO))
        ((↑u⁻¹ : A) * topCoordinate b ω) := by
  change chartSection e (Over.mk (homOfLE hO)) (↑u⁻¹ : A) *
      (frameIso e f h b).hom.val.app (op (Over.mk (homOfLE hO)))
        (chartExteriorSheafSection e f h n (Over.mk (homOfLE hO)) ω) = _
  rw [frameIso_on_section, map_mul]

/-- The inverse-one section is the image of the specified native wedge,
including its unit and its sign. -/
theorem scaledBasisFrame_generator (O : X.Opens) (hO : O ≤ U) :
    frameGenerator (scaledBasisFrame e f h b u) O hO =
      chartExteriorSheafSection e f h n (Over.mk (homOfLE hO))
        ((u : A) • exteriorPower.ιMulti A n b) := by
  apply ((scaledBasisFrame e f h b u).app O hO).injective
  change (scaledBasisFrame e f h b u).app O hO
      (((scaledBasisFrame e f h b u).app O hO).symm (1 : Γ(X,O))) = _
  rw [LinearEquiv.apply_symm_apply, scaledBasisFrame_native]
  simp only [map_smul, topCoordinate_basis, smul_eq_mul, mul_one,
    Units.inv_mul, map_one]

end ScaledBasis

open CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldResidueFrame
  CycleQ2LiteralThreefoldResidueMinors CycleQ2LiteralThreefoldChartVolume
  CycleQ2LiteralThreefoldChartVolumeFrame CycleQ2LiteralThreefoldGradientAtlas
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldOverlapAtlas CycleQ2ExteriorSectionNaturality
  CycleQ2LiteralThreefoldHodgeCech (Threefold structureMap coefficients Cotangent)

attribute [local instance] sourceFixedAlgebra sourceFixedTower

/-- The actual exterior cube of the same differential sheaf used by the
fixed threefold's test Čech complex. -/
abbrev CanonicalForms := exteriorSheaf Threefold.sheaf Cotangent.val 3

abbrev StructureModule := SheafOfModules.unit (ringSheaf Threefold.sheaf)

abbrev CanonicalAdditiveSheaf := CycleQ2GeometricModuleLocalIso.addSheaf CanonicalForms

private theorem chart_over (i : Fin 4) :
    (fixedChart i).symm.inv ≫ (fixedOpen i).ι ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (T i))) := by
  simpa only [Category.assoc, Iso.symm_inv, chartInclusion] using chartInclusion_overComplex i

private theorem gradient_over (i j : Fin 4) :
    (gradientIso i j).inv ≫ (gOpen i j).ι ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Patch i j))) := by
  rw [← Category.assoc, gradientIso_inv_ι, Category.assoc, chartInclusion_overComplex,
    ← Spec.map_comp]
  rfl_cat

private theorem overlap_over (i : Fin 4) (k : Fin 3) :
    (overlapIso i k).hom ≫ (fixedOpen i ⊓ fixedOpen (i.succAbove k)).ι ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FixedOverlap i k))) := by
  rw [← Category.assoc, overlapIso_hom_ι, Category.assoc, chartInclusion_overComplex,
    ← Spec.map_comp]
  rfl_cat

/-- The native projective orientation on the entire affine chart. -/
def orientedChartVolume (i : Fin 4) : ⋀[T i]^3 (KaehlerDifferential ℂ (T i)) :=
  (-1 : T i)^i.val • chartVolume i

/-- The same native form as an actual canonical-sheaf section on a subopen. -/
def orientedVolumeSection (i : Fin 4) (O : Threefold.Opens) (hO : O ≤ fixedOpen i) :
    CanonicalForms.val.obj (op O) :=
  chartExteriorSheafSection (fixedChart i).symm structureMap (chart_over i)
    3 (Over.mk (homOfLE hO)) (orientedChartVolume i)

theorem orientedVolumeSection_restrict (i : Fin 4) {O P : Threefold.Opens}
    (hO : O ≤ fixedOpen i) (hPO : P ≤ O) :
    CanonicalForms.val.map (homOfLE hPO).op (orientedVolumeSection i O hO) =
      orientedVolumeSection i P (hPO.trans hO) :=
  chartExteriorSheafSection_restrict (fixedChart i).symm structureMap (chart_over i)
    (Over.homMk (homOfLE hPO) :
      Over.mk (homOfLE (hPO.trans hO)) ⟶ Over.mk (homOfLE hO)) 3 _

private def orientedPatchUnit (i j : Fin 4) : (Patch i j)ˣ :=
  (-1 : (Patch i j)ˣ)^i.val *
    (IsLocalization.Away.algebraMap_isUnit (S := Patch i j) (gradient i j)).unit⁻¹ *
      (-1 : (Patch i j)ˣ)^j.val

private theorem orientedChartVolume_gradient (i j : Fin 4) :
    exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ (T i) (Patch i j)) 3
      (orientedChartVolume i) =
        (orientedPatchUnit i j : Patch i j) • exteriorPower.ιMulti (Patch i j) 3 (basis i j) := by
  have hb : (basis i j : Fin 3 → _) =
      coordinateForm i (IsScalarTower.toAlgHom ℂ (T i) (Patch i j)) ∘ j.succAbove := by
    funext k
    exact basis_apply i j k
  rw [orientedChartVolume, map_smulₛₗ, map_pow, map_neg, map_one, chartVolume_on_patch,
    patchResidue, residue, signedOmitted, ← hb]
  simp only [orientedPatchUnit, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, mul_smul]

/-- The genuine residue frame on one of the sixteen gradient opens. -/
def gradientCanonicalFrame (i j : Fin 4) : LocalFrame Threefold.sheaf CanonicalForms (gOpen i j) :=
  scaledBasisFrame (gradientIso i j) structureMap (gradient_over i j)
    (basis i j) (orientedPatchUnit i j)

theorem gradientCanonicalFrame_generator (i j : Fin 4)
    (O : Threefold.Opens) (hO : O ≤ gOpen i j) :
    frameGenerator (gradientCanonicalFrame i j) O hO =
      orientedVolumeSection i O (hO.trans (gOpen_le i j)) := by
  rw [gradientCanonicalFrame, scaledBasisFrame_generator, ← orientedChartVolume_gradient]
  exact chartExteriorSheafSection_differentialMap (fixedChart i).symm (gradientIso i j)
    (gOpen_le i j) structureMap (chart_over i) (gradient_over i j)
    (IsScalarTower.toAlgHom ℂ (T i) (Patch i j))
    (by simpa only [Iso.symm_inv, ← Category.assoc, chartInclusion] using gradientIso_inv_ι i j)
    (Over.mk (homOfLE hO)) 3 _

private theorem gradient_generators_agree (i j k : Fin 4) :
    frameGenerator (gradientCanonicalFrame i j) (gOpen i j ⊓ gOpen i k) inf_le_left =
      frameGenerator (gradientCanonicalFrame i k) (gOpen i j ⊓ gOpen i k) inf_le_right := by
  rw [gradientCanonicalFrame_generator, gradientCanonicalFrame_generator]

/-- Extension of the affine chart residue frame to every genuine sheaf
section on that entire affine chart. -/
def chartCanonicalFrame (i : Fin 4) : LocalFrame Threefold.sheaf CanonicalForms (fixedOpen i) :=
  glueLocalFrames Threefold.sheaf CanonicalForms (fixedOpen i) (gOpen i)
    (gOpen_le i) (iSup_gOpen i).ge (gradientCanonicalFrame i) (gradient_generators_agree i)

theorem chartCanonicalFrame_generator (i : Fin 4) (O : Threefold.Opens)
    (hO : O ≤ fixedOpen i) :
    frameGenerator (chartCanonicalFrame i) O hO = orientedVolumeSection i O hO := by
  have hcover : O ≤ ⨆ j, O ⊓ gOpen i j := by
    rw [← inf_iSup_eq, iSup_gOpen]
    exact le_inf le_rfl hO
  apply CanonicalAdditiveSheaf.eq_of_locally_eq' (fun j => O ⊓ gOpen i j) O
    (fun _ => homOfLE inf_le_left) hcover
  intro j
  change CanonicalForms.val.map (homOfLE (show O ⊓ gOpen i j ≤ O from inf_le_left)).op
      (frameGenerator (chartCanonicalFrame i) O hO) =
    CanonicalForms.val.map (homOfLE (show O ⊓ gOpen i j ≤ O from inf_le_left)).op
      (orientedVolumeSection i O hO)
  rw [frameGenerator_naturality, orientedVolumeSection_restrict]
  exact (glueLocalFrames_generator Threefold.sheaf CanonicalForms (fixedOpen i) (gOpen i)
    (gOpen_le i) (iSup_gOpen i).ge (gradientCanonicalFrame i) (gradient_generators_agree i)
    j (O ⊓ gOpen i j) inf_le_right).trans
      (gradientCanonicalFrame_generator i j (O ⊓ gOpen i j) inf_le_right)

/-- On native forms the sheaf coordinate is exactly the original affine
`chartVolumeEquiv` coordinate, with the projective orientation retained. -/
theorem chartCanonicalFrame_native (i : Fin 4) (O : Threefold.Opens)
    (hO : O ≤ fixedOpen i) (ω : ⋀[T i]^3 (KaehlerDifferential ℂ (T i))) :
    (chartCanonicalFrame i).app O hO
      (chartExteriorSheafSection (fixedChart i).symm structureMap (chart_over i)
        3 (Over.mk (homOfLE hO)) ω) =
      chartSection (fixedChart i).symm (Over.mk (homOfLE hO))
        ((-1 : T i)^i.val * (chartVolumeEquiv i).symm ω) := by
  let c := (chartVolumeEquiv i).symm ω
  have hc : c • chartVolume i = ω := (chartVolumeEquiv i).apply_symm_apply ω
  have hs : (-1 : T i)^i.val * (-1 : T i)^i.val = 1 := by
    rw [← mul_pow]
    simp only [neg_mul_neg, one_mul, one_pow]
  have ho : ((-1 : T i)^i.val * c) • orientedChartVolume i = ω := by
    rw [orientedChartVolume, smul_smul]
    have he : ((-1 : T i)^i.val * c) * (-1 : T i)^i.val = c := by
      calc
        _ = ((-1 : T i)^i.val * (-1 : T i)^i.val) * c := by ring
        _ = c := by rw [hs, one_mul]
    rw [he]
    exact hc
  conv_lhs => rw [← ho]
  rw [map_smulₛₗ, map_smul]
  change _ * (chartCanonicalFrame i).app O hO (orientedVolumeSection i O hO) = _
  rw [← chartCanonicalFrame_generator]
  change _ * (chartCanonicalFrame i).app O hO
      (((chartCanonicalFrame i).app O hO).symm (1 : Γ(Threefold,O))) = _
  rw [LinearEquiv.apply_symm_apply, mul_one]

/-- The transition is an equality of the actual native oriented forms,
with the scalars carried through their semilinear restriction maps. -/
theorem orientedChartVolume_overlap (i : Fin 4) (k : Fin 3) :
    exteriorDifferentialMap (fixedTargetMap i k) 3
        (orientedChartVolume (i.succAbove k)) =
      exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ (T i) (FixedOverlap i k)) 3
        (orientedChartVolume i) := by
  simpa only [orientedChartVolume, map_smulₛₗ, map_pow, map_neg, map_one] using
    CycleQ2LiteralThreefoldResidueGluing.fixedChartVolume_overlap i k

/-- The native overlap equation gives equality in the genuine canonical
sheaf on every common subopen of the two whole coordinate charts. -/
theorem orientedVolumeSection_overlap (i : Fin 4) (k : Fin 3)
    (O : Threefold.Opens) (hO : O ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) :
    orientedVolumeSection (i.succAbove k) O (hO.trans inf_le_right) =
      orientedVolumeSection i O (hO.trans inf_le_left) := by
  let V : Over (fixedOpen i ⊓ fixedOpen (i.succAbove k)) := Over.mk (homOfLE hO)
  let r := chartExteriorSheafSection (overlapIso i k).symm structureMap
    (overlap_over i k) 3 V
  have ht := chartExteriorSheafSection_differentialMap
    (fixedChart (i.succAbove k)).symm (overlapIso i k).symm inf_le_right structureMap
    (chart_over (i.succAbove k)) (overlap_over i k) (fixedTargetMap i k)
    (by simpa only [Iso.symm_inv, ← Category.assoc, chartInclusion] using overlapIso_hom_ι_target i k)
    V 3 (orientedChartVolume (i.succAbove k))
  have hs := chartExteriorSheafSection_differentialMap
    (fixedChart i).symm (overlapIso i k).symm inf_le_left structureMap
    (chart_over i) (overlap_over i k) (IsScalarTower.toAlgHom ℂ (T i) (FixedOverlap i k))
    (by simpa only [Iso.symm_inv, ← Category.assoc, chartInclusion] using overlapIso_hom_ι i k)
    V 3 (orientedChartVolume i)
  exact ht.symm.trans ((congrArg r (orientedChartVolume_overlap i k)).trans hs)

private theorem chart_generators_agree (i j : Fin 4) :
    frameGenerator (chartCanonicalFrame i) (fixedOpen i ⊓ fixedOpen j) inf_le_left =
      frameGenerator (chartCanonicalFrame j) (fixedOpen i ⊓ fixedOpen j) inf_le_right := by
  rw [chartCanonicalFrame_generator, chartCanonicalFrame_generator]
  by_cases hij : i = j
  · subst j
    rfl
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
    exact (orientedVolumeSection_overlap i k _ le_rfl).symm

/-- The four actual chart frames glue to a canonical frame on every open
of the fixed threefold, by unique sheaf gluing. -/
def globalFrame : LocalFrame Threefold.sheaf CanonicalForms ⊤ :=
  glueLocalFrames Threefold.sheaf CanonicalForms ⊤ fixedOpen (fun _ => le_top)
    fixedOpen_cover.ge chartCanonicalFrame chart_generators_agree

theorem globalFrame_app_on_chart (i : Fin 4) (O : Threefold.Opens)
    (hO : O ≤ fixedOpen i) (s : CanonicalForms.val.obj (op O)) :
    globalFrame.app O le_top s = (chartCanonicalFrame i).app O hO s :=
  glueLocalFrames_app Threefold.sheaf CanonicalForms ⊤ fixedOpen (fun _ => le_top)
    fixedOpen_cover.ge chartCanonicalFrame chart_generators_agree i O hO s

theorem globalFrame_generator (i : Fin 4) (O : Threefold.Opens) (hO : O ≤ fixedOpen i) :
    frameGenerator globalFrame O le_top = orientedVolumeSection i O hO :=
  (glueLocalFrames_generator Threefold.sheaf CanonicalForms ⊤ fixedOpen (fun _ => le_top)
    fixedOpen_cover.ge chartCanonicalFrame chart_generators_agree i O hO).trans
      (chartCanonicalFrame_generator i O hO)

/-- The globally glued canonical three-form, as an actual global sheaf section. -/
def globalVolume : CanonicalForms.val.obj (op ⊤) := frameGenerator globalFrame ⊤ le_rfl

theorem globalVolume_restrict (i : Fin 4) (O : Threefold.Opens) (hO : O ≤ fixedOpen i) :
    CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op globalVolume =
      orientedVolumeSection i O hO :=
  (frameGenerator_naturality globalFrame (show O ≤ ⊤ from le_top) le_rfl).trans
    (globalFrame_generator i O hO)

/-- An actual isomorphism of module sheaves, not only a statement about
affine native forms or global sections. -/
def canonicalIso : CanonicalForms ≅ StructureModule :=
  CycleQ2GeometricModuleLocalIso.glueIso CanonicalForms StructureModule ⊤ ⊤ (by simp)
    globalFrame globalFrame (fun _ _ _ _ => rfl)

theorem canonicalIso_hom (O : Threefold.Opens) (s : CanonicalForms.val.obj (op O)) :
    canonicalIso.hom.val.app (op O) s = globalFrame.app O le_top s :=
  CycleQ2GeometricModuleLocalIso.glueIso_hom_app_of_leU CanonicalForms StructureModule
    ⊤ ⊤ (by simp) globalFrame globalFrame (fun _ _ _ _ => rfl) O le_top s

theorem canonicalIso_inv (O : Threefold.Opens) (a : Γ(Threefold,O)) :
    canonicalIso.inv.val.app (op O) a = (globalFrame.app O le_top).symm a :=
  CycleQ2GeometricModuleLocalIso.glueIso_inv_app_of_leU CanonicalForms StructureModule
    ⊤ ⊤ (by simp) globalFrame globalFrame (fun _ _ _ _ => rfl) O le_top a

theorem canonicalIso_hom_native (i : Fin 4) (O : Threefold.Opens)
    (hO : O ≤ fixedOpen i) (ω : ⋀[T i]^3 (KaehlerDifferential ℂ (T i))) :
    canonicalIso.hom.val.app (op O)
      (chartExteriorSheafSection (fixedChart i).symm structureMap (chart_over i)
        3 (Over.mk (homOfLE hO)) ω) =
      chartSection (fixedChart i).symm (Over.mk (homOfLE hO))
        ((-1 : T i)^i.val * (chartVolumeEquiv i).symm ω) := by
  rw [canonicalIso_hom, globalFrame_app_on_chart i O hO, chartCanonicalFrame_native]

theorem canonicalIso_inv_one : canonicalIso.inv.val.app (op ⊤) 1 = globalVolume :=
  canonicalIso_inv ⊤ 1

theorem canonicalIso_inv_on_chart (i : Fin 4) (O : Threefold.Opens)
    (hO : O ≤ fixedOpen i) (a : Γ(Threefold,O)) :
    canonicalIso.inv.val.app (op O) a = a • orientedVolumeSection i O hO := by
  rw [canonicalIso_inv, ← globalFrame_generator i O hO]
  change (globalFrame.app O le_top).symm a = a • (globalFrame.app O le_top).symm 1
  rw [← map_smul]
  exact congrArg (globalFrame.app O le_top).symm (mul_one a).symm

/-- Negating the global generator gives the coefficient-one convention
used by the original surface adjunction sequence. -/
def negativeGlobalFrame : LocalFrame Threefold.sheaf CanonicalForms ⊤ where
  app O hO :=
    { toFun := fun s => -(globalFrame.app O hO s)
      invFun := fun a => (globalFrame.app O hO).symm (-a)
      left_inv := fun s => by rw [neg_neg, LinearEquiv.symm_apply_apply]
      right_inv := fun a => by rw [LinearEquiv.apply_symm_apply, neg_neg]
      map_add' := fun s t => by rw [map_add, neg_add]
      map_smul' := fun a s => by rw [map_smul, smul_neg] }
  naturality hPO hO s := by
    change Threefold.presheaf.map (homOfLE hPO).op (-(globalFrame.app _ hO s)) =
      -(globalFrame.app _ (hPO.trans hO) (CanonicalForms.val.map (homOfLE hPO).op s))
    rw [map_neg, globalFrame.naturality]

theorem negativeGlobalFrame_generator (O : Threefold.Opens) :
    frameGenerator negativeGlobalFrame O le_top = -frameGenerator globalFrame O le_top :=
  (globalFrame.app O le_top).symm.map_neg 1

def negativeVolume : CanonicalForms.val.obj (op ⊤) :=
  frameGenerator negativeGlobalFrame ⊤ le_rfl

theorem negativeVolume_eq : negativeVolume = -globalVolume :=
  negativeGlobalFrame_generator ⊤

theorem negativeVolume_restrict (i : Fin 4) (O : Threefold.Opens) (hO : O ≤ fixedOpen i) :
    CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op negativeVolume =
      -orientedVolumeSection i O hO := by
  rw [negativeVolume_eq, map_neg, globalVolume_restrict i O hO]

/-- The corresponding genuine module-sheaf isomorphism has the negative
globally glued volume as its inverse-one section. -/
def negativeCanonicalIso : CanonicalForms ≅ StructureModule :=
  CycleQ2GeometricModuleLocalIso.glueIso CanonicalForms StructureModule ⊤ ⊤ (by simp)
    negativeGlobalFrame negativeGlobalFrame (fun _ _ _ _ => rfl)

theorem negativeCanonicalIso_inv (O : Threefold.Opens) (a : Γ(Threefold,O)) :
    negativeCanonicalIso.inv.val.app (op O) a = (globalFrame.app O le_top).symm (-a) :=
  CycleQ2GeometricModuleLocalIso.glueIso_inv_app_of_leU CanonicalForms StructureModule
    ⊤ ⊤ (by simp) negativeGlobalFrame negativeGlobalFrame (fun _ _ _ _ => rfl) O le_top a

theorem negativeCanonicalIso_inv_one :
    negativeCanonicalIso.inv.val.app (op ⊤) 1 = negativeVolume :=
  negativeCanonicalIso_inv ⊤ 1

theorem negativeCanonicalIso_inv_on_chart (i : Fin 4) (O : Threefold.Opens)
    (hO : O ≤ fixedOpen i) (a : Γ(Threefold,O)) :
    negativeCanonicalIso.inv.val.app (op O) a = -a • orientedVolumeSection i O hO := by
  rw [negativeCanonicalIso_inv]
  rw [← canonicalIso_inv]
  exact canonicalIso_inv_on_chart i O hO (-a)

/-- The surface signs `(+,−,+)` are the negatives of the projective
threefold signs on charts `1,2,3`, in every coefficient ring. -/
theorem surface_orientation (R : Type*) [CommRing R] (j : Fin 3) :
    (CycleQ2SurfaceCoordinateCubicFrames.orientation j : R) = -(-1 : R)^j.succ.val := by
  fin_cases j <;> norm_num [CycleQ2SurfaceCoordinateCubicFrames.orientation]

/-- The global frame with the surface convention restricts to exactly the
established surface orientation times the original native chart volume. -/
theorem negativeVolume_surface_chart (j : Fin 3) (O : Threefold.Opens)
    (hO : O ≤ fixedOpen j.succ) :
    CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op negativeVolume =
      chartExteriorSheafSection (fixedChart j.succ).symm structureMap (chart_over j.succ)
        3 (Over.mk (homOfLE hO))
          ((CycleQ2SurfaceCoordinateCubicFrames.orientation j : T j.succ) • chartVolume j.succ) := by
  rw [negativeVolume_restrict, surface_orientation]
  change -(chartExteriorSheafSection (fixedChart j.succ).symm structureMap (chart_over j.succ)
    3 (Over.mk (homOfLE hO)) ((-1 : T j.succ)^j.succ.val • chartVolume j.succ)) = _
  rw [neg_smul, map_neg]

end CycleQ2LiteralThreefoldCanonicalFrame
end

#print axioms CycleQ2LiteralThreefoldCanonicalFrame.chartCanonicalFrame_native
#print axioms CycleQ2LiteralThreefoldCanonicalFrame.globalVolume_restrict
#print axioms CycleQ2LiteralThreefoldCanonicalFrame.canonicalIso
#print axioms CycleQ2LiteralThreefoldCanonicalFrame.negativeCanonicalIso
#print axioms CycleQ2LiteralThreefoldCanonicalFrame.negativeVolume_surface_chart
