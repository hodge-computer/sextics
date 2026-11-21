import Proposal.GeometricLiteralThreefoldDeformedVolume
import Proposal.GeometricLiteralThreefoldResidueGluing

/-! Coordinate independence of the oriented relative residue of the first-order sextic.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldDeformedTransition

open Module MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldDeformedVolume
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldResidueMinors
  CycleQ2IncidenceDehomogenizedChart CycleQ2LiteralThreefoldResidueGluing
  CycleQ2ExteriorTopBaseChange
open scoped TensorProduct

section Conormal
variable {R : Type} [CommRing R] [Algebra ℂ R] (S : Type) [CommRing S] [Algebra R S]

private def ambientD (v : R) : S ⊗[R] KaehlerDifferential ℂ R :=
  (1 : S) ⊗ₜ[R] KaehlerDifferential.D ℂ R v

private theorem ambientD_mul (a b : R) :
    ambientD S (a*b) = algebraMap R S a • ambientD S b + algebraMap R S b • ambientD S a := by
  simp only [ambientD, Derivation.leibniz, TensorProduct.tmul_add, TensorProduct.tmul_smul,
    IsScalarTower.algebraMap_smul]

private theorem ambientD_polynomial (x : Index → R) (p : P) :
    ambientD S (aeval x p) = ∑ j : Fin 4,
      algebraMap R S (aeval x (pderiv (coordIndex j) p)) • restrictedDifferentials S x j := by
  rw [ambientD, differential_polynomial, TensorProduct.tmul_sum]
  rw [← Equiv.sum_comp coordIndex (fun j => (1 : S) ⊗ₜ[R]
    ((aeval x (pderiv j p)) • KaehlerDifferential.D ℂ R (aeval x (X j))))]
  simp only [TensorProduct.tmul_smul, IsScalarTower.algebraMap_smul, restrictedDifferentials, aeval_X]

private def row (i : Fin 4) (x : Index → R) (e : S) (j : Fin 4) : S :=
  algebraMap R S (aeval x (pderiv (coordIndex j) (seedF i))) -
    e * algebraMap R S (aeval x (pderiv (coordIndex j) (test i)))

private theorem row_sum (i : Fin 4) (x : Index → R) (e : S) :
    ∑ j, row S i x e j • restrictedDifferentials S x j =
      ambientD S (aeval x (seedF i)) - e • ambientD S (aeval x (test i)) := by
  rw [ambientD_polynomial, ambientD_polynomial, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  let a := algebraMap R S (aeval x (pderiv (coordIndex j) (seedF i)))
  let b := algebraMap R S (aeval x (pderiv (coordIndex j) (test i)))
  let m := restrictedDifferentials S x j
  exact (sub_smul a (e*b) m).trans (congrArg (fun z => a • m - z) (mul_smul e b m))

/-- The term coming from differentiating the coordinate factor cancels against
the test sextic, using the full equation F = ε B at the lifted point. -/
theorem row_change (i j : Fin 4) (x : Index → R) (t : R)
    (ht : t * linearValues i x j = 1) (e : S)
    (he : algebraMap R S (aeval x (seedF i)) = e * algebraMap R S (aeval x (test i))) :
    ∑ a, row S j (changedCoordinate i j x t) e a •
        restrictedDifferentials S (changedCoordinate i j x t) a =
      (algebraMap R S t)^6 • ∑ a, row S i x e a • restrictedDifferentials S x a := by
  rw [row_sum, row_sum,
    show aeval (changedCoordinate i j x t) (seedF j) = t^6 * aeval x (seedF i) from
      seedF_change i j x t ht,
    show aeval (changedCoordinate i j x t) (test j) = t^6 * aeval x (test i) from
      homogeneous_change i j x t ht _ test_homogeneous, ambientD_mul, ambientD_mul, he, map_pow]
  simp only [smul_add, smul_sub, mul_smul]
  rw [smul_comm e ((algebraMap R S t)^6)]
  abel

end Conormal

variable {S : Type} [CommRing S] [Algebra ℂ S]

private theorem map_aeval {R : Type} [CommRing R] [Algebra ℂ R] (h : R →ₐ[ℂ] Jet S)
    (x : Index → R) (p : P) : h (aeval x p) = aeval (fun a => h (x a)) p := by
  have e : h.comp (aeval x) = aeval (fun a => h (x a)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, aeval_X]
  exact AlgHom.congr_fun e p

private def overlapMap (k : Fin 3) (x : Index → Jet S) (hu : IsUnit (x (some k))) :
    AmbientOverlap k →ₐ[ℂ] Jet S :=
  IsLocalization.Away.liftAlgHom (X (some k) : P) (f := aeval x) (by simpa only [aeval_X] using hu)

private theorem overlapMap_x (k : Fin 3) (x : Index → Jet S) (hu : IsUnit (x (some k))) (a : Index) :
    overlapMap k x hu (overlapCoordinates k a) = x a :=
  (IsLocalization.Away.lift_eq (S := AmbientOverlap k) (g := (aeval x).toRingHom)
    (X (some k)) (by change IsUnit (aeval x (X (some k))); rwa [aeval_X]) (X a)).trans (aeval_X _ _)

private theorem overlapMap_inverse (k : Fin 3) (x : Index → Jet S) (hu : IsUnit (x (some k)))
    (u : Jet S) (h : u * x (some k) = 1) : overlapMap k x hu (overlapInverse k) = u := by
  apply hu.mul_right_cancel
  rw [h, ← overlapMap_x k x hu (some k), ← map_mul, overlapInverse_mul, map_one]

attribute [local instance] CycleQ2LiteralThreefoldDeformedVolume.dualAlgebra
  CycleQ2LiteralThreefoldDeformedVolume.dualTower

set_option maxHeartbeats 1200000 in
/-- Both oriented relative residues pull back to the same actual relative
Kähler three-form at a lifted point in a weight-one chart overlap. -/
theorem volume_change (i : Fin 4) (k : Fin 3) (x : Lift i S) (u : Jet S)
    (hu : u * linearValues i x.x (i.succAbove k) = 1)
    (f : T i →ₐ[ℂ] S) (hx : LiesOver x f) (g : T (i.succAbove k) →ₐ[ℂ] S)
    (hy : LiesOver (change x (i.succAbove k) u hu) g) :
    (-1 : Jet S)^(i.succAbove k).val • volume (change x _ u hu) g hy =
      (-1 : Jet S)^i.val • volume x f hx := by
  let j := i.succAbove k
  let y := change x j u hu
  have hi : u * x.x (some k) = 1 := by simpa only [linearValues, Fin.insertNth_apply_succAbove] using hu
  have hunit : IsUnit (x.x (some k)) := isUnit_iff_exists_inv'.mpr ⟨u, hi⟩
  let h := overlapMap k x.x hunit
  let : Algebra (AmbientOverlap k) (Jet S) := h.toRingHom.toAlgebra
  let : IsScalarTower ℂ (AmbientOverlap k) (Jet S) := IsScalarTower.of_algHom h
  let x₀ := overlapCoordinates k
  let u₀ := overlapInverse k
  let y₀ := changedCoordinate i j x₀ u₀
  have hₓ : (fun a => h (x₀ a)) = x.x := funext (overlapMap_x k x.x hunit)
  have hᵤ : h u₀ = u := overlapMap_inverse k x.x hunit u hi
  have hᵧ : (fun a => h (y₀ a)) = y.x := by
    funext a
    change h (changedCoordinate i j x₀ u₀ a) = changedCoordinate i j x.x u a
    rw [show h (changedCoordinate i j x₀ u₀ a) = _ from map_changedCoordinate h.toRingHom i j x₀ u₀ a]
    change changedCoordinate i j (fun a => h (x₀ a)) (h u₀) a = _
    rw [hₓ, hᵤ]
  let E := Jet S
  let b := (overlapBasis k).baseChange E
  let v := restrictedDifferentials E y₀
  let p := (KaehlerDifferential.map ℂ Dual E E).comp
    (KaehlerDifferential.mapBaseChange ℂ (AmbientOverlap k) E)
  have hb : ⇑b = restrictedDifferentials E x₀ := by
    funext a
    simp only [b, Basis.baseChange_apply, overlapBasis_apply]
    rfl
  have hpd (z : Index → AmbientOverlap k) (a : Fin 4) :
      p (restrictedDifferentials E z a) = KaehlerDifferential.D Dual E (h (z (coordIndex a))) := by
    simp only [p, restrictedDifferentials, LinearMap.comp_apply, KaehlerDifferential.mapBaseChange_tmul,
      KaehlerDifferential.map_D]
    let a₀ := h (z (coordIndex a))
    exact (congrArg (KaehlerDifferential.map ℂ Dual E E)
      (one_smul E (KaehlerDifferential.D ℂ E a₀))).trans (KaehlerDifferential.map_D ℂ Dual E E a₀)
  have hpb : p ∘ b = coordinateDifferential x := by
    rw [hb]
    funext a
    exact (hpd _ _).trans (congrArg (KaehlerDifferential.D Dual E) (congrFun hₓ _))
  have hpv : p ∘ v = coordinateDifferential y := by
    funext a
    exact (hpd _ _).trans (congrArg (KaehlerDifferential.D Dual E) (congrFun hᵧ _))
  have hrow (l : Fin 4) (z : Index → AmbientOverlap k) (w : Lift l S)
      (hw : (fun a => h (z a)) = w.x) :
      row E l z (epsilon S) = gradient w := by
    funext a
    change h (aeval z _) - epsilon S * h (aeval z _) = _
    simp only [map_aeval, hw, gradient]
  have hn : ∑ a, gradient y a • v a = u^6 • ∑ a, gradient x a • b a := by
    rw [hb, ← hrow j y₀ y hᵧ, ← hrow i x₀ x hₓ, ← hᵤ]
    apply row_change E i j x₀ u₀
    · simpa only [j, x₀, u₀, linearValues, Fin.insertNth_apply_succAbove] using overlapInverse_mul k
    · change h (aeval x₀ _) = epsilon S * h (aeval x₀ _)
      rw [map_aeval, map_aeval, hₓ]
      exact x.equation
  have hv : (-1 : E)^j.val * b.det v = u^6 * (-1 : E)^i.val := by
    have hw : (-1 : E)^j.val • exteriorPower.ιMulti E 4 v =
        u^6 • ((-1 : E)^i.val • exteriorPower.ιMulti E 4 b) := by
      rw [hb, ← hᵤ]
      exact orientedRestrictedVolume_change i k E
    have e := congrArg (topCoordinate b) hw
    simp only [map_smul, smul_eq_mul] at e
    rw [topCoordinate_basis, mul_one, topCoordinate_wedge] at e
    exact e
  obtain ⟨c,hc⟩ := gradient_bezout x f hx
  obtain ⟨c',hc'⟩ := gradient_bezout y g hy
  apply bezout_residue_change b p (gradient x) (gradient y) c c' hc hc' v (u^6) _ _
    ((isUnit_iff_exists_inv.mpr ⟨x.x (some k), hi⟩).pow 6) hv hn
  · change ∑ a, gradient x a • (p ∘ b) a = 0
    rw [hpb]
    exact conormal x
  · intro a
    rw [hpb]
    exact gradient_smul_volume x f hx a
  · intro a
    rw [hpv]
    exact gradient_smul_volume y g hy a

/-- The normalization appearing in the actual Kodaira–Spencer edge preserves
the oriented relative volume, before taking its infinitesimal coefficient. -/
theorem normalized_volume (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) :
    (-1 : Jet S)^(i.succAbove k).val • volume (normalizedLift i k g)
        (g.comp (fixedTargetMap i k)) (normalizedLift_fst i k g) =
      (-1 : Jet S)^i.val • volume (sourceLift i k g) (g.comp (sourceMap i k))
        (canonical_liesOver i (g.comp (sourceMap i k))) :=
  volume_change i k _ _ (sourceUnit_normalizes i k g) _ _ _ _

end CycleQ2LiteralThreefoldDeformedTransition
end

#print axioms CycleQ2LiteralThreefoldDeformedTransition.normalized_volume
