import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Recovering a Jacobian minor on a smooth section chart

For three equations in four variables, a smooth curve neighborhood forces a maximal
Jacobian minor to survive at the original prime. A principal open neighborhood suffices,
as required when the displayed one-row equation for a section uses a matrix pivot.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

noncomputable section

open TensorProduct KaehlerDifferential MvPolynomial
open AlgebraicGeometry CategoryTheory

namespace CycleQ2LiteralAbelJacobiSeedLiftConverse

section Presentation

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {ι σ : Type*} [Fintype ι] (P : Algebra.Presentation R S ι σ)
variable (K : Type*) [Field K] [Algebra S K]

def evaluatedJacobian : Matrix σ ι K :=
  fun r i => algebraMap S K (aeval P.val (pderiv i (P.relation r)))

private def directional (v : ι → K) (f : MvPolynomial ι R) : K :=
  ∑ i, algebraMap S K (aeval P.val (pderiv i f)) * v i

private theorem directional_add (v : ι → K) (f g : MvPolynomial ι R) :
    directional P K v (f + g) = directional P K v f + directional P K v g := by
  simp [directional, add_mul, Finset.sum_add_distrib]

private theorem directional_mul (v : ι → K) (f g : MvPolynomial ι R) :
    directional P K v (f * g) =
      algebraMap S K (aeval P.val f) * directional P K v g +
      algebraMap S K (aeval P.val g) * directional P K v f := by
  simp only [directional, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    add_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum]

private theorem directional_eq_zero (v : LinearMap.ker (evaluatedJacobian P K).mulVecLin)
    (f : MvPolynomial ι R) (hf : aeval P.val f = 0) : directional P K v f = 0 := by
  have hmem : f ∈ Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val]
    exact hf
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, rfl⟩ := hx
    exact congrFun v.property r
  | zero => simp [directional]
  | add x y hx hy hdx hdy =>
    have hx' := P.aeval_val_eq_zero (x := x) (by rw [← P.span_range_relation_eq_ker]; exact hx)
    have hy' := P.aeval_val_eq_zero (x := y) (by rw [← P.span_range_relation_eq_ker]; exact hy)
    simp [directional_add, hdx hx', hdy hy']
  | smul c x hx hdx =>
    have hx' := P.aeval_val_eq_zero (x := x) (by rw [← P.span_range_relation_eq_ker]; exact hx)
    change directional P K v (c * x) = 0
    simp [directional_mul, hx', hdx hx']

private theorem directional_congr (v : LinearMap.ker (evaluatedJacobian P K).mulVecLin)
    {f g : MvPolynomial ι R} (h : aeval P.val f = aeval P.val g) :
    directional P K v f = directional P K v g := by
  have hz := directional_eq_zero P K v (f - g) (by simp [h])
  simpa [directional, sub_mul, Finset.sum_sub_distrib, sub_eq_zero] using hz

variable [Algebra R K] [IsScalarTower R S K]

private def directionalDerivation (v : LinearMap.ker (evaluatedJacobian P K).mulVecLin) :
    Derivation R S K where
  toFun x := directional P K v (P.σ x)
  map_add' x y := by
    rw [← directional_add]
    apply directional_congr
    simp
  map_smul' r x := by
    have he : directional P K v (P.σ (r • x)) = directional P K v (C r * P.σ x) :=
      directional_congr P K v (by simp [Algebra.smul_def])
    change directional P K v (P.σ (r • x)) = r • directional P K v (P.σ x)
    rw [he, directional_mul]
    simp [directional, Algebra.smul_def, IsScalarTower.algebraMap_apply R S K]
  map_one_eq_zero' := by
    change directional P K v (P.σ 1) = 0
    rw [directional_congr P K v (f := P.σ 1) (g := 1) (by simp)]
    simp [directional]
  leibniz' x y := by
    change directional P K v (P.σ (x * y)) = x • directional P K v (P.σ y) + y • directional P K v (P.σ x)
    rw [directional_congr P K v (f := P.σ (x * y)) (g := P.σ x * P.σ y) (by simp)]
    simp [directional_mul, Algebra.smul_def]

def jacobianKernelToDerivation :
    LinearMap.ker (evaluatedJacobian P K).mulVecLin →ₗ[K] Derivation R S K where
  toFun := directionalDerivation P K
  map_add' v w := by
    ext x
    change directional P K (v.val + w.val) (P.σ x) = directional P K v.val (P.σ x) + directional P K w.val (P.σ x)
    simp [directional, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    ext x
    change directional P K (c • v.val) (P.σ x) = c • directional P K v.val (P.σ x)
    simp [directional, Finset.mul_sum, mul_left_comm]

theorem jacobianKernelToDerivation_injective :
    Function.Injective (jacobianKernelToDerivation P K) := by
  classical
  intro v w h
  apply Subtype.ext
  funext i
  have hv (a : LinearMap.ker (evaluatedJacobian P K).mulVecLin) :
      (jacobianKernelToDerivation P K a) (P.val i) = a.val i := by
    change directional P K a (P.σ (P.val i)) = _
    rw [directional_congr P K a (f := P.σ (P.val i)) (g := X i) (by simp)]
    simp [directional, pderiv_X, Pi.single_apply, apply_ite]
  exact (hv v).symm.trans ((congrArg (fun D : Derivation R S K => D (P.val i)) h).trans (hv w))

end Presentation

/-- A three-row matrix with four columns and tangent kernel of dimension at most
one admits an embedding of three columns defining an invertible minor. -/
private theorem exists_three_column_embedding_of_finrank_ker_le_one
    {K ι : Type*} [Field K] [Fintype ι] (hι : Fintype.card ι = 4)
    (A : Matrix (Fin 3) ι K)
    (h : Module.finrank K (LinearMap.ker A.mulVecLin) ≤ 1) :
    ∃ c : Fin 3 ↪ ι, (A.submatrix id c).det ≠ 0 := by
  classical
  have hrank : A.rank = 3 := by
    have hn := A.mulVecLin.finrank_range_add_finrank_ker
    change A.rank + Module.finrank K (LinearMap.ker A.mulVecLin) =
      Module.finrank K (ι → K) at hn
    have hr := A.rank_le_card_height
    simp only [Module.finrank_pi, hι, Fintype.card_fin] at hn hr
    omega
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.col
  let : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = 3 := by
    rw [← finrank_span_eq_card hli, hspan, ← A.rank_eq_finrank_span_cols, hrank]
  let e : Fin 3 ≃ κ := Fintype.equivOfCardEq (by simpa using hcard.symm)
  refine ⟨⟨a ∘ e, ha.comp e.injective⟩, ?_⟩
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_cols_iff_isUnit.mp
  exact hli.comp e e.injective

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {K : Type u} [Field K] [Algebra S K] [Algebra R K] [IsScalarTower R S K]

private def fiberKaehlerEquiv (T : Type u) [CommRing T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [Algebra T K] [IsScalarTower S T K] [Algebra.FormallyEtale S T] :
    K ⊗[S] Ω[S⁄R] ≃ₗ[K] K ⊗[T] Ω[T⁄R] :=
  (AlgebraTensorModule.cancelBaseChange S T K K _).symm ≪≫ₗ
    AlgebraTensorModule.congr (.refl K K) (tensorKaehlerEquivOfFormallyEtale R S T)

omit [Algebra R K] [IsScalarTower R S K] in
private theorem fiberKaehlerFinrank
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1) (algebraMap R S)) :
    Module.finrank K (K ⊗[S] Ω[S⁄R]) = 1 := by
  obtain ⟨U, hU, hstd⟩ := h
  obtain ⟨s, hsU, hs⟩ : ∃ s ∈ U, algebraMap S K s ≠ 0 := by
    by_contra! hbad
    have hle : Ideal.span U ≤ RingHom.ker (algebraMap S K) := Ideal.span_le.mpr hbad
    rw [hU, top_le_iff] at hle
    exact RingHom.ker_ne_top _ hle
  let T := Localization.Away s
  let φ : T →+* K := IsLocalization.Away.lift s (isUnit_iff_ne_zero.mpr hs)
  let : Algebra T K := φ.toAlgebra
  have : IsScalarTower S T K := .of_algebraMap_eq' (IsLocalization.Away.lift_comp s _).symm
  have : Nontrivial T := φ.domain_nontrivial
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 R T := by
    apply (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp
    rw [IsScalarTower.algebraMap_eq R S T]
    exact hstd _ hsU
  have : Algebra.IsStandardSmooth R T := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers s)
  have hT : Module.finrank T Ω[T⁄R] = 1 := by
    simp [Module.finrank, Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := R) (S := T) 1]
  rw [(fiberKaehlerEquiv (R := R) (S := S) (K := K) T).finrank_eq, Module.finrank_baseChange, hT]

private theorem tangentFinrank_of_fiberKaehlerFinrank
    (hK : Module.finrank K (K ⊗[S] Ω[S⁄R]) = 1) :
    Module.finrank K (Derivation R S K) = 1 := by
  have : Module.Finite K (K ⊗[S] Ω[S⁄R]) := Module.finite_of_finrank_eq_succ hK
  let d : (Ω[S⁄R] →ₗ[S] K) ≃ₗ[K] Derivation R S K :=
    { (linearMapEquivDerivation R S).toEquiv with
      map_add' := (linearMapEquivDerivation R S).map_add
      map_smul' := fun a f => by ext x; rfl }
  rw [← d.finrank_eq, (LinearMap.liftBaseChangeEquiv K).finrank_eq]
  exact Subspace.dual_finrank_eq.trans hK

/-- The tangent space to a presented chart has dimension one at a field-valued point
lying on an étale neighborhood of relative dimension one. -/
theorem tangentFinrank_of_smoothNeighborhood (T : Type u) [CommRing T] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] [Algebra T K] [IsScalarTower S T K]
    [Algebra.FormallyEtale S T]
    (h : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap R T)))) :
    Module.finrank K (Derivation R S K) = 1 := by
  apply tangentFinrank_of_fiberKaehlerFinrank
  rw [(fiberKaehlerEquiv (R := R) (S := S) (K := K) T).finrank_eq]
  apply fiberKaehlerFinrank
  exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp h


private theorem exists_minor_of_tangentFinrank {ι : Type*} [Fintype ι]
    (P : Algebra.Presentation R S ι (Fin 3)) (hι : Fintype.card ι = 4)
    (h : Module.finrank K (Derivation R S K) = 1) :
    ∃ c : Fin 3 ↪ ι, ((evaluatedJacobian P K).submatrix id c).det ≠ 0 := by
  have : Module.Finite K (Derivation R S K) := Module.finite_of_finrank_eq_succ h
  apply exists_three_column_embedding_of_finrank_ker_le_one hι
  exact (LinearMap.finrank_le_finrank_of_injective (jacobianKernelToDerivation_injective P K)).trans h.le

/-- The rank of the fiber of the differential module alone detects a nonzero minor
for three equations in four coordinates. -/
theorem exists_minor_of_fiberKaehlerFinrank {ι : Type*} [Fintype ι]
    (P : Algebra.Presentation R S ι (Fin 3)) (hι : Fintype.card ι = 4)
    (h : Module.finrank K (K ⊗[S] Ω[S⁄R]) = 1) :
    ∃ c : Fin 3 ↪ ι, ((evaluatedJacobian P K).submatrix id c).det ≠ 0 :=
  exists_minor_of_tangentFinrank P hι (tangentFinrank_of_fiberKaehlerFinrank h)

omit [Algebra R K] [IsScalarTower R S K] in
private theorem exists_minor_of_smooth_away {ι : Type*} [Fintype ι]
    (P : Algebra.Presentation R S ι (Fin 3)) (hι : Fintype.card ι = 4)
    (s : S) (hs : algebraMap S K s ≠ 0)
    (h : SmoothOfRelativeDimension 1 (Spec.map
      (CommRingCat.ofHom (algebraMap R (Localization.Away s))))) :
    ∃ c : Fin 3 ↪ ι, ((evaluatedJacobian P K).submatrix id c).det ≠ 0 := by
  let T := Localization.Away s
  let φ : T →+* K := IsLocalization.Away.lift s (isUnit_iff_ne_zero.mpr hs)
  let : Algebra T K := φ.toAlgebra
  have : IsScalarTower S T K := .of_algebraMap_eq' (IsLocalization.Away.lift_comp s _).symm
  let : Algebra R K := ((algebraMap S K).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S K := .of_algebraMap_eq' rfl
  have : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers s)
  exact exists_minor_of_tangentFinrank P hι
    (tangentFinrank_of_smoothNeighborhood (R := R) (S := S) (K := K) T h)

/-- On a principal open of a three-equation chart which is smooth of relative
dimension one, every prime in that open avoids a three-column Jacobian minor. -/
theorem exists_minor_notMem_of_smooth_away {ι : Type u} [Fintype ι]
    (v : Fin 3 → MvPolynomial ι R) (hι : Fintype.card ι = 4)
    (p : Ideal (MvPolynomial ι R ⧸ Ideal.span (Set.range v))) [p.IsPrime]
    (s : MvPolynomial ι R ⧸ Ideal.span (Set.range v)) (hs : s ∉ p)
    (h : SmoothOfRelativeDimension 1 (Spec.map
      (CommRingCat.ofHom (algebraMap R (Localization.Away s))))) :
    ∃ c : Fin 3 ↪ ι, Ideal.Quotient.mk (Ideal.span (Set.range v))
      (Matrix.of fun i j : Fin 3 => pderiv (c j) (v i)).det ∉ p := by
  let A := MvPolynomial ι R ⧸ Ideal.span (Set.range v)
  let P : Algebra.Presentation R A ι (Fin 3) := Algebra.Presentation.naive (v := v)
  obtain ⟨c, hc⟩ := exists_minor_of_smooth_away (K := p.ResidueField) P hι s
    (Ideal.algebraMap_residueField_eq_zero.not.mpr hs) h
  refine ⟨c, fun hmem => hc ?_⟩
  have he := Ideal.algebraMap_residueField_eq_zero.mpr hmem
  have hv : aeval P.val = Ideal.Quotient.mkₐ R (Ideal.span (Set.range v)) := by
    apply MvPolynomial.algHom_ext
    intro i
    exact MvPolynomial.aeval_X _ _
  rw [← he, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  change algebraMap A p.ResidueField (aeval P.val _) = algebraMap A p.ResidueField (Ideal.Quotient.mk _ _)
  exact congrArg (algebraMap A p.ResidueField) (DFunLike.congr_fun hv _)

#print axioms exists_minor_of_fiberKaehlerFinrank
#print axioms exists_minor_notMem_of_smooth_away

end CycleQ2LiteralAbelJacobiSeedLiftConverse
