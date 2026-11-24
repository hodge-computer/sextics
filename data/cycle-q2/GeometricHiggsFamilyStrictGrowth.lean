import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Proposal.GeometricFermatHiggsInvertible
import Proposal.GeometricHiggsAlgebraSpecialization
import Proposal.GeometricUniversalJacobianMultiplication

set_option autoImplicit false

/-!
# A principal open with strict Jacobian Higgs growth

The normalized Fermat operators generate every matrix. A determinant
preserves this generation property across a principal open, and socle
pairing coordinates identify the matrices with Jacobian multiplication.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2HiggsFamilyStrictGrowth

open Matrix
open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation)
open CycleQ2HiggsFamilyGrading
open CycleQ2HiggsSocle (H H_seed)
open CycleQ2FermatHiggsInvertible (combined combined_map)
open CycleQ2HiggsNormalizedPair

private def matrices (m : Fin 35) : Matrix (Fin 33) (Fin 33) CoeffRing :=
  fun j i => H m j.rev i

private theorem matrices_seed (m : Fin 35) :
    (matrices m).map seedEvaluation = CycleQ2FermatStrictGrowth.ordered ℂ m := by
  apply Matrix.ext
  intro j i
  simp only [Matrix.map_apply, matrices, CycleQ2FermatStrictGrowth.ordered]
  have h := congrArg (fun X : Matrix (Fin 33) (Fin 33) ℂ => X j.rev i) (H_seed m)
  rw [Matrix.map_apply] at h
  rw [h]
  simp only [CycleQ2FermatHiggs.higgsMatrix,
    CycleQ2FermatHiggs.complement_symm m j.rev i]

private def normalized (m : Fin 35) : Matrix (Fin 33) (Fin 33) CoeffRing :=
  (combined matrices).adjugate * matrices m

private theorem normalized_map {K : Type} [Field K] (φ : CoeffRing →+* K) (m : Fin 35) :
    (normalized m).map φ =
      (combined (fun m => (matrices m).map φ)).adjugate * (matrices m).map φ := by
  have h : ((combined matrices).adjugate).map φ =
      ((combined matrices).map φ).adjugate := φ.map_adjugate (combined matrices)
  unfold normalized
  rw [Matrix.map_mul, h, combined_map]

private theorem det_seed :
    seedEvaluation (combined matrices).det ≠ 0 := by
  rw [RingHom.map_det]
  change ((combined matrices).map seedEvaluation).det ≠ 0
  rw [combined_map]
  simpa only [matrices_seed] using CycleQ2FermatHiggsInvertible.det_ne_zero ℂ

private theorem generates_seed :
    Algebra.adjoin ℂ (Set.range fun m => (normalized m).map seedEvaluation) = ⊤ := by
  simp only [normalized_map, matrices_seed]
  apply generated_eq_top
  · exact CycleQ2FermatHiggsInvertible.det_ne_zero ℂ
  · exact CycleQ2FermatStrictGrowth.stable_pair_trivial ℂ

private theorem sum_stable {K : Type} [Field K]
    (M : Fin 35 → Matrix (Fin 33) (Fin 33) K)
    (W V : Submodule K (Fin 33 → K))
    (h : ∀ m x, x ∈ W → M m *ᵥ x ∈ V) :
    ∀ x ∈ W, combined M *ᵥ x ∈ V := by
  intro x hx
  unfold combined
  generalize CycleQ2FermatHiggsInvertible.directions = ms
  induction ms with
  | nil => simp
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons, Matrix.add_mulVec]
    exact V.add_mem (h m x hx) ih

variable {K : Type} [Field K] (φ : CoeffRing →+* K)

private def lowerCoordinates (h : φ parameter ≠ 0) : Lower φ ≃ₗ[K] (Fin 33 → K) :=
  let L := LinearMap.pi fun j : Fin 33 => (pairing φ) (upperBasis φ h j.rev)
  LinearEquiv.ofInjectiveOfFinrankEq L
    (fun z z' he => by
      apply pairing_flip_injective φ h
      apply (upperBasis φ h).ext
      intro i
      simpa only [L, LinearMap.pi_apply, LinearMap.flip_apply, Fin.rev_rev] using
        congrFun he i.rev)
    (by rw [Module.finrank_eq_card_basis (lowerBasis φ h), Module.finrank_pi])

private theorem lowerCoordinates_apply (h : φ parameter ≠ 0) (z : Lower φ) (j : Fin 33) :
    lowerCoordinates φ h z j = pairing φ (upperBasis φ h j.rev) z := rfl

private theorem matrix_coordinates (h : φ parameter ≠ 0) (m : Fin 35) (x : Upper φ) :
    (matrices m).map φ *ᵥ (upperBasis φ h).equivFun x =
      lowerCoordinates φ h (higgs φ (tangentBasis φ h m) x) := by
  let lhs := ((matrices m).map φ).mulVecLin.comp (upperBasis φ h).equivFun.toLinearMap
  let rhs := (lowerCoordinates φ h).toLinearMap.comp (higgs φ (tangentBasis φ h m))
  have he : lhs = rhs := by
    apply (upperBasis φ h).ext
    intro i
    funext j
    change ((matrices m).map φ *ᵥ (upperBasis φ h).equivFun (upperBasis φ h i)) j = _
    change _ = lowerCoordinates φ h (higgs φ (tangentBasis φ h m) (upperBasis φ h i)) j
    rw [lowerCoordinates_apply, higgs_basis_entry φ h]
    change (∑ k, φ (H m j.rev k) * (upperBasis φ h).equivFun (upperBasis φ h i) k) = _
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · simp
  exact DFunLike.congr_fun he x

private theorem actual_pair (h : φ parameter ≠ 0)
    (hs : ∀ W V : Submodule K (Fin 33 → K),
      (∀ m x, x ∈ W → (matrices m).map φ *ᵥ x ∈ V) →
      Module.finrank K V ≤ Module.finrank K W →
        (W = ⊥ ∧ V = ⊥) ∨ (W = ⊤ ∧ V = ⊤))
    (U : Submodule K (Upper φ)) (V : Submodule K (Lower φ))
    (hmap : ∀ (t : Tangent φ) x, x ∈ U → higgs φ t x ∈ V)
    (hrank : Module.finrank K V ≤ Module.finrank K U) :
    (U = ⊥ ∧ V = ⊥) ∨ (U = ⊤ ∧ V = ⊤) := by
  let e := (upperBasis φ h).equivFun
  let f := lowerCoordinates φ h
  have he := hs (U.map e.toLinearMap) (V.map f.toLinearMap)
  have hm (m : Fin 35) (x : Fin 33 → K) (hx : x ∈ U.map e.toLinearMap) :
      (matrices m).map φ *ᵥ x ∈ V.map f.toLinearMap := by
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hx
    change (matrices m).map φ *ᵥ e u ∈ V.map f.toLinearMap
    rw [matrix_coordinates φ h]
    exact Submodule.mem_map.mpr ⟨_, hmap _ u hu, rfl⟩
  rcases he hm (by simpa only [LinearEquiv.finrank_map_eq] using hrank) with hz | hf
  · left
    exact ⟨(Submodule.map_injective_of_injective e.injective) (by simpa using hz.1),
      (Submodule.map_injective_of_injective f.injective) (by simpa using hz.2)⟩
  · right
    exact ⟨(Submodule.map_injective_of_injective e.injective) (by simpa using hf.1),
      (Submodule.map_injective_of_injective f.injective) (by simpa using hf.2)⟩

private theorem dense_of_seed_ne_zero (p : CoeffRing) (hp : seedEvaluation p ≠ 0) :
    Dense (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum CoeffRing)) := by
  apply PrimeSpectrum.isOpen_basicOpen.dense
  let point : PrimeSpectrum CoeffRing :=
    PrimeSpectrum.comap seedEvaluation ⟨⊥, Ideal.isPrime_bot⟩
  refine ⟨point, (PrimeSpectrum.mem_basicOpen _ _).mpr ?_⟩
  change seedEvaluation p ∉ (⊥ : Ideal ℂ)
  simpa only [Ideal.mem_bot] using hp

private theorem fiber_stable (h : φ parameter ≠ 0)
    (hd : φ (combined matrices).det ≠ 0)
    (hg : Algebra.adjoin K (Set.range fun m => (normalized m).map φ) = ⊤)
    (U : Submodule K (Upper φ)) (V : Submodule K (Lower φ))
    (hmap : ∀ (t : Tangent φ) x, x ∈ U → higgs φ t x ∈ V)
    (hrank : Module.finrank K V ≤ Module.finrank K U) :
    (U = ⊥ ∧ V = ⊥) ∨ (U = ⊤ ∧ V = ⊤) := by
  let M (m : Fin 35) := (matrices m).map φ
  have hdet : (combined M).det ≠ 0 := by
    rw [RingHom.map_det] at hd
    change ((combined matrices).map φ).det ≠ 0 at hd
    rwa [combined_map] at hd
  have hgen : Algebra.adjoin K (Set.range fun m => (combined M).adjugate * M m) = ⊤ := by
    have he : (fun m => (normalized m).map φ) = (fun m => (combined M).adjugate * M m) :=
      funext (normalized_map φ)
    rwa [he] at hg
  refine actual_pair φ h ?_ U V hmap hrank
  intro W V' hm hr
  exact stable_pair_of_generated_eq_top M (combined M) hdet hgen W V' hm
    (sum_stable M W V' hm) hr

/-- A single principal open containing Fermat has the strict-growth dichotomy
for actual multiplication in all field-valued Jacobian fibers. -/
theorem exists_parameter :
    ∃ p : CoeffRing, seedEvaluation p ≠ 0 ∧
      Dense (PrimeSpectrum.basicOpen p : Set (PrimeSpectrum CoeffRing)) ∧
      ∀ (K : Type) [Field K] (φ : CoeffRing →+* K), φ p ≠ 0 →
        ∀ (U : Submodule K (Upper φ)) (V : Submodule K (Lower φ)),
          (∀ (t : Tangent φ) x, x ∈ U → higgs φ t x ∈ V) →
          Module.finrank K V ≤ Module.finrank K U →
          (U = ⊥ ∧ V = ⊥) ∨ (U = ⊤ ∧ V = ⊤) := by
  have hsurj : Function.Surjective seedEvaluation :=
    fun z => ⟨MvPolynomial.C z, by simp [seedEvaluation]⟩
  obtain ⟨q, hq, hgen⟩ := CycleQ2HiggsAlgebraOpen.exists_generation_parameter
    normalized seedEvaluation hsurj generates_seed
  let p := parameter * (combined matrices).det * q
  have hSeed : seedEvaluation p ≠ 0 := by
    simp only [p, map_mul, parameter_seed, one_mul, hq, mul_one]
    exact det_seed
  refine ⟨p, hSeed, dense_of_seed_ne_zero p hSeed, ?_⟩
  intro K _ φ hp U V hmap hrank
  have h : (φ parameter ≠ 0 ∧ φ (combined matrices).det ≠ 0) ∧ φ q ≠ 0 := by
    simpa only [p, map_mul, mul_ne_zero_iff] using hp
  exact fiber_stable φ h.1.1 h.1.2 (hgen K φ h.2) U V hmap hrank

end CycleQ2HiggsFamilyStrictGrowth

#print axioms CycleQ2HiggsFamilyStrictGrowth.exists_parameter
