import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# An elementary flatness criterion over the dual numbers

For an arbitrary module over k[epsilon], with k a field, flatness is
equivalent to every element killed by epsilon being an epsilon multiple.
The proof uses the existing ideal trichotomy for the dual numbers and
the ideal-tensor criterion for flatness. No finite-generation assumption
on the module is needed.

This provides the algebraic criterion for first-order curve deformation;
it does not assert flatness over the full incidence parameter algebra.

Source-only draft: no elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2DualNumberFlatness

open scoped DualNumber TensorProduct
open TensorProduct

variable {k : Type} [Field k]

theorem eps_mul_eq_zero_iff (a : k[ε]) :
    (ε : k[ε]) * a = 0 ↔ ∃ b : k[ε], a = ε * b := by
  constructor
  · intro h
    have hs := congrArg TrivSqZeroExt.snd h
    have hf : a.fst = 0 := by
      simpa only [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps,
        zero_mul, one_mul, zero_add, TrivSqZeroExt.snd_zero] using hs
    exact DualNumber.fst_eq_zero_iff_eps_dvd.mp hf
  · rintro ⟨b, rfl⟩
    rw [← mul_assoc, DualNumber.eps_mul_eps, zero_mul]

variable (k) in
abbrev EpsIdeal := Ideal.span ({ε} : Set k[ε])

def epsIdealElement : EpsIdeal k :=
  ⟨ε, Ideal.subset_span (Set.mem_singleton ε)⟩

theorem eps_smul_epsIdealElement : (ε : k[ε]) • (epsIdealElement : EpsIdeal k) = 0 := by
  apply Subtype.ext
  exact DualNumber.eps_mul_eps

variable {M : Type} [AddCommGroup M] [Module k[ε] M]

/-- The one generator of the epsilon ideal also generates its tensor
product in the first variable. -/
theorem exists_eps_tmul (z : EpsIdeal k ⊗[k[ε]] M) :
    ∃ m : M, z = epsIdealElement ⊗ₜ[k[ε]] m := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a m =>
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp a.property
    have ha : a = b • (epsIdealElement : EpsIdeal k) := by
      apply Subtype.ext
      change a.val = b * ε
      rw [hb, mul_comm]
    refine ⟨b • m, ?_⟩
    rw [ha, TensorProduct.smul_tmul]
  | add z w hz hw =>
    obtain ⟨m, rfl⟩ := hz
    obtain ⟨n, rfl⟩ := hw
    exact ⟨m + n, (TensorProduct.tmul_add _ _ _).symm⟩

/-- Flatness supplies exactness at multiplication by epsilon. -/
theorem eps_smul_eq_zero_of_flat [Module.Flat k[ε] M] (m : M)
    (hm : (ε : k[ε]) • m = 0) : ∃ n : M, m = ε • n := by
  have hrel : ∑ _ : Unit, (ε : k[ε]) • m = 0 := by simpa using hm
  obtain ⟨n, a, z, ha, hz⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (f := fun _ : Unit => (ε : k[ε])) (x := fun _ : Unit => m) hrel
  have hb : ∀ j : Fin n, ∃ b : k[ε], a () j = ε * b := by
    intro j
    apply (eps_mul_eq_zero_iff (a () j)).mp
    simpa using hz j
  choose b hb using hb
  refine ⟨∑ j, b j • z j, ?_⟩
  calc
    m = ∑ j, a () j • z j := ha ()
    _ = ∑ j, (ε : k[ε]) • (b j • z j) := by simp only [hb, mul_smul]
    _ = (ε : k[ε]) • ∑ j, b j • z j := (Finset.smul_sum _ _ _).symm

/-- The epsilon-kernel condition suffices for actual module flatness. -/
theorem flat_of_eps_smul
    (h : ∀ m : M, (ε : k[ε]) • m = 0 → ∃ n : M, m = ε • n) :
    Module.Flat k[ε] M := by
  apply Module.Flat.iff_rTensor_injective'.mpr
  intro I
  rcases DualNumber.ideal_trichotomy I with rfl | rfl | rfl
  · intro x y _
    exact Subsingleton.elim x y
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨m, rfl⟩ := exists_eps_tmul z
    have hm : (ε : k[ε]) • m = 0 := by
      have he := congrArg (TensorProduct.lid k[ε] M) hz
      simpa only [LinearMap.rTensor_tmul, Submodule.subtype_apply,
        TensorProduct.lid_tmul, epsIdealElement, map_zero] using he
    obtain ⟨n, hn⟩ := h m hm
    rw [hn, ← TensorProduct.smul_tmul,
      eps_smul_epsIdealElement, TensorProduct.zero_tmul]
  · let e : (⊤ : Ideal k[ε]) ≃ₗ[k[ε]] k[ε] :=
      LinearEquiv.ofBijective (⊤ : Ideal k[ε]).subtype
        ⟨Subtype.val_injective, fun a => ⟨⟨a, trivial⟩, rfl⟩⟩
    exact (e.rTensor M).injective

theorem flat_iff_eps_smul :
    Module.Flat k[ε] M ↔
      ∀ m : M, (ε : k[ε]) • m = 0 → ∃ n : M, m = ε • n := by
  constructor
  · intro h
    letI := h
    exact eps_smul_eq_zero_of_flat
  · exact flat_of_eps_smul

end CycleQ2DualNumberFlatness

end

#print axioms CycleQ2DualNumberFlatness.eps_smul_eq_zero_of_flat
#print axioms CycleQ2DualNumberFlatness.flat_of_eps_smul
#print axioms CycleQ2DualNumberFlatness.flat_iff_eps_smul
