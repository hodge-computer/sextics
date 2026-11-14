import Proposal.GeometricAffineCohomology
import Proposal.GeometricSurfaceCoordinates
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Tactic.Module
import Proposal.GeometricInverseIdealBasis
import Proposal.GeometricCartierNormalLift
import Proposal.GeometricLiteralCanonicalClass
import Proposal.GeometricDegreeOneCech
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CartierCechRefinement

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped BigOperators

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- The finite partition contraction for arbitrary module-valued numerators. -/
theorem finite_power_module_cocycle_exact {ι : Type} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤) (n : ℕ)
    (a : ι → ι → M)
    (hc : ∀ i j k, f k ^ n • a i j + f i ^ n • a j k = f j ^ n • a i k) :
    ∃ b : ι → M, ∀ i j, f j ^ n • b i - f i ^ n • b j = a i j := by
  classical
  obtain ⟨w, hw⟩ := CycleQ2GeometricAffineCohomology.finite_power_partition f hf n
  refine ⟨fun i => ∑ k, w k • a i k, fun i j => ?_⟩
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  calc
    ∑ k, (f j ^ n • w k • a i k - f i ^ n • w k • a j k) =
        ∑ k, w k • (f k ^ n • a i j) := by
      apply Finset.sum_congr rfl
      intro k _
      have hk : f j ^ n • a i k - f i ^ n • a j k = f k ^ n • a i j := by
        exact eq_sub_of_add_eq (hc i j k) |>.symm
      calc
        _ = w k • (f j ^ n • a i k - f i ^ n • a j k) := by module
        _ = _ := congrArg (fun x : M => w k • x) hk
    _ = (∑ k, w k * f k ^ n) • a i j := by
      simp only [Finset.sum_smul, mul_smul]
    _ = a i j := by rw [hw, one_smul]

abbrev Sections (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (U : Opens (PrimeSpectrum.Top R)) :=
  (structureSheafInType R M).obj.obj (op U)

def restrict {U V : Opens (PrimeSpectrum.Top R)} (h : V ≤ U) :
    Sections R M U →ₗ[R] Sections R M V :=
  ((structurePresheafInModuleCat R M).map (homOfLE h).op).hom

@[simp] theorem restrict_comp {U V W : Opens (PrimeSpectrum.Top R)}
    (hVU : V ≤ U) (hWV : W ≤ V) (s : Sections R M U) :
    restrict hWV (restrict hVU s) = restrict (hWV.trans hVU) s := rfl

@[simp] theorem restrict_toOpen {U V : Opens (PrimeSpectrum.Top R)}
    (h : V ≤ U) (m : M) :
    restrict h (StructureSheaf.toOpenₗ R M U m) = StructureSheaf.toOpenₗ R M V m := rfl

/-- A finite family of module sections admits one common denominator exponent. -/
theorem uniform_module_denominators {ι : Type} [Fintype ι]
    (f : ι → R) (s : ∀ i, Sections R M (PrimeSpectrum.basicOpen (f i))) :
    ∃ (n : ℕ) (a : ι → M), ∀ i,
      f i ^ n • s i = StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen (f i)) (a i) := by
  classical
  choose n a ha using fun i => IsLocalizedModule.Away.surj (r := f i)
    (f := StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen (f i))) (s i)
  let N := Finset.univ.sup n
  have hn (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N, fun i => f i ^ (N - n i) • a i, fun i => ?_⟩
  rw [map_smul, ← ha i, ← mul_smul, ← pow_add, Nat.sub_add_cancel (hn i)]

private theorem triple_le_left (x y z : R) :
    PrimeSpectrum.basicOpen ((x * y) * z) ≤ PrimeSpectrum.basicOpen (x * y) :=
  PrimeSpectrum.basicOpen_mul_le_left _ _

private theorem triple_le_right (x y z : R) :
    PrimeSpectrum.basicOpen ((x * y) * z) ≤ PrimeSpectrum.basicOpen (y * z) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf_right _ inf_le_right

private theorem triple_le_outer (x y z : R) :
    PrimeSpectrum.basicOpen ((x * y) * z) ≤ PrimeSpectrum.basicOpen (x * z) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf_right _ inf_le_left

def IsCocycle {ι : Type} (f : ι → R)
    (c : ∀ i j, Sections R M (PrimeSpectrum.basicOpen (f i * f j))) : Prop :=
  ∀ i j k,
    restrict (triple_le_left (f i) (f j) (f k)) (c i j) +
      restrict (triple_le_right (f i) (f j) (f k)) (c j k) =
    restrict (triple_le_outer (f i) (f j) (f k)) (c i k)

/-- Clear both denominator powers and localization torsion in an actual
module-valued cocycle. No torsion-freeness is required. -/
theorem cleared_module_cocycle {ι : Type} [Fintype ι] (f : ι → R)
    (c : ∀ i j, Sections R M (PrimeSpectrum.basicOpen (f i * f j)))
    (hc : IsCocycle f c) :
    ∃ (n : ℕ) (a : ι → ι → M),
      (∀ i j, (f i * f j) ^ n • c i j =
        StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen (f i * f j)) (a i j)) ∧
      (∀ i j k, f k ^ n • a i j + f i ^ n • a j k = f j ^ n • a i k) := by
  classical
  obtain ⟨N, a, ha⟩ := uniform_module_denominators
    (fun p : ι × ι => f p.1 * f p.2) (fun p => c p.1 p.2)
  have hloc (i j k : ι) :
      StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen ((f i * f j) * f k))
        (f k ^ N • a (i,j) + f i ^ N • a (j,k)) =
      StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen ((f i * f j) * f k))
        (f j ^ N • a (i,k)) := by
    have hij := congrArg (restrict (M := M) (triple_le_left (f i) (f j) (f k))) (ha (i,j))
    have hjk := congrArg (restrict (M := M) (triple_le_right (f i) (f j) (f k))) (ha (j,k))
    have hik := congrArg (restrict (M := M) (triple_le_outer (f i) (f j) (f k))) (ha (i,k))
    simp only [map_smul, restrict_toOpen] at hij hjk hik
    rw [map_add, map_smul, map_smul, map_smul, ← hij, ← hjk, ← hik]
    calc
      _ = ((f i * f j) * f k) ^ N •
          (restrict (triple_le_left (f i) (f j) (f k)) (c i j) +
           restrict (triple_le_right (f i) (f j) (f k)) (c j k)) := by
        simp only [mul_pow]
        module
      _ = ((f i * f j) * f k) ^ N •
          restrict (triple_le_outer (f i) (f j) (f k)) (c i k) :=
        congrArg (fun x => ((f i * f j) * f k) ^ N • x) (hc i j k)
      _ = _ := by simp only [mul_pow]; module
  choose m hm using fun i j k =>
    IsLocalizedModule.Away.exists_of_eq (r := (f i * f j) * f k) (hloc i j k)
  let K := Finset.univ.sup (fun p : ι × ι × ι => m p.1 p.2.1 p.2.2)
  have hK (i j k : ι) : m i j k ≤ K :=
    Finset.le_sup (f := fun p : ι × ι × ι => m p.1 p.2.1 p.2.2)
      (Finset.mem_univ (i,j,k))
  have heq (i j k : ι) :
      ((f i * f j) * f k) ^ K • (f k ^ N • a (i,j) + f i ^ N • a (j,k)) =
      ((f i * f j) * f k) ^ K • (f j ^ N • a (i,k)) := by
    calc
      _ = ((f i * f j) * f k) ^ (K - m i j k) •
          (((f i * f j) * f k) ^ m i j k •
            (f k ^ N • a (i,j) + f i ^ N • a (j,k))) := by
        rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (hK i j k)]
      _ = ((f i * f j) * f k) ^ (K - m i j k) •
          (((f i * f j) * f k) ^ m i j k • (f j ^ N • a (i,k))) := by
        rw [hm]
      _ = _ := by rw [← mul_smul, ← pow_add, Nat.sub_add_cancel (hK i j k)]
  refine ⟨N + K, fun i j => (f i * f j) ^ K • a (i,j), ?_, ?_⟩
  · intro i j
    rw [map_smul, ← ha (i,j), ← mul_smul, ← pow_add, add_comm K N]
  · intro i j k
    calc
      _ = ((f i * f j) * f k) ^ K •
          (f k ^ N • a (i,j) + f i ^ N • a (j,k)) := by
        simp only [pow_add, mul_pow]
        module
      _ = ((f i * f j) * f k) ^ K • (f j ^ N • a (i,k)) := heq i j k
      _ = _ := by simp only [pow_add, mul_pow]; module

/-- Every module-valued cocycle on a finite principal cover of an affine
spectrum has actual local primitives. -/
theorem finite_module_cocycle_exact {ι : Type} [Fintype ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (c : ∀ i j, Sections R M (PrimeSpectrum.basicOpen (f i * f j)))
    (hc : IsCocycle f c) :
    ∃ b : ∀ i, Sections R M (PrimeSpectrum.basicOpen (f i)), ∀ i j,
      restrict (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (b i) -
        restrict (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (b j) = c i j := by
  classical
  obtain ⟨N, a, ha, hc'⟩ := cleared_module_cocycle f c hc
  obtain ⟨b, hb⟩ := finite_power_module_cocycle_exact f hf N a hc'
  let s (i : ι) : Sections R M (PrimeSpectrum.basicOpen (f i)) :=
    IsLocalizedModule.mk' (S := Submonoid.powers (f i))
      (StructureSheaf.toOpenₗ R M _) (b i) ⟨f i ^ N, N, rfl⟩
  have hs (i : ι) : f i ^ N • s i = StructureSheaf.toOpenₗ R M _ (b i) :=
    IsLocalizedModule.mk'_cancel' (StructureSheaf.toOpenₗ R M _) (b i)
      (⟨f i ^ N, N, rfl⟩ : Submonoid.powers (f i))
  refine ⟨s, fun i j => ?_⟩
  have hi := congrArg (restrict (M := M) (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j))) (hs i)
  have hj := congrArg (restrict (M := M) (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j))) (hs j)
  simp only [map_smul, restrict_toOpen] at hi hj
  apply IsLocalizedModule.smul_injective (StructureSheaf.toOpenₗ R M _)
    (⟨(f i * f j) ^ N, N, rfl⟩ : Submonoid.powers (f i * f j))
  change (f i * f j) ^ N • (_ - _) = (f i * f j) ^ N • c i j
  calc
    _ = f j ^ N • (f i ^ N •
          restrict (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (s i)) -
        f i ^ N • (f j ^ N •
          restrict (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (s j)) := by
      simp only [mul_pow]
      module
    _ = StructureSheaf.toOpenₗ R M _ (f j ^ N • b i - f i ^ N • b j) := by
      rw [hi, hj, map_sub, map_smul, map_smul]
    _ = StructureSheaf.toOpenₗ R M _ (a i j) := by rw [hb]
    _ = _ := (ha i j).symm

/-- A radical containment gives a finite partition of a power of the
distinguished element after any common denominator exponent. -/
theorem finite_power_partition_of_radical {ι : Type} [Fintype ι]
    (f : ι → R) (t : R) (ht : t ∈ (Ideal.span (Set.range f)).radical) (n : ℕ) :
    ∃ (L : ℕ) (w : ι → R), ∑ i, w i * f i ^ n = t ^ L := by
  have hle : Ideal.span (Set.range f) ≤
      (Ideal.span (Set.range (fun i => f i ^ n))).radical := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨n, Ideal.subset_span ⟨i, rfl⟩⟩
  have ht' : t ∈ (Ideal.span (Set.range (fun i => f i ^ n))).radical :=
    (Ideal.radical_le_radical_iff.mpr hle) ht
  obtain ⟨L, hL⟩ := ht'
  obtain ⟨w, hw⟩ := (Ideal.mem_span_range_iff_exists_fun).mp hL
  exact ⟨L, w, hw⟩

private theorem weighted_cocycle_contraction {ι : Type} [Fintype ι]
    (f : ι → R) (n : ℕ) (a : ι → ι → M) (w : ι → R)
    (hc : ∀ i j k, f k ^ n • a i j + f i ^ n • a j k = f j ^ n • a i k) :
    ∀ i j, f j ^ n • (∑ k, w k • a i k) - f i ^ n • (∑ k, w k • a j k) =
      (∑ k, w k * f k ^ n) • a i j := by
  intro i j
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro k _
  have hk : f j ^ n • a i k - f i ^ n • a j k = f k ^ n • a i j :=
    (eq_sub_of_add_eq (hc i j k)).symm
  calc
    _ = w k • (f j ^ n • a i k - f i ^ n • a j k) := by module
    _ = w k • (f k ^ n • a i j) := congrArg (fun x : M => w k • x) hk
    _ = _ := by rw [mul_smul]

/-- A scalar invertible at every point of an open acts injectively on
the actual module sections of that open. -/
theorem section_smul_injective (t : R) (U : Opens (PrimeSpectrum.Top R))
    (hU : U ≤ PrimeSpectrum.basicOpen t) :
    Function.Injective (fun s : Sections R M U => t • s) := by
  intro s v h
  apply Subtype.ext
  funext x
  have hx := congrArg (fun z : Sections R M U => z.val x) h
  change t • s.val x = t • v.val x at hx
  exact IsLocalizedModule.smul_injective (LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl M)
    (⟨t, hU x.property⟩ : x.val.asIdeal.primeCompl) hx

/-- Module-valued affine Čech cancellation on an arbitrary principal
open, proved directly in the original ring's actual module sections. -/
theorem relative_finite_module_cocycle_exact {ι : Type} [Fintype ι]
    (f : ι → R) (t : R) (ht : t ∈ (Ideal.span (Set.range f)).radical)
    (hft : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ PrimeSpectrum.basicOpen t)
    (c : ∀ i j, Sections R M (PrimeSpectrum.basicOpen (f i * f j)))
    (hc : IsCocycle f c) :
    ∃ b : ∀ i, Sections R M (PrimeSpectrum.basicOpen (f i)), ∀ i j,
      restrict (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (b i) -
        restrict (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (b j) = c i j := by
  classical
  obtain ⟨N, a, ha, hc'⟩ := cleared_module_cocycle f c hc
  obtain ⟨L, w, hw⟩ := finite_power_partition_of_radical f t ht N
  let b (i : ι) : M := ∑ k, w k • a i k
  have hb (i j : ι) : f j ^ N • b i - f i ^ N • b j = t ^ L • a i j := by
    exact (weighted_cocycle_contraction f N a w hc' i j).trans (by rw [hw])
  have hden (i : ι) : PrimeSpectrum.basicOpen (f i) ≤
      PrimeSpectrum.basicOpen (t ^ L * f i ^ N) := by
    rw [PrimeSpectrum.basicOpen_mul]
    exact le_inf ((hft i).trans (PrimeSpectrum.le_basicOpen_pow t L))
      (PrimeSpectrum.le_basicOpen_pow (f i) N)
  let s (i : ι) : Sections R M (PrimeSpectrum.basicOpen (f i)) :=
    StructureSheaf.const (b i) (t ^ L * f i ^ N) _ (hden i)
  have hs (i : ι) : (t ^ L * f i ^ N) • s i = StructureSheaf.toOpenₗ R M _ (b i) := by
    rw [StructureSheaf.toOpenₗ_eq_const]
    change (t ^ L * f i ^ N) • StructureSheaf.const (b i) _ _ _ = _
    rw [StructureSheaf.smul_const]
    apply StructureSheaf.const_ext
    simp
  refine ⟨s, fun i j => ?_⟩
  have hi := congrArg (restrict (M := M) (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j))) (hs i)
  have hj := congrArg (restrict (M := M) (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j))) (hs j)
  simp only [map_smul, restrict_toOpen] at hi hj
  apply section_smul_injective (t ^ L * (f i * f j) ^ N) _
    (show PrimeSpectrum.basicOpen (f i * f j) ≤
      PrimeSpectrum.basicOpen (t ^ L * (f i * f j) ^ N) from by
      rw [PrimeSpectrum.basicOpen_mul (t ^ L) ((f i * f j) ^ N)]
      exact le_inf ((PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)).trans
        ((hft i).trans (PrimeSpectrum.le_basicOpen_pow t L)))
        (PrimeSpectrum.le_basicOpen_pow (f i * f j) N))
  calc
    _ = f j ^ N • ((t ^ L * f i ^ N) •
          restrict (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (s i)) -
        f i ^ N • ((t ^ L * f j ^ N) •
          restrict (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (s j)) := by
      simp only [mul_pow]
      module
    _ = StructureSheaf.toOpenₗ R M _ (f j ^ N • b i - f i ^ N • b j) := by
      rw [hi, hj, map_sub, map_smul, map_smul]
    _ = StructureSheaf.toOpenₗ R M _ (t ^ L • a i j) := by rw [hb]
    _ = t ^ L • ((f i * f j) ^ N • c i j) := by rw [map_smul, ← ha]
    _ = _ := (mul_smul (t ^ L) ((f i * f j) ^ N) (c i j)).symm

end CartierCechRefinement

namespace CartierCechCoverTransfer

open CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricSheafLocalIso

variable {X : TopCat} (F : AddSheaf X)
variable {ι κ : Type}

/-- Actual one-cochains with the cocycle identity on every common subopen.
The all-subopen form keeps restriction diagrams free of intersection casts. -/
structure OneCocycle (U : ι → Opens X) where
  val : ∀ i j, F.obj.obj (op (U i ⊓ U j))
  condition : ∀ (i j k : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k),
    res F (le_inf hi hj) (val i j) + res F (le_inf hj hk) (val j k) =
      res F (le_inf hi hk) (val i k)

def IsPrimitive {U : ι → Opens X} (c : OneCocycle F U)
    (q : ∀ i, F.obj.obj (op (U i))) : Prop :=
  ∀ (i j : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j),
    res F (le_inf hi hj) (c.val i j) = res F hj (q j) - res F hi (q i)

def FirstExact (U : ι → Opens X) : Prop :=
  ∀ c : OneCocycle F U, ∃ q, IsPrimitive F c q

def OneCocycle.on {U : ι → Opens X} (c : OneCocycle F U) (V : Opens X) :
    OneCocycle F (fun i => U i ⊓ V) where
  val i j := res F (le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans inf_le_left)) (c.val i j)
  condition i j k W hi hj hk := by
    simp only [res_comp]
    exact c.condition i j k W (hi.trans inf_le_left)
      (hj.trans inf_le_left) (hk.trans inf_le_left)

private theorem cover_by_inf (U : ι → Opens X) (W : Opens X) (h : W ≤ iSup U) :
    W ≤ ⨆ i, U i ⊓ W := by
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (h hx)
  exact Opens.mem_iSup.mpr ⟨i, hi, hx⟩

private theorem difference_equal {G : Type*} [AddCommGroup G] (a b c d : G)
    (h : b - a = d - c) : a - c = b - d := by
  have hb : b = d - c + a := sub_eq_iff_eq_add.mp h
  rw [hb]
  abel

/-- Degree-one Čech exactness transfers between covers of the same open
locus when the source cover is exact on each member of the target cover.
The proof is actual sheaf gluing on their common refinement. -/
theorem firstExact_of_common_refinement (U : ι → Opens X) (V : κ → Opens X)
    (hUV : ∀ i, U i ≤ iSup V) (hVU : ∀ j, V j ≤ iSup U)
    (hlocal : ∀ j, FirstExact F (fun i => U i ⊓ V j))
    (hV : FirstExact F V) : FirstExact F U := by
  intro c
  choose q hq using fun j => hlocal j (c.on F (V j))
  have hq' (j : κ) (i k : ι) (W : Opens X)
      (hi : W ≤ U i) (hk : W ≤ U k) (hj : W ≤ V j) :
      res F (le_inf hi hk) (c.val i k) =
        res F (le_inf hk hj) (q j k) - res F (le_inf hi hj) (q j i) := by
    have h := hq j i k W (le_inf hi hj) (le_inf hk hj)
    simpa only [OneCocycle.on, res_comp] using h
  let localDiff (j k : κ) (i : ι) : F.obj.obj (op (U i ⊓ (V j ⊓ V k))) :=
    res F (le_inf inf_le_left (inf_le_right.trans inf_le_right)) (q k i) -
      res F (le_inf inf_le_left (inf_le_right.trans inf_le_left)) (q j i)
  have hcompatible (j k : κ) :
      TopCat.Presheaf.IsCompatible F.obj (fun i => U i ⊓ (V j ⊓ V k)) (localDiff j k) := by
    intro i l
    change res F inf_le_left (localDiff j k i) = res F inf_le_right (localDiff j k l)
    simp only [localDiff, map_sub, res_comp]
    let W := (U i ⊓ (V j ⊓ V k)) ⊓ (U l ⊓ (V j ⊓ V k))
    have hi : W ≤ U i := inf_le_left.trans inf_le_left
    have hl : W ≤ U l := inf_le_right.trans inf_le_left
    have hj : W ≤ V j := inf_le_left.trans (inf_le_right.trans inf_le_left)
    have hk : W ≤ V k := inf_le_left.trans (inf_le_right.trans inf_le_right)
    exact difference_equal _ _ _ _ ((hq' k i l W hi hl hk).symm.trans (hq' j i l W hi hl hj))
  have hglue (j k : κ) :
      ∃ r : F.obj.obj (op (V j ⊓ V k)), ∀ i,
        res F inf_le_right r = localDiff j k i := by
    obtain ⟨r, hr, _⟩ := F.existsUnique_gluing'
      (fun i => U i ⊓ (V j ⊓ V k)) (V j ⊓ V k) (fun _ => homOfLE inf_le_right)
      (cover_by_inf U _ (inf_le_left.trans (hVU j))) (localDiff j k) (hcompatible j k)
    exact ⟨r, hr⟩
  choose r hr using hglue
  have hr' (j k : κ) (i : ι) (W : Opens X)
      (hi : W ≤ U i) (hj : W ≤ V j) (hk : W ≤ V k) :
      res F (le_inf hj hk) (r j k) =
        res F (le_inf hi hk) (q k i) - res F (le_inf hi hj) (q j i) := by
    have h := congrArg (res F (le_inf hi (le_inf hj hk))) (hr j k i)
    simpa only [localDiff, map_sub, res_comp] using h
  have rcondition (j k l : κ) (W : Opens X)
      (hj : W ≤ V j) (hk : W ≤ V k) (hl : W ≤ V l) :
      res F (le_inf hj hk) (r j k) + res F (le_inf hk hl) (r k l) =
        res F (le_inf hj hl) (r j l) := by
    apply F.eq_of_locally_eq' (fun i => U i ⊓ W) W
      (fun _ => homOfLE inf_le_right) (cover_by_inf U W (hj.trans (hVU j)))
    intro i
    change res F inf_le_right (_ + _) = res F inf_le_right _
    simp only [map_add, res_comp]
    rw [hr' j k i (U i ⊓ W) inf_le_left (inf_le_right.trans hj) (inf_le_right.trans hk),
      hr' k l i (U i ⊓ W) inf_le_left (inf_le_right.trans hk) (inf_le_right.trans hl),
      hr' j l i (U i ⊓ W) inf_le_left (inf_le_right.trans hj) (inf_le_right.trans hl)]
    abel
  let rc : OneCocycle F V := ⟨r, rcondition⟩
  obtain ⟨p, hp⟩ := hV rc
  let adjusted (i : ι) (j : κ) : F.obj.obj (op (U i ⊓ V j)) :=
    q j i - res F inf_le_right (p j)
  have hadjusted (i : ι) :
      TopCat.Presheaf.IsCompatible F.obj (fun j => U i ⊓ V j) (adjusted i) := by
    intro j k
    change res F inf_le_left (adjusted i j) = res F inf_le_right (adjusted i k)
    simp only [adjusted, map_sub, res_comp]
    let W := (U i ⊓ V j) ⊓ (U i ⊓ V k)
    have hi : W ≤ U i := inf_le_left.trans inf_le_left
    have hj : W ≤ V j := inf_le_left.trans inf_le_right
    have hk : W ≤ V k := inf_le_right.trans inf_le_right
    have h := (hr' j k i W hi hj hk).symm.trans (hp j k W hj hk)
    exact difference_equal _ _ _ _ h
  have haglue (i : ι) : ∃ a : F.obj.obj (op (U i)), ∀ j,
      res F inf_le_left a = adjusted i j := by
    obtain ⟨a, ha, _⟩ := F.existsUnique_gluing'
      (fun j => U i ⊓ V j) (U i) (fun _ => homOfLE inf_le_left)
      (by simpa only [inf_comm] using cover_by_inf V (U i) (hUV i))
      (adjusted i) (hadjusted i)
    exact ⟨a, ha⟩
  choose a ha using haglue
  refine ⟨a, ?_⟩
  intro i k W hi hk
  apply F.eq_of_locally_eq' (fun j => W ⊓ V j) W
    (fun _ => homOfLE inf_le_left)
    (by simpa only [inf_comm] using cover_by_inf V W (hi.trans (hUV i)))
  intro j
  change res F inf_le_left _ = res F inf_le_left (_ - _)
  simp only [map_sub, res_comp]
  have hia := congrArg (res F (le_inf (inf_le_left.trans hi) inf_le_right)) (ha i j)
  have hka := congrArg (res F (le_inf (inf_le_left.trans hk) inf_le_right)) (ha k j)
  simp only [adjusted, map_sub, res_comp] at hia hka
  rw [hia, hka]
  have h := hq' j i k (W ⊓ V j) (inf_le_left.trans hi) (inf_le_left.trans hk) inf_le_right
  exact h.trans (by abel)

end CartierCechCoverTransfer


namespace CartierCechModuleComparison

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricSheafLocalIso CartierCechCoverTransfer

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- The actual additive sheaf of sections of the module on its affine spectrum. -/
def moduleSheaf (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] :
    AddSheaf (PrimeSpectrum.Top R) :=
  ⟨structurePresheafInModuleCat R M ⋙ forget₂ (ModuleCat R) AddCommGrpCat,
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
      (structureSheafInType R M).property⟩

@[simp] theorem moduleSheaf_res {U V : Opens (PrimeSpectrum.Top R)}
    (h : V ≤ U) (s : CartierCechRefinement.Sections R M U) :
    res (moduleSheaf R M) h s = CartierCechRefinement.restrict h s := rfl

theorem basicOpen_le_iSup_iff {ι : Type} (f : ι → R) (t : R) :
    PrimeSpectrum.basicOpen t ≤ ⨆ i, PrimeSpectrum.basicOpen (f i) ↔
      t ∈ (Ideal.span (Set.range f)).radical := by
  constructor
  · intro h
    rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical,
      PrimeSpectrum.mem_vanishingIdeal]
    intro p hp
    by_contra ht
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (h ht)
    exact hi ((PrimeSpectrum.mem_zeroLocus p _).mp hp (Ideal.subset_span ⟨i,rfl⟩))
  · intro ht p hp
    by_contra h
    have hf : ∀ i, f i ∈ p.asIdeal := by
      intro i
      by_contra hi
      exact h (Opens.mem_iSup.mpr ⟨i, hi⟩)
    have hle : Ideal.span (Set.range f) ≤ p.asIdeal := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact hf i
    have hpprime : p.asIdeal.IsPrime := inferInstance
    exact hp ((hpprime.radical_le_iff.mpr hle) ht)

/-- Principal covers of an affine principal open are exact for the actual
module sheaf, in the all-subopen convention used by cover descent. -/
theorem firstExact_relative_principal {ι : Type} [Fintype ι]
    (f : ι → R) (t : R) (ht : t ∈ (Ideal.span (Set.range f)).radical)
    (hft : ∀ i, PrimeSpectrum.basicOpen (f i) ≤ PrimeSpectrum.basicOpen t) :
    FirstExact (moduleSheaf R M) (fun i => PrimeSpectrum.basicOpen (f i)) := by
  intro c
  let c' (i j : ι) : CartierCechRefinement.Sections R M
      (PrimeSpectrum.basicOpen (f i * f j)) :=
    CartierCechRefinement.restrict (PrimeSpectrum.basicOpen_mul (f i) (f j)).le (c.val i j)
  have hc' : CartierCechRefinement.IsCocycle f c' := by
    intro i j k
    let W := PrimeSpectrum.basicOpen ((f i * f j) * f k)
    have hi : W ≤ PrimeSpectrum.basicOpen (f i) := by
      dsimp only [W]
      exact (PrimeSpectrum.basicOpen_mul_le_left _ _).trans
        (PrimeSpectrum.basicOpen_mul_le_left _ _)
    have hj : W ≤ PrimeSpectrum.basicOpen (f j) := by
      dsimp only [W]
      exact (PrimeSpectrum.basicOpen_mul_le_left _ _).trans
        (PrimeSpectrum.basicOpen_mul_le_right _ _)
    have hk : W ≤ PrimeSpectrum.basicOpen (f k) :=
      PrimeSpectrum.basicOpen_mul_le_right _ _
    have h := c.condition i j k W hi hj hk
    simpa only [moduleSheaf_res, c', CartierCechRefinement.restrict_comp] using h
  obtain ⟨b, hb⟩ := CartierCechRefinement.relative_finite_module_cocycle_exact f t ht hft c' hc'
  refine ⟨fun i => -b i, ?_⟩
  intro i j W hi hj
  have hW : W ≤ PrimeSpectrum.basicOpen (f i * f j) :=
    (le_inf hi hj).trans (PrimeSpectrum.basicOpen_mul (f i) (f j)).ge
  have h := congrArg (CartierCechRefinement.restrict (M := M) hW) (hb i j)
  simp only [c', map_sub, CartierCechRefinement.restrict_comp] at h
  simp only [moduleSheaf_res, map_neg]
  exact h.symm.trans (by abel)

/-- First Čech exactness of a module is independent of the chosen finite
principal cover of the same punctured affine locus. -/
theorem firstExact_principal_of_radical_eq {ι κ : Type} [Fintype ι]
    (f : ι → R) (g : κ → R)
    (hfg : (Ideal.span (Set.range f)).radical = (Ideal.span (Set.range g)).radical)
    (hg : FirstExact (moduleSheaf R M) (fun j => PrimeSpectrum.basicOpen (g j))) :
    FirstExact (moduleSheaf R M) (fun i => PrimeSpectrum.basicOpen (f i)) := by
  have hUV (i : ι) : PrimeSpectrum.basicOpen (f i) ≤
      ⨆ j, PrimeSpectrum.basicOpen (g j) := by
    apply (basicOpen_le_iSup_iff g (f i)).mpr
    rw [← hfg]
    exact Ideal.le_radical (Ideal.subset_span ⟨i,rfl⟩)
  have hVU (j : κ) : PrimeSpectrum.basicOpen (g j) ≤
      ⨆ i, PrimeSpectrum.basicOpen (f i) := by
    apply (basicOpen_le_iSup_iff f (g j)).mpr
    rw [hfg]
    exact Ideal.le_radical (Ideal.subset_span ⟨j,rfl⟩)
  apply firstExact_of_common_refinement (moduleSheaf R M)
    (fun i => PrimeSpectrum.basicOpen (f i)) (fun j => PrimeSpectrum.basicOpen (g j)) hUV hVU
    (fun j => ?_) hg
  have hcover : PrimeSpectrum.basicOpen (g j) ≤
      ⨆ i, PrimeSpectrum.basicOpen (f i * g j) := by
    intro p hp
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hVU j hp)
    apply Opens.mem_iSup.mpr
    refine ⟨i, ?_⟩
    rw [PrimeSpectrum.basicOpen_mul]
    exact ⟨hi,hp⟩
  have ht := (basicOpen_le_iSup_iff (fun i => f i * g j) (g j)).mp hcover
  simpa only [PrimeSpectrum.basicOpen_mul] using
    (firstExact_relative_principal (M := M) (fun i => f i * g j) (g j) ht
      (fun i => PrimeSpectrum.basicOpen_mul_le_right (f i) (g j)))

end CartierCechModuleComparison

namespace CartierCechThree

open CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricSheafLocalIso CartierCechCoverTransfer

variable {X : TopCat} {F : AddSheaf X} {ι : Type} {U : ι → Opens X}

theorem diagonal (c : OneCocycle F U) (i : ι) (W : Opens X) (hi : W ≤ U i) :
    res F (le_inf hi hi) (c.val i i) = 0 :=
  add_eq_left.mp (c.condition i i i W hi hi hi)

theorem reverse (c : OneCocycle F U) (i j : ι) (W : Opens X)
    (hi : W ≤ U i) (hj : W ≤ U j) :
    res F (le_inf hj hi) (c.val j i) = -res F (le_inf hi hj) (c.val i j) := by
  have h := c.condition i j i W hi hj hi
  rw [diagonal c i W hi] at h
  exact eq_neg_of_add_eq_zero_right h

/-- Three ordered edge identities determine all nine identities of a
three-open cocycle, including its diagonal and reversed edges. -/
theorem isPrimitive_of_three_edges {V : Fin 3 → Opens X}
    (c : OneCocycle F V) (q : ∀ i, F.obj.obj (op (V i)))
    (h01 : ∀ (W : Opens X) (h0 : W ≤ V 0) (h1 : W ≤ V 1),
      res F (le_inf h0 h1) (c.val 0 1) = res F h1 (q 1) - res F h0 (q 0))
    (h02 : ∀ (W : Opens X) (h0 : W ≤ V 0) (h2 : W ≤ V 2),
      res F (le_inf h0 h2) (c.val 0 2) = res F h2 (q 2) - res F h0 (q 0))
    (h12 : ∀ (W : Opens X) (h1 : W ≤ V 1) (h2 : W ≤ V 2),
      res F (le_inf h1 h2) (c.val 1 2) = res F h2 (q 2) - res F h1 (q 1)) :
    IsPrimitive F c q := by
  intro i j W hi hj
  fin_cases i <;> fin_cases j
  · exact (diagonal c _ W hi).trans (sub_self _).symm
  · exact h01 W hi hj
  · exact h02 W hi hj
  · exact (reverse c _ _ W hj hi).trans ((congrArg Neg.neg (h01 W hj hi)).trans (neg_sub _ _))
  · exact (diagonal c _ W hi).trans (sub_self _).symm
  · exact h12 W hi hj
  · exact (reverse c _ _ W hj hi).trans ((congrArg Neg.neg (h02 W hj hi)).trans (neg_sub _ _))
  · exact (reverse c _ _ W hj hi).trans ((congrArg Neg.neg (h12 W hj hi)).trans (neg_sub _ _))
  · exact (diagonal c _ W hi).trans (sub_self _).symm

end CartierCechThree

namespace CartierCechCoordinates

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
open scoped TensorProduct

variable (k A M : Type) [CommRing k] [CommRing A] [Algebra (Base k) A]
  [AddCommGroup M] [Module A M] [Module (Base k) M] [IsScalarTower (Base k) A M]

abbrev coordinateOpen (s : Finset (Fin 3)) : Opens (PrimeSpectrum.Top A) :=
  PrimeSpectrum.basicOpen (algebraMap (Base k) A (baseProduct k s))

abbrev CoordinateSections (s : Finset (Fin 3)) :=
  CartierCechRefinement.Sections A M (coordinateOpen k A s)

@[instance_reducible] def sectionBaseModule (U : Opens (PrimeSpectrum.Top A)) :
    Module (Base k) (CartierCechRefinement.Sections A M U) :=
  Module.compHom _ (algebraMap (Base k) A)

attribute [local instance] sectionBaseModule

instance sectionBaseTower (U : Opens (PrimeSpectrum.Top A)) :
    IsScalarTower (Base k) A (CartierCechRefinement.Sections A M U) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def toCoordinateSections (s : Finset (Fin 3)) :
    M →ₗ[Base k] CoordinateSections k A M s :=
  (StructureSheaf.toOpenₗ A M (coordinateOpen k A s)).restrictScalars (Base k)

instance toCoordinateSections_localizes (s : Finset (Fin 3)) :
    IsLocalizedModule (Submonoid.powers (baseProduct k s)) (toCoordinateSections k A M s) :=
  IsLocalizedModule.restrictScalars_powers (baseProduct k s)
    (StructureSheaf.toOpenₗ A M (coordinateOpen k A s))

abbrev toCoordinateTensor (s : Finset (Fin 3)) :
    M →ₗ[Base k] CycleQ2GeometricFreeCoordinateCech.LocalModule k M s :=
  TensorProduct.mk (Base k) (coordinateLocalization k s) M 1

def coordinateSectionsEquiv (s : Finset (Fin 3)) :
    CycleQ2GeometricFreeCoordinateCech.LocalModule k M s ≃ₗ[Base k]
      CoordinateSections k A M s :=
  IsLocalizedModule.linearEquiv (Submonoid.powers (baseProduct k s))
    (toCoordinateTensor k M s) (toCoordinateSections k A M s)

@[simp] theorem coordinateSectionsEquiv_base (s : Finset (Fin 3)) (m : M) :
    coordinateSectionsEquiv k A M s (1 ⊗ₜ[Base k] m) = toCoordinateSections k A M s m :=
  IsLocalizedModule.linearEquiv_apply _ _ _ m

theorem coordinateOpen_mono {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    coordinateOpen k A t ≤ coordinateOpen k A s := by
  obtain ⟨c, hc⟩ := Finset.prod_dvd_prod_of_subset s t
    (fun i : Fin 3 => (MvPolynomial.X i : Base k)) hst
  change PrimeSpectrum.basicOpen (algebraMap (Base k) A (baseProduct k t)) ≤ _
  change baseProduct k t = baseProduct k s * c at hc
  rw [hc, map_mul]
  exact PrimeSpectrum.basicOpen_mul_le_left _ _

def coordinateSectionsRestriction {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    CoordinateSections k A M s →ₗ[Base k] CoordinateSections k A M t :=
  (CartierCechRefinement.restrict (M := M) (coordinateOpen_mono k A hst)).restrictScalars (Base k)

@[simp] theorem coordinateSectionsRestriction_base {s t : Finset (Fin 3)}
    (hst : s ⊆ t) (m : M) :
    coordinateSectionsRestriction k A M hst (toCoordinateSections k A M s m) =
      toCoordinateSections k A M t m := rfl

omit [Module (Base k) M] [IsScalarTower (Base k) A M] in
private theorem base_smul_injective (b : Base k) (U : Opens (PrimeSpectrum.Top A))
    (hU : U ≤ PrimeSpectrum.basicOpen (algebraMap (Base k) A b)) :
    Function.Injective (fun s : CartierCechRefinement.Sections A M U => b • s) :=
  CartierCechRefinement.section_smul_injective (algebraMap (Base k) A b) U hU

@[simp] theorem coordinateSectionsEquiv_restriction {s t : Finset (Fin 3)}
    (hst : s ⊆ t) (p : CycleQ2GeometricFreeCoordinateCech.LocalModule k M s) :
    coordinateSectionsRestriction k A M hst (coordinateSectionsEquiv k A M s p) =
      coordinateSectionsEquiv k A M t (CycleQ2GeometricFreeCoordinateCech.restriction k M hst p) := by
  obtain ⟨n, m, hm⟩ := IsLocalizedModule.Away.surj
    (r := baseProduct k s) (f := toCoordinateTensor k M s) p
  apply base_smul_injective k A M (baseProduct k s ^ n) (coordinateOpen k A t)
    (show coordinateOpen k A t ≤ PrimeSpectrum.basicOpen
      (algebraMap (Base k) A (baseProduct k s ^ n)) from by
      rw [map_pow]
      exact (coordinateOpen_mono k A hst).trans (PrimeSpectrum.le_basicOpen_pow _ n))
  calc
    _ = coordinateSectionsRestriction k A M hst
        (coordinateSectionsEquiv k A M s (baseProduct k s ^ n • p)) := by
      rw [map_smul, map_smul]
    _ = coordinateSectionsRestriction k A M hst (toCoordinateSections k A M s m) := by
      rw [hm]
      exact congrArg (coordinateSectionsRestriction k A M hst)
        (coordinateSectionsEquiv_base k A M s m)
    _ = toCoordinateSections k A M t m := coordinateSectionsRestriction_base k A M hst m
    _ = coordinateSectionsEquiv k A M t (1 ⊗ₜ[Base k] m) :=
      (coordinateSectionsEquiv_base k A M t m).symm
    _ = coordinateSectionsEquiv k A M t
        (CycleQ2GeometricFreeCoordinateCech.restriction k M hst (toCoordinateTensor k M s m)) := by
      simp only [CycleQ2GeometricFreeCoordinateCech.restriction, toCoordinateTensor,
        TensorProduct.mk_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        AlgHom.toLinearMap_apply, map_one]
    _ = coordinateSectionsEquiv k A M t
        (CycleQ2GeometricFreeCoordinateCech.restriction k M hst (baseProduct k s ^ n • p)) := by
      rw [hm]
    _ = _ := by rw [map_smul, map_smul]

end CartierCechCoordinates


namespace CartierCechCoordinates

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
open CartierCechCoverTransfer CartierCechModuleComparison
open CycleQ2GeometricSheafLocalIso
open scoped TensorProduct

variable (k A M : Type) [CommRing k] [CommRing A] [Algebra (Base k) A]
  [AddCommGroup M] [Module A M] [Module (Base k) M] [IsScalarTower (Base k) A M]

attribute [local instance] sectionBaseModule

abbrev coordinateFamily (i : Fin 3) := coordinateOpen k A {i}

theorem coordinateOpen_pair (i j : Fin 3) :
    coordinateOpen k A {i,j} = coordinateFamily k A i ⊓ coordinateFamily k A j := by
  classical
  by_cases h : i = j
  · subst j
    simp only [Finset.insert_eq_of_mem, Finset.mem_singleton, coordinateFamily, inf_idem]
  · simp [coordinateOpen, coordinateFamily, baseProduct, h, map_mul, PrimeSpectrum.basicOpen_mul]

def pairSection (c : OneCocycle (moduleSheaf A M) (coordinateFamily k A)) (i j : Fin 3) :
    CoordinateSections k A M {i,j} :=
  CartierCechRefinement.restrict (coordinateOpen_pair k A i j).le (c.val i j)

def pairTensor (c : OneCocycle (moduleSheaf A M) (coordinateFamily k A)) (i j : Fin 3) :
    CycleQ2GeometricFreeCoordinateCech.LocalModule k M {i,j} :=
  (coordinateSectionsEquiv k A M {i,j}).symm (pairSection k A M c i j)

theorem pairTensor_primitive
    (c : OneCocycle (moduleSheaf A M) (coordinateFamily k A)) (i j : Fin 3)
    (qi : CycleQ2GeometricFreeCoordinateCech.LocalModule k M {i})
    (qj : CycleQ2GeometricFreeCoordinateCech.LocalModule k M {j})
    (h : pairTensor k A M c i j =
      CycleQ2GeometricFreeCoordinateCech.restriction k M
        (show ({j} : Finset (Fin 3)) ⊆ {i,j} by simp) qj -
      CycleQ2GeometricFreeCoordinateCech.restriction k M
        (show ({i} : Finset (Fin 3)) ⊆ {i,j} by simp) qi)
    (W : Opens (PrimeSpectrum.Top A)) (hi : W ≤ coordinateFamily k A i)
    (hj : W ≤ coordinateFamily k A j) :
    res (moduleSheaf A M) (le_inf hi hj) (c.val i j) =
      res (moduleSheaf A M) hj (coordinateSectionsEquiv k A M {j} qj) -
        res (moduleSheaf A M) hi (coordinateSectionsEquiv k A M {i} qi) := by
  have h' := congrArg (coordinateSectionsEquiv k A M {i,j}) h
  simp only [pairTensor, LinearEquiv.apply_symm_apply, map_sub,
    ← coordinateSectionsEquiv_restriction] at h'
  have hW : W ≤ coordinateOpen k A {i,j} :=
    (le_inf hi hj).trans (coordinateOpen_pair k A i j).ge
  have h'' := congrArg (CartierCechRefinement.restrict (M := M) hW) h'
  simpa only [pairSection, coordinateSectionsRestriction, LinearMap.restrictScalars_apply,
    map_sub, CartierCechRefinement.restrict_comp, moduleSheaf_res] using h''

/-- A finite basis over the three-coordinate polynomial ring gives first
Čech exactness of the actual module sheaf on the three coordinate opens. -/
theorem coordinate_firstExact {η : Type} [Fintype η] [DecidableEq η]
    (b : Module.Basis η (Base k) M) :
    FirstExact (moduleSheaf A M) (coordinateFamily k A) := by
  intro c
  let p01 := pairTensor k A M c 0 1
  let p02 := pairTensor k A M c 0 2
  let p12 := pairTensor k A M c 1 2
  have hres (i j : Fin 3) :
      coordinateSectionsEquiv k A M Finset.univ
        (CycleQ2GeometricFreeCoordinateCech.restriction k M
          (Finset.subset_univ {i,j}) (pairTensor k A M c i j)) =
      res (moduleSheaf A M)
        (le_inf (coordinateOpen_mono k A (Finset.subset_univ {i}))
          (coordinateOpen_mono k A (Finset.subset_univ {j}))) (c.val i j) := by
    rw [← coordinateSectionsEquiv_restriction]
    simp only [pairTensor, LinearEquiv.apply_symm_apply]
    rfl
  have hc : CycleQ2GeometricFreeCoordinateCech.restriction k M
      (show ({0,1} : Finset (Fin 3)) ⊆ Finset.univ by simp) p01 -
      CycleQ2GeometricFreeCoordinateCech.restriction k M
      (show ({0,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p02 +
      CycleQ2GeometricFreeCoordinateCech.restriction k M
      (show ({1,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p12 = 0 := by
    apply (coordinateSectionsEquiv k A M Finset.univ).injective
    simp only [map_add, map_sub, map_zero, p01, p02, p12, hres]
    have h := c.condition 0 1 2 (coordinateOpen k A Finset.univ)
      (coordinateOpen_mono k A (Finset.subset_univ {0}))
      (coordinateOpen_mono k A (Finset.subset_univ {1}))
      (coordinateOpen_mono k A (Finset.subset_univ {2}))
    calc
      _ = (res (moduleSheaf A M) _ (c.val 0 1) +
          res (moduleSheaf A M) _ (c.val 1 2)) -
          res (moduleSheaf A M) _ (c.val 0 2) := by abel
      _ = 0 := by rw [h, sub_self]
  obtain ⟨q0, q1, q2, h01, h02, h12⟩ :=
    CycleQ2GeometricFreeCoordinateCech.firstCech_exact b p01 p02 p12 hc
  let q : ∀ i : Fin 3, (moduleSheaf A M).obj.obj (op (coordinateFamily k A i)) :=
    Fin.cases (coordinateSectionsEquiv k A M {0} q0)
      (Fin.cases (coordinateSectionsEquiv k A M {1} q1)
        (Fin.cases (coordinateSectionsEquiv k A M {2} q2) (fun z => Fin.elim0 z)))
  refine ⟨q, CartierCechThree.isPrimitive_of_three_edges c q ?_ ?_ ?_⟩
  · intro W h0 h1
    exact pairTensor_primitive k A M c 0 1 q0 q1 h01 W h0 h1
  · intro W h0 h2
    exact pairTensor_primitive k A M c 0 2 q0 q2 h02 W h0 h2
  · intro W h1 h2
    exact pairTensor_primitive k A M c 1 2 q1 q2 h12 W h1 h2

end CartierCechCoordinates


namespace CartierCechCoordinates

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
open CartierCechCoverTransfer CartierCechModuleComparison

variable (k A M : Type) [CommRing k] [CommRing A] [Algebra (Base k) A]
  [AddCommGroup M] [Module A M] [Module (Base k) M] [IsScalarTower (Base k) A M]

/-- Exactness on any finite principal cover of the coordinate-punctured
locus, from an actual polynomial-base basis and the actual radical equality. -/
theorem principal_firstExact_of_polynomial_basis {ι η : Type}
    [Fintype ι] [Fintype η] [DecidableEq η]
    (b : Module.Basis η (Base k) M) (f : ι → A)
    (hfg : (Ideal.span (Set.range f)).radical =
      (Ideal.span (Set.range (fun i : Fin 3 =>
        algebraMap (Base k) A (MvPolynomial.X i)))).radical) :
    FirstExact (moduleSheaf A M) (fun i => PrimeSpectrum.basicOpen (f i)) := by
  apply firstExact_principal_of_radical_eq f
    (fun i : Fin 3 => algebraMap (Base k) A (MvPolynomial.X i)) hfg
  have hfamily : coordinateFamily k A =
      (fun i : Fin 3 => PrimeSpectrum.basicOpen (algebraMap (Base k) A (MvPolynomial.X i))) := by
    funext i
    simp only [coordinateFamily, coordinateOpen, baseProduct, Finset.prod_singleton]
  exact (congrArg (FirstExact (moduleSheaf A M)) hfamily).mp
    (coordinate_firstExact k A M b)

end CartierCechCoordinates

end
end


section

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open scoped TensorProduct
namespace CycleQ2InverseIdealBaseLocalization
open CycleQ2GeometricLocalizedInverseIdeal

section BaseTensor
variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
variable (r : B) (U : Type*) [CommRing U] [Algebra A U] [Algebra B U]
variable [IsScalarTower B A U] [IsLocalization (Submonoid.powers (algebraMap B A r)) U]
variable (I : Ideal A) [Module.FinitePresentation A I]

/-- The coordinate-base tensor model is the actual localized inverse ideal. -/
def baseLocalizedInverseIdealEquiv :
    Localization.Away r ⊗[B] (I →ₗ[A] A) ≃ₗ[B] LocalInverseIdeal U I := by
  letI := IsLocalizedModule.restrictScalars_powers r
    (localizedInverseIdealMap (Submonoid.powers (algebraMap B A r)) U I)
  exact IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (TensorProduct.mk B (Localization.Away r) (I →ₗ[A] A) 1)
    ((localizedInverseIdealMap (Submonoid.powers (algebraMap B A r)) U I).restrictScalars B)

@[simp] theorem baseLocalizedInverseIdealEquiv_original (ν : I →ₗ[A] A) :
    baseLocalizedInverseIdealEquiv r U I (1 ⊗ₜ[B] ν) =
      localizedInverseIdealMap (Submonoid.powers (algebraMap B A r)) U I ν := by
  let := IsLocalizedModule.restrictScalars_powers r
    (localizedInverseIdealMap (Submonoid.powers (algebraMap B A r)) U I)
  exact IsLocalizedModule.linearEquiv_apply (Submonoid.powers r)
    (TensorProduct.mk B (Localization.Away r) (I →ₗ[A] A) 1) _ ν

theorem baseLocalizedInverseIdealEquiv_eval (ν : I →ₗ[A] A) (x : I) :
    baseLocalizedInverseIdealEquiv r U I (1 ⊗ₜ[B] ν) (Algebra.idealMap U I x) =
      algebraMap A U (ν x) := by
  rw [baseLocalizedInverseIdealEquiv_original, localizedInverseIdealMap_eval]

end BaseTensor

section Restrictions
variable {A : Type*} [CommRing A]
variable (S : Submonoid A) (U : Type*) [CommRing U] [Algebra A U] [IsLocalization S U]
variable (I : Ideal A) [Module.FinitePresentation A I]
variable (T : Submonoid A) (V : Type*) [CommRing V] [Algebra A V] [IsLocalization T V]

omit [Module.FinitePresentation A I] in
theorem localInverseIdeal_scalar_unit (z : A) (hz : IsUnit (algebraMap A V z)) :
    IsUnit (algebraMap A (Module.End A (LocalInverseIdeal V I)) z) := by
  rw [← (Algebra.lsmul A A (LocalInverseIdeal V I) (A := V)).commutes]
  exact hz.map (Algebra.lsmul A A (LocalInverseIdeal V I) (A := V)).toRingHom

/-- Canonical inverse-ideal restriction when source denominators become units.
This includes products of cover generators; it does not require powers of
one product to be contained in the powers of another. -/
def inverseIdealRestrictionByUnits
    (hS : ∀ s : S, IsUnit (algebraMap A V (s : A))) :
    LocalInverseIdeal U I →ₗ[A] LocalInverseIdeal V I :=
  IsLocalizedModule.lift S (localizedInverseIdealMap S U I) (localizedInverseIdealMap T V I)
    (fun s => localInverseIdeal_scalar_unit I V s (hS s))

@[simp] theorem inverseIdealRestrictionByUnits_original
    (hS : ∀ s : S, IsUnit (algebraMap A V (s : A))) (ν : I →ₗ[A] A) :
    inverseIdealRestrictionByUnits S U I T V hS (localizedInverseIdealMap S U I ν) =
      localizedInverseIdealMap T V I ν := by
  apply IsLocalizedModule.lift_apply

/-- Restriction preserves evaluation through the actual localization algebra map. -/
theorem inverseIdealRestrictionByUnits_eval
    (hS : ∀ s : S, IsUnit (algebraMap A V (s : A))) (ρ : U →ₐ[A] V)
    (ν : LocalInverseIdeal U I) (x : I) :
    inverseIdealRestrictionByUnits S U I T V hS ν (Algebra.idealMap V I x) =
      ρ (ν (Algebra.idealMap U I x)) := by
  obtain ⟨⟨μ, s⟩, hμ⟩ := IsLocalizedModule.surj S (localizedInverseIdealMap S U I) ν
  change (s : A) • ν = localizedInverseIdealMap S U I μ at hμ
  let res := inverseIdealRestrictionByUnits S U I T V hS
  have hleft : (s : A) • res ν = localizedInverseIdealMap T V I μ := by
    rw [← res.map_smul, hμ]
    exact inverseIdealRestrictionByUnits_original S U I T V hS μ
  have hl := congrArg (fun η : LocalInverseIdeal V I => η (Algebra.idealMap V I x)) hleft
  have hr := congrArg (fun η : LocalInverseIdeal U I => η (Algebra.idealMap U I x)) hμ
  simp only [LinearMap.smul_apply, Algebra.smul_def] at hl hr
  change algebraMap A V (s : A) * res ν (Algebra.idealMap V I x) =
    localizedInverseIdealMap T V I μ (Algebra.idealMap V I x) at hl
  change algebraMap A U (s : A) * ν (Algebra.idealMap U I x) =
    localizedInverseIdealMap S U I μ (Algebra.idealMap U I x) at hr
  rw [localizedInverseIdealMap_eval] at hl hr
  apply (hS s).mul_left_cancel
  change algebraMap A V (s : A) * res ν (Algebra.idealMap V I x) = _
  rw [hl, ← ρ.commutes (μ x), ← hr, map_mul, ρ.commutes]

variable (W : Submonoid A) (Z : Type*) [CommRing Z] [Algebra A Z] [IsLocalization W Z]

theorem inverseIdealRestrictionByUnits_comp
    (hST : ∀ s : S, IsUnit (algebraMap A V (s : A)))
    (hTW : ∀ t : T, IsUnit (algebraMap A Z (t : A)))
    (hSW : ∀ s : S, IsUnit (algebraMap A Z (s : A))) :
    (inverseIdealRestrictionByUnits T V I W Z hTW).comp
      (inverseIdealRestrictionByUnits S U I T V hST) =
        inverseIdealRestrictionByUnits S U I W Z hSW := by
  apply IsLocalizedModule.ext S (localizedInverseIdealMap S U I)
    (fun s => localInverseIdeal_scalar_unit I Z s (hSW s))
  ext ν
  simp only [LinearMap.comp_apply, inverseIdealRestrictionByUnits_original]

end Restrictions

#print axioms baseLocalizedInverseIdealEquiv
#print axioms baseLocalizedInverseIdealEquiv_eval
#print axioms inverseIdealRestrictionByUnits_eval
#print axioms inverseIdealRestrictionByUnits_comp

end CycleQ2InverseIdealBaseLocalization
end

end


section

/-!
The actual four-open inverse-ideal Cech cochains, the Cartier lift identity,
and reduction to the already fixed surface-relative normal cochain.
All local modules are Hom modules of the actual localized curve ideal.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
open scoped TensorProduct

namespace CycleQ2CartierInverseIdealCech

open CycleQ2GeometricCartierNormalLift CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricLocalizedInverseIdeal CycleQ2InverseIdealBaseLocalization

section Reduction
variable {R U V : Type*} [CommRing R] [CommRing U] [CommRing V]
  [Algebra R U] [Algebra R V]

theorem cotangentDual_ext (I : Ideal R)
    {φ ψ : V ⊗[R] I.Cotangent →ₗ[V] V}
    (h : ∀ x : I, φ ((1 : V) ⊗ₜ[R] I.toCotangent x) =
      ψ ((1 : V) ⊗ₜ[R] I.toCotangent x)) : φ = ψ := by
  apply (LinearMap.liftBaseChangeEquiv V).symm.injective
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective y
  exact h x

def multiplicationHom (J : Ideal U) : U →ₗ[U] (J →ₗ[U] U) where
  toFun a := a • J.subtype
  map_add' a b := add_smul a b J.subtype
  map_smul' a b := (smul_smul a b J.subtype).symm

@[simp] theorem multiplicationHom_apply (J : Ideal U) (a : U) (x : J) :
    multiplicationHom J a x = a * (x : U) := rfl

def inverseIdealReductionAdd (I : Ideal R) (ρ : U →ₐ[R] V)
    (hI : ∀ x ∈ I, algebraMap R V x = 0) :
    LocalInverseIdeal U I →+ (V ⊗[R] I.Cotangent →ₗ[V] V) where
  toFun := inverseIdealReduction I ρ hI
  map_zero' := by
    apply cotangentDual_ext I
    intro x
    simp only [inverseIdealReduction_equation, LinearMap.zero_apply, map_zero]
  map_add' ν μ := by
    apply cotangentDual_ext I
    intro x
    simp only [inverseIdealReduction_equation, LinearMap.add_apply, map_add]

theorem inverseIdealReduction_multiplication (I : Ideal R) (ρ : U →ₐ[R] V)
    (hI : ∀ x ∈ I, algebraMap R V x = 0) (a : U) :
    inverseIdealReductionAdd I ρ hI
      (multiplicationHom (I.map (algebraMap R U)) a) = 0 := by
  apply cotangentDual_ext I
  intro x
  change inverseIdealReduction I ρ hI _ ((1 : V) ⊗ₜ[R] I.toCotangent x) = 0
  rw [inverseIdealReduction_equation]
  change ρ (a * algebraMap R U (x : R)) = 0
  rw [map_mul, ρ.commutes, hI _ x.property, mul_zero]

end Reduction

abbrev CoverInverseIdeal (r θ : ℂ) (s : Finset (Fin 4)) :=
  LocalInverseIdeal (CoverLocal r θ s) (curveIdealOnSurface r θ)

theorem coverDenominatorsUnit (r θ : ℂ) {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (z : Submonoid.powers (coverProduct r θ s)) :
    IsUnit (algebraMap (SurfaceRing r θ) (CoverLocal r θ t) (z : SurfaceRing r θ)) := by
  have hz := (IsLocalization.map_units (CoverLocal r θ s) z).map
    (coverRestriction r θ hst).toRingHom
  change IsUnit (coverRestriction r θ hst
    (algebraMap (SurfaceRing r θ) (CoverLocal r θ s) (z : SurfaceRing r θ))) at hz
  simpa only [coverRestriction_base] using hz

def coverInverseRestriction (r θ : ℂ) {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    CoverInverseIdeal r θ s →ₗ[SurfaceRing r θ] CoverInverseIdeal r θ t :=
  inverseIdealRestrictionByUnits (Submonoid.powers (coverProduct r θ s))
    (CoverLocal r θ s) (curveIdealOnSurface r θ)
    (Submonoid.powers (coverProduct r θ t)) (CoverLocal r θ t)
    (coverDenominatorsUnit r θ hst)

theorem coverInverseRestriction_eval (r θ : ℂ) {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (ν : CoverInverseIdeal r θ s) (x : curveIdealOnSurface r θ) :
    coverInverseRestriction r θ hst ν
      (Algebra.idealMap (CoverLocal r θ t) (curveIdealOnSurface r θ) x) =
      coverRestriction r θ hst
        (ν (Algebra.idealMap (CoverLocal r θ s) (curveIdealOnSurface r θ) x)) :=
  inverseIdealRestrictionByUnits_eval _ _ _ _ _
    (coverDenominatorsUnit r θ hst) (coverRestriction r θ hst) ν x

theorem coverInverseRestriction_comp (r θ : ℂ) {s t u : Finset (Fin 4)}
    (hst : s ⊆ t) (htu : t ⊆ u) :
    (coverInverseRestriction r θ htu).comp (coverInverseRestriction r θ hst) =
      coverInverseRestriction r θ (hst.trans htu) :=
  inverseIdealRestrictionByUnits_comp _ _ _ _ _ _ _
    (coverDenominatorsUnit r θ hst) (coverDenominatorsUnit r θ htu)
    (coverDenominatorsUnit r θ (hst.trans htu))

def coverMultiplication (r θ : ℂ) (s : Finset (Fin 4)) :
    CoverLocal r θ s →ₗ[SurfaceRing r θ] CoverInverseIdeal r θ s :=
  (multiplicationHom ((curveIdealOnSurface r θ).map
    (algebraMap (SurfaceRing r θ) (CoverLocal r θ s)))).restrictScalars (SurfaceRing r θ)

theorem coverInverseRestriction_multiplication (r θ : ℂ) {s t : Finset (Fin 4)}
    (hst : s ⊆ t) (a : CoverLocal r θ s) :
    coverInverseRestriction r θ hst (coverMultiplication r θ s a) =
      coverMultiplication r θ t (coverRestriction r θ hst a) := by
  apply localInverseIdeal_ext (Submonoid.powers (coverProduct r θ t))
    (CoverLocal r θ t) (curveIdealOnSurface r θ)
  intro x
  rw [coverInverseRestriction_eval]
  change coverRestriction r θ hst
      (a * algebraMap (SurfaceRing r θ) (CoverLocal r θ s) (x : SurfaceRing r θ)) =
    coverRestriction r θ hst a *
      algebraMap (SurfaceRing r θ) (CoverLocal r θ t) (x : SurfaceRing r θ)
  rw [map_mul, coverRestriction_base]

abbrev InverseZero (r θ : ℂ) :=
  CoverInverseIdeal r θ {0} × CoverInverseIdeal r θ {1} ×
    CoverInverseIdeal r θ {2} × CoverInverseIdeal r θ {3}

abbrev InverseOne (r θ : ℂ) :=
  CoverInverseIdeal r θ {0,1} × CoverInverseIdeal r θ {0,2} ×
    CoverInverseIdeal r θ {0,3} × CoverInverseIdeal r θ {1,2} ×
      CoverInverseIdeal r θ {1,3} × CoverInverseIdeal r θ {2,3}

abbrev InverseTwo (r θ : ℂ) :=
  CoverInverseIdeal r θ {0,1,2} × CoverInverseIdeal r θ {0,1,3} ×
    CoverInverseIdeal r θ {0,2,3} × CoverInverseIdeal r θ {1,2,3}

abbrev ScalarOne (r θ : ℂ) :=
  CoverLocal r θ {0,1} × CoverLocal r θ {0,2} × CoverLocal r θ {0,3} ×
    CoverLocal r θ {1,2} × CoverLocal r θ {1,3} × CoverLocal r θ {2,3}

def inverseZeroDifferential (r θ : ℂ) (q : InverseZero r θ) : InverseOne r θ :=
  ⟨coverInverseRestriction r θ (show ({1}:Finset (Fin 4)) ⊆ {0,1} by simp) q.2.1 -
      coverInverseRestriction r θ (show ({0}:Finset (Fin 4)) ⊆ {0,1} by simp) q.1,
   coverInverseRestriction r θ (show ({2}:Finset (Fin 4)) ⊆ {0,2} by simp) q.2.2.1 -
      coverInverseRestriction r θ (show ({0}:Finset (Fin 4)) ⊆ {0,2} by simp) q.1,
   coverInverseRestriction r θ (show ({3}:Finset (Fin 4)) ⊆ {0,3} by simp) q.2.2.2 -
      coverInverseRestriction r θ (show ({0}:Finset (Fin 4)) ⊆ {0,3} by simp) q.1,
   coverInverseRestriction r θ (show ({2}:Finset (Fin 4)) ⊆ {1,2} by simp) q.2.2.1 -
      coverInverseRestriction r θ (show ({1}:Finset (Fin 4)) ⊆ {1,2} by simp) q.2.1,
   coverInverseRestriction r θ (show ({3}:Finset (Fin 4)) ⊆ {1,3} by simp) q.2.2.2 -
      coverInverseRestriction r θ (show ({1}:Finset (Fin 4)) ⊆ {1,3} by simp) q.2.1,
   coverInverseRestriction r θ (show ({3}:Finset (Fin 4)) ⊆ {2,3} by simp) q.2.2.2 -
      coverInverseRestriction r θ (show ({2}:Finset (Fin 4)) ⊆ {2,3} by simp) q.2.2.1⟩

def inverseOneDifferential (r θ : ℂ) (c : InverseOne r θ) : InverseTwo r θ :=
  ⟨coverInverseRestriction r θ (show ({1,2}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.2.2.2.1 -
      coverInverseRestriction r θ (show ({0,2}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.2.1 +
      coverInverseRestriction r θ (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.1,
   coverInverseRestriction r θ (show ({1,3}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.2.2.2.2.1 -
      coverInverseRestriction r θ (show ({0,3}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.2.2.1 +
      coverInverseRestriction r θ (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.1,
   coverInverseRestriction r θ (show ({2,3}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.2.2.2.2 -
      coverInverseRestriction r θ (show ({0,3}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.2.1 +
      coverInverseRestriction r θ (show ({0,2}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.1,
   coverInverseRestriction r θ (show ({2,3}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.2.2 -
      coverInverseRestriction r θ (show ({1,3}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.2.1 +
      coverInverseRestriction r θ (show ({1,2}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.1⟩

def scalarOneDifferential (r θ : ℂ) (c : ScalarOne r θ) : SurfaceCechTwo r θ :=
  ⟨coverRestriction r θ (show ({1,2}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.2.2.2.1 -
      coverRestriction r θ (show ({0,2}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.2.1 +
      coverRestriction r θ (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.1,
   coverRestriction r θ (show ({1,3}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.2.2.2.2.1 -
      coverRestriction r θ (show ({0,3}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.2.2.1 +
      coverRestriction r θ (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.1,
   coverRestriction r θ (show ({2,3}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.2.2.2.2 -
      coverRestriction r θ (show ({0,3}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.2.1 +
      coverRestriction r θ (show ({0,2}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.1,
   coverRestriction r θ (show ({2,3}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.2.2 -
      coverRestriction r θ (show ({1,3}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.2.1 +
      coverRestriction r θ (show ({1,2}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.1⟩

def multiplicationOne (r θ : ℂ) (c : ScalarOne r θ) : InverseOne r θ :=
  ⟨coverMultiplication r θ _ c.1, coverMultiplication r θ _ c.2.1,
   coverMultiplication r θ _ c.2.2.1, coverMultiplication r θ _ c.2.2.2.1,
   coverMultiplication r θ _ c.2.2.2.2.1, coverMultiplication r θ _ c.2.2.2.2.2⟩

def multiplicationTwo (r θ : ℂ) (c : SurfaceCechTwo r θ) : InverseTwo r θ :=
  ⟨coverMultiplication r θ _ c.face012, coverMultiplication r θ _ c.face013,
   coverMultiplication r θ _ c.face023, coverMultiplication r θ _ c.face123⟩

theorem multiplication_differential (r θ : ℂ) (c : ScalarOne r θ) :
    inverseOneDifferential r θ (multiplicationOne r θ c) =
      multiplicationTwo r θ (scalarOneDifferential r θ c) := by
  simp only [inverseOneDifferential, multiplicationOne, multiplicationTwo,
    scalarOneDifferential, coverInverseRestriction_multiplication, map_add, map_sub]

def cartierInverseLift (r θ : ℂ) (A L : CycleQ2SeedTrace.WeightedPoly) : InverseOne r θ :=
  ⟨inverseIdealConnectingLift r θ A L, 0, 0, 0, 0, 0⟩

theorem cartierInverseLift_face012 (r θ : ℂ) (A L : CycleQ2SeedTrace.WeightedPoly) :
    coverInverseRestriction r θ (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,2} by simp)
      (inverseIdealConnectingLift r θ A L) =
        coverMultiplication r θ {0,1,2} (boundary012 r θ A L) := by
  apply localInverseIdeal_ext (Submonoid.powers (coverProduct r θ {0,1,2}))
    (CoverLocal r θ {0,1,2}) (curveIdealOnSurface r θ)
  intro x
  refine (coverInverseRestriction_eval r θ
    (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,2} by simp)
    (show CoverInverseIdeal r θ {0,1} from inverseIdealConnectingLift r θ A L) x).trans ?_
  refine (boundary012_evaluation r θ A L
    (Algebra.idealMap (CoverLocal r θ {0,1}) (curveIdealOnSurface r θ) x)).trans ?_
  change boundary012 r θ A L * coverRestriction r θ _
      (algebraMap (SurfaceRing r θ) (CoverLocal r θ {0,1}) (x : SurfaceRing r θ)) =
    boundary012 r θ A L *
      algebraMap (SurfaceRing r θ) (CoverLocal r θ {0,1,2}) (x : SurfaceRing r θ)
  rw [coverRestriction_base]

theorem cartierInverseLift_face013 (r θ : ℂ) (A L : CycleQ2SeedTrace.WeightedPoly) :
    coverInverseRestriction r θ (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,3} by simp)
      (inverseIdealConnectingLift r θ A L) =
        coverMultiplication r θ {0,1,3} (boundary013 r θ A L) := by
  apply localInverseIdeal_ext (Submonoid.powers (coverProduct r θ {0,1,3}))
    (CoverLocal r θ {0,1,3}) (curveIdealOnSurface r θ)
  intro x
  refine (coverInverseRestriction_eval r θ
    (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,3} by simp)
    (show CoverInverseIdeal r θ {0,1} from inverseIdealConnectingLift r θ A L) x).trans ?_
  refine (boundary013_evaluation r θ A L
    (Algebra.idealMap (CoverLocal r θ {0,1}) (curveIdealOnSurface r θ) x)).trans ?_
  change boundary013 r θ A L * coverRestriction r θ _
      (algebraMap (SurfaceRing r θ) (CoverLocal r θ {0,1}) (x : SurfaceRing r θ)) =
    boundary013 r θ A L *
      algebraMap (SurfaceRing r θ) (CoverLocal r θ {0,1,3}) (x : SurfaceRing r θ)
  rw [coverRestriction_base]

theorem cartierInverseLift_differential (r θ : ℂ) (A L : CycleQ2SeedTrace.WeightedPoly) :
    inverseOneDifferential r θ (cartierInverseLift r θ A L) =
      multiplicationTwo r θ (cartierBoundaryTwoCochain r θ A L) := by
  simp only [inverseOneDifferential, cartierInverseLift, multiplicationTwo,
    cartierBoundaryTwoCochain, map_zero, sub_zero, zero_add,
    add_zero, cartierInverseLift_face012, cartierInverseLift_face013]

/-- Exactness of the actual inverse-ideal Cech complex on this four-open cover.
This remains an explicit premise until the independent refinement theorem is bound. -/
def InverseFirstExact (r θ : ℂ) : Prop :=
  ∀ c : InverseOne r θ, inverseOneDifferential r θ c = 0 →
    ∃ q : InverseZero r θ, inverseZeroDifferential r θ q = c

private theorem subtract_sums {M : Type*} [AddCommGroup M] (a b c d e f : M) :
    (a-b)-(c-d)+(e-f) = (a-c+e)-(b-d+f) := by abel

private theorem cycle_cancel {M : Type*} [AddCommGroup M] (a b c : M) :
    (a-b)-(a-c)+(b-c) = 0 := by abel

theorem inverseOneDifferential_sub (r θ : ℂ) (c d : InverseOne r θ) :
    inverseOneDifferential r θ (c-d) =
      inverseOneDifferential r θ c - inverseOneDifferential r θ d := by
  apply Prod.ext
  · simp only [inverseOneDifferential, Prod.fst_sub, Prod.snd_sub, map_sub]
    exact subtract_sums _ _ _ _ _ _
  apply Prod.ext
  · simp only [inverseOneDifferential, Prod.fst_sub, Prod.snd_sub, map_sub]
    exact subtract_sums _ _ _ _ _ _
  apply Prod.ext
  · simp only [inverseOneDifferential, Prod.fst_sub, Prod.snd_sub, map_sub]
    exact subtract_sums _ _ _ _ _ _
  · simp only [inverseOneDifferential, Prod.fst_sub, Prod.snd_sub, map_sub]
    exact subtract_sums _ _ _ _ _ _

theorem coverInverseRestriction_comp_apply (r θ : ℂ) {s t u : Finset (Fin 4)}
    (hst : s ⊆ t) (htu : t ⊆ u) (ν : CoverInverseIdeal r θ s) :
    coverInverseRestriction r θ htu (coverInverseRestriction r θ hst ν) =
      coverInverseRestriction r θ (hst.trans htu) ν :=
  DFunLike.congr_fun (coverInverseRestriction_comp r θ hst htu) ν

theorem inverseDifferential_squared (r θ : ℂ) (q : InverseZero r θ) :
    inverseOneDifferential r θ (inverseZeroDifferential r θ q) = 0 := by
  change inverseOneDifferential r θ (inverseZeroDifferential r θ q) = (0,0,0,0)
  simp only [inverseOneDifferential, inverseZeroDifferential, map_sub,
    coverInverseRestriction_comp_apply]
  apply Prod.ext
  · exact cycle_cancel _ _ _
  apply Prod.ext
  · exact cycle_cancel _ _ _
  apply Prod.ext <;> exact cycle_cancel _ _ _

theorem correctedLift_cocycle (r θ : ℂ) (A L : CycleQ2SeedTrace.WeightedPoly)
    (c : ScalarOne r θ)
    (hc : scalarOneDifferential r θ c = cartierBoundaryTwoCochain r θ A L) :
    inverseOneDifferential r θ
      (cartierInverseLift r θ A L - multiplicationOne r θ c) = 0 := by
  rw [inverseOneDifferential_sub, cartierInverseLift_differential,
    multiplication_differential, hc, sub_self]

theorem scalarBoundary_has_corrected_primitive (r θ : ℂ)
    (he : InverseFirstExact r θ) (A L : CycleQ2SeedTrace.WeightedPoly)
    (c : ScalarOne r θ)
    (hc : scalarOneDifferential r θ c = cartierBoundaryTwoCochain r θ A L) :
    ∃ q : InverseZero r θ, inverseZeroDifferential r θ q =
      cartierInverseLift r θ A L - multiplicationOne r θ c :=
  he _ (correctedLift_cocycle r θ A L c hc)

end CycleQ2CartierInverseIdealCech
end

end


section

/-!
Reduction of the genuine four-open inverse-ideal complex to the fixed normal
connecting class. Exactness of the inverse-ideal Cech complex is the only
remaining premise in the final nonboundary statement.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
open scoped TensorProduct

namespace CycleQ2CartierInverseIdealCech

open CycleQ2GeometricCartierNormalLift CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricLocalizedInverseIdeal CycleQ2InverseIdealBaseLocalization
  CycleQ2SeedTrace CycleQ2ActualNormalCech CycleQ2GenuineNormalConnecting
  CycleQ2NormalRestriction CycleQ2GeometricRelativeNormalConnecting
  CycleQ2ConormalJacobian CycleQ2SeedCechTheta CycleQ2NormalConnecting

def firstCoverToCurve (r θ : ℂ) :
    CoverLocal r θ {0} →ₐ[SurfaceRing r θ] FirstOpen r θ where
  __ := IsLocalization.Away.lift (S := CoverLocal r θ {0})
    (g := algebraMap (SurfaceRing r θ) (FirstOpen r θ)) (coverProduct r θ {0}) (by
      have hprod : coverProduct r θ {0} = surfaceQuotient r θ (originalG1 r) := by
        simp [coverProduct, coverElement]
      rw [hprod]
      change IsUnit (algebraMap P (FirstOpen r θ) (originalG1 r))
      rw [← firstUnit_value r θ]
      exact (CycleQ2NormalConnecting.firstOpenUnit r θ).isUnit)
  commutes' x := IsLocalization.Away.lift_eq _ _ x

def secondCoverToCurve (r θ : ℂ) :
    CoverLocal r θ {1} →ₐ[SurfaceRing r θ] SecondOpen r θ where
  __ := IsLocalization.Away.lift (S := CoverLocal r θ {1})
    (g := algebraMap (SurfaceRing r θ) (SecondOpen r θ)) (coverProduct r θ {1}) (by
      have hprod : coverProduct r θ {1} = surfaceQuotient r θ originalG2 := by
        simp [coverProduct, coverElement]
      rw [hprod]
      change IsUnit (algebraMap P (SecondOpen r θ) originalG2)
      rw [← secondUnit_value r θ]
      exact (CycleQ2NormalConnecting.secondOpenUnit r θ).isUnit)
  commutes' x := IsLocalization.Away.lift_eq _ _ x

def firstCurveRestrictionAlg (r θ : ℂ) : FirstOpen r θ →ₐ[SurfaceRing r θ] Overlap r θ where
  __ := (firstRestrictionAlg r θ).toRingHom
  commutes' x := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (firstRestrictionAlg r θ).commutes p

def secondCurveRestrictionAlg (r θ : ℂ) : SecondOpen r θ →ₐ[SurfaceRing r θ] Overlap r θ where
  __ := (secondRestrictionAlg r θ).toRingHom
  commutes' x := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (secondRestrictionAlg r θ).commutes p

theorem firstCoverToCurve_restriction (r θ : ℂ) (a : CoverLocal r θ {0}) :
    overlapToCurve r θ (coverRestriction r θ
      (show ({0}:Finset (Fin 4)) ⊆ {0,1} by simp) a) =
      firstRestriction r θ (firstCoverToCurve r θ a) := by
  let := IsLocalization.algHom_subsingleton
    (S := CoverLocal r θ {0}) (Submonoid.powers (coverProduct r θ {0}))
    (P := Overlap r θ)
  have he : (overlapToCurve r θ).comp (coverRestriction r θ
      (show ({0}:Finset (Fin 4)) ⊆ {0,1} by simp)) =
    (firstCurveRestrictionAlg r θ).comp (firstCoverToCurve r θ) := Subsingleton.elim _ _
  exact DFunLike.congr_fun he a

theorem secondCoverToCurve_restriction (r θ : ℂ) (a : CoverLocal r θ {1}) :
    overlapToCurve r θ (coverRestriction r θ
      (show ({1}:Finset (Fin 4)) ⊆ {0,1} by simp) a) =
      secondRestriction r θ (secondCoverToCurve r θ a) := by
  let := IsLocalization.algHom_subsingleton
    (S := CoverLocal r θ {1}) (Submonoid.powers (coverProduct r θ {1}))
    (P := Overlap r θ)
  have he : (overlapToCurve r θ).comp (coverRestriction r θ
      (show ({1}:Finset (Fin 4)) ⊆ {0,1} by simp)) =
    (secondCurveRestrictionAlg r θ).comp (secondCoverToCurve r θ) := Subsingleton.elim _ _
  exact DFunLike.congr_fun he a

theorem firstSurfaceIdeal_annihilates (r θ : ℂ) :
    ∀ x ∈ curveIdealOnSurface r θ, algebraMap (SurfaceRing r θ) (FirstOpen r θ) x = 0 := by
  have h : curveIdealOnSurface r θ ≤
      RingHom.ker (algebraMap (SurfaceRing r θ) (FirstOpen r θ)) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    exact first_annihilates r θ p hp
  exact fun x hx => h hx

theorem secondSurfaceIdeal_annihilates (r θ : ℂ) :
    ∀ x ∈ curveIdealOnSurface r θ, algebraMap (SurfaceRing r θ) (SecondOpen r θ) x = 0 := by
  have h : curveIdealOnSurface r θ ≤
      RingHom.ker (algebraMap (SurfaceRing r θ) (SecondOpen r θ)) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    exact second_annihilates r θ p hp
  exact fun x hx => h hx

def firstNormalReduction (r θ : ℂ) (ν : CoverInverseIdeal r θ {0}) : FirstKernel r θ :=
  firstNormalModuleEquiv r θ
    (inverseIdealReduction (curveIdealOnSurface r θ) (firstCoverToCurve r θ)
      (firstSurfaceIdeal_annihilates r θ) ν)

def secondNormalReduction (r θ : ℂ) (ν : CoverInverseIdeal r θ {1}) : SecondKernel r θ :=
  secondNormalModuleEquiv r θ
    (inverseIdealReduction (curveIdealOnSurface r θ) (secondCoverToCurve r θ)
      (secondSurfaceIdeal_annihilates r θ) ν)

def overlapNormalReduction (r θ : ℂ) : CoverInverseIdeal r θ {0,1} →+ OverlapKernel r θ :=
  (overlapNormalModuleEquiv r θ).toAddMonoidHom.comp
    (inverseIdealReductionAdd (curveIdealOnSurface r θ) (overlapToCurve r θ)
      (surfaceCurveIdeal_annihilates r θ))

def surfaceEquationElement (r θ : ℂ) (i : Fin 3) : curveIdealOnSurface r θ :=
  ⟨surfaceQuotient r θ (curveEquations r θ i),
    Ideal.mem_map_of_mem _ (curveEquation_mem r θ i)⟩

def coverEquationElement (r θ : ℂ) (s : Finset (Fin 4)) (i : Fin 3) :
    (curveIdealOnSurface r θ).map (algebraMap (SurfaceRing r θ) (CoverLocal r θ s)) :=
  Algebra.idealMap (CoverLocal r θ s) (curveIdealOnSurface r θ) (surfaceEquationElement r θ i)

section Comparison
variable (r θ : ℂ) (S : Type*) [CommRing S] [Algebra P S]
  [Algebra (SurfaceRing r θ) S] [IsScalarTower P (SurfaceRing r θ) S]

theorem normalComparison_equation (ν : RelativeNormal r θ S) (i : Fin 3) :
    (normalModuleEquiv r θ S ν).val (curveClass r θ i) =
      ν (relativeEquationClass r θ S i) := by
  simpa only [curveClass, LinearEquiv.symm_apply_apply] using
    (normalModuleEquiv_symm_equation r θ S (normalModuleEquiv r θ S ν) i).symm

end Comparison

theorem firstNormalReduction_equation (r θ : ℂ) (ν : CoverInverseIdeal r θ {0})
    (i : Fin 3) :
    (firstNormalReduction r θ ν).val (curveClass r θ i) =
      firstCoverToCurve r θ (ν (coverEquationElement r θ {0} i)) := by
  change (normalModuleEquiv r θ (FirstOpen r θ)
    (inverseIdealReduction (curveIdealOnSurface r θ) (firstCoverToCurve r θ)
      (firstSurfaceIdeal_annihilates r θ) ν)).val (curveClass r θ i) = _
  rw [normalComparison_equation]
  exact inverseIdealReduction_equation (curveIdealOnSurface r θ)
    (firstCoverToCurve r θ) (firstSurfaceIdeal_annihilates r θ) ν (surfaceEquationElement r θ i)

theorem secondNormalReduction_equation (r θ : ℂ) (ν : CoverInverseIdeal r θ {1})
    (i : Fin 3) :
    (secondNormalReduction r θ ν).val (curveClass r θ i) =
      secondCoverToCurve r θ (ν (coverEquationElement r θ {1} i)) := by
  change (normalModuleEquiv r θ (SecondOpen r θ)
    (inverseIdealReduction (curveIdealOnSurface r θ) (secondCoverToCurve r θ)
      (secondSurfaceIdeal_annihilates r θ) ν)).val (curveClass r θ i) = _
  rw [normalComparison_equation]
  exact inverseIdealReduction_equation (curveIdealOnSurface r θ)
    (secondCoverToCurve r θ) (secondSurfaceIdeal_annihilates r θ) ν (surfaceEquationElement r θ i)

theorem overlapNormalReduction_equation (r θ : ℂ) (ν : CoverInverseIdeal r θ {0,1})
    (i : Fin 3) :
    (overlapNormalReduction r θ ν).val (curveClass r θ i) =
      overlapToCurve r θ (ν (coverEquationElement r θ {0,1} i)) := by
  change (normalModuleEquiv r θ (Overlap r θ)
    (inverseIdealReduction (curveIdealOnSurface r θ) (overlapToCurve r θ)
      (surfaceCurveIdeal_annihilates r θ) ν)).val (curveClass r θ i) = _
  rw [normalComparison_equation]
  exact inverseIdealReduction_equation (curveIdealOnSurface r θ)
    (overlapToCurve r θ) (surfaceCurveIdeal_annihilates r θ) ν (surfaceEquationElement r θ i)

theorem overlapNormalReduction_first (r θ : ℂ) (ν : CoverInverseIdeal r θ {0}) :
    overlapNormalReduction r θ (coverInverseRestriction r θ
      (show ({0}:Finset (Fin 4)) ⊆ {0,1} by simp) ν) =
      firstKernelRestriction r θ (firstNormalReduction r θ ν) := by
  apply Subtype.ext
  apply curveNormal_ext r θ
  intro i
  rw [overlapNormalReduction_equation]
  change overlapToCurve r θ _ = curveRestriction r θ (firstRestrictionAlg r θ)
    (firstNormalReduction r θ ν).val (curveClass r θ i)
  rw [curveRestriction_class, firstNormalReduction_equation]
  refine (congrArg (overlapToCurve r θ) (coverInverseRestriction_eval r θ
    (show ({0}:Finset (Fin 4)) ⊆ {0,1} by simp) ν (surfaceEquationElement r θ i))).trans ?_
  exact firstCoverToCurve_restriction r θ (ν (coverEquationElement r θ {0} i))

theorem overlapNormalReduction_second (r θ : ℂ) (ν : CoverInverseIdeal r θ {1}) :
    overlapNormalReduction r θ (coverInverseRestriction r θ
      (show ({1}:Finset (Fin 4)) ⊆ {0,1} by simp) ν) =
      secondKernelRestriction r θ (secondNormalReduction r θ ν) := by
  apply Subtype.ext
  apply curveNormal_ext r θ
  intro i
  rw [overlapNormalReduction_equation]
  change overlapToCurve r θ _ = curveRestriction r θ (secondRestrictionAlg r θ)
    (secondNormalReduction r θ ν).val (curveClass r θ i)
  rw [curveRestriction_class, secondNormalReduction_equation]
  refine (congrArg (overlapToCurve r θ) (coverInverseRestriction_eval r θ
    (show ({1}:Finset (Fin 4)) ⊆ {0,1} by simp) ν (surfaceEquationElement r θ i))).trans ?_
  exact secondCoverToCurve_restriction r θ (ν (coverEquationElement r θ {1} i))

theorem overlapNormalReduction_multiplication (r θ : ℂ) (a : CoverLocal r θ {0,1}) :
    overlapNormalReduction r θ (coverMultiplication r θ {0,1} a) = 0 := by
  change overlapNormalModuleEquiv r θ
    (inverseIdealReductionAdd (curveIdealOnSurface r θ) (overlapToCurve r θ)
      (surfaceCurveIdeal_annihilates r θ)
      (multiplicationHom ((curveIdealOnSurface r θ).map
        (algebraMap (SurfaceRing r θ) (CoverLocal r θ {0,1}))) a)) = 0
  rw [inverseIdealReduction_multiplication, map_zero]

theorem overlapNormalReduction_lift (r θ : ℂ) (A L : P) :
    overlapNormalReduction r θ (inverseIdealConnectingLift r θ A L) =
      connectingRepresentative r θ A L := by
  change overlapNormalModuleEquiv r θ (reducedInverseIdealConnectingLift r θ A L) = _
  rw [reducedInverseIdealConnectingLift_eq, relativeConnectingRepresentative_comparison]

/-- A scalar boundary makes the fixed normal connecting cochain a boundary,
provided the actual inverse-ideal first Cech complex is exact. -/
theorem scalarBoundary_connectingClass_eq_zero (r θ : ℂ)
    (he : InverseFirstExact r θ) (A L : P) (c : ScalarOne r θ)
    (hc : scalarOneDifferential r θ c = cartierBoundaryTwoCochain r θ A L) :
    connectingClass r θ A L = 0 := by
  obtain ⟨q, hq⟩ := scalarBoundary_has_corrected_primitive r θ he A L c hc
  have h01 := congrArg Prod.fst hq
  change coverInverseRestriction r θ (show ({1}:Finset (Fin 4)) ⊆ {0,1} by simp) q.2.1 -
      coverInverseRestriction r θ (show ({0}:Finset (Fin 4)) ⊆ {0,1} by simp) q.1 =
    (show CoverInverseIdeal r θ {0,1} from inverseIdealConnectingLift r θ A L) -
      coverMultiplication r θ {0,1} c.1 at h01
  have hr := congrArg (overlapNormalReduction r θ) h01
  rw [map_sub, map_sub, overlapNormalReduction_second, overlapNormalReduction_first,
    overlapNormalReduction_lift, overlapNormalReduction_multiplication, sub_zero] at hr
  have hf : firstKernelRestriction r θ (firstNormalReduction r θ q.1) ∈ normalBoundaries r θ :=
    Submodule.mem_sup_left (show firstKernelRestriction r θ (firstNormalReduction r θ q.1) ∈
      LinearMap.range (firstKernelRestriction r θ) from ⟨_, rfl⟩)
  have hs : secondKernelRestriction r θ (secondNormalReduction r θ q.2.1) ∈ normalBoundaries r θ :=
    Submodule.mem_sup_right (show secondKernelRestriction r θ (secondNormalReduction r θ q.2.1) ∈
      LinearMap.range (secondKernelRestriction r θ) from ⟨_, rfl⟩)
  change (Submodule.Quotient.mk (connectingRepresentative r θ A L) : NormalCech r θ) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [← hr]
  exact (normalBoundaries r θ).sub_mem hs hf

/-- Conditional nonboundary of the literal actual surface Cartier cocycle.
The premise is the exact four-open inverse-ideal Cech statement being proved
independently by coordinate cancellation and radical-cover refinement. -/
theorem literal_cartierBoundary_not_boundary (he : InverseFirstExact 57 1) :
    ¬ ∃ c : ScalarOne 57 1,
      scalarOneDifferential 57 1 c = cartierBoundaryTwoCochain 57 1 derivativeA 0 := by
  rintro ⟨c, hc⟩
  exact CycleQ2GeometricLiteralNormalBinding.literal_normalConnectingClass_ne_zero
    (scalarBoundary_connectingClass_eq_zero 57 1 he derivativeA 0 c hc)

end CycleQ2CartierInverseIdealCech
end

end


section

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open AlgebraicGeometry TopologicalSpace

namespace CycleQ2InverseIdealSheaf

open CycleQ2GeometricLocalizedInverseIdeal CycleQ2InverseIdealBaseLocalization

section General
variable {A : Type} [CommRing A] (I : Ideal A) [Module.FinitePresentation A I]
variable (r : A) (U : Type) [CommRing U] [Algebra A U]
  [IsLocalization (Submonoid.powers r) U]

/-- The actual inverse Hom on a principal localization is the section module
of the sheaf associated to the actual inverse ideal. -/
def localizedInverseIdealSectionsEquiv :
    LocalInverseIdeal U I ≃ₗ[A]
      CartierCechRefinement.Sections A (I →ₗ[A] A) (PrimeSpectrum.basicOpen r) :=
  IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (localizedInverseIdealMap (Submonoid.powers r) U I)
    (StructureSheaf.toOpenₗ A (I →ₗ[A] A) (PrimeSpectrum.basicOpen r))

@[simp] theorem localizedInverseIdealSectionsEquiv_original (ν : I →ₗ[A] A) :
    localizedInverseIdealSectionsEquiv I r U
      (localizedInverseIdealMap (Submonoid.powers r) U I ν) =
        StructureSheaf.toOpenₗ A (I →ₗ[A] A) (PrimeSpectrum.basicOpen r) ν :=
  IsLocalizedModule.linearEquiv_apply _ _ _ ν

@[simp] theorem localizedInverseIdealSectionsEquiv_symm_original (ν : I →ₗ[A] A) :
    (localizedInverseIdealSectionsEquiv I r U).symm
      (StructureSheaf.toOpenₗ A (I →ₗ[A] A) (PrimeSpectrum.basicOpen r) ν) =
        localizedInverseIdealMap (Submonoid.powers r) U I ν := by
  apply (localizedInverseIdealSectionsEquiv I r U).injective
  simp only [LinearEquiv.apply_symm_apply, localizedInverseIdealSectionsEquiv_original]

variable (s : A) (V : Type) [CommRing V] [Algebra A V]
  [IsLocalization (Submonoid.powers s) V]

/-- The section comparison preserves the actual restriction maps. -/
theorem localizedInverseIdealSectionsEquiv_restrict
    (hopen : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r)
    (hunit : ∀ z : Submonoid.powers r, IsUnit (algebraMap A V (z : A)))
    (ν : LocalInverseIdeal U I) :
    CartierCechRefinement.restrict hopen
      (localizedInverseIdealSectionsEquiv I r U ν) =
        localizedInverseIdealSectionsEquiv I s V
          (inverseIdealRestrictionByUnits (Submonoid.powers r) U I
            (Submonoid.powers s) V hunit ν) := by
  have hmaps :
      ((localizedInverseIdealSectionsEquiv I s V).symm.toLinearMap.comp
        (CartierCechRefinement.restrict hopen)).comp
          (localizedInverseIdealSectionsEquiv I r U).toLinearMap =
        inverseIdealRestrictionByUnits (Submonoid.powers r) U I
          (Submonoid.powers s) V hunit := by
    apply IsLocalizedModule.ext (Submonoid.powers r)
      (localizedInverseIdealMap (Submonoid.powers r) U I)
      (fun z => localInverseIdeal_scalar_unit I V z (hunit z))
    apply LinearMap.ext
    intro μ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      localizedInverseIdealSectionsEquiv_original, inverseIdealRestrictionByUnits_original]
    change (localizedInverseIdealSectionsEquiv I s V).symm
      (StructureSheaf.toOpenₗ A (I →ₗ[A] A) (PrimeSpectrum.basicOpen s) μ) = _
    exact localizedInverseIdealSectionsEquiv_symm_original I s V μ
  apply (localizedInverseIdealSectionsEquiv I s V).symm.injective
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    using DFunLike.congr_fun hmaps ν

end General

open CycleQ2GeometricCartierNormalLift CycleQ2GeometricSeedNormalIdeals

abbrev coverOpen (r θ : ℂ) (s : Finset (Fin 4)) :=
  PrimeSpectrum.basicOpen (coverProduct r θ s)

theorem coverOpen_mono (r θ : ℂ) {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    coverOpen r θ t ≤ coverOpen r θ s := by
  obtain ⟨c, hc⟩ := Finset.prod_dvd_prod_of_subset s t (coverElement r θ) hst
  change coverProduct r θ t = coverProduct r θ s * c at hc
  change PrimeSpectrum.basicOpen (coverProduct r θ t) ≤ _
  rw [hc]
  exact PrimeSpectrum.basicOpen_mul_le_left _ _

def coverSectionsEquiv (r θ : ℂ) (s : Finset (Fin 4)) :
    LocalInverseIdeal (CoverLocal r θ s) (curveIdealOnSurface r θ) ≃ₗ[SurfaceRing r θ]
      CartierCechRefinement.Sections (SurfaceRing r θ)
        ((curveIdealOnSurface r θ) →ₗ[SurfaceRing r θ] SurfaceRing r θ) (coverOpen r θ s) :=
  localizedInverseIdealSectionsEquiv (curveIdealOnSurface r θ)
    (coverProduct r θ s) (CoverLocal r θ s)

@[simp] theorem coverOpen_singleton (r θ : ℂ) (i : Fin 4) :
    coverOpen r θ {i} = PrimeSpectrum.basicOpen (coverElement r θ i) := by
  simp [coverOpen, coverProduct]

theorem coverOpen_pair (r θ : ℂ) (i j : Fin 4) :
    coverOpen r θ {i,j} = coverOpen r θ {i} ⊓ coverOpen r θ {j} := by
  by_cases hij : i = j
  · subst j
    simp
  · simp [coverOpen, coverProduct, Finset.prod_pair hij, PrimeSpectrum.basicOpen_mul]

end CycleQ2InverseIdealSheaf
end

end


section

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2InverseIdealSheaf

open CycleQ2GeometricCartierNormalLift CycleQ2GeometricSeedNormalIdeals
  CycleQ2CartierInverseIdealCech

@[simp] theorem coverSectionsEquiv_restrict (r θ : ℂ) {s t : Finset (Fin 4)}
    (hst : s ⊆ t) (ν : CoverInverseIdeal r θ s) :
    CartierCechRefinement.restrict (coverOpen_mono r θ hst)
      (coverSectionsEquiv r θ s ν) =
        coverSectionsEquiv r θ t (coverInverseRestriction r θ hst ν) :=
  localizedInverseIdealSectionsEquiv_restrict (curveIdealOnSurface r θ)
    (coverProduct r θ s) (CoverLocal r θ s) (coverProduct r θ t) (CoverLocal r θ t)
    (coverOpen_mono r θ hst) (coverDenominatorsUnit r θ hst) ν

@[simp] theorem coverSectionsEquiv_symm_restrict (r θ : ℂ) {s t : Finset (Fin 4)}
    (hst : s ⊆ t)
    (σ : CartierCechRefinement.Sections (SurfaceRing r θ)
      ((curveIdealOnSurface r θ) →ₗ[SurfaceRing r θ] SurfaceRing r θ) (coverOpen r θ s)) :
    (coverSectionsEquiv r θ t).symm
      (CartierCechRefinement.restrict (coverOpen_mono r θ hst) σ) =
        coverInverseRestriction r θ hst ((coverSectionsEquiv r θ s).symm σ) := by
  apply (coverSectionsEquiv r θ t).injective
  simpa only [LinearEquiv.apply_symm_apply] using
    coverSectionsEquiv_restrict r θ hst ((coverSectionsEquiv r θ s).symm σ)

end CycleQ2InverseIdealSheaf
end

end


section

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CartierCechFour

open CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricSheafLocalIso CartierCechCoverTransfer

universe u

def quad {α : Fin 4 → Type u} (a0 : α 0) (a1 : α 1) (a2 : α 2) (a3 : α 3) :
    ∀ i, α i :=
  Fin.cases a0 (Fin.cases a1 (Fin.cases a2 (Fin.cases a3 (fun z => Fin.elim0 z))))

@[simp] theorem quad_0 {α : Fin 4 → Type u} (a0 : α 0) (a1 : α 1) (a2 : α 2) (a3 : α 3) :
    quad a0 a1 a2 a3 0 = a0 := rfl

@[simp] theorem quad_1 {α : Fin 4 → Type u} (a0 : α 0) (a1 : α 1) (a2 : α 2) (a3 : α 3) :
    quad a0 a1 a2 a3 1 = a1 := rfl

@[simp] theorem quad_2 {α : Fin 4 → Type u} (a0 : α 0) (a1 : α 1) (a2 : α 2) (a3 : α 3) :
    quad a0 a1 a2 a3 2 = a2 := rfl

@[simp] theorem quad_3 {α : Fin 4 → Type u} (a0 : α 0) (a1 : α 1) (a2 : α 2) (a3 : α 3) :
    quad a0 a1 a2 a3 3 = a3 := rfl

@[simp] theorem quad_mk_0 {α : Fin 4 → Type u} (a0 : α 0) (a1 : α 1)
    (a2 : α 2) (a3 : α 3) (hi : 0 < 4) :
    quad a0 a1 a2 a3 ⟨0, hi⟩ = a0 := rfl

@[simp] theorem quad_mk_1 {α : Fin 4 → Type u} (a0 : α 0) (a1 : α 1)
    (a2 : α 2) (a3 : α 3) (hi : 1 < 4) :
    quad a0 a1 a2 a3 ⟨1, hi⟩ = a1 := rfl

@[simp] theorem quad_mk_2 {α : Fin 4 → Type u} (a0 : α 0) (a1 : α 1)
    (a2 : α 2) (a3 : α 3) (hi : 2 < 4) :
    quad a0 a1 a2 a3 ⟨2, hi⟩ = a2 := rfl

@[simp] theorem quad_mk_3 {α : Fin 4 → Type u} (a0 : α 0) (a1 : α 1)
    (a2 : α 2) (a3 : α 3) (hi : 3 < 4) :
    quad a0 a1 a2 a3 ⟨3, hi⟩ = a3 := rfl

private theorem res_comp_site {X : TopCat}
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    {O P Q : Opens X} (hPO : P ≤ O) (hQP : Q ≤ P) (s : F.obj.obj (op O)) :
    res F hQP (res F hPO s) = res F (hQP.trans hPO) s :=
  CycleQ2GeometricSheafLocalIso.res_comp F hPO hQP s

private theorem res_self_site {X : TopCat}
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat)
    (O : Opens X) (s : F.obj.obj (op O)) : res F (le_refl O) s = s :=
  CycleQ2GeometricSheafLocalIso.res_self F O s

variable {X : TopCat} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat) (U : Fin 4 → Opens X)
  (c01 : F.obj.obj (op (U 0 ⊓ U 1))) (c02 : F.obj.obj (op (U 0 ⊓ U 2)))
  (c03 : F.obj.obj (op (U 0 ⊓ U 3))) (c12 : F.obj.obj (op (U 1 ⊓ U 2)))
  (c13 : F.obj.obj (op (U 1 ⊓ U 3))) (c23 : F.obj.obj (op (U 2 ⊓ U 3)))

/-- The alternating extension of the six ordered edges to all pairs. -/
def fourEdgeCochain : ∀ i j, F.obj.obj (op (U i ⊓ U j)) :=
  quad
    (quad 0 c01 c02 c03)
    (quad (-res F (inf_comm (U 0) (U 1)).ge c01) 0 c12 c13)
    (quad (-res F (inf_comm (U 0) (U 2)).ge c02)
      (-res F (inf_comm (U 1) (U 2)).ge c12) 0 c23)
    (quad (-res F (inf_comm (U 0) (U 3)).ge c03)
      (-res F (inf_comm (U 1) (U 3)).ge c13)
      (-res F (inf_comm (U 2) (U 3)).ge c23) 0)

variable
  (h012 : ∀ (W : Opens X) (h0 : W ≤ U 0) (h1 : W ≤ U 1) (h2 : W ≤ U 2),
    res F (le_inf h0 h1) c01 + res F (le_inf h1 h2) c12 = res F (le_inf h0 h2) c02)
  (h013 : ∀ (W : Opens X) (h0 : W ≤ U 0) (h1 : W ≤ U 1) (h3 : W ≤ U 3),
    res F (le_inf h0 h1) c01 + res F (le_inf h1 h3) c13 = res F (le_inf h0 h3) c03)
  (h023 : ∀ (W : Opens X) (h0 : W ≤ U 0) (h2 : W ≤ U 2) (h3 : W ≤ U 3),
    res F (le_inf h0 h2) c02 + res F (le_inf h2 h3) c23 = res F (le_inf h0 h3) c03)
  (h123 : ∀ (W : Opens X) (h1 : W ≤ U 1) (h2 : W ≤ U 2) (h3 : W ≤ U 3),
    res F (le_inf h1 h2) c12 + res F (le_inf h2 h3) c23 = res F (le_inf h1 h3) c13)

private theorem triangle_permutations {G : Type*} [AddCommGroup G]
    (a b c : G) (h : a + b = c) :
    (c + -b = a) ∧ (-a + c = b) ∧ (b + -c = -a) ∧
      (-c + a = -b) ∧ (-b + -a = -c) := by
  subst c
  exact ⟨by abel, by abel, by abel, by abel, by abel⟩

include h012 h013 h023 in
private theorem fourEdgeCondition0 (j k : Fin 4) (W : Opens X)
    (hi : W ≤ U 0) (hj : W ≤ U j) (hk : W ≤ U k) :
    res F (le_inf hi hj) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 0 j) +
      res F (le_inf hj hk) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 j k) =
        res F (le_inf hi hk) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 0 k) := by
  fin_cases j <;> fin_cases k <;> dsimp only at hj hk ⊢
  · simp [fourEdgeCochain]
  · simp [fourEdgeCochain]
  · simp [fourEdgeCochain]
  · simp [fourEdgeCochain]
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain]
  · have h := h012 W hi hj hk
    simp only [fourEdgeCochain, quad_0, quad_mk_1, quad_mk_2]
    exact h
  · have h := h013 W hi hj hk
    simp only [fourEdgeCochain, quad_0, quad_mk_1, quad_mk_3]
    exact h
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h012 W hi hk hj
    simp only [fourEdgeCochain, quad_0, quad_mk_1, quad_mk_2, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).1
  · simp [fourEdgeCochain]
  · have h := h023 W hi hj hk
    simp only [fourEdgeCochain, quad_0, quad_mk_2, quad_mk_3]
    exact h
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h013 W hi hk hj
    simp only [fourEdgeCochain, quad_0, quad_mk_1, quad_mk_3, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).1
  · have h := h023 W hi hk hj
    simp only [fourEdgeCochain, quad_0, quad_mk_2, quad_mk_3, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).1
  · simp [fourEdgeCochain]

include h012 h013 h123 in
private theorem fourEdgeCondition1 (j k : Fin 4) (W : Opens X)
    (hi : W ≤ U 1) (hj : W ≤ U j) (hk : W ≤ U k) :
    res F (le_inf hi hj) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 1 j) +
      res F (le_inf hj hk) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 j k) =
        res F (le_inf hi hk) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 1 k) := by
  fin_cases j <;> fin_cases k <;> dsimp only at hj hk ⊢
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h012 W hj hi hk
    simp only [fourEdgeCochain, quad_1, quad_mk_0, quad_mk_2, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.1
  · have h := h013 W hj hi hk
    simp only [fourEdgeCochain, quad_1, quad_mk_0, quad_mk_3, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.1
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain]
  · simp [fourEdgeCochain]
  · simp [fourEdgeCochain]
  · have h := h012 W hk hi hj
    simp only [fourEdgeCochain, quad_1, quad_mk_0, quad_mk_2, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.1
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain]
  · have h := h123 W hi hj hk
    simp only [fourEdgeCochain, quad_1, quad_mk_2, quad_mk_3]
    exact h
  · have h := h013 W hk hi hj
    simp only [fourEdgeCochain, quad_1, quad_mk_0, quad_mk_3, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.1
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h123 W hi hk hj
    simp only [fourEdgeCochain, quad_1, quad_mk_2, quad_mk_3, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).1
  · simp [fourEdgeCochain]

include h012 h023 h123 in
private theorem fourEdgeCondition2 (j k : Fin 4) (W : Opens X)
    (hi : W ≤ U 2) (hj : W ≤ U j) (hk : W ≤ U k) :
    res F (le_inf hi hj) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 2 j) +
      res F (le_inf hj hk) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 j k) =
        res F (le_inf hi hk) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 2 k) := by
  fin_cases j <;> fin_cases k <;> dsimp only at hj hk ⊢
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h012 W hj hk hi
    simp only [fourEdgeCochain, quad_2, quad_mk_0, quad_mk_1, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.2.1
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h023 W hj hi hk
    simp only [fourEdgeCochain, quad_2, quad_mk_0, quad_mk_3, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.1
  · have h := h012 W hk hj hi
    simp only [fourEdgeCochain, quad_2, quad_mk_0, quad_mk_1, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.2.2
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h123 W hj hi hk
    simp only [fourEdgeCochain, quad_2, quad_mk_1, quad_mk_3, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.1
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain]
  · simp [fourEdgeCochain]
  · have h := h023 W hk hi hj
    simp only [fourEdgeCochain, quad_2, quad_mk_0, quad_mk_3, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.1
  · have h := h123 W hk hi hj
    simp only [fourEdgeCochain, quad_2, quad_mk_1, quad_mk_3, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.1
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain]

include h013 h023 h123 in
private theorem fourEdgeCondition3 (j k : Fin 4) (W : Opens X)
    (hi : W ≤ U 3) (hj : W ≤ U j) (hk : W ≤ U k) :
    res F (le_inf hi hj) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 3 j) +
      res F (le_inf hj hk) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 j k) =
        res F (le_inf hi hk) (fourEdgeCochain F U c01 c02 c03 c12 c13 c23 3 k) := by
  fin_cases j <;> fin_cases k <;> dsimp only at hj hk ⊢
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h013 W hj hk hi
    simp only [fourEdgeCochain, quad_3, quad_mk_0, quad_mk_1, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.2.1
  · have h := h023 W hj hk hi
    simp only [fourEdgeCochain, quad_3, quad_mk_0, quad_mk_2, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.2.1
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h013 W hk hj hi
    simp only [fourEdgeCochain, quad_3, quad_mk_0, quad_mk_1, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.2.2
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h123 W hj hk hi
    simp only [fourEdgeCochain, quad_3, quad_mk_1, quad_mk_2, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.2.1
  · simp [fourEdgeCochain, res_comp_site]
  · have h := h023 W hk hj hi
    simp only [fourEdgeCochain, quad_3, quad_mk_0, quad_mk_2, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.2.2
  · have h := h123 W hk hj hi
    simp only [fourEdgeCochain, quad_3, quad_mk_1, quad_mk_2, map_neg, res_comp_site]
    exact (triangle_permutations _ _ _ h).2.2.2.2
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain, res_comp_site]
  · simp [fourEdgeCochain]

def fourEdgeCocycle : OneCocycle F U where
  val := fourEdgeCochain F U c01 c02 c03 c12 c13 c23
  condition i j k W hi hj hk := by
    fin_cases i
    · exact fourEdgeCondition0 F U c01 c02 c03 c12 c13 c23 h012 h013 h023 j k W hi hj hk
    · exact fourEdgeCondition1 F U c01 c02 c03 c12 c13 c23 h012 h013 h123 j k W hi hj hk
    · exact fourEdgeCondition2 F U c01 c02 c03 c12 c13 c23 h012 h023 h123 j k W hi hj hk
    · exact fourEdgeCondition3 F U c01 c02 c03 c12 c13 c23 h013 h023 h123 j k W hi hj hk

include h012 h013 h023 h123 in
/-- Actual all-pairs exactness supplies primitives for the six-edge
convention of the four-open Cartier complex. -/
theorem sixEdge_primitive (he : FirstExact F U) :
    ∃ q : ∀ i, F.obj.obj (op (U i)),
      c01 = res F inf_le_right (q 1) - res F inf_le_left (q 0) ∧
      c02 = res F inf_le_right (q 2) - res F inf_le_left (q 0) ∧
      c03 = res F inf_le_right (q 3) - res F inf_le_left (q 0) ∧
      c12 = res F inf_le_right (q 2) - res F inf_le_left (q 1) ∧
      c13 = res F inf_le_right (q 3) - res F inf_le_left (q 1) ∧
      c23 = res F inf_le_right (q 3) - res F inf_le_left (q 2) := by
  obtain ⟨q, hq⟩ := he (fourEdgeCocycle F U c01 c02 c03 c12 c13 c23 h012 h013 h023 h123)
  refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [fourEdgeCocycle, fourEdgeCochain, quad_0, quad_1, quad_2, quad_3, res_self_site] using
      hq 0 1 (U 0 ⊓ U 1) inf_le_left inf_le_right
  · simpa only [fourEdgeCocycle, fourEdgeCochain, quad_0, quad_1, quad_2, quad_3, res_self_site] using
      hq 0 2 (U 0 ⊓ U 2) inf_le_left inf_le_right
  · simpa only [fourEdgeCocycle, fourEdgeCochain, quad_0, quad_1, quad_2, quad_3, res_self_site] using
      hq 0 3 (U 0 ⊓ U 3) inf_le_left inf_le_right
  · simpa only [fourEdgeCocycle, fourEdgeCochain, quad_0, quad_1, quad_2, quad_3, res_self_site] using
      hq 1 2 (U 1 ⊓ U 2) inf_le_left inf_le_right
  · simpa only [fourEdgeCocycle, fourEdgeCochain, quad_0, quad_1, quad_2, quad_3, res_self_site] using
      hq 1 3 (U 1 ⊓ U 3) inf_le_left inf_le_right
  · simpa only [fourEdgeCocycle, fourEdgeCochain, quad_0, quad_1, quad_2, quad_3, res_self_site] using
      hq 2 3 (U 2 ⊓ U 3) inf_le_left inf_le_right

end CartierCechFour

end
end


section

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2ActualCartierFirstExact

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace MvPolynomial
open CycleQ2GeometricSeedNormalIdeals CycleQ2ActualSurfaceTower
open CycleQ2SeedQuotientFiniteFree CycleQ2GeometricCartierNormalLift
open CartierCechCoverTransfer CartierCechModuleComparison CartierCechCoordinates

private theorem baseVariable (r : ℂ) (i : Fin 3) :
    algebraMap (CycleQ2SeedQuotientFiniteFree.Base ℂ) (SurfaceRing r 1) (X i) =
      CycleQ2GeometricCartierNormalLift.surfaceQuotient r 1 (X (remainingIndex i)) := by
  change (Ideal.Quotient.mk _) (remainingInclusion ℂ (X i)) = _
  simp only [remainingInclusion, rename_X]
  rfl

theorem baseCoordinateIdeal (r : ℂ) :
    Ideal.span (Set.range (fun i : Fin 3 =>
      algebraMap (CycleQ2SeedQuotientFiniteFree.Base ℂ) (SurfaceRing r 1) (X i))) =
      surfaceCoordinateIdeal r 1 := by
  unfold surfaceCoordinateIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    change algebraMap (CycleQ2SeedQuotientFiniteFree.Base ℂ) (SurfaceRing r 1) (X i) ∈ _
    rw [baseVariable]
    fin_cases i <;> simp [remainingIndex]
  · intro hx
    rcases hx with rfl | hx
    · exact ⟨0, baseVariable r 0⟩
    · rcases hx with rfl | hx
      · exact ⟨1, baseVariable r 1⟩
      · rcases hx with rfl
        exact ⟨2, baseVariable r 2⟩

local instance chartBaseModule (r : ℂ) :
    Module CycleQ2ActualSurfaceTower.Base (SurfaceRing r 1) :=
  Submodule.Quotient.module' (S := CycleQ2ActualSurfaceTower.Base) (CycleQ2ConormalJacobian.surfaceIdeal r 1)

local instance chartBaseTower (r : ℂ) :
    IsScalarTower CycleQ2ActualSurfaceTower.Base (SurfaceRing r 1) (SurfaceRing r 1) where
  smul_assoc b a z := by
    change (b • a) * z = b • (a * z)
    rw [surfaceBase_smul, surfaceBase_smul, mul_assoc]

local instance chartBaseComm (r : ℂ) :
    SMulCommClass (SurfaceRing r 1) CycleQ2ActualSurfaceTower.Base (SurfaceRing r 1) where
  smul_comm a b z := by
    change a * (b • z) = b • (a * z)
    rw [surfaceBase_smul, surfaceBase_smul]
    ring

local instance inverseBaseModule (r : ℂ) :
    Module CycleQ2ActualSurfaceTower.Base (ActualInverseIdeal r) := by
  unfold ActualInverseIdeal
  exact LinearMap.module

local instance inverseSurfaceModule (r : ℂ) :
    Module (SurfaceRing r 1) (ActualInverseIdeal r) := by
  unfold ActualInverseIdeal
  exact LinearMap.module

local instance inverseBaseTower (r : ℂ) :
    IsScalarTower CycleQ2ActualSurfaceTower.Base (SurfaceRing r 1) (ActualInverseIdeal r) where
  smul_assoc b a ν := by
    apply LinearMap.ext
    intro x
    change ((b • a) : SurfaceRing r 1) * ν x = b • (a * ν x)
    exact smul_assoc b a (ν x)

/-- The actual inverse-ideal sheaf has exact first Čech complex on the
four Cartier opens of the actual theta=1 surface, for every nonzero r. -/
theorem inverseIdeal_four_cover_firstExact (r : ℂ) (hr : r ≠ 0) :
    FirstExact (moduleSheaf (SurfaceRing r 1) (ActualInverseIdeal r))
      (fun i : Fin 4 => PrimeSpectrum.basicOpen (coverElement r 1 i)) := by
  apply principal_firstExact_of_polynomial_basis ℂ (SurfaceRing r 1) (ActualInverseIdeal r)
    (actualInverseIdealBaseBasis r) (coverElement r 1)
  rw [baseCoordinateIdeal]
  exact cover_radical_eq_coordinate_radical r 1 hr (by norm_num)

theorem literal_inverseIdeal_four_cover_firstExact :
    FirstExact (moduleSheaf (SurfaceRing 57 1) (ActualInverseIdeal 57))
      (fun i : Fin 4 => PrimeSpectrum.basicOpen (coverElement 57 1 i)) :=
  inverseIdeal_four_cover_firstExact 57 (by norm_num)

end CycleQ2ActualCartierFirstExact

end
end


section

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2CartierSurfaceGrading

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift

def weight : Fin 5 → ℕ := ![1, 1, 1, 1, 2]

abbrev PolynomialGrade (d : ℕ) : Submodule ℂ WeightedPoly :=
  weightedHomogeneousSubmodule ℂ weight d

attribute [local instance] MvPolynomial.weightedGradedAlgebra

private theorem x0 : (X (0 : Fin 5) : WeightedPoly).IsWeightedHomogeneous weight 1 := by
  simpa only [weight, Matrix.cons_val_zero] using isWeightedHomogeneous_X ℂ weight (0 : Fin 5)

private theorem x1 : (X (1 : Fin 5) : WeightedPoly).IsWeightedHomogeneous weight 1 := by
  simpa [weight] using isWeightedHomogeneous_X ℂ weight (1 : Fin 5)

private theorem x2 : (X (2 : Fin 5) : WeightedPoly).IsWeightedHomogeneous weight 1 := by
  simpa [weight] using isWeightedHomogeneous_X ℂ weight (2 : Fin 5)

private theorem x3 : (X (3 : Fin 5) : WeightedPoly).IsWeightedHomogeneous weight 1 := by
  simpa [weight] using isWeightedHomogeneous_X ℂ weight (3 : Fin 5)

private theorem x4 : (X (4 : Fin 5) : WeightedPoly).IsWeightedHomogeneous weight 2 := by
  simpa [weight] using isWeightedHomogeneous_X ℂ weight (4 : Fin 5)

theorem originalF1_homogeneous (r : ℂ) : originalF1 r ∈ PolynomialGrade 2 := by
  exact (x0.pow 2).sub (((x1.C_mul r).mul x3))

theorem originalF2_homogeneous : originalF2 ∈ PolynomialGrade 2 :=
  x4.add (x2.pow 2)

theorem originalG1_homogeneous (r : ℂ) : originalG1 r ∈ PolynomialGrade 4 :=
  ((x0.pow 4).add ((((x0.pow 2).C_mul r).mul x1).mul x3)).add
    (((x1.pow 2).C_mul (r ^ 2)).mul (x3.pow 2))

theorem originalG2_homogeneous : originalG2 ∈ PolynomialGrade 4 :=
  ((x4.pow 2).sub (x4.mul (x2.pow 2))).add (x2.pow 4)

theorem originalB_homogeneous : originalB ∈ PolynomialGrade 3 :=
  ((((x3.pow 3).add (x2.pow 3)).add ((x1.mul x2).mul x3)).add
    ((x0.mul x2).mul x3)).add (x0.mul (x1.pow 2))

theorem originalH_homogeneous : originalH ∈ PolynomialGrade 3 :=
  originalB_homogeneous.sub (((x1.pow 3).add (x3.pow 3)).C_mul Complex.I)

theorem originalK_homogeneous : originalK ∈ PolynomialGrade 3 :=
  originalB_homogeneous.add (((x1.pow 3).add (x3.pow 3)).C_mul Complex.I)

theorem thetaH_homogeneous (θ : ℂ) : thetaH θ ∈ PolynomialGrade 3 :=
  originalH_homogeneous.add ((x0.pow 3).C_mul θ)

theorem thetaK_homogeneous (θ : ℂ) : thetaK θ ∈ PolynomialGrade 3 :=
  originalK_homogeneous.add ((x0.pow 3).C_mul θ)

theorem actualSeedEquation_homogeneous (r θ : ℂ) :
    actualSeedEquation r θ ∈ PolynomialGrade 6 :=
  (((originalF1_homogeneous r).mul (originalG1_homogeneous r)).add
    (originalF2_homogeneous.mul originalG2_homogeneous)).add
      ((thetaH_homogeneous θ).mul (thetaK_homogeneous θ))

theorem derivativeA_homogeneous : derivativeA ∈ PolynomialGrade 6 :=
  (x2.mul (x3.pow 3)).mul x4

theorem surfaceIdeal_homogeneous (r θ : ℂ) :
    (surfaceIdeal r θ).IsHomogeneous PolynomialGrade := by
  apply Ideal.homogeneous_span
  rintro p ⟨i, rfl⟩
  fin_cases i
  · exact ⟨6, actualSeedEquation_homogeneous r θ⟩
  · exact ⟨3, thetaH_homogeneous θ⟩

/-- The genuine weighted grading on the actual surface quotient. -/
abbrev surfaceGrade (r θ : ℂ) (d : ℕ) : Submodule ℂ (SurfaceRing r θ) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
    PolynomialGrade (surfaceIdeal r θ) d

instance surfaceGradedRing (r θ : ℂ) : GradedRing (surfaceGrade r θ) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing
    PolynomialGrade (surfaceIdeal r θ) (surfaceIdeal_homogeneous r θ)

theorem surfaceQuotient_mem_grade (r θ : ℂ) {d : ℕ} {p : WeightedPoly}
    (hp : p ∈ PolynomialGrade d) : surfaceQuotient r θ p ∈ surfaceGrade r θ d :=
  ⟨p, hp, rfl⟩

def coverDegree : Fin 4 → ℕ := ![4, 4, 2, 2]

theorem coverElement_mem_grade (r θ : ℂ) (i : Fin 4) :
    coverElement r θ i ∈ surfaceGrade r θ (coverDegree i) := by
  fin_cases i
  · exact surfaceQuotient_mem_grade r θ (originalG1_homogeneous r)
  · exact surfaceQuotient_mem_grade r θ originalG2_homogeneous
  · exact surfaceQuotient_mem_grade r θ (originalF1_homogeneous r)
  · exact surfaceQuotient_mem_grade r θ originalF2_homogeneous

def coverProductDegree (s : Finset (Fin 4)) : ℕ := ∑ i ∈ s, coverDegree i

theorem coverProduct_mem_grade (r θ : ℂ) (s : Finset (Fin 4)) :
    coverProduct r θ s ∈ surfaceGrade r θ (coverProductDegree s) := by
  exact SetLike.prod_mem_graded (surfaceGrade r θ) coverDegree (coverElement r θ)
    (fun i _ => coverElement_mem_grade r θ i)

end CycleQ2CartierSurfaceGrading
end

end


section

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2CartierHomogeneousCech

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading
  CycleQ2CartierInverseIdealCech

private theorem awayLift_eq_algHom {A V : Type*} [CommRing A] [CommRing V]
    [Algebra A V] (a : A) (hu : IsUnit (algebraMap A V a))
    (ρ : Localization.Away a →ₐ[A] V) :
    Localization.awayLift (algebraMap A V) a hu = ρ.toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  apply RingHom.ext
  intro x
  change IsLocalization.Away.lift a hu (algebraMap A (Localization.Away a) x) =
    ρ (algebraMap A (Localization.Away a) x)
  rw [IsLocalization.Away.lift_eq, ρ.commutes]

abbrev HomogeneousCoverLocal (r θ : ℂ) (s : Finset (Fin 4)) :=
  HomogeneousLocalization.Away (surfaceGrade r θ) (coverProduct r θ s)

theorem coverProduct_factor (r θ : ℂ) {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    coverProduct r θ t = coverProduct r θ s * coverProduct r θ (t \ s) := by
  unfold coverProduct
  rw [mul_comm]
  exact (Finset.prod_sdiff hst).symm

/-- The genuine degree-zero restriction between the homogeneous localizations. -/
def homogeneousCoverRestriction (r θ : ℂ) {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    HomogeneousCoverLocal r θ s →+* HomogeneousCoverLocal r θ t :=
  HomogeneousLocalization.awayMap (surfaceGrade r θ)
    (coverProduct_mem_grade r θ (t \ s)) (coverProduct_factor r θ hst)

@[simp] theorem homogeneousCoverRestriction_val (r θ : ℂ) {s t : Finset (Fin 4)}
    (hst : s ⊆ t) (z : HomogeneousCoverLocal r θ s) :
    (homogeneousCoverRestriction r θ hst z).val = coverRestriction r θ hst z.val := by
  rw [homogeneousCoverRestriction, HomogeneousLocalization.val_awayMap]
  have hu : IsUnit (algebraMap (SurfaceRing r θ) (CoverLocal r θ t) (coverProduct r θ s)) :=
    isUnit_of_dvd_unit
      (map_dvd _ ⟨coverProduct r θ (t \ s), coverProduct_factor r θ hst⟩)
      (IsLocalization.Away.algebraMap_isUnit (coverProduct r θ t))
  have hm : Localization.awayLift (algebraMap (SurfaceRing r θ) (CoverLocal r θ t))
      (coverProduct r θ s) hu =
      (coverRestriction r θ hst).toRingHom :=
    awayLift_eq_algHom (coverProduct r θ s) hu (coverRestriction r θ hst)
  exact DFunLike.congr_fun hm z.val

theorem homogeneousCoverRestriction_comp (r θ : ℂ) {s t u : Finset (Fin 4)}
    (hst : s ⊆ t) (htu : t ⊆ u) (z : HomogeneousCoverLocal r θ s) :
    homogeneousCoverRestriction r θ htu (homogeneousCoverRestriction r θ hst z) =
      homogeneousCoverRestriction r θ (hst.trans htu) z := by
  apply HomogeneousLocalization.val_injective
  simp only [homogeneousCoverRestriction_val, coverRestriction_comp_apply]

private theorem numerator012_homogeneous :
    surfaceQuotient 57 1 (-derivativeA * originalG2) ∈
      surfaceGrade 57 1 (1 • coverProductDegree {0,1,2}) := by
  change _ ∈ surfaceGrade 57 1 10
  exact surfaceQuotient_mem_grade 57 1
    (derivativeA_homogeneous.neg.mul originalG2_homogeneous)

private theorem numerator013_homogeneous :
    surfaceQuotient 57 1 (derivativeA * originalG1 57) ∈
      surfaceGrade 57 1 (1 • coverProductDegree {0,1,3}) := by
  change _ ∈ surfaceGrade 57 1 10
  exact surfaceQuotient_mem_grade 57 1
    (derivativeA_homogeneous.mul (originalG1_homogeneous 57))

def literalHomogeneousBoundary012 : HomogeneousCoverLocal 57 1 {0,1,2} :=
  HomogeneousLocalization.Away.mk (surfaceGrade 57 1)
    (coverProduct_mem_grade 57 1 {0,1,2}) 1
    (surfaceQuotient 57 1 (-derivativeA * originalG2)) numerator012_homogeneous

def literalHomogeneousBoundary013 : HomogeneousCoverLocal 57 1 {0,1,3} :=
  HomogeneousLocalization.Away.mk (surfaceGrade 57 1)
    (coverProduct_mem_grade 57 1 {0,1,3}) 1
    (surfaceQuotient 57 1 (derivativeA * originalG1 57)) numerator013_homogeneous

private theorem cancel_first_third {R : Type*} [CommRing R]
    (a : R) (u v w : Rˣ) :
    (a * (↑(u⁻¹) : R) * (↑(w⁻¹) : R)) * ((u : R) * (v : R) * (w : R)) =
      a * (v : R) := by
  calc
    _ = a * (v : R) * ((↑(u⁻¹) : R) * (u : R)) *
        ((↑(w⁻¹) : R) * (w : R)) := by ring
    _ = _ := by rw [Units.inv_mul, Units.inv_mul, mul_one, mul_one]

private theorem cancel_second_third {R : Type*} [CommRing R]
    (a : R) (u v w : Rˣ) :
    (a * (↑(v⁻¹) : R) * (↑(w⁻¹) : R)) * ((u : R) * (v : R) * (w : R)) =
      a * (u : R) := by
  calc
    _ = a * (u : R) * ((↑(v⁻¹) : R) * (v : R)) *
        ((↑(w⁻¹) : R) * (w : R)) := by ring
    _ = _ := by rw [Units.inv_mul, Units.inv_mul, mul_one, mul_one]

theorem literalHomogeneousBoundary012_val :
    literalHomogeneousBoundary012.val = boundary012 57 1 derivativeA 0 := by
  have hden : algebraMap (SurfaceRing 57 1) (CoverLocal 57 1 {0,1,2})
      (coverProduct 57 1 {0,1,2}) =
      (coverUnit 57 1 {0,1,2} 0 (by simp) : CoverLocal 57 1 {0,1,2}) *
      (coverUnit 57 1 {0,1,2} 1 (by simp) : CoverLocal 57 1 {0,1,2}) *
      (coverUnit 57 1 {0,1,2} 2 (by simp) : CoverLocal 57 1 {0,1,2}) := by
    simp [coverProduct, map_mul, coverUnit_value, mul_assoc]
  simp only [literalHomogeneousBoundary012, HomogeneousLocalization.Away.val_mk, pow_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  change coverPolyMap 57 1 {0,1,2} (-derivativeA * originalG2) = _
  rw [hden, literal_ambient_boundary012, map_mul, map_neg]
  have hg : coverPolyMap 57 1 {0,1,2} originalG2 =
      (coverUnit 57 1 {0,1,2} 1 (by simp) : CoverLocal 57 1 {0,1,2}) := by
    rw [coverUnit_value]
    rfl
  rw [hg]
  exact (cancel_first_third (-coverPolyMap 57 1 {0,1,2} derivativeA)
    (coverUnit 57 1 {0,1,2} 0 (by simp))
    (coverUnit 57 1 {0,1,2} 1 (by simp))
    (coverUnit 57 1 {0,1,2} 2 (by simp))).symm

theorem literalHomogeneousBoundary013_val :
    literalHomogeneousBoundary013.val = boundary013 57 1 derivativeA 0 := by
  have hden : algebraMap (SurfaceRing 57 1) (CoverLocal 57 1 {0,1,3})
      (coverProduct 57 1 {0,1,3}) =
      (coverUnit 57 1 {0,1,3} 0 (by simp) : CoverLocal 57 1 {0,1,3}) *
      (coverUnit 57 1 {0,1,3} 1 (by simp) : CoverLocal 57 1 {0,1,3}) *
      (coverUnit 57 1 {0,1,3} 3 (by simp) : CoverLocal 57 1 {0,1,3}) := by
    simp [coverProduct, map_mul, coverUnit_value, mul_assoc]
  simp only [literalHomogeneousBoundary013, HomogeneousLocalization.Away.val_mk, pow_one]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  change coverPolyMap 57 1 {0,1,3} (derivativeA * originalG1 57) = _
  rw [hden, literal_ambient_boundary013, map_mul]
  have hg : coverPolyMap 57 1 {0,1,3} (originalG1 57) =
      (coverUnit 57 1 {0,1,3} 0 (by simp) : CoverLocal 57 1 {0,1,3}) := by
    rw [coverUnit_value]
    rfl
  rw [hg]
  exact (cancel_second_third (coverPolyMap 57 1 {0,1,3} derivativeA)
    (coverUnit 57 1 {0,1,3} 0 (by simp))
    (coverUnit 57 1 {0,1,3} 1 (by simp))
    (coverUnit 57 1 {0,1,3} 3 (by simp))).symm

abbrev HomogeneousScalarOne (r θ : ℂ) :=
  HomogeneousCoverLocal r θ {0,1} × HomogeneousCoverLocal r θ {0,2} ×
    HomogeneousCoverLocal r θ {0,3} × HomogeneousCoverLocal r θ {1,2} ×
      HomogeneousCoverLocal r θ {1,3} × HomogeneousCoverLocal r θ {2,3}

abbrev HomogeneousScalarTwo (r θ : ℂ) :=
  FourFaces (HomogeneousCoverLocal r θ {0,1,2}) (HomogeneousCoverLocal r θ {0,1,3})
    (HomogeneousCoverLocal r θ {0,2,3}) (HomogeneousCoverLocal r θ {1,2,3})

def forgetOne (r θ : ℂ) (c : HomogeneousScalarOne r θ) : ScalarOne r θ :=
  ⟨c.1.val, c.2.1.val, c.2.2.1.val, c.2.2.2.1.val, c.2.2.2.2.1.val, c.2.2.2.2.2.val⟩

def forgetTwo (r θ : ℂ) (c : HomogeneousScalarTwo r θ) : SurfaceCechTwo r θ :=
  ⟨c.face012.val, c.face013.val, c.face023.val, c.face123.val⟩

def homogeneousOneDifferential (r θ : ℂ) (c : HomogeneousScalarOne r θ) :
    HomogeneousScalarTwo r θ :=
  ⟨homogeneousCoverRestriction r θ (show ({1,2}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.2.2.2.1 -
      homogeneousCoverRestriction r θ (show ({0,2}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.2.1 +
      homogeneousCoverRestriction r θ (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.1,
   homogeneousCoverRestriction r θ (show ({1,3}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.2.2.2.2.1 -
      homogeneousCoverRestriction r θ (show ({0,3}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.2.2.1 +
      homogeneousCoverRestriction r θ (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.1,
   homogeneousCoverRestriction r θ (show ({2,3}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.2.2.2.2 -
      homogeneousCoverRestriction r θ (show ({0,3}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.2.1 +
      homogeneousCoverRestriction r θ (show ({0,2}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.1,
   homogeneousCoverRestriction r θ (show ({2,3}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.2.2 -
      homogeneousCoverRestriction r θ (show ({1,3}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.2.1 +
      homogeneousCoverRestriction r θ (show ({1,2}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.1⟩

theorem forgetOneDifferential (r θ : ℂ) (c : HomogeneousScalarOne r θ) :
    forgetTwo r θ (homogeneousOneDifferential r θ c) =
      scalarOneDifferential r θ (forgetOne r θ c) := by
  simp only [forgetTwo, homogeneousOneDifferential, scalarOneDifferential, forgetOne,
    HomogeneousLocalization.val_add, HomogeneousLocalization.val_sub,
    homogeneousCoverRestriction_val]

def homogeneousTwoDifferential (r θ : ℂ) (c : HomogeneousScalarTwo r θ) :
    HomogeneousCoverLocal r θ Finset.univ :=
  homogeneousCoverRestriction r θ (Finset.subset_univ {1,2,3}) c.face123 -
    homogeneousCoverRestriction r θ (Finset.subset_univ {0,2,3}) c.face023 +
    homogeneousCoverRestriction r θ (Finset.subset_univ {0,1,3}) c.face013 -
    homogeneousCoverRestriction r θ (Finset.subset_univ {0,1,2}) c.face012

theorem forgetTwoDifferential (r θ : ℂ) (c : HomogeneousScalarTwo r θ) :
    (homogeneousTwoDifferential r θ c).val = surfaceCechTwoDifferential r θ (forgetTwo r θ c) := by
  simp only [homogeneousTwoDifferential, surfaceCechTwoDifferential, forgetTwo,
    HomogeneousLocalization.val_add, HomogeneousLocalization.val_sub,
    homogeneousCoverRestriction_val]

def literalHomogeneousCartierCochain : HomogeneousScalarTwo 57 1 :=
  ⟨literalHomogeneousBoundary012, literalHomogeneousBoundary013, 0, 0⟩

theorem literalHomogeneousCartierCochain_forget :
    forgetTwo 57 1 literalHomogeneousCartierCochain =
      cartierBoundaryTwoCochain 57 1 derivativeA 0 := by
  simp only [forgetTwo, literalHomogeneousCartierCochain, cartierBoundaryTwoCochain,
    literalHomogeneousBoundary012_val, literalHomogeneousBoundary013_val,
    HomogeneousLocalization.val_zero]

/-- The literal Cartier class is represented by an actual degree-zero cocycle. -/
theorem literalHomogeneousCartierCochain_cocycle :
    homogeneousTwoDifferential 57 1 literalHomogeneousCartierCochain = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [forgetTwoDifferential, literalHomogeneousCartierCochain_forget,
    cartierBoundaryTwoCochain_cocycle, HomogeneousLocalization.val_zero]

/-- Forgetting homogeneous degree sends a boundary to an actual scalar boundary.
No injectivity assertion about derived cohomology is used. -/
theorem literalHomogeneousCartierCochain_not_boundary (he : InverseFirstExact 57 1) :
    ¬ ∃ c : HomogeneousScalarOne 57 1,
      homogeneousOneDifferential 57 1 c = literalHomogeneousCartierCochain := by
  rintro ⟨c, hc⟩
  apply literal_cartierBoundary_not_boundary he
  refine ⟨forgetOne 57 1 c, ?_⟩
  rw [← forgetOneDifferential, hc, literalHomogeneousCartierCochain_forget]

end CycleQ2CartierHomogeneousCech
end

end


section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CartierProjectiveCover

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2CartierHomogeneousCech

def projectiveSurface (r θ : ℂ) : Scheme := Proj (surfaceGrade r θ)

def coordinatePatch (r θ : ℂ) (j : Fin 5) : (projectiveSurface r θ).Opens :=
  Proj.basicOpen (surfaceGrade r θ) (surfaceQuotient r θ (X j))

def coverPatch (r θ : ℂ) (s : Finset (Fin 4)) : (projectiveSurface r θ).Opens :=
  Proj.basicOpen (surfaceGrade r θ) (coverProduct r θ s)

def coverFamily (r θ : ℂ) (i : Fin 4) : (projectiveSurface r θ).Opens :=
  Proj.basicOpen (surfaceGrade r θ) (coverElement r θ i)

theorem irrelevant_le_coordinateIdeal (r θ : ℂ) :
    (HomogeneousIdeal.irrelevant (surfaceGrade r θ)).toIdeal ≤
      Ideal.span (Set.range (fun j : Fin 5 => surfaceQuotient r θ (X j))) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn q hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hpI : p ∈ MvPolynomial.idealOfVars (Fin 5) ℂ := by
    have hpow : p ∈ MvPolynomial.idealOfVars (Fin 5) ℂ ^ 1 := by
      apply (MvPolynomial.mem_pow_idealOfVars_iff' 1 p).mpr
      intro e he
      have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
      subst e
      by_contra hc
      have hz : 0 = n := by simpa only [map_zero] using hp hc
      omega
    simpa only [pow_one] using hpow
  have hmap : MvPolynomial.idealOfVars (Fin 5) ℂ ≤
      (Ideal.span (Set.range (fun j : Fin 5 => surfaceQuotient r θ (X j)))).comap
        (surfaceQuotient r θ) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨j, rfl⟩
  exact hmap hpI

theorem coordinatePatches_cover (r θ : ℂ) :
    (⨆ j : Fin 5, coordinatePatch r θ j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (surfaceGrade r θ) _ (irrelevant_le_coordinateIdeal r θ)

/-- The four actual Cartier denominator patches cover the actual projective surface. -/
theorem projective_four_cover (r θ : ℂ) (hr : r ≠ 0) :
    (⨆ i : Fin 4, coverFamily r θ i) = ⊤ := by
  apply top_le_iff.mp
  intro q _
  have hq : q ∈ ⨆ j : Fin 5, coordinatePatch r θ j := by
    rw [coordinatePatches_cover]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hq
  let : q.asHomogeneousIdeal.toIdeal.IsPrime := q.isPrime
  obtain ⟨i, hi⟩ := surface_relevant_prime_cover r θ hr q.asHomogeneousIdeal.toIdeal ⟨j, hj⟩
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

@[simp] theorem coverPatch_singleton (r θ : ℂ) (i : Fin 4) :
    coverPatch r θ {i} = coverFamily r θ i := by
  simp [coverPatch, coverFamily, coverProduct]

theorem coverPatch_pair (r θ : ℂ) (i j : Fin 4) :
    coverPatch r θ {i,j} = coverFamily r θ i ⊓ coverFamily r θ j := by
  by_cases hij : i = j
  · subst j
    simp
  · simp [coverPatch, coverFamily, coverProduct, Finset.prod_pair hij, Proj.basicOpen_mul]

theorem coverPatch_mono (r θ : ℂ) {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    coverPatch r θ t ≤ coverPatch r θ s :=
  Proj.basicOpen_mono (surfaceGrade r θ) (coverProduct r θ s) (coverProduct r θ t)
    ⟨coverProduct r θ (t \ s), coverProduct_factor r θ hst⟩

theorem coverDegree_pos (i : Fin 4) : 0 < coverDegree i := by
  fin_cases i <;> decide

theorem coverProductDegree_pos {s : Finset (Fin 4)} (hs : s.Nonempty) :
    0 < coverProductDegree s := by
  obtain ⟨i, hi⟩ := hs
  exact (coverDegree_pos i).trans_le (Finset.single_le_sum (fun j _ => Nat.zero_le (coverDegree j)) hi)

/-- Each nonempty finite intersection is the canonical affine Proj chart. -/
def coverChart (r θ : ℂ) (s : Finset (Fin 4)) (hs : s.Nonempty) :
    (coverPatch r θ s).toScheme ≅ Spec (CommRingCat.of (HomogeneousCoverLocal r θ s)) :=
  Proj.basicOpenIsoSpec (surfaceGrade r θ) (coverProduct r θ s)
    (coverProduct_mem_grade r θ s) (coverProductDegree_pos hs)

def coverSectionsEquiv (r θ : ℂ) (s : Finset (Fin 4)) (hs : s.Nonempty) :
    HomogeneousCoverLocal r θ s ≃+* Γ(projectiveSurface r θ, coverPatch r θ s) :=
  (Proj.basicOpenIsoAway (surfaceGrade r θ) (coverProduct r θ s)
    (coverProduct_mem_grade r θ s) (coverProductDegree_pos hs)).commRingCatIsoToRingEquiv

/-- The degree-zero localization maps are exactly the structure-sheaf restrictions. -/
theorem coverSectionsEquiv_restrict (r θ : ℂ) {s t : Finset (Fin 4)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) (z : HomogeneousCoverLocal r θ s) :
    (projectiveSurface r θ).presheaf.map (homOfLE (coverPatch_mono r θ hst)).op
      (coverSectionsEquiv r θ s hs z) =
        coverSectionsEquiv r θ t ht (homogeneousCoverRestriction r θ hst z) := by
  exact congrArg (fun k => k z)
    (Proj.awayMap_awayToSection (surfaceGrade r θ)
      (coverProduct_mem_grade r θ (t \ s)) (coverProduct_factor r θ hst)).symm

open CycleQ2GeometricProjectiveHOne

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual affine-chart vanishing in the ambient sheaf category. -/
theorem coverPatch_H_one_subsingleton (r θ : ℂ) (s : Finset (Fin 4)) (hs : s.Nonempty) :
    Subsingleton ((structureAdditiveSheaf (projectiveSurface r θ)).H' 1 (coverPatch r θ s)) :=
  affineFrameHOne_subsingleton (coverChart r θ s hs)
    (structureAdditiveSheaf (projectiveSurface r θ)) (Iso.refl _)

end CycleQ2CartierProjectiveCover
end

end


section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveCartierCochain

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricCartierNormalLift CycleQ2CartierHomogeneousCech
  CycleQ2CartierProjectiveCover CycleQ2CartierInverseIdealCech

abbrev Sections (r θ : ℂ) (s : Finset (Fin 4)) :=
  Γ(projectiveSurface r θ, coverPatch r θ s)

def restriction (r θ : ℂ) {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    Sections r θ s →+* Sections r θ t :=
  ((projectiveSurface r θ).presheaf.map (homOfLE (coverPatch_mono r θ hst)).op).hom

theorem fromSections_restriction (r θ : ℂ) {s t : Finset (Fin 4)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) (a : Sections r θ s) :
    (coverSectionsEquiv r θ t ht).symm (restriction r θ hst a) =
      homogeneousCoverRestriction r θ hst ((coverSectionsEquiv r θ s hs).symm a) := by
  apply (coverSectionsEquiv r θ t ht).injective
  simpa only [restriction, RingEquiv.apply_symm_apply] using
    coverSectionsEquiv_restrict r θ hs ht hst ((coverSectionsEquiv r θ s hs).symm a)

abbrev One (r θ : ℂ) :=
  Sections r θ {0,1} × Sections r θ {0,2} × Sections r θ {0,3} ×
    Sections r θ {1,2} × Sections r θ {1,3} × Sections r θ {2,3}

abbrev Two (r θ : ℂ) :=
  FourFaces (Sections r θ {0,1,2}) (Sections r θ {0,1,3})
    (Sections r θ {0,2,3}) (Sections r θ {1,2,3})

def fromOne (r θ : ℂ) (c : One r θ) : HomogeneousScalarOne r θ :=
  ⟨(coverSectionsEquiv r θ {0,1} (by simp)).symm c.1,
   (coverSectionsEquiv r θ {0,2} (by simp)).symm c.2.1,
   (coverSectionsEquiv r θ {0,3} (by simp)).symm c.2.2.1,
   (coverSectionsEquiv r θ {1,2} (by simp)).symm c.2.2.2.1,
   (coverSectionsEquiv r θ {1,3} (by simp)).symm c.2.2.2.2.1,
   (coverSectionsEquiv r θ {2,3} (by simp)).symm c.2.2.2.2.2⟩

def fromTwo (r θ : ℂ) (c : Two r θ) : HomogeneousScalarTwo r θ :=
  ⟨(coverSectionsEquiv r θ {0,1,2} (by simp)).symm c.face012,
   (coverSectionsEquiv r θ {0,1,3} (by simp)).symm c.face013,
   (coverSectionsEquiv r θ {0,2,3} (by simp)).symm c.face023,
   (coverSectionsEquiv r θ {1,2,3} (by simp)).symm c.face123⟩

/-- The differential formed from the actual projective structure-sheaf restrictions. -/
def oneDifferential (r θ : ℂ) (c : One r θ) : Two r θ :=
  ⟨restriction r θ (show ({1,2}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.2.2.2.1 -
      restriction r θ (show ({0,2}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.2.1 +
      restriction r θ (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,2} by simp) c.1,
   restriction r θ (show ({1,3}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.2.2.2.2.1 -
      restriction r θ (show ({0,3}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.2.2.1 +
      restriction r θ (show ({0,1}:Finset (Fin 4)) ⊆ {0,1,3} by simp) c.1,
   restriction r θ (show ({2,3}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.2.2.2.2 -
      restriction r θ (show ({0,3}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.2.1 +
      restriction r θ (show ({0,2}:Finset (Fin 4)) ⊆ {0,2,3} by simp) c.2.1,
   restriction r θ (show ({2,3}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.2.2 -
      restriction r θ (show ({1,3}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.2.1 +
      restriction r θ (show ({1,2}:Finset (Fin 4)) ⊆ {1,2,3} by simp) c.2.2.2.1⟩

theorem fromOneDifferential (r θ : ℂ) (c : One r θ) :
    fromTwo r θ (oneDifferential r θ c) =
      homogeneousOneDifferential r θ (fromOne r θ c) := by
  simp [fromTwo, oneDifferential, homogeneousOneDifferential, fromOne,
    fromSections_restriction]

def twoDifferential (r θ : ℂ) (c : Two r θ) : Sections r θ Finset.univ :=
  restriction r θ (Finset.subset_univ {1,2,3}) c.face123 -
    restriction r θ (Finset.subset_univ {0,2,3}) c.face023 +
    restriction r θ (Finset.subset_univ {0,1,3}) c.face013 -
    restriction r θ (Finset.subset_univ {0,1,2}) c.face012

theorem fromTwoDifferential (r θ : ℂ) (c : Two r θ) :
    (coverSectionsEquiv r θ Finset.univ (by simp)).symm (twoDifferential r θ c) =
      homogeneousTwoDifferential r θ (fromTwo r θ c) := by
  simp [twoDifferential, homogeneousTwoDifferential, fromTwo,
    fromSections_restriction]

/-- The actual Cartier cocycle expressed in sections of the actual projective surface. -/
def literalProjectiveCartierCochain : Two 57 1 :=
  ⟨coverSectionsEquiv 57 1 {0,1,2} (by simp) literalHomogeneousBoundary012,
   coverSectionsEquiv 57 1 {0,1,3} (by simp) literalHomogeneousBoundary013, 0, 0⟩

theorem literalProjectiveCartierCochain_from :
    fromTwo 57 1 literalProjectiveCartierCochain = literalHomogeneousCartierCochain := by
  simp only [fromTwo, literalProjectiveCartierCochain, literalHomogeneousCartierCochain,
    RingEquiv.symm_apply_apply, map_zero]

theorem literalProjectiveCartierCochain_cocycle :
    twoDifferential 57 1 literalProjectiveCartierCochain = 0 := by
  apply (coverSectionsEquiv 57 1 Finset.univ (by simp)).symm.injective
  rw [fromTwoDifferential, literalProjectiveCartierCochain_from,
    literalHomogeneousCartierCochain_cocycle, map_zero]

theorem literalProjectiveCartierCochain_not_boundary (he : InverseFirstExact 57 1) :
    ¬ ∃ c : One 57 1, oneDifferential 57 1 c = literalProjectiveCartierCochain := by
  rintro ⟨c, hc⟩
  apply literalHomogeneousCartierCochain_not_boundary he
  refine ⟨fromOne 57 1 c, ?_⟩
  rw [← fromOneDifferential, hc, literalProjectiveCartierCochain_from]

end CycleQ2ProjectiveCartierCochain
end

end


section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ActualCartierNonboundary

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierInverseIdealCech CycleQ2InverseIdealSheaf
  CycleQ2GeometricSheafLocalIso CartierCechCoverTransfer CartierCechModuleComparison

private theorem restrict_self {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (U : Opens (PrimeSpectrum.Top A)) (s : CartierCechRefinement.Sections A M U) :
    CartierCechRefinement.restrict (le_refl U) s = s :=
  res_self (moduleSheaf A M) U s

abbrev inverseSheaf (r θ : ℂ) :=
  moduleSheaf (SurfaceRing r θ) ((curveIdealOnSurface r θ) →ₗ[SurfaceRing r θ] SurfaceRing r θ)

abbrev patch (r θ : ℂ) (i : Fin 4) := coverOpen r θ {i}

private theorem le_coverOpen (r θ : ℂ) (W : Opens (PrimeSpectrum.Top (SurfaceRing r θ)))
    (s : Finset (Fin 4)) (h : ∀ i ∈ s, W ≤ patch r θ i) : W ≤ coverOpen r θ s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [coverOpen, coverProduct, Finset.prod_empty, PrimeSpectrum.basicOpen_one]
      exact le_top
  | @insert i s hi ih =>
      change W ≤ PrimeSpectrum.basicOpen (coverProduct r θ (insert i s))
      rw [coverProduct, Finset.prod_insert hi, PrimeSpectrum.basicOpen_mul]
      exact le_inf (by simpa only [patch, coverOpen_singleton] using h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

def edgeSection (r θ : ℂ) (i j : Fin 4) (ν : CoverInverseIdeal r θ {i,j}) :
    (inverseSheaf r θ).obj.obj (op (patch r θ i ⊓ patch r θ j)) :=
  CartierCechRefinement.restrict (coverOpen_pair r θ i j).ge (coverSectionsEquiv r θ {i,j} ν)

private theorem triangle_equation {G : Type*} [AddCommGroup G]
    (a b c : G) (h : b - c + a = 0) : a + b = c := by
  calc
    a + b = (b - c + a) + c := by abel
    _ = c := by rw [h, zero_add]

/-- A zero face in the actual localized-Hom complex gives the section cocycle
identity on every subopen of the corresponding triple intersection. -/
theorem edgeSection_triangle (r θ : ℂ) (i j k : Fin 4)
    (cij : CoverInverseIdeal r θ {i,j}) (cik : CoverInverseIdeal r θ {i,k})
    (cjk : CoverInverseIdeal r θ {j,k})
    (hc : coverInverseRestriction r θ (show ({j,k}:Finset (Fin 4)) ⊆ {i,j,k} by simp) cjk -
      coverInverseRestriction r θ (show ({i,k}:Finset (Fin 4)) ⊆ {i,j,k} by simp) cik +
      coverInverseRestriction r θ (show ({i,j}:Finset (Fin 4)) ⊆ {i,j,k} by simp) cij = 0)
    (W : Opens (PrimeSpectrum.Top (SurfaceRing r θ)))
    (hi : W ≤ patch r θ i) (hj : W ≤ patch r θ j) (hk : W ≤ patch r θ k) :
    res (inverseSheaf r θ) (le_inf hi hj) (edgeSection r θ i j cij) +
      res (inverseSheaf r θ) (le_inf hj hk) (edgeSection r θ j k cjk) =
        res (inverseSheaf r θ) (le_inf hi hk) (edgeSection r θ i k cik) := by
  have hW : W ≤ coverOpen r θ {i,j,k} := le_coverOpen r θ W _ (by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk)
  have h := congrArg (fun ν : CoverInverseIdeal r θ {i,j,k} =>
    CartierCechRefinement.restrict hW (coverSectionsEquiv r θ {i,j,k} ν)) hc
  simp only [map_add, map_sub, map_zero, ← coverSectionsEquiv_restrict,
    CartierCechRefinement.restrict_comp] at h
  simp only [edgeSection, moduleSheaf_res, CartierCechRefinement.restrict_comp]
  exact triangle_equation _ _ _ h

/-- A primitive identity for actual sheaf sections transfers to the exact
localized inverse-Hom restriction maps used in the Cartier complex. -/
theorem edgeSection_primitive (r θ : ℂ) (i j : Fin 4)
    (cij : CoverInverseIdeal r θ {i,j})
    (qi : (inverseSheaf r θ).obj.obj (op (patch r θ i)))
    (qj : (inverseSheaf r θ).obj.obj (op (patch r θ j)))
    (h : edgeSection r θ i j cij =
      res (inverseSheaf r θ) inf_le_right qj - res (inverseSheaf r θ) inf_le_left qi) :
    coverInverseRestriction r θ (show ({j}:Finset (Fin 4)) ⊆ {i,j} by simp)
        ((coverSectionsEquiv r θ {j}).symm qj) -
      coverInverseRestriction r θ (show ({i}:Finset (Fin 4)) ⊆ {i,j} by simp)
        ((coverSectionsEquiv r θ {i}).symm qi) = cij := by
  apply (coverSectionsEquiv r θ {i,j}).injective
  rw [map_sub, ← coverSectionsEquiv_restrict, ← coverSectionsEquiv_restrict]
  simp only [LinearEquiv.apply_symm_apply]
  have h' := congrArg (CartierCechRefinement.restrict
    (M := (curveIdealOnSurface r θ) →ₗ[SurfaceRing r θ] SurfaceRing r θ)
    (coverOpen_pair r θ i j).le) h
  simpa only [edgeSection, moduleSheaf_res, map_sub,
    CartierCechRefinement.restrict_comp, restrict_self] using h'.symm

/-- This is a comparison of the actual four-open complexes, using the
section/local-Hom equivalences and their checked restriction squares. -/
theorem inverseFirstExact_of_sheaf (r θ : ℂ)
    (he : FirstExact (inverseSheaf r θ) (patch r θ)) : InverseFirstExact r θ := by
  intro c hc
  have h012 := congrArg Prod.fst hc
  have h013 := congrArg (fun z : InverseTwo r θ => z.2.1) hc
  have h023 := congrArg (fun z : InverseTwo r θ => z.2.2.1) hc
  have h123 := congrArg (fun z : InverseTwo r θ => z.2.2.2) hc
  change coverInverseRestriction r θ _ c.2.2.2.1 - coverInverseRestriction r θ _ c.2.1 +
    coverInverseRestriction r θ _ c.1 = 0 at h012
  change coverInverseRestriction r θ _ c.2.2.2.2.1 - coverInverseRestriction r θ _ c.2.2.1 +
    coverInverseRestriction r θ _ c.1 = 0 at h013
  change coverInverseRestriction r θ _ c.2.2.2.2.2 - coverInverseRestriction r θ _ c.2.2.1 +
    coverInverseRestriction r θ _ c.2.1 = 0 at h023
  change coverInverseRestriction r θ _ c.2.2.2.2.2 - coverInverseRestriction r θ _ c.2.2.2.2.1 +
    coverInverseRestriction r θ _ c.2.2.2.1 = 0 at h123
  obtain ⟨q, h01, h02, h03, h12, h13, h23⟩ :=
    CartierCechFour.sixEdge_primitive (inverseSheaf r θ) (patch r θ)
      (edgeSection r θ 0 1 c.1) (edgeSection r θ 0 2 c.2.1)
      (edgeSection r θ 0 3 c.2.2.1) (edgeSection r θ 1 2 c.2.2.2.1)
      (edgeSection r θ 1 3 c.2.2.2.2.1) (edgeSection r θ 2 3 c.2.2.2.2.2)
      (edgeSection_triangle r θ 0 1 2 _ _ _ h012)
      (edgeSection_triangle r θ 0 1 3 _ _ _ h013)
      (edgeSection_triangle r θ 0 2 3 _ _ _ h023)
      (edgeSection_triangle r θ 1 2 3 _ _ _ h123) he
  refine ⟨⟨(coverSectionsEquiv r θ {0}).symm (q 0),
    (coverSectionsEquiv r θ {1}).symm (q 1),
    (coverSectionsEquiv r θ {2}).symm (q 2),
    (coverSectionsEquiv r θ {3}).symm (q 3)⟩, ?_⟩
  apply Prod.ext
  · exact edgeSection_primitive r θ 0 1 c.1 (q 0) (q 1) h01
  apply Prod.ext
  · exact edgeSection_primitive r θ 0 2 c.2.1 (q 0) (q 2) h02
  apply Prod.ext
  · exact edgeSection_primitive r θ 0 3 c.2.2.1 (q 0) (q 3) h03
  apply Prod.ext
  · exact edgeSection_primitive r θ 1 2 c.2.2.2.1 (q 1) (q 2) h12
  apply Prod.ext
  · exact edgeSection_primitive r θ 1 3 c.2.2.2.2.1 (q 1) (q 3) h13
  · exact edgeSection_primitive r θ 2 3 c.2.2.2.2.2 (q 2) (q 3) h23

/-- Unconditional first exactness for the actual inverse ideal at theta=1. -/
theorem inverseFirstExact (r : ℂ) (hr : r ≠ 0) : InverseFirstExact r 1 := by
  apply inverseFirstExact_of_sheaf
  have h := CycleQ2ActualCartierFirstExact.inverseIdeal_four_cover_firstExact r hr
  change FirstExact (inverseSheaf r 1)
    (fun i : Fin 4 => PrimeSpectrum.basicOpen (coverElement r 1 i)) at h
  have hpatch : patch r 1 =
      (fun i : Fin 4 => PrimeSpectrum.basicOpen (coverElement r 1 i)) := by
    funext i
    exact coverOpen_singleton r 1 i
  exact (congrArg (FirstExact (inverseSheaf r 1)) hpatch).mpr h

theorem literal_inverseFirstExact : InverseFirstExact 57 1 :=
  inverseFirstExact 57 (by norm_num)

/-- The literal Cartier cocycle is not a boundary in the actual ungraded
four-open scalar complex. -/
theorem literal_cartier_not_boundary :
    ¬ ∃ c : ScalarOne 57 1,
      scalarOneDifferential 57 1 c = cartierBoundaryTwoCochain 57 1
        CycleQ2NormalConnecting.derivativeA 0 :=
  literal_cartierBoundary_not_boundary literal_inverseFirstExact

/-- The same actual class has no boundary even in the homogeneous degree-zero
complex; the proof uses the checked forgetful chain map. -/
theorem literal_homogeneous_cartier_not_boundary :
    ¬ ∃ c : CycleQ2CartierHomogeneousCech.HomogeneousScalarOne 57 1,
      CycleQ2CartierHomogeneousCech.homogeneousOneDifferential 57 1 c =
        CycleQ2CartierHomogeneousCech.literalHomogeneousCartierCochain :=
  CycleQ2CartierHomogeneousCech.literalHomogeneousCartierCochain_not_boundary
    literal_inverseFirstExact

/-- The literal cocycle is not a boundary in the complex formed from the
actual projective structure-sheaf sections and their actual restrictions. -/
theorem literal_projective_cartier_not_boundary :
    ¬ ∃ c : CycleQ2ProjectiveCartierCochain.One 57 1,
      CycleQ2ProjectiveCartierCochain.oneDifferential 57 1 c =
        CycleQ2ProjectiveCartierCochain.literalProjectiveCartierCochain :=
  CycleQ2ProjectiveCartierCochain.literalProjectiveCartierCochain_not_boundary
    literal_inverseFirstExact

end CycleQ2ActualCartierNonboundary
end

end
