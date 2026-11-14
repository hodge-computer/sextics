import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Derived first cohomology of the affine structure sheaf

The sections used here are the actual structure-sheaf sections on principal
opens of `Spec A`. Finite denominator clearing is performed in the affine
ring itself, retaining the actual restriction maps. A finite partition of
unity then makes every principal-open cocycle a coboundary.

For an arbitrary short exact sequence of additive sheaves beginning with
the structure sheaf, these coboundaries correct local lifts into a global
lift. Applying this fact to an injective presentation proves vanishing of
the actual derived group `Sheaf.H` in degree one. No module structure on
the other terms of the short exact sequence is assumed.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricAffineCohomology

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open scoped BigOperators

variable {A : Type} [CommRing A]

abbrev Sections (f : A) :=
  (Spec.structureSheaf A).obj.obj (op (PrimeSpectrum.basicOpen f))

def restrict {f g : A} (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) :
    Sections f →+* Sections g :=
  ((Spec.structureSheaf A).obj.map (homOfLE h).op).hom

@[simp] theorem restrict_algebraMap {f g : A}
    (h : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f) (a : A) :
    restrict h (algebraMap A (Sections f) a) = algebraMap A (Sections g) a := rfl

@[simp] theorem restrict_comp {f g h : A}
    (hgf : PrimeSpectrum.basicOpen g ≤ PrimeSpectrum.basicOpen f)
    (hhg : PrimeSpectrum.basicOpen h ≤ PrimeSpectrum.basicOpen g) (s : Sections f) :
    restrict hhg (restrict hgf s) = restrict (hhg.trans hgf) s := rfl

/-- A finite family of actual affine sections has one common denominator
exponent; no reducedness or regularity assumption is needed. -/
theorem uniform_denominators {ι : Type} [Fintype ι]
    (f : ι → A) (s : ∀ i, Sections (f i)) :
    ∃ (N : ℕ) (a : ι → A), ∀ i,
      s i * algebraMap A (Sections (f i)) (f i ^ N) =
        algebraMap A (Sections (f i)) (a i) := by
  classical
  choose n a ha using fun i => IsLocalization.Away.surj (f i) (s i)
  let N := Finset.univ.sup n
  have hn (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N, fun i => f i ^ (N - n i) * a i, fun i => ?_⟩
  rw [map_mul, map_pow, ← ha i, map_pow]
  conv_lhs => rw [← Nat.sub_add_cancel (hn i), pow_add]
  ring

private theorem triple_le_left (x y z : A) :
    PrimeSpectrum.basicOpen ((x * y) * z) ≤ PrimeSpectrum.basicOpen (x * y) :=
  PrimeSpectrum.basicOpen_mul_le_left _ _

private theorem triple_le_right (x y z : A) :
    PrimeSpectrum.basicOpen ((x * y) * z) ≤ PrimeSpectrum.basicOpen (y * z) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf_right _ inf_le_right

private theorem triple_le_outer (x y z : A) :
    PrimeSpectrum.basicOpen ((x * y) * z) ≤ PrimeSpectrum.basicOpen (x * z) := by
  simp only [PrimeSpectrum.basicOpen_mul]
  exact inf_le_inf_right _ inf_le_left

/-- The additive cocycle equation on actual triple intersections. -/
def IsCocycle {ι : Type} (f : ι → A)
    (c : ∀ i j, Sections (f i * f j)) : Prop :=
  ∀ i j k,
    restrict (triple_le_left (f i) (f j) (f k)) (c i j) +
      restrict (triple_le_right (f i) (f j) (f k)) (c j k) =
    restrict (triple_le_outer (f i) (f j) (f k)) (c i k)

/-- A finite actual cocycle can be represented by affine-ring numerators
whose cocycle equations hold in the ring itself. The second denominator
clearing removes localization torsion, so this also applies to nonreduced rings. -/
theorem cleared_cocycle {ι : Type} [Fintype ι] (f : ι → A)
    (c : ∀ i j, Sections (f i * f j)) (hc : IsCocycle f c) :
    ∃ (N : ℕ) (a : ι → ι → A),
      (∀ i j, c i j * algebraMap A (Sections (f i * f j)) ((f i * f j) ^ N) =
        algebraMap A (Sections (f i * f j)) (a i j)) ∧
      (∀ i j k, a i j * f k ^ N + a j k * f i ^ N = a i k * f j ^ N) := by
  classical
  obtain ⟨N, a, ha⟩ := uniform_denominators
    (fun p : ι × ι => f p.1 * f p.2) (fun p => c p.1 p.2)
  have hloc (i j k : ι) :
      algebraMap A (Sections ((f i * f j) * f k))
        (a (i, j) * f k ^ N + a (j, k) * f i ^ N) =
      algebraMap A (Sections ((f i * f j) * f k)) (a (i, k) * f j ^ N) := by
    have hij := congrArg (restrict (triple_le_left (f i) (f j) (f k))) (ha (i, j))
    have hjk := congrArg (restrict (triple_le_right (f i) (f j) (f k))) (ha (j, k))
    have hik := congrArg (restrict (triple_le_outer (f i) (f j) (f k))) (ha (i, k))
    simp only [map_mul, restrict_algebraMap] at hij hjk hik
    rw [map_add, map_mul, map_mul, map_mul, ← hij, ← hjk, ← hik]
    let ri := restrict (triple_le_left (f i) (f j) (f k)) (c i j)
    let rj := restrict (triple_le_right (f i) (f j) (f k)) (c j k)
    let rk := restrict (triple_le_outer (f i) (f j) (f k)) (c i k)
    let xi := algebraMap A (Sections ((f i * f j) * f k)) (f i)
    let xj := algebraMap A (Sections ((f i * f j) * f k)) (f j)
    let xk := algebraMap A (Sections ((f i * f j) * f k)) (f k)
    have hc' : ri + rj = rk := hc i j k
    calc
      _ = (ri + rj) * (xi ^ N * xj ^ N * xk ^ N) := by
        dsimp only [ri, rj, xi, xj, xk]
        simp only [map_pow, map_mul, mul_pow]
        ring
      _ = rk * (xi ^ N * xj ^ N * xk ^ N) := by rw [hc']
      _ = _ := by
        dsimp only [rk, xi, xj, xk]
        simp only [map_pow, map_mul, mul_pow]
        ring
  choose m hm using fun i j k =>
    IsLocalization.Away.exists_of_eq ((f i * f j) * f k) (hloc i j k)
  let M := Finset.univ.sup (fun p : ι × ι × ι => m p.1 p.2.1 p.2.2)
  have hM (i j k : ι) : m i j k ≤ M :=
    Finset.le_sup (f := fun p : ι × ι × ι => m p.1 p.2.1 p.2.2)
      (Finset.mem_univ (i, j, k))
  have heq (i j k : ι) :
      ((f i * f j) * f k) ^ M * (a (i, j) * f k ^ N + a (j, k) * f i ^ N) =
      ((f i * f j) * f k) ^ M * (a (i, k) * f j ^ N) := by
    calc
      _ = ((f i * f j) * f k) ^ (M - m i j k) *
          (((f i * f j) * f k) ^ m i j k *
            (a (i, j) * f k ^ N + a (j, k) * f i ^ N)) := by
        rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hM i j k)]
      _ = ((f i * f j) * f k) ^ (M - m i j k) *
          (((f i * f j) * f k) ^ m i j k * (a (i, k) * f j ^ N)) := by rw [hm]
      _ = _ := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hM i j k)]
  refine ⟨M + N, fun i j => (f i * f j) ^ M * a (i, j), ?_, ?_⟩
  · intro i j
    rw [map_mul, ← ha (i, j), pow_add, map_mul]
    ring
  · intro i j k
    calc
      _ = ((f i * f j) * f k) ^ M *
          (a (i, j) * f k ^ N + a (j, k) * f i ^ N) := by
        simp only [pow_add, mul_pow]
        ring
      _ = ((f i * f j) * f k) ^ M * (a (i, k) * f j ^ N) := heq i j k
      _ = _ := by
        simp only [pow_add, mul_pow]
        ring

/-- A finite principal cover admits a partition of one after any common power. -/
theorem finite_power_partition {ι : Type} [Fintype ι] (f : ι → A)
    (hf : Ideal.span (Set.range f) = ⊤) (n : ℕ) :
    ∃ w : ι → A, ∑ i, w i * f i ^ n = 1 := by
  have hpow : Ideal.span (Set.range (fun i => f i ^ n)) = ⊤ := by
    rw [Set.range_comp' (fun x : A => x ^ n) f]
    exact Ideal.span_pow_eq_top (Set.range f) hf n
  exact (Ideal.mem_span_range_iff_exists_fun).mp
    ((Ideal.eq_top_iff_one _).mp hpow)

/-- The finite algebraic contraction after denominators have been cleared. -/
theorem finite_power_cocycle_exact {ι : Type} [Fintype ι] (f : ι → A)
    (hf : Ideal.span (Set.range f) = ⊤) (n : ℕ) (a : ι → ι → A)
    (hcocycle : ∀ i j k,
      a i j * f k ^ n + a j k * f i ^ n = a i k * f j ^ n) :
    ∃ b : ι → A, ∀ i j,
      b i * f j ^ n - b j * f i ^ n = a i j := by
  classical
  obtain ⟨w, hw⟩ := finite_power_partition f hf n
  refine ⟨fun i => ∑ k, w k * a i k, ?_⟩
  intro i j
  simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
  calc
    ∑ k, (w k * a i k * f j ^ n - w k * a j k * f i ^ n) =
        ∑ k, w k * (a i j * f k ^ n) := by
      apply Finset.sum_congr rfl
      intro k _
      have hk : a i k * f j ^ n - a j k * f i ^ n = a i j * f k ^ n :=
        (sub_eq_iff_eq_add).mpr (hcocycle i j k).symm
      calc
        w k * a i k * f j ^ n - w k * a j k * f i ^ n =
            w k * (a i k * f j ^ n - a j k * f i ^ n) := by ring
        _ = w k * (a i j * f k ^ n) := congrArg (fun t => w k * t) hk
    _ = a i j * (∑ k, w k * f k ^ n) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = a i j := by rw [hw, mul_one]

/-- Every actual structure-sheaf one-cocycle on a finite principal cover
of an affine spectrum is a coboundary. -/
theorem finite_cocycle_exact {ι : Type} [Fintype ι] (f : ι → A)
    (hf : Ideal.span (Set.range f) = ⊤)
    (c : ∀ i j, Sections (f i * f j)) (hc : IsCocycle f c) :
    ∃ b : ∀ i, Sections (f i), ∀ i j,
      restrict (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (b i) -
        restrict (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (b j) = c i j := by
  obtain ⟨N, a, ha, hc'⟩ := cleared_cocycle f c hc
  obtain ⟨b, hb⟩ := finite_power_cocycle_exact f hf N a hc'
  let s (i : ι) : Sections (f i) :=
    IsLocalization.mk' (Sections (f i)) (b i) (Submonoid.pow (f i) N)
  have hs (i : ι) : s i * algebraMap A (Sections (f i)) (f i ^ N) =
      algebraMap A (Sections (f i)) (b i) :=
    IsLocalization.mk'_spec (Sections (f i)) (b i) (Submonoid.pow (f i) N)
  refine ⟨s, fun i j => ?_⟩
  have hi := congrArg (restrict (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j))) (hs i)
  have hj := congrArg (restrict (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j))) (hs j)
  simp only [map_mul, restrict_algebraMap] at hi hj
  have hu : IsUnit (algebraMap A (Sections (f i * f j)) ((f i * f j) ^ N)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (f i * f j)).pow N
  apply hu.mul_left_inj.mp
  calc
    _ = (restrict (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (s i) *
          algebraMap A (Sections (f i * f j)) (f i ^ N)) *
          algebraMap A (Sections (f i * f j)) (f j ^ N) -
        (restrict (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (s j) *
          algebraMap A (Sections (f i * f j)) (f j ^ N)) *
          algebraMap A (Sections (f i * f j)) (f i ^ N) := by
      rw [mul_pow, map_mul]
      ring
    _ = algebraMap A (Sections (f i * f j))
        (b i * f j ^ N - b j * f i ^ N) := by rw [hi, hj, map_sub, map_mul, map_mul]
    _ = algebraMap A (Sections (f i * f j)) (a i j) := by rw [hb]
    _ = _ := (ha i j).symm

abbrev AbSheaf (A : Type) [CommRing A] :=
  Sheaf (Opens.grothendieckTopology (PrimeSpectrum.Top A)) AddCommGrpCat.{0}

/-- The actual additive sheaf underlying the affine structure sheaf. -/
def additiveStructureSheaf (A : Type) [CommRing A] : AbSheaf A :=
  (sheafCompose _ (forget₂ CommRingCat RingCat ⋙
    forget₂ RingCat AddCommGrpCat)).obj (Spec.structureSheaf A)

/-- Local liftability on an affine spectrum supplies lifts on a finite
principal cover. Finiteness follows algebraically from the unit ideal. -/
theorem finite_local_lifts {F G : AbSheaf A} (g : F ⟶ G)
    [Sheaf.IsLocallySurjective g] (q : G.obj.obj (op ⊤)) :
    ∃ (s : Finset A) (u : ∀ i : s, F.obj.obj (op (PrimeSpectrum.basicOpen (i : A)))),
      Ideal.span (s : Set A) = ⊤ ∧
      ∀ i : s, g.hom.app _ (u i) = G.obj.map (homOfLE
        (show PrimeSpectrum.basicOpen (i : A) ≤ ⊤ from le_top)).op q := by
  classical
  let T : Set A := {a | ∃ u : F.obj.obj (op (PrimeSpectrum.basicOpen a)),
    g.hom.app _ u = G.obj.map (homOfLE
      (show PrimeSpectrum.basicOpen a ≤ ⊤ from le_top)).op q}
  have hT : Ideal.span T = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    apply top_unique
    intro x hx
    obtain ⟨V, i, ⟨v, hv⟩, hxV⟩ :=
      Presheaf.imageSieve_mem (Opens.grothendieckTopology (PrimeSpectrum.Top A)) g.hom q x hx
    obtain ⟨_, ⟨a, rfl⟩, hxa, haV⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxV V.isOpen
    have ha : a ∈ T := by
      refine ⟨F.obj.map (homOfLE haV).op v, ?_⟩
      erw [NatTrans.naturality_apply, hv, ← G.obj.map_comp_apply, ← op_comp]
      rfl
    exact Opens.mem_iSup.mpr ⟨a, Opens.mem_iSup.mpr ⟨ha, hxa⟩⟩
  obtain ⟨s, hsT, hs⟩ := Submodule.mem_span_finite_of_mem_span
    ((Ideal.eq_top_iff_one _).mp hT)
  have hu (i : s) := hsT i.property
  choose u hu using hu
  exact ⟨s, u, (Ideal.eq_top_iff_one _).mpr hs, hu⟩

/-- Exactness of additive sheaves with an injective first arrow remains
exact on sections at the middle term. -/
private theorem section_preimage (S : CategoryTheory.ShortComplex (AbSheaf A))
    (hS : S.ShortExact) (U : Opens (PrimeSpectrum.Top A))
    (x : S.X₂.obj.obj (op U)) (hx : S.g.hom.app _ x = 0) :
    ∃ y : S.X₁.obj.obj (op U), S.f.hom.app _ y = x := by
  let E := sheafToPresheaf (Opens.grothendieckTopology (PrimeSpectrum.Top A)) AddCommGrpCat ⋙
    (evaluation _ AddCommGrpCat).obj (op U)
  have he := hS.exact.map_of_mono_of_preservesKernel E hS.mono_f (by infer_instance)
  exact (CategoryTheory.ShortComplex.ab_exact_iff (S.map E)).mp he x hx

private def res (F : AbSheaf A) {U V : Opens (PrimeSpectrum.Top A)} (h : V ≤ U) :
    F.obj.obj (op U) →+ F.obj.obj (op V) :=
  (F.obj.map (homOfLE h).op).hom

@[simp] private theorem res_comp (F : AbSheaf A)
    {U V W : Opens (PrimeSpectrum.Top A)} (hVU : V ≤ U) (hWV : W ≤ V)
    (x : F.obj.obj (op U)) : res F hWV (res F hVU x) = res F (hWV.trans hVU) x := by
  change (F.obj.map (homOfLE hVU).op ≫ F.obj.map (homOfLE hWV).op) x = _
  rw [← F.obj.map_comp]
  rfl

@[simp] private theorem hom_res {F G : AbSheaf A} (g : F ⟶ G)
    {U V : Opens (PrimeSpectrum.Top A)} (h : V ≤ U) (x : F.obj.obj (op U)) :
    g.hom.app (op V) (res F h x) = res G h (g.hom.app (op U) x) :=
  NatTrans.naturality_apply g.hom (homOfLE h).op x

private theorem section_injective (S : CategoryTheory.ShortComplex (AbSheaf A))
    (hS : S.ShortExact) (U : Opens (PrimeSpectrum.Top A)) :
    Function.Injective (S.f.hom.app (op U)) := by
  let E := sheafToPresheaf (Opens.grothendieckTopology (PrimeSpectrum.Top A)) AddCommGrpCat ⋙
    (evaluation _ AddCommGrpCat).obj (op U)
  have := hS.mono_f
  have h : Mono (E.map S.f) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective (E.map S.f)).mp h

/-- An epimorphism of additive sheaves with kernel the actual affine
structure sheaf is surjective on global sections. -/
theorem global_lift {I Q : AbSheaf A} (α : additiveStructureSheaf A ⟶ I)
    (β : I ⟶ Q) (hαβ : α ≫ β = 0)
    (hS : (CategoryTheory.ShortComplex.mk α β hαβ).ShortExact)
    [Sheaf.IsLocallySurjective β] : Function.Surjective (β.hom.app (op ⊤)) := by
  classical
  intro q
  let S := CategoryTheory.ShortComplex.mk α β hαβ
  obtain ⟨s, u, hs, hu⟩ := finite_local_lifts β q
  let f (i : s) : A := i
  have hf : Ideal.span (Set.range f) = ⊤ := by
    have hfr : Set.range f = (s : Set A) := by
      ext a
      constructor
      · rintro ⟨i, rfl⟩
        exact i.property
      · intro ha
        exact ⟨⟨a, ha⟩, rfl⟩
    rwa [hfr]
  have hcover : (⨆ i : s, PrimeSpectrum.basicOpen (f i)) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hf
  have hex (i j : s) : ∃ c : Sections (f i * f j), α.hom.app _ c =
      res I (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (u i) -
        res I (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (u j) := by
    apply section_preimage S hS
    change β.hom.app _
      (res I (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (u i) -
        res I (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (u j)) = 0
    rw [map_sub, hom_res, hom_res, hu, hu]
    change res Q _ (res Q _ q) - res Q _ (res Q _ q) = 0
    simp only [res_comp, sub_self]
  choose c hc using hex
  have hcin : IsCocycle f c := by
    intro i j k
    apply section_injective S hS (PrimeSpectrum.basicOpen ((f i * f j) * f k))
    change α.hom.app _
      (res (additiveStructureSheaf A) (triple_le_left (f i) (f j) (f k)) (c i j) +
        res (additiveStructureSheaf A) (triple_le_right (f i) (f j) (f k)) (c j k)) =
      α.hom.app _
        (res (additiveStructureSheaf A) (triple_le_outer (f i) (f j) (f k)) (c i k))
    simp only [map_add, hom_res, hc, map_sub, res_comp]
    abel
  obtain ⟨b, hb⟩ := finite_cocycle_exact f hf c hcin
  have hb' (i j : s) :
      res (additiveStructureSheaf A) (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (b i) -
        res (additiveStructureSheaf A) (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (b j) =
      c i j := hb i j
  let v (i : s) := u i - α.hom.app _ (b i)
  have hβzero (U : Opens (PrimeSpectrum.Top A))
      (t : (additiveStructureSheaf A).obj.obj (op U)) :
      β.hom.app _ (α.hom.app _ t) = 0 := by
    exact congrArg (fun γ : additiveStructureSheaf A ⟶ Q => γ.hom.app (op U) t) hαβ
  have hvβ (i : s) : β.hom.app _ (v i) = res Q (show PrimeSpectrum.basicOpen (f i) ≤ ⊤ from le_top) q := by
    dsimp only [v]
    rw [map_sub, hβzero, sub_zero]
    exact hu i
  have hvpair (i j : s) :
      res I (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (v i) =
        res I (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (v j) := by
    apply sub_eq_zero.mp
    change res I _ (u i - α.hom.app _ (b i)) - res I _ (u j - α.hom.app _ (b j)) = 0
    simp only [map_sub]
    erw [← hom_res α (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (b i),
      ← hom_res α (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (b j)]
    calc
      _ = (res I (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (u i) -
            res I (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (u j)) -
          α.hom.app _
            (res (additiveStructureSheaf A) (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (b i) -
              res (additiveStructureSheaf A) (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (b j)) := by
        rw [map_sub]
        abel
      _ = α.hom.app _ (c i j) - α.hom.app _ (c i j) := by rw [← hc, hb']
      _ = 0 := sub_self _
  have hcompatible (i j : s) :
      I.obj.map (Opens.infLELeft (PrimeSpectrum.basicOpen (f i)) (PrimeSpectrum.basicOpen (f j))).op (v i) =
        I.obj.map (Opens.infLERight (PrimeSpectrum.basicOpen (f i)) (PrimeSpectrum.basicOpen (f j))).op (v j) := by
    let e := (eqToHom (PrimeSpectrum.basicOpen_mul (f i) (f j))).op
    have hinj : Function.Injective (I.obj.map e) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback _
    apply hinj
    rw [← I.obj.map_comp_apply, ← I.obj.map_comp_apply]
    exact hvpair i j
  obtain ⟨v₀, hv₀, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (show TopCat.Sheaf AddCommGrpCat (PrimeSpectrum.Top A) from I)
    (fun i : s => PrimeSpectrum.basicOpen (f i)) ⊤ (fun _ => homOfLE le_top)
    (by rw [hcover]) v hcompatible
  refine ⟨v₀, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq'
    (show TopCat.Sheaf AddCommGrpCat (PrimeSpectrum.Top A) from Q)
    (fun i : s => PrimeSpectrum.basicOpen (f i)) ⊤ (fun _ => homOfLE le_top)
    (by rw [hcover])
  intro i
  change res Q _ (β.hom.app _ v₀) = res Q _ q
  rw [← hom_res]
  have hh : res I (show PrimeSpectrum.basicOpen (f i) ≤ ⊤ from le_top) v₀ = v i := hv₀ i
  rw [hh]
  exact hvβ i

open CategoryTheory.Limits CategoryTheory.Abelian

local instance affineHasExt (A : Type) [CommRing A] : HasExt.{1} (AbSheaf A) :=
  HasExt.standard _

/-- Genuine derived first cohomology of the additive structure sheaf
vanishes on every affine spectrum. -/
theorem affine_H_one_eq_zero (A : Type) [CommRing A]
    (x : (additiveStructureSheaf A).H 1) : x = 0 := by
  let F := additiveStructureSheaf A
  let α := Injective.ι F
  let S := CategoryTheory.ShortComplex.mk α (cokernel.π α) (cokernel.condition α)
  have hS : S.ShortExact := { exact := CategoryTheory.ShortComplex.exact_cokernel α }
  have : Sheaf.IsLocallySurjective S.g :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.g).mpr hS.epi_g
  have hsurj := global_lift α S.g S.zero hS
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
    ((constantSheaf (Opens.grothendieckTopology (PrimeSpectrum.Top A)) AddCommGrpCat).obj
      (AddCommGrpCat.of (ULift ℤ))) hS x (Ext.eq_zero_of_injective _) rfl
  let eI := Sheaf.H.equiv₀ S.X₂ (T := ⊤) isTerminalTop
  let eQ := Sheaf.H.equiv₀ S.X₃ (T := ⊤) isTerminalTop
  obtain ⟨u, hu⟩ := hsurj (eQ y)
  let z : S.X₂.H 0 := eI.symm u
  have hz : Sheaf.H.map S.g 0 z = y := by
    apply eQ.injective
    rw [← Sheaf.H.equiv₀_naturality]
    change S.g.hom.app _ (eI (eI.symm u)) = eQ y
    rw [eI.apply_symm_apply]
    exact hu
  rw [← hy, ← hz]
  simp only [Sheaf.H.map_apply, Ext.comp_assoc_of_second_deg_zero,
    CategoryTheory.ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

theorem affine_H_one_subsingleton (A : Type) [CommRing A] :
    Subsingleton ((additiveStructureSheaf A).H 1) :=
  subsingleton_of_forall_eq 0 (affine_H_one_eq_zero A)

end CycleQ2GeometricAffineCohomology
end
