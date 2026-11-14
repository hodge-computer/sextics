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
import Proposal.GeometricSheafHZero
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Proposal.GeometricProjectiveCohomologyLinear
import Proposal.GeometricAffineChartSections
import Proposal.GeometricTwistedModule
import Proposal.GeometricSheafLocalIso

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

/-!
# Actual restriction of first sheaf cohomology

Restriction to the over-site of an open induces an injective map from
ambient-site first cohomology on that open. The proof uses the exact
restriction functor, additive Yoneda, and actual injective presentations.
It does not assume affine acyclicity or a comparison of derived groups.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSheafCohomologyRestriction

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
  CycleQ2GeometricConeCech.HZero

section ExactFunctor
universe u u' v v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- Exact restriction detects degree-one extensions when it preserves
all morphisms out of their fixed source. No preservation of injective
objects by the restriction functor is needed. -/
theorem mapExtOne_injective_of_hom_bijective (X : C)
    (hX : ∀ Y : C, Function.Bijective (fun f : X ⟶ Y => G.map f)) (Y : C) :
    Function.Injective (G.mapExtAddHom X Y 1) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  change x.mapExactFunctor G = 0 at hx
  let I : InjectivePresentation Y := Classical.arbitrary _
  let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
  have : Injective S.X₂ := I.injective
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ X hS x
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective z
  have hf : (Ext.mk₀ (G.map f)).comp (hS.map G).extClass rfl = 0 := by
    have hh := congrArg (fun t => t.mapExactFunctor G) hz
    simpa only [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
      Ext.mapExactFunctor_extClass, hx] using hh
  obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ (G.obj X) (hS.map G)
    (Ext.mk₀ (G.map f)) rfl hf
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective t
  change (Ext.mk₀ g).comp (Ext.mk₀ (G.map S.g)) (zero_add 0) =
    Ext.mk₀ (G.map f) at ht
  obtain ⟨g₀, hg₀⟩ := (hX S.X₂).surjective g
  have hgf : g₀ ≫ S.g = f := by
    apply (hX S.X₃).injective
    apply (Ext.mk₀_bijective _ _).injective
    simpa only [Ext.mk₀_comp_mk₀, Functor.map_comp, hg₀] using ht
  rw [← hz, ← hgf, ← Ext.mk₀_comp_mk₀_assoc]
  simp
end ExactFunctor

section Sheaves
variable {C : Type} [Category.{0} C] [Quiver.IsThin C]
  (J : GrothendieckTopology C) (U : C)

local instance overIsThin : Quiver.IsThin (Over U) :=
  fun _ _ => ⟨fun _ _ => Over.OverMorphism.ext (Subsingleton.elim _ _)⟩

abbrev freeAbelianSheaf :=
  (presheafToSheaf J AddCommGrpCat.{0}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

abbrev restrictionFunctor : Sheaf J AddCommGrpCat.{0} ⥤ Sheaf (J.over U) AddCommGrpCat.{0} :=
  J.overPullback AddCommGrpCat U

local instance : (restrictionFunctor J U).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionCocontinuous AddCommGrpCat (J.over U) J).isLeftAdjoint

local instance : (restrictionFunctor J U).IsRightAdjoint :=
  ((Over.forget U).sheafAdjunctionContinuous AddCommGrpCat (J.over U) J).isRightAdjoint

local instance : (restrictionFunctor J U).Additive where

/-- A thin site's representable at U restricts to the representable at
the terminal object of its actual over-site. -/
def overYonedaIso :
    (Over.forget U).op ⋙ yoneda.obj U ≅ yoneda.obj (Over.mk (𝟙 U)) :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun f => Over.homMk f (Subsingleton.elim _ _)
      invFun := fun f => f.left
      left_inv := fun _ => rfl
      right_inv := fun _ => by apply Over.OverMorphism.ext; rfl })
    (fun _ => by ext; rfl)

/-- The preceding comparison on free abelian presheaves. -/
def overFreePresheafIso :
    (Over.forget U).op ⋙ (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      yoneda.obj (Over.mk (𝟙 U)) ⋙ AddCommGrpCat.free :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (overYonedaIso U) AddCommGrpCat.free

/-- The actual restricted free abelian sheaf, using compatibility of
restriction and sheafification for the over-forget functor. -/
def overFreeSheafIso :
    (restrictionFunctor J U).obj (freeAbelianSheaf J U) ≅
      freeAbelianSheaf (J.over U) (Over.mk (𝟙 U)) :=
  (((Over.forget U).pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat (J.over U) J).app (yoneda.obj U ⋙ AddCommGrpCat.free)).symm ≪≫
      (presheafToSheaf (J.over U) AddCommGrpCat).mapIso (overFreePresheafIso U)

/-- Evaluation on the free generator is additive Yoneda after actual
sheafification. -/
def freeSheafSections (F : Sheaf J AddCommGrpCat.{0}) :
    (freeAbelianSheaf J U ⟶ F) ≃+ F.obj.obj (op U) :=
  ((sheafificationAdjunction J AddCommGrpCat).homAddEquiv _ F).trans
    (freeYonedaSections F.obj U)

theorem overFreeSheafIso_inv_unit :
    toSheafify (J.over U) (yoneda.obj (Over.mk (𝟙 U)) ⋙ AddCommGrpCat.free) ≫
        (overFreeSheafIso J U).inv.hom =
      (overFreePresheafIso U).inv ≫
        Functor.whiskerLeft (Over.forget U).op
          (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)) := by
  change toSheafify (J.over U) _ ≫
      (sheafifyMap (J.over U) (overFreePresheafIso U).inv ≫
        (((Over.forget U).pushforwardContinuousSheafificationCompatibility
          AddCommGrpCat (J.over U) J).app _).hom.hom) = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  exact congrArg (fun f => (overFreePresheafIso U).inv ≫ f)
    ((Over.forget U).toSheafify_pullbackSheafificationCompatibility
      AddCommGrpCat (J.over U) J (yoneda.obj U ⋙ AddCommGrpCat.free))

/-- The canonical free generator is preserved by the actual sheaf comparison. -/
theorem overFreeSheafIso_generator :
    (overFreeSheafIso J U).inv.hom.app (op (Over.mk (𝟙 U)))
      ((toSheafify (J.over U)
        (yoneda.obj (Over.mk (𝟙 U)) ⋙ AddCommGrpCat.free)).app
          (op (Over.mk (𝟙 U))) (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U))))) =
      (toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)
        (FreeAbelianGroup.of (𝟙 U)) := by
  have hh := congrArg (fun f => f.app (op (Over.mk (𝟙 U)))
      (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U)))))
    (overFreeSheafIso_inv_unit J U)
  have hraw : (overFreePresheafIso U).inv.app (op (Over.mk (𝟙 U)))
      (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U)))) = FreeAbelianGroup.of (𝟙 U) := by
    change FreeAbelianGroup.map (fun f : Over.mk (𝟙 U) ⟶ Over.mk (𝟙 U) => f.left)
      (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U)))) = _
    exact FreeAbelianGroup.map_of_apply _
  exact hh.trans (congrArg
    ((toSheafify J (yoneda.obj U ⋙ AddCommGrpCat.free)).app (op U)) hraw)

/-- The restriction of a map from the free sheaf evaluates to exactly the
same section on U. -/
theorem freeSheafSections_restriction (F : Sheaf J AddCommGrpCat.{0})
    (f : freeAbelianSheaf J U ⟶ F) :
    freeSheafSections (J.over U) (Over.mk (𝟙 U)) (F.over U)
      ((overFreeSheafIso J U).inv ≫ (restrictionFunctor J U).map f) =
        freeSheafSections J U F f := by
  change f.hom.app (op U)
    ((overFreeSheafIso J U).inv.hom.app (op (Over.mk (𝟙 U)))
      ((toSheafify (J.over U)
        (yoneda.obj (Over.mk (𝟙 U)) ⋙ AddCommGrpCat.free)).app
          (op (Over.mk (𝟙 U))) (FreeAbelianGroup.of (𝟙 (Over.mk (𝟙 U)))))) = _
  rw [overFreeSheafIso_generator]
  rfl

/-- Restriction is fully faithful on all morphisms out of this actual
free abelian sheaf. -/
theorem restriction_hom_bijective (F : Sheaf J AddCommGrpCat.{0}) :
    Function.Bijective (fun f : freeAbelianSheaf J U ⟶ F =>
      (restrictionFunctor J U).map f) := by
  constructor
  · intro f g hfg
    apply (freeSheafSections J U F).injective
    exact (freeSheafSections_restriction J U F f).symm.trans
      ((congrArg (fun k => freeSheafSections (J.over U) (Over.mk (𝟙 U))
        (F.over U) ((overFreeSheafIso J U).inv ≫ k)) hfg).trans
          (freeSheafSections_restriction J U F g))
  · intro g
    obtain ⟨f, hf⟩ := (freeSheafSections J U F).surjective
      (freeSheafSections (J.over U) (Over.mk (𝟙 U)) (F.over U)
        ((overFreeSheafIso J U).inv ≫ g))
    refine ⟨f, ?_⟩
    apply (cancel_epi (overFreeSheafIso J U).inv).mp
    apply (freeSheafSections (J.over U) (Over.mk (𝟙 U)) (F.over U)).injective
    exact (freeSheafSections_restriction J U F f).trans hf

/-- At a terminal object, the free abelian representable presheaf is
literally the constant integer presheaf up to this explicit isomorphism. -/
def terminalFreePresheafIso (T : C) (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  NatIso.ofComponents (fun V => by
    letI : Unique (V.unop ⟶ T) :=
      { default := hT.from V.unop, uniq := fun _ => hT.hom_ext _ _ }
    exact ((FreeAbelianGroup.uniqueEquiv (V.unop ⟶ T)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso)
    (by
      intro V W f
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro g
      simp [Functor.comp_map, AddCommGrpCat.free_map, FreeAbelianGroup.uniqueEquiv])

/-- The actual free sheaf at a terminal object is the constant integer sheaf. -/
def terminalFreeSheafIso (T : C) (hT : IsTerminal T) :
    freeAbelianSheaf J T ≅
      (constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  (presheafToSheaf J AddCommGrpCat).mapIso (terminalFreePresheafIso T hT)

local instance sheafHasExt : HasExt.{1} (Sheaf J AddCommGrpCat.{0}) := HasExt.standard _

/-- The ambient-site cohomology at a terminal object is the ordinary
cohomology of that same additive sheaf, in every degree. -/
def terminalCohomologyEquiv (F : Sheaf J AddCommGrpCat.{0})
    (T : C) (hT : IsTerminal T) (n : ℕ) : F.H' n T ≃+ F.H n :=
  (((extFunctor n).mapIso (terminalFreeSheafIso J T hT).op).app F).addCommGroupIsoToAddEquiv.symm

/-- The restricted free source of H′ is the actual constant integer
sheaf on the over-site. -/
def restrictionSourceIso :
    (restrictionFunctor J U).obj (freeAbelianSheaf J U) ≅
      (constantSheaf (J.over U) AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  overFreeSheafIso J U ≪≫ terminalFreeSheafIso (J.over U) (Over.mk (𝟙 U)) Over.mkIdTerminal

/-- The actual degree-one restriction map, induced by the exact
restriction functor and the constructed source isomorphism. -/
def restrictionHOne (F : Sheaf J AddCommGrpCat.{0}) : F.H' 1 U →+ (F.over U).H 1 :=
  ((((extFunctor 1).mapIso (restrictionSourceIso J U).op).app (F.over U)).addCommGroupIsoToAddEquiv).symm.toAddMonoidHom.comp
      ((restrictionFunctor J U).mapExtAddHom (freeAbelianSheaf J U) F 1)

/-- Vanishing after restriction detects vanishing of the original
ambient-site degree-one class. This applies to the actual opens site. -/
theorem restrictionHOne_injective (F : Sheaf J AddCommGrpCat.{0}) :
    Function.Injective (restrictionHOne J U F) :=
  ((((extFunctor 1).mapIso (restrictionSourceIso J U).op).app (F.over U)).addCommGroupIsoToAddEquiv).symm.injective.comp
      (mapExtOne_injective_of_hom_bijective (restrictionFunctor J U)
        (freeAbelianSheaf J U) (restriction_hom_bijective J U) F)

theorem restrictionHOne_eq_zero_iff (F : Sheaf J AddCommGrpCat.{0}) (x : F.H' 1 U) :
    restrictionHOne J U F x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply restrictionHOne_injective J U F
    simpa only [map_zero] using hx
  · rintro rfl
    exact map_zero _

/-- Actual over-site vanishing implies ambient-site vanishing on the open. -/
theorem ambientHOne_subsingleton (F : Sheaf J AddCommGrpCat.{0})
    [Subsingleton ((F.over U).H 1)] : Subsingleton (F.H' 1 U) :=
  Function.Injective.subsingleton (restrictionHOne_injective J U F)

end Sheaves

section SiteEquivalence
variable {C D : Type} [Category.{0} C] [Category.{0} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
  [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]

/-- The actual equivalence of additive sheaves associated to a site
category equivalence whose two directions are continuous. -/
def continuousSheafEquiv : Sheaf J AddCommGrpCat.{0} ≌ Sheaf K AddCommGrpCat.{0} where
  functor := e.inverse.sheafPushforwardContinuous AddCommGrpCat K J
  inverse := e.functor.sheafPushforwardContinuous AddCommGrpCat J K
  unitIso := NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight e.op.unitIso F.obj))
    (by
      intro F G f
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext V
      exact (f.hom.naturality (e.op.unitIso.hom.app V)).symm)
  counitIso := NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.isoWhiskerRight e.op.counitIso F.obj))
    (by
      intro F G f
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext V
      exact (f.hom.naturality (e.op.counitIso.hom.app V)).symm)
  functor_unitIso_comp F := by
    ext
    simp [← Functor.map_comp, ← op_comp]
    rfl

local instance : (continuousSheafEquiv J K e).functor.Additive where

/-- Constant additive sheaves transport along this actual equivalence.
The construction uses their adjunction with terminal evaluation. -/
def constantSheafEquiv (T : D) (hT : IsTerminal T) :
    constantSheaf J AddCommGrpCat ≅
      constantSheaf K AddCommGrpCat ⋙ (continuousSheafEquiv J K e).inverse :=
  (constantSheafAdj J AddCommGrpCat (hT.isTerminalObj e.inverse T)).leftAdjointUniq
    ((constantSheafAdj K AddCommGrpCat hT).comp
      (continuousSheafEquiv J K e).symm.toAdjunction)

/-- The integer source of actual sheaf cohomology is preserved. -/
def constantSourceIso (T : D) (hT : IsTerminal T) :
    (continuousSheafEquiv J K e).functor.obj
        ((constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{0} ℤ))) ≅
      (constantSheaf K AddCommGrpCat).obj (AddCommGrpCat.of (ULift.{0} ℤ)) :=
  (continuousSheafEquiv J K e).functor.mapIso
    ((constantSheafEquiv J K e T hT).app _) ≪≫
      (continuousSheafEquiv J K e).counitIso.app _

local instance sourceHasExt : HasExt.{1} (Sheaf J AddCommGrpCat.{0}) := HasExt.standard _
local instance targetHasExt : HasExt.{1} (Sheaf K AddCommGrpCat.{0}) := HasExt.standard _

/-- Transport of actual first sheaf cohomology along equivalent sites. -/
def siteEquivalenceHOne (T : D) (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{0}) :
    F.H 1 →+ ((continuousSheafEquiv J K e).functor.obj F).H 1 :=
  ((((extFunctor 1).mapIso (constantSourceIso J K e T hT).op).app
    ((continuousSheafEquiv J K e).functor.obj F)).addCommGroupIsoToAddEquiv).symm.toAddMonoidHom.comp
      ((continuousSheafEquiv J K e).functor.mapExtAddHom _ F 1)

/-- The map is injective; full faithfulness supplies all degree-zero lifts. -/
theorem siteEquivalenceHOne_injective
    (T : D) (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{0}) :
    Function.Injective (siteEquivalenceHOne J K e T hT F) :=
  ((((extFunctor 1).mapIso (constantSourceIso J K e T hT).op).app
    ((continuousSheafEquiv J K e).functor.obj F)).addCommGroupIsoToAddEquiv).symm.injective.comp
      (mapExtOne_injective_of_hom_bijective (continuousSheafEquiv J K e).functor _
        (fun _ => ⟨(continuousSheafEquiv J K e).functor.map_injective,
          (continuousSheafEquiv J K e).functor.map_surjective⟩) F)

/-- First cohomology vanishing transfers through a genuine site equivalence
and an actual isomorphism of the transported sheaves. -/
theorem hOne_subsingleton_of_continuousEquivalence
    (T : D) (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{0})
    (G : Sheaf K AddCommGrpCat.{0})
    (i : F ≅ (e.functor.sheafPushforwardContinuous AddCommGrpCat J K).obj G)
    [Subsingleton (G.H 1)] : Subsingleton (F.H 1) := by
  let j : (continuousSheafEquiv J K e).functor.obj F ≅ G :=
    (continuousSheafEquiv J K e).functor.mapIso i ≪≫
      (continuousSheafEquiv J K e).counitIso.app G
  let : Subsingleton ((Sheaf.functorH K 1).obj G) :=
    inferInstanceAs (Subsingleton (G.H 1))
  exact Function.Injective.subsingleton
    ((((Sheaf.functorH K 1).mapIso j).addCommGroupIsoToAddEquiv).injective.comp
      (siteEquivalenceHOne_injective J K e T hT F))

end SiteEquivalence

section ChartVanishing
variable {C D : Type} [Category.{0} C] [Category.{0} D] [Quiver.IsThin C]
  (J : GrothendieckTopology C) (U : C) (K : GrothendieckTopology D)
  (e : Over U ≌ D)
  [e.functor.IsContinuous (J.over U) K]
  [e.inverse.IsContinuous K (J.over U)]

local instance chartSourceHasExt : HasExt.{1} (Sheaf J AddCommGrpCat.{0}) := HasExt.standard _
local instance chartTargetHasExt : HasExt.{1} (Sheaf K AddCommGrpCat.{0}) := HasExt.standard _
local instance chartOverHasExt : HasExt.{1} (Sheaf (J.over U) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual affine-chart vanishing gives vanishing of the ambient H′ group.
All transports here are constructed from the sites and the given sheaf
isomorphism; no derived restriction comparison is assumed. -/
theorem ambientHOne_subsingleton_of_chart
    (T : D) (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{0})
    (G : Sheaf K AddCommGrpCat.{0})
    (i : F.over U ≅
      (e.functor.sheafPushforwardContinuous AddCommGrpCat (J.over U) K).obj G)
    [Subsingleton (G.H 1)] : Subsingleton (F.H' 1 U) := by
  let : Subsingleton ((F.over U).H 1) :=
    hOne_subsingleton_of_continuousEquivalence (J.over U) K e T hT (F.over U) G i
  exact ambientHOne_subsingleton J U F

end ChartVanishing
end CycleQ2GeometricSheafCohomologyRestriction
end

/-!
# The full first cohomology of the actual projective canonical sheaf

The affine structure-sheaf vanishing theorem is transported through the
actual projective chart isomorphisms and the proved degree-one frames.
The resulting ambient-site vanishing makes the existing Mayer-Vietoris
injection from the concrete Cech quotient surjective.

At the sparse seed this identifies every class of actual H¹(Ω) with its
unique complex normalization coordinate, using the intrinsic complex
scalar action. The coordinate agrees with the already checked finite
degree-nine trace. No identification with a geometric Serre trace or
moving-cycle Abel-Jacobi map is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveHOne

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricAffineChartSections

abbrev additiveForget : CommRingCat.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

def structureAdditiveSheaf (X : Scheme.{0}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} :=
  (sheafCompose _ additiveForget).obj X.sheaf

def overIsoOfPatchIso {X : TopCat.{0}} {F G : X.Sheaf AddCommGrpCat.{0}}
    {U : Opens X} (e : CycleQ2GeometricSheafLocalIso.PatchIso F G U) :
    F.over U ≅ G.over U :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun V => (e.app V.unop.left V.unop.hom.le).toAddCommGrpIso)
    (by
      intro V W f
      ext x
      exact (e.naturality f.unop.left.le V.unop.hom.le x).symm))

def chartStructureOverIso {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A]
    (e : U.toScheme ≅ Spec (CommRingCat.of A)) :
    (structureAdditiveSheaf X).over U ≅
      ((chartOpensEquiv e).functor.sheafPushforwardContinuous AddCommGrpCat
        ((Opens.grothendieckTopology X).over U)
        (Opens.grothendieckTopology (Spec (CommRingCat.of A)))).obj
          (structureAdditiveSheaf (Spec (CommRingCat.of A))) :=
  ObjectProperty.isoMk _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (chartSectionsIso e) additiveForget ≪≫
        Functor.associator _ _ _)

def firstPatchAdditiveIso (r θ : ℂ) :
    CycleQ2GeometricSheafLocalIso.PatchIso (degreeOneSheaf r θ)
      (structureAdditiveSheaf (projectiveCurve r θ)) (firstProjectivePatch r θ) where
  app O hO := Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
  naturality hPO hO s :=
    (Twisted.firstLocalSectionsEquiv_naturality (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) hPO hO s).symm

def secondPatchAdditiveIso (r θ : ℂ) :
    CycleQ2GeometricSheafLocalIso.PatchIso (degreeOneSheaf r θ)
      (structureAdditiveSheaf (projectiveCurve r θ)) (secondProjectivePatch r θ) where
  app O hO := Twisted.secondLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
  naturality hPO hO s :=
    (Twisted.secondLocalSectionsEquiv_naturality (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) hPO hO s).symm

open CycleQ2GeometricAffineCohomology CycleQ2GeometricSheafCohomologyRestriction
  CycleQ2GeometricProjectiveCohomologyLinear CycleQ2GeometricProjectiveCanonicalH1
  CycleQ2GeometricProjectiveNonzero CycleQ2GeometricCechPoleReduction
  CycleQ2GeometricCechTrace CycleQ2GeometricConeCech.HZero CycleQ2SeedTrace

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Affine vanishing is transported through an actual affine chart and
an actual frame of the given sheaf on that chart. -/
theorem affineFrameHOne_subsingleton {X : Scheme.{0}} {U : X.Opens}
    {A : Type} [CommRing A] (e : U.toScheme ≅ Spec (CommRingCat.of A))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (frame : F.over U ≅ (structureAdditiveSheaf X).over U) :
    Subsingleton (F.H' 1 U) := by
  let : Subsingleton ((structureAdditiveSheaf (Spec (CommRingCat.of A))).H 1) :=
    affine_H_one_subsingleton A
  exact ambientHOne_subsingleton_of_chart (Opens.grothendieckTopology X) U
    (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (chartOpensEquiv e)
    ⊤ isTerminalTop F (structureAdditiveSheaf (Spec (CommRingCat.of A)))
    (frame ≪≫ chartStructureOverIso e)

/-- The first denominator open is actually affine and its degree-one
frame has been constructed, so its ambient-site H′¹ is zero. -/
theorem firstPatchHOne_subsingleton (r θ : ℂ) :
    Subsingleton ((degreeOneSheaf r θ).H' 1 (firstProjectivePatch r θ)) :=
  affineFrameHOne_subsingleton (firstProjectiveChart r θ) (degreeOneSheaf r θ)
    (overIsoOfPatchIso (firstPatchAdditiveIso r θ))

theorem secondPatchHOne_subsingleton (r θ : ℂ) :
    Subsingleton ((degreeOneSheaf r θ).H' 1 (secondProjectivePatch r θ)) :=
  affineFrameHOne_subsingleton (secondProjectiveChart r θ) (degreeOneSheaf r θ)
    (overIsoOfPatchIso (secondPatchAdditiveIso r θ))

/-- Surjectivity of the original actual Cech comparison, obtained from
Mayer-Vietoris exactness and the two proved affine vanishing statements. -/
theorem degreeOneToProjectiveH1_surjective (r θ : ℂ) (hr : r ≠ 0) :
    Function.Surjective (degreeOneToProjectiveH1 r θ hr) := by
  let F := degreeOneSheaf r θ
  let S := projectiveMayerVietoris r θ hr
  let : Subsingleton ((F.cohomologyPresheaf 1).obj (op S.X₂)) :=
    firstPatchHOne_subsingleton r θ
  let : Subsingleton ((F.cohomologyPresheaf 1).obj (op S.X₃)) :=
    secondPatchHOne_subsingleton r θ
  intro y
  have hnext : S.toBiprod F 1 y = 0 := by
    rw [S.toBiprod_apply]
    have hp :
        (((F.cohomologyPresheaf 1).map S.f₂₄.op y),
          ((F.cohomologyPresheaf 1).map S.f₃₄.op y)) =
        (0, 0) := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    rw [hp]
    exact map_zero _
  obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).mp
    ((S.sequence_exact F 0 1 rfl).exact 2) y hnext
  have hx' : S.δ F 0 1 rfl x = y := hx
  let a := (overlapDegreeOneSectionsEquiv r θ).symm
    (sectionsEquiv F (overlapProjectivePatch r θ) x)
  refine ⟨QuotientAddGroup.mk a, ?_⟩
  change S.δ F 0 1 rfl
      ((sectionsEquiv F (overlapProjectivePatch r θ)).symm
        (overlapDegreeOneSectionsEquiv r θ a)) = y
  simpa only [a, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply] using hx'

def degreeOneCechHOneEquiv (r θ : ℂ) (hr : r ≠ 0) :
    DegreeOneCech r θ ≃+ ProjectiveSheafH1 r θ :=
  AddEquiv.ofBijective (degreeOneToProjectiveH1 r θ hr)
    ⟨degreeOneToProjectiveH1_injective r θ hr,
      degreeOneToProjectiveH1_surjective r θ hr⟩

theorem normalizedProjectiveClass_surjective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Surjective (normalizedProjectiveClass r hr) := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  exact (degreeOneToProjectiveH1_surjective r 0 hr0).comp
    (normalizedCechClass_bijective r hr).surjective

theorem normalizedCanonicalClass_surjective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Surjective (normalizedCanonicalClass r hr) :=
  (canonicalH1Equiv r hr).surjective.comp (normalizedProjectiveClass_surjective r hr)

/-- Every class in genuine H¹(Ω) has one and only one intrinsic complex
normalization coordinate. -/
def canonicalNormalizationEquiv (r : ℂ) (hr : r ^ 3 = 2) :
    ℂ ≃ₗ[ℂ] DifferentialSheafH1 r 0 :=
  LinearEquiv.ofBijective (normalizedCanonicalLinear r hr)
    ⟨normalizedCanonicalLinear_injective r hr, normalizedCanonicalClass_surjective r hr⟩

/-- A linear coordinate on all genuine H¹(Ω), fixed by the displayed
normalization numerator. Its geometric Serre-trace interpretation is a
separate comparison, not a hypothesis or conclusion of this construction. -/
def canonicalResidueCoordinate (r : ℂ) (hr : r ^ 3 = 2) :
    DifferentialSheafH1 r 0 →ₗ[ℂ] ℂ :=
  (canonicalNormalizationEquiv r hr).symm.toLinearMap

@[simp] theorem canonicalResidueCoordinate_normalized (r : ℂ) (hr : r ^ 3 = 2)
    (z : ℂ) :
    canonicalResidueCoordinate r hr (normalizedCanonicalClass r hr z) = z :=
  (canonicalNormalizationEquiv r hr).symm_apply_apply z

theorem degreeNineCanonicalClass_eq_normalized (r : ℂ) (hr : r ^ 3 = 2)
    (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineCanonicalClass r hr p hp =
      normalizedCanonicalClass r hr (traceLinear r p) := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  exact congrArg (fun z : DegreeOneCech r 0 =>
    canonicalH1Equiv r hr (degreeOneToProjectiveH1 r 0 hr0 z))
      (degreeNineCechClass_eq_normalized r hr p hp)

/-- The actual derived-cohomology coordinate equals the existing exact
finite trace on every homogeneous degree-nine representative. -/
theorem canonicalResidueCoordinate_degreeNine (r : ℂ) (hr : r ^ 3 = 2)
    (p : Poly) (hp : p.IsHomogeneous 9) :
    canonicalResidueCoordinate r hr (degreeNineCanonicalClass r hr p hp) =
      traceLinear r p := by
  rw [degreeNineCanonicalClass_eq_normalized, canonicalResidueCoordinate_normalized]

theorem canonicalResidueCoordinate_eq_zero_iff (r : ℂ) (hr : r ^ 3 = 2)
    (x : DifferentialSheafH1 r 0) :
    canonicalResidueCoordinate r hr x = 0 ↔ x = 0 :=
  (canonicalNormalizationEquiv r hr).symm.map_eq_zero_iff

#print axioms firstPatchHOne_subsingleton
#print axioms secondPatchHOne_subsingleton
#print axioms degreeOneToProjectiveH1_surjective
#print axioms canonicalNormalizationEquiv
#print axioms canonicalResidueCoordinate_degreeNine

end CycleQ2GeometricProjectiveHOne
end

