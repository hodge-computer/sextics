import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Topology.NoetherianSpace

/-!
# The image dimension of a morphism between smooth schemes over a field

Suppose the image is dense. An étale chart of the target meets the generic
point of affine n-space. The finitely many generic points of the Noetherian
source ensure that some source point maps to this generic point. A pointed
standard-smooth affine chart there has residue transcendence degree at most
m, while dominance on the polynomial coordinates forces at least n.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SweptSupport
open Set Algebra TopologicalSpace AlgebraicGeometry CategoryTheory

theorem residueField_trdeg_eq_quotient (K A : Type) [Field K] [CommRing A] [Algebra K A]
    (p : Ideal A) [p.IsPrime] :
    trdeg K p.ResidueField = trdeg K (A ⧸ p) := by
  let : Algebra.IsAlgebraic (A ⧸ p) p.ResidueField := IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  have h := trdeg_add_eq K (A ⧸ p) (A := p.ResidueField)
  simpa only [trdeg_eq_zero (R := A ⧸ p) (A := p.ResidueField), add_zero] using h.symm

theorem polynomial_residueField_trdeg_le (K : Type) [Field K] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) K)) [p.IsPrime] : trdeg K p.ResidueField ≤ n := by
  rw [residueField_trdeg_eq_quotient]
  have h := trdeg_le_of_surjective (Ideal.Quotient.mkₐ K p) Ideal.Quotient.mk_surjective
  simpa using h

private theorem etale_polynomial_residueField (K A : Type) [Field K] [CommRing A] [Algebra K A]
    (n : ℕ) (g : MvPolynomial (Fin n) K →ₐ[K] A) (hg : g.Etale) (p : Ideal A) [p.IsPrime] :
    trdeg K p.ResidueField = trdeg K (p.comap g.toRingHom).ResidueField := by
  let P := MvPolynomial (Fin n) K
  let : Algebra P A := g.toRingHom.toAlgebra
  have : IsScalarTower K P A := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have : Algebra.Etale P A := (RingHom.etale_algebraMap).mp hg
  let q := p.under P
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime p) := Localization.AtPrime.algebraOfLiesOver q p
  let : Localization.AtPrime.IsLiesOverAlgebra q p := inferInstance
  have : Module.Finite q.ResidueField p.ResidueField := inferInstance
  have : IsScalarTower K q.ResidueField p.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    intro k
    rw [IsScalarTower.algebraMap_apply K A p.ResidueField, IsScalarTower.algebraMap_apply K P q.ResidueField,
      IsScalarTower.algebraMap_apply K P A]
    exact (IsScalarTower.algebraMap_apply P A p.ResidueField _).symm.trans
      (IsScalarTower.algebraMap_apply P q.ResidueField p.ResidueField _)
  have h := trdeg_add_eq K q.ResidueField (A := p.ResidueField)
  rw [trdeg_eq_zero (R := q.ResidueField) (A := p.ResidueField), add_zero] at h
  exact h.symm

theorem standardSmooth_residueField_trdeg_le (K A : Type) [Field K] [CommRing A] [Algebra K A]
    (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n K A] (p : Ideal A) [p.IsPrime] :
    trdeg K p.ResidueField ≤ n := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n K A
  rw [etale_polynomial_residueField K A n g hg p]
  exact polynomial_residueField_trdeg_le K n _

/-- A pointed standard-smooth affine neighborhood with its original structure map. -/
theorem exists_standard_affine_chart {K : Type} [Field K] {X : Scheme.{0}}
    (n : ℕ) (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (R : CommRingCat.{0}) (j : Spec R ⟶ X), IsOpenImmersion j ∧
      ∃ (p : Spec R), j p = x ∧ ∃ (φ : K →+* R),
        j ≫ f = Spec.map (CommRingCat.ofHom φ) ∧ φ.IsStandardSmoothOfRelativeDimension n := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  have hUtop : U = ⊤ := by
    apply top_unique
    intro z _
    exact Subsingleton.elim (f x) z ▸ e hx
  subst U
  let R := CommRingCat.of K
  let φ : K →+* Γ(X, V) := (f.appLE ⊤ V e).hom.comp (Scheme.ΓSpecIso R).inv.hom
  have hx' : x ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hx
  obtain ⟨p, hp⟩ := hx'
  refine ⟨Γ(X, V), hV.fromSpec, inferInstance, p, hp, φ, ?_, ?_⟩
  · have he := IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at he
    exact he.symm.trans (Spec.map_comp _ _).symm
  · exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _
      (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv h

abbrev affineSpace (K : Type) [Field K] (n : ℕ) := Spec (CommRingCat.of (MvPolynomial (Fin n) K))

abbrev genericPolynomialPoint (K : Type) [Field K] (n : ℕ) : affineSpace K n :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (MvPolynomial (Fin n) K))

theorem genericPolynomialPoint_spec {K : Type} [Field K] (n : ℕ) :
    IsGenericPoint (genericPolynomialPoint K n) Set.univ := by
  change closure ({⟨⊥, Ideal.isPrime_bot⟩} : Set (PrimeSpectrum (MvPolynomial (Fin n) K))) = _
  rw [PrimeSpectrum.closure_singleton]
  exact PrimeSpectrum.zeroLocus_bot

/-- A smooth pointed scheme over a field meets the polynomial generic point on an étale chart. -/
theorem exists_etale_chart {K : Type} [Field K] {X : Scheme.{0}}
    (n : ℕ) (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension n f] (x : X) :
    ∃ (R : CommRingCat.{0}) (j : Spec R ⟶ X), IsOpenImmersion j ∧ x ∈ Set.range j ∧
      ∃ (g : Spec R ⟶ affineSpace K n), Etale g ∧
        g ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = j ≫ f ∧
        genericPolynomialPoint K n ∈ Set.range g := by
  obtain ⟨R, j, hj, p, hp, φ, hφ, hs⟩ := exists_standard_affine_chart n f x
  obtain ⟨g, hcomp, hg⟩ := hs.exists_etale_mvPolynomial
  let G : Spec R ⟶ affineSpace K n := Spec.map (CommRingCat.ofHom g)
  have hG : Etale G := (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom g)).mpr hg
  refine ⟨R, j, hj, ⟨p, hp⟩, G, hG, ?_, ?_⟩
  · rw [hφ]
    change Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) =
      Spec.map (CommRingCat.ofHom φ)
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hcomp)
  · exact ((genericPolynomialPoint_spec n).mem_open_set_iff G.isOpenMap.isOpen_range).mpr
      ⟨G p, Set.mem_univ _, ⟨p, rfl⟩⟩

theorem hitsGeneric_of_dense {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [T0Space X] [T0Space Y] [QuasiSober X] [NoetherianSpace X] (f : X → Y)
    (hf : Continuous f) (hd : DenseRange f) {η : Y} (hη : IsGenericPoint η univ) :
    ∃ x, f x = η := by
  have hfinite : (genericPoints X).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  have h : Dense (f '' genericPoints X) :=
    hd.dense_image hf (dense_iff_closure_eq.mpr genericPoints.closure)
  have hs : f '' genericPoints X = ⋃ x ∈ genericPoints X, {f x} := by
    ext
    simp [eq_comm]
  have hmem := h η
  rw [hs, hfinite.closure_biUnion] at hmem
  obtain ⟨x, hx⟩ := mem_iUnion.mp hmem
  obtain ⟨_, hηx⟩ := mem_iUnion.mp hx
  have hxy : closure {f x} = univ := by
    apply eq_univ_of_univ_subset
    rw [← hη.def]
    exact (isClosed_closure.closure_subset_iff.mpr (singleton_subset_iff.mpr hηx))
  exact ⟨x, IsGenericPoint.eq (show IsGenericPoint (f x) univ from hxy) hη⟩

theorem denseRange_restrict {X Y : Scheme.{0}} (f : X ⟶ Y)
    (hf : DenseRange f) (U : Y.Opens) : DenseRange (f ∣_ U) := by
  have h (x : (f ⁻¹ᵁ U).toScheme) : U.ι ((f ∣_ U) x) = f ((f ⁻¹ᵁ U).ι x) :=
    congrArg (fun k : (f ⁻¹ᵁ U).toScheme ⟶ Y => k x) (morphismRestrict_ι f U)
  have hr : range (f ∣_ U) = U.ι ⁻¹' range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, (h x).symm⟩
    · rintro ⟨x, hx⟩
      have hx' : f x ∈ U := hx ▸ y.property
      let x' : (f ⁻¹ᵁ U).toScheme := ⟨x, hx'⟩
      exact ⟨x', U.ι.isOpenEmbedding.injective ((h x').trans hx)⟩
  change Dense (range (f ∣_ U))
  rw [hr]
  exact Dense.preimage hf U.ι.isOpenEmbedding.isOpenMap

private theorem polynomial_bound {K : Type} [Field K] {B : Type} [CommRing B]
    (φ : K →+* B) (m n : ℕ) (hs : φ.IsStandardSmoothOfRelativeDimension m)
    (g : MvPolynomial (Fin n) K →+* B) (hc : g.comp MvPolynomial.C = φ)
    (p : PrimeSpectrum B) (hp : p.asIdeal.comap g = ⊥) : n ≤ m := by
  let : Algebra K B := φ.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension m K B := hs
  let a : MvPolynomial (Fin n) K →ₐ[K] B :=
    { g with commutes' := RingHom.congr_fun hc }
  let b : MvPolynomial (Fin n) K →ₐ[K] B ⧸ p.asIdeal := (Ideal.Quotient.mkₐ K p.asIdeal).comp a
  have hi : Function.Injective b := by
    apply (RingHom.injective_iff_ker_eq_bot b.toRingHom).mpr
    apply le_antisymm _ bot_le
    intro z hz
    change Ideal.Quotient.mk p.asIdeal (g z) = 0 at hz
    have hmem : g z ∈ p.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hz
    change z ∈ p.asIdeal.comap g at hmem
    simpa only [hp] using hmem
  have hle : (n : Cardinal) ≤ trdeg K (B ⧸ p.asIdeal) := by
    simpa using trdeg_le_of_injective b hi
  have hu := standardSmooth_residueField_trdeg_le K B m p.asIdeal
  rw [residueField_trdeg_eq_quotient] at hu
  exact_mod_cast hle.trans hu

private theorem source_point_bound {K : Type} [Field K] {X : Scheme.{0}} (m n : ℕ)
    (pX : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension m pX]
    (g : X ⟶ affineSpace K n) (hg : g ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = pX)
    (x : X) (hx : g x = genericPolynomialPoint K n) : n ≤ m := by
  obtain ⟨B, j, _, p, hp, φ, hφ, hstd⟩ := exists_standard_affine_chart m pX x
  obtain ⟨a, ha⟩ := Spec.map_surjective (j ≫ g)
  have hc : a.hom.comp MvPolynomial.C = φ := by
    have hA : CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin n) K) ≫ a =
        CommRingCat.ofHom φ := Spec.map_injective <| calc
      _ = Spec.map a ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) := Spec.map_comp _ _
      _ = Spec.map (CommRingCat.ofHom φ) := by rw [ha, Category.assoc, hg, hφ]
    exact congrArg CommRingCat.Hom.hom hA
  have h : Spec.map a p = genericPolynomialPoint K n := by
    rw [ha]
    change g (j p) = _
    rw [hp, hx]
  exact polynomial_bound φ m n hstd a.hom hc p (congrArg PrimeSpectrum.asIdeal h)

/-- A morphism over the field from a lower-dimensional smooth Noetherian
scheme has proper image closure in every nonempty smooth target of dimension n. -/
theorem closure_range_ne_univ {K : Type} [Field K] {X Y : Scheme.{0}} (m n : ℕ) (hmn : m < n)
    [NoetherianSpace X] (pX : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension m pX]
    (pY : Y ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension n pY] (y : Y)
    (f : X ⟶ Y) (hf : f ≫ pY = pX) : closure (range f) ≠ univ := by
  intro h
  have hd : DenseRange f := dense_iff_closure_eq.mpr h
  obtain ⟨R, j, hj, _, q, hq, hbase, z, hz⟩ := exists_etale_chart n pY y
  let U := j.opensRange
  let V := f ⁻¹ᵁ U
  let g : V.toScheme ⟶ affineSpace K n := (f ∣_ U) ≫ j.isoOpensRange.inv ≫ q
  have hq' : DenseRange q := by
    rw [denseRange_iff_closure_range]
    exact eq_univ_of_univ_subset ((genericPolynomialPoint_spec (K := K) n).def ▸
      closure_mono (singleton_subset_iff.mpr (show genericPolynomialPoint K n ∈ range q from ⟨z, hz⟩)))
  have hgd : DenseRange g := hq'.comp
    (j.isoOpensRange.inv.surjective.denseRange.comp (denseRange_restrict f hd U)
      j.isoOpensRange.inv.continuous) q.continuous
  have : NoetherianSpace V.toScheme := inferInstanceAs (NoetherianSpace (V : Set X))
  obtain ⟨x, hx⟩ := hitsGeneric_of_dense g g.continuous hgd (genericPolynomialPoint_spec (K := K) n)
  have hs : SmoothOfRelativeDimension m (V.ι ≫ pX) :=
    by simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 m V.ι pX
  have hg : g ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C) = V.ι ≫ pX := by
    simp only [g, Category.assoc, hbase, j.isoOpensRange_inv_comp_assoc]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hf]
  exact hmn.not_ge (source_point_bound m n (V.ι ≫ pX) g hg x hx)

end CycleQ2SweptSupport
end
#print axioms CycleQ2SweptSupport.closure_range_ne_univ
