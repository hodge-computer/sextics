import Proposal.GeometricMonicGenericSupport
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic

/-! Two local equations for a smooth surface closed in a smooth fourfold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2SmoothStalkFrames

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Algebra KaehlerDifferential Module
open CycleQ2SmoothRelativeFrames (sectionCoefficients exists_exact_affine_neighborhood)
open CycleQ2RelativeAffineOverlap (baseChangeFrame baseChangeFrame_apply)

variable {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (x : X)

def coefficient : k →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x (by trivial)).hom.comp (sectionCoefficients p ⊤)

theorem coefficient_from_open (U : X.Opens) (hx : x ∈ U) :
    coefficient p x = (X.presheaf.germ U x hx).hom.comp (sectionCoefficients p U) := by
  rw [coefficient,sectionCoefficients,sectionCoefficients,← CommRingCat.hom_comp,← CommRingCat.hom_comp]
  apply congrArg (fun f : CommRingCat.of k ⟶ X.presheaf.stalk x => f.hom)
  rw [← X.presheaf.germ_res (homOfLE (show U ≤ ⊤ from le_top)) x hx]
  simp only [Category.assoc,Scheme.Hom.appLE_map_assoc]

private theorem topCoefficient {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of k)) :
    sectionCoefficients g ⊤ = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom := by
  have h := g.appLE_eq_app (U := ⊤)
  exact congrArg (fun a : Γ(Spec (CommRingCat.of k),⊤) ⟶ Γ(Y,⊤) =>
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ a).hom) h

theorem coefficient_comp {Y Z : Scheme.{0}} (f : Y ⟶ Z)
    (g : Z ⟶ Spec (CommRingCat.of k)) (y : Y) :
    coefficient (f ≫ g) y = (f.stalkMap y).hom.comp (coefficient g (f y)) := by
  rw [coefficient,coefficient,topCoefficient,topCoefficient]
  let a := (Scheme.ΓSpecIso (CommRingCat.of k)).inv
  change ((a ≫ (f ≫ g).appTop) ≫ Y.presheaf.germ ⊤ y (by trivial)).hom =
    (((a ≫ g.appTop) ≫ Z.presheaf.germ ⊤ (f y) (by trivial)) ≫ f.stalkMap y).hom
  apply congrArg (fun a : CommRingCat.of k ⟶ Y.presheaf.stalk y => a.hom)
  rw [Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  exact congrArg (fun h => a ≫ g.appTop ≫ h)
    (f.germ_stalkMap (⊤ : Z.Opens) y (by trivial)).symm

abbrev coefficientAlg : Algebra k (X.presheaf.stalk x) := (coefficient p x).toAlgebra

private theorem exact_frame_from_open (U : X.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) (n : ℕ) :
    letI : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
    letI := coefficientAlg p x
    ∀ (u : Fin n → Γ(X,U)) (b : Basis (Fin n) Γ(X,U) Ω[Γ(X,U)⁄k]),
      (∀ i, b i = D k Γ(X,U) (u i)) →
      ∃ c : Basis (Fin n) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k],
        ∀ i, c i = D k (X.presheaf.stalk x) (X.presheaf.germ U x hx (u i)) := by
  letI : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
  letI := coefficientAlg p x
  letI : Algebra Γ(X,U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
  letI : IsScalarTower k Γ(X,U) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (coefficient_from_open p x U hx)
  let q := (hU.primeIdealOf ⟨x,hx⟩).asIdeal
  letI : q.IsPrime := (hU.primeIdealOf ⟨x,hx⟩).isPrime
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) q := hU.isLocalization_stalk ⟨x,hx⟩
  letI : FormallyEtale Γ(X,U) (X.presheaf.stalk x) := FormallyEtale.of_isLocalization q.primeCompl
  intro u b hu
  exact ⟨baseChangeFrame b,baseChangeFrame_apply b u hu⟩

/-- An actual smooth stalk has the exact cotangent rank of the scheme morphism. -/
theorem exists_exact_frame (n : ℕ) [SmoothOfRelativeDimension n p] :
    letI := coefficientAlg p x
    ∃ (u : Fin n → X.presheaf.stalk x) (b : Basis (Fin n) (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k]),
      ∀ i, b i = D k (X.presheaf.stalk x) (u i) := by
  obtain ⟨U,hU,hx,u,b,hb⟩ := exists_exact_affine_neighborhood p n x
  obtain ⟨c,hc⟩ := exact_frame_from_open p x U hU hx n u b hb
  exact ⟨(X.presheaf.germ U x hx) ∘ u,c,hc⟩

/-- The same geometric coefficient map makes the smooth stalk formally smooth. -/
theorem formallySmooth_stalk [Smooth p] : (coefficient p x).FormallySmooth := by
  obtain ⟨U,hU,hx,_⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (Opens.mem_top x)
  rw [coefficient_from_open p x U hx]
  have hA := CycleQ2NativeAffineCoefficientLifts.section_smooth p U hU
  letI : Algebra Γ(X,U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
  let q := (hU.primeIdealOf ⟨x,hx⟩).asIdeal
  letI : q.IsPrime := (hU.primeIdealOf ⟨x,hx⟩).isPrime
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) q := hU.isLocalization_stalk ⟨x,hx⟩
  have hloc : (X.presheaf.germ U x hx).hom.FormallySmooth :=
    (RingHom.formallySmooth_algebraMap).mpr (FormallySmooth.of_isLocalization q.primeCompl)
  exact hA.comp hloc

end CycleQ2SmoothStalkFrames

namespace CycleQ2SmoothConormalRank

open Algebra KaehlerDifferential Module
open scoped TensorProduct

variable {k A B : Type} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
  (φ : A →ₐ[k] B) (hφ : Function.Surjective φ)

abbrev presentation : Extension k B := Extension.ofSurjective φ hφ

variable [FormallySmooth k A] [FormallySmooth k B]

/-- The actual conormal sequence splits, with the usual Kähler projection. -/
def splitting : (presentation φ hφ).CotangentSpace ≃ₗ[B]
    ((presentation φ hφ).Cotangent × Ω[B⁄k]) := by
  let P := presentation φ hφ
  letI : FormallySmooth k P.Ring := inferInstanceAs (FormallySmooth k A)
  have h := (P.formallySmooth_iff_split_injection).mp (inferInstance : FormallySmooth k B)
  exact (P.exact_cotangentComplex_toKaehler.splitInjectiveEquiv P.toKaehler_surjective
    ⟨h.choose,h.choose_spec⟩).1

variable [IsLocalRing B] {n m : ℕ}

/-- A basis of the conormal module has exactly the rank difference. -/
def conormalBasis (b : Basis (Fin n) A Ω[A⁄k]) (c : Basis (Fin m) B Ω[B⁄k]) :
    Basis (Fin (n-m)) B (presentation φ hφ).Cotangent := by
  letI : Algebra A B := φ.toAlgebra
  let P := presentation φ hφ
  let N := P.CotangentSpace
  let M := P.Cotangent
  let e := splitting φ hφ
  let b₀ : Basis (Fin n) B N := b.baseChange B
  let f : M →ₗ[B] N := e.symm.toLinearMap.comp (LinearMap.inl B M Ω[B⁄k])
  let g : N →ₗ[B] M := (LinearMap.fst B M Ω[B⁄k]).comp e.toLinearMap
  have he : g.comp f = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change (e (e.symm (x,0))).1 = x
    rw [e.apply_symm_apply]
  letI : Module.Projective B N := Module.Projective.of_basis b₀
  letI : Module.Projective B M := Module.Projective.of_split f g he
  letI : Module.Finite B N := Module.Finite.of_basis b₀
  letI : Module.Finite B M := Module.Finite.of_surjective g (Function.RightInverse.surjective (LinearMap.congr_fun he))
  letI : Module.Free B M := Module.free_of_flat_of_isLocalRing
  letI : Module.Free B Ω[B⁄k] := Module.Free.of_basis c
  letI : Module.Finite B Ω[B⁄k] := Module.Finite.of_basis c
  have hN : Module.finrank B N = n := by simpa using Module.finrank_eq_card_basis b₀
  have hK : Module.finrank B Ω[B⁄k] = m := by simpa using Module.finrank_eq_card_basis c
  have h := e.finrank_eq
  change Module.finrank B N = Module.finrank B (M × Ω[B⁄k]) at h
  rw [Module.finrank_prod,hN,hK] at h
  have hr : Module.finrank B M = n - m := by omega
  exact Module.finBasisOfFinrankEq B M hr

end CycleQ2SmoothConormalRank

namespace CycleQ2LocalConormalGenerators

open Algebra KaehlerDifferential Module
open CycleQ2SmoothConormalRank (presentation conormalBasis)

variable {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- Nakayama on a proper ideal, with its own conormal quotient. -/
theorem map_eq_top_iff (I : Ideal A) (hI : I ≠ ⊤) (M : Submodule A I) :
    M.map I.toCotangent = ⊤ ↔ M = ⊤ := by
  refine ⟨fun H => eq_top_iff.mpr ?_, by rintro rfl; simp [Ideal.toCotangent_range]⟩
  refine (Submodule.map_le_map_iff_of_injective (Submodule.injective_subtype I) _ _).mp ?_
  rw [Submodule.map_top,Submodule.range_subtype]
  have hJacob : I ≤ Ideal.jacobson (⊥ : Ideal A) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hI
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) hJacob
  rw [smul_eq_mul,← pow_two,← Ideal.map_toCotangent_ker,← Submodule.map_sup,
    ← Submodule.comap_map_eq,H,Submodule.comap_top,Submodule.map_top,Submodule.range_subtype]

variable {k B : Type} [CommRing k] [CommRing B] [IsLocalRing B]
  [Algebra k A] [Algebra k B] [FormallySmooth k A] [FormallySmooth k B]
  (φ : A →ₐ[k] B) (hφ : Function.Surjective φ) {n m : ℕ}

include hφ in
/-- The actual kernel of a smooth local surjection is generated by lifts
of a basis of its conormal space. -/
theorem exists_kernel_generators (b : Basis (Fin n) A Ω[A⁄k]) (c : Basis (Fin m) B Ω[B⁄k]) :
    ∃ f : Fin (n-m) → A, Ideal.span (Set.range f) = RingHom.ker φ.toRingHom := by
  let P := presentation φ hφ
  let I := P.ker
  let e : Basis (Fin (n-m)) B P.Cotangent := conormalBasis φ hφ b c
  have hI : I ≠ ⊤ := RingHom.ker_ne_top (algebraMap P.Ring B)
  choose x hx using fun i => Extension.Cotangent.mk_surjective (P := P) (e i)
  let M : Submodule P.Ring I := Submodule.span P.Ring (Set.range x)
  have hM : M.map (Extension.Cotangent.mk (P := P)) = ⊤ := by
    have eq : (Extension.Cotangent.mk (P := P)) ∘ x = e := funext hx
    change (Submodule.span P.Ring (Set.range x)).map (Extension.Cotangent.mk (P := P)) = ⊤
    rw [Submodule.map_span,← Set.range_comp,eq,
      ← Submodule.restrictScalars_span P.Ring B P.algebraMap_surjective,e.span_eq,
      Submodule.restrictScalars_top]
  let v : P.Cotangent ≃ₗ[P.Ring] I.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' := Extension.Cotangent.val_smul' }
  have hV : v.toLinearMap.comp (Extension.Cotangent.mk (P := P)) = I.toCotangent := rfl
  have htop : M.map I.toCotangent = ⊤ := by
    rw [← hV,Submodule.map_comp,hM,Submodule.map_top,
      LinearMap.range_eq_top.mpr v.surjective]
  let : IsLocalRing P.Ring := inferInstanceAs (IsLocalRing A)
  let : IsNoetherianRing P.Ring := inferInstanceAs (IsNoetherianRing A)
  have hm : M = ⊤ := (map_eq_top_iff I hI M).mp htop
  have he := congrArg (Submodule.map I.subtype) hm
  change (Submodule.span P.Ring (Set.range x)).map I.subtype = (⊤ : Submodule P.Ring I).map I.subtype at he
  rw [Submodule.map_span,← Set.range_comp,Submodule.map_top,Submodule.range_subtype] at he
  exact ⟨Subtype.val ∘ x,he⟩

end CycleQ2LocalConormalGenerators

namespace CycleQ2SmoothImmersionStalkEquations

open CategoryTheory AlgebraicGeometry Algebra KaehlerDifferential Module
open CycleQ2SmoothStalkFrames (coefficient coefficientAlg coefficient_comp exists_exact_frame formallySmooth_stalk)
open CycleQ2LocalConormalGenerators (exists_kernel_generators)

variable {k : Type} [Field k] {X Y : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
  (i : X ⟶ Y) (hi : i ≫ q = p) (x : X)

/-- The actual morphism on the two stalks is a map over the original field. -/
def stalkAlgHom :
    letI := coefficientAlg q (i x)
    letI := coefficientAlg p x
    Y.presheaf.stalk (i x) →ₐ[k] X.presheaf.stalk x := by
  letI := coefficientAlg q (i x)
  letI := coefficientAlg p x
  refine { toRingHom := (i.stalkMap x).hom, commutes' := ?_ }
  intro a
  have h := coefficient_comp i q x
  rw [hi] at h
  exact (DFunLike.congr_fun h a).symm

include hi in
/-- Generation is in the actual stalk of the ambient scheme, with the
rank difference taken in the ordinary smooth cotangent spaces. -/
theorem stalk_kernel_generators (n m : ℕ) [SmoothOfRelativeDimension n q] [SmoothOfRelativeDimension m p]
    (hs : Function.Surjective (i.stalkMap x)) :
    ∃ f : Fin (n-m) → Y.presheaf.stalk (i x), Ideal.span (Set.range f) = RingHom.ker (i.stalkMap x).hom := by
  letI : Smooth q := SmoothOfRelativeDimension.smooth n q
  letI : Smooth p := SmoothOfRelativeDimension.smooth m p
  letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  letI := coefficientAlg q (i x)
  letI := coefficientAlg p x
  letI : FormallySmooth k (Y.presheaf.stalk (i x)) := formallySmooth_stalk q (i x)
  letI : FormallySmooth k (X.presheaf.stalk x) := formallySmooth_stalk p x
  obtain ⟨_,b,_⟩ := exists_exact_frame q (i x) n
  obtain ⟨_,c,_⟩ := exists_exact_frame p x m
  exact exists_kernel_generators (stalkAlgHom p q i hi x) hs b c

end CycleQ2SmoothImmersionStalkEquations

namespace CycleQ2ClosedImmersionStalkIdeal

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

variable {X Y : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i]
  (U : Y.Opens) (hU : IsAffineOpen U) (x : X) (hx : i x ∈ U)

private abbrev V := i ⁻¹ᵁ U
private abbrev hV : IsAffineOpen (V i U) := hU.preimage i

private abbrev P := (hU.primeIdealOf ⟨i x,hx⟩).asIdeal
private abbrev Q := ((hV i U hU).primeIdealOf ⟨x,hx⟩).asIdeal
private abbrev a := (i.app U).hom

private theorem comap_eq : (Q i U hU x hx).comap (a i U) = P i U hU x hx := by
  have h := IsAffineOpen.comap_primeIdealOf_appLE (f := i) U hU (V i U) (hV i U hU) le_rfl hx
  have e := i.appLE_eq_app (U := U)
  rw [e] at h
  exact congrArg PrimeSpectrum.asIdeal h

include hU in
/-- The actual affine kernel maps to the actual stalk kernel. -/
theorem map_kernel :
    (RingHom.ker (i.app U).hom).map (Y.presheaf.germ U (i x) hx).hom = RingHom.ker (i.stalkMap x).hom := by
  let R := Γ(Y,U)
  let S := Γ(X,V i U)
  let Rₚ := Y.presheaf.stalk (i x)
  let Sₚ := X.presheaf.stalk x
  let P₀ := P i U hU x hx
  let Q₀ := Q i U hU x hx
  let g : R →+* S := a i U
  letI : P₀.IsPrime := (hU.primeIdealOf ⟨i x,hx⟩).isPrime
  letI : Q₀.IsPrime := ((hV i U hU).primeIdealOf ⟨x,hx⟩).isPrime
  letI : Algebra R Rₚ := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨i x,hx⟩
  letI : Algebra S Sₚ := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x,hx⟩
  letI : IsLocalization.AtPrime Rₚ P₀ := hU.isLocalization_stalk ⟨i x,hx⟩
  letI : IsLocalization.AtPrime Sₚ Q₀ := (hV i U hU).isLocalization_stalk ⟨x,hx⟩
  have e : P₀.primeCompl.map g = Q₀.primeCompl := by
    have he : Q₀.comap g = P₀ := comap_eq i U hU x hx
    have hm : P₀.primeCompl = (Q₀.comap g).primeCompl := by
      ext z
      change z ∉ P₀ ↔ z ∉ Q₀.comap g
      rw [he]
    rw [hm]
    exact Ideal.map_primeCompl_comap_of_surjective g (i.app_surjective U hU) Q₀
  let h : P₀.primeCompl ≤ Q₀.primeCompl.comap g := e.symm ▸ P₀.primeCompl.le_comap_map
  have he : (i.stalkMap x).hom = (IsLocalization.map Sₚ g h : Rₚ →+* Sₚ) := by
    apply IsLocalization.ringHom_ext P₀.primeCompl
    rw [IsLocalization.map_comp]
    apply RingHom.ext
    intro z
    exact i.germ_stalkMap_apply U x hx z
  change (RingHom.ker g).map (algebraMap R Rₚ) = _
  rw [he]
  exact (IsLocalization.ker_map (S := Rₚ) Sₚ g e).symm

end CycleQ2ClosedImmersionStalkIdeal

namespace CycleQ2LocalIdealEquations

open Algebra Ideal

variable {A L : Type} [CommRing A] [CommRing L] [Algebra A L]
  (M : Submonoid A) [IsLocalization M L]

private theorem finite_clear (I J : Ideal A) (hI : I.FG)
    (h : I.map (algebraMap A L) ≤ J.map (algebraMap A L)) :
    ∃ d ∈ M, ∀ x ∈ I, d * x ∈ J := by
  obtain ⟨s,hs⟩ := hI
  have hm (x : s) : ∃ d ∈ M, d * (x : A) ∈ J :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff M L J x).mp
      (h (Ideal.mem_map_of_mem _ (hs ▸ Ideal.subset_span x.property)))
  choose u hu hu' using hm
  let d := ∏ x : s, u x
  have hd : d ∈ M := M.prod_mem (fun x _ => hu x)
  refine ⟨d,hd,?_⟩
  have hc : ∀ y ∈ Ideal.span (s : Set A), d * y ∈ J := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      let a : s := ⟨x,hx⟩
      obtain ⟨b,hb⟩ := Finset.dvd_prod_of_mem (f := fun x : s => u x) (Finset.mem_univ a)
      change d = u a * b at hb
      have hh := J.mul_mem_left b (hu' a)
      change b * (u a * x) ∈ J at hh
      rw [hb, mul_comm (u a) b, mul_assoc]
      exact hh
    | zero => simp
    | add x y hx hy hX hY => rw [mul_add]; exact J.add_mem hX hY
    | smul a x hx hX =>
      rw [smul_eq_mul,← mul_assoc,mul_comm d a,mul_assoc]
      exact J.mul_mem_left a hX
  exact fun y hy => hc y (hs.symm ▸ hy)

include M in
private theorem generators_numerators (I : Ideal A) {n : ℕ} (f : Fin n → L)
    (hf : Ideal.span (Set.range f) = I.map (algebraMap A L)) :
    ∃ a : Fin n → A, (∀ i, a i ∈ I) ∧
      (Ideal.span (Set.range a)).map (algebraMap A L) = I.map (algebraMap A L) := by
  have hm (i : Fin n) : f i ∈ I.map (algebraMap A L) := hf ▸ Ideal.subset_span (Set.mem_range_self i)
  have h (i : Fin n) := (IsLocalization.mem_map_algebraMap_iff M L).mp (hm i)
  choose u he using h
  let a : Fin n → A := fun i => (u i).1
  refine ⟨a,fun i => (u i).1.2,le_antisymm ?_ ?_⟩
  · apply Ideal.map_mono
    rw [Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    exact (u i).1.2
  · rw [← hf,Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    have h' : algebraMap A L (a i) ∈ (Ideal.span (Set.range a)).map (algebraMap A L) :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))
    rw [← he i,mul_comm] at h'
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units L (u i).2)).mp h'

/-- The localization ideal is generated by the original equations on one
principal chart, using only denominators from the given localization set. -/
theorem exists_away_equations (I : Ideal A) (hI : I.FG) {n : ℕ} (f : Fin n → L)
    (hf : Ideal.span (Set.range f) = I.map (algebraMap A L)) :
    ∃ d ∈ M, ∃ a : Fin n → A, (∀ i, a i ∈ I) ∧
      (∀ x ∈ I, d * x ∈ Ideal.span (Set.range a)) := by
  obtain ⟨a,ha,he⟩ := generators_numerators M I f hf
  obtain ⟨d,hd,h⟩ := finite_clear M I (Ideal.span (Set.range a)) hI he.ge
  exact ⟨d,hd,a,ha,h⟩

/-- Any algebra in which the one denominator is a unit has precisely
the designated ideal of equations. -/
theorem map_eq_of_clear {S : Type} [CommRing S] (φ : A →+* S) {d : A} (hd : IsUnit (φ d))
    {I J : Ideal A} (hle : J ≤ I) (h : ∀ x ∈ I, d * x ∈ J) : I.map φ = J.map φ := by
  apply le_antisymm _ (Ideal.map_mono hle)
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have hw := Ideal.mem_map_of_mem φ (h x hx)
  rw [map_mul] at hw
  exact (Ideal.unit_mul_mem_iff_mem _ hd).mp hw

end CycleQ2LocalIdealEquations

namespace CycleQ2ClosedImmersionAffineEquations

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2ClosedImmersionStalkIdeal (map_kernel)
open CycleQ2LocalIdealEquations (exists_away_equations map_eq_of_clear)

variable {X Y : Scheme.{0}} [IsLocallyNoetherian Y] (i : X ⟶ Y) [IsClosedImmersion i]
  (U : Y.affineOpens) (x : X) (hx : i x ∈ U.1)

include hx in

/-- The same ideal is generated by sections on one actual principal subopen. -/
theorem exists_affine_equations {n : ℕ} (f : Fin n → Y.presheaf.stalk (i x))
    (hf : Ideal.span (Set.range f) = RingHom.ker (i.stalkMap x).hom) :
    ∃ d : Γ(Y,U.1), i x ∈ Y.basicOpen d ∧
      ∃ a : Fin n → Γ(Y,(Y.affineBasicOpen d).1),
        Ideal.span (Set.range a) = i.ker.ideal (Y.affineBasicOpen d) := by
  let A := Γ(Y,U.1)
  let L := Y.presheaf.stalk (i x)
  let p := (U.2.primeIdealOf ⟨i x,hx⟩).asIdeal
  letI : p.IsPrime := (U.2.primeIdealOf ⟨i x,hx⟩).isPrime
  letI : Algebra A L := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨i x,hx⟩
  letI : IsLocalization.AtPrime L p := U.2.isLocalization_stalk ⟨i x,hx⟩
  letI : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
  let I : Ideal A := i.ker.ideal U
  have hi : I = RingHom.ker (i.app U.1).hom := i.ker_apply U
  have hloc : Ideal.span (Set.range f) = I.map (algebraMap A L) :=
    hf.trans ((congrArg (fun J : Ideal A => J.map (algebraMap A L)) hi).trans
      (map_kernel i U.1 U.2 x hx)).symm
  obtain ⟨d,hd,g,hg,hrel⟩ := exists_away_equations p.primeCompl I (IsNoetherian.noetherian I) f hloc
  let W := Y.affineBasicOpen d
  let ρ := (Y.presheaf.map (homOfLE (Y.basicOpen_le d)).op).hom
  have hxW : i x ∈ Y.basicOpen d := (Y.mem_basicOpen d (i x) hx).mpr
    (IsLocalization.map_units L (⟨d,hd⟩ : p.primeCompl))
  have hu : IsUnit (ρ d) := Y.toRingedSpace.isUnit_res_basicOpen d
  have hle : Ideal.span (Set.range g) ≤ I := Ideal.span_le.mpr (by rintro _ ⟨j,rfl⟩; exact hg j)
  have he := map_eq_of_clear ρ hu hle hrel
  refine ⟨d,hxW,ρ ∘ g,?_⟩
  rw [← (i.ker).map_ideal_basicOpen U d]
  change Ideal.span (Set.range (ρ ∘ g)) = I.map ρ
  rw [he,Ideal.map_span,← Set.range_comp]

end CycleQ2ClosedImmersionAffineEquations
