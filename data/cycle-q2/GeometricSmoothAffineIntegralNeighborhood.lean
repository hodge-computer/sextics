import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Localization.LocalizationLocalization

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Integral affine neighborhoods in a smooth scheme over a factorial domain

In a standard étale chart the derivative of the defining equation is a unit.
At a prime, precisely one prime factor of the equation vanishes there, with
multiplicity one. The corresponding local ring embeds in the fraction field
of that factor. A finite denominator argument gives a principal integral
neighborhood inside any chosen affine chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
noncomputable section
namespace CycleQ2SmoothAffineIntegralNeighborhood
open Polynomial Ideal

private theorem prime_factor_at_simple_root {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R[X]] (P : Ideal R[X]) [hp : P.IsPrime] (f : R[X])
    (hf : f ∈ P) (hd : f.derivative ∉ P) :
    ∃ p q, Prime p ∧ p ∈ P ∧ q ∉ P ∧ f = p * q := by
  revert hf hd
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ x hx =>
    intro h _
    exact (hp.ne_top ((P.eq_top_of_isUnit_mem h hx))).elim
  | h₃ a p _ hp' ih =>
    intro h hd
    have hsep : ¬ (p ∈ P ∧ a ∈ P) := by
      rintro ⟨hp, ha⟩
      apply hd
      rw [derivative_mul]
      exact P.add_mem (P.mul_mem_left _ ha) (P.mul_mem_right _ hp)
    rcases hp.mem_or_mem h with hP | hA
    · exact ⟨p, a, hp', hP, fun hA => hsep ⟨hP, hA⟩, rfl⟩
    · have hD : a.derivative ∉ P := by
        intro h'
        apply hd
        rw [derivative_mul]
        exact P.add_mem (P.mul_mem_left _ hA) (P.mul_mem_left _ h')
      obtain ⟨g, q, hg, hgP, hq, rfl⟩ := ih hA hD
      exact ⟨g, p*q, hg, hgP, hp.mul_notMem (fun hP => hsep ⟨hP, hA⟩) hq, by ac_rfl⟩

private theorem germ_domain {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R[X]] (f : R[X]) (p : Ideal (AdjoinRoot f)) [hp : p.IsPrime]
    (hd : AdjoinRoot.mk f f.derivative ∉ p) {L : Type*} [CommRing L] [Algebra (AdjoinRoot f) L]
    [hL : IsLocalization.AtPrime L p] : IsDomain L := by
  let P := p.comap (AdjoinRoot.mk f)
  have : P.IsPrime := inferInstanceAs (p.comap _).IsPrime
  have hf : f ∈ P := by simp [P]
  obtain ⟨g, q, hg, _, hq, hf⟩ := prime_factor_at_simple_root P f hf hd
  have : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hg
  have hle : Ideal.span ({f} : Set R[X]) ≤ Ideal.span {g} :=
    Ideal.span_singleton_le_span_singleton.mpr ⟨q, hf⟩
  let φ : AdjoinRoot f →+* AdjoinRoot g := Ideal.Quotient.factor hle
  have kill (x : AdjoinRoot f) (hx : φ x = 0) : AdjoinRoot.mk f q * x = 0 := by
    obtain ⟨y, rfl⟩ := AdjoinRoot.mk_surjective x
    change AdjoinRoot.mk g y = 0 at hx
    obtain ⟨z, hz⟩ := (AdjoinRoot.mk_eq_zero.mp hx)
    rw [← map_mul, AdjoinRoot.mk_eq_zero]
    exact ⟨z, by rw [hz, hf]; ac_rfl⟩
  let F := FractionRing (AdjoinRoot g)
  let ψ := (algebraMap (AdjoinRoot g) F).comp φ
  have ker (x : AdjoinRoot f) (h : ψ x = 0) : φ x = 0 :=
    (IsFractionRing.injective (AdjoinRoot g) F) (h.trans (map_zero _).symm)
  let χ : L →+* F := IsLocalization.lift (M := p.primeCompl) (g := ψ)
    (fun u => isUnit_iff_ne_zero.mpr (fun he =>
      u.2 ((hp.mem_or_mem_of_mul_eq_zero (kill u (ker u he))).resolve_left hq)))
  have hinj : Function.Injective χ := by
    apply hL.injective_of_map_algebraMap_zero
    intro x hx
    have hx' : ψ x = 0 := (IsLocalization.lift_eq _ _).symm.trans hx
    exact (IsLocalization.map_eq_zero_iff p.primeCompl L x).mpr
      ⟨⟨AdjoinRoot.mk f q, hq⟩, kill x (ker x hx')⟩
  exact hinj.isDomain χ
private theorem standardEtale_germ_domain {R S : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R[X]] [CommRing S] [Algebra R S] [Algebra.IsStandardEtale R S]
    (p : Ideal S) [p.IsPrime] : IsDomain (Localization.AtPrime p) := by
  let P : StandardEtalePresentation R S := Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let B := AdjoinRoot P.f
  let T := Localization.Away (AdjoinRoot.mk P.f P.g)
  let e : S ≃ₐ[R] T := P.equivRing.trans P.P.equivAwayAdjoinRoot
  let q := p.comap e.symm.toRingHom
  have : q.IsPrime := inferInstanceAs (p.comap _).IsPrime
  have ht : P.P.HasMap (algebraMap B T (.root P.f)) := by
    constructor
    · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
    · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
      exact IsLocalization.Away.algebraMap_isUnit ..
  have hu := ht.isUnit_derivative_f
  rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq] at hu
  have := germ_domain P.f (q.comap (algebraMap B T)) (q.notMem_of_isUnit hu)
      (L := Localization.AtPrime q)
  let i := Localization.localRingEquiv q p e.symm.toRingEquiv rfl
  exact i.symm.injective.isDomain i.symm

theorem smooth_germ_domain {R S : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [CommRing S] [Algebra R S] [Algebra.Smooth R S] (p : Ideal S) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) := by
  obtain ⟨f, hf, n, a, _, h⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  let T := Localization.Away f
  let q := p.map (algebraMap S T)
  have dis : Disjoint (Submonoid.powers f : Set S) (p : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) T p inferInstance dis
  have := standardEtale_germ_domain (R := MvPolynomial (Fin n) R) q
  have hq : q.comap (algebraMap S T) = p := IsLocalization.under_map_of_isPrime_disjoint (.powers f) T inferInstance dis
  let i := IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers f) q
  let j := Localization.localRingEquiv p (q.comap (algebraMap S T)) (RingEquiv.refl S) (by change p = Ideal.comap (RingHom.id _) _; rw [Ideal.comap_id, hq])
  exact (j.trans i.toRingEquiv).injective.isDomain (j.trans i.toRingEquiv)


open CategoryTheory AlgebraicGeometry

private theorem finite_kernel_denominator {A B : Type} [CommRing A] [CommRing B]
    [Algebra A B] (P : Submonoid A) [IsLocalization P B] (T : Finset A)
    (h : ∀ a ∈ T, algebraMap A B a = 0) : ∃ d : P, ∀ a ∈ T, (d : A) * a = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a T ha ih =>
    obtain ⟨d,hd⟩ := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    obtain ⟨e,he⟩ := (IsLocalization.map_eq_zero_iff P B a).mp (h a (Finset.mem_insert_self _ _))
    refine ⟨e*d, fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with hba | hb
    · rw [hba]
      change ((e : A) * d) * a = 0
      rw [mul_right_comm, he, zero_mul]
    · change ((e : A) * d) * b = 0
      rw [mul_assoc, hd b hb, mul_zero]

private theorem domain_away {A B : Type} [CommRing A] [CommRing B] [IsNoetherianRing A]
    [IsDomain B] [Algebra A B] (P : Submonoid A) [IsLocalization P B] :
    ∃ s : P, ∀ (C : Type) [CommRing C] [Algebra A C] [IsLocalization.Away (s : A) C], IsDomain C := by
  let I := RingHom.ker (algebraMap A B)
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian I)
  have hgen : Ideal.span (T : Set A) = I := hT
  obtain ⟨s, hs⟩ := finite_kernel_denominator (B := B) P T (fun a ha =>
    show a ∈ I from hgen ▸ Ideal.subset_span ha)
  refine ⟨s, ?_⟩
  intro C _ _ hC
  let f : C →+* B := IsLocalization.Away.lift (s : A) (IsLocalization.map_units B s)
  have hker : I ≤ RingHom.ker (algebraMap A C) := by
    rw [← hgen]
    exact Ideal.span_le.mpr fun a ha =>
      (IsLocalization.map_eq_zero_iff (.powers (s : A)) C a).mpr
        ⟨⟨_, Submonoid.mem_powers _⟩, hs a ha⟩
  have hfinj : Function.Injective f := by
    apply hC.injective_of_map_algebraMap_zero
    intro x hx
    exact hker (show x ∈ I from (IsLocalization.Away.lift_eq _ _ _).symm.trans hx)
  exact hfinj.isDomain f

/-- Every prescribed point of a smooth affine chart over a Noetherian factorial base
has an integral principal neighborhood in that chart. -/
theorem exists_integral_chart {R : Type} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [IsNoetherianRing R] {X : Scheme} (p : X ⟶ Spec (CommRingCat.of R)) [Smooth p]
    (A : X.Opens) (hA : IsAffineOpen A) (x : X) (hx : x ∈ A) :
    ∃ U : X.Opens, U ≤ A ∧ IsAffineOpen U ∧ x ∈ U ∧ IsIntegral U.toScheme := by
  let x' : A := ⟨x, hx⟩
  let q := (hA.primeIdealOf x').asIdeal
  have : q.IsPrime := (hA.primeIdealOf x').isPrime
  have hle : A ≤ p ⁻¹ᵁ ⊤ := by rw [Scheme.Hom.preimage_top]; exact le_top
  let φ := (p.appLE ⊤ A hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let : Algebra R Γ(X, A) := φ.toAlgebra
  have hs : φ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv))
    (p.smooth_appLE (isAffineOpen_top _) hA hle)
  have : Algebra.Smooth R Γ(X, A) := hs
  have : IsNoetherianRing Γ(X, A) := Algebra.FiniteType.isNoetherianRing R Γ(X, A)
  have := smooth_germ_domain (R := R) q
  let : Algebra Γ(X, A) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q := hA.isLocalization_stalk x'
  let e := IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) (X.presheaf.stalk x)
  have : IsDomain (X.presheaf.stalk x) := e.symm.injective.isDomain e.symm
  obtain ⟨d, hd⟩ := domain_away (B := X.presheaf.stalk x) q.primeCompl
  let U := X.basicOpen (d : Γ(X, A))
  have hU := hA.basicOpen (d : Γ(X, A))
  have : IsLocalization.Away (d : Γ(X, A)) Γ(X, U) := hA.isLocalization_basicOpen _
  have : IsDomain Γ(X, U) := hd _
  exact ⟨U, X.basicOpen_le _, hU, (X.mem_basicOpen _ x hx).mpr (IsLocalization.map_units _ d),
    IsIntegral.of_isIso hU.isoSpec.inv⟩

end CycleQ2SmoothAffineIntegralNeighborhood

#print axioms CycleQ2SmoothAffineIntegralNeighborhood.exists_integral_chart
