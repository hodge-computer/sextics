import Proposal.GeometricSmoothImageDimension
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
A nonempty smooth scheme of relative dimension d over a field has dimension at least d.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2SmoothDimensionLower

open CategoryTheory AlgebraicGeometry Algebra TopologicalSpace

private theorem polynomial_dim_le {k A : Type} [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [FiniteType k A] (n : ℕ) (b : MvPolynomial (Fin n) k →ₐ[k] A)
    (hb : Function.Injective b) : (n : WithBot ℕ∞) ≤ ringKrullDim A := by
  obtain ⟨s,g,hinj,hi⟩ := exists_integral_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin s) k
  let : Algebra P A := g.toRingHom.toAlgebra
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  have : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have : Algebra.IsIntegral P A := ⟨hi⟩
  have hns : n ≤ s := by
    have hn := trdeg_le_of_injective b hb
    have hs := trdeg_add_eq k P (A := A)
    rw [trdeg_eq_zero (R := P) (A := A), add_zero] at hs
    rw [← hs] at hn
    simpa [P] using hn
  have hdim : ringKrullDim P ≤ ringKrullDim A := by
    apply iSup_le
    intro l
    obtain ⟨Q, _, hQ, heq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
      (⊥ : Ideal A) (by simp)
    have : Q.LiesOver l.head.asIdeal := ⟨heq.symm⟩
    obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L
  have hk : ringKrullDim k = 0 := Order.krullDim_eq_zero_of_unique
  have hP : ringKrullDim P = s := by
    simp [P, MvPolynomial.ringKrullDim_of_isNoetherianRing, hk, Nat.card_eq_fintype_card]
  rw [hP] at hdim
  exact (show (n : WithBot ℕ∞) ≤ s by exact_mod_cast hns).trans hdim

theorem le_topologicalKrullDim {k : Type} [Field k] {X : Scheme.{0}} (n : ℕ)
    (f : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension n f] [Nonempty X] :
    (n : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  let x : X := Classical.choice ‹Nonempty X›
  obtain ⟨R,j,hj,_,v,hv,_,p,hp⟩ := CycleQ2SweptSupport.exists_etale_chart n f x
  obtain ⟨a, rfl⟩ := Spec.map_surjective v
  let P := MvPolynomial (Fin n) k
  let : Algebra P R := a.hom.toAlgebra
  have : Algebra.Etale P R :=
    (RingHom.etale_algebraMap).mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hv)
  let : Algebra k R := ((algebraMap P R).comp (algebraMap k P)).toAlgebra
  have : IsScalarTower k P R := .of_algebraMap_eq' rfl
  let : Algebra.FiniteType k R := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k P) (inferInstance : Algebra.FiniteType P R)
  let g : P →ₐ[k] R := IsScalarTower.toAlgHom k P R
  let b := (Ideal.Quotient.mkₐ k p.asIdeal).comp g
  have hi : Function.Injective b := by
    apply (RingHom.injective_iff_ker_eq_bot b.toRingHom).mpr
    apply le_antisymm _ bot_le
    intro z hz
    change Ideal.Quotient.mk p.asIdeal (a.hom z) = 0 at hz
    have hmem : a.hom z ∈ p.asIdeal := Ideal.Quotient.eq_zero_iff_mem.mp hz
    change z ∈ p.asIdeal.comap a.hom at hmem
    have hbot : p.asIdeal.comap a.hom = ⊥ := congrArg PrimeSpectrum.asIdeal hp
    exact hbot ▸ hmem
  calc
    (n : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p.asIdeal) := polynomial_dim_le n b hi
    _ ≤ ringKrullDim R := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
    _ = topologicalKrullDim (Spec R) := (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
    _ ≤ topologicalKrullDim X := j.isOpenEmbedding.isInducing.topologicalKrullDim_le

end CycleQ2SmoothDimensionLower

#print axioms CycleQ2SmoothDimensionLower.le_topologicalKrullDim
