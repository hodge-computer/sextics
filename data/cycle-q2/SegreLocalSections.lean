import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Proposal.SegreCartierEquations

/-! # Local principality, regularity and transition maps for Segre sections -/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/GenericLinearSection.lean -/
section
/-! A linear form in three independent section parameters is regular as
soon as any one coefficient is a unit.  This is an elementary statement
over arbitrary commutative rings; no integral or smooth surface assumption
is needed. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2GenericLinearSection
open MvPolynomial

variable {R : Type*} [CommRing R]

def linearForm (a : Fin 3 → R) : MvPolynomial (Fin 3) R :=
  ∑ j, C (a j)*X j

theorem regular_of_injective_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (a : A) (ha : IsRegular (f a)) :
    IsRegular a := by
  constructor
  · intro x y h
    apply hf
    apply ha.left
    simpa only [map_mul] using congrArg f h
  · intro x y h
    apply hf
    apply ha.right
    simpa only [map_mul] using congrArg f h

theorem univariate_regular (u : Rˣ) (b : R) :
    IsRegular (Polynomial.C (u : R)*Polynomial.X+Polynomial.C b) := by
  have h : Polynomial.C (u : R)*
      (Polynomial.X+Polynomial.C ((↑(u⁻¹) : R)*b))=
        Polynomial.C (u : R)*Polynomial.X+Polynomial.C b := by
    rw [mul_add,←Polynomial.C_mul,←mul_assoc,Units.mul_inv,one_mul]
  rw [←h]
  exact (u.isUnit.map Polynomial.C).isRegular.mul (Polynomial.monic_X_add_C _).isRegular

theorem linearForm_regular_zero (a : Fin 3 → R) (hu : IsUnit (a 0)) :
    IsRegular (linearForm a) := by
  let e := finSuccEquiv R 2
  have hc (r : R) : e (C r)=Polynomial.C (C r) := e.commutes r
  have hf : e (linearForm a)=
      Polynomial.C (C (a 0))*Polynomial.X+
        Polynomial.C (C (a 1)*X 0+C (a 2)*X 1) := by
    simp only [linearForm,Fin.sum_univ_three,map_add,map_mul,hc]
    change Polynomial.C (C (a 0))*finSuccEquiv R 2 (X 0)+
      Polynomial.C (C (a 1))*finSuccEquiv R 2 (X (Fin.succ 0))+
      Polynomial.C (C (a 2))*finSuccEquiv R 2 (X (Fin.succ 1))=_
    rw [finSuccEquiv_X_zero,finSuccEquiv_X_succ,finSuccEquiv_X_succ]
    ring
  apply regular_of_injective_map e.toRingHom e.injective
  change IsRegular (e (linearForm a))
  rw [hf]
  obtain ⟨u,hu⟩ := hu.map (C : R →+* MvPolynomial (Fin 2) R)
  rw [←hu]
  exact univariate_regular u _

theorem linearForm_regular (a : Fin 3 → R) (j : Fin 3) (hu : IsUnit (a j)) :
    IsRegular (linearForm a) := by
  classical
  fin_cases j
  · exact linearForm_regular_zero a hu
  · let e := renameEquiv R (Equiv.swap (0 : Fin 3) 1)
    have he : e (linearForm a)=linearForm ![a 1,a 0,a 2] := by
      simp only [e,linearForm,Fin.sum_univ_three,map_add,map_mul,renameEquiv_apply,
        rename_C,rename_X]
      change C (a 0)*X 1+C (a 1)*X 0+C (a 2)*X 2=
        C (a 1)*X 0+C (a 0)*X 1+C (a 2)*X 2
      ring
    apply regular_of_injective_map e.toRingHom e.injective
    change IsRegular (e (linearForm a))
    rw [he]
    exact linearForm_regular_zero _ hu
  · let e := renameEquiv R (Equiv.swap (0 : Fin 3) 2)
    have he : e (linearForm a)=linearForm ![a 2,a 1,a 0] := by
      simp only [e,linearForm,Fin.sum_univ_three,map_add,map_mul,renameEquiv_apply,
        rename_C,rename_X]
      change C (a 0)*X 2+C (a 1)*X 1+C (a 2)*X 0=
        C (a 2)*X 0+C (a 1)*X 1+C (a 0)*X 2
      ring
    apply regular_of_injective_map e.toRingHom e.injective
    change IsRegular (e (linearForm a))
    rw [he]
    exact linearForm_regular_zero _ hu

end CycleQ2GenericLinearSection

#print axioms CycleQ2GenericLinearSection.linearForm_regular
end
end

/- Component: continuation_3/LinkageIdealPrincipal.lean -/
section
/-!
# Local principality from a regular linkage pairing

If I*J is contained in (p), p is regular, and a selected pairing a*b is
p times a unit, the selected sections generate I and J. The argument
works in arbitrary commutative rings, including reducible seed rings.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace CycleQ2LinkageIdealPrincipal

variable {R : Type*} [CommRing R]

theorem factors_regular (p a b u : R)
    (hp : Function.Injective (fun x : R => p*x)) (hu : IsUnit u)
    (hab : a*b=p*u) :
    Function.Injective (fun x : R => a*x) ∧
      Function.Injective (fun x : R => b*x) := by
  constructor
  · intro x y h
    apply hu.mul_right_injective
    apply hp
    calc
      p*(u*x) = b*(a*x) := by rw [← mul_assoc, ← hab]; ring
      _ = b*(a*y) := congrArg (b*·) h
      _ = p*(u*y) := by linear_combination y * hab
  · intro x y h
    apply hu.mul_right_injective
    apply hp
    calc
      p*(u*x) = a*(b*x) := by rw [← mul_assoc, ← hab]; ring
      _ = a*(b*y) := congrArg (a*·) h
      _ = p*(u*y) := by linear_combination y * hab

theorem ideal_eq_selected (I J : Ideal R) (p a b u : R)
    (hp : Function.Injective (fun x : R => p*x)) (hu : IsUnit u)
    (ha : a∈I) (hb : b∈J) (hab : a*b=p*u)
    (hpair : ∀ x∈I, ∀ y∈J, p ∣ x*y) : I=Ideal.span {a} := by
  rcases hu with ⟨v,rfl⟩
  have hbinj := (factors_regular p a b (v:R) hp v.isUnit hab).2
  apply le_antisymm
  · intro x hx
    obtain ⟨q,hq⟩ := hpair x hx b hb
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(↑(v⁻¹):R)*q, ?_⟩
    apply hbinj
    calc
      b*x = p*q := by simpa only [mul_comm] using hq
      _ = b*(a*((↑(v⁻¹):R)*q)) := by
        calc
          p*q = (p*(v:R))*(↑(v⁻¹):R)*q := by simp [mul_assoc]
          _ = b*(a*((↑(v⁻¹):R)*q)) := by rw [← hab]; ring
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)

/-- Both actual factor ideals become principal on every chart where
one selected product has unit quotient by the linkage element. -/
theorem ideals_principal (I J : Ideal R) (p a b u : R)
    (hp : Function.Injective (fun x : R => p*x)) (hu : IsUnit u)
    (ha : a∈I) (hb : b∈J) (hab : a*b=p*u)
    (hpair : ∀ x∈I, ∀ y∈J, p ∣ x*y) :
    I=Ideal.span {a} ∧ J=Ideal.span {b} := by
  refine ⟨ideal_eq_selected I J p a b u hp hu ha hb hab hpair, ?_⟩
  apply ideal_eq_selected J I p b a u hp hu hb ha (by simpa [mul_comm] using hab)
  intro y hy x hx
  simpa only [mul_comm] using hpair x hx y hy

/-- Regularity survives every localization, without requiring that the
localization map itself be injective. -/
theorem localization_mul_injective (M : Submonoid R) (S : Type*)
    [CommRing S] [Algebra R S] [IsLocalization M S]
    (p : R) (hp : Function.Injective (fun x : R => p*x)) :
    Function.Injective (fun x : S => algebraMap R S p*x) := by
  have hpn : p ∈ nonZeroDivisors R := by
    apply mem_nonZeroDivisors_iff_left.mpr
    intro x hx
    apply hp
    simpa only [mul_zero] using hx
  have hsn : algebraMap R S p ∈ nonZeroDivisors S :=
    IsLocalization.nonZeroDivisors_le_comap M S hpn
  intro x y h
  change algebraMap R S p*x=algebraMap R S p*y at h
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_left.mp hsn)
  rw [mul_sub, h, sub_self]

end CycleQ2LinkageIdealPrincipal

#print axioms CycleQ2LinkageIdealPrincipal.ideals_principal
#print axioms CycleQ2LinkageIdealPrincipal.localization_mul_injective
end
end

/- Component: continuation_3/LocalizationKernel.lean -/
section
/-! # Kernels of the actual localized ring map

This is the fraction calculation for a map of localizations whose target
denominators are exactly the images of the source denominators.
-/

noncomputable section

namespace CycleQ2LocalizationKernel

theorem kernel_map {R S P Q : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring P] [CommSemiring Q]
    {M : Submonoid R} {T : Submonoid P}
    [Algebra R S] [Algebra P Q] [IsLocalization M S] [IsLocalization T Q]
    (g : R →+* P) (hT : Submonoid.map g M = T) :
    RingHom.ker (IsLocalization.map Q g (hT.symm ▸ M.le_comap_map) : S →+* Q) =
      (RingHom.ker g).map (algebraMap R S) := by
  ext x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp [RingHom.mem_ker, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff, ← hT]

theorem kernel_away {R S P Q : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring P] [CommSemiring Q]
    [Algebra R S] [Algebra P Q] (g : R →+* P) (x : R)
    [IsLocalization.Away x S] [IsLocalization.Away (g x) Q] :
    RingHom.ker (IsLocalization.Away.map S Q g x) =
      (RingHom.ker g).map (algebraMap R S) := by
  exact kernel_map g (Submonoid.map_powers g x)

end CycleQ2LocalizationKernel

#print axioms CycleQ2LocalizationKernel.kernel_away
end
end

/- Component: continuation_3/LocalizationRegularFactor.lean -/
section
/-! # Faithfulness when a regular factor is added to an open -/

noncomputable section

namespace CycleQ2LocalizationRegularFactor

theorem pow_mul_injective {R : Type*} [CommMonoid R] (b : R)
    (hb : Function.Injective (fun x : R => b*x)) (n : ℕ) :
    Function.Injective (fun x : R => b^n*x) := by
  induction n with
  | zero =>
    intro x y h
    simpa only [pow_zero,one_mul] using h
  | succ n ih =>
    intro x y h
    apply ih
    apply hb
    simpa only [pow_succ',mul_assoc] using h

/-- Passing from D(a) to D(a*b) is faithful whenever b is regular.
The source denominator a need not be regular. -/
theorem restriction_injective {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (a b : R) [IsLocalization.Away a S] [IsLocalization.Away (a*b) T]
    (hb : Function.Injective (fun x : R => b*x)) (f : S →+* T)
    (hf : ∀ x : R, f (algebraMap R S x)=algebraMap R T x) :
    Function.Injective f := by
  have hz : ∀ z : S, f z=0 → z=0 := by
    intro z hz
    obtain ⟨n,x,hx⟩ := IsLocalization.Away.surj a z
    have ht : algebraMap R T x=0 := by
      have hh := congrArg f hx
      simp only [map_mul,map_pow,hf,hz,zero_mul] at hh
      exact hh.symm
    obtain ⟨m,hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (a*b)) T x).mp ht
    obtain ⟨k,hk⟩ := m.property
    have hax : a^k*x=0 := by
      apply pow_mul_injective b hb k
      have hprod : (a*b)^k*x=b^k*(a^k*x) := by rw [mul_pow]; ring
      simpa only [← hk,hprod,mul_zero] using hm
    have hs : algebraMap R S x=0 :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers a) S x).mpr
        ⟨⟨a^k,⟨k,rfl⟩⟩,hax⟩
    have hu : IsUnit (algebraMap R S a^n) :=
      (IsLocalization.Away.algebraMap_isUnit a).pow n
    apply hu.mul_left_injective
    simpa only [hs,zero_mul] using hx
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub,h,sub_self]

end CycleQ2LocalizationRegularFactor

#print axioms CycleQ2LocalizationRegularFactor.restriction_injective
end
end

/- Component: continuation_3/cylinder_bridge/SegreTransitionDerivative.lean -/
section
/-! # First-order logarithmic variation of the actual Segre transition unit

The overlap unit is the existing matrix-entry transition.  The first-order
functional is the universal Kähler differential evaluated by the genuine
special-fiber derivation on the dual numbers.  Its entry formula is proved
without replacing the transition by an assumed cocycle.  Applying it to a
moving surface requires local trivializations of that deformation; this file
does not supply an Abel--Jacobi comparison.
-/

noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreTransitionDerivative

open CycleQ2SegreCech

variable {R : Type*} [CommRing R]

abbrev Jet (R : Type*) := TrivSqZeroExt R R

attribute [local instance] TrivSqZeroExt.algebraBase

/-- The parameter derivative takes values in the special fiber.  In
particular it is not the invalid derivation ε↦1 with values in R[ε]/ε². -/
def tangentDerivation : Derivation R (Jet R) R where
  toLinearMap := TrivSqZeroExt.sndHom R R
  map_one_eq_zero' := rfl
  leibniz' x y := by
    simp only [TrivSqZeroExt.sndHom_apply, TrivSqZeroExt.snd_mul,
      smul_eq_mul, op_smul_eq_smul]
    rfl

def unitLogTangent (u : (Jet R)ˣ) : R :=
  (tangentDerivation (R := R)).liftKaehlerDifferential (unitDlog R u)

theorem unitLogTangent_eq (u : (Jet R)ˣ) :
    unitLogTangent u = (↑(u⁻¹) : Jet R).fst*(u : Jet R).snd := by
  rw [unitLogTangent, unitDlog_apply]
  rfl

theorem unitLogTangent_mul (u v : (Jet R)ˣ) :
    unitLogTangent (u*v)=unitLogTangent u+unitLogTangent v := by
  simp only [unitLogTangent, unitDlog_mul, map_add]

theorem unitLogTangent_inv (u : (Jet R)ˣ) : unitLogTangent u⁻¹= -unitLogTangent u := by
  simp only [unitLogTangent, unitDlog_inv, map_neg]

theorem unitLogTangent_pow (u : (Jet R)ˣ) (d : ℕ) :
    unitLogTangent (u^d)=d • unitLogTangent u := by
  simp only [unitLogTangent, unitDlog_pow, map_nsmul]

theorem inverse_snd (u : (Jet R)ˣ) :
    (↑(u⁻¹) : Jet R).snd =
      -((↑(u⁻¹) : Jet R).fst^2*(u : Jet R).snd) := by
  have h₀ := congrArg TrivSqZeroExt.fst u.inv_mul
  have h₁ := congrArg TrivSqZeroExt.snd u.mul_inv
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_one] at h₀
  simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one,
    smul_eq_mul, op_smul_eq_smul] at h₁
  linear_combination (↑(u⁻¹) : Jet R).fst*h₁-
    (↑(u⁻¹) : Jet R).snd*h₀

/-- Literal entry formula for the first-order logarithmic transition.
`p` and `q` are the same pivot charts used by the published image-line
construction, and both pivot units belong to the actual square-zero ring. -/
theorem transition_logTangent_entries
    (M : Matrix (Fin 3) (Fin 3) (Jet R)) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q : Chart) (up uq : (Jet R)ˣ)
    (hp : (up : Jet R)=M p.1 p.2) (hq : (uq : Jet R)=M q.1 q.2) :
    unitLogTangent (transition M hM p q up uq hp hq)=
      (↑((transition M hM p q up uq hp hq)⁻¹) : Jet R).fst*
        ((M q.1 p.2).snd*(↑(up⁻¹) : Jet R).fst-
          (M q.1 p.2).fst*(↑(up⁻¹) : Jet R).fst^2*(M p.1 p.2).snd) := by
  rw [unitLogTangent_eq]
  change _*(M q.1 p.2*(↑(up⁻¹) : Jet R)).snd = _
  rw [TrivSqZeroExt.snd_mul, inverse_snd up, hp]
  simp only [smul_eq_mul, op_smul_eq_smul]
  ring

theorem transition_logTangent_cocycle
    (M : Matrix (Fin 3) (Fin 3) (Jet R)) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q s : Chart) (up uq us : (Jet R)ˣ)
    (hp : (up : Jet R)=M p.1 p.2) (hq : (uq : Jet R)=M q.1 q.2)
    (hs : (us : Jet R)=M s.1 s.2) :
    unitLogTangent (transition M hM p q up uq hp hq)+
      unitLogTangent (transition M hM q s uq us hq hs)=
        unitLogTangent (transition M hM p s up us hp hs) := by
  rw [← unitLogTangent_mul, transition_cocycle]

/-- The homogeneous O(d) correction survives at first order as well. -/
theorem twistedTransition_logTangent
    (M : Matrix (Fin 3) (Fin 3) (Jet R)) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q : Chart) (up uq : (Jet R)ˣ)
    (hp : (up : Jet R)=M p.1 p.2) (hq : (uq : Jet R)=M q.1 q.2)
    (xp xq : (Jet R)ˣ) (d : ℕ) :
    unitLogTangent (twistedTransition M hM p q up uq hp hq xp xq d)=
      d • (unitLogTangent xp-unitLogTangent xq)+
        unitLogTangent (transition M hM p q up uq hp hq) := by
  simp only [twistedTransition, unitLogTangent_mul, unitLogTangent_pow,
    unitLogTangent_inv, sub_eq_add_neg]

end CycleQ2SegreTransitionDerivative

#print axioms CycleQ2SegreTransitionDerivative.tangentDerivation
#print axioms CycleQ2SegreTransitionDerivative.transition_logTangent_entries
#print axioms CycleQ2SegreTransitionDerivative.twistedTransition_logTangent
end
end

/- Component: continuation_3/UnitFiberRegular.lean -/
section
/-!
# A unit in one fiber detects a nonzerodivisor in a finite free algebra

The base is an integral domain. No domain hypothesis is imposed on the
finite free algebra. The proof uses the determinant of multiplication and
its checked compatibility with scalar extension.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UnitFiberRegular

open scoped TensorProduct

variable {R A S : Type*} [CommRing R] [IsDomain R]
  [CommRing A] [Nontrivial A] [Algebra R A]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]

theorem multiplication_baseChange (p : S) :
    (Algebra.lmul R S p).baseChange A =
      Algebra.lmul A (A ⊗[R] S) (Algebra.TensorProduct.includeRight p) := by
  ext a s
  simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]

/-- A single fiber on which p is a unit proves that multiplication by p
is injective on the original finite free algebra. -/
theorem injective_mul_of_unit_fiber (p : S)
    (hp : IsUnit (Algebra.TensorProduct.includeRight p : A ⊗[R] S)) :
    Function.Injective (fun x : S => p*x) := by
  have hu : IsUnit ((Algebra.lmul R S p).baseChange A) := by
    rw [multiplication_baseChange]
    exact Algebra.lmul_isUnit_iff.mpr hp
  have hd := LinearMap.isUnit_det _ hu
  rw [LinearMap.det_baseChange] at hd
  have hn : (Algebra.lmul R S p).det ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hd
    exact not_isUnit_zero hd
  have hk : LinearMap.ker (Algebra.lmul R S p) = ⊥ := by
    by_contra h
    exact hn (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  exact LinearMap.ker_eq_bot.mp hk

end CycleQ2UnitFiberRegular

#print axioms CycleQ2UnitFiberRegular.multiplication_baseChange
#print axioms CycleQ2UnitFiberRegular.injective_mul_of_unit_fiber
end
end

/- Component: continuation_3/cylinder_bridge/SegreGenericSection.lean -/
section
/-! The three literal components of M·T define one common homogeneous
ideal.  On every unit-pivot chart this actual ideal is generated by a
regular linear form, and the local generators are related by the already
proved matrix transition units.  The section parameters are independent
polynomial variables, so regularity needs no domain assumption. -/

noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreGenericSection
open MvPolynomial Matrix CycleQ2SegreCech CycleQ2GenericLinearSection

variable {R : Type*} [CommRing R]

def sectionVector (M : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) :
    MvPolynomial (Fin 3) R := linearForm (M i)

def sectionIdeal (M : Matrix (Fin 3) (Fin 3) R) : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span (Set.range (sectionVector M))

def localEquation (M : Matrix (Fin 3) (Fin 3) R) (p : Chart) : MvPolynomial (Fin 3) R :=
  sectionVector M p.1

/-- When the matrix entries have the same homogeneous degree, division
by the pivot gives the degree-zero local equation on its projective chart. -/
def normalizedEquation (M : Matrix (Fin 3) (Fin 3) R) (p : Chart) (u : Rˣ) :
    MvPolynomial (Fin 3) R := C (↑(u⁻¹) : R)*localEquation M p

theorem section_factorization
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p : Chart) (u : Rˣ) (hu : (u : R)=M p.1 p.2) (i : Fin 3) :
    sectionVector M i=C (column M p u i)*localEquation M p := by
  simp only [sectionVector,localEquation,linearForm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [CycleQ2SegreLocal.unit_pivot_factorization M hM p.1 p.2 u hu i j,
    map_mul,mul_assoc]
  rfl

theorem sectionIdeal_principal
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p : Chart) (u : Rˣ) (hu : (u : R)=M p.1 p.2) :
    sectionIdeal M=Ideal.span {localEquation M p} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rw [section_factorization M hM p u hu i]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact Ideal.subset_span (Set.mem_range_self p.1)

theorem localEquation_regular (M : Matrix (Fin 3) (Fin 3) R) (p : Chart)
    (hu : IsUnit (M p.1 p.2)) : IsRegular (localEquation M p) :=
  linearForm_regular (M p.1) p.2 hu

theorem normalizedEquation_regular (M : Matrix (Fin 3) (Fin 3) R) (p : Chart)
    (u : Rˣ) (hu : (u : R)=M p.1 p.2) : IsRegular (normalizedEquation M p u) := by
  exact ((u⁻¹).isUnit.map C).isRegular.mul
    (localEquation_regular M p (hu ▸ u.isUnit))

/-- Both principal generators come from the same literal section ideal;
the displayed unit is the original image-line transition, mapped into the
section-parameter polynomial ring. -/
theorem localEquation_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R)=M p.1 p.2) (hq : (uq : R)=M q.1 q.2) :
    localEquation M q=C (transition M hM p q up uq hp hq : R)*localEquation M p := by
  simp only [localEquation,sectionVector,linearForm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [row_overlap M hM p q up uq hp hq j,map_mul,mul_assoc]

theorem normalizedEquation_overlap
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R)=M p.1 p.2) (hq : (uq : R)=M q.1 q.2) :
    normalizedEquation M q uq=
      C ((up*uq⁻¹*transition M hM p q up uq hp hq : Rˣ) : R)*
        normalizedEquation M p up := by
  rw [normalizedEquation,normalizedEquation,localEquation_overlap M hM p q up uq hp hq]
  simp only [Units.val_mul,map_mul]
  have hunit : C (up : R)*C (↑(up⁻¹) : R)=(1 : MvPolynomial (Fin 3) R) := by
    rw [←map_mul,Units.mul_inv,map_one]
  linear_combination
    -(C (↑(uq⁻¹) : R)*C (transition M hM p q up uq hp hq : R)*localEquation M p)*hunit

theorem sectionVector_map {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) :
    MvPolynomial.map f (sectionVector M i)=sectionVector (f.mapMatrix M) i := by
  simp only [sectionVector,linearForm,map_sum,map_mul,map_C,map_X]
  rfl

theorem normalizedEquation_transition_cocycle
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R)=M p.1 p.2) (hq : (uq : R)=M q.1 q.2)
    (hr : (ur : R)=M r.1 r.2) :
    (up*uq⁻¹*transition M hM p q up uq hp hq)*
      (uq*ur⁻¹*transition M hM q r uq ur hq hr)=
        up*ur⁻¹*transition M hM p r up ur hp hr := by
  simpa only [twistedTransition,pow_one] using
    twistedTransition_cocycle M hM p q r up uq ur hp hq hr up uq ur 1

end CycleQ2SegreGenericSection

#print axioms CycleQ2SegreGenericSection.sectionIdeal_principal
#print axioms CycleQ2SegreGenericSection.localEquation_regular
#print axioms CycleQ2SegreGenericSection.localEquation_overlap
#print axioms CycleQ2SegreGenericSection.normalizedEquation_overlap
#print axioms CycleQ2SegreGenericSection.normalizedEquation_transition_cocycle
end
end
