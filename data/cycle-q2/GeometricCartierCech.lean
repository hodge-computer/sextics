import Proposal.GeometricCartierNormalLift
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.Group.Commute.Units

/-!
# Actual Cartier Cech classes and principal-cover comparison

The four-open Cartier cocycle is placed in its actual degree-two cochain
quotient. Affine exactness and unique gluing are proved from localization
and an explicit unit-open contraction. The change-of-cover theorem uses
actual tensor-localized common refinements and their canonical maps.
These constructions preserve the original surface equations and cochains.
The nonvanishing application and the final geometric existence theorem
are separate obligations.
-/

set_option Elab.async false

noncomputable section
open scoped BigOperators TensorProduct

/-! The actual four-open Cartier cocycle as a class of the genuine
localization Čech complex. The generic complex also applies to modules. -/
namespace CycleQ2GeometricFourOpenCech

variable (R : Type*) [CommRing R]
variable (V : Finset (Fin 4) → Type*)
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]

structure RestrictionSystem where
  res {s t : Finset (Fin 4)} : s ⊆ t → V s →ₗ[R] V t
  res_id (s : Finset (Fin 4)) : res (s := s) (t := s) (by rfl) = LinearMap.id
  res_comp {s t u : Finset (Fin 4)} (hst : s ⊆ t) (htu : t ⊆ u) :
    (res htu).comp (res hst) = res (hst.trans htu)

variable {R V}

@[simp] theorem RestrictionSystem.res_res (D : RestrictionSystem R V)
    {s t u : Finset (Fin 4)} (hst : s ⊆ t) (htu : t ⊆ u) (v : V s) :
    D.res htu (D.res hst v) = D.res (hst.trans htu) v :=
  LinearMap.congr_fun (D.res_comp hst htu) v

abbrev ZeroCochain (V : Finset (Fin 4) → Type*) :=
  (V {0} × V {1}) × (V {2} × V {3})

abbrev OneCochain (V : Finset (Fin 4) → Type*) :=
  (V {0,1} × V {0,2} × V {0,3}) × (V {1,2} × V {1,3} × V {2,3})

abbrev TwoCochain (V : Finset (Fin 4) → Type*) :=
  (V {0,1,2} × V {0,1,3}) × (V {0,2,3} × V {1,2,3})

abbrev ThreeCochain (V : Finset (Fin 4) → Type*) := V Finset.univ

def d0 (D : RestrictionSystem R V) : ZeroCochain V →ₗ[R] OneCochain V where
  toFun q :=
    ((D.res (by decide) q.1.2 - D.res (by decide) q.1.1,
      D.res (by decide) q.2.1 - D.res (by decide) q.1.1,
      D.res (by decide) q.2.2 - D.res (by decide) q.1.1),
     (D.res (by decide) q.2.1 - D.res (by decide) q.1.2,
      D.res (by decide) q.2.2 - D.res (by decide) q.1.2,
      D.res (by decide) q.2.2 - D.res (by decide) q.2.1))
  map_add' p q := by ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> abel
  map_smul' c q := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, RingHom.id_apply]

def d1 (D : RestrictionSystem R V) : OneCochain V →ₗ[R] TwoCochain V where
  toFun p :=
    ((D.res (by decide) p.2.1 - D.res (by decide) p.1.2.1 + D.res (by decide) p.1.1,
      D.res (by decide) p.2.2.1 - D.res (by decide) p.1.2.2 + D.res (by decide) p.1.1),
     (D.res (by decide) p.2.2.2 - D.res (by decide) p.1.2.2 + D.res (by decide) p.1.2.1,
      D.res (by decide) p.2.2.2 - D.res (by decide) p.2.2.1 + D.res (by decide) p.2.1))
  map_add' p q := by ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> abel
  map_smul' c q := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, smul_add,
      RingHom.id_apply]

def d2 (D : RestrictionSystem R V) : TwoCochain V →ₗ[R] ThreeCochain V where
  toFun p := D.res (by decide) p.2.2 - D.res (by decide) p.2.1 +
    D.res (by decide) p.1.2 - D.res (by decide) p.1.1
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
  map_smul' c q := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, smul_add,
      RingHom.id_apply]

@[simp] theorem d1_d0 (D : RestrictionSystem R V) (q : ZeroCochain V) :
    d1 D (d0 D q) = 0 := by
  ext <;> dsimp [d0, d1] <;> simp only [map_sub, RestrictionSystem.res_res] <;> abel

@[simp] theorem d2_d1 (D : RestrictionSystem R V) (q : OneCochain V) :
    d2 D (d1 D q) = 0 := by
  dsimp [d1, d2]
  simp only [map_add, map_sub, RestrictionSystem.res_res]
  abel

abbrev TwoCocycles (D : RestrictionSystem R V) := LinearMap.ker (d2 D)

def boundaryMap (D : RestrictionSystem R V) : OneCochain V →ₗ[R] TwoCocycles D :=
  (d1 D).codRestrict (TwoCocycles D) (fun p => d2_d1 D p)

abbrev SecondCech (D : RestrictionSystem R V) :=
  TwoCocycles D ⧸ LinearMap.range (boundaryMap D)

def classOf (D : RestrictionSystem R V) : TwoCocycles D →ₗ[R] SecondCech D :=
  (LinearMap.range (boundaryMap D)).mkQ

theorem classOf_eq_zero_iff (D : RestrictionSystem R V) (c : TwoCocycles D) :
    classOf D c = 0 ↔ ∃ p : OneCochain V, d1 D p = c.val := by
  change (Submodule.Quotient.mk c : SecondCech D) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p, congrArg Subtype.val hp⟩
  · rintro ⟨p,hp⟩
    exact ⟨p, Subtype.ext hp⟩

/-- The degree-one obstruction step of the connecting-map argument.
All maps are maps of the stated cochains. Actual applications must supply
and prove the middle complex's exactness and the commutative squares. -/
theorem connecting_zero_forces_boundary
    {A0 A1 A2 B0 B1 B2 C0 C1 : Type*}
    [AddCommGroup A0] [AddCommGroup A1] [AddCommGroup A2]
    [AddCommGroup B0] [AddCommGroup B1] [AddCommGroup B2]
    [AddCommGroup C0] [AddCommGroup C1]
    [Module R A0] [Module R A1] [Module R A2]
    [Module R B0] [Module R B1] [Module R B2]
    [Module R C0] [Module R C1]
    (dA : A1 →ₗ[R] A2) (dB0 : B0 →ₗ[R] B1) (dB1 : B1 →ₗ[R] B2)
    (dC : C0 →ₗ[R] C1) (i1 : A1 →ₗ[R] B1) (i2 : A2 →ₗ[R] B2)
    (p0 : B0 →ₗ[R] C0) (p1 : B1 →ₗ[R] C1)
    (hi : ∀ a, dB1 (i1 a) = i2 (dA a))
    (hp : ∀ b, p1 (dB0 b) = dC (p0 b))
    (hpi : ∀ a, p1 (i1 a) = 0)
    (hexact : ∀ b, dB1 b = 0 → ∃ a, dB0 a = b)
    (c : C1) (b : B1) (a : A2)
    (hlift : p1 b = c) (hboundary : dB1 b = i2 a)
    (hzero : ∃ q, dA q = a) : ∃ q, dC q = c := by
  obtain ⟨q,hq⟩ := hzero
  have hz : dB1 (b - i1 q) = 0 := by
    rw [map_sub, hboundary, hi, hq, sub_self]
  obtain ⟨v,hv⟩ := hexact (b - i1 q) hz
  refine ⟨p0 v, ?_⟩
  rw [← hp, hv, map_sub, hpi, sub_zero, hlift]

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricCartierCech

open CycleQ2GeometricSeedNormalIdeals CycleQ2ConormalJacobian
  CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricFourOpenCech

abbrev P := MvPolynomial (Fin 5) ℂ

/-- The diagram of actual four-open surface localization rings. -/
def surfaceSystem (r θ : ℂ) :
    RestrictionSystem (SurfaceRing r θ) (CoverLocal r θ) where
  res h := (coverRestriction r θ h).toLinearMap
  res_id s := by
    have hh : coverRestriction r θ (s := s) (t := s) (by rfl) = AlgHom.id _ _ := by
      apply IsLocalization.algHom_ext (Submonoid.powers (coverProduct r θ s))
      ext a
    exact congrArg AlgHom.toLinearMap hh
  res_comp hst htu := by
    ext a
    exact coverRestriction_comp_apply r θ hst htu a

abbrev ActualSecondCech (r θ : ℂ) := SecondCech (surfaceSystem r θ)

/-- The actual inverse-ideal lift's previously proved cocycle, placed in
its actual cochain kernel, with the same two nonzero faces and signs. -/
def cartierCycle (r θ : ℂ) (A L : P) : TwoCocycles (surfaceSystem r θ) :=
  ⟨((boundary012 r θ A L, boundary013 r θ A L), (0,0)), by
    change surfaceCechTwoDifferential r θ (cartierBoundaryTwoCochain r θ A L) = 0
    exact cartierBoundaryTwoCochain_cocycle r θ A L⟩

def cartierClass (r θ : ℂ) (A L : P) : ActualSecondCech r θ :=
  classOf (surfaceSystem r θ) (cartierCycle r θ A L)

/-- Vanishing refers to an actual scalar Čech coboundary, not to a chosen
trace or an auxiliary finite-dimensional model. -/
theorem cartierClass_eq_zero_iff (r θ : ℂ) (A L : P) :
    cartierClass r θ A L = 0 ↔
      ∃ p : OneCochain (CoverLocal r θ),
        d1 (surfaceSystem r θ) p =
          ((boundary012 r θ A L, boundary013 r θ A L), (0,0)) :=
  classOf_eq_zero_iff (surfaceSystem r θ) (cartierCycle r θ A L)

end CycleQ2GeometricCartierCech

namespace CycleQ2GeometricLocalizedCech

variable {R : Type*} [CommRing R]
variable {M N M' N' : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
variable [Module R M] [Module R N] [Module R M'] [Module R N']

/-- A finite product of actual module localizations is the localization
of the actual product. This supplies the cochain localization comparison. -/
theorem isLocalizedModule_prod (S : Submonoid R)
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    [IsLocalizedModule S f] [IsLocalizedModule S g] :
    IsLocalizedModule S (f.prodMap g) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hf := (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)
    have hg := (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units g s)
    constructor
    · intro a b hab
      apply Prod.ext
      · apply hf.1
        exact congrArg Prod.fst hab
      · apply hg.1
        exact congrArg Prod.snd hab
    · intro a
      obtain ⟨b,hb⟩ := hf.2 a.1
      obtain ⟨c,hc⟩ := hg.2 a.2
      exact ⟨(b,c), Prod.ext hb hc⟩
  surj a := by
    obtain ⟨⟨b,u⟩,hu⟩ := IsLocalizedModule.surj S f a.1
    obtain ⟨⟨c,v⟩,hv⟩ := IsLocalizedModule.surj S g a.2
    change u.val • a.1 = f b at hu
    change v.val • a.2 = g c at hv
    refine ⟨((v.val • b, u.val • c), u * v), ?_⟩
    apply Prod.ext
    · change (u.val * v.val) • a.1 = f (v.val • b)
      rw [map_smul, mul_smul, smul_comm, hu]
    · change (u.val * v.val) • a.2 = g (u.val • c)
      rw [map_smul, mul_smul, hv]
  exists_of_eq {a b} h := by
    obtain ⟨u,hu⟩ := (IsLocalizedModule.eq_iff_exists S f).mp (congrArg Prod.fst h)
    obtain ⟨v,hv⟩ := (IsLocalizedModule.eq_iff_exists S g).mp (congrArg Prod.snd h)
    change u.val • a.1 = u.val • b.1 at hu
    change v.val • a.2 = v.val • b.2 at hv
    refine ⟨u*v, ?_⟩
    apply Prod.ext
    · change (u.val * v.val) • a.1 = (u.val * v.val) • b.1
      simpa only [mul_smul, smul_comm u.val v.val] using congrArg (v.val • ·) hu
    · change (u.val * v.val) • a.2 = (u.val * v.val) • b.2
      simpa only [mul_smul] using congrArg (u.val • ·) hv

/-- The local exactness criterion applied to an actual quotient class.
This form is useful for finite distinguished-open Čech contractions. -/
theorem exact_of_unit_span
    {L : Type*} [AddCommGroup L] [Module R L]
    {ι : Type*} (a : ι → R) (ha : Ideal.span (Set.range a) = ⊤)
    (d0 : M →ₗ[R] N) (d1 : N →ₗ[R] L)
    (h : ∀ i, Function.Exact
      (LocalizedModule.map (Submonoid.powers (a i)) d0)
      (LocalizedModule.map (Submonoid.powers (a i)) d1)) :
    Function.Exact d0 d1 := by
  apply exact_of_localized_span (Set.range a) ha d0 d1
  rintro ⟨r,⟨i,rfl⟩⟩
  exact h i

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricLocalizedCech

variable {R : Type*} [CommRing R]

/-- The actual map R[1/a] → R[1/(ab)] is localization of modules away
from b. The proof uses the genuine iterated localization and its universal
comparison, and does not posit an abstract restriction isomorphism. -/
theorem awayProduct_isLocalized (a b : R)
    {S T : Type*} [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [IsLocalization.Away a S] [IsLocalization.Away (a*b) T]
    (φ : S →ₐ[R] T) : IsLocalizedModule (Submonoid.powers b) φ.toLinearMap := by
  let U := Localization.Away (algebraMap R S b)
  let f : S →ₐ[R] U := IsScalarTower.toAlgHom R S U
  haveI : IsLocalization.Away (a*b) U := inferInstance
  haveI : IsLocalizedModule (Submonoid.powers b) f.toLinearMap := inferInstance
  let e : U ≃ₐ[R] T := IsLocalization.algEquiv (Submonoid.powers (a*b)) U T
  have he : e.toAlgHom.comp f = φ := by
    apply IsLocalization.algHom_ext (Submonoid.powers a)
    ext x
  have hm : e.toLinearEquiv.toLinearMap.comp f.toLinearMap = φ.toLinearMap :=
    congrArg AlgHom.toLinearMap he
  rw [← hm]
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers b) f.toLinearMap e.toLinearEquiv

variable {ι : Type*} [DecidableEq ι]

def coverProduct (a : ι → R) (s : Finset ι) : R := ∏ i ∈ s, a i
abbrev RingAt (a : ι → R) (s : Finset ι) := Localization.Away (coverProduct a s)

def ringRestriction (a : ι → R) {s t : Finset ι} (hst : s ⊆ t) :
    RingAt a s →ₐ[R] RingAt a t where
  __ := IsLocalization.Away.lift (S := RingAt a s) (coverProduct a s)
    (IsLocalization.Away.isUnit_of_dvd (S := RingAt a t) (coverProduct a t)
      (Finset.prod_dvd_prod_of_subset s t a hst))
  commutes' x := IsLocalization.Away.lift_eq _ _ x

@[simp] theorem ringRestriction_base (a : ι → R) {s t : Finset ι}
    (hst : s ⊆ t) (x : R) :
    ringRestriction a hst (algebraMap R (RingAt a s) x) =
      algebraMap R (RingAt a t) x := (ringRestriction a hst).commutes x

@[simp] theorem ringRestriction_comp (a : ι → R) {s t u : Finset ι}
    (hst : s ⊆ t) (htu : t ⊆ u) (x : RingAt a s) :
    ringRestriction a htu (ringRestriction a hst x) =
      ringRestriction a (hst.trans htu) x := by
  have hh : (ringRestriction a htu).comp (ringRestriction a hst) =
      ringRestriction a (hst.trans htu) := by
    apply IsLocalization.algHom_ext (Submonoid.powers (coverProduct a s))
    ext p
  exact AlgHom.congr_fun hh x

@[simp] theorem ringRestriction_self (a : ι → R) (s : Finset ι) :
    ringRestriction a (s := s) (t := s) (by rfl) = AlgHom.id _ _ := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coverProduct a s))
  ext p

/-- Every restriction adjoining one distinguished open is precisely the
localization at that element, including repeated indices. -/
theorem ringRestriction_insert_isLocalized (a : ι → R) (i : ι) (s : Finset ι) :
    IsLocalizedModule (Submonoid.powers (a i))
      (ringRestriction a (s := s) (t := insert i s) (by simp)).toLinearMap := by
  by_cases hi : i ∈ s
  · haveI : IsLocalization.Away (coverProduct a s) (RingAt a (insert i s)) := by
      rw [Finset.insert_eq_of_mem hi]
      infer_instance
    have hu : IsUnit (algebraMap R (RingAt a (insert i s)) (a i)) :=
      IsLocalization.Away.isUnit_of_dvd (S := RingAt a (insert i s))
        (coverProduct a (insert i s)) (Finset.dvd_prod_of_mem a (by simp))
    haveI : IsLocalization.Away (coverProduct a s * a i) (RingAt a (insert i s)) :=
      IsLocalization.Away.mul_of_isUnit (coverProduct a s) (a i) hu
    exact awayProduct_isLocalized (coverProduct a s) (a i) _
  · have hp : coverProduct a (insert i s) = coverProduct a s * a i := by
      simp [coverProduct, Finset.prod_insert hi, mul_comm]
    haveI : IsLocalization.Away (coverProduct a s * a i) (RingAt a (insert i s)) := by
      rw [← hp]
      infer_instance
    exact awayProduct_isLocalized (coverProduct a s) (a i) _

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]

/-- A genuine Čech contraction when one open is the whole space: adjoining
that index changes no section module. No cohomological vanishing is assumed. -/
theorem first_exact_of_pivot (D : RestrictionSystem R V) (k : Fin 4)
    (h : ∀ s : Finset (Fin 4),
      Function.Bijective (D.res (s := s) (t := insert k s) (by simp))) :
    Function.Exact (d0 D) (d1 D) := by
  intro p
  constructor
  · intro hp
    have bij {s t : Finset (Fin 4)} (hst : s ⊆ t) (ht : t = insert k s) :
        Function.Bijective (D.res hst) := by
      subst t
      exact h s
    fin_cases k
    · obtain ⟨q1, h1⟩ := (bij (s := {1}) (t := {0,1}) (by decide) (by decide)).2 p.1.1
      obtain ⟨q2, h2⟩ := (bij (s := {2}) (t := {0,2}) (by decide) (by decide)).2 p.1.2.1
      obtain ⟨q3, h3⟩ := (bij (s := {3}) (t := {0,3}) (by decide) (by decide)).2 p.1.2.2
      refine ⟨((0, q1), (q2, q3)), ?_⟩
      refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) (Prod.ext ?_ (Prod.ext ?_ ?_))
      · change D.res (s := {1}) (t := {0,1}) (by decide) q1 - D.res (s := {0}) (t := {0,1}) (by decide) 0 = p.1.1
        simp only [map_zero, h1, sub_zero, zero_sub, neg_neg]
      · change D.res (s := {2}) (t := {0,2}) (by decide) q2 - D.res (s := {0}) (t := {0,2}) (by decide) 0 = p.1.2.1
        simp only [map_zero, h2, sub_zero, zero_sub, neg_neg]
      · change D.res (s := {3}) (t := {0,3}) (by decide) q3 - D.res (s := {0}) (t := {0,3}) (by decide) 0 = p.1.2.2
        simp only [map_zero, h3, sub_zero, zero_sub, neg_neg]
      · apply (bij (s := {1,2}) (t := {0,1,2}) (by decide) (by decide)).1
        change D.res (s := {1,2}) (t := {0,1,2}) (by decide) (D.res (s := {2}) (t := {1,2}) (by decide) q2 - D.res (s := {1}) (t := {1,2}) (by decide) q1) = D.res (s := {1,2}) (t := {0,1,2}) (by decide) p.2.1
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {0,1}) (t := {0,1,2}) (by decide)) h1
        have hj := congrArg (D.res (s := {0,2}) (t := {0,1,2}) (by decide)) h2
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.1.1) hp
        change (D.res (s := {1,2}) (t := {0,1,2}) (by decide) p.2.1 - D.res (s := {0,2}) (t := {0,1,2}) (by decide) p.1.2.1 + D.res (s := {0,1}) (t := {0,1,2}) (by decide) p.1.1) = 0 at ht
        calc
          _ = D.res (s := {1,2}) (t := {0,1,2}) (by decide) p.2.1 - (D.res (s := {1,2}) (t := {0,1,2}) (by decide) p.2.1 - D.res (s := {0,2}) (t := {0,1,2}) (by decide) p.1.2.1 + D.res (s := {0,1}) (t := {0,1,2}) (by decide) p.1.1) := by abel
          _ = _ := by rw [ht, sub_zero]
      · apply (bij (s := {1,3}) (t := {0,1,3}) (by decide) (by decide)).1
        change D.res (s := {1,3}) (t := {0,1,3}) (by decide) (D.res (s := {3}) (t := {1,3}) (by decide) q3 - D.res (s := {1}) (t := {1,3}) (by decide) q1) = D.res (s := {1,3}) (t := {0,1,3}) (by decide) p.2.2.1
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {0,1}) (t := {0,1,3}) (by decide)) h1
        have hj := congrArg (D.res (s := {0,3}) (t := {0,1,3}) (by decide)) h3
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.1.2) hp
        change (D.res (s := {1,3}) (t := {0,1,3}) (by decide) p.2.2.1 - D.res (s := {0,3}) (t := {0,1,3}) (by decide) p.1.2.2 + D.res (s := {0,1}) (t := {0,1,3}) (by decide) p.1.1) = 0 at ht
        calc
          _ = D.res (s := {1,3}) (t := {0,1,3}) (by decide) p.2.2.1 - (D.res (s := {1,3}) (t := {0,1,3}) (by decide) p.2.2.1 - D.res (s := {0,3}) (t := {0,1,3}) (by decide) p.1.2.2 + D.res (s := {0,1}) (t := {0,1,3}) (by decide) p.1.1) := by abel
          _ = _ := by rw [ht, sub_zero]
      · apply (bij (s := {2,3}) (t := {0,2,3}) (by decide) (by decide)).1
        change D.res (s := {2,3}) (t := {0,2,3}) (by decide) (D.res (s := {3}) (t := {2,3}) (by decide) q3 - D.res (s := {2}) (t := {2,3}) (by decide) q2) = D.res (s := {2,3}) (t := {0,2,3}) (by decide) p.2.2.2
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {0,2}) (t := {0,2,3}) (by decide)) h2
        have hj := congrArg (D.res (s := {0,3}) (t := {0,2,3}) (by decide)) h3
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.2.1) hp
        change (D.res (s := {2,3}) (t := {0,2,3}) (by decide) p.2.2.2 - D.res (s := {0,3}) (t := {0,2,3}) (by decide) p.1.2.2 + D.res (s := {0,2}) (t := {0,2,3}) (by decide) p.1.2.1) = 0 at ht
        calc
          _ = D.res (s := {2,3}) (t := {0,2,3}) (by decide) p.2.2.2 - (D.res (s := {2,3}) (t := {0,2,3}) (by decide) p.2.2.2 - D.res (s := {0,3}) (t := {0,2,3}) (by decide) p.1.2.2 + D.res (s := {0,2}) (t := {0,2,3}) (by decide) p.1.2.1) := by abel
          _ = _ := by rw [ht, sub_zero]
    · obtain ⟨q0, h0⟩ := (bij (s := {0}) (t := {0,1}) (by decide) (by decide)).2 (-p.1.1)
      obtain ⟨q2, h2⟩ := (bij (s := {2}) (t := {1,2}) (by decide) (by decide)).2 p.2.1
      obtain ⟨q3, h3⟩ := (bij (s := {3}) (t := {1,3}) (by decide) (by decide)).2 p.2.2.1
      refine ⟨((q0, 0), (q2, q3)), ?_⟩
      refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) (Prod.ext ?_ (Prod.ext ?_ ?_))
      · change D.res (s := {1}) (t := {0,1}) (by decide) 0 - D.res (s := {0}) (t := {0,1}) (by decide) q0 = p.1.1
        simp only [map_zero, h0, sub_zero, zero_sub, neg_neg]
      · apply (bij (s := {0,2}) (t := {0,1,2}) (by decide) (by decide)).1
        change D.res (s := {0,2}) (t := {0,1,2}) (by decide) (D.res (s := {2}) (t := {0,2}) (by decide) q2 - D.res (s := {0}) (t := {0,2}) (by decide) q0) = D.res (s := {0,2}) (t := {0,1,2}) (by decide) p.1.2.1
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {0,1}) (t := {0,1,2}) (by decide)) h0
        have hj := congrArg (D.res (s := {1,2}) (t := {0,1,2}) (by decide)) h2
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.1.1) hp
        change (D.res (s := {1,2}) (t := {0,1,2}) (by decide) p.2.1 - D.res (s := {0,2}) (t := {0,1,2}) (by decide) p.1.2.1 + D.res (s := {0,1}) (t := {0,1,2}) (by decide) p.1.1) = 0 at ht
        calc
          _ = D.res (s := {0,2}) (t := {0,1,2}) (by decide) p.1.2.1 + (D.res (s := {1,2}) (t := {0,1,2}) (by decide) p.2.1 - D.res (s := {0,2}) (t := {0,1,2}) (by decide) p.1.2.1 + D.res (s := {0,1}) (t := {0,1,2}) (by decide) p.1.1) := by abel
          _ = _ := by rw [ht, add_zero]
      · apply (bij (s := {0,3}) (t := {0,1,3}) (by decide) (by decide)).1
        change D.res (s := {0,3}) (t := {0,1,3}) (by decide) (D.res (s := {3}) (t := {0,3}) (by decide) q3 - D.res (s := {0}) (t := {0,3}) (by decide) q0) = D.res (s := {0,3}) (t := {0,1,3}) (by decide) p.1.2.2
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {0,1}) (t := {0,1,3}) (by decide)) h0
        have hj := congrArg (D.res (s := {1,3}) (t := {0,1,3}) (by decide)) h3
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.1.2) hp
        change (D.res (s := {1,3}) (t := {0,1,3}) (by decide) p.2.2.1 - D.res (s := {0,3}) (t := {0,1,3}) (by decide) p.1.2.2 + D.res (s := {0,1}) (t := {0,1,3}) (by decide) p.1.1) = 0 at ht
        calc
          _ = D.res (s := {0,3}) (t := {0,1,3}) (by decide) p.1.2.2 + (D.res (s := {1,3}) (t := {0,1,3}) (by decide) p.2.2.1 - D.res (s := {0,3}) (t := {0,1,3}) (by decide) p.1.2.2 + D.res (s := {0,1}) (t := {0,1,3}) (by decide) p.1.1) := by abel
          _ = _ := by rw [ht, add_zero]
      · change D.res (s := {2}) (t := {1,2}) (by decide) q2 - D.res (s := {1}) (t := {1,2}) (by decide) 0 = p.2.1
        simp only [map_zero, h2, sub_zero, zero_sub, neg_neg]
      · change D.res (s := {3}) (t := {1,3}) (by decide) q3 - D.res (s := {1}) (t := {1,3}) (by decide) 0 = p.2.2.1
        simp only [map_zero, h3, sub_zero, zero_sub, neg_neg]
      · apply (bij (s := {2,3}) (t := {1,2,3}) (by decide) (by decide)).1
        change D.res (s := {2,3}) (t := {1,2,3}) (by decide) (D.res (s := {3}) (t := {2,3}) (by decide) q3 - D.res (s := {2}) (t := {2,3}) (by decide) q2) = D.res (s := {2,3}) (t := {1,2,3}) (by decide) p.2.2.2
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {1,2}) (t := {1,2,3}) (by decide)) h2
        have hj := congrArg (D.res (s := {1,3}) (t := {1,2,3}) (by decide)) h3
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.2.2) hp
        change (D.res (s := {2,3}) (t := {1,2,3}) (by decide) p.2.2.2 - D.res (s := {1,3}) (t := {1,2,3}) (by decide) p.2.2.1 + D.res (s := {1,2}) (t := {1,2,3}) (by decide) p.2.1) = 0 at ht
        calc
          _ = D.res (s := {2,3}) (t := {1,2,3}) (by decide) p.2.2.2 - (D.res (s := {2,3}) (t := {1,2,3}) (by decide) p.2.2.2 - D.res (s := {1,3}) (t := {1,2,3}) (by decide) p.2.2.1 + D.res (s := {1,2}) (t := {1,2,3}) (by decide) p.2.1) := by abel
          _ = _ := by rw [ht, sub_zero]
    · obtain ⟨q0, h0⟩ := (bij (s := {0}) (t := {0,2}) (by decide) (by decide)).2 (-p.1.2.1)
      obtain ⟨q1, h1⟩ := (bij (s := {1}) (t := {1,2}) (by decide) (by decide)).2 (-p.2.1)
      obtain ⟨q3, h3⟩ := (bij (s := {3}) (t := {2,3}) (by decide) (by decide)).2 p.2.2.2
      refine ⟨((q0, q1), (0, q3)), ?_⟩
      refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) (Prod.ext ?_ (Prod.ext ?_ ?_))
      · apply (bij (s := {0,1}) (t := {0,1,2}) (by decide) (by decide)).1
        change D.res (s := {0,1}) (t := {0,1,2}) (by decide) (D.res (s := {1}) (t := {0,1}) (by decide) q1 - D.res (s := {0}) (t := {0,1}) (by decide) q0) = D.res (s := {0,1}) (t := {0,1,2}) (by decide) p.1.1
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {0,2}) (t := {0,1,2}) (by decide)) h0
        have hj := congrArg (D.res (s := {1,2}) (t := {0,1,2}) (by decide)) h1
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.1.1) hp
        change (D.res (s := {1,2}) (t := {0,1,2}) (by decide) p.2.1 - D.res (s := {0,2}) (t := {0,1,2}) (by decide) p.1.2.1 + D.res (s := {0,1}) (t := {0,1,2}) (by decide) p.1.1) = 0 at ht
        calc
          _ = D.res (s := {0,1}) (t := {0,1,2}) (by decide) p.1.1 - (D.res (s := {1,2}) (t := {0,1,2}) (by decide) p.2.1 - D.res (s := {0,2}) (t := {0,1,2}) (by decide) p.1.2.1 + D.res (s := {0,1}) (t := {0,1,2}) (by decide) p.1.1) := by abel
          _ = _ := by rw [ht, sub_zero]
      · change D.res (s := {2}) (t := {0,2}) (by decide) 0 - D.res (s := {0}) (t := {0,2}) (by decide) q0 = p.1.2.1
        simp only [map_zero, h0, sub_zero, zero_sub, neg_neg]
      · apply (bij (s := {0,3}) (t := {0,2,3}) (by decide) (by decide)).1
        change D.res (s := {0,3}) (t := {0,2,3}) (by decide) (D.res (s := {3}) (t := {0,3}) (by decide) q3 - D.res (s := {0}) (t := {0,3}) (by decide) q0) = D.res (s := {0,3}) (t := {0,2,3}) (by decide) p.1.2.2
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {0,2}) (t := {0,2,3}) (by decide)) h0
        have hj := congrArg (D.res (s := {2,3}) (t := {0,2,3}) (by decide)) h3
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.2.1) hp
        change (D.res (s := {2,3}) (t := {0,2,3}) (by decide) p.2.2.2 - D.res (s := {0,3}) (t := {0,2,3}) (by decide) p.1.2.2 + D.res (s := {0,2}) (t := {0,2,3}) (by decide) p.1.2.1) = 0 at ht
        calc
          _ = D.res (s := {0,3}) (t := {0,2,3}) (by decide) p.1.2.2 + (D.res (s := {2,3}) (t := {0,2,3}) (by decide) p.2.2.2 - D.res (s := {0,3}) (t := {0,2,3}) (by decide) p.1.2.2 + D.res (s := {0,2}) (t := {0,2,3}) (by decide) p.1.2.1) := by abel
          _ = _ := by rw [ht, add_zero]
      · change D.res (s := {2}) (t := {1,2}) (by decide) 0 - D.res (s := {1}) (t := {1,2}) (by decide) q1 = p.2.1
        simp only [map_zero, h1, sub_zero, zero_sub, neg_neg]
      · apply (bij (s := {1,3}) (t := {1,2,3}) (by decide) (by decide)).1
        change D.res (s := {1,3}) (t := {1,2,3}) (by decide) (D.res (s := {3}) (t := {1,3}) (by decide) q3 - D.res (s := {1}) (t := {1,3}) (by decide) q1) = D.res (s := {1,3}) (t := {1,2,3}) (by decide) p.2.2.1
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {1,2}) (t := {1,2,3}) (by decide)) h1
        have hj := congrArg (D.res (s := {2,3}) (t := {1,2,3}) (by decide)) h3
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.2.2) hp
        change (D.res (s := {2,3}) (t := {1,2,3}) (by decide) p.2.2.2 - D.res (s := {1,3}) (t := {1,2,3}) (by decide) p.2.2.1 + D.res (s := {1,2}) (t := {1,2,3}) (by decide) p.2.1) = 0 at ht
        calc
          _ = D.res (s := {1,3}) (t := {1,2,3}) (by decide) p.2.2.1 + (D.res (s := {2,3}) (t := {1,2,3}) (by decide) p.2.2.2 - D.res (s := {1,3}) (t := {1,2,3}) (by decide) p.2.2.1 + D.res (s := {1,2}) (t := {1,2,3}) (by decide) p.2.1) := by abel
          _ = _ := by rw [ht, add_zero]
      · change D.res (s := {3}) (t := {2,3}) (by decide) q3 - D.res (s := {2}) (t := {2,3}) (by decide) 0 = p.2.2.2
        simp only [map_zero, h3, sub_zero, zero_sub, neg_neg]
    · obtain ⟨q0, h0⟩ := (bij (s := {0}) (t := {0,3}) (by decide) (by decide)).2 (-p.1.2.2)
      obtain ⟨q1, h1⟩ := (bij (s := {1}) (t := {1,3}) (by decide) (by decide)).2 (-p.2.2.1)
      obtain ⟨q2, h2⟩ := (bij (s := {2}) (t := {2,3}) (by decide) (by decide)).2 (-p.2.2.2)
      refine ⟨((q0, q1), (q2, 0)), ?_⟩
      refine Prod.ext (Prod.ext ?_ (Prod.ext ?_ ?_)) (Prod.ext ?_ (Prod.ext ?_ ?_))
      · apply (bij (s := {0,1}) (t := {0,1,3}) (by decide) (by decide)).1
        change D.res (s := {0,1}) (t := {0,1,3}) (by decide) (D.res (s := {1}) (t := {0,1}) (by decide) q1 - D.res (s := {0}) (t := {0,1}) (by decide) q0) = D.res (s := {0,1}) (t := {0,1,3}) (by decide) p.1.1
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {0,3}) (t := {0,1,3}) (by decide)) h0
        have hj := congrArg (D.res (s := {1,3}) (t := {0,1,3}) (by decide)) h1
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.1.2) hp
        change (D.res (s := {1,3}) (t := {0,1,3}) (by decide) p.2.2.1 - D.res (s := {0,3}) (t := {0,1,3}) (by decide) p.1.2.2 + D.res (s := {0,1}) (t := {0,1,3}) (by decide) p.1.1) = 0 at ht
        calc
          _ = D.res (s := {0,1}) (t := {0,1,3}) (by decide) p.1.1 - (D.res (s := {1,3}) (t := {0,1,3}) (by decide) p.2.2.1 - D.res (s := {0,3}) (t := {0,1,3}) (by decide) p.1.2.2 + D.res (s := {0,1}) (t := {0,1,3}) (by decide) p.1.1) := by abel
          _ = _ := by rw [ht, sub_zero]
      · apply (bij (s := {0,2}) (t := {0,2,3}) (by decide) (by decide)).1
        change D.res (s := {0,2}) (t := {0,2,3}) (by decide) (D.res (s := {2}) (t := {0,2}) (by decide) q2 - D.res (s := {0}) (t := {0,2}) (by decide) q0) = D.res (s := {0,2}) (t := {0,2,3}) (by decide) p.1.2.1
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {0,3}) (t := {0,2,3}) (by decide)) h0
        have hj := congrArg (D.res (s := {2,3}) (t := {0,2,3}) (by decide)) h2
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.2.1) hp
        change (D.res (s := {2,3}) (t := {0,2,3}) (by decide) p.2.2.2 - D.res (s := {0,3}) (t := {0,2,3}) (by decide) p.1.2.2 + D.res (s := {0,2}) (t := {0,2,3}) (by decide) p.1.2.1) = 0 at ht
        calc
          _ = D.res (s := {0,2}) (t := {0,2,3}) (by decide) p.1.2.1 - (D.res (s := {2,3}) (t := {0,2,3}) (by decide) p.2.2.2 - D.res (s := {0,3}) (t := {0,2,3}) (by decide) p.1.2.2 + D.res (s := {0,2}) (t := {0,2,3}) (by decide) p.1.2.1) := by abel
          _ = _ := by rw [ht, sub_zero]
      · change D.res (s := {3}) (t := {0,3}) (by decide) 0 - D.res (s := {0}) (t := {0,3}) (by decide) q0 = p.1.2.2
        simp only [map_zero, h0, sub_zero, zero_sub, neg_neg]
      · apply (bij (s := {1,2}) (t := {1,2,3}) (by decide) (by decide)).1
        change D.res (s := {1,2}) (t := {1,2,3}) (by decide) (D.res (s := {2}) (t := {1,2}) (by decide) q2 - D.res (s := {1}) (t := {1,2}) (by decide) q1) = D.res (s := {1,2}) (t := {1,2,3}) (by decide) p.2.1
        simp only [map_sub, RestrictionSystem.res_res]
        have hi := congrArg (D.res (s := {1,3}) (t := {1,2,3}) (by decide)) h1
        have hj := congrArg (D.res (s := {2,3}) (t := {1,2,3}) (by decide)) h2
        simp only [RestrictionSystem.res_res, map_neg] at hi hj
        rw [hi, hj]
        have ht := congrArg (fun x : TwoCochain V => x.2.2) hp
        change (D.res (s := {2,3}) (t := {1,2,3}) (by decide) p.2.2.2 - D.res (s := {1,3}) (t := {1,2,3}) (by decide) p.2.2.1 + D.res (s := {1,2}) (t := {1,2,3}) (by decide) p.2.1) = 0 at ht
        calc
          _ = D.res (s := {1,2}) (t := {1,2,3}) (by decide) p.2.1 - (D.res (s := {2,3}) (t := {1,2,3}) (by decide) p.2.2.2 - D.res (s := {1,3}) (t := {1,2,3}) (by decide) p.2.2.1 + D.res (s := {1,2}) (t := {1,2,3}) (by decide) p.2.1) := by abel
          _ = _ := by rw [ht, sub_zero]
      · change D.res (s := {3}) (t := {1,3}) (by decide) 0 - D.res (s := {1}) (t := {1,3}) (by decide) q1 = p.2.2.1
        simp only [map_zero, h1, sub_zero, zero_sub, neg_neg]
      · change D.res (s := {3}) (t := {2,3}) (by decide) 0 - D.res (s := {2}) (t := {2,3}) (by decide) q2 = p.2.2.2
        simp only [map_zero, h2, sub_zero, zero_sub, neg_neg]
  · rintro ⟨q, rfl⟩
    exact d1_d0 D q

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]

def augmentation (D : RestrictionSystem R V) : V ∅ →ₗ[R] ZeroCochain V where
  toFun x := ((D.res (by simp) x, D.res (by simp) x),
    (D.res (by simp) x, D.res (by simp) x))
  map_add' x y := by ext <;> simp only [map_add, Prod.fst_add, Prod.snd_add]
  map_smul' r x := by
    ext <;> simp only [map_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]

@[simp] theorem d0_augmentation (D : RestrictionSystem R V) (x : V ∅) :
    d0 D (augmentation D x) = 0 := by
  ext <;> dsimp [augmentation, d0] <;>
    simp only [RestrictionSystem.res_res, sub_self]

theorem zero_exact_of_pivot (D : RestrictionSystem R V) (k : Fin 4)
    (h : ∀ s : Finset (Fin 4),
      Function.Bijective (D.res (s := s) (t := insert k s) (by simp))) :
    Function.Exact (augmentation D) (d0 D) := by
  intro p
  constructor
  · intro hp
    have bij {s t : Finset (Fin 4)} (hst : s ⊆ t) (ht : t = insert k s) :
        Function.Bijective (D.res hst) := by
      subst t
      exact h s
    fin_cases k
    · obtain ⟨x,hx⟩ := (bij (s := ∅) (t := {0}) (by simp) (by decide)).2 p.1.1
      refine ⟨x, Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)⟩
      · exact hx
      · apply (bij (s := {1}) (t := {0,1}) (by decide) (by decide)).1
        change D.res (s := {1}) (t := {0,1}) (by decide) (D.res (s := ∅) (t := {1}) (by decide) x) = D.res (s := {1}) (t := {0,1}) (by decide) p.1.2
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.1.1) hp
        change D.res (s := {1}) (t := {0,1}) (by decide) p.1.2 - D.res (s := {0}) (t := {0,1}) (by decide) p.1.1 = 0 at he
        have hx' := congrArg (D.res (s := {0}) (t := {0,1}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he).symm
      · apply (bij (s := {2}) (t := {0,2}) (by decide) (by decide)).1
        change D.res (s := {2}) (t := {0,2}) (by decide) (D.res (s := ∅) (t := {2}) (by decide) x) = D.res (s := {2}) (t := {0,2}) (by decide) p.2.1
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.1.2.1) hp
        change D.res (s := {2}) (t := {0,2}) (by decide) p.2.1 - D.res (s := {0}) (t := {0,2}) (by decide) p.1.1 = 0 at he
        have hx' := congrArg (D.res (s := {0}) (t := {0,2}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he).symm
      · apply (bij (s := {3}) (t := {0,3}) (by decide) (by decide)).1
        change D.res (s := {3}) (t := {0,3}) (by decide) (D.res (s := ∅) (t := {3}) (by decide) x) = D.res (s := {3}) (t := {0,3}) (by decide) p.2.2
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.1.2.2) hp
        change D.res (s := {3}) (t := {0,3}) (by decide) p.2.2 - D.res (s := {0}) (t := {0,3}) (by decide) p.1.1 = 0 at he
        have hx' := congrArg (D.res (s := {0}) (t := {0,3}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he).symm
    · obtain ⟨x,hx⟩ := (bij (s := ∅) (t := {1}) (by simp) (by decide)).2 p.1.2
      refine ⟨x, Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)⟩
      · apply (bij (s := {0}) (t := {0,1}) (by decide) (by decide)).1
        change D.res (s := {0}) (t := {0,1}) (by decide) (D.res (s := ∅) (t := {0}) (by decide) x) = D.res (s := {0}) (t := {0,1}) (by decide) p.1.1
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.1.1) hp
        change D.res (s := {1}) (t := {0,1}) (by decide) p.1.2 - D.res (s := {0}) (t := {0,1}) (by decide) p.1.1 = 0 at he
        have hx' := congrArg (D.res (s := {1}) (t := {0,1}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he)
      · exact hx
      · apply (bij (s := {2}) (t := {1,2}) (by decide) (by decide)).1
        change D.res (s := {2}) (t := {1,2}) (by decide) (D.res (s := ∅) (t := {2}) (by decide) x) = D.res (s := {2}) (t := {1,2}) (by decide) p.2.1
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.2.1) hp
        change D.res (s := {2}) (t := {1,2}) (by decide) p.2.1 - D.res (s := {1}) (t := {1,2}) (by decide) p.1.2 = 0 at he
        have hx' := congrArg (D.res (s := {1}) (t := {1,2}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he).symm
      · apply (bij (s := {3}) (t := {1,3}) (by decide) (by decide)).1
        change D.res (s := {3}) (t := {1,3}) (by decide) (D.res (s := ∅) (t := {3}) (by decide) x) = D.res (s := {3}) (t := {1,3}) (by decide) p.2.2
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.2.2.1) hp
        change D.res (s := {3}) (t := {1,3}) (by decide) p.2.2 - D.res (s := {1}) (t := {1,3}) (by decide) p.1.2 = 0 at he
        have hx' := congrArg (D.res (s := {1}) (t := {1,3}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he).symm
    · obtain ⟨x,hx⟩ := (bij (s := ∅) (t := {2}) (by simp) (by decide)).2 p.2.1
      refine ⟨x, Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)⟩
      · apply (bij (s := {0}) (t := {0,2}) (by decide) (by decide)).1
        change D.res (s := {0}) (t := {0,2}) (by decide) (D.res (s := ∅) (t := {0}) (by decide) x) = D.res (s := {0}) (t := {0,2}) (by decide) p.1.1
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.1.2.1) hp
        change D.res (s := {2}) (t := {0,2}) (by decide) p.2.1 - D.res (s := {0}) (t := {0,2}) (by decide) p.1.1 = 0 at he
        have hx' := congrArg (D.res (s := {2}) (t := {0,2}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he)
      · apply (bij (s := {1}) (t := {1,2}) (by decide) (by decide)).1
        change D.res (s := {1}) (t := {1,2}) (by decide) (D.res (s := ∅) (t := {1}) (by decide) x) = D.res (s := {1}) (t := {1,2}) (by decide) p.1.2
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.2.1) hp
        change D.res (s := {2}) (t := {1,2}) (by decide) p.2.1 - D.res (s := {1}) (t := {1,2}) (by decide) p.1.2 = 0 at he
        have hx' := congrArg (D.res (s := {2}) (t := {1,2}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he)
      · exact hx
      · apply (bij (s := {3}) (t := {2,3}) (by decide) (by decide)).1
        change D.res (s := {3}) (t := {2,3}) (by decide) (D.res (s := ∅) (t := {3}) (by decide) x) = D.res (s := {3}) (t := {2,3}) (by decide) p.2.2
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.2.2.2) hp
        change D.res (s := {3}) (t := {2,3}) (by decide) p.2.2 - D.res (s := {2}) (t := {2,3}) (by decide) p.2.1 = 0 at he
        have hx' := congrArg (D.res (s := {2}) (t := {2,3}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he).symm
    · obtain ⟨x,hx⟩ := (bij (s := ∅) (t := {3}) (by simp) (by decide)).2 p.2.2
      refine ⟨x, Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)⟩
      · apply (bij (s := {0}) (t := {0,3}) (by decide) (by decide)).1
        change D.res (s := {0}) (t := {0,3}) (by decide) (D.res (s := ∅) (t := {0}) (by decide) x) = D.res (s := {0}) (t := {0,3}) (by decide) p.1.1
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.1.2.2) hp
        change D.res (s := {3}) (t := {0,3}) (by decide) p.2.2 - D.res (s := {0}) (t := {0,3}) (by decide) p.1.1 = 0 at he
        have hx' := congrArg (D.res (s := {3}) (t := {0,3}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he)
      · apply (bij (s := {1}) (t := {1,3}) (by decide) (by decide)).1
        change D.res (s := {1}) (t := {1,3}) (by decide) (D.res (s := ∅) (t := {1}) (by decide) x) = D.res (s := {1}) (t := {1,3}) (by decide) p.1.2
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.2.2.1) hp
        change D.res (s := {3}) (t := {1,3}) (by decide) p.2.2 - D.res (s := {1}) (t := {1,3}) (by decide) p.1.2 = 0 at he
        have hx' := congrArg (D.res (s := {3}) (t := {1,3}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he)
      · apply (bij (s := {2}) (t := {2,3}) (by decide) (by decide)).1
        change D.res (s := {2}) (t := {2,3}) (by decide) (D.res (s := ∅) (t := {2}) (by decide) x) = D.res (s := {2}) (t := {2,3}) (by decide) p.2.1
        rw [RestrictionSystem.res_res]
        have he := congrArg (fun x : OneCochain V => x.2.2.2) hp
        change D.res (s := {3}) (t := {2,3}) (by decide) p.2.2 - D.res (s := {2}) (t := {2,3}) (by decide) p.2.1 = 0 at he
        have hx' := congrArg (D.res (s := {3}) (t := {2,3}) (by decide)) hx
        rw [RestrictionSystem.res_res] at hx'
        rw [hx']
        exact (sub_eq_zero.mp he)
      · exact hx
  · rintro ⟨x,rfl⟩
    exact d0_augmentation D x

theorem augmentation_injective_of_pivot (D : RestrictionSystem R V) (k : Fin 4)
    (h : ∀ s : Finset (Fin 4),
      Function.Bijective (D.res (s := s) (t := insert k s) (by simp))) :
    Function.Injective (augmentation D) := by
  intro x y hxy
  have hk := (h ∅).1
  fin_cases k
  · exact hk (congrArg (fun q : ZeroCochain V => q.1.1) hxy)
  · exact hk (congrArg (fun q : ZeroCochain V => q.1.2) hxy)
  · exact hk (congrArg (fun q : ZeroCochain V => q.2.1) hxy)
  · exact hk (congrArg (fun q : ZeroCochain V => q.2.2) hxy)

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V W : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]
variable [∀ s, AddCommGroup (W s)] [∀ s, Module R (W s)]

structure SystemMorphism (D : RestrictionSystem R V) (E : RestrictionSystem R W) where
  app (s : Finset (Fin 4)) : V s →ₗ[R] W s
  naturality {s t : Finset (Fin 4)} (hst : s ⊆ t) :
    (app t).comp (D.res hst) = (E.res hst).comp (app s)

namespace SystemMorphism

variable {D : RestrictionSystem R V} {E : RestrictionSystem R W}

@[simp] theorem app_res (f : SystemMorphism D E) {s t : Finset (Fin 4)}
    (hst : s ⊆ t) (x : V s) : f.app t (D.res hst x) = E.res hst (f.app s x) :=
  LinearMap.congr_fun (f.naturality hst) x

def map0 (f : SystemMorphism D E) : ZeroCochain V →ₗ[R] ZeroCochain W :=
  ((f.app {0}).prodMap (f.app {1})).prodMap ((f.app {2}).prodMap (f.app {3}))

def map1 (f : SystemMorphism D E) : OneCochain V →ₗ[R] OneCochain W :=
  ((f.app {0,1}).prodMap ((f.app {0,2}).prodMap (f.app {0,3}))).prodMap
    ((f.app {1,2}).prodMap ((f.app {1,3}).prodMap (f.app {2,3})))

def map2 (f : SystemMorphism D E) : TwoCochain V →ₗ[R] TwoCochain W :=
  ((f.app {0,1,2}).prodMap (f.app {0,1,3})).prodMap
    ((f.app {0,2,3}).prodMap (f.app {1,2,3}))

@[simp] theorem map1_d0 (f : SystemMorphism D E) (p : ZeroCochain V) :
    f.map1 (d0 D p) = d0 E (f.map0 p) := by
  ext <;> dsimp [map0, map1, d0]
  all_goals simp only [map_sub, app_res]

@[simp] theorem map2_d1 (f : SystemMorphism D E) (p : OneCochain V) :
    f.map2 (d1 D p) = d1 E (f.map1 p) := by
  ext <;> dsimp [map1, map2, d1]
  all_goals simp only [map_add, map_sub, app_res]

@[simp] theorem app_d2 (f : SystemMorphism D E) (p : TwoCochain V) :
    f.app Finset.univ (d2 D p) = d2 E (f.map2 p) := by
  dsimp [map2, d2]
  simp only [map_add, map_sub, app_res]

open CycleQ2GeometricLocalizedCech

variable (S : Submonoid R) (f : SystemMorphism D E)
variable [∀ s, IsLocalizedModule S (f.app s)]

instance map0_isLocalized : IsLocalizedModule S f.map0 := by
  letI := isLocalizedModule_prod S (f.app {0}) (f.app {1})
  letI := isLocalizedModule_prod S (f.app {2}) (f.app {3})
  exact isLocalizedModule_prod S _ _

instance map1_isLocalized : IsLocalizedModule S f.map1 := by
  letI := isLocalizedModule_prod S (f.app {0,2}) (f.app {0,3})
  letI := isLocalizedModule_prod S (f.app {1,3}) (f.app {2,3})
  letI := isLocalizedModule_prod S (f.app {0,1})
    ((f.app {0,2}).prodMap (f.app {0,3}))
  letI := isLocalizedModule_prod S (f.app {1,2})
    ((f.app {1,3}).prodMap (f.app {2,3}))
  exact isLocalizedModule_prod S _ _

instance map2_isLocalized : IsLocalizedModule S f.map2 := by
  letI := isLocalizedModule_prod S (f.app {0,1,2}) (f.app {0,1,3})
  letI := isLocalizedModule_prod S (f.app {0,2,3}) (f.app {1,2,3})
  exact isLocalizedModule_prod S _ _

theorem localized_d0 :
    IsLocalizedModule.map S f.map0 f.map1 (d0 D) = d0 E := by
  letI := f.map0_isLocalized S
  letI := f.map1_isLocalized S
  apply IsLocalizedModule.linearMap_ext S f.map0 f.map1
  rw [IsLocalizedModule.map_comp]
  exact LinearMap.ext f.map1_d0

theorem localized_d1 :
    IsLocalizedModule.map S f.map1 f.map2 (d1 D) = d1 E := by
  letI := f.map1_isLocalized S
  letI := f.map2_isLocalized S
  apply IsLocalizedModule.linearMap_ext S f.map1 f.map2
  rw [IsLocalizedModule.map_comp]
  exact LinearMap.ext f.map2_d1

include f in
theorem localized_exact_iff :
    Function.Exact
      (LocalizedModule.map S (d0 D)) (LocalizedModule.map S (d1 D)) ↔
      Function.Exact (d0 E) (d1 E) := by
  rw [← f.localized_d0 S, ← f.localized_d1 S]
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (IsLocalizedModule.map_iso_commute S f.map0 f.map1 (d0 D))
    (IsLocalizedModule.map_iso_commute S f.map1 f.map2 (d1 D))).symm

end SystemMorphism

/-- An affine distinguished-open cover is exact in degree one when each
localized system has its actual unit-open contraction. -/
theorem first_exact_of_unit_span
    (D : RestrictionSystem R V) (a : Fin 4 → R)
    (ha : Ideal.span (Set.range a) = ⊤)
    (W : Fin 4 → Finset (Fin 4) → Type*)
    [∀ i s, AddCommGroup (W i s)] [∀ i s, Module R (W i s)]
    (E : ∀ i, RestrictionSystem R (W i))
    (f : ∀ i, SystemMorphism D (E i))
    [∀ i s, IsLocalizedModule (Submonoid.powers (a i)) ((f i).app s)]
    (hpivot : ∀ (i : Fin 4) (s : Finset (Fin 4)),
      Function.Bijective ((E i).res (s := s) (t := insert i s) (by simp))) :
    Function.Exact (d0 D) (d1 D) := by
  apply CycleQ2GeometricLocalizedCech.exact_of_unit_span a ha (d0 D) (d1 D)
  intro i
  apply ((f i).localized_exact_iff (Submonoid.powers (a i))).mpr
  exact first_exact_of_pivot (E i) i (hpivot i)

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricLocalizedCech

open scoped TensorProduct
open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {ι : Type*} [DecidableEq ι]
variable (M : Type*) [AddCommGroup M] [Module R M]

abbrev ModuleAt (a : ι → R) (s : Finset ι) := RingAt a s ⊗[R] M

def moduleRestriction (a : ι → R) {s t : Finset ι} (hst : s ⊆ t) :
    ModuleAt M a s →ₗ[R] ModuleAt M a t :=
  TensorProduct.map (ringRestriction a hst).toLinearMap LinearMap.id

@[simp] theorem moduleRestriction_tmul (a : ι → R) {s t : Finset ι}
    (hst : s ⊆ t) (r : RingAt a s) (m : M) :
    moduleRestriction M a hst (r ⊗ₜ[R] m) = ringRestriction a hst r ⊗ₜ[R] m := by
  simp [moduleRestriction]

@[simp] theorem moduleRestriction_comp (a : ι → R) {s t u : Finset ι}
    (hst : s ⊆ t) (htu : t ⊆ u) (x : ModuleAt M a s) :
    moduleRestriction M a htu (moduleRestriction M a hst x) =
      moduleRestriction M a (hst.trans htu) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m => simp only [moduleRestriction_tmul, ringRestriction_comp]
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem moduleRestriction_self (a : ι → R) (s : Finset ι) :
    moduleRestriction M a (s := s) (t := s) (by rfl) = LinearMap.id := by
  ext r m
  change ringRestriction a (s := s) (t := s) (by rfl) r ⊗ₜ[R] m = r ⊗ₜ[R] m
  simp only [ringRestriction_self, AlgHom.id_apply]

theorem moduleRestriction_bijective_of_eq (a : ι → R) {s t : Finset ι}
    (h : s ⊆ t) (e : s = t) :
    Function.Bijective (moduleRestriction M a h) := by
  subst t
  rw [moduleRestriction_self]
  exact Function.bijective_id

theorem moduleRestriction_insert_isLocalized (a : ι → R) (i : ι) (s : Finset ι) :
    IsLocalizedModule (Submonoid.powers (a i))
      (moduleRestriction M a (s := s) (t := insert i s) (by simp)) := by
  letI := ringRestriction_insert_isLocalized a i s
  have heq : TensorProduct.AlgebraTensorModule.rTensor R M
      (ringRestriction a (s := s) (t := insert i s) (by simp)).toLinearMap =
      moduleRestriction M a (s := s) (t := insert i s) (by simp) := by
    rfl
  rw [← heq]
  infer_instance

/-- The genuine distinguished-open localization diagram of an R-module. -/
def moduleSystem (a : Fin 4 → R) :
    RestrictionSystem R (ModuleAt M a) where
  res h := moduleRestriction M a h
  res_id s := moduleRestriction_self M a s
  res_comp hst htu := by
    apply LinearMap.ext
    intro x
    exact moduleRestriction_comp M a hst htu x

/-- The same actual diagram after adjoining one fixed principal open to
every overlap. -/
def localizedSystem (a : Fin 4 → R) (i : Fin 4) :
    RestrictionSystem R (fun s : Finset (Fin 4) => ModuleAt M a (insert i s)) where
  res h := moduleRestriction M a (Finset.insert_subset_insert i h)
  res_id s := moduleRestriction_self M a (insert i s)
  res_comp hst htu := by
    apply LinearMap.ext
    intro x
    exact moduleRestriction_comp M a
      (Finset.insert_subset_insert i hst) (Finset.insert_subset_insert i htu) x

def localizationMorphism (a : Fin 4 → R) (i : Fin 4) :
    SystemMorphism (moduleSystem M a) (localizedSystem M a i) where
  app s := moduleRestriction M a (s := s) (t := insert i s) (by simp)
  naturality hst := by
    apply LinearMap.ext
    intro x
    exact (moduleRestriction_comp M a hst (by simp) x).trans
      (moduleRestriction_comp M a (by simp) (Finset.insert_subset_insert i hst) x).symm

/-- The repeated pivot is an actual identity restriction. -/
theorem localizedSystem_pivot (a : Fin 4 → R) (i : Fin 4)
    (s : Finset (Fin 4)) :
    Function.Bijective ((localizedSystem M a i).res
      (s := s) (t := insert i s) (by simp)) := by
  exact moduleRestriction_bijective_of_eq M a
    (Finset.insert_subset_insert i (by simp)) (Finset.insert_idem i s).symm

/-- Every one-cocycle of actual module localizations on an affine
four-element principal cover has actual local primitives. -/
theorem affine_firstCech_exact (a : Fin 4 → R)
    (ha : Ideal.span (Set.range a) = ⊤) :
    Function.Exact (d0 (moduleSystem M a)) (d1 (moduleSystem M a)) := by
  letI (i : Fin 4) (s : Finset (Fin 4)) :
      IsLocalizedModule (Submonoid.powers (a i)) ((localizationMorphism M a i).app s) :=
    moduleRestriction_insert_isLocalized M a i s
  exact first_exact_of_unit_span (moduleSystem M a) a ha
    (fun i s => ModuleAt M a (insert i s)) (localizedSystem M a)
    (localizationMorphism M a) (localizedSystem_pivot M a)

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V W : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]
variable [∀ s, AddCommGroup (W s)] [∀ s, Module R (W s)]

namespace SystemMorphism

variable {D : RestrictionSystem R V} {E : RestrictionSystem R W}

@[simp] theorem map0_augmentation (f : SystemMorphism D E) (x : V ∅) :
    f.map0 (augmentation D x) = augmentation E (f.app ∅ x) := by
  ext <;> dsimp [map0, augmentation]
  all_goals simp only [app_res]

variable (S : Submonoid R) (f : SystemMorphism D E)
variable [∀ s, IsLocalizedModule S (f.app s)]

theorem localized_augmentation :
    IsLocalizedModule.map S (f.app ∅) f.map0 (augmentation D) = augmentation E := by
  apply IsLocalizedModule.linearMap_ext S (f.app ∅) f.map0
  rw [IsLocalizedModule.map_comp]
  exact LinearMap.ext f.map0_augmentation

include f in
theorem localized_zero_exact_iff :
    Function.Exact
      (LocalizedModule.map S (augmentation D)) (LocalizedModule.map S (d0 D)) ↔
      Function.Exact (augmentation E) (d0 E) := by
  rw [← f.localized_augmentation S, ← f.localized_d0 S]
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (IsLocalizedModule.map_iso_commute S (f.app ∅) f.map0 (augmentation D))
    (IsLocalizedModule.map_iso_commute S f.map0 f.map1 (d0 D))).symm

end SystemMorphism

section UnitSpan

variable (D : RestrictionSystem R V) (a : Fin 4 → R)
variable (ha : Ideal.span (Set.range a) = ⊤)
variable (W : Fin 4 → Finset (Fin 4) → Type*)
variable [∀ i s, AddCommGroup (W i s)] [∀ i s, Module R (W i s)]
variable (E : ∀ i, RestrictionSystem R (W i))
variable (f : ∀ i, SystemMorphism D (E i))
variable [∀ i s, IsLocalizedModule (Submonoid.powers (a i)) ((f i).app s)]
variable (hpivot : ∀ (i : Fin 4) (s : Finset (Fin 4)),
  Function.Bijective ((E i).res (s := s) (t := insert i s) (by simp)))

include ha f hpivot in
theorem zero_exact_of_unit_span : Function.Exact (augmentation D) (d0 D) := by
  apply CycleQ2GeometricLocalizedCech.exact_of_unit_span a ha (augmentation D) (d0 D)
  intro i
  apply ((f i).localized_zero_exact_iff (Submonoid.powers (a i))).mpr
  exact zero_exact_of_pivot (E i) i (hpivot i)

include ha f hpivot in
theorem augmentation_injective_of_unit_span : Function.Injective (augmentation D) := by
  apply injective_of_localized_span (Set.range a) ha (augmentation D)
  rintro ⟨r,⟨i,rfl⟩⟩
  let S := Submonoid.powers (a i)
  let e0 := IsLocalizedModule.iso S ((f i).app ∅)
  let e1 := IsLocalizedModule.iso S (f i).map0
  have hh := IsLocalizedModule.map_iso_commute S ((f i).app ∅) (f i).map0 (augmentation D)
  rw [(f i).localized_augmentation S] at hh
  intro x y hxy
  apply e0.injective
  apply augmentation_injective_of_pivot (E i) i (hpivot i)
  exact (LinearMap.congr_fun hh x).trans
    ((congrArg e1 hxy).trans (LinearMap.congr_fun hh y).symm)

end UnitSpan

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricLocalizedCech

open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Actual matching localized sections on an affine cover glue uniquely. -/
theorem affine_existsUnique_gluing (a : Fin 4 → R)
    (ha : Ideal.span (Set.range a) = ⊤) (p : ZeroCochain (ModuleAt M a))
    (hp : d0 (moduleSystem M a) p = 0) :
    ∃! x : ModuleAt M a ∅, augmentation (moduleSystem M a) x = p := by
  letI (i : Fin 4) (s : Finset (Fin 4)) :
      IsLocalizedModule (Submonoid.powers (a i)) ((localizationMorphism M a i).app s) :=
    moduleRestriction_insert_isLocalized M a i s
  have he := zero_exact_of_unit_span (moduleSystem M a) a ha
    (fun i s => ModuleAt M a (insert i s)) (localizedSystem M a)
    (localizationMorphism M a) (localizedSystem_pivot M a)
  have hi := augmentation_injective_of_unit_span (moduleSystem M a) a ha
    (fun i s => ModuleAt M a (insert i s)) (localizedSystem M a)
    (localizationMorphism M a) (localizedSystem_pivot M a)
  obtain ⟨x,hx⟩ := (he p).mp hp
  exact ⟨x,hx,fun y hy => hi (hy.trans hx.symm)⟩

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricFourOpenCech

section CoverDescent

variable {R : Type*} [CommRing R]
variable {A0 A1 A2 C0 C1 C2 B00 B10 B20 B01 B11 B02 : Type*}
variable [AddCommGroup A0] [AddCommGroup A1] [AddCommGroup A2]
variable [AddCommGroup C0] [AddCommGroup C1] [AddCommGroup C2]
variable [AddCommGroup B00] [AddCommGroup B10] [AddCommGroup B20]
variable [AddCommGroup B01] [AddCommGroup B11] [AddCommGroup B02]
variable [Module R A0] [Module R A1] [Module R A2]
variable [Module R C0] [Module R C1] [Module R C2]
variable [Module R B00] [Module R B10] [Module R B20]
variable [Module R B01] [Module R B11] [Module R B02]

/-- The elementary change-of-cover argument in degree one. The rows and
columns are actual cochains on the common refinement. Local affine
exactness, gluing, uniqueness, and exactness on the second cover yield
actual primitives on the first cover by a proved double-complex chase. -/
theorem first_exact_of_cover_descent
    (dA0 : A0 →ₗ[R] A1) (dA1 : A1 →ₗ[R] A2)
    (dC0 : C0 →ₗ[R] C1) (dC1 : C1 →ₗ[R] C2)
    (u0 : A0 →ₗ[R] B00) (u1 : A1 →ₗ[R] B10) (u2 : A2 →ₗ[R] B20)
    (i0 : C0 →ₗ[R] B00) (i1 : C1 →ₗ[R] B01) (i2 : C2 →ₗ[R] B02)
    (h00 : B00 →ₗ[R] B10) (h10 : B10 →ₗ[R] B20)
    (h01 : B01 →ₗ[R] B11)
    (v00 : B00 →ₗ[R] B01) (v10 : B10 →ₗ[R] B11) (v01 : B01 →ₗ[R] B02)
    (hA : ∀ x, dA1 (dA0 x) = 0)
    (hu0 : ∀ x, u1 (dA0 x) = h00 (u0 x))
    (hu1 : ∀ x, h10 (u1 x) = u2 (dA1 x))
    (hi0 : ∀ x, v00 (i0 x) = i1 (dC0 x))
    (hi1 : ∀ x, v01 (i1 x) = i2 (dC1 x))
    (hcomm : ∀ x, h01 (v00 x) = v10 (h00 x))
    (huv : ∀ x, v10 (u1 x) = 0)
    (hih : ∀ x, h00 (i0 x) = 0)
    (hvv : ∀ x, v01 (v00 x) = 0)
    (hrow : Function.Exact h00 h10)
    (hglueLeft : Function.Exact i1 h01)
    (huniqueLeft : Function.Injective i2)
    (hcoordinate : Function.Exact dC0 dC1)
    (hglueRight : Function.Exact u0 v00)
    (huniqueRight : Function.Injective u1) :
    Function.Exact dA0 dA1 := by
  intro p
  constructor
  · intro hp
    have hp' : h10 (u1 p) = 0 := by rw [hu1, hp, map_zero]
    obtain ⟨q,hq⟩ := (hrow (u1 p)).mp hp'
    have hq' : h01 (v00 q) = 0 := by rw [hcomm, hq, huv]
    obtain ⟨t,ht⟩ := (hglueLeft (v00 q)).mp hq'
    have ht' : dC1 t = 0 := by
      apply huniqueLeft
      rw [map_zero, ← hi1, ht, hvv]
    obtain ⟨z,hz⟩ := (hcoordinate t).mp ht'
    have hqz : v00 (q - i0 z) = 0 := by
      rw [map_sub, hi0, hz, ht, sub_self]
    obtain ⟨a,ha⟩ := (hglueRight (q - i0 z)).mp hqz
    refine ⟨a,huniqueRight ?_⟩
    rw [hu0, ha, map_sub, hih, sub_zero, hq]
  · rintro ⟨a,rfl⟩
    exact hA a

end CoverDescent

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]

/-- The actual restriction diagrams on a common refinement, with their
proved interchange law. The two directions retain their original maps. -/
structure BiSystem (V : Finset (Fin 4) → Finset (Fin 4) → Type*)
    [∀ s t, AddCommGroup (V s t)] [∀ s t, Module R (V s t)] where
  left (t : Finset (Fin 4)) : RestrictionSystem R (fun s => V s t)
  right (s : Finset (Fin 4)) : RestrictionSystem R (V s)
  interchange {s s' t t' : Finset (Fin 4)} (hs : s ⊆ s') (ht : t ⊆ t')
    (x : V s t) :
    (left t').res hs ((right s).res ht x) =
      (right s').res ht ((left t).res hs x)

namespace BiSystem

variable {V : Finset (Fin 4) → Finset (Fin 4) → Type*}
variable [∀ s t, AddCommGroup (V s t)] [∀ s t, Module R (V s t)]
variable (D : BiSystem (R := R) V)

def horizontalMorphism {s s' : Finset (Fin 4)} (hs : s ⊆ s') :
    SystemMorphism (D.right s) (D.right s') where
  app t := (D.left t).res hs
  naturality ht := by
    ext x
    exact D.interchange hs ht x

def row0 : RestrictionSystem R (fun s => ZeroCochain (V s)) where
  res hs := (D.horizontalMorphism hs).map0
  res_id s := by
    apply LinearMap.ext
    intro x
    ext <;> dsimp [SystemMorphism.map0, horizontalMorphism]
    all_goals simp only [RestrictionSystem.res_id, LinearMap.id_apply]
  res_comp hs ht := by
    apply LinearMap.ext
    intro x
    ext <;> dsimp [SystemMorphism.map0, horizontalMorphism]
    all_goals exact RestrictionSystem.res_res _ _ _ _

def row1 : RestrictionSystem R (fun s => OneCochain (V s)) where
  res hs := (D.horizontalMorphism hs).map1
  res_id s := by
    apply LinearMap.ext
    intro x
    ext <;> dsimp [SystemMorphism.map1, horizontalMorphism]
    all_goals simp only [RestrictionSystem.res_id, LinearMap.id_apply]
  res_comp hs ht := by
    apply LinearMap.ext
    intro x
    ext <;> dsimp [SystemMorphism.map1, horizontalMorphism]
    all_goals exact RestrictionSystem.res_res _ _ _ _

def row2 : RestrictionSystem R (fun s => TwoCochain (V s)) where
  res hs := (D.horizontalMorphism hs).map2
  res_id s := by
    apply LinearMap.ext
    intro x
    ext <;> dsimp [SystemMorphism.map2, horizontalMorphism]
    all_goals simp only [RestrictionSystem.res_id, LinearMap.id_apply]
  res_comp hs ht := by
    apply LinearMap.ext
    intro x
    ext <;> dsimp [SystemMorphism.map2, horizontalMorphism]
    all_goals exact RestrictionSystem.res_res _ _ _ _

def horizontalAugmentation : SystemMorphism (D.left ∅) D.row0 where
  app s := augmentation (D.right s)
  naturality hs := by
    apply LinearMap.ext
    intro x
    exact ((D.horizontalMorphism hs).map0_augmentation x).symm

def vertical0 : SystemMorphism D.row0 D.row1 where
  app s := d0 (D.right s)
  naturality hs := by
    apply LinearMap.ext
    intro x
    exact ((D.horizontalMorphism hs).map1_d0 x).symm

def vertical1 : SystemMorphism D.row1 D.row2 where
  app s := d1 (D.right s)
  naturality hs := by
    apply LinearMap.ext
    intro x
    exact ((D.horizontalMorphism hs).map2_d1 x).symm

end BiSystem

section ProductExact

variable {M₀ M₁ M₂ N₀ N₁ N₂ : Type*}
variable [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
variable [AddCommGroup N₀] [AddCommGroup N₁] [AddCommGroup N₂]
variable [Module R M₀] [Module R M₁] [Module R M₂]
variable [Module R N₀] [Module R N₁] [Module R N₂]

theorem exact_prod {f : M₀ →ₗ[R] M₁} {g : M₁ →ₗ[R] M₂}
    {f' : N₀ →ₗ[R] N₁} {g' : N₁ →ₗ[R] N₂}
    (h : Function.Exact f g) (h' : Function.Exact f' g') :
    Function.Exact (f.prodMap f') (g.prodMap g') := by
  intro p
  constructor
  · intro hp
    obtain ⟨x,hx⟩ := (h p.1).mp (congrArg Prod.fst hp)
    obtain ⟨y,hy⟩ := (h' p.2).mp (congrArg Prod.snd hp)
    exact ⟨(x,y),Prod.ext hx hy⟩
  · rintro ⟨p,rfl⟩
    exact Prod.ext ((h (f p.1)).mpr ⟨p.1,rfl⟩)
      ((h' (f' p.2)).mpr ⟨p.2,rfl⟩)

theorem injective_prod {f : M₀ →ₗ[R] M₁} {g : N₀ →ₗ[R] N₁}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (f.prodMap g) := by
  intro x y h
  exact Prod.ext (hf (congrArg Prod.fst h)) (hg (congrArg Prod.snd h))

end ProductExact

namespace BiSystem

variable {V : Finset (Fin 4) → Finset (Fin 4) → Type*}
variable [∀ s t, AddCommGroup (V s t)] [∀ s t, Module R (V s t)]
variable (D : BiSystem (R := R) V)

/-- Degree-one row exactness is the finite product of the genuine
exact complexes on the four opens of the second cover. -/
theorem row0_first_exact
    (h : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (d0 (D.left t)) (d1 (D.left t))) :
    Function.Exact (d0 D.row0) (d1 D.row0) := by
  intro p
  constructor
  · intro hp
    have h0 : d1 (D.left {0}) ((p.1.1.1.1, p.1.2.1.1.1, p.1.2.2.1.1), (p.2.1.1.1, p.2.2.1.1.1, p.2.2.2.1.1)) = 0 :=
      congrArg (fun z : TwoCochain (fun s => ZeroCochain (V s)) => ((z.1.1.1.1, z.1.2.1.1), (z.2.1.1.1, z.2.2.1.1))) hp
    obtain ⟨q0,hq0⟩ := (h {0} (by simp) ((p.1.1.1.1, p.1.2.1.1.1, p.1.2.2.1.1), (p.2.1.1.1, p.2.2.1.1.1, p.2.2.2.1.1))).mp h0
    have h1 : d1 (D.left {1}) ((p.1.1.1.2, p.1.2.1.1.2, p.1.2.2.1.2), (p.2.1.1.2, p.2.2.1.1.2, p.2.2.2.1.2)) = 0 :=
      congrArg (fun z : TwoCochain (fun s => ZeroCochain (V s)) => ((z.1.1.1.2, z.1.2.1.2), (z.2.1.1.2, z.2.2.1.2))) hp
    obtain ⟨q1,hq1⟩ := (h {1} (by simp) ((p.1.1.1.2, p.1.2.1.1.2, p.1.2.2.1.2), (p.2.1.1.2, p.2.2.1.1.2, p.2.2.2.1.2))).mp h1
    have h2 : d1 (D.left {2}) ((p.1.1.2.1, p.1.2.1.2.1, p.1.2.2.2.1), (p.2.1.2.1, p.2.2.1.2.1, p.2.2.2.2.1)) = 0 :=
      congrArg (fun z : TwoCochain (fun s => ZeroCochain (V s)) => ((z.1.1.2.1, z.1.2.2.1), (z.2.1.2.1, z.2.2.2.1))) hp
    obtain ⟨q2,hq2⟩ := (h {2} (by simp) ((p.1.1.2.1, p.1.2.1.2.1, p.1.2.2.2.1), (p.2.1.2.1, p.2.2.1.2.1, p.2.2.2.2.1))).mp h2
    have h3 : d1 (D.left {3}) ((p.1.1.2.2, p.1.2.1.2.2, p.1.2.2.2.2), (p.2.1.2.2, p.2.2.1.2.2, p.2.2.2.2.2)) = 0 :=
      congrArg (fun z : TwoCochain (fun s => ZeroCochain (V s)) => ((z.1.1.2.2, z.1.2.2.2), (z.2.1.2.2, z.2.2.2.2))) hp
    obtain ⟨q3,hq3⟩ := (h {3} (by simp) ((p.1.1.2.2, p.1.2.1.2.2, p.1.2.2.2.2), (p.2.1.2.2, p.2.2.1.2.2, p.2.2.2.2.2))).mp h3
    refine ⟨((((q0.1.1, q1.1.1), (q2.1.1, q3.1.1)), ((q0.1.2, q1.1.2), (q2.1.2, q3.1.2))), (((q0.2.1, q1.2.1), (q2.2.1, q3.2.1)), ((q0.2.2, q1.2.2), (q2.2.2, q3.2.2)))), ?_⟩
    exact (Prod.ext (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0} ) => z.1.1) hq0) (congrArg (fun z : OneCochain (fun s => V s {1} ) => z.1.1) hq1)) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {2} ) => z.1.1) hq2) (congrArg (fun z : OneCochain (fun s => V s {3} ) => z.1.1) hq3))) (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0} ) => z.1.2.1) hq0) (congrArg (fun z : OneCochain (fun s => V s {1} ) => z.1.2.1) hq1)) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {2} ) => z.1.2.1) hq2) (congrArg (fun z : OneCochain (fun s => V s {3} ) => z.1.2.1) hq3))) (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0} ) => z.1.2.2) hq0) (congrArg (fun z : OneCochain (fun s => V s {1} ) => z.1.2.2) hq1)) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {2} ) => z.1.2.2) hq2) (congrArg (fun z : OneCochain (fun s => V s {3} ) => z.1.2.2) hq3))))) (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0} ) => z.2.1) hq0) (congrArg (fun z : OneCochain (fun s => V s {1} ) => z.2.1) hq1)) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {2} ) => z.2.1) hq2) (congrArg (fun z : OneCochain (fun s => V s {3} ) => z.2.1) hq3))) (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0} ) => z.2.2.1) hq0) (congrArg (fun z : OneCochain (fun s => V s {1} ) => z.2.2.1) hq1)) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {2} ) => z.2.2.1) hq2) (congrArg (fun z : OneCochain (fun s => V s {3} ) => z.2.2.1) hq3))) (Prod.ext (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {0} ) => z.2.2.2) hq0) (congrArg (fun z : OneCochain (fun s => V s {1} ) => z.2.2.2) hq1)) (Prod.ext (congrArg (fun z : OneCochain (fun s => V s {2} ) => z.2.2.2) hq2) (congrArg (fun z : OneCochain (fun s => V s {3} ) => z.2.2.2) hq3))))))
  · rintro ⟨q,rfl⟩
    exact d1_d0 D.row0 q

/-- Matching degree-one columns glue by the actual affine gluing in
each overlap of the second cover. -/
theorem row1_zero_exact
    (h : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (augmentation (D.left t)) (d0 (D.left t))) :
    Function.Exact (augmentation D.row1) (d0 D.row1) := by
  intro p
  constructor
  · intro hp
    have h0 : d0 (D.left {0,1}) ((p.1.1.1.1, p.1.2.1.1), (p.2.1.1.1, p.2.2.1.1)) = 0 :=
      congrArg (fun z : OneCochain (fun s => OneCochain (V s)) => ((z.1.1.1.1, z.1.2.1.1.1, z.1.2.2.1.1), (z.2.1.1.1, z.2.2.1.1.1, z.2.2.2.1.1))) hp
    obtain ⟨q0,hq0⟩ := (h {0,1} (by simp) ((p.1.1.1.1, p.1.2.1.1), (p.2.1.1.1, p.2.2.1.1))).mp h0
    have h1 : d0 (D.left {0,2}) ((p.1.1.1.2.1, p.1.2.1.2.1), (p.2.1.1.2.1, p.2.2.1.2.1)) = 0 :=
      congrArg (fun z : OneCochain (fun s => OneCochain (V s)) => ((z.1.1.1.2.1, z.1.2.1.1.2.1, z.1.2.2.1.2.1), (z.2.1.1.2.1, z.2.2.1.1.2.1, z.2.2.2.1.2.1))) hp
    obtain ⟨q1,hq1⟩ := (h {0,2} (by simp) ((p.1.1.1.2.1, p.1.2.1.2.1), (p.2.1.1.2.1, p.2.2.1.2.1))).mp h1
    have h2 : d0 (D.left {0,3}) ((p.1.1.1.2.2, p.1.2.1.2.2), (p.2.1.1.2.2, p.2.2.1.2.2)) = 0 :=
      congrArg (fun z : OneCochain (fun s => OneCochain (V s)) => ((z.1.1.1.2.2, z.1.2.1.1.2.2, z.1.2.2.1.2.2), (z.2.1.1.2.2, z.2.2.1.1.2.2, z.2.2.2.1.2.2))) hp
    obtain ⟨q2,hq2⟩ := (h {0,3} (by simp) ((p.1.1.1.2.2, p.1.2.1.2.2), (p.2.1.1.2.2, p.2.2.1.2.2))).mp h2
    have h3 : d0 (D.left {1,2}) ((p.1.1.2.1, p.1.2.2.1), (p.2.1.2.1, p.2.2.2.1)) = 0 :=
      congrArg (fun z : OneCochain (fun s => OneCochain (V s)) => ((z.1.1.2.1, z.1.2.1.2.1, z.1.2.2.2.1), (z.2.1.2.1, z.2.2.1.2.1, z.2.2.2.2.1))) hp
    obtain ⟨q3,hq3⟩ := (h {1,2} (by simp) ((p.1.1.2.1, p.1.2.2.1), (p.2.1.2.1, p.2.2.2.1))).mp h3
    have h4 : d0 (D.left {1,3}) ((p.1.1.2.2.1, p.1.2.2.2.1), (p.2.1.2.2.1, p.2.2.2.2.1)) = 0 :=
      congrArg (fun z : OneCochain (fun s => OneCochain (V s)) => ((z.1.1.2.2.1, z.1.2.1.2.2.1, z.1.2.2.2.2.1), (z.2.1.2.2.1, z.2.2.1.2.2.1, z.2.2.2.2.2.1))) hp
    obtain ⟨q4,hq4⟩ := (h {1,3} (by simp) ((p.1.1.2.2.1, p.1.2.2.2.1), (p.2.1.2.2.1, p.2.2.2.2.1))).mp h4
    have h5 : d0 (D.left {2,3}) ((p.1.1.2.2.2, p.1.2.2.2.2), (p.2.1.2.2.2, p.2.2.2.2.2)) = 0 :=
      congrArg (fun z : OneCochain (fun s => OneCochain (V s)) => ((z.1.1.2.2.2, z.1.2.1.2.2.2, z.1.2.2.2.2.2), (z.2.1.2.2.2, z.2.2.1.2.2.2, z.2.2.2.2.2.2))) hp
    obtain ⟨q5,hq5⟩ := (h {2,3} (by simp) ((p.1.1.2.2.2, p.1.2.2.2.2), (p.2.1.2.2.2, p.2.2.2.2.2))).mp h5
    refine ⟨((q0, q1, q2), (q3, q4, q5)), ?_⟩
    exact (Prod.ext (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,1} ) => z.1.1) hq0) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,2} ) => z.1.1) hq1) (congrArg (fun z : ZeroCochain (fun s => V s {0,3} ) => z.1.1) hq2))) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {1,2} ) => z.1.1) hq3) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {1,3} ) => z.1.1) hq4) (congrArg (fun z : ZeroCochain (fun s => V s {2,3} ) => z.1.1) hq5)))) (Prod.ext (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,1} ) => z.1.2) hq0) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,2} ) => z.1.2) hq1) (congrArg (fun z : ZeroCochain (fun s => V s {0,3} ) => z.1.2) hq2))) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {1,2} ) => z.1.2) hq3) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {1,3} ) => z.1.2) hq4) (congrArg (fun z : ZeroCochain (fun s => V s {2,3} ) => z.1.2) hq5))))) (Prod.ext (Prod.ext (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,1} ) => z.2.1) hq0) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,2} ) => z.2.1) hq1) (congrArg (fun z : ZeroCochain (fun s => V s {0,3} ) => z.2.1) hq2))) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {1,2} ) => z.2.1) hq3) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {1,3} ) => z.2.1) hq4) (congrArg (fun z : ZeroCochain (fun s => V s {2,3} ) => z.2.1) hq5)))) (Prod.ext (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,1} ) => z.2.2) hq0) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {0,2} ) => z.2.2) hq1) (congrArg (fun z : ZeroCochain (fun s => V s {0,3} ) => z.2.2) hq2))) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {1,2} ) => z.2.2) hq3) (Prod.ext (congrArg (fun z : ZeroCochain (fun s => V s {1,3} ) => z.2.2) hq4) (congrArg (fun z : ZeroCochain (fun s => V s {2,3} ) => z.2.2) hq5))))))
  · rintro ⟨q,rfl⟩
    exact d0_augmentation D.row1 q

/-- Uniqueness on the second-cover triple overlaps is preserved by the
actual common-refinement augmentation. -/
theorem row2_augmentation_injective
    (h : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Injective (augmentation (D.left t))) :
    Function.Injective (augmentation D.row2) := by
  intro x y hxy
  exact (Prod.ext (Prod.ext (h {0,1,2} (by simp) (congrArg (fun z : ZeroCochain (fun s => TwoCochain (V s)) => ((z.1.1.1.1, z.1.2.1.1), (z.2.1.1.1, z.2.2.1.1))) hxy)) (h {0,1,3} (by simp) (congrArg (fun z : ZeroCochain (fun s => TwoCochain (V s)) => ((z.1.1.1.2, z.1.2.1.2), (z.2.1.1.2, z.2.2.1.2))) hxy))) (Prod.ext (h {0,2,3} (by simp) (congrArg (fun z : ZeroCochain (fun s => TwoCochain (V s)) => ((z.1.1.2.1, z.1.2.2.1), (z.2.1.2.1, z.2.2.2.1))) hxy)) (h {1,2,3} (by simp) (congrArg (fun z : ZeroCochain (fun s => TwoCochain (V s)) => ((z.1.1.2.2, z.1.2.2.2), (z.2.1.2.2, z.2.2.2.2))) hxy))))

/-- The first-cover sections glue along the actual second-cover diagram. -/
theorem horizontal_augmentation_exact
    (h : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Exact (augmentation (D.right s)) (d0 (D.right s))) :
    Function.Exact D.horizontalAugmentation.map0 D.vertical0.map0 := by
  exact exact_prod (exact_prod (h {0} (by simp)) (h {1} (by simp)))
    (exact_prod (h {2} (by simp)) (h {3} (by simp)))

theorem horizontal_augmentation_one_injective
    (h : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Injective (augmentation (D.right s))) :
    Function.Injective D.horizontalAugmentation.map1 := by
  exact injective_prod
    (injective_prod (h {0,1} (by simp))
      (injective_prod (h {0,2} (by simp)) (h {0,3} (by simp))))
    (injective_prod (h {1,2} (by simp))
      (injective_prod (h {1,3} (by simp)) (h {2,3} (by simp))))

/-- A change of four-element cover through actual common-refinement
restriction maps. Every local exactness and uniqueness assertion refers
only to a nonempty overlap. The global input is exactness on the second
cover, and the conclusion supplies primitives on the first cover. -/
theorem first_exact_of_bicover
    (hleft1 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (d0 (D.left t)) (d1 (D.left t)))
    (hleft0 : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Exact (augmentation (D.left t)) (d0 (D.left t)))
    (hleftinj : ∀ t : Finset (Fin 4), t.Nonempty →
      Function.Injective (augmentation (D.left t)))
    (hright0 : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Exact (augmentation (D.right s)) (d0 (D.right s)))
    (hrightinj : ∀ s : Finset (Fin 4), s.Nonempty →
      Function.Injective (augmentation (D.right s)))
    (hcoordinate : Function.Exact (d0 (D.right ∅)) (d1 (D.right ∅))) :
    Function.Exact (d0 (D.left ∅)) (d1 (D.left ∅)) := by
  refine first_exact_of_cover_descent
    (d0 (D.left ∅)) (d1 (D.left ∅))
    (d0 (D.right ∅)) (d1 (D.right ∅))
    D.horizontalAugmentation.map0 D.horizontalAugmentation.map1
    D.horizontalAugmentation.map2
    (augmentation D.row0) (augmentation D.row1) (augmentation D.row2)
    (d0 D.row0) (d1 D.row0) (d0 D.row1)
    D.vertical0.map0 D.vertical0.map1 D.vertical1.map0
    (d1_d0 (D.left ∅))
    D.horizontalAugmentation.map1_d0
    (fun x => (D.horizontalAugmentation.map2_d1 x).symm)
    D.vertical0.map0_augmentation D.vertical1.map0_augmentation
    (fun x => (D.vertical0.map1_d0 x).symm)
    ?_ (d0_augmentation D.row0) ?_
    (D.row0_first_exact hleft1) (D.row1_zero_exact hleft0)
    (D.row2_augmentation_injective hleftinj) hcoordinate
    (D.horizontal_augmentation_exact hright0)
    (D.horizontal_augmentation_one_injective hrightinj)
  · intro x
    exact Prod.ext
      (Prod.ext (d0_augmentation (D.right {0,1}) x.1.1)
        (Prod.ext (d0_augmentation (D.right {0,2}) x.1.2.1)
          (d0_augmentation (D.right {0,3}) x.1.2.2)))
      (Prod.ext (d0_augmentation (D.right {1,2}) x.2.1)
        (Prod.ext (d0_augmentation (D.right {1,3}) x.2.2.1)
          (d0_augmentation (D.right {2,3}) x.2.2.2)))
  · intro x
    exact Prod.ext
      (Prod.ext (d1_d0 (D.right {0}) x.1.1) (d1_d0 (D.right {1}) x.1.2))
      (Prod.ext (d1_d0 (D.right {2}) x.2.1) (d1_d0 (D.right {3}) x.2.2))

end BiSystem

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricLocalizedCech

open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]

/-- Actual localization of modules commutes with arbitrary scalar
extension. This is the tensor universal property, with no flatness or
projectivity hypothesis on the extension. -/
theorem isLocalizedModule_baseChange (S : Submonoid R)
    (T : Type*) [CommRing T] [Algebra R T]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid T S) (f.baseChange T) := by
  let g := TensorProduct.AlgebraTensorModule.rTensor R T f
  haveI : IsLocalizedModule S g := inferInstance
  let e0 := TensorProduct.comm R T M
  let e1 := TensorProduct.comm R N T
  haveI : IsLocalizedModule S (g.comp e0.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S g e0
  have he : e1.toLinearMap.comp (g.comp e0.toLinearMap) =
      (f.baseChange T).restrictScalars R := by
    ext t m <;> rfl
  haveI : IsLocalizedModule S ((f.baseChange T).restrictScalars R) := by
    rw [← he]
    exact IsLocalizedModule.of_linearEquiv S _ e1
  exact IsLocalizedModule.of_restrictScalars S (f.baseChange T)

theorem isLocalizedModule_baseChange_away (r : R)
    (T : Type*) [CommRing T] [Algebra R T]
    (f : M →ₗ[R] N) [IsLocalizedModule (Submonoid.powers r) f] :
    IsLocalizedModule (Submonoid.powers (algebraMap R T r)) (f.baseChange T) := by
  simpa only [Algebra.algebraMapSubmonoid_powers] using
    isLocalizedModule_baseChange (Submonoid.powers r) T f

theorem baseChange_bijective (T : Type*) [CommRing T] [Algebra R T]
    (f : M →ₗ[R] N) (hf : Function.Bijective f) :
    Function.Bijective (f.baseChange T) :=
  ((LinearEquiv.ofBijective f hf).baseChange R T M N).bijective

/-- A radical containment gives a genuine unit-ideal cover on every
nonempty overlap of the second cover. -/
theorem localized_cover_span_top (a b : Fin 4 → R)
    (hab : (Ideal.span (Set.range b)).radical ≤ (Ideal.span (Set.range a)).radical)
    (t : Finset (Fin 4)) (ht : t.Nonempty) :
    Ideal.span (Set.range (fun i => algebraMap R (RingAt b t) (a i))) = ⊤ := by
  obtain ⟨j,hj⟩ := ht
  have hb : b j ∈ (Ideal.span (Set.range a)).radical :=
    hab (Ideal.le_radical (Ideal.subset_span ⟨j,rfl⟩))
  obtain ⟨n,hn⟩ := (Ideal.mem_radical_iff).mp hb
  have hm := Ideal.mem_map_of_mem (algebraMap R (RingAt b t)) hn
  rw [Ideal.map_span, ← Set.range_comp'] at hm
  have hu : IsUnit (algebraMap R (RingAt b t) (b j)) :=
    IsLocalization.Away.isUnit_of_dvd (S := RingAt b t) (coverProduct b t)
      (Finset.dvd_prod_of_mem b hj)
  apply Ideal.eq_top_of_isUnit_mem (I :=
    Ideal.span (Set.range (fun i => algebraMap R (RingAt b t) (a i))))
      (by simpa only [map_pow, Function.comp_apply] using hm)
  exact hu.pow n

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricFourOpenCech

open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {V W : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]
variable [∀ s, AddCommGroup (W s)] [∀ s, Module R (W s)]

def baseChangedSystem (T : Type*) [CommRing T] [Algebra R T]
    (D : RestrictionSystem R V) : RestrictionSystem T (fun s => T ⊗[R] V s) where
  res h := (D.res h).baseChange T
  res_id s := by rw [D.res_id, LinearMap.baseChange_id]
  res_comp hs ht := by rw [← LinearMap.baseChange_comp, D.res_comp]

def SystemMorphism.baseChange (T : Type*) [CommRing T] [Algebra R T]
    {D : RestrictionSystem R V} {E : RestrictionSystem R W}
    (f : SystemMorphism D E) :
    SystemMorphism (baseChangedSystem T D) (baseChangedSystem T E) where
  app s := (f.app s).baseChange T
  naturality h := by
    change (f.app _).baseChange T ∘ₗ (D.res h).baseChange T =
      (E.res h).baseChange T ∘ₗ (f.app _).baseChange T
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, f.naturality]

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricLocalizedCech

open scoped TensorProduct
open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Actual module sections on a principal cover after scalar extension.
The cover need only generate the unit ideal on the extended base. This
applies to every genuine common-refinement row and column. -/
theorem baseChanged_affine_exact (T : Type*) [CommRing T] [Algebra R T]
    (a : Fin 4 → R)
    (ha : Ideal.span (Set.range (fun i => algebraMap R T (a i))) = ⊤) :
    Function.Exact (augmentation (baseChangedSystem T (moduleSystem M a)))
        (d0 (baseChangedSystem T (moduleSystem M a))) ∧
      Function.Injective (augmentation (baseChangedSystem T (moduleSystem M a))) ∧
      Function.Exact (d0 (baseChangedSystem T (moduleSystem M a)))
        (d1 (baseChangedSystem T (moduleSystem M a))) := by
  letI (i : Fin 4) (s : Finset (Fin 4)) :
      IsLocalizedModule (Submonoid.powers (a i)) ((localizationMorphism M a i).app s) :=
    moduleRestriction_insert_isLocalized M a i s
  letI (i : Fin 4) (s : Finset (Fin 4)) :
      IsLocalizedModule (Submonoid.powers (algebraMap R T (a i)))
        (((localizationMorphism M a i).baseChange T).app s) :=
    isLocalizedModule_baseChange_away (a i) T ((localizationMorphism M a i).app s)
  have hpivot (i : Fin 4) (s : Finset (Fin 4)) :
      Function.Bijective ((baseChangedSystem T (localizedSystem M a i)).res
        (s := s) (t := insert i s) (by simp)) :=
    baseChange_bijective T _ (localizedSystem_pivot M a i s)
  let a' : Fin 4 → T := fun i => algebraMap R T (a i)
  let W : Fin 4 → Finset (Fin 4) → Type _ :=
    fun i s => T ⊗[R] ModuleAt M a (insert i s)
  let E := fun i => baseChangedSystem T (localizedSystem M a i)
  let f := fun i => (localizationMorphism M a i).baseChange T
  exact ⟨zero_exact_of_unit_span (baseChangedSystem T (moduleSystem M a))
      a' ha W E f hpivot,
    augmentation_injective_of_unit_span (baseChangedSystem T (moduleSystem M a))
      a' ha W E f hpivot,
    first_exact_of_unit_span (baseChangedSystem T (moduleSystem M a))
      a' ha W E f hpivot⟩

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricFourOpenCech

section RestrictScalars

variable (R : Type*) [CommRing R]
variable {T : Type*} [CommRing T] [Algebra R T]
variable {V W : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)] [∀ s, Module T (V s)]
variable [∀ s, IsScalarTower R T (V s)]
variable [∀ s, AddCommGroup (W s)] [∀ s, Module R (W s)] [∀ s, Module T (W s)]
variable [∀ s, IsScalarTower R T (W s)]

def RestrictionSystem.restrictScalars (D : RestrictionSystem T V) :
    RestrictionSystem R V where
  res h := (D.res h).restrictScalars R
  res_id s := congrArg (LinearMap.restrictScalars R) (D.res_id s)
  res_comp hs ht := by
    apply LinearMap.ext
    intro x
    exact D.res_res hs ht x

@[simp] theorem d0_restrictScalars (D : RestrictionSystem T V) (x : ZeroCochain V) :
    d0 (D.restrictScalars R) x = d0 D x := rfl

@[simp] theorem d1_restrictScalars (D : RestrictionSystem T V) (x : OneCochain V) :
    d1 (D.restrictScalars R) x = d1 D x := rfl

@[simp] theorem augmentation_restrictScalars (D : RestrictionSystem T V) (x : V ∅) :
    augmentation (D.restrictScalars R) x = augmentation D x := rfl

def SystemMorphism.restrictScalars {D : RestrictionSystem T V}
    {E : RestrictionSystem T W} (f : SystemMorphism D E) :
    SystemMorphism (D.restrictScalars R) (E.restrictScalars R) where
  app s := (f.app s).restrictScalars R
  naturality h := by
    apply LinearMap.ext
    intro x
    exact f.app_res h x

end RestrictScalars

namespace SystemMorphism

variable {R : Type*} [CommRing R]
variable {V W : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]
variable [∀ s, AddCommGroup (W s)] [∀ s, Module R (W s)]
variable {D : RestrictionSystem R V} {E : RestrictionSystem R W}

private theorem prod_bijective {M N M' N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module R M] [Module R N] [Module R M'] [Module R N']
    (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (f.prodMap g) := by
  constructor
  · intro x y h
    exact Prod.ext (hf.1 (congrArg Prod.fst h)) (hg.1 (congrArg Prod.snd h))
  · intro y
    obtain ⟨x,hx⟩ := hf.2 y.1
    obtain ⟨x',hx'⟩ := hg.2 y.2
    exact ⟨(x,x'),Prod.ext hx hx'⟩

variable (f : SystemMorphism D E) (hf : ∀ s, Function.Bijective (f.app s))

include hf in
theorem map0_bijective : Function.Bijective f.map0 :=
  prod_bijective _ _ (prod_bijective _ _ (hf {0}) (hf {1}))
    (prod_bijective _ _ (hf {2}) (hf {3}))

include hf in
theorem map1_bijective : Function.Bijective f.map1 :=
  prod_bijective _ _
    (prod_bijective _ _ (hf {0,1}) (prod_bijective _ _ (hf {0,2}) (hf {0,3})))
    (prod_bijective _ _ (hf {1,2}) (prod_bijective _ _ (hf {1,3}) (hf {2,3})))

include hf in
theorem map2_bijective : Function.Bijective f.map2 :=
  prod_bijective _ _ (prod_bijective _ _ (hf {0,1,2}) (hf {0,1,3}))
    (prod_bijective _ _ (hf {0,2,3}) (hf {1,2,3}))

include f hf in
theorem first_exact_iff_of_bijective :
    Function.Exact (d0 D) (d1 D) ↔ Function.Exact (d0 E) (d1 E) := by
  let e0 := LinearEquiv.ofBijective f.map0 (f.map0_bijective hf)
  let e1 := LinearEquiv.ofBijective f.map1 (f.map1_bijective hf)
  let e2 := LinearEquiv.ofBijective f.map2 (f.map2_bijective hf)
  have h0 : (d0 E).comp e0.toLinearMap = e1.toLinearMap.comp (d0 D) :=
    LinearMap.ext (fun x => (f.map1_d0 x).symm)
  have h1 : (d1 E).comp e1.toLinearMap = e2.toLinearMap.comp (d1 D) :=
    LinearMap.ext (fun x => (f.map2_d1 x).symm)
  exact (Function.Exact.iff_of_ladder_linearEquiv h0 h1).symm

include f hf in
theorem zero_exact_iff_of_bijective :
    Function.Exact (augmentation D) (d0 D) ↔
      Function.Exact (augmentation E) (d0 E) := by
  let e := LinearEquiv.ofBijective (f.app ∅) (hf ∅)
  let e0 := LinearEquiv.ofBijective f.map0 (f.map0_bijective hf)
  let e1 := LinearEquiv.ofBijective f.map1 (f.map1_bijective hf)
  have h0 : (augmentation E).comp e.toLinearMap = e0.toLinearMap.comp (augmentation D) :=
    LinearMap.ext (fun x => (f.map0_augmentation x).symm)
  have h1 : (d0 E).comp e0.toLinearMap = e1.toLinearMap.comp (d0 D) :=
    LinearMap.ext (fun x => (f.map1_d0 x).symm)
  exact (Function.Exact.iff_of_ladder_linearEquiv h0 h1).symm

include f hf in
theorem augmentation_injective_iff_of_bijective :
    Function.Injective (augmentation D) ↔ Function.Injective (augmentation E) := by
  constructor
  · intro h x y hxy
    obtain ⟨x',rfl⟩ := (hf ∅).2 x
    obtain ⟨y',rfl⟩ := (hf ∅).2 y
    apply congrArg (f.app ∅)
    apply h
    apply (f.map0_bijective hf).1
    simpa only [map0_augmentation] using hxy
  · intro h x y hxy
    apply (hf ∅).1
    apply h
    rw [← f.map0_augmentation, ← f.map0_augmentation, hxy]

end SystemMorphism

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricLocalizedCech

open scoped TensorProduct
open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

/-- Sections on the actual common principal refinement, expressed as
successive tensor localizations. Both restriction directions are the
canonical tensor maps. -/
abbrev MixedModule (a b : Fin 4 → R) (s t : Finset (Fin 4)) :=
  RingAt b t ⊗[R] ModuleAt M a s

def mixedSystem (a b : Fin 4 → R) : BiSystem (R := R) (MixedModule M a b) where
  left t := (baseChangedSystem (RingAt b t) (moduleSystem M a)).restrictScalars R
  right s := moduleSystem (ModuleAt M a s) b
  interchange hs ht x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Swapping the two localization factors identifies the other direction
of the common refinement with actual scalar extension on its base open. -/
def mixedRightSwap (a b : Fin 4 → R) (s : Finset (Fin 4)) :
    SystemMorphism ((mixedSystem M a b).right s)
      ((baseChangedSystem (RingAt a s) (moduleSystem M b)).restrictScalars R) where
  app t := (TensorProduct.leftComm R (RingAt b t) (RingAt a s) M).toLinearMap
  naturality h := by
    ext z y m <;> rfl

theorem mixedLeft_exact (a b : Fin 4 → R)
    (hab : (Ideal.span (Set.range b)).radical ≤ (Ideal.span (Set.range a)).radical)
    (t : Finset (Fin 4)) (ht : t.Nonempty) :
    Function.Exact (augmentation ((mixedSystem M a b).left t))
        (d0 ((mixedSystem M a b).left t)) ∧
      Function.Injective (augmentation ((mixedSystem M a b).left t)) ∧
      Function.Exact (d0 ((mixedSystem M a b).left t))
        (d1 ((mixedSystem M a b).left t)) :=
  baseChanged_affine_exact M (RingAt b t) a (localized_cover_span_top a b hab t ht)

theorem mixedRight_gluing (a b : Fin 4 → R)
    (hab : (Ideal.span (Set.range a)).radical ≤ (Ideal.span (Set.range b)).radical)
    (s : Finset (Fin 4)) (hs : s.Nonempty) :
    Function.Exact (augmentation ((mixedSystem M a b).right s))
        (d0 ((mixedSystem M a b).right s)) ∧
      Function.Injective (augmentation ((mixedSystem M a b).right s)) := by
  let f := mixedRightSwap M a b s
  have hf (t : Finset (Fin 4)) : Function.Bijective (f.app t) :=
    (TensorProduct.leftComm R (RingAt b t) (RingAt a s) M).bijective
  have h := baseChanged_affine_exact M (RingAt a s) b
    (localized_cover_span_top b a hab s hs)
  exact ⟨(f.zero_exact_iff_of_bijective hf).mpr h.1,
    (f.augmentation_injective_iff_of_bijective hf).mpr h.2.1⟩

instance ringAt_empty_isAwayOne (a : Fin 4 → R) :
    IsLocalization.Away (1 : R) (RingAt a ∅) := by
  simpa only [coverProduct, Finset.prod_empty] using
    (inferInstance : IsLocalization.Away (coverProduct a ∅) (RingAt a ∅))

def emptyRingEquiv (a : Fin 4 → R) : RingAt a ∅ ≃ₐ[R] R :=
  (IsLocalization.atOne R (RingAt a ∅)).symm

def emptyModuleEquiv (a : Fin 4 → R) : ModuleAt M a ∅ ≃ₗ[R] M :=
  (TensorProduct.congr (emptyRingEquiv a).toLinearEquiv (LinearEquiv.refl R M)).trans
    (TensorProduct.lid R M)

@[simp] theorem emptyModuleEquiv_tmul (a : Fin 4 → R) (z : RingAt a ∅) (m : M) :
    emptyModuleEquiv M a (z ⊗ₜ[R] m) = emptyRingEquiv a z • m := rfl

/-- Removing the localization at the empty second index set recovers
the original first-cover sections, with their actual restrictions. -/
def mixedLeftEmpty (a b : Fin 4 → R) :
    SystemMorphism ((mixedSystem M a b).left ∅) (moduleSystem M a) where
  app s := (emptyModuleEquiv (ModuleAt M a s) b).toLinearMap
  naturality h := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z m =>
      change emptyRingEquiv b z • moduleRestriction M a h m =
        moduleRestriction M a h (emptyRingEquiv b z • m)
      exact (moduleRestriction M a h).map_smul _ _ |>.symm
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Removing the empty first localization similarly recovers the second
cover; the comparison is induced by the actual tensor equivalence. -/
def mixedRightEmpty (a b : Fin 4 → R) :
    SystemMorphism ((mixedSystem M a b).right ∅) (moduleSystem M b) where
  app t := (TensorProduct.congr (LinearEquiv.refl R (RingAt b t))
    (emptyModuleEquiv M a)).toLinearMap
  naturality h := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]

/-- Degree-one exactness is unchanged between the two actual principal
covers of the same punctured affine scheme. The proof constructs their
common localization refinement and uses proved affine gluing. The
second-cover exactness is transported by these explicit maps. -/
theorem first_exact_of_radical_eq (a b : Fin 4 → R)
    (hab : (Ideal.span (Set.range a)).radical = (Ideal.span (Set.range b)).radical)
    (hb : Function.Exact (d0 (moduleSystem M b)) (d1 (moduleSystem M b))) :
    Function.Exact (d0 (moduleSystem M a)) (d1 (moduleSystem M a)) := by
  let D := mixedSystem M a b
  let fL := mixedLeftEmpty M a b
  let fR := mixedRightEmpty M a b
  have hL (s : Finset (Fin 4)) : Function.Bijective (fL.app s) :=
    (emptyModuleEquiv (ModuleAt M a s) b).bijective
  have hR (t : Finset (Fin 4)) : Function.Bijective (fR.app t) :=
    (TensorProduct.congr (LinearEquiv.refl R (RingAt b t))
      (emptyModuleEquiv M a)).bijective
  have hc : Function.Exact (d0 (D.right ∅)) (d1 (D.right ∅)) :=
    (fR.first_exact_iff_of_bijective hR).mpr hb
  apply (fL.first_exact_iff_of_bijective hL).mp
  exact D.first_exact_of_bicover
    (fun t ht => (mixedLeft_exact M a b hab.ge t ht).2.2)
    (fun t ht => (mixedLeft_exact M a b hab.ge t ht).1)
    (fun t ht => (mixedLeft_exact M a b hab.ge t ht).2.1)
    (fun s hs => (mixedRight_gluing M a b hab.le s hs).1)
    (fun s hs => (mixedRight_gluing M a b hab.le s hs).2) hc

end CycleQ2GeometricLocalizedCech

namespace CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable {V : Finset (Fin 4) → Type*}
variable [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]

/-- The primitive assertion on the first three members of an actual
four-open restriction diagram, using its original section modules. -/
def FirstThreeExact (D : RestrictionSystem R V) : Prop :=
  ∀ (p01 : V {0,1}) (p02 : V {0,2}) (p12 : V {1,2}),
    D.res (show ({1,2} : Finset (Fin 4)) ⊆ {0,1,2} by decide) p12 -
      D.res (show ({0,2} : Finset (Fin 4)) ⊆ {0,1,2} by decide) p02 +
      D.res (show ({0,1} : Finset (Fin 4)) ⊆ {0,1,2} by decide) p01 = 0 →
    ∃ (q0 : V {0}) (q1 : V {1}) (q2 : V {2}),
      p01 = D.res (show ({1} : Finset (Fin 4)) ⊆ {0,1} by decide) q1 -
        D.res (show ({0} : Finset (Fin 4)) ⊆ {0,1} by decide) q0 ∧
      p02 = D.res (show ({2} : Finset (Fin 4)) ⊆ {0,2} by decide) q2 -
        D.res (show ({0} : Finset (Fin 4)) ⊆ {0,2} by decide) q0 ∧
      p12 = D.res (show ({2} : Finset (Fin 4)) ⊆ {1,2} by decide) q2 -
        D.res (show ({1} : Finset (Fin 4)) ⊆ {1,2} by decide) q1

/-- Adding an empty fourth open preserves the actual degree-one
exactness. Its overlaps are the zero section modules, not auxiliary
quotients or choices of trace representatives. -/
theorem first_exact_of_empty_fourth (D : RestrictionSystem R V)
    (hzero : ∀ s : Finset (Fin 4), 3 ∈ s → Subsingleton (V s))
    (hthree : FirstThreeExact D) : Function.Exact (d0 D) (d1 D) := by
  intro p
  constructor
  · intro hp
    have hc := congrArg (fun z : TwoCochain V => z.1.1) hp
    obtain ⟨q0,q1,q2,h01,h02,h12⟩ := hthree p.1.1 p.1.2.1 p.2.1 hc
    letI : Subsingleton (V {0,3}) := hzero {0,3} (by decide)
    letI : Subsingleton (V {1,3}) := hzero {1,3} (by decide)
    letI : Subsingleton (V {2,3}) := hzero {2,3} (by decide)
    exact ⟨((q0,q1),(q2,0)),
      Prod.ext (Prod.ext h01.symm (Prod.ext h02.symm (Subsingleton.elim _ _)))
        (Prod.ext h12.symm (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)))⟩
  · rintro ⟨q,rfl⟩
    exact d1_d0 D q

end CycleQ2GeometricFourOpenCech

namespace CycleQ2GeometricLocalizedCech

open CycleQ2GeometricFourOpenCech

variable {R : Type*} [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module R M]

theorem moduleAt_subsingleton_of_zero (a : Fin 4 → R) (j : Fin 4)
    (hj : a j = 0) (s : Finset (Fin 4)) (hs : j ∈ s) :
    Subsingleton (ModuleAt M a s) := by
  have hp : coverProduct a s = 0 := Finset.prod_eq_zero hs hj
  letI : Subsingleton (RingAt a s) :=
    IsLocalization.subsingleton (S := RingAt a s) (M := Submonoid.powers (coverProduct a s))
      ⟨1, by simp [hp]⟩
  exact Module.subsingleton (RingAt a s) (ModuleAt M a s)

theorem first_exact_of_zero_fourth (a : Fin 4 → R) (ha : a 3 = 0)
    (hthree : FirstThreeExact (moduleSystem M a)) :
    Function.Exact (d0 (moduleSystem M a)) (d1 (moduleSystem M a)) :=
  first_exact_of_empty_fourth (moduleSystem M a)
    (moduleAt_subsingleton_of_zero M a 3 ha) hthree

def withEmptyFourth (a : Fin 3 → R) : Fin 4 → R := ![a 0,a 1,a 2,0]

theorem withEmptyFourth_span (a : Fin 3 → R) :
    Ideal.span (Set.range (withEmptyFourth a)) = Ideal.span (Set.range a) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨i,rfl⟩
    fin_cases i
    · exact Ideal.subset_span ⟨0,rfl⟩
    · exact Ideal.subset_span ⟨1,rfl⟩
    · exact Ideal.subset_span ⟨2,rfl⟩
    · exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro x ⟨i,rfl⟩
    fin_cases i
    · exact Ideal.subset_span ⟨0,rfl⟩
    · exact Ideal.subset_span ⟨1,rfl⟩
    · exact Ideal.subset_span ⟨2,rfl⟩

end CycleQ2GeometricLocalizedCech

