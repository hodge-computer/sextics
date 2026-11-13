import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields
import HodgeComputer.Constructions.HoldoutCover.EvaluationMatrix
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.PolynomialFamilyBridge
import HodgeComputer.Constructions.HoldoutCover.PolynomialFieldMap
import HodgeComputer.Constructions.HoldoutCover.PolynomialNormal
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic

/-!
Target-independent algebra extracted from the accepted crossed-ternary proof
by GitHub contributor `1337isnot1337`. Original declarations and namespaces
are retained. The accepted application imports the maintained shared modules.

The source explanation credits fqlx's moving-conic/Fermat-cover construction,
Benjamin Diamond's maintained library extraction, the project contributors,
classical elliptic-curve/residue methods, Lean/mathlib, and OpenAI Codex.
This extraction was prepared with Codex assistance for fqlx.

This module supplies reusable steps; it asserts no new instance certificate.
-/

/- Source component: WeightedRadialEmbedding. -/
section

noncomputable section
namespace CrossedWeightedRadial
open MvPolynomial

/-- Exponents for x -> rho*x, y -> rho, S -> rho^2*S, T -> rho^2*T. -/
def exponentMap : (Fin 4 →₀ ℕ) →+ (Fin 4 →₀ ℕ) where
  toFun s := s+Finsupp.single 1 (s 0+2*s 2+2*s 3)
  map_zero' := by ext j; simp
  map_add' s t := by
    ext j
    simp only [Finsupp.add_apply,Finsupp.single_apply]
    split_ifs <;> omega

lemma exponentMap_injective : Function.Injective exponentMap := by
  intro s t h
  have h0 := congrArg (fun v : Fin 4 →₀ ℕ => v 0) h
  have h1 := congrArg (fun v : Fin 4 →₀ ℕ => v 1) h
  have h2 := congrArg (fun v : Fin 4 →₀ ℕ => v 2) h
  have h3 := congrArg (fun v : Fin 4 →₀ ℕ => v 3) h
  simp [exponentMap] at h0 h1 h2 h3
  have hs1 : s 1=t 1 := by omega
  ext j
  fin_cases j
  · exact h0
  · exact hs1
  · exact h2
  · exact h3

def monomialMap {R : Type*} [CommSemiring R] : MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) R :=
  AddMonoidAlgebra.mapDomainRingHom R exponentMap

lemma monomialMap_injective {R : Type*} [CommSemiring R] : Function.Injective (monomialMap (R:=R)) :=
  AddMonoidAlgebra.mapDomain_injective exponentMap_injective

lemma monomialMap_C {R : Type*} [CommSemiring R] (c : R) : monomialMap (C c)=C c := by
  simp [monomialMap,MvPolynomial.C,MvPolynomial.monomial,exponentMap]

lemma monomialMap_X {R : Type*} [CommSemiring R] (i : Fin 4) :
    monomialMap (X i : MvPolynomial (Fin 4) R)=![X 0*X 1,X 1,X 2*X 1^2,X 3*X 1^2] i := by
  change AddMonoidAlgebra.mapDomain exponentMap
    (AddMonoidAlgebra.single (Finsupp.single i 1) (1 : R))=_
  rw [AddMonoidAlgebra.mapDomain_single]
  fin_cases i <;>
    simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',MvPolynomial.X,
      MvPolynomial.monomial,AddMonoidAlgebra.lsingle_apply,AddMonoidAlgebra.single_mul_single,
      AddMonoidAlgebra.single_pow,one_mul,one_pow]
  all_goals congr 1
  all_goals ext j
  all_goals fin_cases j <;> simp [exponentMap]

end CrossedWeightedRadial
end
end

/- Source component: MonicHypersurfaceDerivations. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedMonicHypersurface
open Polynomial HoldoutConstruction
variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

omit [CharZero K] in
lemma derivative_finSuccEquiv (f : MvPolynomial (Fin (n+1)) K) :
    (MvPolynomial.finSuccEquiv K n f).derivative=
      MvPolynomial.finSuccEquiv K n (integerPartial 0 f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    rw [show MvPolynomial.finSuccEquiv K n (MvPolynomial.C c)=C (MvPolynomial.C c)
      from (MvPolynomial.finSuccEquiv K n).commutes c]
    rw [derivative_C,integerPartial_C,map_zero]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    have hx : (MvPolynomial.finSuccEquiv K n (MvPolynomial.X j)).derivative=
        MvPolynomial.finSuccEquiv K n (integerPartial 0 (MvPolynomial.X j)) := by
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [MvPolynomial.finSuccEquiv_X_zero,derivative_X,integerPartial_X_self,map_one]
      · simp only [MvPolynomial.finSuccEquiv_X_succ,derivative_C,
          integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j),map_zero]
    simp only [map_mul,derivative_mul,Derivation.leibniz,smul_eq_mul,map_add,hp,hx]
    ring

variable (p : Polynomial (MvPolynomial (Fin n) K))
variable [IsDomain (AdjoinRoot p)]
abbrev CoordinateRing := AdjoinRoot p
abbrev FunctionField := FractionRing (CoordinateRing p)

instance field_charZero : CharZero (FunctionField p) :=
  charZero_of_injective_ringHom (f:=algebraMap K (FunctionField p))
    (algebraMap K (FunctionField p)).injective

def equation : MvPolynomial (Fin (n+1)) K := (MvPolynomial.finSuccEquiv K n).symm p
def projection : MvPolynomial (Fin (n+1)) K →+* CoordinateRing p :=
  (AdjoinRoot.mk p).comp (MvPolynomial.finSuccEquiv K n).toRingHom
omit [CharZero K] [IsDomain (AdjoinRoot p)] in
lemma projection_surjective : Function.Surjective (projection p) :=
  (AdjoinRoot.mk_surjective (g:=p)).comp (MvPolynomial.finSuccEquiv K n).surjective

omit [CharZero K] [IsDomain (AdjoinRoot p)] in
lemma projection_kernel (f : MvPolynomial (Fin (n+1)) K) : projection p f=0 ↔ equation p ∣ f := by
  change AdjoinRoot.mk p (MvPolynomial.finSuccEquiv K n f)=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero,← map_dvd_iff (MvPolynomial.finSuccEquiv K n)]
  simp only [equation,AlgEquiv.apply_symm_apply]

def residueMap : MvPolynomial (Fin (n+1)) K →+* FunctionField p :=
  (algebraMap (CoordinateRing p) (FunctionField p)).comp (projection p)

omit [CharZero K] [IsDomain (AdjoinRoot p)] in
@[simp] lemma residueMap_C (c : K) : residueMap p (MvPolynomial.C c)=algebraMap K (FunctionField p) c := by
  change algebraMap (CoordinateRing p) (FunctionField p)
    (AdjoinRoot.mk p (MvPolynomial.finSuccEquiv K n (MvPolynomial.C c)))=_
  rw [show MvPolynomial.finSuccEquiv K n (MvPolynomial.C c)=C (MvPolynomial.C c)
    from (MvPolynomial.finSuccEquiv K n).commutes c]
  rfl

omit [CharZero K] [IsDomain (AdjoinRoot p)] in
@[simp] lemma residueMap_X_zero : residueMap p (MvPolynomial.X 0)=
    algebraMap (CoordinateRing p) (FunctionField p) (AdjoinRoot.root p) := by
  change algebraMap (CoordinateRing p) (FunctionField p)
    (AdjoinRoot.mk p (MvPolynomial.finSuccEquiv K n (MvPolynomial.X 0)))=_
  rw [MvPolynomial.finSuccEquiv_X_zero]
  rfl

omit [CharZero K] [IsDomain (AdjoinRoot p)] in
@[simp] lemma residueMap_X_succ (j : Fin n) : residueMap p (MvPolynomial.X j.succ)=
    algebraMap (CoordinateRing p) (FunctionField p) (AdjoinRoot.of p (MvPolynomial.X j)) := by
  change algebraMap (CoordinateRing p) (FunctionField p)
    (AdjoinRoot.mk p (MvPolynomial.finSuccEquiv K n (MvPolynomial.X j.succ)))=_
  rw [MvPolynomial.finSuccEquiv_X_succ]
  rfl

lemma residueMap_kernel (f : MvPolynomial (Fin (n+1)) K) : residueMap p f=0 ↔ equation p ∣ f :=
  residue_fractionMap_kernel (projection p) (equation p) (projection_kernel p) f

omit [IsDomain (AdjoinRoot p)] in
lemma normal_ne_zero (hp : p.Monic) (hi : Irreducible p) :
    residueMap p (integerPartial 0 (equation p))≠0 := by
  have hd : p.degree≠0 := ne_of_gt (hp.degree_pos_of_not_isUnit hi.not_isUnit)
  have hn : p.natDegree≠0 := by
    intro h
    apply hd
    rw [degree_eq_natDegree hp.ne_zero,h]
    rfl
  have hm := AdjoinRoot.mk_ne_zero_of_degree_lt hp
    (Polynomial.derivative_ne_zero.mpr hn) (degree_derivative_lt hp.ne_zero)
  have he : MvPolynomial.finSuccEquiv K n (integerPartial 0 (equation p))=p.derivative := by
    rw [← derivative_finSuccEquiv,equation,AlgEquiv.apply_symm_apply]
  change algebraMap (CoordinateRing p) (FunctionField p)
    (AdjoinRoot.mk p (MvPolynomial.finSuccEquiv K n (integerPartial 0 (equation p))))≠0
  rw [he]
  simpa only [map_zero] using (IsFractionRing.injective (CoordinateRing p) (FunctionField p)).ne hm

local instance : Algebra ℤ (FunctionField p) := Ring.toIntAlgebra _

def tangent (hp : p.Monic) (hi : Irreducible p) (i : Fin n) :
    Derivation ℤ (FunctionField p) (FunctionField p) :=
  residueTangent (K:=FunctionField p) (projection p) (projection_surjective p)
    (integerPartial 0) (integerPartial i.succ) (equation p) (projection_kernel p) (normal_ne_zero p hp hi)

lemma tangent_apply (hp : p.Monic) (hi : Irreducible p) (i : Fin n)
    (f : MvPolynomial (Fin (n+1)) K) :
    tangent p hp hi i (residueMap p f)=residueMap p (integerPartial i.succ f)-
      residueMap p (integerPartial i.succ (equation p))/residueMap p (integerPartial 0 (equation p))*
        residueMap p (integerPartial 0 f) :=
  residueTangent_apply (K:=FunctionField p) (projection p) (projection_surjective p)
    (integerPartial 0) (integerPartial i.succ) (equation p) (projection_kernel p) (normal_ne_zero p hp hi) f

@[simp] lemma tangent_constant (hp : p.Monic) (hi : Irreducible p) (i : Fin n) (c : K) :
    tangent p hp hi i (algebraMap K (FunctionField p) c)=0 := by
  rw [← residueMap_C,tangent_apply]
  simp only [integerPartial_C,map_zero,mul_zero,sub_self]

lemma tangent_parameter (hp : p.Monic) (hi : Irreducible p) (i j : Fin n) :
    tangent p hp hi i (residueMap p (MvPolynomial.X j.succ))=if j=i then 1 else 0 := by
  rw [tangent_apply,integerPartial_X_of_ne 0 j.succ (Fin.succ_ne_zero j)]
  simp only [map_zero,mul_zero,sub_zero]
  by_cases h : j=i
  · subst j; simp
  · have hs : j.succ≠i.succ := fun he => h (Fin.succ_injective _ he)
    simp [integerPartial_X_of_ne _ _ hs,h]

end CrossedMonicHypersurface
end
end

/- Source component: ImplicitIntertwining. -/
section

noncomputable section
namespace CrossedImplicitIntertwining
open HoldoutConstruction
open scoped BigOperators
variable {R K L : Type*} [CommRing R] [Field K] [Field L] {n : ℕ}

/-- On a hypersurface with nonzero normal partial, compatibility on constants
and the independent coordinates forces compatibility on the normal root. -/
lemma normal_coordinate_compatible
    (θ : MvPolynomial (Fin (n+1)) R →+* K) (φ : K →+* L)
    (f : MvPolynomial (Fin (n+1)) R) (hf : θ f=0)
    (hg : θ (MvPolynomial.pderiv 0 f)≠0)
    (D : Derivation ℤ K K) (E : Derivation ℤ L L)
    (hDC : ∀ r,D (θ (MvPolynomial.C r))=0)
    (hEC : ∀ r,E (φ (θ (MvPolynomial.C r)))=0)
    (hX : ∀ i : Fin n,E (φ (θ (MvPolynomial.X i.succ)))=
      φ (D (θ (MvPolynomial.X i.succ)))) :
    E (φ (θ (MvPolynomial.X 0)))=φ (D (θ (MvPolynomial.X 0))) := by
  have hd := derivation_polynomial_ringHom_chain D θ hDC f
  have he := derivation_polynomial_ringHom_chain E (φ.comp θ) hEC f
  rw [hf,map_zero] at hd
  have hf' : (φ.comp θ) f=0 := by simp [hf]
  rw [hf',map_zero] at he
  have hm := congrArg φ hd
  simp only [map_zero,map_sum,map_mul] at hm
  simp only [RingHom.comp_apply,Fin.sum_univ_succ,hX] at he hm
  apply mul_left_cancel₀ ((_root_.map_ne_zero φ).mpr hg)
  linear_combination hm-he

theorem quotient_fraction_intertwines
    {B : Type*} [CommRing B] [Algebra B K] [IsFractionRing B K]
    (π : MvPolynomial (Fin (n+1)) R →+* B) (hπ : Function.Surjective π)
    (φ : K →+* L) (f : MvPolynomial (Fin (n+1)) R)
    (hf : algebraMap B K (π f)=0)
    (hg : algebraMap B K (π (MvPolynomial.pderiv 0 f))≠0)
    (D : Derivation ℤ K K) (E : Derivation ℤ L L)
    (hDC : ∀ r,D (algebraMap B K (π (MvPolynomial.C r)))=0)
    (hEC : ∀ r,E (φ (algebraMap B K (π (MvPolynomial.C r))))=0)
    (hX : ∀ i : Fin n,E (φ (algebraMap B K (π (MvPolynomial.X i.succ))))=
      φ (D (algebraMap B K (π (MvPolynomial.X i.succ))))) :
    ∀ z : K,E (φ z)=φ (D z) := by
  apply derivation_intertwines_quotient_fraction π hπ φ D E
  · intro r
    rw [hDC,hEC,map_zero]
  · intro i
    refine Fin.cases ?_ (fun i => hX i) i
    exact normal_coordinate_compatible ((algebraMap B K).comp π) φ f hf hg D E hDC hEC hX

end CrossedImplicitIntertwining
end
end

/- Source component: OpenIncidence. -/
section

/- A second principal localization preserves a selected nonzero matrix minor
   in the square etale incidence. Uses fqlx's accepted generic incidence
   algebra and flat generic-fibre construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace CrossedOpenIncidence
open HoldoutConstruction
variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def openElement (equations : ι → MvPolynomial ι R) (g : MvPolynomial ι R) :
    SquareEtaleRing equations :=
  algebraMap (SquareSystemRing equations) (SquareEtaleRing equations) (Ideal.Quotient.mk _ g)

abbrev OpenSystemRing (equations : ι → MvPolynomial ι R) (g : MvPolynomial ι R) :=
  Localization.Away (openElement equations g)

instance open_etale (equations : ι → MvPolynomial ι R) (g : MvPolynomial ι R) :
    Algebra.Etale R (OpenSystemRing equations g) := by
  let : Algebra.Etale R (SquareEtaleRing equations) := square_system_jacobian_etale equations
  infer_instance

lemma etaleEval_polynomial {T : Type*} [CommRing T] [Algebra R T]
    (equations : ι → MvPolynomial ι R) (x : ι → T)
    (hx : ∀ i, MvPolynomial.aeval x (equations i)=0)
    (hj : IsUnit (Matrix.det (fun i j => MvPolynomial.aeval x
      (MvPolynomial.pderiv i (equations j))))) (g : MvPolynomial ι R) :
    squareSystemEtaleEval equations x hx hj (openElement equations g) =
      MvPolynomial.aeval x g := by
  simp only [openElement,squareSystemEtaleEval,IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq]
  rfl

lemma open_nontrivial {T : Type*} [CommRing T] [Nontrivial T] [Algebra R T]
    (equations : ι → MvPolynomial ι R) (x : ι → T)
    (hx : ∀ i, MvPolynomial.aeval x (equations i)=0)
    (hj : IsUnit (Matrix.det (fun i j => MvPolynomial.aeval x
      (MvPolynomial.pderiv i (equations j)))))
    (g : MvPolynomial ι R) (hg : IsUnit (MvPolynomial.aeval x g)) :
    Nontrivial (OpenSystemRing equations g) := by
  have hu : IsUnit (squareSystemEtaleEval equations x hx hj (openElement equations g)) := by
    rwa [etaleEval_polynomial]
  exact (IsLocalization.Away.liftAlgHom (openElement equations g) hu).toRingHom.domain_nontrivial

abbrev GenericRing (K : Type*) [Field K] [Algebra R K]
    (equations : ι → MvPolynomial ι R) (g : MvPolynomial ι R) :=
  K ⊗[R] OpenSystemRing equations g

variable {S : Type*} [CommRing S] [Algebra R S]

def systemMap (equations : ι → MvPolynomial ι R) (g : MvPolynomial ι R)
    (η : OpenSystemRing equations g →ₐ[R] S) : SquareSystemRing equations →ₐ[R] S :=
  η.comp
    ((IsScalarTower.toAlgHom R (SquareEtaleRing equations) (OpenSystemRing equations g)).comp
      (IsScalarTower.toAlgHom R (SquareSystemRing equations) (SquareEtaleRing equations)))

def coordinates (equations : ι → MvPolynomial ι R) (g : MvPolynomial ι R)
    (η : OpenSystemRing equations g →ₐ[R] S) (i : ι) : S :=
  systemMap equations g η (Ideal.Quotient.mk _ (MvPolynomial.X i))

omit [DecidableEq ι] in
lemma evaluation (equations : ι → MvPolynomial ι R) (g : MvPolynomial ι R)
    (η : OpenSystemRing equations g →ₐ[R] S) (P : MvPolynomial ι R) :
    MvPolynomial.aeval (coordinates equations g η) P =
      systemMap equations g η (Ideal.Quotient.mk _ P) := by
  have hh : MvPolynomial.aeval (coordinates equations g η) =
      (systemMap equations g η).comp (Ideal.Quotient.mkₐ R _) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [coordinates]
  exact congrArg (fun f : MvPolynomial ι R →ₐ[R] _ => f P) hh

lemma solution (equations : ι → MvPolynomial ι R) (g : MvPolynomial ι R)
    (η : OpenSystemRing equations g →ₐ[R] S) (i : ι) :
    MvPolynomial.aeval (coordinates equations g η) (equations i)=0 := by
  rw [evaluation]
  have hz : Ideal.Quotient.mk (Ideal.span (Set.range equations)) (equations i)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  rw [hz,map_zero]

lemma open_unit (equations : ι → MvPolynomial ι R) (g : MvPolynomial ι R)
    (η : OpenSystemRing equations g →ₐ[R] S) :
    IsUnit (MvPolynomial.aeval (coordinates equations g η) g) := by
  rw [evaluation]
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := OpenSystemRing equations g) (openElement equations g)
  exact h.map η.toRingHom

end CrossedOpenIncidence
end
end

/- Source component: FullCoefficientNormal. -/
section

/- Full-coefficient version of the accepted polynomial-normal linear algebra.
   The freeness matrix here includes the constant coefficient row. -/
noncomputable section
open scoped BigOperators
namespace CrossedPolynomialNormal
open Polynomial HoldoutConstruction
variable {R : Type*} [CommRing R]

theorem full_linear_combination_one {n : ℕ} (hn : 0<n)
    (Q : Fin n → Polynomial R) (bound : ∀ j, (Q j).natDegree < n)
    (hunit : IsUnit (Matrix.det (fun i j : Fin n => (Q j).coeff i.val))) :
    ∃ u : Fin n → R, ∑ j, C (u j)*Q j=1 := by
  let J : Matrix (Fin n) (Fin n) R := fun i j => (Q j).coeff i.val
  let e : Fin n → R := Pi.single ⟨0,hn⟩ 1
  let u := J⁻¹.mulVec e
  have hu : J.mulVec u=e := by
    dsimp [u]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv J hunit,Matrix.one_mulVec]
  refine ⟨u,?_⟩
  apply Polynomial.ext
  intro k
  by_cases hk : k<n
  · have h := congrFun hu ⟨k,hk⟩
    simp only [Matrix.mulVec,dotProduct,J,e,Pi.single_apply] at h
    rw [show (∑ j, (Q j).coeff k*u j) = ∑ j, u j*(Q j).coeff k by
      apply Finset.sum_congr rfl
      intro j hj
      ring] at h
    simpa [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,Polynomial.coeff_one,
      Fin.ext_iff] using h
  · have hQ (j : Fin n) : (Q j).coeff k=0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (bound j) (Nat.le_of_not_gt hk))
    have hk0 : k ≠ 0 := by omega
    simp [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,hQ,Polynomial.coeff_one,hk0]

theorem exists_full_polynomial_normal {n : ℕ} (hn : 0<n)
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : κ → Polynomial R) (coordinate : Fin n → κ) (degree : Fin n → ℕ)
    (bound : ∀ j, (G (coordinate j)*X^degree j).natDegree < n)
    (hunit : IsUnit (Matrix.det (fun i j : Fin n =>
      (G (coordinate j)*X^degree j).coeff i.val))) :
    ∃ N : κ → Polynomial R, polynomialPairing G N=1 := by
  let v : Fin n → κ → Polynomial R := fun j => Pi.single (coordinate j) (X^degree j)
  have hpair (j : Fin n) : polynomialPairing G (v j) = G (coordinate j)*X^degree j := by
    simp [v,polynomialPairing,Pi.single_apply]
  obtain ⟨u,hu⟩ := full_linear_combination_one hn
    (fun j => G (coordinate j)*X^degree j) bound hunit
  refine ⟨fun i => 0+∑ j, C (u j)*v j i,?_⟩
  rw [polynomialPairing_affine]
  have hz : polynomialPairing G (fun _ : κ => 0)=0 := by simp [polynomialPairing]
  rw [hz,zero_add]
  simpa only [hpair] using hu

end CrossedPolynomialNormal
end
end

/- Source component: AffinePrimitiveData. -/
section

/- The representative construction here is the first, pre-legality part of
   fqlx's maintained residue_solution_clearing, retaining exactly the normal
   identity and zero reduced divergence needed by the elliptic jet calculation. -/
noncomputable section
namespace CrossedAffinePrimitiveData
open HoldoutConstruction
open scoped BigOperators
variable {R K : Type*} [CommRing R] [Field K]

lemma tangent_formula_from_coordinates {n : ℕ}
    (θ : MvPolynomial (Fin (n+1)) R →+* K) (f : MvPolynomial (Fin (n+1)) R)
    (hf : θ f=0) (hg : θ (MvPolynomial.pderiv 0 f)≠0)
    (D : Derivation ℤ K K) (i : Fin n)
    (hC : ∀ r,D (θ (MvPolynomial.C r))=0)
    (hX : ∀ j : Fin n,D (θ (MvPolynomial.X j.succ))=if j=i then 1 else 0)
    (p : MvPolynomial (Fin (n+1)) R) :
    D (θ p)=θ (MvPolynomial.pderiv i.succ p)-
      θ (MvPolynomial.pderiv i.succ f)/θ (MvPolynomial.pderiv 0 f)*θ (MvPolynomial.pderiv 0 p) := by
  have he := derivation_polynomial_ringHom_chain D θ hC f
  rw [hf,map_zero] at he
  simp only [Fin.sum_univ_succ,hX,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at he
  have hn : D (θ (MvPolynomial.X 0))= -θ (MvPolynomial.pderiv i.succ f)/θ (MvPolynomial.pderiv 0 f) := by
    field_simp
    linear_combination -he
  rw [derivation_polynomial_ringHom_chain D θ hC p]
  simp only [Fin.sum_univ_succ,hX,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hn]
  ring

theorem ambient_data {ι : Type*} [Fintype ι]
    (ρ : R →+* K) (Δ₀ : Derivation ℤ R R) (Δ : ι → Derivation ℤ R R)
    (E : ι → Derivation ℤ K K) (f A : R) (w : ι → K)
    (hg : ρ (Δ₀ f)≠0)
    (mixed : ∀ i,Δ i (Δ₀ f)=Δ₀ (Δ i f))
    (compatible : ∀ i p,E i (ρ p)=ρ (Δ i p)-ρ (Δ i f)/ρ (Δ₀ f)*ρ (Δ₀ p))
    (representatives : ∃ d : R,∃ n : ι → R,ρ d≠0 ∧ ∀ i,ρ (n i)=ρ d*w i)
    (equation : residueDivergence E (ρ (Δ₀ f)) w=
      -(ρ (Δ₀ A)/ρ (Δ₀ f)-ρ A*ρ (Δ₀ (Δ₀ f))/(ρ (Δ₀ f))^2)) :
    ∃ D N₀ : R,∃ N : ι → R,
      ρ D≠0 ∧ (N₀*Δ₀ f+∑ i,N i*Δ i f=A*D) ∧ ρ (residueDivNum Δ₀ Δ D N₀ N)=0 := by
  obtain ⟨d,n,hd,hn⟩ := representatives
  let D := Δ₀ f*d
  let N₀ := A*d-∑ i,Δ i f*n i
  let N : ι → R := fun i => Δ₀ f*n i
  have hD : ρ D≠0 := by
    change ρ (Δ₀ f*d)≠0
    rw [map_mul]
    exact mul_ne_zero hg hd
  have hN (i : ι) : ρ (N i)=ρ D*w i := by
    simp only [N,D,map_mul,hn]
    ring
  have hnormal : N₀*Δ₀ f+∑ i,N i*Δ i f=A*D :=
    cleared_normal_source A d (Δ₀ f) (fun i => Δ i f) n
  have heq : (ρ (Δ₀ A)*ρ (Δ₀ f)-ρ A*ρ (Δ₀ (Δ₀ f)))/(ρ (Δ₀ f))^2+
      ∑ i,(E i (w i)-w i*E i (ρ (Δ₀ f))/ρ (Δ₀ f))=0 := by
    have he : residueDivergence E (ρ (Δ₀ f)) w=
        ∑ i,(E i (w i)-w i*E i (ρ (Δ₀ f))/ρ (Δ₀ f)) := by
      simp only [residueDivergence,fieldDivergence,Finset.sum_sub_distrib,Finset.sum_div]
    rw [← he,equation]
    field_simp
    ring
  have hdiv := residue_divergence_identity ρ Δ₀ Δ E A D N₀ (Δ₀ f) N
    (fun i => Δ i f) w hg mixed compatible hN hnormal
  rw [heq,mul_zero] at hdiv
  exact ⟨D,N₀,N,hD,hnormal,hdiv⟩

end CrossedAffinePrimitiveData
end
end
