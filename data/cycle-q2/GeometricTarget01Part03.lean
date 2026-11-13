import Proposal.GeometricTarget01Part02

/-! Continuation of GeometricTarget01.lean; complete source components and declarations. -/

set_option Elab.async false

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


/- Component: continuation_3/cylinder_bridge/MatrixImageLocalization.lean -/
section
/-! Localization of the actual matrix image is the image of its localized
matrix.  This is proved using the span of the literal columns and mathlib's
localization of submodules, so local image trivializations apply to the
global image module itself. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2MatrixImageLocalization
open Matrix LinearMap

variable {R S α β : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [Fintype α] [Fintype β]
  (p : Submonoid R) [IsLocalization p S]

def vectorMap : (α → R) →ₗ[R] (α → S) :=
  LinearMap.pi (fun i => (Algebra.linearMap R S).comp (LinearMap.proj i))

instance vectorMap_localized : IsLocalizedModule p (vectorMap (R := R) (S := S) (α := α)) :=
  IsLocalizedModule.pi p (fun _ : α => Algebra.linearMap R S)

theorem localized_image (M : Matrix α β R) :
    (LinearMap.range M.mulVecLin).localized' S p (vectorMap (R := R) (S := S))=
      LinearMap.range (M.map (algebraMap R S)).mulVecLin := by
  rw [Matrix.range_mulVecLin,Submodule.localized'_span,Matrix.range_mulVecLin]
  congr 1
  rw [←Set.range_comp]
  rfl

end CycleQ2MatrixImageLocalization

#print axioms CycleQ2MatrixImageLocalization.localized_image
end
end


/- Component: continuation_3/MatrixTraceAugment.lean -/
section
/-! Appending one actual scalar functional to a matrix preserves the
linear-map product description and commutes with coefficient maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2MatrixTraceAugment
open Matrix

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]
  {m n : Type*} [Fintype n]

def rowLinear (r : n → R) : (n → R) →ₗ[R] R :=
  dotProductBilin R R r

def augment (A : Matrix m n R) (r : n → R) : Matrix (m ⊕ Unit) n R :=
  fun i j => Sum.elim (fun k => A k j) (fun _ => r j) i

theorem augment_apply_left (A : Matrix m n R) (r x : n → R) (i : m) :
    (augment A r *ᵥ x) (Sum.inl i)=(A*ᵥx) i := rfl

theorem augment_apply_right (A : Matrix m n R) (r x : n → R) :
    (augment A r *ᵥ x) (Sum.inr ())=rowLinear r x := rfl

theorem augment_map (φ : R →+* S) (A : Matrix m n R) (r : n → R) :
    (augment A r).map φ=augment (A.map φ) (φ ∘ r) := by
  funext i j
  rcases i with i | i <;> rfl

theorem augment_ker (A : Matrix m n K) (r : n → K) :
    LinearMap.ker (Matrix.mulVecLin (augment A r))=
      LinearMap.ker ((Matrix.mulVecLin A).prod (rowLinear r)) := by
  ext x
  change (augment A r *ᵥ x=0) ↔ (A*ᵥx,rowLinear r x)=0
  constructor
  · intro h
    apply Prod.ext
    · funext i
      exact congrFun h (Sum.inl i)
    · exact congrFun h (Sum.inr ())
  · intro h
    funext i
    rcases i with i | i
    · exact congrFun (congrArg Prod.fst h) i
    · cases i
      exact congrArg Prod.snd h

theorem augment_rank [Fintype m] (A : Matrix m n K) (r : n → K) :
    (augment A r).rank=
      Module.finrank K (LinearMap.range ((Matrix.mulVecLin A).prod (rowLinear r))) := by
  classical
  have hA := (Matrix.mulVecLin (augment A r)).finrank_range_add_finrank_ker
  have hB := ((Matrix.mulVecLin A).prod (rowLinear r)).finrank_range_add_finrank_ker
  rw [augment_ker] at hA
  change (augment A r).rank+_= _ at hA
  omega

end CycleQ2MatrixTraceAugment

#print axioms CycleQ2MatrixTraceAugment.augment_rank
end
end


/- Component: continuation_3/NaturalPolynomialDigits.lean -/
section
/-! Exact extraction of polynomial coefficients from a natural base evaluation.
The coefficient bound rules out carries. -/

namespace CycleQ2NaturalPolynomialDigits
open Polynomial

theorem eval_split (B : ℕ) (p : ℕ[X]) :
    p.eval B=p.coeff 0+B*p.divX.eval B := by
  have h := congrArg (Polynomial.eval B) (divX_mul_X_add p)
  simpa only [eval_add,eval_mul,eval_X,eval_C,Nat.mul_comm,Nat.add_comm] using h.symm

theorem div_eval (B : ℕ) (hB : 0<B) (p : ℕ[X]) (h0 : p.coeff 0<B) :
    p.eval B/B=p.divX.eval B := by
  rw [eval_split,Nat.add_mul_div_left _ _ hB,Nat.div_eq_of_lt h0,zero_add]

theorem coefficient (B : ℕ) (hB : 0<B) (p : ℕ[X])
    (hc : ∀ n,p.coeff n<B) (k : ℕ) :
    p.coeff k=(p.eval B/B^k)%B := by
  induction k generalizing p with
  | zero =>
    rw [Nat.pow_zero,Nat.div_one,eval_split]
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (hc 0)]
  | succ k ih =>
    have h := ih p.divX (fun n => by simpa only [coeff_divX] using hc (n+1))
    rw [coeff_divX,←div_eval B hB p (hc 0)] at h
    simpa only [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm] using h

end CycleQ2NaturalPolynomialDigits

#print axioms CycleQ2NaturalPolynomialDigits.coefficient
end


/- Component: continuation_3/PointedEtaleGeneric.lean -/
section
/-! A finite separable generic point specializing to a prescribed seed.

Flat going-down first produces a prime below the seed kernel and contracting
to zero in the base domain.  Localizing at the nonzero base elements then
gives a prime of the actual generic fiber.  That fiber is an étale algebra
over a field, hence finite; its prime is maximal and its quotient separable.
The contraction containment is retained in the conclusion, so this does not
choose an unrelated component of the generic fiber.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PointedEtaleGeneric

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]

theorem exists_generic_prime_below [Module.Flat R B]
    (q : Ideal B) [q.IsPrime] :
    ∃ P : Ideal B, P≤q ∧ P.IsPrime ∧ P.under R=⊥ := by
  obtain ⟨P,hP,hprime,hlying⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R))
      (q := q.under R) q bot_le
  exact ⟨P,hP,hprime,hlying.over.symm⟩

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

theorem genericFiber_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (K ⊗[R] B) :=
  (Algebra.isLocalization_iff_isPushout (nonZeroDivisors R) K).mpr inferInstance

theorem generic_prime_disjoint (P : Ideal B) (hP : P.under R=⊥) :
    Disjoint (Algebra.algebraMapSubmonoid B (nonZeroDivisors R) : Set B) P := by
  rw [Set.disjoint_left]
  intro b hb hmem
  obtain ⟨r,hr,rfl⟩ := hb
  have hz : r∈P.under R := hmem
  rw [hP,Ideal.mem_bot] at hz
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) hz

/-- The chosen maximal ideal of the generic fiber lies on a component
whose closure contains the prescribed seed. -/
theorem exists_pointed_fieldFactor [Algebra.Etale R B]
    {T : Type*} [Field T] [Algebra R T] (seed : B →ₐ[R] T) :
    ∃ I : Ideal (K ⊗[R] B), I.IsMaximal ∧
      Module.Finite K ((K ⊗[R] B) ⧸ I) ∧
      Algebra.IsSeparable K ((K ⊗[R] B) ⧸ I) ∧
      I.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ≤
        RingHom.ker seed.toRingHom := by
  let q : Ideal B := RingHom.ker seed.toRingHom
  letI : q.IsPrime := RingHom.ker_isPrime seed.toRingHom
  obtain ⟨P,hP,hprime,hzero⟩ := exists_generic_prime_below (R := R) q
  letI : P.IsPrime := hprime
  let M : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
  letI : IsLocalization M (K ⊗[R] B) := genericFiber_isLocalization K
  have hd : Disjoint (M : Set B) P := generic_prime_disjoint P hzero
  let I : Ideal (K ⊗[R] B) := P.map (algebraMap B (K ⊗[R] B))
  letI : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P hprime hd
  letI : Module.Finite K (K ⊗[R] B) :=
    Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] B)
  letI : IsArtinianRing (K ⊗[R] B) := IsArtinianRing.of_finite K (K ⊗[R] B)
  refine ⟨I,inferInstance,inferInstance,inferInstance,?_⟩
  have hIP : I.under B=P :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hprime hd
  change I.under B≤q
  rw [hIP]
  exact hP

theorem seed_zero_of_generic_zero {T : Type*} [Field T] [Algebra R T]
    (seed : B →ₐ[R] T) (I : Ideal (K ⊗[R] B))
    (hI : I.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ≤
      RingHom.ker seed.toRingHom) (b : B)
    (hb : Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight b)=0) :
    seed b=0 := by
  apply hI
  change Algebra.TensorProduct.includeRight b∈I
  exact Ideal.Quotient.eq_zero_iff_mem.mp hb

theorem generic_ne_zero_of_seed_ne_zero {T : Type*} [Field T] [Algebra R T]
    (seed : B →ₐ[R] T) (I : Ideal (K ⊗[R] B))
    (hI : I.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ≤
      RingHom.ker seed.toRingHom) (b : B) (hb : seed b≠0) :
    Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight b)≠0 :=
  fun h => hb (seed_zero_of_generic_zero K seed I hI b h)

end CycleQ2PointedEtaleGeneric

#print axioms CycleQ2PointedEtaleGeneric.exists_pointed_fieldFactor
#print axioms CycleQ2PointedEtaleGeneric.generic_ne_zero_of_seed_ne_zero
end
end


/- Component: continuation_3/cylinder_bridge/PolynomialAffineSlice.lean -/
section
/-! Affine polynomial substitution and its literal Jacobian.  The centre may
belong to a parameter coefficient ring; it need not be a constant complex
point.  Thus the same construction fixes the external family parameters. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialAffineSlice
open MvPolynomial Matrix

variable {R S σ ι m : Type*} [CommRing R] [CommRing S]
  [Fintype ι]

def affinePoint (a : σ → R) (B : Matrix σ ι R) : σ → MvPolynomial ι R :=
  fun k => C (a k) + ∑ j, C (B k j) * X j

def substitute (a : σ → R) (B : Matrix σ ι R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial ι R :=
  aeval (affinePoint a B)

def pointValue (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) : σ → S :=
  fun k => φ (a k) + ∑ j, φ (B k j) * x j

theorem eval_affinePoint (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (k : σ) :
    eval₂Hom φ x (affinePoint a B k) = pointValue φ a B x k := by
  simp [affinePoint,pointValue]

theorem eval_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (p : MvPolynomial σ R) :
    eval₂Hom φ x (substitute a B p) = eval₂Hom φ (pointValue φ a B x) p := by
  have h : (eval₂Hom φ x).comp (substitute a B).toRingHom =
      eval₂Hom φ (pointValue φ a B x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [substitute]
    · intro k
      change eval₂Hom φ x (aeval (affinePoint a B) (X k)) =
        eval₂Hom φ (pointValue φ a B x) (X k)
      rw [aeval_X,eval₂Hom_X']
      exact eval_affinePoint φ a B x k
  exact RingHom.congr_fun h p

theorem eval_zero_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (p : MvPolynomial σ R) :
    eval₂Hom φ (0 : ι → S) (substitute a B p) = eval₂Hom φ (φ ∘ a) p := by
  have hp : pointValue φ a B (0 : ι → S) = φ ∘ a := by
    funext k
    simp [pointValue]
  rw [eval_substitute,hp]

theorem pderiv_affinePoint (a : σ → R) (B : Matrix σ ι R) (j : ι) (k : σ) :
    pderiv j (affinePoint a B k) = C (B k j) := by
  classical
  simp [affinePoint,Pi.single_apply]

theorem substitute_C (a : σ → R) (B : Matrix σ ι R) (r : R) :
    substitute a B (C r) = C r := by
  exact aeval_C (affinePoint a B) r

theorem substitute_X (a : σ → R) (B : Matrix σ ι R) (k : σ) :
    substitute a B (X k) = affinePoint a B k := aeval_X _ k

variable [Fintype σ]

/-- The exact chain rule for the chosen affine parameter directions. -/
theorem pderiv_substitute (a : σ → R) (B : Matrix σ ι R) (j : ι)
    (p : MvPolynomial σ R) :
    pderiv j (substitute a B p) =
      ∑ k, C (B k j) * substitute a B (pderiv k p) := by
  classical
  refine MvPolynomial.induction_on (motive := fun f =>
    pderiv j (substitute a B f) = ∑ k, C (B k j) * substitute a B (pderiv k f))
    p ?_ ?_ ?_
  · intro r
    simp only [substitute_C,pderiv_C,map_zero,mul_zero,Finset.sum_const_zero]
  · intro p q hp hq
    simp only [map_add,hp,hq,mul_add,Finset.sum_add_distrib]
  · intro p k hp
    have hx : substitute a B (X k) = affinePoint a B k := substitute_X a B k
    have hs : (∑ l, C (B l j) * substitute a B p *
        substitute a B (pderiv l (X k))) = C (B k j) * substitute a B p := by
      rw [Finset.sum_eq_single k]
      · rw [pderiv_X_self,map_one,mul_one]
      · intro l _ hl
        rw [pderiv_X_of_ne (Ne.symm hl),map_zero,mul_zero]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    calc
      _ = (∑ l, C (B l j) * substitute a B (pderiv l p)) * affinePoint a B k +
          substitute a B p * C (B k j) := by
        rw [map_mul,pderiv_mul,hp,hx,pderiv_affinePoint]
      _ = (∑ l, C (B l j) * substitute a B (pderiv l p) * affinePoint a B k) +
          ∑ l, C (B l j) * substitute a B p * substitute a B (pderiv l (X k)) := by
        rw [← Finset.sum_mul,hs,mul_comm (substitute a B p)]
      _ = ∑ l, C (B l j) * substitute a B (pderiv l (p * X k)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro l _
        rw [pderiv_mul,map_add,map_mul,map_mul,hx]
        simp only [mul_add,mul_assoc]
theorem eval_pderiv_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (j : ι) (p : MvPolynomial σ R) :
    eval₂Hom φ x (pderiv j (substitute a B p)) =
      ∑ k, φ (B k j) * eval₂Hom φ (pointValue φ a B x) (pderiv k p) := by
  rw [pderiv_substitute]
  simp only [map_sum,map_mul,eval₂Hom_C,eval_substitute]

theorem eval_zero_pderiv_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (j : ι) (p : MvPolynomial σ R) :
    eval₂Hom φ (0 : ι → S) (pderiv j (substitute a B p)) =
      ∑ k, φ (B k j) * eval₂Hom φ (φ ∘ a) (pderiv k p) := by
  have hp : pointValue φ a B (0 : ι → S) = φ ∘ a := by
    funext k
    simp [pointValue]
  rw [eval_pderiv_substitute,hp]

def jacobian (φ : R →+* S) (x : σ → S) (e : m → MvPolynomial σ R) :
    Matrix m σ S := fun q k => eval₂Hom φ x (pderiv k (e q))

theorem jacobian_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (e : m → MvPolynomial σ R) :
    jacobian φ x (fun q => substitute a B (e q)) =
      jacobian φ (pointValue φ a B x) e * B.map φ := by
  funext q j
  simp only [jacobian,eval_pderiv_substitute,Matrix.mul_apply,Matrix.map_apply,mul_comm]

theorem jacobian_zero_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) :
    jacobian φ (0 : ι → S) (fun q => substitute a B (e q)) =
      jacobian φ (φ ∘ a) e * B.map φ := by
  have hp : pointValue φ a B (0 : ι → S) = φ ∘ a := by
    funext k
    simp [pointValue]
  rw [jacobian_substitute,hp]

end CycleQ2PolynomialAffineSlice

#print axioms CycleQ2PolynomialAffineSlice.pderiv_substitute
#print axioms CycleQ2PolynomialAffineSlice.jacobian_zero_substitute
end
end


/- Component: continuation_3/cylinder_bridge/PolynomialDualEvaluation.lean -/
section
/-! A literal single-coordinate dual-number evaluation of a polynomial has
first coefficient equal to its formal partial derivative at the base point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace CycleQ2PolynomialDualEvaluation
open MvPolynomial

variable {R σ : Type*} [CommRing R]

abbrev Dual (R : Type*) := TrivSqZeroExt R R

def point (x : σ → R) (j : σ) : σ → Dual R := by
  classical
  exact fun i => ⟨x i,if j=i then 1 else 0⟩

theorem eval_point (x : σ → R) (j : σ) (p : MvPolynomial σ R) :
    aeval (point x j) p = (⟨eval x p,eval x (pderiv j p)⟩ : Dual R) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
      apply TrivSqZeroExt.ext <;> simp [point, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
      rw [map_add,hp,hq]
      apply TrivSqZeroExt.ext <;> simp
  | mul_X p i hp =>
      rw [map_mul,hp,aeval_X]
      apply TrivSqZeroExt.ext
      · simp [point]
      · by_cases hij : j=i
        · subst i
          simp [point,pderiv_mul,pderiv_X,smul_eq_mul,op_smul_eq_smul]
          ring
        · simp [point,pderiv_mul,pderiv_X,Pi.single_apply,hij,Ne.symm hij,
            smul_eq_mul,op_smul_eq_smul]
          ring

theorem eval_point_fst (x : σ → R) (j : σ) (p : MvPolynomial σ R) :
    (aeval (point x j) p).fst=eval x p := by rw [eval_point]; rfl

theorem eval_point_snd (x : σ → R) (j : σ) (p : MvPolynomial σ R) :
    (aeval (point x j) p).snd=eval x (pderiv j p) := by rw [eval_point]; rfl

end CycleQ2PolynomialDualEvaluation

#print axioms CycleQ2PolynomialDualEvaluation.eval_point_snd
end
end


/- Component: continuation_3/PolynomialSurjectivityOpen.lean -/
section
/-! A single principal open preserves surjectivity of an actual finite
coefficient matrix. A coefficient section lifts a nonconstructively chosen
seed right inverse. The resulting determinant evaluates to one at the seed.
No evaluated choice of a maximal minor is required. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2PolynomialSurjectivityOpen
open Matrix

variable {R K : Type*} [CommRing R] [CommRing K]
  {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]

/-- A surjective seed matrix remains surjective after any coefficient map
on which the chosen determinant is a unit. This holds over arbitrary
commutative target rings, including actual coordinate localizations. -/
theorem exists_surjectivity_open (f : R →+* K) (c : K →+* R)
    (hfc : ∀ x, f (c x) = x) (A : Matrix m n R)
    (hA : Function.Surjective (A.map f).mulVec) :
    ∃ (B : Matrix n m R) (s : R),
      s = (A * B).det ∧ f s = 1 ∧
      ∀ (S : Type*) [CommRing S] (g : R →+* S), IsUnit (g s) →
        Function.Surjective (A.map g).mulVec := by
  classical
  obtain ⟨B, hB⟩ := mulVec_surjective_iff_exists_right_inverse.mp hA
  let B₀ : Matrix n m R := B.map c
  have hmap : B₀.map f = B := by
    ext i j
    exact hfc (B i j)
  have hproduct : f.mapMatrix (A * B₀) = 1 := by
    change (A * B₀).map f = 1
    rw [Matrix.map_mul, hmap]
    exact hB
  refine ⟨B₀, (A * B₀).det, rfl, ?_, ?_⟩
  · rw [f.map_det, hproduct, Matrix.det_one]
  · intro S _ g hs
    have hdet : IsUnit (g.mapMatrix (A * B₀)).det := by
      rwa [← g.map_det]
    have hu : IsUnit (g.mapMatrix (A * B₀)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hdet
    have hsurj := mulVec_surjective_iff_isUnit.mpr hu
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨B₀.map g *ᵥ x, ?_⟩
    rw [mulVec_mulVec]
    simpa only [RingHom.mapMatrix_apply, Matrix.map_mul] using hx

end CycleQ2PolynomialSurjectivityOpen

#print axioms CycleQ2PolynomialSurjectivityOpen.exists_surjectivity_open
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechAlgebra.lean -/
section
/-!
# The actual sparse seed curve and its two residue charts

The two monic equations below are the equations obtained from the published
sparse seed after eliminating `w = -x₂²`.  This is deliberately not the smooth
Segre incidence seed, whose cubic has the additional term `x₀³`.
-/

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

def quadratic (r x y : R) : R[X] := X ^ 2 - C (r * x * y)

theorem quadratic_monic (r x y : R) : (quadratic r x y).Monic :=
  monic_X_pow_sub_C _ (by decide)

abbrev Quadratic (r x y : R) := AdjoinRoot (quadratic r x y)

def a (r x y : R) : Quadratic r x y := AdjoinRoot.root _

theorem a_sq (r x y : R) :
    a r x y ^ 2 = algebraMap R (Quadratic r x y) (r * x * y) := by
  have hh := AdjoinRoot.mk_self (f := quadratic r x y)
  change AdjoinRoot.mk (quadratic r x y) (X ^ 2 - C (r * x * y)) = 0 at hh
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  exact sub_eq_zero.mp hh

def cubic (r i x y : R) : (Quadratic r x y)[X] :=
  X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ (x ^ 2) +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))

theorem cubic_monic (r i x y : R) : (cubic r i x y).Monic := by
  unfold cubic
  rw [add_assoc]
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (degree_mul_le _ _)
    calc
      _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
      _ < (3 : WithBot ℕ) := by norm_num
  · exact lt_of_le_of_lt degree_C_le (by norm_num)

abbrev CurveAlgebra (r i x y : R) := AdjoinRoot (cubic r i x y)

def x0 (r i x y : R) : CurveAlgebra r i x y :=
  algebraMap (Quadratic r x y) _ (a r x y)

def x2 (r i x y : R) : CurveAlgebra r i x y := AdjoinRoot.root _

def base (r i x y : R) : R →+* CurveAlgebra r i x y :=
  (algebraMap (Quadratic r x y) _).comp (algebraMap R _)

theorem x0_sq (r i x y : R) : x0 r i x y ^ 2 = base r i x y (r * x * y) := by
  rw [x0, ← map_pow, a_sq]
  rfl

theorem x2_cubic (r i x y : R) :
    x2 r i x y ^ 3 + (x0 r i x y + base r i x y x) *
        base r i x y y * x2 r i x y +
      x0 r i x y * base r i x y (x ^ 2) +
        base r i x y ((1 - i) * y ^ 3 - i * x ^ 3) = 0 := by
  have hh := AdjoinRoot.mk_self (f := cubic r i x y)
  change AdjoinRoot.mk (cubic r i x y)
    (X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
      C (a r x y * algebraMap R _ (x ^ 2) +
        algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))) = 0 at hh
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  simpa only [x0, x2, base, RingHom.comp_apply, AdjoinRoot.algebraMap_eq,
    map_pow, add_assoc] using hh

def coefficient (r i x y : R) : CurveAlgebra r i x y →ₗ[R] R :=
  (Polynomial.lcoeff R 1).comp
    ((AdjoinRoot.modByMonicHom (quadratic_monic r x y)).comp
      (((Polynomial.lcoeff (Quadratic r x y) 2).comp
        (AdjoinRoot.modByMonicHom (cubic_monic r i x y))).restrictScalars R))

theorem modByMonicHom_map (f : R →+* S) (p : R[X])
    (hp : p.Monic) (z : AdjoinRoot p) :
    AdjoinRoot.modByMonicHom (hp.map f)
      (AdjoinRoot.map f p (p.map f) (dvd_refl _) z) =
      (AdjoinRoot.modByMonicHom hp z).map f := by
  induction z using AdjoinRoot.induction_on
  rename_i z
  have hm : AdjoinRoot.map f p (p.map f) (dvd_refl _) (AdjoinRoot.mk p z) =
      AdjoinRoot.mk (p.map f) (z.map f) := by
    rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
    exact AdjoinRoot.aeval_eq _
  rw [hm, AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk,
    Polynomial.map_modByMonic _ hp]

theorem modByMonicHom_map_eq (f : R →+* S) (p : R[X]) (q : S[X])
    (hp : p.Monic) (hq : q.Monic) (hpq : p.map f = q) (z : AdjoinRoot p) :
    AdjoinRoot.modByMonicHom hq
      (AdjoinRoot.map f p q (by rw [hpq]) z) =
      (AdjoinRoot.modByMonicHom hp z).map f := by
  subst q
  exact modByMonicHom_map f p hp z

theorem quadratic_map (f : R →+* S) (r x y : R) :
    (quadratic r x y).map f = quadratic (f r) (f x) (f y) := by
  simp [quadratic]

def quadraticMap (f : R →+* S) (r x y : R) :
    Quadratic r x y →+* Quadratic (f r) (f x) (f y) :=
  AdjoinRoot.map f _ _ (by rw [quadratic_map])

@[simp] theorem quadraticMap_a (f : R →+* S) (r x y : R) :
    quadraticMap f r x y (a r x y) = a (f r) (f x) (f y) := by
  simp [quadraticMap, a]

@[simp] theorem quadraticMap_base (f : R →+* S) (r x y z : R) :
    quadraticMap f r x y (algebraMap R (Quadratic r x y) z) =
      algebraMap S _ (f z) := by
  simp [quadraticMap, AdjoinRoot.algebraMap_eq]

@[simp] theorem quadraticMap_of (f : R →+* S) (r x y z : R) :
    quadraticMap f r x y (AdjoinRoot.of (quadratic r x y) z) =
      AdjoinRoot.of (quadratic (f r) (f x) (f y)) (f z) := by
  simp [quadraticMap]

theorem cubic_map (f : R →+* S) (r i x y : R) :
    (cubic r i x y).map (quadraticMap f r x y) =
      cubic (f r) (f i) (f x) (f y) := by
  simp [cubic]

def curveMap (f : R →+* S) (r i x y : R) :
    CurveAlgebra r i x y →+* CurveAlgebra (f r) (f i) (f x) (f y) :=
  AdjoinRoot.map (quadraticMap f r x y) _ _
    (by rw [cubic_map])

@[simp] theorem curveMap_x0 (f : R →+* S) (r i x y : R) :
    curveMap f r i x y (x0 r i x y) = x0 (f r) (f i) (f x) (f y) := by
  simp [curveMap, x0, AdjoinRoot.algebraMap_eq]

@[simp] theorem curveMap_x2 (f : R →+* S) (r i x y : R) :
    curveMap f r i x y (x2 r i x y) = x2 (f r) (f i) (f x) (f y) := by
  simp [curveMap, x2]

@[simp] theorem curveMap_base (f : R →+* S) (r i x y z : R) :
    curveMap f r i x y (base r i x y z) = base (f r) (f i) (f x) (f y) (f z) := by
  simp [curveMap, base, AdjoinRoot.algebraMap_eq]

@[simp] theorem coefficient_curveMap (f : R →+* S) (r i x y : R)
    (z : CurveAlgebra r i x y) :
    coefficient (f r) (f i) (f x) (f y) (curveMap f r i x y z) =
      f (coefficient r i x y z) := by
  change ((AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
    (((AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y)))
      (curveMap f r i x y z)).coeff 2)).coeff 1 =
    f (((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
      (((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).coeff 2)).coeff 1)
  rw [show (AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y)))
      (curveMap f r i x y z) =
      ((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).map
        (quadraticMap f r x y) from
    modByMonicHom_map_eq _ _ _ (cubic_monic r i x y)
      (cubic_monic (f r) (f i) (f x) (f y)) (cubic_map f r i x y) z]
  rw [coeff_map]
  rw [show (AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
      (quadraticMap f r x y
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).coeff 2)) =
      ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).coeff 2)).map f from
    modByMonicHom_map_eq _ _ _ (quadratic_monic r x y)
      (quadratic_monic (f r) (f x) (f y)) (quadratic_map f r x y) _]
  rw [coeff_map]

def norm (r i x y : R) : R :=
  ((1 - i) * y ^ 3 - i * x ^ 3) ^ 2 - r * x ^ 5 * y

def inverseNumerator (r i x y : R) : CurveAlgebra r i x y :=
  -(x2 r i x y ^ 2 + (x0 r i x y + base r i x y x) * base r i x y y) *
    (base r i x y ((1 - i) * y ^ 3 - i * x ^ 3) -
      x0 r i x y * base r i x y (x ^ 2))

/-- An explicit inverse numerator for x₂; no irreducibility or smoothness is
needed.  The only scalar denominator is the displayed binary sextic. -/
theorem x2_mul_inverseNumerator (r i x y : R) :
    x2 r i x y * inverseNumerator r i x y = base r i x y (norm r i x y) := by
  have h0 := x0_sq r i x y
  have h2 := x2_cubic r i x y
  simp only [map_sub, map_mul, map_pow, map_one] at h0 h2 ⊢
  unfold inverseNumerator norm
  simp only [map_sub, map_mul, map_pow, map_one]
  linear_combination
    -((1 - base r i x y i) * base r i x y y ^ 3 -
      base r i x y i * base r i x y x ^ 3 -
      x0 r i x y * base r i x y x ^ 2) * h2 -
    base r i x y x ^ 4 * h0

def x2Unit (r i x y : R) (u : Rˣ) (hu : (u : R) = norm r i x y) :
    (CurveAlgebra r i x y)ˣ where
  val := x2 r i x y
  inv := inverseNumerator r i x y * base r i x y (↑(u⁻¹) : R)
  val_inv := by
    rw [← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp
  inv_val := by
    rw [mul_comm, ← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp

@[simp] theorem coe_x2Unit (r i x y : R) (u : Rˣ) (hu : (u : R) = norm r i x y) :
    (x2Unit r i x y u hu : CurveAlgebra r i x y) = x2 r i x y := rfl

end CycleQ2SeedCech
end
end


/- Component: continuation_3/SeedCechCover.lean -/
section
/-!
# The two actual projective seed charts cover the curve

The proof includes the perturbation by θ x₀³.  Consequently the same two
opens cover both the sparse trace seed (θ = 0) and the smooth incidence
seed (θ = 1).  No smoothness conclusion is inferred from this cover.
-/

namespace CycleQ2SeedCechCover

set_option backward.isDefEq.respectTransparency false

open MvPolynomial CycleQ2SeedTrace

theorem zero_of_chart_equations {R : Type*} [CommRing R] [NoZeroDivisors R]
    (r i θ : R) (hi : i ≠ 0) (h1 : 1 - i ≠ 0) (x : Fin 4 → R)
    (hf : x 0 ^ 2 - r * x 1 * x 3 = 0)
    (hh : x 3 ^ 3 + x 2 ^ 3 + x 1 * x 2 * x 3 + x 0 * x 2 * x 3 +
      x 0 * x 1 ^ 2 - i * (x 1 ^ 3 + x 3 ^ 3) + θ * x 0 ^ 3 = 0)
    (hA : x 1 * x 3 = 0) (hB : x 2 = 0) : x = 0 := by
  have hx0sq : x 0 ^ 2 = 0 := by
    rw [sub_eq_zero] at hf
    rw [hf, mul_assoc, hA, mul_zero]
  have hx0 : x 0 = 0 := eq_zero_of_pow_eq_zero hx0sq
  have hc : (1 - i) * x 3 ^ 3 - i * x 1 ^ 3 = 0 := by
    have hh' : x 3 ^ 3 - i * (x 1 ^ 3 + x 3 ^ 3) = 0 := by
      simpa only [hx0, hB, zero_pow (by decide : 3 ≠ 0), mul_zero,
        zero_mul, add_zero, zero_add] using hh
    calc
      _ = x 3 ^ 3 - i * (x 1 ^ 3 + x 3 ^ 3) := by ring
      _ = 0 := hh'
  have hx13 : x 1 = 0 ∧ x 3 = 0 := by
    rcases mul_eq_zero.mp hA with hx1 | hx3
    · have hz : (1 - i) * x 3 ^ 3 = 0 := by simpa [hx1] using hc
      exact ⟨hx1, eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_left h1)⟩
    · have hz : i * x 1 ^ 3 = 0 := by simpa [hx3] using hc
      exact ⟨eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_left hi), hx3⟩
  funext j
  fin_cases j
  · exact hx0
  · exact hx13.1
  · exact hB
  · exact hx13.2

/-- A nonzero homogeneous representative satisfying the actual curve
equations lies in D₊(x₁x₃) or D₊(x₂). -/
theorem projective_cover (r θ : ℂ) (x : Fin 4 → ℂ)
    (hf : eval x (relation r 0) = 0)
    (hh : eval x (h + C θ * X 0 ^ 3) = 0) (hx : x ≠ 0) :
    x 1 * x 3 ≠ 0 ∨ x 2 ≠ 0 := by
  by_contra hcover
  push Not at hcover
  apply hx
  apply zero_of_chart_equations r Complex.I θ Complex.I_ne_zero
    (by norm_num [Complex.ext_iff]) x
  · simpa [relation] using hf
  · simpa [h, b] using hh
  · exact hcover.1
  · exact hcover.2

theorem sparse_projective_cover (r : ℂ) (x : Fin 4 → ℂ)
    (hf : eval x (relation r 0) = 0) (hh : eval x h = 0) (hx : x ≠ 0) :
    x 1 * x 3 ≠ 0 ∨ x 2 ≠ 0 := by
  exact projective_cover r 0 x hf (by simpa using hh) hx

theorem smooth_seed_projective_cover (r : ℂ) (x : Fin 4 → ℂ)
    (hf : eval x (relation r 0) = 0) (hh : eval x (h + X 0 ^ 3) = 0)
    (hx : x ≠ 0) : x 1 * x 3 ≠ 0 ∨ x 2 ≠ 0 := by
  exact projective_cover r 1 x hf (by simpa using hh) hx

/-- The same cover holds at every relevant prime ideal, including the
nonclosed points of the projective curve. -/
theorem prime_chart_cover (r θ : ℂ) (P : Ideal Poly) [P.IsPrime]
    (hf : relation r 0 ∈ P) (hh : h + C θ * X 0 ^ 3 ∈ P)
    (hrelevant : ∃ j : Fin 4, X j ∉ P) :
    X 1 * X 3 ∉ P ∨ X 2 ∉ P := by
  by_contra hcover
  push Not at hcover
  let π : Poly →+* Poly ⧸ P := Ideal.Quotient.mk P
  have hi : π (C Complex.I) ≠ 0 := by
    have hn := (π.comp (C : ℂ →+* Poly)).injective.ne Complex.I_ne_zero
    simpa only [RingHom.comp_apply, map_zero] using hn
  have h1 : 1 - π (C Complex.I) ≠ 0 := by
    have hc : (1 : ℂ) - Complex.I ≠ 0 := by norm_num [Complex.ext_iff]
    have hn := (π.comp (C : ℂ →+* Poly)).injective.ne hc
    simpa only [RingHom.comp_apply, map_sub, map_one, map_zero] using hn
  have hf' : π (relation r 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have hh' : π (h + C θ * X 0 ^ 3) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hh
  have hA : π (X 1 * X 3) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcover.1
  have hB : π (X 2) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcover.2
  have hz : (fun j : Fin 4 => π (X j)) = 0 := by
    apply zero_of_chart_equations (π (C r)) (π (C Complex.I)) (π (C θ)) hi h1
    · simpa [relation] using hf'
    · simpa [h, b] using hh'
    · simpa only [map_mul] using hA
    · exact hB
  obtain ⟨j, hj⟩ := hrelevant
  exact hj (Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hz j))

section ProjectiveSpectrum

open CycleQ2SupportEquation
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_coordinate_exists (p : AmbientProjectiveSpace 3) :
    ∃ j : Fin 4, X j ∉ p.asHomogeneousIdeal.toIdeal := by
  by_contra hn
  push Not at hn
  have hvars : idealOfVars (Fin 4) ℂ ≤ p.asHomogeneousIdeal.toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hn j
  apply p.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le (ambientGrading 3)).mpr
  intro d hd q hq
  apply hvars
  have hqhom : q.IsHomogeneous d := hq
  have hmem : q ∈ idealOfVars (Fin 4) ℂ ^ 1 := by
    apply (mem_pow_idealOfVars_iff 1 q).mpr
    intro e he
    have heq : e.degree = d := by
      rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
      exact hqhom (mem_support_iff.mp he)
    rw [heq]
    exact hd
  simpa only [pow_one] using hmem

/-- The actual closed curve in the standard projective spectrum. -/
def projectiveCurve (r θ : ℂ) : Set (AmbientProjectiveSpace 3) :=
  ProjectiveSpectrum.zeroLocus (ambientGrading 3)
    ({relation r 0, h + C θ * X 0 ^ 3} : Set Poly)

/-- The two genuine standard opens cover the closed projective seed curve. -/
theorem projectiveCurve_covered (r θ : ℂ) :
    projectiveCurve r θ ⊆
      (ProjectiveSpectrum.basicOpen (ambientGrading 3) (X 1 * X 3) :
        Set (AmbientProjectiveSpace 3)) ∪
      (ProjectiveSpectrum.basicOpen (ambientGrading 3) (X 2) :
        Set (AmbientProjectiveSpace 3)) := by
  intro p hp
  have hf : relation r 0 ∈ p.asHomogeneousIdeal.toIdeal := hp (by simp)
  have hh : h + C θ * X 0 ^ 3 ∈ p.asHomogeneousIdeal.toIdeal := hp (by simp)
  exact prime_chart_cover r θ p.asHomogeneousIdeal.toIdeal hf hh
    (projective_coordinate_exists p)

end ProjectiveSpectrum

end CycleQ2SeedCechCover

#print axioms CycleQ2SeedCechCover.projective_cover
#print axioms CycleQ2SeedCechCover.prime_chart_cover
#print axioms CycleQ2SeedCechCover.projectiveCurve_covered
end


/- Component: continuation_3/SegreGenericLifting.lean -/
section
/-!
# Algebraic generic lifting with all redundant equations

A nonsingular square subsystem and a complementary relation minor at any
special-fiber seed give an actual finite separable generic solution of the
entire polynomial system. The prescribed open and complementary minor are
kept invertible by the proved open-square construction. The special-fiber
coefficient map may have positive-characteristic image.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CycleQ2SegreGenericLifting

open MvPolynomial Matrix HoldoutConstruction

variable {R T K ι κ : Type*} [CommRing R] [CommRing T] [Nontrivial T]
  [Algebra R T] [Field K] [Algebra R K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The existence conclusion concerns the complete polynomial incidence
system. Neither a formal solution nor an algebraic generic solution is a
premise; only the literal equations, relations, and the two seed minors
remain to be supplied by a concrete incidence calculation. -/
theorem lift_all_equations_on_open
    (equations : ι → MvPolynomial ι R)
    (residual : κ → MvPolynomial ι R)
    (A : Matrix κ κ (MvPolynomial ι R))
    (B : Matrix κ ι (MvPolynomial ι R))
    (c : MvPolynomial ι R)
    (hrelations : A *ᵥ residual + B *ᵥ equations = 0)
    (seed : ι → T)
    (hseed : ∀ i, aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (equations j)))))
    (hcomplement : IsUnit (aeval seed A.det))
    (hc : IsUnit (aeval seed c))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (SquareGenericAlgebra K
        (CycleQ2OpenSquareLifting.openSystem equations (c * A.det))),
      I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K
        (CycleQ2OpenSquareLifting.openSystem equations (c * A.det))) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K
        (CycleQ2OpenSquareLifting.openSystem equations (c * A.det))) ⧸ I) ∧
      ∃ x : ι → ((SquareGenericAlgebra K
          (CycleQ2OpenSquareLifting.openSystem equations (c * A.det))) ⧸ I),
        (∀ i, aeval x (equations i) = 0) ∧
        (∀ j, aeval x (residual j) = 0) ∧
        IsUnit (aeval x c) ∧ IsUnit (aeval x A.det) := by
  have hprod : IsUnit (aeval seed (c * A.det)) := by
    rw [map_mul]
    exact hc.mul hcomplement
  obtain ⟨I, hI, hfinite, hsep, x, heq, hopen⟩ :=
    CycleQ2OpenSquareLifting.square_system_generic_lift_on_open
      (K := K) equations (c * A.det) seed hseed hjac hprod hinj
  let E := (SquareGenericAlgebra K
    (CycleQ2OpenSquareLifting.openSystem equations (c * A.det))) ⧸ I
  letI : I.IsMaximal := hI
  letI : Field E := Ideal.Quotient.field I
  have hprod' : IsUnit (aeval x c * aeval x A.det) := by
    simpa only [map_mul] using hopen
  have hA := isUnit_of_mul_isUnit_right hprod'
  let φ : MvPolynomial ι R →+* E := (aeval x).toRingHom
  have heq' : φ ∘ equations = 0 := by
    funext i
    exact heq i
  have hres : φ ∘ residual = 0 :=
    CycleQ2SegreRelations.evaluated_residual_eq_zero
      φ A B residual equations hrelations heq' hA
  exact ⟨I, hI, hfinite, hsep, x, heq, fun j => congrFun hres j,
    isUnit_of_mul_isUnit_left hprod', hA⟩

end CycleQ2SegreGenericLifting

#print axioms CycleQ2SegreGenericLifting.lift_all_equations_on_open
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


