import Mathlib.LinearAlgebra.Matrix.Rank
import Proposal.ImplicitPolynomialTrace
import Proposal.SegreGenericLifting

/-! # Pointed generic lifts of the compatible incidence equations -/

set_option Elab.async false

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

/- Component: continuation_3/cylinder_bridge/CompatibleEquationCoordinates.lean -/
section
/-! Compatible equation coordinates turn an exact linear splitting into
the literal complementary polynomial relation block required by generic
lifting.  This file proves the reconstruction and transformed identities;
it does not assume an independent minor or a generic solution. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CompatibleEquationCoordinates
open Matrix MvPolynomial CycleQ2PolynomialAffineSlice

variable {R S m l ι κ σ : Type*} [CommRing R] [CommRing S]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ]
  [DecidableEq m]

theorem reconstruction (P : Matrix ι m R) (Q : Matrix m ι R)
    (V : Matrix m κ R) (W : Matrix κ m R) (h : Q*P+V*W=1)
    (e : m → R) : Q *ᵥ (P *ᵥ e) + V *ᵥ (W *ᵥ e) = e := by
  rw [mulVec_mulVec,mulVec_mulVec,← add_mulVec,h,one_mulVec]

theorem equations_zero_iff (P : Matrix ι m R) (Q : Matrix m ι R)
    (V : Matrix m κ R) (W : Matrix κ m R) (h : Q*P+V*W=1)
    (e : m → R) : P*ᵥe=0 ∧ W*ᵥe=0 ↔ e=0 := by
  constructor
  · rintro ⟨hP,hW⟩
    have hr := reconstruction P Q V W h e
    rw [hP,hW,mulVec_zero,mulVec_zero,add_zero] at hr
    exact hr.symm
  · rintro rfl
    exact ⟨mulVec_zero _,mulVec_zero _⟩

theorem transformed_relations (P : Matrix ι m R) (Q : Matrix m ι R)
    (V : Matrix m κ R) (W : Matrix κ m R) (T : Matrix κ l R)
    (D : Matrix l m R) (h : Q*P+V*W=1) (e : m → R) (he : D*ᵥe=0) :
    (T*D*V) *ᵥ (W*ᵥe) + (T*D*Q) *ᵥ (P*ᵥe) = 0 := by
  calc
    _ = (T*D) *ᵥ (V*ᵥ(W*ᵥe) + Q*ᵥ(P*ᵥe)) := by
      simp only [mulVec_add,mulVec_mulVec,Matrix.mul_assoc]
    _ = (T*D) *ᵥ e := by rw [add_comm,reconstruction P Q V W h]
    _ = 0 := by rw [← mulVec_mulVec,he,mulVec_zero]

theorem mapped_decomposition (φ : R →+* S)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (h : Q*P+V*W=1) : Q.map φ * P.map φ + V.map φ * W.map φ = 1 := by
  have hm := congrArg (fun M : Matrix m m R => M.map φ) h
  simpa only [Matrix.map_add φ (map_add φ),Matrix.map_mul,
    Matrix.map_one φ (map_zero φ) (map_one φ)] using hm

def retained (P : Matrix ι m R) (e : m → MvPolynomial σ R) :
    ι → MvPolynomial σ R := P.map C *ᵥ e

def complementary (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (V : Matrix m κ R) : Matrix κ κ (MvPolynomial σ R) := T.map C * D * V.map C

def crossBlock (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (Q : Matrix m ι R) : Matrix κ ι (MvPolynomial σ R) := T.map C * D * Q.map C

theorem polynomial_relations
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (h : Q*P+V*W=1) (e : m → MvPolynomial σ R) (he : D*ᵥe=0) :
    complementary T D V *ᵥ retained W e + crossBlock T D Q *ᵥ retained P e = 0 :=
  transformed_relations (P.map C) (Q.map C) (V.map C) (W.map C) (T.map C) D
    (mapped_decomposition C P Q V W h) e he

theorem eval_retained (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R) :
    (fun q => eval₂Hom φ x (retained P e q)) =
      P.map φ *ᵥ (fun q => eval₂Hom φ x (e q)) := by
  funext q
  simp only [retained,Matrix.mulVec,Matrix.map_apply,dotProduct,map_sum,map_mul,eval₂Hom_C]

theorem eval_complementary (φ : R →+* S) (x : σ → S)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R) :
    (complementary T D V).map (eval₂Hom φ x) =
      T.map φ * D.map (eval₂Hom φ x) * V.map φ := by
  simp only [complementary,Matrix.map_mul,Matrix.map_map,Function.comp_def,eval₂Hom_C]

theorem jacobian_retained [Fintype σ] (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R) :
    jacobian φ x (retained P e) = P.map φ * jacobian φ x e := by
  funext q j
  simp only [jacobian,retained,Matrix.mulVec,dotProduct,Matrix.map_apply,Matrix.mul_apply,
    map_sum,pderiv_C_mul,map_mul,eval₂Hom_C]

theorem sliced_jacobian [Fintype σ] (φ : R →+* S) (a : σ → R)
    (B : Matrix σ ι R) (P : Matrix ι m R) (e : m → MvPolynomial σ R) :
    jacobian φ (0 : ι → S) (fun q => substitute a B (retained P e q)) =
      P.map φ * jacobian φ (φ ∘ a) e * B.map φ := by
  rw [jacobian_zero_substitute,jacobian_retained]

end CycleQ2CompatibleEquationCoordinates

#print axioms CycleQ2CompatibleEquationCoordinates.polynomial_relations
#print axioms CycleQ2CompatibleEquationCoordinates.sliced_jacobian
end
end

/- Component: continuation_3/PointedSquareGeneric.lean -/
section
/-! The generic component of a literal Jacobian-localized square system can
be chosen to specialize to its given nonsingular seed.  The resulting
coordinates satisfy the same actual equations and Jacobian condition, and
every polynomial identity at the generic point remains an identity at the
seed.  No map from the entire generic field to the special field is asserted.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PointedSquareGeneric

open MvPolynomial HoldoutConstruction CycleQ2PointedEtaleGeneric
open scoped TensorProduct

variable {R K T ι : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field T] [Algebra R T] [Fintype ι] [DecidableEq ι]

theorem seedEtaleEval_polynomial
    (e : ι → MvPolynomial ι R) (seed : ι → T)
    (he : ∀i,aeval seed (e i)=0)
    (hj : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (e j)))))
    (p : MvPolynomial ι R) :
    squareSystemEtaleEval e seed he hj
      (algebraMap (SquareSystemRing e) (SquareEtaleRing e) (Ideal.Quotient.mk _ p))=
        aeval seed p := by
  rw [squareSystemEtaleEval,IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq]
  rfl

theorem polynomial_zero_specializes
    (e : ι → MvPolynomial ι R) (seed : ι → T)
    (he : ∀i,aeval seed (e i)=0)
    (hj : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (e j)))))
    (I : Ideal (SquareGenericAlgebra K e))
    (hI : I.comap (Algebra.TensorProduct.includeRight :
        SquareEtaleRing e →ₐ[R] SquareGenericAlgebra K e).toRingHom ≤
      RingHom.ker (squareSystemEtaleEval e seed he hj).toRingHom)
    (p : MvPolynomial ι R)
    (hp : aeval (squareGenericCoordinates e I) p=0) : aeval seed p=0 := by
  let b : SquareEtaleRing e :=
    algebraMap (SquareSystemRing e) (SquareEtaleRing e) (Ideal.Quotient.mk _ p)
  have hb : Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight b)=0 := by
    change squareGenericMap e I (Ideal.Quotient.mk _ p)=0
    rw [←squareGeneric_eval]
    exact hp
  have hs := seed_zero_of_generic_zero K (squareSystemEtaleEval e seed he hj) I hI b hb
  change squareSystemEtaleEval e seed he hj
    (algebraMap (SquareSystemRing e) (SquareEtaleRing e) (Ideal.Quotient.mk _ p))=0 at hs
  rwa [seedEtaleEval_polynomial] at hs

theorem exists_pointed_square_fieldFactor
    (e : ι → MvPolynomial ι R) (seed : ι → T)
    (he : ∀i,aeval seed (e i)=0)
    (hj : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (e j))))) :
    ∃ I : Ideal (SquareGenericAlgebra K e), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K e) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K e) ⧸ I) ∧
      (I.comap (Algebra.TensorProduct.includeRight :
          SquareEtaleRing e →ₐ[R] SquareGenericAlgebra K e).toRingHom ≤
        RingHom.ker (squareSystemEtaleEval e seed he hj).toRingHom) ∧
      (∀ i,aeval (squareGenericCoordinates e I) (e i)=0) ∧
      IsUnit (Matrix.det (fun i j =>
        aeval (squareGenericCoordinates e I) (pderiv i (e j)))) ∧
      (∀ p : MvPolynomial ι R,
        aeval (squareGenericCoordinates e I) p=0 → aeval seed p=0) := by
  letI : Algebra.Etale R (SquareEtaleRing e) := square_system_jacobian_etale e
  obtain ⟨I,hmax,hfin,hsep,hpoint⟩ :=
    exists_pointed_fieldFactor K (squareSystemEtaleEval e seed he hj)
  exact ⟨I,hmax,hfin,hsep,hpoint,squareGeneric_solution e I,
    squareGeneric_jacobian e I,polynomial_zero_specializes e seed he hj I hpoint⟩

end CycleQ2PointedSquareGeneric

#print axioms CycleQ2PointedSquareGeneric.exists_pointed_square_fieldFactor
#print axioms CycleQ2PointedSquareGeneric.polynomial_zero_specializes
end
end

/- Component: continuation_3/PointedOpenLifting.lean -/
section
/-! A generic solution on a prescribed polynomial open, chosen on a
component through the actual nonsingular seed.  The field quotient and
coordinates are those of the same Jacobian-localized open-square system
used by the original lifting construction. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PointedOpenLifting

open MvPolynomial HoldoutConstruction CycleQ2OpenSquareLifting
  CycleQ2PointedSquareGeneric

variable {R K T ι : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field T] [Algebra R T] [Fintype ι] [DecidableEq ι]

theorem square_system_pointed_lift_on_open
    (e : ι → MvPolynomial ι R) (c : MvPolynomial ι R)
    (seed : ι → T) (he : ∀i,aeval seed (e i)=0)
    (hj : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (e j)))))
    (hc : IsUnit (aeval seed c)) :
    ∃ I : Ideal (SquareGenericAlgebra K (openSystem e c)), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K (openSystem e c)) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K (openSystem e c)) ⧸ I) ∧
      ∃ x : ι → ((SquareGenericAlgebra K (openSystem e c)) ⧸ I),
        (∀i,aeval x (e i)=0) ∧ IsUnit (aeval x c) ∧
        (∀p : MvPolynomial ι R,aeval x p=0 → aeval seed p=0) := by
  obtain ⟨u,hu⟩ := hc.exists_left_inv
  have haug := openSystem_seed e c seed u he hu
  have hjaug : IsUnit (Matrix.det (fun i j =>
      aeval (extendedPoint seed u) (pderiv i (openSystem e c j)))) := by
    rw [openSystem_jacobian_det]
    exact hc.mul hj
  obtain ⟨I,hmax,hfin,hsep,hpoint,hsol,hjac,hspecializes⟩ :=
    exists_pointed_square_fieldFactor (K := K) (openSystem e c)
      (extendedPoint seed u) haug hjaug
  let z := squareGenericCoordinates (openSystem e c) I
  let x : ι → ((SquareGenericAlgebra K (openSystem e c)) ⧸ I) :=
    fun i => z (Sum.inr i)
  have hx := solution_on_open e c z hsol
  refine ⟨I,hmax,hfin,hsep,x,hx.1,hx.2,?_⟩
  intro p hp
  have hp' : aeval z (rename (Sum.inr : ι → Unit ⊕ ι) p)=0 := by
    rw [aeval_rename]
    exact hp
  have hs := hspecializes (rename (Sum.inr : ι → Unit ⊕ ι) p) hp'
  rwa [aeval_extended_rename] at hs

end CycleQ2PointedOpenLifting

#print axioms CycleQ2PointedOpenLifting.square_system_pointed_lift_on_open
end
end

/- Component: continuation_3/cylinder_bridge/SlicedCompatibleSystem.lean -/
section
/-! The square subsystem, complementary relation determinant and prescribed
open after an affine parameter slice.  Both seed determinants are exactly
one whenever the compatible linear splitting has identity seed blocks. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SlicedCompatibleSystem
open MvPolynomial Matrix CycleQ2PolynomialAffineSlice CycleQ2CompatibleEquationCoordinates

variable {R S m l ι κ σ : Type*} [CommRing R] [CommRing S]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ] [Fintype σ]
  [DecidableEq m] [DecidableEq ι] [DecidableEq κ]

def equations (a : σ → R) (B : Matrix σ ι R) (P : Matrix ι m R)
    (e : m → MvPolynomial σ R) : ι → MvPolynomial ι R :=
  fun q => substitute a B (retained P e q)

def residual (a : σ → R) (B : Matrix σ ι R) (W : Matrix κ m R)
    (e : m → MvPolynomial σ R) : κ → MvPolynomial ι R :=
  fun q => substitute a B (retained W e q)

def relationA (a : σ → R) (B : Matrix σ ι R) (T : Matrix κ l R)
    (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R) :
    Matrix κ κ (MvPolynomial ι R) :=
  (complementary T D V).map (substitute a B)

def relationC (a : σ → R) (B : Matrix σ ι R) (T : Matrix κ l R)
    (D : Matrix l m (MvPolynomial σ R)) (Q : Matrix m ι R) :
    Matrix κ ι (MvPolynomial ι R) :=
  (crossBlock T D Q).map (substitute a B)

theorem relation_identity
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (h : Q*P+V*W=1) (e : m → MvPolynomial σ R) (he : D*ᵥe=0) :
    relationA a B T D V *ᵥ residual a B W e +
      relationC a B T D Q *ᵥ equations a B P e = 0 := by
  have hr := polynomial_relations P Q V W T D h e he
  funext q
  have hq := congrArg (substitute a B) (congrFun hr q)
  simpa only [relationA,relationC,equations,residual,Pi.add_apply,Pi.zero_apply,
    Matrix.mulVec,dotProduct,Matrix.map_apply,map_add,map_sum,map_mul,map_zero] using hq

theorem seed_equations_zero (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R)
    (he : ∀ q, eval₂Hom φ (φ ∘ a) (e q)=0) (q : ι) :
    eval₂Hom φ (0 : ι → S) (equations a B P e q)=0 := by
  rw [equations,eval_zero_substitute]
  have hev := congrFun (eval_retained φ (φ ∘ a) P e) q
  have hz : (fun k => eval₂Hom φ (φ ∘ a) (e k))=0 := funext he
  rw [hz,mulVec_zero] at hev
  exact hev

theorem seed_relationA (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R) :
    (relationA a B T D V).map (eval₂Hom φ (0 : ι → S)) =
      T.map φ * D.map (eval₂Hom φ (φ ∘ a)) * V.map φ := by
  have hm : (relationA a B T D V).map (eval₂Hom φ (0 : ι → S)) =
      (complementary T D V).map (eval₂Hom φ (φ ∘ a)) := by
    funext i j
    exact eval_zero_substitute φ a B (complementary T D V i j)
  rw [hm,eval_complementary]

theorem seed_relationA_det_one (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R)
    (h : T.map φ * D.map (eval₂Hom φ (φ ∘ a)) * V.map φ=1) :
    eval₂Hom φ (0 : ι → S) (relationA a B T D V).det=1 := by
  rw [RingHom.map_det]
  change ((relationA a B T D V).map (eval₂Hom φ (0 : ι → S))).det=1
  rw [seed_relationA,h,Matrix.det_one]

/-- The derivative convention used by the generic lifting theorem has
variables as rows.  Its transpose is still the identity seed block. -/
theorem seed_jacobian_one (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R)
    (h : P.map φ * jacobian φ (φ ∘ a) e * B.map φ=1) :
    (fun i j => eval₂Hom φ (0 : ι → S) (pderiv i (equations a B P e j))) =
      (1 : Matrix ι ι S) := by
  have hj : jacobian φ (0 : ι → S) (equations a B P e)=1 := by
    exact (sliced_jacobian φ a B P e).trans h
  funext i j
  have hji := congrFun (congrFun hj j) i
  simpa only [jacobian,Matrix.one_apply,eq_comm] using hji

theorem seed_jacobian_det_one (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R)
    (h : P.map φ * jacobian φ (φ ∘ a) e * B.map φ=1) :
    Matrix.det (fun i j => eval₂Hom φ (0 : ι → S) (pderiv i (equations a B P e j)))=1 := by
  rw [seed_jacobian_one φ a B P e h,Matrix.det_one]

theorem evaluated_equations_zero
    (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (h : Q*P+V*W=1) (e : m → MvPolynomial σ R) (x : ι → S)
    (hP : ∀ q, eval₂Hom φ x (equations a B P e q)=0)
    (hW : ∀ q, eval₂Hom φ x (residual a B W e q)=0) :
    ∀ q, eval₂Hom φ (pointValue φ a B x) (e q)=0 := by
  have hP' : P.map φ *ᵥ (fun q => eval₂Hom φ (pointValue φ a B x) (e q))=0 := by
    rw [← eval_retained]
    funext q
    exact (eval_substitute φ a B x (retained P e q)).symm.trans (hP q)
  have hW' : W.map φ *ᵥ (fun q => eval₂Hom φ (pointValue φ a B x) (e q))=0 := by
    rw [← eval_retained]
    funext q
    exact (eval_substitute φ a B x (retained W e q)).symm.trans (hW q)
  have hz := (equations_zero_iff (P.map φ) (Q.map φ) (V.map φ) (W.map φ)
    (mapped_decomposition φ P Q V W h) _).mp ⟨hP',hW'⟩
  exact fun q => congrFun hz q

end CycleQ2SlicedCompatibleSystem

#print axioms CycleQ2SlicedCompatibleSystem.relation_identity
#print axioms CycleQ2SlicedCompatibleSystem.seed_relationA_det_one
#print axioms CycleQ2SlicedCompatibleSystem.seed_jacobian_det_one
#print axioms CycleQ2SlicedCompatibleSystem.evaluated_equations_zero
end
end

/- Component: continuation_3/cylinder_bridge/CompatibleAffineGenericLifting.lean -/
section
/-! A compatible equation splitting and affine parameter directions give
an actual finite separable generic solution of the entire polynomial
system.  The two nonsingular blocks used in lifting are proved to be the
identity, rather than supplied as additional minor hypotheses. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CompatibleAffineGenericLifting
open MvPolynomial Matrix HoldoutConstruction
open CycleQ2PolynomialAffineSlice CycleQ2CompatibleEquationCoordinates
open CycleQ2SlicedCompatibleSystem

variable {R T K m l ι κ σ : Type*}
  [CommRing R] [CommRing T] [Nontrivial T] [Algebra R T]
  [Field K] [Algebra R K]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ] [Fintype σ]
  [DecidableEq m] [DecidableEq ι] [DecidableEq κ]

abbrev GenericAlgebra (K : Type*) [Field K] [Algebra R K]
    (a : σ → R) (B : Matrix σ ι R) (P : Matrix ι m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R)
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R) :=
  SquareGenericAlgebra K (CycleQ2OpenSquareLifting.openSystem (equations a B P e)
    (substitute a B c * (relationA a B T₀ D V).det))

/-- The coefficient ring may contain the external family parameters.  The
only varied variables are the affine slice coordinates; the resulting
point satisfies every original equation and the original prescribed open. -/
theorem lift_all_on_compatible_affine_slice
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R)
    (hdecomp : Q*P+V*W=1)
    (hrelations : D*ᵥe=0)
    (hseed : ∀ q, eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) (e q)=0)
    (hjac : P.map (algebraMap R T) *
      jacobian (algebraMap R T) ((algebraMap R T) ∘ a) e *
      B.map (algebraMap R T)=1)
    (hcomplement : T₀.map (algebraMap R T) *
      D.map (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a)) *
      V.map (algebraMap R T)=1)
    (hc : IsUnit (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) c))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (GenericAlgebra K a B P T₀ D V e c),
      I.IsMaximal ∧
      Module.Finite K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      Algebra.IsSeparable K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      ∃ x : ι → ((GenericAlgebra K a B P T₀ D V e c) ⧸ I),
        (∀ q, aeval (pointValue (algebraMap R _) a B x) (e q)=0) ∧
        IsUnit (aeval (pointValue (algebraMap R _) a B x) c) := by
  have hseed' (q : ι) : aeval (0 : ι → T) (equations a B P e q)=0 := by
    exact seed_equations_zero (algebraMap R T) a B P e hseed q
  have hjac' : IsUnit (Matrix.det (fun i j =>
      aeval (0 : ι → T) (pderiv i (equations a B P e j)))) := by
    change IsUnit (Matrix.det (fun i j =>
      eval₂Hom (algebraMap R T) (0 : ι → T) (pderiv i (equations a B P e j))))
    rw [seed_jacobian_det_one (algebraMap R T) a B P e hjac]
    exact isUnit_one
  have hcomplement' : IsUnit (aeval (0 : ι → T) (relationA a B T₀ D V).det) := by
    change IsUnit (eval₂Hom (algebraMap R T) (0 : ι → T) (relationA a B T₀ D V).det)
    rw [seed_relationA_det_one (algebraMap R T) a B T₀ D V hcomplement]
    exact isUnit_one
  have hc' : IsUnit (aeval (0 : ι → T) (substitute a B c)) := by
    change IsUnit (eval₂Hom (algebraMap R T) (0 : ι → T) (substitute a B c))
    rw [eval_zero_substitute]
    exact hc
  obtain ⟨I,hI,hfinite,hsep,x,hP,hW,hopen,_⟩ :=
    CycleQ2SegreGenericLifting.lift_all_equations_on_open (K := K)
      (equations a B P e) (residual a B W e)
      (relationA a B T₀ D V) (relationC a B T₀ D Q) (substitute a B c)
      (relation_identity a B P Q V W T₀ D hdecomp e hrelations)
      (0 : ι → T) hseed' hjac' hcomplement' hc' hinj
  refine ⟨I,hI,hfinite,hsep,x,?_,?_⟩
  · exact evaluated_equations_zero (algebraMap R _) a B P Q V W hdecomp e x hP hW
  · change IsUnit (eval₂Hom (algebraMap R _) (pointValue (algebraMap R _) a B x) c)
    rw [← eval_substitute (algebraMap R _) a B x c]
    exact hopen

end CycleQ2CompatibleAffineGenericLifting

#print axioms CycleQ2CompatibleAffineGenericLifting.lift_all_on_compatible_affine_slice
end
end

/- Component: continuation_3/cylinder_bridge/PointedCompatibleAffineLifting.lean -/
section
/-! A compatible affine incidence slice has a finite generic point on a
component through the actual nonsingular seed.  The extra conclusion is
an implication for the original parameter polynomials, obtained from the
proved containment of prime ideals in the Jacobian-localized algebra. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PointedCompatibleAffineLifting
open MvPolynomial Matrix HoldoutConstruction
  CycleQ2PolynomialAffineSlice CycleQ2CompatibleEquationCoordinates
  CycleQ2SlicedCompatibleSystem CycleQ2CompatibleAffineGenericLifting

variable {R S T K m l ι κ σ : Type*}
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ] [Fintype σ]
  [DecidableEq m] [DecidableEq ι] [DecidableEq κ]

theorem affine_lift_semantics
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R)
    (hdecomp : Q*P+V*W=1) (hrelations : D*ᵥe=0)
    (x : ι → S) (hP : ∀q, aeval x (equations a B P e q)=0)
    (hopen : IsUnit (aeval x (substitute a B c*(relationA a B T₀ D V).det))) :
    (∀q, aeval (pointValue (algebraMap R S) a B x) (e q)=0) ∧
      IsUnit (aeval (pointValue (algebraMap R S) a B x) c) := by
  let φ : MvPolynomial ι R →+* S := (aeval x).toRingHom
  have hprod : IsUnit (aeval x (substitute a B c)*aeval x (relationA a B T₀ D V).det) :=
    (congrArg IsUnit ((aeval x).map_mul _ _)).mp hopen
  have heq : φ ∘ equations a B P e=0 := funext hP
  have hres := CycleQ2SegreRelations.evaluated_residual_eq_zero φ
    (relationA a B T₀ D V) (relationC a B T₀ D Q)
    (residual a B W e) (equations a B P e)
    (relation_identity a B P Q V W T₀ D hdecomp e hrelations) heq
    (isUnit_of_mul_isUnit_right hprod)
  refine ⟨evaluated_equations_zero (algebraMap R S) a B P Q V W hdecomp e x hP
    (fun q => congrFun hres q),?_⟩
  exact (congrArg IsUnit (eval_substitute (algebraMap R S) a B x c)).mp
    (isUnit_of_mul_isUnit_left hprod)

variable [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field T] [Algebra R T]

theorem pointed_lift_all_on_compatible_affine_slice
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R)
    (hdecomp : Q*P+V*W=1)
    (hrelations : D*ᵥe=0)
    (hseed : ∀q,eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) (e q)=0)
    (hjac : P.map (algebraMap R T)*
      jacobian (algebraMap R T) ((algebraMap R T) ∘ a) e*B.map (algebraMap R T)=1)
    (hcomplement : T₀.map (algebraMap R T)*
      D.map (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a))*V.map (algebraMap R T)=1)
    (hc : IsUnit (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) c)) :
    ∃ I : Ideal (GenericAlgebra K a B P T₀ D V e c), I.IsMaximal ∧
      Module.Finite K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      Algebra.IsSeparable K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      ∃ x : ι → ((GenericAlgebra K a B P T₀ D V e c) ⧸ I),
        (∀q,aeval (pointValue (algebraMap R _) a B x) (e q)=0) ∧
        IsUnit (aeval (pointValue (algebraMap R _) a B x) c) ∧
        (∀p : MvPolynomial σ R,
          aeval (pointValue (algebraMap R _) a B x) p=0 →
            eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) p=0) := by
  have hseed' (q : ι) : aeval (0 : ι → T) (equations a B P e q)=0 :=
    seed_equations_zero (algebraMap R T) a B P e hseed q
  have hjac' : IsUnit (Matrix.det (fun i j =>
      aeval (0 : ι → T) (pderiv i (equations a B P e j)))) := by
    change IsUnit (Matrix.det (fun i j =>
      eval₂Hom (algebraMap R T) (0 : ι → T) (pderiv i (equations a B P e j))))
    rw [seed_jacobian_det_one (algebraMap R T) a B P e hjac]
    exact isUnit_one
  have hcomplement' : IsUnit (aeval (0 : ι → T) (relationA a B T₀ D V).det) := by
    change IsUnit (eval₂Hom (algebraMap R T) (0 : ι → T) (relationA a B T₀ D V).det)
    rw [seed_relationA_det_one (algebraMap R T) a B T₀ D V hcomplement]
    exact isUnit_one
  have hc' : IsUnit (aeval (0 : ι → T) (substitute a B c)) := by
    change IsUnit (eval₂Hom (algebraMap R T) (0 : ι → T) (substitute a B c))
    rw [eval_zero_substitute]
    exact hc
  have hopen : IsUnit (aeval (0 : ι → T)
      (substitute a B c*(relationA a B T₀ D V).det)) := by
    rw [map_mul]
    exact hc'.mul hcomplement'
  obtain ⟨I,hI,hfinite,hsep,x,hP,ho,hspecializes⟩ :=
    CycleQ2PointedOpenLifting.square_system_pointed_lift_on_open (K := K)
      (equations a B P e) (substitute a B c*(relationA a B T₀ D V).det)
      (0 : ι → T) hseed' hjac' hopen
  have hsem := affine_lift_semantics a B P Q V W T₀ D e c hdecomp hrelations x hP ho
  refine ⟨I,hI,hfinite,hsep,x,hsem.1,hsem.2,?_⟩
  intro p hp
  have hp' : aeval x (substitute a B p)=0 :=
    (eval_substitute (algebraMap R _) a B x p).trans hp
  exact (eval_zero_substitute (algebraMap R T) a B p).symm.trans
    (hspecializes (substitute a B p) hp')

end CycleQ2PointedCompatibleAffineLifting

#print axioms CycleQ2PointedCompatibleAffineLifting.affine_lift_semantics
#print axioms CycleQ2PointedCompatibleAffineLifting.pointed_lift_all_on_compatible_affine_slice
end
end
