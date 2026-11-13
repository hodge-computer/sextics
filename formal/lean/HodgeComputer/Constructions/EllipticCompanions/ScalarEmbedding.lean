import HodgeComputer.Constructions.EllipticCompanions.Coordinates
import HodgeComputer.Constructions.HoldoutCover.AlgebraicFields

/-!
Parameter-dependent version of the monic cubic/elliptic embedding in
1337isnot1337's accepted crossed-ternary proof (PR #149). The polynomial
on the two ordinary affine coordinates is an argument, not a fixed sextic.
The application must supply irreducibility of its companion cubic.
Prepared with OpenAI Codex assistance for fqlx; original mathematical credit
is retained in the library README and the accepted source explanation.
-/

noncomputable section
namespace EllipticCompanion
open Polynomial HoldoutConstruction CrossedElliptic
abbrev P2 := MvPolynomial (Fin 2) ℂ
abbrev Coeff := MvPolynomial (Fin 3) ℂ

def base (p : P2) : Coeff := (MvPolynomial.finSuccEquiv ℂ 2).symm (C p)
def equation (p : P2) : Polynomial Coeff := X^3+C (MvPolynomial.X 0^3+base p)
lemma equation_monic (p : P2) : (equation p).Monic := monic_X_pow_add_C _ (by decide)
abbrev CoordinateRing (p : P2) := AdjoinRoot (equation p)

variable {K : Type*} [Field K] [CharZero K]

def coefficientMap (φ : P2 →+* K) (u : K) : Coeff →+* E K :=
  (Polynomial.eval₂RingHom (algebraMap K (E K)) (algebraMap K (E K) u*a (K:=K))).comp
    ((Polynomial.mapRingHom φ).comp (MvPolynomial.finSuccEquiv ℂ 2).toRingHom)

lemma coefficientMap_injective (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu : u≠0) : Function.Injective (coefficientMap φ u) :=
  (transcendental_iff_injective.mp (fermat_scaled_a_transcendental u hu)).comp
    ((Polynomial.map_injective φ hφ).comp (MvPolynomial.finSuccEquiv ℂ 2).injective)

lemma base_univariate (p : P2) : MvPolynomial.finSuccEquiv ℂ 2 (base p)=C p :=
  (MvPolynomial.finSuccEquiv ℂ 2).apply_symm_apply _

omit [CharZero K] in
lemma coefficientMap_base (φ : P2 →+* K) (u : K) (p : P2) :
    coefficientMap φ u (base p)=algebraMap K (E K) (φ p) := by
  change Polynomial.eval₂ (algebraMap K (E K)) (algebraMap K (E K) u*a (K:=K))
    ((MvPolynomial.finSuccEquiv ℂ 2 (base p)).map φ)=_
  rw [base_univariate,Polynomial.map_C,Polynomial.eval₂_C]

omit [CharZero K] in
lemma coefficientMap_S (φ : P2 →+* K) (u : K) :
    coefficientMap φ u (MvPolynomial.X 0)=algebraMap K (E K) u*a (K:=K) := by
  change Polynomial.eval₂ (algebraMap K (E K)) (algebraMap K (E K) u*a (K:=K))
    ((MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.X 0)).map φ)=_
  rw [MvPolynomial.finSuccEquiv_X_zero,Polynomial.map_X,Polynomial.eval₂_X]

omit [CharZero K] in
lemma coefficientMap_X_succ (φ : P2 →+* K) (u : K) (i : Fin 2) :
    coefficientMap φ u (MvPolynomial.X i.succ)=algebraMap K (E K) (φ (MvPolynomial.X i)) := by
  change Polynomial.eval₂ (algebraMap K (E K)) (algebraMap K (E K) u*a (K:=K))
    ((MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.X i.succ)).map φ)=_
  rw [MvPolynomial.finSuccEquiv_X_succ,Polynomial.map_C,Polynomial.eval₂_C]

omit [CharZero K] in
lemma coefficientMap_C (φ : P2 →+* K) (u : K) (c : ℂ) :
    coefficientMap φ u (MvPolynomial.C c)=algebraMap K (E K) (φ (MvPolynomial.C c)) := by
  change Polynomial.eval₂ (algebraMap K (E K)) (algebraMap K (E K) u*a (K:=K))
    ((MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.C c)).map φ)=_
  rw [show MvPolynomial.finSuccEquiv ℂ 2 (MvPolynomial.C c)=C (MvPolynomial.C c)
    from (MvPolynomial.finSuccEquiv ℂ 2).commutes c,Polynomial.map_C,Polynomial.eval₂_C]

lemma equation_root (p : P2) (φ : P2 →+* K) (u : K) (hu : u^3=φ p) :
    (equation p).eval₂ (coefficientMap φ u) (algebraMap K (E K) u*b (K:=K))=0 := by
  simp only [equation,Polynomial.eval₂_add,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,Polynomial.eval₂_C,map_add,map_pow,coefficientMap_base,coefficientMap_S]
  rw [← hu,map_pow]
  linear_combination (algebraMap K (E K) u)^3*fermat_relation (K:=K)

def ringMap (p : P2) (φ : P2 →+* K) (u : K) (hu : u^3=φ p) :
    CoordinateRing p →+* E K :=
  AdjoinRoot.lift (f:=equation p) (coefficientMap φ u)
    (algebraMap K (E K) u*b (K:=K)) (equation_root p φ u hu)

/-- Inverting a nonzero companion denominator after elliptic substitution
is justified by this injection, not by the substitution formula alone. -/
theorem ringMap_injective (p : P2) (hp : Irreducible (equation p))
    (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ p) : Function.Injective (ringMap p φ u hu) :=
  monic_root_embedding_injective (equation p) (equation_monic p) hp
    (coefficientMap φ u) (coefficientMap_injective φ hφ u hu0)
    (algebraMap K (E K) u*b (K:=K)) (equation_root p φ u hu)

#print axioms ringMap_injective
end EllipticCompanion
