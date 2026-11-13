import HodgeComputer.Constructions.EllipticCompanions.Coordinates
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import Mathlib.RingTheory.Derivation.Basic
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

/- Source component: EvaluatedRationalJets. -/
section

noncomputable section
namespace CrossedEvaluatedJets
open HoldoutConstruction
open scoped BigOperators
variable {R L : Type*} [CommRing R] [Field L]

def values (ρ : R →+* L) (D : R) (N : Fin 4 → R) (i : Fin 4) : L := ρ (N i)/ρ D
def jet (ρ : R →+* L) (Δ : Fin 4 → Derivation ℤ R R) (D : R) (N : Fin 4 → R)
    (i j : Fin 4) : L := (ρ (Δ j (N i))*ρ D-ρ (N i)*ρ (Δ j D))/(ρ D)^2

lemma normal_values (ρ : R →+* L) (D A : R) (N g : Fin 4 → R)
    (hd : ρ D≠0) (hn : (∑ i,N i*g i)=A*D) :
    (∑ i,values ρ D N i*ρ (g i))=ρ A := by
  have he := congrArg ρ hn
  simp only [map_mul,map_add,map_zero,Fin.sum_univ_succ,Fin.sum_univ_zero] at he
  simp only [values,Fin.sum_univ_succ,Fin.sum_univ_zero]
  field_simp
  linear_combination he

lemma normal_jets (ρ : R →+* L) (Δ : Fin 4 → Derivation ℤ R R) (D A : R)
    (N g : Fin 4 → R) (hd : ρ D≠0) (hn : (∑ i,N i*g i)=A*D) (j : Fin 4) :
    (∑ i,jet ρ Δ D N i j*ρ (g i))+
      (∑ i,values ρ D N i*ρ (Δ j (g i)))=ρ (Δ j A) := by
  have he := congrArg ρ hn
  have he' := congrArg (fun p => ρ (Δ j p)) hn
  simp only [map_mul,map_add,map_zero,Derivation.leibniz,smul_eq_mul,
    Fin.sum_univ_succ,Fin.sum_univ_zero] at he he'
  simp only [jet,values,Fin.sum_univ_succ,Fin.sum_univ_zero]
  field_simp
  linear_combination ρ D*he'-ρ (Δ j D)*he

lemma divergence_jets (ρ : R →+* L) (Δ : Fin 4 → Derivation ℤ R R) (D : R) (N : Fin 4 → R)
    (hd : ρ D≠0)
    (hdiv : ρ (D*(∑ i,Δ i (N i))-(∑ i,N i*Δ i D))=0) :
    (∑ i,jet ρ Δ D N i i)=0 := by
  simp only [map_sub,map_mul,map_add,map_zero,Fin.sum_univ_succ,Fin.sum_univ_zero] at hdiv
  simp only [jet,Fin.sum_univ_succ,Fin.sum_univ_zero]
  field_simp
  linear_combination hdiv

lemma derivative_values (ρ : R →+* L) (Δ : Fin 4 → Derivation ℤ R R)
    (E : Derivation ℤ L L) (z : Fin 4 → L)
    (hchain : ∀ p,E (ρ p)=∑ j,ρ (Δ j p)*z j)
    (D : R) (N : Fin 4 → R) (hd : ρ D≠0) (i : Fin 4) :
    E (values ρ D N i)=(∑ j,jet ρ Δ D N i j*z j) := by
  simp only [values,Derivation.leibniz_div,hchain,smul_eq_mul,jet,
    Fin.sum_univ_succ,Fin.sum_univ_zero]
  field_simp
  ring

end CrossedEvaluatedJets
end
end

/- Source component: EllipticJet. -/
section

/- Algebraic identities for a proposed split-sextic construction.
   These are intermediate identities, not a certificate existence theorem.
   Prepared with OpenAI Codex assistance for 1337isnot1337. -/
namespace CrossedEllipticJet

variable {R : Type*} [CommRing R]

theorem scaled_jet_identity
    (u a b px py B Bs Bt vx vy vs vt vxx vyy vss vtt
      vxs vys vts vxt vyt vst : R) :
    (3*u^2*(-a^2*vs-b^2*vt)
      +3*u^3*(b^3*vss-a^2*b*vst-a*b^2*vts+a^3*vtt)
      -3*u^3*(vxx+vyy)
      -u*(px*(a*vxs+b*vxt)+py*(a*vys+b*vyt))+px*vx+py*vy)
      -B+u*(a*Bs+b*Bt) =
    -3*u^3*(vxx+vyy+vss+vtt)
      -a*u*(px*vxs+py*vys+6*u*a*vs+3*u^2*a^2*vss+3*u^2*b^2*vts-Bs)
      -b*u*(px*vxt+py*vyt+6*u*b*vt+3*u^2*a^2*vst+3*u^2*b^2*vtt-Bt)
      +(px*vx+py*vy+3*u^2*a^2*vs+3*u^2*b^2*vt-B)
      +3*u^3*(a^3+b^3+1)*(vss+vtt) := by
  ring

variable {K : Type*} [Field K] [CharZero K]

theorem affine_first_equation
    (p q l src Pd Qd : K) (hp : p ≠ 0) (hq : q ≠ 0) (hl : l ≠ 0) :
    -(l/(3*p))*(Pd+l^6*Qd)
      +6*l^5*q*((3*p*src+Pd+l^6*Qd)/(18*p*l^4*q)) = src*l := by
  field_simp
  ring

theorem affine_divergence_quotient
    (p q l src Pd Qd : K) (hp : p ≠ 0) (hq : q ≠ 0) (hl : l ≠ 0) :
    -l/(3*p)*(src+4*Pd/(3*p)+2*Qd/(3*q)) + l*Pd/(3*p^2)
      -(3*p*src+Pd)/(9*p*q*l^5)+2*l*Qd/(9*p*q)
      = -(p+l^6*q)*(3*p*src+Pd)/(9*p^2*q*l^5) := by
  field_simp
  ring

end CrossedEllipticJet
end

/- Source component: ScalarCompanionJet. -/
section

noncomputable section
namespace CrossedScalarCompanionJet
variable {L : Type*} [Field L] [CharZero L]

def scalarB (u a b : L) (v : Fin 4 → L) : L := 3*(b*v 2-a*v 3)/u^2
def scalarX (u : L) (v : Fin 4 → L) : L := -3*v 0/u
def scalarY (u : L) (v : Fin 4 → L) : L := -3*v 1/u

def jetNumerator (u a b px py : L) (v : Fin 4 → L) (J : Matrix (Fin 4) (Fin 4) L) : L :=
  3*u^2*(-a^2*v 2-b^2*v 3)+
  3*u^3*(b^3*J 2 2-a^2*b*J 2 3-a*b^2*J 3 2+a^3*J 3 3)-
  3*u^3*(J 0 0+J 1 1)-
  u*(px*(a*J 0 2+b*J 0 3)+py*(a*J 1 2+b*J 1 3))+px*v 0+py*v 1

theorem scalar_equation (δ Dx Dy : Derivation ℤ L L)
    (u a b px py B Bs Bt : L) (v : Fin 4 → L) (J : Matrix (Fin 4) (Fin 4) L)
    (hu : u≠0) (hδu : δ u=0) (ha : δ a=b^2) (hb : δ b= -a^2)
    (hDxu : Dx u=px/(3*u^2)) (hDyu : Dy u=py/(3*u^2))
    (hδs : δ (v 2)=u*b^2*J 2 2-u*a^2*J 2 3)
    (hδt : δ (v 3)=u*b^2*J 3 2-u*a^2*J 3 3)
    (hDx : Dx (v 0)=J 0 0+px/(3*u^2)*(a*J 0 2+b*J 0 3))
    (hDy : Dy (v 1)=J 1 1+py/(3*u^2)*(a*J 1 2+b*J 1 3))
    (hfermat : a^3+b^3+1=0)
    (hdiv : J 0 0+J 1 1+J 2 2+J 3 3=0)
    (hnormal : px*v 0+py*v 1+3*u^2*a^2*v 2+3*u^2*b^2*v 3=B)
    (hs : px*J 0 2+py*J 1 2+6*u*a*v 2+3*u^2*a^2*J 2 2+3*u^2*b^2*J 3 2=Bs)
    (ht : px*J 0 3+py*J 1 3+6*u*b*v 3+3*u^2*a^2*J 2 3+3*u^2*b^2*J 3 3=Bt) :
    δ (scalarB u a b v)+Dx (scalarX u v)+Dy (scalarY u v)=B/u^4-(a*Bs+b*Bt)/u^3 := by
  have hraw := CrossedEllipticJet.scaled_jet_identity u a b px py B Bs Bt
    (v 0) (v 1) (v 2) (v 3) (J 0 0) (J 1 1) (J 2 2) (J 3 3)
    (J 0 2) (J 1 2) (J 3 2) (J 0 3) (J 1 3) (J 2 3)
  simp only [hdiv,hnormal,hs,ht,hfermat,sub_self,mul_zero,zero_mul,add_zero] at hraw
  change jetNumerator u a b px py v J-B+u*(a*Bs+b*Bt)=0 at hraw
  have hδ3 : δ (3 : L)=0 := δ.map_natCast 3
  have hx3 : Dx (3 : L)=0 := Dx.map_natCast 3
  have hy3 : Dy (3 : L)=0 := Dy.map_natCast 3
  have he : δ (scalarB u a b v)+Dx (scalarX u v)+Dy (scalarY u v)-
      (B/u^4-(a*Bs+b*Bt)/u^3)=(jetNumerator u a b px py v J-B+u*(a*Bs+b*Bt))/u^4 := by
    simp only [scalarB,scalarX,scalarY,jetNumerator,Derivation.leibniz_div,Derivation.leibniz,
      Derivation.leibniz_pow,map_sub,map_neg,hδ3,hx3,hy3,hδu,ha,hb,hDxu,hDyu,
      hδs,hδt,hDx,hDy,smul_eq_mul,smul_zero,mul_zero,add_zero]
    norm_num only
    field_simp [hu]
    ring
  rw [hraw,zero_div] at he
  exact sub_eq_zero.mp he

end CrossedScalarCompanionJet
end
end

/- Source component: EllipticTranslationMap. -/
section

noncomputable section
namespace CrossedElliptic
open Polynomial CrossedEllipticTranslation
variable (K : Type*) [Field K] [CharZero K]

def translateX (u v : K) : E K :=
  translatedX (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v)
def translateY (u v : K) : E K :=
  translatedY (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v)

lemma translate_relation (u v : K) (hp : v^2=u^3-432) :
    (translateY K u v)^2=(translateX K u v)^3-432 := by
  have hp' := congrArg (algebraMap K (E K)) hp
  have h432 : algebraMap K (E K) (432 : K)=(432 : E K) := map_natCast _ 432
  simp only [map_pow,map_sub,h432] at hp'
  exact translated_curve _ _ _ _ (x_sub_constant_ne_zero K u) (relation K) hp'

lemma translateX_transcendental (u v : K) (hp : v^2=u^3-432) :
    Transcendental K (translateX K u v) := by
  intro hx
  have hy : IsAlgebraic K (translateY K u v) := by
    apply IsAlgebraic.of_pow (by decide : 0<2)
    rw [translate_relation K u v hp]
    exact (hx.pow 3).sub (isAlgebraic_natCast 432)
  have hu : IsAlgebraic K (algebraMap K (E K) u) := isAlgebraic_algebraMap u
  have hv : IsAlgebraic K (algebraMap K (E K) v) := isAlgebraic_algebraMap v
  have hm : IsAlgebraic K ((translateY K u v+algebraMap K (E K) v)/
      (translateX K u v-algebraMap K (E K) u)) := by
    rw [div_eq_mul_inv]
    exact (hy.add hv).mul (IsAlgebraic.inv_iff.mpr (hx.sub hu))
  have hi := inverse_x (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v)
    (x_sub_constant_ne_zero K u) (translatedX_sub_constant_ne_zero_of_point K u v hp)
  have halg : IsAlgebraic K (translateX K u v |> fun z =>
      ((translateY K u v+algebraMap K (E K) v)/(z-algebraMap K (E K) u))^2-z-
        algebraMap K (E K) u) := ((hm.pow 2).sub hx).sub hu
  have he : ((translateY K u v+algebraMap K (E K) v)/
      (translateX K u v-algebraMap K (E K) u))^2-translateX K u v-algebraMap K (E K) u=x K := by
    simpa only [translatedX,slope,sub_neg_eq_add,translateX,translateY] using hi
  exact x_transcendental K (he ▸ halg)

def translateRational (u v : K) (hp : v^2=u^3-432) : RatFunc K →+* E K :=
  IsFractionRing.lift (transcendental_iff_injective.mp (translateX_transcendental K u v hp))

lemma translateRational_C (u v : K) (hp : v^2=u^3-432) (c : K) :
    translateRational K u v hp (RatFunc.C c)=algebraMap K (E K) c := by
  change translateRational K u v hp (algebraMap K[X] (RatFunc K) (C c))=_
  rw [translateRational,IsFractionRing.lift_algebraMap]
  exact Polynomial.aeval_C _ _

lemma translateRational_X (u v : K) (hp : v^2=u^3-432) :
    translateRational K u v hp (RatFunc.X)=translateX K u v := by
  change translateRational K u v hp (algebraMap K[X] (RatFunc K) X)=_
  rw [translateRational,IsFractionRing.lift_algebraMap]
  exact Polynomial.aeval_X _

lemma translate_root (u v : K) (hp : v^2=u^3-432) :
    (equation K).eval₂ (translateRational K u v hp) (translateY K u v)=0 := by
  conv_lhs => arg 3; rw [equation_eq]
  simp only [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,map_sub,map_pow,translateRational_X]
  have hc : translateRational K u v hp (432 : RatFunc K)=(432 : E K) := map_natCast _ 432
  rw [hc,translate_relation K u v hp,sub_self]

def translateMap (u v : K) (hp : v^2=u^3-432) : E K →+* E K :=
  AdjoinRoot.lift (f:=equation K) (translateRational K u v hp) (translateY K u v) (translate_root K u v hp)

lemma translateMap_x (u v : K) (hp : v^2=u^3-432) :
    translateMap K u v hp (x K)=translateX K u v := by
  rw [x,translateMap]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ RatFunc.X)=_
  rw [AdjoinRoot.lift_of,translateRational_X]

lemma translateMap_y (u v : K) (hp : v^2=u^3-432) :
    translateMap K u v hp (y K)=translateY K u v := AdjoinRoot.lift_root _

lemma translateMap_base (u v : K) (hp : v^2=u^3-432) (c : K) :
    translateMap K u v hp (algebraMap K (E K) c)=algebraMap K (E K) c := by
  rw [← map_constant]
  change AdjoinRoot.lift _ _ _ (AdjoinRoot.of _ (RatFunc.C c))=_
  rw [AdjoinRoot.lift_of,translateRational_C]
  exact (map_constant K c).symm

end CrossedElliptic
end
end

/- Source component: EllipticTranslationDifferentials. -/
section

noncomputable section
namespace CrossedEllipticTranslation
variable {L : Type*} [Field L] [CharZero L]

lemma translatedX_derivation (D : Derivation ℤ L L) (x y u v : L)
    (h : x-u≠0) (hx : D x= -y/3) (hy : D y= -x^2/2) (hu : D u=0) (hv : D v=0)
    (hp : y^2=x^3-432) (hq : v^2=u^3-432) :
    D (translatedX x y u v)= -translatedY x y u v/3 := by
  have hi : D (translatedX x y u v)+translatedY x y u v/3=
      ((y-v)*(y^2-x^3+432)+(v-y)*(v^2-u^3+432))/(3*(x-u)^3) := by
    simp only [translatedY,translatedX,slope,div_eq_mul_inv]
    simp only [map_sub,Derivation.leibniz_pow,Derivation.leibniz,
      Derivation.leibniz_inv,hx,hy,hu,hv,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat,
      sub_zero]
    norm_num only
    generalize hd : x-u=d at *
    field_simp [h]
    rw [← hd]
    ring
  rw [hp,hq] at hi
  linear_combination hi

lemma translatedY_derivation (D : Derivation ℤ L L) (x y u v : L)
    (h : x-u≠0) (hx : D x= -y/3) (hy : D y= -x^2/2) (hu : D u=0) (hv : D v=0)
    (hp : y^2=x^3-432) (hq : v^2=u^3-432) :
    D (translatedY x y u v)= -(translatedX x y u v)^2/2 := by
  have hi : D (translatedY x y u v)+(translatedX x y u v)^2/2=
      ((-2*u^2*x+u*x^2+2*v*y-y^2+432)*(y^2-x^3+432)+
        (-u^3+2*u^2*x-u*x^2+v^2-2*v*y+x^3-432)*(v^2-u^3+432))/(2*(x-u)^4) := by
    simp only [translatedY,translatedX,slope,div_eq_mul_inv]
    simp only [map_sub,map_add,map_neg,Derivation.leibniz_pow,
      Derivation.leibniz_inv,Derivation.leibniz,hx,hy,hu,hv,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat,sub_zero]
    norm_num only
    generalize hd : x-u=d at *
    field_simp [h]
    rw [← hd]
    ring
  rw [hp,hq] at hi
  linear_combination hi

end CrossedEllipticTranslation
end
end

/- Source component: EllipticTranslationCommutation. -/
section

noncomputable section
namespace CrossedElliptic
open Polynomial HoldoutConstruction CrossedEllipticTranslation

section Polynomial
variable {R F L : Type*} [CommRing R] [Field F] [Field L]
lemma polynomial_intertwines (θ : R →+* F) (φ : F →+* L)
    (D : Derivation ℤ F F) (E : Derivation ℤ L L) (z : F)
    (hC : ∀ c,E (φ (θ c))=φ (D (θ c))) (hX : E (φ z)=φ (D z))
    (p : R[X]) : E (φ (p.eval₂ θ z))=φ (D (p.eval₂ θ z)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval₂_add,map_add,hp,hq]
  | monomial n c =>
    simp only [eval₂_monomial,map_mul,Derivation.leibniz,Derivation.leibniz_pow,
      map_add,map_pow,smul_eq_mul,nsmul_eq_mul,map_natCast,hC,hX]
end Polynomial

variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

lemma polynomial_field_image (p : K[X]) :
    algebraMap (RatFunc K) (E K) (algebraMap K[X] (RatFunc K) p)=
      p.eval₂ (algebraMap K (E K)) (x K) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,eval₂_add,hp,hq]
  | monomial n c =>
    simp only [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,RatFunc.algebraMap_C,
      map_constant,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X]
    rfl

lemma field_intertwines {L : Type*} [Field L] (φ : E K →+* L)
    (D : Derivation ℤ (E K) (E K)) (E' : Derivation ℤ L L)
    (hC : ∀ c,E' (φ (algebraMap K (E K) c))=φ (D (algebraMap K (E K) c)))
    (hX : E' (φ (x K))=φ (D (x K))) (hY : E' (φ (y K))=φ (D (y K)))
    (f : E K) : E' (φ f)=φ (D f) := by
  have hpoly (p : K[X]) :
      E' (φ (algebraMap (RatFunc K) (E K) (algebraMap K[X] (RatFunc K) p)))=
      φ (D (algebraMap (RatFunc K) (E K) (algebraMap K[X] (RatFunc K) p))) := by
    rw [polynomial_field_image]
    exact polynomial_intertwines (algebraMap K (E K)) φ D E' (x K) hC hX p
  have hcoeff (r : RatFunc K) : E' (φ (algebraMap (RatFunc K) (E K) r))=
      φ (D (algebraMap (RatFunc K) (E K) r)) := by
    induction r using RatFunc.induction_on with
    | f P Q hQ =>
      simp only [map_div₀,Derivation.leibniz_div,smul_eq_mul,map_mul,map_sub,map_pow,map_inv₀,hpoly]
  induction f using AdjoinRoot.induction_on with
  | ih p =>
    rw [← AdjoinRoot.aeval_eq,Polynomial.aeval_def]
    exact polynomial_intertwines (algebraMap (RatFunc K) (E K)) φ D E' (y K) hcoeff hY p

lemma delta_base (c : K) : delta (K:=K) (algebraMap K (E K) c)=0 := by
  rw [delta,Derivation.smul_apply,IsScalarTower.algebraMap_apply K (RatFunc K) (E K),time_base]
  change (-y K/3) • algebraMap (RatFunc K) (E K) (baseTime (RatFunc.C c))=0
  rw [baseTime_C,map_zero,smul_zero]

theorem translateMap_delta (u v : K) (hp : v^2=u^3-432) (f : E K) :
    delta (translateMap K u v hp f)=translateMap K u v hp (delta f) := by
  apply field_intertwines (translateMap K u v hp) delta delta
  · intro c
    rw [translateMap_base,delta_base,map_zero]
  · rw [translateMap_x,delta_x,map_div₀,map_neg,translateMap_y]
    have hc : translateMap K u v hp (3 : E K)=(3 : E K) := map_natCast _ 3
    rw [hc]
    exact translatedX_derivation delta _ _ _ _ (x_sub_constant_ne_zero K u) delta_x delta_y
      (delta_base u) (delta_base v) (relation K) (by
        have h := congrArg (algebraMap K (E K)) hp
        have h432 : algebraMap K (E K) (432 : K)=(432 : E K) := map_natCast _ 432
        simpa only [map_pow,map_sub,h432] using h)
  · rw [translateMap_y,delta_y,map_div₀,map_neg,map_pow,translateMap_x]
    have hc : translateMap K u v hp (2 : E K)=(2 : E K) := map_natCast _ 2
    rw [hc]
    exact translatedY_derivation delta _ _ _ _ (x_sub_constant_ne_zero K u) delta_x delta_y
      (delta_base u) (delta_base v) (relation K) (by
        have h := congrArg (algebraMap K (E K)) hp
        have h432 : algebraMap K (E K) (432 : K)=(432 : E K) := map_natCast _ 432
        simpa only [map_pow,map_sub,h432] using h)

lemma coefficient_scalar (D : Derivation ℤ K K) (c : K) :
    coefficient D (algebraMap K (E K) c)=algebraMap K (E K) (D c) := by
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) (E K),coefficient_base]
  rw [RatFunc.algebraMap_eq_C,baseCoefficient_C,map_constant]

lemma coefficient_translateX (D : Derivation ℤ K K) (u v : K) (hu : D u=0) (hv : D v=0) :
    coefficient D (translateX K u v)=0 := by
  simp [translateX,translatedX,slope,map_sub,Derivation.leibniz_pow,Derivation.leibniz_div,
    coefficient_x,coefficient_y,coefficient_scalar,hu,hv]

lemma coefficient_translateY (D : Derivation ℤ K K) (u v : K) (hu : D u=0) (hv : D v=0) :
    coefficient D (translateY K u v)=0 := by
  simp [translateY,translatedY,translatedX,slope,map_sub,map_add,map_neg,Derivation.leibniz_pow,
    Derivation.leibniz,Derivation.leibniz_div,coefficient_x,coefficient_y,coefficient_scalar,hu,hv]

theorem translateMap_coefficient (D : Derivation ℤ K K) (u v : K) (hp : v^2=u^3-432)
    (hu : D u=0) (hv : D v=0) (f : E K) :
    coefficient D (translateMap K u v hp f)=translateMap K u v hp (coefficient D f) := by
  apply field_intertwines (translateMap K u v hp) (coefficient D) (coefficient D)
  · intro c
    rw [translateMap_base,coefficient_scalar,translateMap_base]
  · rw [translateMap_x,coefficient_translateX D u v hu hv,coefficient_x,map_zero]
  · rw [translateMap_y,coefficient_translateY D u v hu hv,coefficient_y,map_zero]

end CrossedElliptic
end
end
