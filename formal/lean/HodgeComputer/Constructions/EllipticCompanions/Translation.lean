import HodgeComputer.Constructions.EllipticCompanions.Kernels

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

/- Source component: EllipticFibreRegular. -/
section

noncomputable section
namespace CrossedElliptic
open Polynomial CrossedRationalResidue
variable {K : Type*} [Field K] [CharZero K]

/-- Regularity on both branches of a finite x fibre. -/
def FibreRegular (r : K) (f : E K) : Prop := RegularAt r (first K f) ∧ RegularAt r (second K f)

def fibreValue (r s : K) : E K →ₗ[K] K :=
  ((valueAt r).comp ((first K).restrictScalars K))+
    s • ((valueAt r).comp ((second K).restrictScalars K))
lemma fibreValue_apply (r s : K) (f : E K) :
    fibreValue r s f=valueAt r (first K f)+s*valueAt r (second K f) := rfl

lemma mul_expansion (f g : E K) : f*g=algebraMap (RatFunc K) (E K)
      (first K f*first K g+((RatFunc.X : RatFunc K)^3-432)*second K f*second K g)+
      algebraMap (RatFunc K) (E K) (first K f*second K g+second K f*first K g)*y K := by
  conv_lhs => rw [first_second_expansion K f,first_second_expansion K g]
  simp only [map_add,map_mul,map_pow,map_sub,map_ofNat]
  have hr := relation K
  change (y K)^2=(algebraMap (RatFunc K) (E K) RatFunc.X)^3-432 at hr
  linear_combination algebraMap (RatFunc K) (E K) (second K f)*
    algebraMap (RatFunc K) (E K) (second K g)*hr

lemma first_mul (f g : E K) : first K (f*g)=first K f*first K g+
    ((RatFunc.X : RatFunc K)^3-432)*second K f*second K g := by
  rw [mul_expansion,map_add,first_algebraMap,first_coeff_y,add_zero]
lemma second_mul (f g : E K) : second K (f*g)=first K f*second K g+second K f*first K g := by
  rw [mul_expansion,map_add,second_algebraMap,second_coeff_y,zero_add]

lemma FibreRegular.add {r : K} {f g : E K} (hf : FibreRegular r f) (hg : FibreRegular r g) :
    FibreRegular r (f+g) := by
  constructor <;> rw [map_add]
  · exact hf.1.add hg.1
  · exact hf.2.add hg.2
lemma FibreRegular.neg {r : K} {f : E K} (hf : FibreRegular r f) : FibreRegular r (-f) := by
  constructor <;> rw [map_neg]
  · exact hf.1.neg
  · exact hf.2.neg
lemma FibreRegular.mul {r : K} {f g : E K} (hf : FibreRegular r f) (hg : FibreRegular r g) :
    FibreRegular r (f*g) := by
  have hc : RegularAt r ((RatFunc.X : RatFunc K)^3-432) := by
    convert RegularAt.polynomial r (X^3-C (432 : K)) using 1 <;> simp [map_ofNat]
  exact ⟨by rw [first_mul]; exact (hf.1.mul hg.1).add ((hc.mul hf.2).mul hg.2),
    by rw [second_mul]; exact (hf.1.mul hg.2).add (hf.2.mul hg.1)⟩
lemma FibreRegular.rational (r : K) (f : RatFunc K) (hf : RegularAt r f) :
    FibreRegular r (algebraMap (RatFunc K) (E K) f) := by
  rw [FibreRegular,first_algebraMap,second_algebraMap]
  exact ⟨hf,(by simpa using RegularAt.C r (0 : K))⟩
lemma FibreRegular.base (r c : K) : FibreRegular r (algebraMap K (E K) c) := by
  rw [← map_constant]
  exact FibreRegular.rational r _ (RegularAt.C r c)
lemma FibreRegular.one (r : K) : FibreRegular r (1 : E K) := by
  simpa using FibreRegular.base r (1 : K)
lemma FibreRegular.y (r : K) : FibreRegular r (y K) := by
  rw [FibreRegular,first_y,second_y]
  exact ⟨(by simpa using RegularAt.C r (0 : K)),by simpa using RegularAt.C r (1 : K)⟩
lemma FibreRegular.x (r : K) : FibreRegular r (x K) :=
  FibreRegular.rational r _ (RegularAt.polynomial r X)
lemma FibreRegular.pow {r : K} {f : E K} (hf : FibreRegular r f) (n : ℕ) : FibreRegular r (f^n) := by
  induction n with
  | zero => simpa using FibreRegular.one r
  | succ n h => rw [pow_succ]; exact h.mul hf

lemma fibreValue_mul (r s : K) (hs : s^2=r^3-432) (f g : E K)
    (hf : FibreRegular r f) (hg : FibreRegular r g) :
    fibreValue r s (f*g)=fibreValue r s f*fibreValue r s g := by
  have hc : RegularAt r ((RatFunc.X : RatFunc K)^3-432) := by
    convert RegularAt.polynomial r (X^3-C (432 : K)) using 1 <;> simp [map_ofNat]
  have hv : valueAt r ((RatFunc.X : RatFunc K)^3-432)=r^3-432 := by
    convert valueAt_polynomial r (X^3-C (432 : K)) using 1 <;> simp [map_ofNat]
  simp only [fibreValue_apply,first_mul,second_mul,map_add,
    valueAt_mul hf.1 hg.1,valueAt_mul (hc.mul hf.2) hg.2,valueAt_mul hc hf.2,
    valueAt_mul hf.1 hg.2,valueAt_mul hf.2 hg.1,hv]
  linear_combination -valueAt r (second K f)*valueAt r (second K g)*hs

lemma fibreValue_base (r s c : K) : fibreValue r s (algebraMap K (E K) c)=c := by
  rw [← map_constant,fibreValue_apply,first_algebraMap,second_algebraMap,valueAt_C,map_zero,mul_zero,add_zero]
lemma fibreValue_one (r s : K) : fibreValue r s (1 : E K)=1 := by
  simpa using fibreValue_base r s (1 : K)
lemma fibreValue_x (r s : K) : fibreValue r s (x K)=r := by
  rw [x,fibreValue_apply,first_algebraMap,second_algebraMap,map_zero,mul_zero,add_zero]
  simpa using valueAt_polynomial r X
lemma fibreValue_y (r s : K) : fibreValue r s (y K)=s := by
  rw [fibreValue_apply,first_y,second_y,map_zero]
  have h1 : valueAt r (1 : RatFunc K)=1 := by simpa using valueAt_C r (1 : K)
  rw [h1,mul_one,zero_add]

end CrossedElliptic
end
end

/- Source component: EllipticFibreInverse. -/
section

noncomputable section
namespace CrossedElliptic
open Polynomial CrossedRationalResidue
variable {K : Type*} [Field K] [CharZero K]

lemma conjugate_root : (equation K).eval₂ (algebraMap (RatFunc K) (E K)) (-y K)=0 := by
  conv_lhs => arg 3; rw [equation_eq]
  simp only [Polynomial.eval₂_sub,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_C,Polynomial.eval₂_ofNat,
    map_sub,map_pow,map_ofNat,neg_sq]
  exact sub_eq_zero.mpr (relation K)
def conjugate : E K →+* E K :=
  AdjoinRoot.lift (algebraMap (RatFunc K) (E K)) (-y K) conjugate_root
lemma conjugate_rational (f : RatFunc K) :
    conjugate (algebraMap (RatFunc K) (E K) f)=algebraMap (RatFunc K) (E K) f :=
  AdjoinRoot.lift_of conjugate_root
lemma conjugate_y : conjugate (y K)= -y K := AdjoinRoot.lift_root conjugate_root
lemma conjugate_expansion (f : E K) :
    conjugate f=algebraMap (RatFunc K) (E K) (first K f)-
      algebraMap (RatFunc K) (E K) (second K f)*y K := by
  conv_lhs => rw [first_second_expansion K f]
  rw [map_add,map_mul,conjugate_rational,conjugate_rational,conjugate_y]
  ring

def fibreNorm (f : E K) : RatFunc K := (first K f)^2-
  ((RatFunc.X : RatFunc K)^3-432)*(second K f)^2
lemma fibreNorm_product (f : E K) : algebraMap (RatFunc K) (E K) (fibreNorm f)=f*conjugate f := by
  rw [conjugate_expansion]
  conv_rhs => arg 1; rw [first_second_expansion K f]
  simp only [fibreNorm,map_sub,map_pow,map_mul,map_ofNat]
  have hr := relation K
  change (y K)^2=(algebraMap (RatFunc K) (E K) RatFunc.X)^3-432 at hr
  linear_combination (algebraMap (RatFunc K) (E K) (second K f))^2*hr
lemma fibreNorm_ne_zero {f : E K} (hf : f≠0) : fibreNorm f≠0 := by
  intro hn
  have hp := fibreNorm_product f
  rw [hn,map_zero] at hp
  have hc : conjugate f≠0 := (_root_.map_ne_zero _).mpr hf
  exact (mul_ne_zero hf hc) hp.symm

lemma inverse_expansion (f : E K) : f⁻¹=algebraMap (RatFunc K) (E K) (first K f/fibreNorm f)+
    algebraMap (RatFunc K) (E K) (-second K f/fibreNorm f)*y K := by
  by_cases hf : f=0
  · subst f
    simp [fibreNorm]
  have hn : algebraMap (RatFunc K) (E K) (fibreNorm f)≠0 :=
    (_root_.map_ne_zero _).mpr (fibreNorm_ne_zero hf)
  apply mul_right_cancel₀ hf
  rw [inv_mul_cancel₀ hf]
  simp only [map_div₀,map_neg]
  have hp := fibreNorm_product f
  rw [conjugate_expansion] at hp
  field_simp
  linear_combination hp

lemma FibreRegular.norm_regular {r : K} {f : E K} (hf : FibreRegular r f) :
    RegularAt r (fibreNorm f) := by
  have hc : RegularAt r ((RatFunc.X : RatFunc K)^3-432) := by
    convert RegularAt.polynomial r (X^3-C (432 : K)) using 1 <;> simp [map_ofNat]
  simpa only [fibreNorm,pow_two] using (hf.1.mul hf.1).sub (hc.mul (hf.2.mul hf.2))

lemma fibreNorm_value (r s : K) (hs : s^2=r^3-432) (f : E K) (hf : FibreRegular r f) :
    valueAt r (fibreNorm f)=fibreValue r s f*fibreValue r (-s) f := by
  have hc : RegularAt r ((RatFunc.X : RatFunc K)^3-432) := by
    convert RegularAt.polynomial r (X^3-C (432 : K)) using 1 <;> simp [map_ofNat]
  have hv : valueAt r ((RatFunc.X : RatFunc K)^3-432)=r^3-432 := by
    convert valueAt_polynomial r (X^3-C (432 : K)) using 1 <;> simp [map_ofNat]
  simp only [fibreNorm,pow_two,map_sub,valueAt_mul hf.1 hf.1,
    valueAt_mul hc (hf.2.mul hf.2),valueAt_mul hf.2 hf.2,hv,fibreValue_apply]
  linear_combination (valueAt r (second K f))^2*hs

lemma FibreRegular.inv {r : K} {f : E K} (hf : FibreRegular r f)
    (hn : valueAt r (fibreNorm f)≠0) : FibreRegular r f⁻¹ := by
  rw [inverse_expansion]
  exact (FibreRegular.rational r _ (hf.1.div hf.norm_regular hn)).add
    ((FibreRegular.rational r _ (hf.2.neg.div hf.norm_regular hn)).mul (FibreRegular.y r))

lemma FibreRegular.inv_of_values {r s : K} (hs : s^2=r^3-432) {f : E K} (hf : FibreRegular r f)
    (hplus : fibreValue r s f≠0) (hminus : fibreValue r (-s) f≠0) : FibreRegular r f⁻¹ := by
  apply hf.inv
  rw [fibreNorm_value r s hs f hf]
  exact mul_ne_zero hplus hminus

lemma fibreValue_inv (r s : K) (hs : s^2=r^3-432) (f : E K)
    (hf : FibreRegular r f) (hn : valueAt r (fibreNorm f)≠0) :
    fibreValue r s f⁻¹=(fibreValue r s f)⁻¹ := by
  have hf0 : f≠0 := by intro h; subst f; simp [fibreNorm] at hn
  have hp := fibreValue_mul r s hs f f⁻¹ hf (hf.inv hn)
  rw [mul_inv_cancel₀ hf0,fibreValue_one] at hp
  exact eq_inv_of_mul_eq_one_right hp.symm

end CrossedElliptic
end
end

/- Source component: EllipticFibreSpecialization. -/
section

noncomputable section
set_option maxHeartbeats 800000
namespace CrossedElliptic
open Polynomial CrossedRationalResidue
variable {F L : Type*} [Field F] [Field L] [CharZero L]

/-- A simultaneous specialization on both branches with nonzero field images. -/
def FibreSpecializes (Φ : F →+* E L) (ψplus ψminus : F →+* L) (r s : L) (f : F) : Prop :=
  FibreRegular r (Φ f) ∧ fibreValue r s (Φ f)=ψplus f ∧ fibreValue r (-s) (Φ f)=ψminus f

lemma FibreSpecializes.add (Φ : F →+* E L) (ψplus ψminus : F →+* L) (r s : L)
    {f g : F} (hf : FibreSpecializes Φ ψplus ψminus r s f)
    (hg : FibreSpecializes Φ ψplus ψminus r s g) : FibreSpecializes Φ ψplus ψminus r s (f+g) := by
  refine ⟨by rw [map_add]; exact hf.1.add hg.1,?_,?_⟩
  · rw [map_add,map_add,hf.2.1,hg.2.1,map_add]
  · rw [map_add,map_add,hf.2.2,hg.2.2,map_add]
lemma FibreSpecializes.mul (Φ : F →+* E L) (ψplus ψminus : F →+* L) (r s : L) (hs : s^2=r^3-432)
    {f g : F} (hf : FibreSpecializes Φ ψplus ψminus r s f)
    (hg : FibreSpecializes Φ ψplus ψminus r s g) : FibreSpecializes Φ ψplus ψminus r s (f*g) := by
  refine ⟨by rw [map_mul]; exact hf.1.mul hg.1,?_,?_⟩
  · rw [map_mul,fibreValue_mul r s hs _ _ hf.1 hg.1,hf.2.1,hg.2.1,map_mul]
  · rw [map_mul,fibreValue_mul r (-s) (by simpa using hs) _ _ hf.1 hg.1,hf.2.2,hg.2.2,map_mul]
lemma FibreSpecializes.one (Φ : F →+* E L) (ψplus ψminus : F →+* L) (r s : L) :
    FibreSpecializes Φ ψplus ψminus r s 1 := by
  simp only [FibreSpecializes,map_one,fibreValue_one,and_self,FibreRegular.one]
lemma FibreSpecializes.zero (Φ : F →+* E L) (ψplus ψminus : F →+* L) (r s : L) :
    FibreSpecializes Φ ψplus ψminus r s 0 := by
  have hr : FibreRegular r (0 : E L) := by simpa using FibreRegular.base r (0 : L)
  simp only [FibreSpecializes,map_zero,and_self,hr]
lemma FibreSpecializes.inv (Φ : F →+* E L) (ψplus ψminus : F →+* L) (r s : L) (hs : s^2=r^3-432)
    {f : F} (hf : FibreSpecializes Φ ψplus ψminus r s f) : FibreSpecializes Φ ψplus ψminus r s f⁻¹ := by
  by_cases hf0 : f=0
  · subst f; simpa using FibreSpecializes.zero Φ ψplus ψminus r s
  have hp : fibreValue r s (Φ f)≠0 := by rw [hf.2.1]; exact (_root_.map_ne_zero _).mpr hf0
  have hm : fibreValue r (-s) (Φ f)≠0 := by rw [hf.2.2]; exact (_root_.map_ne_zero _).mpr hf0
  have hn : valueAt r (fibreNorm (Φ f))≠0 := by
    rw [fibreNorm_value r s hs _ hf.1]; exact mul_ne_zero hp hm
  refine ⟨by rw [map_inv₀]; exact hf.1.inv hn,?_,?_⟩
  · rw [map_inv₀,fibreValue_inv r s hs _ hf.1 hn,hf.2.1,map_inv₀]
  · rw [map_inv₀,fibreValue_inv r (-s) (by simpa using hs) _ hf.1 hn,hf.2.2,map_inv₀]
lemma FibreSpecializes.pow (Φ : F →+* E L) (ψplus ψminus : F →+* L) (r s : L) (hs : s^2=r^3-432)
    {f : F} (hf : FibreSpecializes Φ ψplus ψminus r s f) (n : ℕ) :
    FibreSpecializes Φ ψplus ψminus r s (f^n) := by
  induction n with
  | zero => simpa using FibreSpecializes.one Φ ψplus ψminus r s
  | succ n h => rw [pow_succ]; exact h.mul Φ ψplus ψminus r s hs hf


lemma polynomial_specialization {R : Type*} [CommRing R]
  (Φ : F →+* E L) (ψplus ψminus : F →+* L) (r s : L) (hs : s^2=r^3-432)
  (θ : R →+* F) (z : F)
    (hc : ∀ c,FibreSpecializes Φ ψplus ψminus r s (θ c))
    (hz : FibreSpecializes Φ ψplus ψminus r s z) (p : R[X]) :
    FibreSpecializes Φ ψplus ψminus r s (p.eval₂ θ z) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [eval₂_add]; exact hp.add Φ ψplus ψminus r s hq
  | monomial n c =>
    rw [eval₂_monomial]
    exact (hc c).mul Φ ψplus ψminus r s hs (hz.pow Φ ψplus ψminus r s hs n)

variable {K : Type*} [Field K] [CharZero K]

theorem field_specialization (Φ : E K →+* E L) (ψplus ψminus : E K →+* L)
    (r s : L) (hs : s^2=r^3-432)
    (hC : ∀ c,FibreSpecializes Φ ψplus ψminus r s (algebraMap K (E K) c))
    (hX : FibreSpecializes Φ ψplus ψminus r s (x K))
    (hY : FibreSpecializes Φ ψplus ψminus r s (y K)) (f : E K) :
    FibreSpecializes Φ ψplus ψminus r s f := by
  have hrational (v : RatFunc K) :
      FibreSpecializes Φ ψplus ψminus r s (algebraMap (RatFunc K) (E K) v) := by
    have hp (p : K[X]) : FibreSpecializes Φ ψplus ψminus r s
        (algebraMap (RatFunc K) (E K) (algebraMap K[X] (RatFunc K) p)) := by
      rw [polynomial_field_image (K:=K) p]
      exact polynomial_specialization Φ ψplus ψminus r s hs (R:=K) (algebraMap K (E K)) (x K) hC hX p
    induction v using RatFunc.induction_on with
    | f P Q hQ =>
      rw [map_div₀,div_eq_mul_inv]
      exact (hp P).mul Φ ψplus ψminus r s hs ((hp Q).inv Φ ψplus ψminus r s hs)
  induction f using AdjoinRoot.induction_on with
  | ih p =>
    rw [← AdjoinRoot.aeval_eq,Polynomial.aeval_def]
    exact polynomial_specialization Φ ψplus ψminus r s hs (R:=RatFunc K) (algebraMap (RatFunc K) (E K)) (y K) hrational hY p

end CrossedElliptic
end
end

/- Source component: EllipticLocalTranslation. -/
section

noncomputable section
namespace CrossedElliptic
open Polynomial CrossedRationalResidue CrossedEllipticTranslation
variable {K : Type*} [Field K] [CharZero K]

lemma FibreRegular.sub {r : K} {f g : E K} (hf : FibreRegular r f) (hg : FibreRegular r g) :
    FibreRegular r (f-g) := by simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma FibreRegular.div_of_values {r s : K} (hs : s^2=r^3-432) {f g : E K}
    (hf : FibreRegular r f) (hg : FibreRegular r g)
    (hp : fibreValue r s g≠0) (hm : fibreValue r (-s) g≠0) : FibreRegular r (f/g) := by
  rw [div_eq_mul_inv]; exact hf.mul (hg.inv_of_values hs hp hm)
lemma fibreValue_pow (r s : K) (hs : s^2=r^3-432) (f : E K)
    (hf : FibreRegular r f) (n : ℕ) : fibreValue r s (f^n)=(fibreValue r s f)^n := by
  induction n with
  | zero => simp [fibreValue_one]
  | succ n h => rw [pow_succ,fibreValue_mul r s hs _ _ (hf.pow n) hf,h,pow_succ]
lemma fibreValue_div (r s : K) (hs : s^2=r^3-432) (f g : E K)
    (hf : FibreRegular r f) (hg : FibreRegular r g)
    (hp : fibreValue r s g≠0) (hm : fibreValue r (-s) g≠0) :
    fibreValue r s (f/g)=fibreValue r s f/fibreValue r s g := by
  have hn : valueAt r (fibreNorm g)≠0 := by
    rw [fibreNorm_value r s hs _ hg]; exact mul_ne_zero hp hm
  rw [div_eq_mul_inv,fibreValue_mul r s hs _ _ hf (hg.inv hn),fibreValue_inv r s hs _ hg hn,
    div_eq_mul_inv]

lemma local_slope (r s u v : K) (hs : s^2=r^3-432) (hru : r≠u) :
    FibreRegular r (slope (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v)) ∧
    fibreValue r s (slope (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v))=
      slope r s u v := by
  have hy : FibreRegular r (y K-algebraMap K (E K) v) := (FibreRegular.y r).sub (FibreRegular.base r v)
  have hx : FibreRegular r (x K-algebraMap K (E K) u) := (FibreRegular.x r).sub (FibreRegular.base r u)
  have hp : fibreValue r s (x K-algebraMap K (E K) u)≠0 := by
    rw [map_sub,fibreValue_x,fibreValue_base]; exact sub_ne_zero.mpr hru
  have hm : fibreValue r (-s) (x K-algebraMap K (E K) u)≠0 := by
    rw [map_sub,fibreValue_x,fibreValue_base]; exact sub_ne_zero.mpr hru
  refine ⟨hy.div_of_values hs hx hp hm,?_⟩
  rw [slope,fibreValue_div r s hs _ _ hy hx hp hm,map_sub,map_sub,
    fibreValue_x,fibreValue_y,fibreValue_base,fibreValue_base]
  rfl

lemma local_translatedX (r s u v : K) (hs : s^2=r^3-432) (hru : r≠u) :
    FibreRegular r (translatedX (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v)) ∧
    fibreValue r s (translatedX (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v))=
      translatedX r s u v := by
  obtain ⟨hsl,hv⟩ := local_slope r s u v hs hru
  refine ⟨((hsl.pow 2).sub (FibreRegular.x r)).sub (FibreRegular.base r u),?_⟩
  rw [translatedX,map_sub,map_sub,fibreValue_pow r s hs _ hsl 2,hv,fibreValue_x,fibreValue_base]
  rfl
lemma local_translatedY (r s u v : K) (hs : s^2=r^3-432) (hru : r≠u) :
    FibreRegular r (translatedY (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v)) ∧
    fibreValue r s (translatedY (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v))=
      translatedY r s u v := by
  obtain ⟨hsl,hv⟩ := local_slope r s u v hs hru
  obtain ⟨htx,htv⟩ := local_translatedX r s u v hs hru
  refine ⟨(FibreRegular.y r).neg.add (hsl.mul ((FibreRegular.x r).sub htx)),?_⟩
  rw [translatedY,map_add,map_neg,fibreValue_mul r s hs _ _ hsl ((FibreRegular.x r).sub htx),
    map_sub,hv,htv,fibreValue_x,fibreValue_y]
  rfl

lemma translatedX_symmetric (x y u v : K) : translatedX x y u v=translatedX u v x y := by
  unfold translatedX slope
  by_cases hd : x=u
  · subst x; simp
  · field_simp [sub_ne_zero.mpr hd,sub_ne_zero.mpr (Ne.symm hd)]; ring
lemma translatedY_symmetric (x y u v : K) (hd : x≠u) :
    translatedY x y u v=translatedY u v x y := by
  unfold translatedY translatedX slope
  field_simp [sub_ne_zero.mpr hd,sub_ne_zero.mpr (Ne.symm hd)]
  ring

end CrossedElliptic
end
end

/- Source component: EllipticGenericTranslation. -/
section

noncomputable section
set_option maxHeartbeats 400000
namespace CrossedElliptic
open Polynomial CrossedRationalResidue CrossedEllipticTranslation
variable (K : Type*) [Field K] [CharZero K]

def genericTranslate : E K →+* E (E K) :=
  (translateMap (E K) (x K) (y K) (relation K)).comp
    (CrossedEllipticBaseChange.map (algebraMap K (E K)))

lemma genericTranslate_base (c : K) : genericTranslate K (algebraMap K (E K) c)=
    algebraMap (E K) (E (E K)) (algebraMap K (E K) c) := by
  rw [genericTranslate,RingHom.comp_apply,CrossedEllipticBaseChange.map_base,translateMap_base]
lemma genericTranslate_x : genericTranslate K (x K)=
    translatedX (x (E K)) (y (E K)) (algebraMap (E K) (E (E K)) (x K))
      (algebraMap (E K) (E (E K)) (y K)) := by
  rw [genericTranslate,RingHom.comp_apply,CrossedEllipticBaseChange.map_x,translateMap_x]
  rfl
lemma genericTranslate_y : genericTranslate K (y K)=
    translatedY (x (E K)) (y (E K)) (algebraMap (E K) (E (E K)) (x K))
      (algebraMap (E K) (E (E K)) (y K)) := by
  rw [genericTranslate,RingHom.comp_apply,CrossedEllipticBaseChange.map_y,translateMap_y]
  rfl

lemma genericTranslate_delta (f : E K) : delta (genericTranslate K f)=genericTranslate K (delta f) := by
  rw [genericTranslate,RingHom.comp_apply,translateMap_delta,CrossedEllipticBaseChange.map_delta]
  rfl
lemma genericTranslate_coefficient (D : Derivation ℤ K K) (f : E K) :
    coefficient (coefficient D) (genericTranslate K f)=genericTranslate K (coefficient D f) := by
  rw [genericTranslate,RingHom.comp_apply,translateMap_coefficient _ _ _ _ (coefficient_x D) (coefficient_y D)]
  rw [CrossedEllipticBaseChange.map_coefficient _ D (coefficient D) (coefficient_scalar D)]
  rfl

/-- An independent translating point avoids every old rational point simultaneously. -/
theorem genericTranslate_specializes (r s : K) (hs : s^2=r^3-432) (f : E K) :
    FibreSpecializes (genericTranslate K) (translateMap K r s hs)
      (translateMap K r (-s) (by simpa using hs))
      (algebraMap K (E K) r) (algebraMap K (E K) s) f := by
  let R := algebraMap K (E K) r
  let S := algebraMap K (E K) s
  have hpoint : S^2=R^3-432 := by
    have h := congrArg (algebraMap K (E K)) hs
    simpa only [map_pow,map_sub,map_ofNat] using h
  have hru : R≠x K := by
    intro he
    exact x_sub_constant_ne_zero K r (sub_eq_zero.mpr he.symm)
  apply field_specialization _ _ _ R S hpoint
  · intro c
    refine ⟨?_,?_,?_⟩
    · rw [genericTranslate_base]; exact FibreRegular.base R _
    · rw [genericTranslate_base,fibreValue_base,translateMap_base]
    · rw [genericTranslate_base,fibreValue_base,translateMap_base]
  · refine ⟨?_,?_,?_⟩
    · rw [genericTranslate_x]
      exact (local_translatedX R S (x K) (y K) hpoint hru).1
    · rw [genericTranslate_x,translateMap_x]
      change fibreValue R S _=translatedX (x K) (y K) R S
      rw [(local_translatedX R S (x K) (y K) hpoint hru).2,translatedX_symmetric]
    · rw [genericTranslate_x,translateMap_x]
      simp only [translateX,map_neg]
      change fibreValue R (-S) _=translatedX (x K) (y K) R (-S)
      rw [(local_translatedX R (-S) (x K) (y K) (by simpa using hpoint) hru).2,translatedX_symmetric]
  · refine ⟨?_,?_,?_⟩
    · rw [genericTranslate_y]
      exact (local_translatedY R S (x K) (y K) hpoint hru).1
    · rw [genericTranslate_y,translateMap_y]
      change fibreValue R S _=translatedY (x K) (y K) R S
      rw [(local_translatedY R S (x K) (y K) hpoint hru).2,translatedY_symmetric _ _ _ _ hru]
    · rw [genericTranslate_y,translateMap_y]
      simp only [translateY,map_neg]
      change fibreValue R (-S) _=translatedY (x K) (y K) R (-S)
      rw [(local_translatedY R (-S) (x K) (y K) (by simpa using hpoint) hru).2,
        translatedY_symmetric _ _ _ _ hru]

end CrossedElliptic
end
end

/- Source component: EllipticBasisDifferentiation. -/
section

noncomputable section
namespace CrossedElliptic
open Polynomial HoldoutConstruction
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

lemma coefficient_basis_expansion (D : Derivation ℤ K K) (f : E K) :
    coefficient D f=algebraMap (RatFunc K) (E K) (baseCoefficient D (first K f))+
      algebraMap (RatFunc K) (E K) (baseCoefficient D (second K f))*y K := by
  have h := congrArg (coefficient D) (first_second_expansion K f)
  simp only [map_add,Derivation.leibniz,coefficient_base,coefficient_y,smul_eq_mul,
    mul_zero,add_zero] at h
  linear_combination h

lemma first_coefficient (D : Derivation ℤ K K) (f : E K) :
    first K (coefficient D f)=baseCoefficient D (first K f) := by
  rw [coefficient_basis_expansion,map_add,first_algebraMap,first_coeff_y,add_zero]
lemma second_coefficient (D : Derivation ℤ K K) (f : E K) :
    second K (coefficient D f)=baseCoefficient D (second K f) := by
  rw [coefficient_basis_expansion,map_add,second_algebraMap,second_coeff_y,zero_add]

lemma delta_rational (f : RatFunc K) :
    delta (K:=K) (algebraMap (RatFunc K) (E K) f)=
      (-y K/3)*algebraMap (RatFunc K) (E K) (baseTime f) := by
  rw [delta,Derivation.smul_apply,time_base]
  rfl

lemma delta_basis_expansion (f : E K) :
    delta f=algebraMap (RatFunc K) (E K)
      (-((RatFunc.X : RatFunc K)^3-432)/3*baseTime (second K f)-
        RatFunc.X^2/2*second K f)+
      algebraMap (RatFunc K) (E K) (-baseTime (first K f)/3)*y K := by
  have h := congrArg (delta (K:=K)) (first_second_expansion K f)
  simp only [map_add,Derivation.leibniz,delta_rational,delta_y,smul_eq_mul] at h
  rw [h]
  have h432 : algebraMap (RatFunc K) (E K) (432 : RatFunc K)=(432 : E K) := map_natCast _ 432
  have h3 : algebraMap (RatFunc K) (E K) (3 : RatFunc K)=(3 : E K) := map_natCast _ 3
  have h2 : algebraMap (RatFunc K) (E K) (2 : RatFunc K)=(2 : E K) := map_natCast _ 2
  simp only [map_sub,map_add,map_mul,map_pow,map_neg,map_div₀,h432,h3,h2]
  have hr := relation K
  dsimp only [x] at hr
  dsimp only [x]
  field_simp
  linear_combination -2*algebraMap (RatFunc K) (E K) (baseTime (second K f))*hr

lemma first_delta (f : E K) : first K (delta f)=
    -((RatFunc.X : RatFunc K)^3-432)/3*baseTime (second K f)-RatFunc.X^2/2*second K f := by
  rw [delta_basis_expansion,map_add,first_algebraMap,first_coeff_y,add_zero]
lemma second_delta (f : E K) : second K (delta f)= -baseTime (first K f)/3 := by
  rw [delta_basis_expansion,map_add,second_algebraMap,second_coeff_y,zero_add]

end CrossedElliptic
end
end

/- Source component: EllipticThetaEvaluation. -/
section

noncomputable section
namespace CrossedRationalResidue
open Polynomial CrossedElliptic
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

lemma valueAt_coefficient (r : K) (D : Derivation ℤ K K) (hr : D r=0) (f : RatFunc K) :
    valueAt r (baseCoefficient D f)=D (valueAt r f) := by
  rw [← residue_div_uniformizer,← residue_div_uniformizer]
  have hu : baseCoefficient D (uniformizer r)=0 := by
    simp [uniformizer,baseCoefficient_X,baseCoefficient_C,hr]
  have he : baseCoefficient D (f/uniformizer r)=baseCoefficient D f/uniformizer r := by
    rw [Derivation.leibniz_div_const _ _ _ hu]
    simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [← he,residue_coefficient]
lemma valueAt_polynomial_mul (r : K) (P : K[X]) (f : RatFunc K) (hf : RegularAt r f) :
    valueAt r (algebraMap K[X] (RatFunc K) P*f)=P.eval r*valueAt r f := by
  rw [valueAt_mul (RegularAt.polynomial r P) hf,valueAt_polynomial]

end CrossedRationalResidue
namespace CrossedElliptic
open Polynomial CrossedRationalResidue CrossedEllipticTheta
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

lemma fibreValue_coefficient (r s : K) (D : Derivation ℤ K K) (hr : D r=0) (hs : D s=0) (f : E K) :
    fibreValue r s (coefficient D f)=D (fibreValue r s f) := by
  simp only [fibreValue_apply,first_coefficient,second_coefficient,valueAt_coefficient r D hr,
    map_add,Derivation.leibniz,hs,smul_eq_mul,mul_zero,add_zero]

lemma theta_residue_delta (r : K) (hr : r^3=1728) (f : E K) (hf : FibreRegular r f) :
    residueAt r (thetaRatio*f)= -fibreValue r (-36) (delta f) := by
  have hc0 : (-(RatFunc.X^3-432)/3 : RatFunc K)=
      algebraMap K[X] (RatFunc K) (C (-1/3 : K)*(X^3-C (432 : K))) := by simp [map_ofNat]; ring
  have hc1 : (-(RatFunc.X^2)/2 : RatFunc K)=
      algebraMap K[X] (RatFunc K) (C (-1/2 : K)*X^2) := by simp [map_ofNat]; ring
  have hc3 : (-(1 : RatFunc K)/3)=RatFunc.C (-1/3 : K) := by simp [map_ofNat]
  have hlinear (c : K) (g : RatFunc K) : valueAt r (RatFunc.C c*g)=c*valueAt r g := by
    rw [← RatFunc.smul_eq_C_mul,map_smul,smul_eq_mul]
  change residue r (differentialTrace (thetaRatio*f))= -fibreValue r (-36) (delta f)
  rw [theta_trace,theta_trace_residue r hr _ _ hf.1 hf.2,fibreValue_apply,first_delta,second_delta]
  have hsecond : -(baseTime (first K f))/3=RatFunc.C (-1/3 : K)*baseTime (first K f) := by
    rw [← hc3]; ring
  have hfirst : -((RatFunc.X : RatFunc K)^3-432)/3*baseTime (second K f)-
      RatFunc.X^2/2*second K f=
      algebraMap K[X] (RatFunc K) (C (-1/3 : K)*(X^3-C (432 : K)))*baseTime (second K f)+
      algebraMap K[X] (RatFunc K) (C (-1/2 : K)*X^2)*second K f := by
    rw [← hc0,← hc1]; ring
  rw [hfirst,hsecond,map_add,valueAt_polynomial_mul r _ _ hf.2.time,
    valueAt_polynomial_mul r _ _ hf.2,hlinear]
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,
    Polynomial.eval_sub,hr]
  ring

end CrossedElliptic
end
end
