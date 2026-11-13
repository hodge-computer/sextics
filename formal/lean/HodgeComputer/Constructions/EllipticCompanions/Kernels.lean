import HodgeComputer.Constructions.EllipticCompanions.Calculus

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

/- Source component: RationalRegularAlgebra. -/
section

noncomputable section
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

lemma RegularAt.mul {a : K} {f g : RatFunc K} (hf : RegularAt a f) (hg : RegularAt a g) :
    RegularAt a (f*g) := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  obtain ⟨R,S,hS,rfl⟩ := hg
  refine ⟨P*R,Q*S,by simpa using mul_ne_zero hQ hS,?_⟩
  simp only [map_mul]
  ring

lemma RegularAt.neg {a : K} {f : RatFunc K} (hf : RegularAt a f) : RegularAt a (-f) := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  exact ⟨-P,Q,hQ,by simp only [map_neg,neg_div]⟩

lemma RegularAt.sub {a : K} {f g : RatFunc K} (hf : RegularAt a f) (hg : RegularAt a g) :
    RegularAt a (f-g) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma RegularAt.C (a c : K) : RegularAt a (RatFunc.C c) :=
  RegularAt.polynomial a (Polynomial.C c)

lemma valueAt_C (a c : K) : valueAt a (RatFunc.C c)=c := by
  have h := valueAt_div_polynomials a (Polynomial.C c) 1 (by simp)
  simpa using h

lemma valueAt_polynomial (a : K) (P : K[X]) :
    valueAt a (algebraMap K[X] (RatFunc K) P)=P.eval a := by
  have h := valueAt_div_polynomials a P 1 (by simp)
  simpa using h

lemma valueAt_mul {a : K} {f g : RatFunc K} (hf : RegularAt a f) (hg : RegularAt a g) :
    valueAt a (f*g)=valueAt a f*valueAt a g := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  obtain ⟨R,S,hS,rfl⟩ := hg
  have hm : algebraMap K[X] (RatFunc K) P/algebraMap K[X] (RatFunc K) Q*
      (algebraMap K[X] (RatFunc K) R/algebraMap K[X] (RatFunc K) S)=
      algebraMap K[X] (RatFunc K) (P*R)/algebraMap K[X] (RatFunc K) (Q*S) := by
    simp only [map_mul]
    ring
  rw [hm,valueAt_div_polynomials a (P*R) (Q*S) (by simpa using mul_ne_zero hQ hS),
    valueAt_div_polynomials a P Q hQ,valueAt_div_polynomials a R S hS]
  simp only [eval_mul]
  ring

lemma RegularAt.inv {a : K} {f : RatFunc K} (hf : RegularAt a f) (hn : valueAt a f≠0) :
    RegularAt a f⁻¹ := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  rw [valueAt_div_polynomials a P Q hQ] at hn
  have hP : P.eval a≠0 := by
    intro h; apply hn; rw [h,zero_div]
  exact ⟨Q,P,hP,by rw [inv_div]⟩

lemma RegularAt.div {a : K} {f g : RatFunc K} (hf : RegularAt a f) (hg : RegularAt a g)
    (hn : valueAt a g≠0) : RegularAt a (f/g) := by
  rw [div_eq_mul_inv]
  exact hf.mul (hg.inv hn)

lemma baseTime_polynomial [CharZero K] (P : K[X]) :
    CrossedElliptic.baseTime (algebraMap K[X] (RatFunc K) P)=
      algebraMap K[X] (RatFunc K) P.derivative :=
  HoldoutConstruction.extendRingDerivation_apply (L := RatFunc K)
    (HoldoutConstruction.timePolynomialDerivation (E := K)) P

lemma RegularAt.time [CharZero K] {a : K} {f : RatFunc K} (hf : RegularAt a f) :
    RegularAt a (CrossedElliptic.baseTime f) := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  refine ⟨P.derivative*Q-P*Q.derivative,Q^2,by simpa using pow_ne_zero 2 hQ,?_⟩
  rw [Derivation.leibniz_div,baseTime_polynomial,baseTime_polynomial]
  simp only [smul_eq_mul,map_sub,map_mul,map_pow]
  ring

end CrossedRationalResidue
end
end

/- Source component: EllipticThetaKernels. -/
section

noncomputable section
namespace CrossedEllipticTheta
open Polynomial CrossedRationalResidue
variable {K : Type*} [Field K] [CharZero K]

def cofactor (r : K) : K[X] := X^2+C r*X+C (r^2)
def remainderZero (r : K) : K[X] := 12*(-2*X^2-2*C r*X+C (r^2))
def remainderOne (r : K) : K[X] :=
  -C (r^2)*X^3+1728*X^2+1728*C r*X+864*C (r^2)
def kernelZero : RatFunc K := -36*RatFunc.X*(RatFunc.X^3+3456)/(RatFunc.X^3-1728)^2
def kernelOne : RatFunc K := 3888*RatFunc.X^4/(RatFunc.X^3-1728)^2

lemma root_ne_zero (r : K) (hr : r^3=1728) : r≠0 := by
  intro h; rw [h] at hr; norm_num at hr

omit [CharZero K] in
lemma cofactor_at_root (r : K) : (cofactor r).eval r=3*r^2 := by
  simp [cofactor]
  ring

lemma cofactor_at_root_ne_zero (r : K) (hr : r^3=1728) : (cofactor r).eval r≠0 := by
  rw [cofactor_at_root]
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (root_ne_zero r hr))

lemma cofactor_fraction_ne_zero (r : K) (hr : r^3=1728) :
    algebraMap K[X] (RatFunc K) (cofactor r)≠0 := by
  apply polynomialMap_ne_zero
  intro h
  apply cofactor_at_root_ne_zero r hr
  simp [h]

omit [CharZero K] in
lemma cubic_factor (r : K) (hr : r^3=1728) :
    (RatFunc.X : RatFunc K)^3-1728=uniformizer r*algebraMap K[X] (RatFunc K) (cofactor r) := by
  have h := congrArg (RatFunc.C : K →+* RatFunc K) hr
  have h1728 : RatFunc.C (1728 : K)=(1728 : RatFunc K) := map_natCast _ 1728
  rw [map_pow,h1728] at h
  simp only [uniformizer,cofactor,map_add,map_sub,map_mul,map_pow,RatFunc.algebraMap_X,RatFunc.algebraMap_C]
  linear_combination h

lemma kernelZero_decomposition (r : K) (hr : r^3=1728) :
    kernelZero (K:=K)= -12/(uniformizer r)^2+
      algebraMap K[X] (RatFunc K) (remainderZero r)/
        (algebraMap K[X] (RatFunc K) (cofactor r))^2 := by
  have hu := uniformizer_ne_zero r
  have hc := cofactor_fraction_ne_zero r hr
  have hn := congrArg (RatFunc.C : K →+* RatFunc K) hr
  have h1728 : RatFunc.C (1728 : K)=(1728 : RatFunc K) := map_natCast _ 1728
  have h12 : RatFunc.C (12 : K)=(12 : RatFunc K) := map_natCast _ 12
  have h2 : RatFunc.C (2 : K)=(2 : RatFunc K) := map_natCast _ 2
  have hp12 : algebraMap K[X] (RatFunc K) (12 : K[X])=(12 : RatFunc K) := map_natCast _ 12
  have hp2 : algebraMap K[X] (RatFunc K) (2 : K[X])=(2 : RatFunc K) := map_natCast _ 2
  rw [map_pow,h1728] at hn
  rw [kernelZero,cubic_factor r hr]
  simp only [uniformizer,cofactor,remainderZero,map_mul,map_sub,map_add,map_pow,map_neg,
    RatFunc.algebraMap_X,RatFunc.algebraMap_C,hp12,hp2]
  have hu' : (RatFunc.X : RatFunc K)-RatFunc.C r≠0 := by simpa [uniformizer] using hu
  have hc' : (RatFunc.X : RatFunc K)^2+RatFunc.C r*RatFunc.X+(RatFunc.C r)^2≠0 := by
    simpa [cofactor] using hc
  generalize hd : (RatFunc.X : RatFunc K)-RatFunc.C r=d at *
  generalize hq : (RatFunc.X : RatFunc K)^2+RatFunc.C r*RatFunc.X+(RatFunc.C r)^2=c at *
  field_simp [hu',hc']
  rw [← hd,← hq]
  linear_combination 72*(RatFunc.X : RatFunc K)*hn

lemma kernelOne_decomposition (r : K) (hr : r^3=1728) :
    2*kernelOne (K:=K)=864/(uniformizer r)^2+RatFunc.C (r^2)/uniformizer r+
      algebraMap K[X] (RatFunc K) (remainderOne r)/
        (algebraMap K[X] (RatFunc K) (cofactor r))^2 := by
  have hu := uniformizer_ne_zero r
  have hc := cofactor_fraction_ne_zero r hr
  have hn := congrArg (RatFunc.C : K →+* RatFunc K) hr
  have h1728 : RatFunc.C (1728 : K)=(1728 : RatFunc K) := map_natCast _ 1728
  have h864 : RatFunc.C (864 : K)=(864 : RatFunc K) := map_natCast _ 864
  have hp1728 : algebraMap K[X] (RatFunc K) (1728 : K[X])=(1728 : RatFunc K) := map_natCast _ 1728
  have hp864 : algebraMap K[X] (RatFunc K) (864 : K[X])=(864 : RatFunc K) := map_natCast _ 864
  rw [map_pow,h1728] at hn
  rw [kernelOne,cubic_factor r hr]
  simp only [uniformizer,cofactor,remainderOne,map_mul,map_sub,map_add,map_pow,map_neg,
    RatFunc.algebraMap_X,RatFunc.algebraMap_C,hp1728,hp864]
  have hu' : (RatFunc.X : RatFunc K)-RatFunc.C r≠0 := by simpa [uniformizer] using hu
  have hc' : (RatFunc.X : RatFunc K)^2+RatFunc.C r*RatFunc.X+(RatFunc.C r)^2≠0 := by
    simpa [cofactor] using hc
  generalize hd : (RatFunc.X : RatFunc K)-RatFunc.C r=d at *
  generalize hq : (RatFunc.X : RatFunc K)^2+RatFunc.C r*RatFunc.X+(RatFunc.C r)^2=c at *
  field_simp [hu',hc']
  rw [← hd,← hq]
  linear_combination ((RatFunc.C r)^4+(RatFunc.C r)^3*RatFunc.X+
    (RatFunc.C r)^2*RatFunc.X^2-3*RatFunc.X^4)*hn

lemma remainder_regular (r : K) (hr : r^3=1728) (P : K[X]) :
    RegularAt r (algebraMap K[X] (RatFunc K) P/
      (algebraMap K[X] (RatFunc K) (cofactor r))^2) := by
  refine ⟨P,(cofactor r)^2,by simpa using pow_ne_zero 2 (cofactor_at_root_ne_zero r hr),?_⟩
  rw [map_pow]

end CrossedEllipticTheta
end
end

/- Source component: EllipticThetaLocalPairing. -/
section

noncomputable section
namespace CrossedEllipticTheta
open Polynomial CrossedRationalResidue CrossedElliptic
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

omit [CharZero K] in
lemma residue_C_mul (r c : K) (f : RatFunc K) :
    residue r (RatFunc.C c*f)=c*residue r f := by
  rw [← RatFunc.smul_eq_C_mul,map_smul,smul_eq_mul]

lemma kernelZero_residue (r : K) (hr : r^3=1728) (f : RatFunc K) (hf : RegularAt r f) :
    residue r (f*kernelZero)= -12*valueAt r (baseTime f) := by
  rw [kernelZero_decomposition r hr,mul_add,map_add]
  have hrem := (hf.mul (remainder_regular r hr (remainderZero r))).residue_eq_zero
  rw [hrem,add_zero]
  have hc : RatFunc.C (-12 : K)=(-12 : RatFunc K) := by
    rw [map_neg]
    congr 1
    exact map_natCast _ 12
  have he : f*(-12/(uniformizer r)^2)=RatFunc.C (-12 : K)*(f/(uniformizer r)^2) := by
    rw [hc]
    ring
  rw [he,residue_C_mul,residue_div_uniformizer_sq r baseTime baseTime_C baseTime_X]

lemma kernelOne_residue (r : K) (hr : r^3=1728) (f : RatFunc K) (hf : RegularAt r f) :
    residue r (f*kernelOne)=432*valueAt r (baseTime f)+(r^2/2)*valueAt r f := by
  have hd := kernelOne_decomposition r hr
  have h2 : RatFunc.C (2 : K)=(2 : RatFunc K) := map_natCast _ 2
  have h864 : RatFunc.C (864 : K)=(864 : RatFunc K) := map_natCast _ 864
  have he : RatFunc.C (2 : K)*(f*kernelOne)=
      RatFunc.C (864 : K)*(f/(uniformizer r)^2)+RatFunc.C (r^2)*(f/uniformizer r)+
      f*(algebraMap K[X] (RatFunc K) (remainderOne r)/
        (algebraMap K[X] (RatFunc K) (cofactor r))^2) := by
    rw [h2,h864]
    calc
      2*(f*kernelOne)=f*(2*kernelOne) := by ring
      _=f*(864/(uniformizer r)^2+RatFunc.C (r^2)/uniformizer r+
          algebraMap K[X] (RatFunc K) (remainderOne r)/
            (algebraMap K[X] (RatFunc K) (cofactor r))^2) := by rw [hd]
      _=_ := by ring
  have hres := congrArg (residue r) he
  have hrem := (hf.mul (remainder_regular r hr (remainderOne r))).residue_eq_zero
  rw [map_add,map_add,residue_C_mul,residue_C_mul,residue_C_mul,
    residue_div_uniformizer_sq r baseTime baseTime_C baseTime_X,residue_div_uniformizer,hrem,add_zero] at hres
  linear_combination hres/2

theorem theta_trace_residue (r : K) (hr : r^3=1728) (f0 f1 : RatFunc K)
    (h0 : RegularAt r f0) (h1 : RegularAt r f1) :
    residue r (f0*kernelZero+f1*kernelOne)=
      -12*valueAt r (baseTime f0)+432*valueAt r (baseTime f1)+(r^2/2)*valueAt r f1 := by
  rw [map_add,kernelZero_residue r hr f0 h0,kernelOne_residue r hr f1 h1]
  ring

end CrossedEllipticTheta
end
end

/- Source component: EllipticThetaTrace. -/
section

noncomputable section
namespace CrossedElliptic
open Polynomial CrossedRationalResidue CrossedEllipticTheta
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

omit [CharZero K] in
lemma first_y : first K (y K)=0 := by
  change (basis K).repr (y K) 0=0
  rw [← basis_one,(basis K).repr_self]
  simp
omit [CharZero K] in
lemma first_coeff_y (f : RatFunc K) : first K (algebraMap (RatFunc K) (E K) f*y K)=0 := by
  rw [← Algebra.smul_def,map_smul,first_y,smul_zero]

lemma y_add_scalar_ne_zero (c : K) : y K+algebraMap K (E K) c≠0 := by
  intro h
  have hs := congrArg (second K) h
  rw [← map_constant K c,map_add,second_y,second_algebraMap,map_zero,add_zero] at hs
  exact one_ne_zero hs

omit [CharZero K] in
lemma cubic_sub_constant_ne_zero (c : K) : (RatFunc.X : RatFunc K)^3-RatFunc.C c≠0 := by
  have h := polynomialMap_ne_zero (monic_X_pow_sub_C c (by decide : (3 : ℕ)≠0)).ne_zero
  simpa only [map_sub,map_pow,RatFunc.algebraMap_X,RatFunc.algebraMap_C] using h

lemma theta_density_rationalization {L : Type*} [Field L] [CharZero L]
    (x y : L) (hy : y≠0) (hp : y^2=x^3-432) (hy36 : y+36≠0)
    (hJ : x^3-1728≠0) :
    -18*x*(y-36)/(y*(y+36)^2)=
      -18*x*(x^3+3456)/(x^3-1728)^2+
      1944*x^4/((x^3-1728)^2*(x^3-432))*y := by
  have hx3 : x^3=y^2+432 := by linear_combination -hp
  have hx4 : x^4=x*(y^2+432) := by rw [show x^4=x*x^3 by ring,hx3]
  have hj : y^2-1296≠0 := by
    convert hJ using 1
    linear_combination hp
  rw [hx4,hx3]
  rw [show y^2+432-1728=y^2-1296 by ring,
    show y^2+432-432=y^2 by ring,
    show y^2+432+3456=y^2+3888 by ring]
  generalize hd : y^2-1296=d at *
  generalize hs : y+36=s at *
  field_simp [hy,hy36,hj]
  rw [← hd,← hs]
  ring

def thetaRatio : E K := b/(a^2)

lemma theta_density_decomposition : (-3/y K)*thetaRatio (K:=K)=
    algebraMap (RatFunc K) (E K) (kernelZero/2)+
      algebraMap (RatFunc K) (E K)
        (kernelOne/(2*((RatFunc.X : RatFunc K)^3-432)))*y K := by
  have hy := y_ne_zero (K:=K)
  have h36 : algebraMap K (E K) (36 : K)=(36 : E K) := map_natCast _ 36
  have hy36 : y K+36≠0 := by simpa only [h36] using y_add_scalar_ne_zero (K:=K) (36 : K)
  have hJ0 := cubic_sub_constant_ne_zero (K:=K) (1728 : K)
  have hc1728 : RatFunc.C (1728 : K)=(1728 : RatFunc K) := map_natCast _ 1728
  rw [hc1728] at hJ0
  have hJ : (x K)^3-1728≠0 := by
    have hm := (_root_.map_ne_zero (algebraMap (RatFunc K) (E K))).mpr hJ0
    have hc : algebraMap (RatFunc K) (E K) (1728 : RatFunc K)=(1728 : E K) := map_natCast _ 1728
    simpa only [map_sub,map_pow,hc,x] using hm
  have hs : (-3/y K)*thetaRatio (K:=K)= -18*x K*(y K-36)/(y K*(y K+36)^2) := by
    unfold thetaRatio a b
    field_simp [x_ne_zero K,hy,hy36]
    ring
  rw [hs,theta_density_rationalization (x K) (y K) hy (relation K) hy36 hJ]
  have h2 : algebraMap (RatFunc K) (E K) (2 : RatFunc K)=(2 : E K) := map_natCast _ 2
  have h36' : algebraMap (RatFunc K) (E K) (36 : RatFunc K)=(36 : E K) := map_natCast _ 36
  have h3456 : algebraMap (RatFunc K) (E K) (3456 : RatFunc K)=(3456 : E K) := map_natCast _ 3456
  have h1728 : algebraMap (RatFunc K) (E K) (1728 : RatFunc K)=(1728 : E K) := map_natCast _ 1728
  have h432 : algebraMap (RatFunc K) (E K) (432 : RatFunc K)=(432 : E K) := map_natCast _ 432
  have h3888 : algebraMap (RatFunc K) (E K) (3888 : RatFunc K)=(3888 : E K) := map_natCast _ 3888
  simp only [kernelZero,kernelOne,map_div₀,map_neg,map_mul,map_add,map_sub,map_pow,
    h2,h36',h3456,h1728,h432,h3888]
  change -18*x K*((x K)^3+3456)/((x K)^3-1728)^2+
    1944*(x K)^4/(((x K)^3-1728)^2*((x K)^3-432))*y K=
    (-36*x K*((x K)^3+3456)/((x K)^3-1728)^2)/2+
    (3888*(x K)^4/((x K)^3-1728)^2/(2*((x K)^3-432)))*y K
  have hF : (x K)^3-432≠0 := by rw [← relation K]; exact pow_ne_zero 2 hy
  generalize hd : (x K)^3-1728=d at *
  generalize he : (x K)^3-432=e at *
  field_simp [hJ,hF]
  ring

theorem theta_trace (f : E K) : differentialTrace (thetaRatio*f)=
    first K f*kernelZero+second K f*kernelOne := by
  rw [differentialTrace_apply,← mul_assoc,theta_density_decomposition]
  have hf : (algebraMap (RatFunc K) (E K) (kernelZero/2)+
      algebraMap (RatFunc K) (E K) (kernelOne/(2*((RatFunc.X : RatFunc K)^3-432)))*y K)*f=
      (algebraMap (RatFunc K) (E K) (kernelZero/2)+
      algebraMap (RatFunc K) (E K) (kernelOne/(2*((RatFunc.X : RatFunc K)^3-432)))*y K)*
      (algebraMap (RatFunc K) (E K) (first K f)+algebraMap (RatFunc K) (E K) (second K f)*y K) :=
    congrArg (fun z => (algebraMap (RatFunc K) (E K) (kernelZero/2)+
      algebraMap (RatFunc K) (E K) (kernelOne/(2*((RatFunc.X : RatFunc K)^3-432)))*y K)*z)
      (first_second_expansion K f)
  rw [hf]
  have he : (algebraMap (RatFunc K) (E K) (kernelZero/2)+
      algebraMap (RatFunc K) (E K) (kernelOne/(2*((RatFunc.X : RatFunc K)^3-432)))*y K)*
      (algebraMap (RatFunc K) (E K) (first K f)+algebraMap (RatFunc K) (E K) (second K f)*y K)=
      algebraMap (RatFunc K) (E K) (kernelZero/2*first K f+kernelOne/2*second K f)+
      algebraMap (RatFunc K) (E K)
        (kernelZero/2*second K f+kernelOne/(2*((RatFunc.X : RatFunc K)^3-432))*first K f)*y K := by
    have hr := relation K
    have hc432 : algebraMap (RatFunc K) (E K) (432 : RatFunc K)=(432 : E K) := map_natCast _ 432
    have hc2 : algebraMap (RatFunc K) (E K) (2 : RatFunc K)=(2 : E K) := map_natCast _ 2
    have hF := cubic_sub_constant_ne_zero (K:=K) (432 : K)
    have hC432 : RatFunc.C (432 : K)=(432 : RatFunc K) := map_natCast _ 432
    rw [hC432] at hF
    have heF : (x K)^3-432≠0 := by rw [← relation K]; exact pow_ne_zero 2 (y_ne_zero (K:=K))
    simp only [map_add,map_mul,map_div₀,map_sub,map_pow,hc432,hc2]
    dsimp only [x] at hr heF
    field_simp [heF]
    linear_combination (algebraMap (RatFunc K) (E K) kernelOne*
      algebraMap (RatFunc K) (E K) (second K f))*hr
  rw [he,trace_expansion]
  rw [map_add,first_algebraMap,first_coeff_y,add_zero]
  ring

end CrossedElliptic
end
end

/- Source component: RationalCoefficientMap. -/
section

noncomputable section
namespace CrossedRationalCoefficientMap
open Polynomial CrossedElliptic CrossedRationalResidue
variable {K L : Type*} [Field K] [Field L]

def polynomialMap (φ : K →+* L) : K[X] →+* RatFunc L :=
  (algebraMap L[X] (RatFunc L)).comp (Polynomial.mapRingHom φ)
lemma polynomialMap_injective (φ : K →+* L) : Function.Injective (polynomialMap φ) :=
  (IsFractionRing.injective L[X] (RatFunc L)).comp (Polynomial.map_injective φ φ.injective)

def map (φ : K →+* L) : RatFunc K →+* RatFunc L := IsFractionRing.lift (polynomialMap_injective φ)

lemma map_polynomial (φ : K →+* L) (P : K[X]) :
    map φ (algebraMap K[X] (RatFunc K) P)=algebraMap L[X] (RatFunc L) (P.map φ) :=
  IsFractionRing.lift_algebraMap (polynomialMap_injective φ) P

@[simp] lemma map_C (φ : K →+* L) (c : K) : map φ (RatFunc.C c)=RatFunc.C (φ c) := by
  change map φ (algebraMap K[X] (RatFunc K) (C c))=_
  rw [map_polynomial,Polynomial.map_C,RatFunc.algebraMap_C]

@[simp] lemma map_X (φ : K →+* L) : map φ (RatFunc.X)=RatFunc.X := by
  change map φ (algebraMap K[X] (RatFunc K) X)=_
  rw [map_polynomial,Polynomial.map_X,RatFunc.algebraMap_X]

lemma map_regular (φ : K →+* L) {a : K} {f : RatFunc K} (hf : RegularAt a f) :
    RegularAt (φ a) (map φ f) := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  refine ⟨P.map φ,Q.map φ,?_,?_⟩
  · rw [Polynomial.eval_map_apply]
    exact (_root_.map_ne_zero φ).mpr hQ
  · rw [map_div₀,map_polynomial,map_polynomial]

section Differentials
variable [CharZero K] [CharZero L]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (RatFunc L) := Ring.toIntAlgebra _

omit [CharZero K] in
lemma polynomial_image_eval (P : K[X]) :
    algebraMap K[X] (RatFunc K) P=P.eval₂ RatFunc.C RatFunc.X := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add,eval₂_add,hP,hQ]
  | monomial n c =>
    simp only [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow,
      RatFunc.algebraMap_C,RatFunc.algebraMap_X,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X]

omit [CharZero K] in
omit [CharZero L] in
lemma map_polynomial_eval (φ : K →+* L) (P : K[X]) :
    map φ (algebraMap K[X] (RatFunc K) P)=P.eval₂ ((RatFunc.C : L →+* RatFunc L).comp φ) RatFunc.X := by
  rw [map_polynomial]
  rw [polynomial_image_eval,Polynomial.eval₂_map]

lemma rational_intertwines (φ : RatFunc K →+* RatFunc L)
    (D : Derivation ℤ (RatFunc K) (RatFunc K)) (E : Derivation ℤ (RatFunc L) (RatFunc L))
    (hC : ∀ c,E (φ (RatFunc.C c))=φ (D (RatFunc.C c)))
    (hX : E (φ RatFunc.X)=φ (D RatFunc.X)) (f : RatFunc K) : E (φ f)=φ (D f) := by
  have hp (P : K[X]) : E (φ (algebraMap K[X] (RatFunc K) P))=
      φ (D (algebraMap K[X] (RatFunc K) P)) := by
    rw [polynomial_image_eval]
    exact polynomial_intertwines RatFunc.C φ D E RatFunc.X hC hX P
  induction f using RatFunc.induction_on with
  | f P Q hQ =>
    simp only [map_div₀,Derivation.leibniz_div,smul_eq_mul,map_mul,map_sub,map_pow,map_inv₀,hp]

lemma coefficient_compatible (φ : K →+* L)
    (D : Derivation ℤ K K) (D' : Derivation ℤ L L)
    (h : ∀ c,D' (φ c)=φ (D c)) (f : RatFunc K) :
    baseCoefficient D' (map φ f)=map φ (baseCoefficient D f) := by
  have hp (P : K[X]) :
      baseCoefficient D' (map φ (algebraMap K[X] (RatFunc K) P))=
      map φ (baseCoefficient D (algebraMap K[X] (RatFunc K) P)) := by
    have he : algebraMap K[X] (RatFunc K) P=P.eval₂ RatFunc.C RatFunc.X := polynomial_image_eval P
    rw [he]
    apply polynomial_intertwines RatFunc.C (map φ) (baseCoefficient D) (baseCoefficient D') RatFunc.X
    · intro c
      rw [map_C,baseCoefficient_C,baseCoefficient_C,map_C,h]
    · rw [map_X,baseCoefficient_X,baseCoefficient_X,map_zero]
  induction f using RatFunc.induction_on with
  | f P Q hQ =>
    simp only [map_div₀,Derivation.leibniz_div,smul_eq_mul,map_mul,map_sub,map_pow,map_inv₀,hp]

lemma time_compatible (φ : K →+* L) (f : RatFunc K) :
    baseTime (map φ f)=map φ (baseTime f) := by
  have hp (P : K[X]) : baseTime (map φ (algebraMap K[X] (RatFunc K) P))=
      map φ (baseTime (algebraMap K[X] (RatFunc K) P)) := by
    rw [polynomial_image_eval]
    apply polynomial_intertwines RatFunc.C (map φ) baseTime baseTime RatFunc.X
    · intro c; rw [map_C,baseTime_C,baseTime_C,map_zero]
    · rw [map_X,baseTime_X,baseTime_X,map_one]
  induction f using RatFunc.induction_on with
  | f P Q hQ =>
    simp only [map_div₀,Derivation.leibniz_div,smul_eq_mul,map_mul,map_sub,map_pow,map_inv₀,hp]

omit [CharZero K] [CharZero L] in
lemma map_killed (φ : K →+* L) (D : Derivation ℤ L L) (h : ∀ c,D (φ c)=0) (f : RatFunc K) :
    baseCoefficient D (map φ f)=0 := by
  have hp (P : K[X]) : baseCoefficient D (map φ (algebraMap K[X] (RatFunc K) P))=0 := by
    rw [polynomial_image_eval]
    have he := polynomial_intertwines RatFunc.C (map φ) (0 : Derivation ℤ (RatFunc K) (RatFunc K))
      (baseCoefficient D) RatFunc.X
      (fun c => by simp only [map_C,baseCoefficient_C,h,Derivation.coe_zero,Pi.zero_apply,map_zero])
      (by simp only [map_X,baseCoefficient_X,Derivation.coe_zero,Pi.zero_apply,map_zero]) P
    simpa only [Derivation.coe_zero,Pi.zero_apply,map_zero] using he
  induction f using RatFunc.induction_on with
  | f P Q hQ =>
    simp only [map_div₀,Derivation.leibniz_div,hp,smul_zero,sub_self,smul_zero]

omit [CharZero L] in
lemma derivation_ratCast (D : Derivation ℤ L L) (q : ℚ) : D (q : L)=0 := by
  rw [Rat.cast_def,Derivation.leibniz_div,D.map_intCast,D.map_natCast]
  simp

lemma rational_map_killed (D : Derivation ℤ L L) (f : RatFunc ℚ) :
    baseCoefficient D (map (algebraMap ℚ L) f)=0 := by
  apply map_killed _ D _ f
  intro q
  rw [show algebraMap ℚ L q=(q : L) from map_ratCast _ q]
  exact derivation_ratCast D q

end Differentials
end CrossedRationalCoefficientMap
end
end

/- Source component: EllipticBaseChange. -/
section

noncomputable section
namespace CrossedEllipticBaseChange
open Polynomial CrossedElliptic CrossedRationalResidue
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (E L) := Ring.toIntAlgebra _

def coefficientMap (φ : K →+* L) : RatFunc K →+* E L :=
  (algebraMap (RatFunc L) (E L)).comp (CrossedRationalCoefficientMap.map φ)
omit [CharZero K] [CharZero L] in
lemma equation_root (φ : K →+* L) : (equation K).eval₂ (coefficientMap φ) (y L)=0 := by
  conv_lhs => arg 3; rw [equation_eq]
  simp only [Polynomial.eval₂_sub,Polynomial.eval₂_pow,Polynomial.eval₂_X,Polynomial.eval₂_C,Polynomial.eval₂_ofNat,
    coefficientMap,RingHom.comp_apply,map_sub,map_pow,map_ofNat,CrossedRationalCoefficientMap.map_X]
  exact sub_eq_zero.mpr (relation L)

def map (φ : K →+* L) : E K →+* E L :=
  AdjoinRoot.lift (f:=equation K) (coefficientMap φ) (y L) (equation_root φ)
omit [CharZero K] [CharZero L] in
lemma map_rational (φ : K →+* L) (f : RatFunc K) :
    map φ (algebraMap (RatFunc K) (E K) f)=
      algebraMap (RatFunc L) (E L) (CrossedRationalCoefficientMap.map φ f) :=
  AdjoinRoot.lift_of (equation_root φ)
omit [CharZero K] [CharZero L] in
lemma map_y (φ : K →+* L) : map φ (y K)=y L := AdjoinRoot.lift_root (equation_root φ)
lemma map_x (φ : K →+* L) : map φ (x K)=x L := by
  rw [x,map_rational,CrossedRationalCoefficientMap.map_X]
  rfl
lemma map_base (φ : K →+* L) (c : K) :
    map φ (algebraMap K (E K) c)=algebraMap L (E L) (φ c) := by
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) (E K),map_rational,
    RatFunc.algebraMap_eq_C,CrossedRationalCoefficientMap.map_C,map_constant]

lemma map_expansion (φ : K →+* L) (f : E K) :
    map φ f=algebraMap (RatFunc L) (E L) (CrossedRationalCoefficientMap.map φ (first K f))+
      algebraMap (RatFunc L) (E L) (CrossedRationalCoefficientMap.map φ (second K f))*y L := by
  conv_lhs => rw [first_second_expansion K f]
  rw [map_add,map_mul,map_rational,map_rational,map_y]
lemma first_map (φ : K →+* L) (f : E K) :
    first L (map φ f)=CrossedRationalCoefficientMap.map φ (first K f) := by
  rw [map_expansion,map_add,first_algebraMap,first_coeff_y,add_zero]
lemma second_map (φ : K →+* L) (f : E K) :
    second L (map φ f)=CrossedRationalCoefficientMap.map φ (second K f) := by
  rw [map_expansion,map_add,second_algebraMap,second_coeff_y,zero_add]

lemma map_delta (φ : K →+* L) (f : E K) : delta (map φ f)=map φ (delta f) := by
  apply field_intertwines (map φ) delta delta
  · intro c; rw [map_base,delta_base,delta_base,map_zero]
  · rw [map_x,delta_x,delta_x,map_div₀,map_neg,map_y,map_ofNat]
  · rw [map_y,delta_y,delta_y,map_div₀,map_neg,map_pow,map_x,map_ofNat]
lemma map_coefficient (φ : K →+* L) (D : Derivation ℤ K K) (D' : Derivation ℤ L L)
    (h : ∀ c,D' (φ c)=φ (D c)) (f : E K) : coefficient D' (map φ f)=map φ (coefficient D f) := by
  apply field_intertwines (map φ) (coefficient D) (coefficient D')
  · intro c; rw [map_base,coefficient_scalar,coefficient_scalar,map_base,h]
  · rw [map_x,coefficient_x,coefficient_x,map_zero]
  · rw [map_y,coefficient_y,coefficient_y,map_zero]
lemma map_a (φ : K →+* L) : map φ (a (K:=K))=a (K:=L) := by
  simp only [a,map_div₀,map_neg,map_add,map_y,map_mul,map_x,map_ofNat]
lemma map_b (φ : K →+* L) : map φ (b (K:=K))=b (K:=L) := by
  simp only [b,map_div₀,map_sub,map_y,map_mul,map_x,map_ofNat]

end CrossedEllipticBaseChange
end
end
