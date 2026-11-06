import HodgeComputer.Constructions.EllipticCompanions.Translation

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

/- Source component: RationalLocalDivision. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedRationalResidue
open Polynomial
variable {K : Type*} [Field K]

lemma RegularAt.subtract_value_div_X {f : RatFunc K} (hf : RegularAt 0 f) :
    RegularAt 0 ((f-RatFunc.C (valueAt 0 f))/RatFunc.X) := by
  obtain ⟨P,Q,hQ,rfl⟩ := hf
  rw [valueAt_div_polynomials 0 P Q hQ]
  let N := P-Polynomial.C (P.eval 0/Q.eval 0)*Q
  have hN : N.eval 0=0 := by
    simp only [N,eval_sub,eval_mul,eval_C]
    field_simp <;> ring
  have hx : (X : K[X]) ∣ N := by
    rw [Polynomial.X_dvd_iff]
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hN
  obtain ⟨R,hR⟩ := hx
  have hmap := congrArg (algebraMap K[X] (RatFunc K)) hR
  simp only [N,map_sub,map_mul,RatFunc.algebraMap_C,RatFunc.algebraMap_X] at hmap
  refine ⟨R,Q,hQ,?_⟩
  have hq : algebraMap K[X] (RatFunc K) Q≠0 := by
    apply polynomialMap_ne_zero
    intro h; apply hQ; simp [h]
  have hX : (RatFunc.X : RatFunc K)≠0 := X_ne_zero
  field_simp
  linear_combination hmap

lemma RegularAt.div_X_of_value_zero {f : RatFunc K} (hf : RegularAt 0 f) (h0 : valueAt 0 f=0) :
    RegularAt 0 (f/RatFunc.X) := by
  have h := hf.subtract_value_div_X
  simpa only [h0,map_zero,sub_zero] using h

lemma RegularAt.pow {a : K} {f : RatFunc K} (hf : RegularAt a f) (n : ℕ) : RegularAt a (f^n) := by
  induction n with
  | zero => simpa using RegularAt.polynomial a (1 : K[X])
  | succ n ih => simpa only [pow_succ] using ih.mul hf

lemma valueAt_X (a : K) : valueAt a (RatFunc.X : RatFunc K)=a := by
  have h := valueAt_polynomial a (X : K[X])
  simpa using h

lemma valueAt_pow {a : K} {f : RatFunc K} (hf : RegularAt a f) (n : ℕ) :
    valueAt a (f^n)=(valueAt a f)^n := by
  induction n with
  | zero => simpa using valueAt_C a (1 : K)
  | succ n ih => rw [pow_succ,valueAt_mul (hf.pow n) hf,ih,pow_succ]

end CrossedRationalResidue
end
end

/- Source component: EllipticInfinityApproximation. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace CrossedEllipticInfinity
open Polynomial CrossedRationalResidue CrossedElliptic
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

/-- The regular-singular operator for the local second-kind primitive at infinity. -/
def jetOperator (h : RatFunc K) : RatFunc K :=
  5*h+2*RatFunc.X*baseTime h-3456*RatFunc.X^3*h-864*RatFunc.X^4*baseTime h

lemma jetOperator_add (h k : RatFunc K) : jetOperator (h+k)=jetOperator h+jetOperator k := by
  simp only [jetOperator,map_add]
  ring
lemma jetOperator_zero : jetOperator (0 : RatFunc K)=0 := by simp [jetOperator]

lemma euler_power (n : ℕ) : (RatFunc.X : RatFunc K)*baseTime (RatFunc.X^n)=
    (n : RatFunc K)*RatFunc.X^n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Derivation.leibniz_pow]
    simp only [baseTime_X,smul_eq_mul,nsmul_eq_mul,Nat.succ_sub_one,mul_one,pow_succ]
    ring

lemma jetOperator_monomial (a : K) (n : ℕ) :
    jetOperator (RatFunc.C a*RatFunc.X^n)=
      RatFunc.C (a*(5+2*(n:K)))*RatFunc.X^n-
      RatFunc.C (a*(3456+864*(n:K)))*RatFunc.X^(n+3) := by
  have hX : (RatFunc.X : RatFunc K)≠0 := X_ne_zero
  have hd : baseTime ((RatFunc.X : RatFunc K)^n)=(n : RatFunc K)*RatFunc.X^n/RatFunc.X := by
    apply (eq_div_iff hX).mpr
    linear_combination euler_power (K:=K) n
  have h5 : RatFunc.C (5 : K)=(5 : RatFunc K) := map_natCast _ 5
  have h2 : RatFunc.C (2 : K)=(2 : RatFunc K) := map_natCast _ 2
  have h3456 : RatFunc.C (3456 : K)=(3456 : RatFunc K) := map_natCast _ 3456
  have h864 : RatFunc.C (864 : K)=(864 : RatFunc K) := map_natCast _ 864
  have hn : RatFunc.C (n : K)=(n : RatFunc K) := map_natCast _ n
  simp only [jetOperator,Derivation.leibniz,baseTime_C,zero_smul,add_zero,smul_eq_mul,
    hd,map_mul,map_add,h5,h2,h3456,h864,hn,pow_add]
  field_simp
  ring

theorem exists_jet_approximation (f : RatFunc K) (hf : RegularAt 0 f) (N : ℕ) :
    ∃ h r : RatFunc K,RegularAt 0 h ∧ RegularAt 0 r ∧ f-jetOperator h=RatFunc.X^N*r := by
  have hXreg : RegularAt (0 : K) (RatFunc.X : RatFunc K) := RegularAt.polynomial 0 X
  have hX : (RatFunc.X : RatFunc K)≠0 := X_ne_zero
  induction N with
  | zero =>
    refine ⟨0,f,by simpa using RegularAt.polynomial (0 : K) (0 : K[X]),hf,?_⟩
    rw [jetOperator_zero,sub_zero,pow_zero,one_mul]
  | succ n ih =>
    obtain ⟨h,r,hh,hr,he⟩ := ih
    let a : K := valueAt 0 r/(5+2*(n:K))
    let g : RatFunc K := r-RatFunc.C (a*(5+2*(n:K)))+
      RatFunc.C (a*(3456+864*(n:K)))*RatFunc.X^3
    have hdiag : (5+2*(n:K))≠0 := by
      exact_mod_cast (show (5+2*n : ℕ)≠0 by omega)
    have hg : RegularAt 0 g := (hr.sub (RegularAt.C 0 _)).add
      ((RegularAt.C 0 _).mul (hXreg.pow 3))
    have hval : valueAt 0 g=0 := by
      simp only [g,map_add,map_sub,valueAt_C]
      rw [valueAt_mul (RegularAt.C 0 _) (hXreg.pow 3),valueAt_C,
        valueAt_pow hXreg 3,valueAt_X]
      simp only [zero_pow (by decide : (3 : ℕ)≠0),mul_zero,add_zero]
      dsimp only [a]
      field_simp
      ring
    refine ⟨h+RatFunc.C a*RatFunc.X^n,g/RatFunc.X,
      hh.add ((RegularAt.C 0 a).mul (hXreg.pow n)),hg.div_X_of_value_zero hval,?_⟩
    rw [jetOperator_add,jetOperator_monomial]
    have he' : f-jetOperator h=RatFunc.X^n*r := he
    rw [sub_add_eq_sub_sub,he']
    dsimp only [g]
    rw [pow_succ,pow_add]
    field_simp
    ring

end CrossedEllipticInfinity
end
end

/- Source component: EllipticInfinityConstants. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedEllipticInfinity
open Polynomial CrossedRationalResidue CrossedElliptic
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

def forcing : RatFunc K := 3888/(1-1728*RatFunc.X^3)^2

lemma forcing_regular : RegularAt (0 : K) (forcing (K:=K)) := by
  refine ⟨3888,(1-1728*X^3)^2,by norm_num,?_⟩
  have hc3888 : algebraMap K[X] (RatFunc K) (3888 : K[X])=(3888 : RatFunc K) := map_natCast _ 3888
  have hc1728 : algebraMap K[X] (RatFunc K) (1728 : K[X])=(1728 : RatFunc K) := map_natCast _ 1728
  simp only [forcing,map_pow,map_sub,map_one,map_mul,RatFunc.algebraMap_X,hc3888,hc1728]

lemma map_jetOperator {L : Type*} [Field L] [CharZero L] (φ : K →+* L) (h : RatFunc K) :
    CrossedRationalCoefficientMap.map φ (jetOperator h)=
      jetOperator (CrossedRationalCoefficientMap.map φ h) := by
  let ψ := CrossedRationalCoefficientMap.map φ
  have h5 : ψ (5 : RatFunc K)=(5 : RatFunc L) := map_natCast _ 5
  have h2 : ψ (2 : RatFunc K)=(2 : RatFunc L) := map_natCast _ 2
  have h3456 : ψ (3456 : RatFunc K)=(3456 : RatFunc L) := map_natCast _ 3456
  have h864 : ψ (864 : RatFunc K)=(864 : RatFunc L) := map_natCast _ 864
  change ψ (jetOperator h)=_
  simp only [jetOperator,map_sub,map_add,map_mul,map_pow,h5,h2,h3456,h864]
  rw [CrossedRationalCoefficientMap.map_X,← CrossedRationalCoefficientMap.time_compatible]

lemma map_forcing {L : Type*} [Field L] [CharZero L] (φ : K →+* L) :
    CrossedRationalCoefficientMap.map φ (forcing (K:=K))=forcing (K:=L) := by
  let ψ := CrossedRationalCoefficientMap.map φ
  have h3888 : ψ (3888 : RatFunc K)=(3888 : RatFunc L) := map_natCast _ 3888
  have h1728 : ψ (1728 : RatFunc K)=(1728 : RatFunc L) := map_natCast _ 1728
  change ψ (forcing (K:=K))=forcing (K:=L)
  simp only [forcing,map_div₀,map_sub,map_one,map_mul,map_pow,h3888,h1728]
  rw [CrossedRationalCoefficientMap.map_X]

theorem exists_constant_jet_approximation (N : ℕ) :
    ∃ h r : RatFunc K,RegularAt 0 h ∧ RegularAt 0 r ∧
      forcing-jetOperator h=RatFunc.X^N*r ∧
      ∀ D : Derivation ℤ K K,baseCoefficient D h=0 ∧ baseCoefficient D r=0 := by
  obtain ⟨h,r,hh,hr,he⟩ := exists_jet_approximation (forcing (K:=ℚ)) forcing_regular N
  let ψ := CrossedRationalCoefficientMap.map (algebraMap ℚ K)
  refine ⟨ψ h,ψ r,?_,?_,?_,?_⟩
  · simpa only [map_zero] using CrossedRationalCoefficientMap.map_regular (algebraMap ℚ K) hh
  · simpa only [map_zero] using CrossedRationalCoefficientMap.map_regular (algebraMap ℚ K) hr
  · have hm := congrArg ψ he
    rw [map_sub,map_forcing,map_jetOperator,map_mul,map_pow,CrossedRationalCoefficientMap.map_X] at hm
    exact hm
  · intro D
    exact ⟨CrossedRationalCoefficientMap.rational_map_killed D h,
      CrossedRationalCoefficientMap.rational_map_killed D r⟩

end CrossedEllipticInfinity
end
end

/- Source component: RationalInfinityCalculus. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedRationalResidue
open Polynomial CrossedElliptic CrossedRationalCoefficientMap
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

lemma time_reciprocal (f : RatFunc K) : reciprocal (baseTime f)=
    -(RatFunc.X : RatFunc K)^2*baseTime (reciprocal f) := by
  have he := rational_intertwines (reciprocal (K:=K)).toRingHom baseTime
    (-(RatFunc.X : RatFunc K)^2 • baseTime)
    (fun c => by simp [reciprocal_C,Derivation.smul_apply,baseTime_C])
    (by
      change (-(RatFunc.X : RatFunc K)^2 • baseTime) (reciprocal RatFunc.X)=reciprocal (baseTime RatFunc.X)
      rw [reciprocal_X,Derivation.smul_apply,Derivation.leibniz_inv,baseTime_X]
      simp only [smul_eq_mul,mul_one,map_one]
      field_simp [X_ne_zero (K:=K)]) f
  exact he.symm

lemma coefficient_reciprocal (D : Derivation ℤ K K) (f : RatFunc K) :
    baseCoefficient D (reciprocal f)=reciprocal (baseCoefficient D f) := by
  apply rational_intertwines (reciprocal (K:=K)).toRingHom (baseCoefficient D) (baseCoefficient D)
  · intro c
    change baseCoefficient D (reciprocal (RatFunc.C c))=reciprocal (baseCoefficient D (RatFunc.C c))
    rw [reciprocal_C,baseCoefficient_C,reciprocal_C]
  · change baseCoefficient D (reciprocal RatFunc.X)=reciprocal (baseCoefficient D RatFunc.X)
    rw [reciprocal_X,Derivation.leibniz_inv,baseCoefficient_X,map_zero,smul_zero]

lemma exists_power_regular_zero (f : RatFunc K) : ∃ n : ℕ,RegularAt 0 (RatFunc.X^n*f) := by
  induction f using RatFunc.induction_on with
  | f P Q hQ =>
    obtain ⟨R,hR,hnd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ (0 : K)
    have hr : R.eval 0≠0 := by
      simpa only [dvd_iff_isRoot,IsRoot] using hnd
    let n := Q.rootMultiplicity 0
    refine ⟨n,?_⟩
    have hq : algebraMap K[X] (RatFunc K) Q≠0 := polynomialMap_ne_zero hQ
    have hr' : algebraMap K[X] (RatFunc K) R≠0 := by
      apply polynomialMap_ne_zero
      intro h; apply hr; simp [h]
    have hx : (RatFunc.X : RatFunc K)≠0 := X_ne_zero
    have hm := congrArg (algebraMap K[X] (RatFunc K)) hR
    simp only [map_mul,map_pow,map_sub,map_zero,sub_zero,RatFunc.algebraMap_X] at hm
    have he : (RatFunc.X : RatFunc K)^n*
        (algebraMap K[X] (RatFunc K) P/algebraMap K[X] (RatFunc K) Q)=
        algebraMap K[X] (RatFunc K) P/algebraMap K[X] (RatFunc K) R := by
      rw [hm]
      change RatFunc.X^n*(algebraMap K[X] (RatFunc K) P/
        (RatFunc.X^n*algebraMap K[X] (RatFunc K) R))=_
      rw [← mul_div_assoc,mul_div_mul_left _ _ (pow_ne_zero n hx)]
    rw [he]
    exact ⟨P,R,hr,rfl⟩

end CrossedRationalResidue
end
end

/- Source component: EllipticInfinityKernels. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedEllipticInfinity
open Polynomial CrossedElliptic CrossedRationalResidue CrossedEllipticTheta
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _

def denominator : RatFunc K := 1-1728*RatFunc.X^3
def firstDensity : RatFunc K := 36*(1+3456*RatFunc.X^3)/denominator^2
def primitiveZero : RatFunc K := 36*RatFunc.X/denominator
def primitiveOne (h : RatFunc K) : RatFunc K := -2*RatFunc.X*h*(1-432*RatFunc.X^3)

lemma denominator_ne_zero : denominator (K:=K)≠0 := by
  have hp : (1-1728*X^3 : K[X])≠0 := by
    intro h
    have he := congrArg (Polynomial.eval (0 : K)) h
    norm_num at he
  have hm := polynomialMap_ne_zero hp
  have hc : algebraMap K[X] (RatFunc K) (1728 : K[X])=(1728 : RatFunc K) := map_natCast _ 1728
  simpa only [denominator,map_sub,map_one,map_mul,map_pow,hc,RatFunc.algebraMap_X] using hm

lemma primitiveZero_derivative : baseTime (primitiveZero (K:=K))=firstDensity := by
  have hc36 : baseTime (36 : RatFunc K)=0 := baseTime.map_natCast 36
  have hc1728 : baseTime (1728 : RatFunc K)=0 := baseTime.map_natCast 1728
  have hc1 : baseTime (K:=K) (1 : RatFunc K)=0 := (baseTime (K:=K)).map_one_eq_zero
  have hz := denominator_ne_zero (K:=K)
  simp only [primitiveZero,firstDensity,denominator,div_eq_mul_inv]
  simp only [Derivation.leibniz,Derivation.leibniz_inv,Derivation.leibniz_pow,map_sub,
    hc36,hc1728,hc1,baseTime_X,smul_eq_mul,nsmul_eq_mul,
    zero_mul,mul_zero,mul_one,zero_sub,sub_zero,add_zero,zero_add]
  norm_num only
  generalize hd : (1-1728*(RatFunc.X : RatFunc K)^3)=d at *
  field_simp [hz]
  rw [← hd]
  ring

lemma primitiveOne_derivative (h : RatFunc K) :
    -baseTime (primitiveOne h)+3*h=jetOperator h := by
  have hc2 : baseTime (2 : RatFunc K)=0 := baseTime.map_natCast 2
  have hc432 : baseTime (432 : RatFunc K)=0 := baseTime.map_natCast 432
  have hc1 : baseTime (K:=K) (1 : RatFunc K)=0 := (baseTime (K:=K)).map_one_eq_zero
  simp only [primitiveOne,jetOperator,Derivation.leibniz,Derivation.leibniz_pow,map_sub,map_neg,
    hc2,hc432,hc1,baseTime_X,smul_eq_mul,nsmul_eq_mul,
    zero_mul,mul_zero,mul_one,zero_sub,sub_zero,add_zero,zero_add]
  norm_num only
  ring

lemma reciprocal_kernelZero : ((RatFunc.X : RatFunc K)^2)⁻¹*reciprocal (kernelZero (K:=K))=
    -firstDensity := by
  have hx : (RatFunc.X : RatFunc K)≠0 := X_ne_zero
  have hz := denominator_ne_zero (K:=K)
  have h36 : reciprocal (36 : RatFunc K)=(36 : RatFunc K) := map_natCast _ 36
  have h3456 : reciprocal (3456 : RatFunc K)=(3456 : RatFunc K) := map_natCast _ 3456
  have h1728 : reciprocal (1728 : RatFunc K)=(1728 : RatFunc K) := map_natCast _ 1728
  simp only [kernelZero,map_div₀,map_neg,map_mul,map_add,map_sub,map_pow,h36,h3456,h1728,reciprocal_X,
    firstDensity,denominator]
  have he : ((RatFunc.X : RatFunc K)⁻¹)^3-1728=(1-1728*RatFunc.X^3)/RatFunc.X^3 := by
    field_simp
  rw [he]
  generalize hd : (1-1728*(RatFunc.X : RatFunc K)^3)=d at *
  field_simp [hx,hz] <;> ring

lemma reciprocal_kernelOne : ((RatFunc.X : RatFunc K)^2)⁻¹*reciprocal (kernelOne (K:=K))=
    forcing := by
  have hx : (RatFunc.X : RatFunc K)≠0 := X_ne_zero
  have hz := denominator_ne_zero (K:=K)
  have h3888 : reciprocal (3888 : RatFunc K)=(3888 : RatFunc K) := map_natCast _ 3888
  have h1728 : reciprocal (1728 : RatFunc K)=(1728 : RatFunc K) := map_natCast _ 1728
  simp only [kernelOne,map_div₀,map_mul,map_sub,map_pow,h3888,h1728,reciprocal_X,forcing]
  have he : ((RatFunc.X : RatFunc K)⁻¹)^3-1728=(1-1728*RatFunc.X^3)/RatFunc.X^3 := by
    field_simp
  rw [he]
  generalize hd : (1-1728*(RatFunc.X : RatFunc K)^3)=d at *
  field_simp [hx,hz] <;> ring

lemma infinity_theta_expression (f : E K) :
    infinityCoefficient (differentialTrace (thetaRatio*f))=
      residue (K:=K) 0 (-firstDensity*reciprocal (first K f)+forcing*reciprocal (second K f)) := by
  rw [theta_trace]
  change residue (K:=K) 0 _=_
  congr 1
  rw [map_add,map_mul,map_mul,mul_add]
  have h0 := reciprocal_kernelZero (K:=K)
  have h1 := reciprocal_kernelOne (K:=K)
  linear_combination reciprocal (first K f)*h0+reciprocal (second K f)*h1

lemma residue_integration_by_parts (J0 J1 f0 f1 h : RatFunc K) :
    residue (K:=K) 0 (J0*baseTime f0+J1*baseTime f1+3*h*f1)=
      residue (K:=K) 0 (-baseTime J0*f0+(-baseTime J1+3*h)*f1) := by
  have he : (J0*baseTime f0+J1*baseTime f1+3*h*f1)-
      (-baseTime J0*f0+(-baseTime J1+3*h)*f1)=baseTime (J0*f0)+baseTime (J1*f1) := by
    simp only [Derivation.leibniz,smul_eq_mul]
    ring
  have hr := congrArg (residue (K:=K) 0) he
  have hz : residue (K:=K) 0 (baseTime (J0*f0)+baseTime (J1*f1))=0 := by
    rw [map_add,residue_time,residue_time,add_zero]
  rw [map_sub,hz] at hr
  exact sub_eq_zero.mp hr

end CrossedEllipticInfinity
end
end

/- Source component: EllipticInfinityBoundary. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace CrossedEllipticInfinity
open Polynomial CrossedElliptic CrossedRationalResidue
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

def boundaryKernelZero (h : RatFunc K) : RatFunc K := -6*RatFunc.X^2*h
def boundaryKernelOne : RatFunc K := 108/(RatFunc.X*denominator)

def boundary (h : RatFunc K) : E K →ₗ[K] K :=
  (residue (K:=K) 0).comp
    (((LinearMap.mulLeft K (boundaryKernelZero h)).comp
        ((reciprocal (K:=K)).toLinearMap.comp ((first K).restrictScalars K)))+
     ((LinearMap.mulLeft K (boundaryKernelOne (K:=K))).comp
        ((reciprocal (K:=K)).toLinearMap.comp ((second K).restrictScalars K))))

lemma boundary_apply (h : RatFunc K) (f : E K) : boundary h f=
    residue (K:=K) 0 (boundaryKernelZero h*reciprocal (first K f)+
      boundaryKernelOne*reciprocal (second K f)) := rfl

lemma boundary_one (h : RatFunc K) (hh : RegularAt 0 h) : boundary h (1 : E K)=0 := by
  rw [boundary_apply,first_one,second_one,map_one,map_zero,mul_one,mul_zero,add_zero]
  apply RegularAt.residue_eq_zero
  have h6 : RatFunc.C (-6 : K)=(-6 : RatFunc K) := by
    rw [map_neg]; congr 1; exact map_natCast _ 6
  have hX : RegularAt (0 : K) (RatFunc.X : RatFunc K) := RegularAt.polynomial 0 X
  have hr := ((RegularAt.C (0 : K) (-6)).mul (hX.pow 2)).mul hh
  simpa only [h6,boundaryKernelZero] using hr

lemma kernelZero_coefficient (D : Derivation ℤ K K) (h : RatFunc K) (hh : baseCoefficient D h=0) :
    baseCoefficient D (boundaryKernelZero h)=0 := by
  have h6 : baseCoefficient D (6 : RatFunc K)=0 := (baseCoefficient D).map_natCast 6
  simp [boundaryKernelZero,Derivation.leibniz,Derivation.leibniz_pow,baseCoefficient_X,h6,hh]

lemma kernelOne_coefficient (D : Derivation ℤ K K) :
    baseCoefficient D (boundaryKernelOne (K:=K))=0 := by
  have h108 : baseCoefficient D (108 : RatFunc K)=0 := (baseCoefficient D).map_natCast 108
  have h1728 : baseCoefficient D (1728 : RatFunc K)=0 := (baseCoefficient D).map_natCast 1728
  have h1 : baseCoefficient D (1 : RatFunc K)=0 := (baseCoefficient D).map_one_eq_zero
  simp [boundaryKernelOne,denominator,Derivation.leibniz,Derivation.leibniz_pow,
    Derivation.leibniz_div,baseCoefficient_X,h108,h1728,h1]

lemma boundary_coefficient (D : Derivation ℤ K K) (h : RatFunc K)
    (hh : baseCoefficient D h=0) (f : E K) : boundary h (coefficient D f)=D (boundary h f) := by
  rw [boundary_apply,boundary_apply,first_coefficient,second_coefficient,
    ← coefficient_reciprocal D (first K f),← coefficient_reciprocal D (second K f)]
  have he : baseCoefficient D
      (boundaryKernelZero h*reciprocal (first K f)+boundaryKernelOne*reciprocal (second K f))=
      boundaryKernelZero h*baseCoefficient D (reciprocal (first K f))+
        boundaryKernelOne*baseCoefficient D (reciprocal (second K f)) := by
    simp only [map_add,Derivation.leibniz,kernelZero_coefficient D h hh,kernelOne_coefficient,
      smul_eq_mul,mul_zero,add_zero]
  rw [← he,residue_coefficient]

lemma boundary_delta_integrand (h : RatFunc K) (f : E K) :
    boundaryKernelZero h*reciprocal (first K (delta f))+
      boundaryKernelOne*reciprocal (second K (delta f))=
    primitiveZero*baseTime (reciprocal (first K f))+
      primitiveOne h*baseTime (reciprocal (second K f))+3*h*reciprocal (second K f) := by
  rw [first_delta,second_delta]
  have h432 : reciprocal (432 : RatFunc K)=(432 : RatFunc K) := map_natCast _ 432
  have h3 : reciprocal (3 : RatFunc K)=(3 : RatFunc K) := map_natCast _ 3
  have h2 : reciprocal (2 : RatFunc K)=(2 : RatFunc K) := map_natCast _ 2
  simp only [map_sub,map_neg,map_div₀,map_mul,map_pow,h432,h3,h2,reciprocal_X,time_reciprocal]
  simp only [boundaryKernelZero,boundaryKernelOne,primitiveZero,primitiveOne]
  have hx : (RatFunc.X : RatFunc K)≠0 := X_ne_zero
  have hz := denominator_ne_zero (K:=K)
  generalize hd : denominator (K:=K)=d at *
  field_simp [hx,hz]
  ring

lemma boundary_delta (h : RatFunc K) (f : E K) : boundary h (delta f)=
    residue (K:=K) 0 (-firstDensity*reciprocal (first K f)+jetOperator h*reciprocal (second K f)) := by
  rw [boundary_apply,boundary_delta_integrand,residue_integration_by_parts,
    primitiveZero_derivative,primitiveOne_derivative]

theorem infinity_boundary_identity (f : E K) (N : ℕ) (h r : RatFunc K)
    (hr : RegularAt 0 r)
    (he : forcing-jetOperator h=RatFunc.X^N*r)
    (hpole : RegularAt 0 (RatFunc.X^N*reciprocal (second K f))) :
    infinityCoefficient (differentialTrace (thetaRatio*f))=boundary h (delta f) := by
  rw [infinity_theta_expression,boundary_delta]
  have hg : RegularAt 0 ((forcing-jetOperator h)*reciprocal (second K f)) := by
    rw [he]
    have hm : (RatFunc.X^N*r)*reciprocal (second K f)=r*(RatFunc.X^N*reciprocal (second K f)) := by ring
    rw [hm]
    exact hr.mul hpole
  have hz := hg.residue_eq_zero
  have hid : (-firstDensity*reciprocal (first K f)+forcing*reciprocal (second K f))-
      (-firstDensity*reciprocal (first K f)+jetOperator h*reciprocal (second K f))=
      (forcing-jetOperator h)*reciprocal (second K f) := by ring
  have hm := congrArg (residue (K:=K) 0) hid
  rw [map_sub,hz] at hm
  exact sub_eq_zero.mp hm

theorem exists_infinity_boundary (f : E K) : ∃ B : E K →ₗ[K] K,
    B 1=0 ∧ (∀ (D : Derivation ℤ K K) (g : E K),B (coefficient D g)=D (B g)) ∧
      infinityCoefficient (differentialTrace (thetaRatio*f))=B (delta f) := by
  obtain ⟨N,hN⟩ := exists_power_regular_zero (reciprocal (second K f))
  obtain ⟨h,r,hh,hr,he,hconst⟩ := exists_constant_jet_approximation (K:=K) N
  exact ⟨boundary h,boundary_one h hh,
    fun D g => boundary_coefficient D h (hconst D).1 g,infinity_boundary_identity f N h r hr he hN⟩

end CrossedEllipticInfinity
end
end

/- Source component: EllipticResiduePairing. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace CrossedElliptic
open Polynomial CrossedRationalResidue CrossedEllipticTheta CrossedEllipticInfinity
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

lemma differentialTrace_second (f : E K) : differentialTrace f= -6*second K f := by
  have he : (-3/y K)*f=algebraMap (RatFunc K) (E K) (-3*second K f)+
      algebraMap (RatFunc K) (E K) (-3*first K f/((RatFunc.X : RatFunc K)^3-432))*y K := by
    conv_lhs => arg 2; rw [first_second_expansion K f]
    have hy := y_ne_zero (K:=K)
    have hc : (x K)^3-432≠0 := by rw [← relation K]; exact pow_ne_zero 2 hy
    have hr := relation K
    simp only [map_mul,map_div₀,map_sub,map_pow,map_neg,map_ofNat]
    change (y K)^2=(algebraMap (RatFunc K) (E K) RatFunc.X)^3-432 at hr
    rw [← hr]
    field_simp [hy]
    ring
  rw [differentialTrace_apply,he,trace_expansion,map_add,first_algebraMap,first_coeff_y,add_zero]
  ring

lemma residueAt_regular (r : K) (f : E K) (hf : FibreRegular r f) : residueAt r f=0 := by
  change residue r (differentialTrace f)=0
  rw [differentialTrace_second]
  have h6 : RatFunc.C (-6 : K)=(-6 : RatFunc K) := by simp [map_ofNat]
  rw [← h6,CrossedEllipticTheta.residue_C_mul,hf.2.residue_eq_zero,mul_zero]

lemma theta_cubic_constant (D : Derivation ℤ K K) (r : K) (hr : r^3=1728) : D r=0 := by
  have h := congrArg D hr
  simp only [Derivation.leibniz_pow,D.map_natCast,smul_eq_mul,nsmul_eq_mul] at h
  have h1728 : D (1728 : K)=0 := D.map_natCast 1728
  rw [h1728] at h
  norm_num only at h
  rw [← mul_assoc] at h
  have hr0 : r≠0 := by intro h0; rw [h0] at hr; norm_num at hr
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr0))

/-- The full global theta pairing, including the finite correction at infinity. -/
theorem theta_residue_pairing [DecidableEq K] {ι : Type*} [Fintype ι]
    (s t : Finset K) (hst : Disjoint s t) (htcard : t.card=3)
    (ht : ∀ r∈t,r^3=1728) (bf : E K) (Cf : ι → E K) (D : ι → Derivation ℤ K K) (α : K)
    (hfirst : delta bf+∑ i,coefficient (D i) (Cf i)=algebraMap K (E K) α)
    (hreg : ∀ r∈t,FibreRegular r bf)
    (hsplit : (differentialTrace (thetaRatio*bf)).denom.Splits)
    (hout : ∀ r∉s∪t,residueAt r (thetaRatio*bf)=0) :
    ∃ ξ : ι → K,residueOn s (bf*thetaRatio)=3*α-∑ i,D i (ξ i) := by
  classical
  obtain ⟨B,hBone,hBD,hB⟩ := exists_infinity_boundary bf
  let ξ : ι → K := fun i => (∑ r∈t,fibreValue r (-36) (Cf i))+B (Cf i)
  refine ⟨ξ,?_⟩
  have hInf : infinityCoefficient (differentialTrace (thetaRatio*bf))=
      -(∑ i,D i (B (Cf i))) := by
    rw [hB]
    have hb := congrArg B hfirst
    have hconst : B (algebraMap K (E K) α)=0 := by
      have he : algebraMap K (E K) α=α • (1 : E K) := by rw [Algebra.smul_def,mul_one]
      rw [he,map_smul,hBone,smul_zero]
    rw [map_add,map_sum,hconst] at hb
    simp only [hBD] at hb
    linear_combination hb
  have hlocal (r : K) (hr : r∈t) : residueAt r (thetaRatio*bf)=
      -α+∑ i,D i (fibreValue r (-36) (Cf i)) := by
    rw [theta_residue_delta r (ht r hr) bf (hreg r hr)]
    have he := congrArg (fibreValue r (-36)) hfirst
    simp only [map_add,map_sum,fibreValue_base] at he
    have hc (i : ι) : D i (-36 : K)=0 := by rw [map_neg]; exact neg_eq_zero.mpr ((D i).map_natCast 36)
    simp only [fibreValue_coefficient r (-36) (D _) (theta_cubic_constant (D _) r (ht r hr)) (hc _)] at he
    linear_combination -he
  have hsum : (∑ r∈t,residueAt r (thetaRatio*bf))=
      -3*α+∑ i,D i (∑ r∈t,fibreValue r (-36) (Cf i)) := by
    rw [Finset.sum_congr rfl (fun r hr => hlocal r hr)]
    rw [Finset.sum_add_distrib,Finset.sum_comm]
    simp only [Finset.sum_const,nsmul_eq_mul,htcard,Nat.cast_ofNat,map_sum]
    ring
  have hglobal := residue_sum_eq_infinity (differentialTrace (thetaRatio*bf)) hsplit (s∪t) hout
  change (∑ r∈s∪t,residueAt r (thetaRatio*bf))=_ at hglobal
  rw [Finset.sum_union hst,hsum,hInf] at hglobal
  have hξ : (∑ i,D i (ξ i))=
      (∑ i,D i (∑ r∈t,fibreValue r (-36) (Cf i)))+(∑ i,D i (B (Cf i))) := by
    simp only [ξ,map_add,Finset.sum_add_distrib]
  rw [hξ]
  simp only [residueOn,LinearMap.sum_apply]
  simp only [mul_comm bf thetaRatio]
  linear_combination hglobal

end CrossedElliptic
end
end
