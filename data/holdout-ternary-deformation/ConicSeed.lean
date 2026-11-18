import Proposal.DeformedEquation

noncomputable section
set_option profiler true
set_option profiler.threshold 100
namespace DeformedConic
open Polynomial

abbrev K := ZMod 5
local instance conicSeed_local_1 : Fact (Nat.Prime 5) := ⟨by decide⟩
def seed : Fin 13 → K := ![1,
0,
2,
2,
2,
1,
1,
3,
3,
1,
4,
4,
3]
def parameters : Fin 3 → K := ![4,4,4]
def seedCurve : Fin 5 → Polynomial K := ![(1) + (2)*X^2,
(1)*X^1,
(4) + (2)*X^1 + (2)*X^2,
(4) + (1)*X^1 + (1)*X^2 + (3)*X^3 + (3)*X^4,
(4) + (1)*X^1 + (4)*X^2 + (4)*X^3 + (3)*X^4]
lemma curveEval_seed : curveEval parameters (RingHom.id K) seed = seedCurve := by
  funext i
  fin_cases i <;> simp [curveEval,curve,cv,cp,seed,parameters,seedCurve,map_ofNat]
lemma seed_incidence : H 1 0 seedCurve = 0 := by
  have he : H (1 : Polynomial K) 0 seedCurve = 5*((11318) + (34661)*X^1 + (77742)*X^2 + (115454)*X^3 + (141180)*X^4 + (132372)*X^5 + (104704)*X^6 + (65336)*X^7 + (34792)*X^8 + (13274)*X^9 + (4342)*X^10 + (608)*X^11 + (220)*X^12) := by
    dsimp [H,seedCurve]
    ring
  have hz : (5 : Polynomial K)=0 := by
    have h : (5 : K)=0 := by decide
    simpa only [map_ofNat,map_zero] using congrArg (Polynomial.C : K →+* Polynomial K) h
  rw [he,hz,zero_mul]
set_option profiler true in
lemma seed_equations (i : Fin 13) :
    MvPolynomial.eval₂Hom (RingHom.id K) seed (equations 1 0 parameters i)=0 := by
  rw [equations_eval,curveEval_seed]
  simpa using congrArg (fun p : Polynomial K => p.coeff i.val) seed_incidence

def rawGradient : Fin 5 → Polynomial K := ![(1108) + (2733)*X^1 + (6002)*X^2 + (7280)*X^3 + (10416)*X^4 + (6742)*X^5 + (10920)*X^6 + (2936)*X^7 + (8032)*X^8 + (744)*X^9 + (2720)*X^10,
(57) + (14)*X^1 + (402)*X^2 + (140)*X^3 + (1130)*X^4 + (608)*X^5 + (1472)*X^6 + (784)*X^7 + (1032)*X^8 + (448)*X^9 + (368)*X^10,
(87296) + (217600)*X^1 + (437120)*X^2 + (547200)*X^3 + (577360)*X^4 + (443970)*X^5 + (291200)*X^6 + (139200)*X^7 + (56080)*X^8 + (14080)*X^9 + (2848)*X^10,
(-1008)*X^2 + (-588)*X^3 + (-714)*X^4 + (-1092)*X^5 + (-1050)*X^6 + (-252)*X^7,
(-1344) + (-658)*X^1 + (-1764)*X^2 + (-2688)*X^3 + (-2940)*X^4 + (-1680)*X^5 + (-2268)*X^6 + (-1652)*X^7 + (-756)*X^8]
lemma seed_raw_gradient : gradient (1 : Polynomial K) 0 seedCurve = rawGradient := by
  funext i
  fin_cases i <;> dsimp [gradient,seedCurve,rawGradient] <;> ring


def expandedGradient : Fin 5 → Polynomial K := ![(3) + (3)*X^1 + (2)*X^2 + (1)*X^4 + (2)*X^5 + (1)*X^7 + (2)*X^8 + (4)*X^9,
(2) + (4)*X^1 + (2)*X^2 + (3)*X^5 + (2)*X^6 + (4)*X^7 + (2)*X^8 + (3)*X^9 + (3)*X^10,
(1) + (3)*X^10,
(2)*X^2 + (2)*X^3 + (1)*X^4 + (3)*X^5 + (3)*X^7,
(1) + (2)*X^1 + (1)*X^2 + (2)*X^3 + (2)*X^6 + (3)*X^7 + (4)*X^8]
lemma seed_gradient : gradient (1 : Polynomial K) 0 seedCurve = expandedGradient := by
  rw [seed_raw_gradient]
  have h14 : (14 : Polynomial K)=4 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (14 : K)=4)
  have h57 : (57 : Polynomial K)=2 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (57 : K)=2)
  have h140 : (140 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (140 : K)=0)
  have h252 : (252 : Polynomial K)=2 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (252 : K)=2)
  have h368 : (368 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (368 : K)=3)
  have h402 : (402 : Polynomial K)=2 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (402 : K)=2)
  have h448 : (448 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (448 : K)=3)
  have h588 : (588 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (588 : K)=3)
  have h608 : (608 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (608 : K)=3)
  have h658 : (658 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (658 : K)=3)
  have h714 : (714 : Polynomial K)=4 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (714 : K)=4)
  have h744 : (744 : Polynomial K)=4 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (744 : K)=4)
  have h756 : (756 : Polynomial K)=1 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (756 : K)=1)
  have h784 : (784 : Polynomial K)=4 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (784 : K)=4)
  have h1008 : (1008 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1008 : K)=3)
  have h1032 : (1032 : Polynomial K)=2 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1032 : K)=2)
  have h1050 : (1050 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1050 : K)=0)
  have h1092 : (1092 : Polynomial K)=2 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1092 : K)=2)
  have h1108 : (1108 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1108 : K)=3)
  have h1130 : (1130 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1130 : K)=0)
  have h1344 : (1344 : Polynomial K)=4 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1344 : K)=4)
  have h1472 : (1472 : Polynomial K)=2 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1472 : K)=2)
  have h1652 : (1652 : Polynomial K)=2 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1652 : K)=2)
  have h1680 : (1680 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1680 : K)=0)
  have h1764 : (1764 : Polynomial K)=4 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (1764 : K)=4)
  have h2268 : (2268 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (2268 : K)=3)
  have h2688 : (2688 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (2688 : K)=3)
  have h2720 : (2720 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (2720 : K)=0)
  have h2733 : (2733 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (2733 : K)=3)
  have h2848 : (2848 : Polynomial K)=3 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (2848 : K)=3)
  have h2936 : (2936 : Polynomial K)=1 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (2936 : K)=1)
  have h2940 : (2940 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (2940 : K)=0)
  have h6002 : (6002 : Polynomial K)=2 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (6002 : K)=2)
  have h6742 : (6742 : Polynomial K)=2 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (6742 : K)=2)
  have h7280 : (7280 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (7280 : K)=0)
  have h8032 : (8032 : Polynomial K)=2 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (8032 : K)=2)
  have h10416 : (10416 : Polynomial K)=1 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (10416 : K)=1)
  have h10920 : (10920 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (10920 : K)=0)
  have h14080 : (14080 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (14080 : K)=0)
  have h56080 : (56080 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (56080 : K)=0)
  have h87296 : (87296 : Polynomial K)=1 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (87296 : K)=1)
  have h139200 : (139200 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (139200 : K)=0)
  have h217600 : (217600 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (217600 : K)=0)
  have h291200 : (291200 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (291200 : K)=0)
  have h437120 : (437120 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (437120 : K)=0)
  have h443970 : (443970 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (443970 : K)=0)
  have h547200 : (547200 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (547200 : K)=0)
  have h577360 : (577360 : Polynomial K)=0 := by
    simpa only [map_ofNat,map_zero,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (577360 : K)=0)
  have hm1 : (-(1 : Polynomial K))=4 := by
    simpa only [map_neg,map_ofNat,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (-(1 : K))=4)
  have hm2 : (-(2 : Polynomial K))=3 := by
    simpa only [map_neg,map_ofNat,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (-(2 : K))=3)
  have hm3 : (-(3 : Polynomial K))=2 := by
    simpa only [map_neg,map_ofNat,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (-(3 : K))=2)
  have hm4 : (-(4 : Polynomial K))=1 := by
    simpa only [map_neg,map_ofNat,map_one] using congrArg (Polynomial.C : K →+* Polynomial K)
      (by decide : (-(4 : K))=1)
  funext i
  fin_cases i <;> simp only [rawGradient,expandedGradient,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,h14,h57,h140,h252,h368,h402,h448,h588,h608,h658,h714,h744,h756,h784,h1008,h1032,h1050,h1092,h1108,h1130,h1344,h1472,h1652,h1680,h1764,h2268,h2688,h2720,h2733,h2848,h2936,h2940,h6002,h6742,h7280,h8032,h10416,h10920,h14080,h56080,h87296,h139200,h217600,h291200,h437120,h443970,h547200,h577360,hm1,hm2,hm3,hm4,neg_zero,zero_mul,one_mul,zero_add,add_zero]
  all_goals ring

#print axioms seed_incidence
#print axioms seed_gradient
end DeformedConic
