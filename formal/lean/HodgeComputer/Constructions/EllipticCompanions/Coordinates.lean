import HodgeComputer.Constructions.EllipticCompanions.Residues
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback
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

/- Source component: EllipticFermatCoordinates. -/
section

noncomputable section
namespace CrossedElliptic
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (RatFunc K) := Ring.toIntAlgebra _
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

def a : E K := -(y K+36)/(6*x K)
def b : E K := (y K-36)/(6*x K)

lemma fermat_relation : (a (K := K))^3+(b (K := K))^3+1=0 := by
  dsimp [a,b]
  field_simp [x_ne_zero K]
  linear_combination -216*(relation K)

lemma delta_x : delta (K := K) (x K) = -y K/3 := by
  simp [delta,time_x]
lemma delta_y : delta (K := K) (y K) = -(x K)^2/2 := by
  simp only [delta,Derivation.smul_apply,smul_eq_mul,time_y]
  field_simp [y_ne_zero (K := K)]

lemma delta_a : delta (K := K) (a (K := K)) = (b (K := K))^2 := by
  have hc6 : delta (K := K) (6 : E K) = 0 := (delta (K := K)).map_natCast 6
  have hc36 : delta (K := K) (36 : E K) = 0 := (delta (K := K)).map_natCast 36
  dsimp [a,b]
  rw [Derivation.leibniz_div,map_neg,map_add,hc36,add_zero,
    Derivation.leibniz,hc6,smul_zero,add_zero,delta_x,delta_y]
  simp only [smul_eq_mul]
  field_simp [x_ne_zero K]
  linear_combination -18*(relation K)

lemma delta_b : delta (K := K) (b (K := K)) = -(a (K := K))^2 := by
  have hc6 : delta (K := K) (6 : E K) = 0 := (delta (K := K)).map_natCast 6
  have hc36 : delta (K := K) (36 : E K) = 0 := (delta (K := K)).map_natCast 36
  dsimp [a,b]
  rw [Derivation.leibniz_div,map_sub,hc36,sub_zero,
    Derivation.leibniz,hc6,smul_zero,add_zero,delta_x,delta_y]
  simp only [smul_eq_mul]
  field_simp [x_ne_zero K]
  linear_combination 18*(relation K)

lemma coefficient_a (D : Derivation ℤ K K) : coefficient D (a (K := K)) = 0 := by
  have hc6 : coefficient D (6 : E K) = 0 := (coefficient D).map_natCast 6
  have hc36 : coefficient D (36 : E K) = 0 := (coefficient D).map_natCast 36
  dsimp [a]
  rw [Derivation.leibniz_div,map_neg,map_add,coefficient_y,hc36,
    Derivation.leibniz,hc6,coefficient_x]
  simp
lemma coefficient_b (D : Derivation ℤ K K) : coefficient D (b (K := K)) = 0 := by
  have hc6 : coefficient D (6 : E K) = 0 := (coefficient D).map_natCast 6
  have hc36 : coefficient D (36 : E K) = 0 := (coefficient D).map_natCast 36
  dsimp [b]
  rw [Derivation.leibniz_div,map_sub,coefficient_y,hc36,
    Derivation.leibniz,hc6,coefficient_x]
  simp

end CrossedElliptic
end
end

/- Source component: EllipticBasis. -/
section

noncomputable section
namespace CrossedElliptic
open Polynomial
variable (K : Type*) [Field K]

lemma equation_natDegree : (equation K).natDegree = 2 := by
  rw [equation_eq]
  compute_degree <;> simp

def basis : Module.Basis (Fin 2) (RatFunc K) (E K) :=
  (AdjoinRoot.powerBasis' (equation_monic K)).basis.reindex (finCongr (equation_natDegree K))

lemma basis_apply (i : Fin 2) : basis K i = (y K)^i.val := by
  rw [basis,Module.Basis.reindex_apply]
  rw [(AdjoinRoot.powerBasis' (equation_monic K)).basis_eq_pow]
  rfl

lemma basis_zero : basis K 0 = 1 := by rw [basis_apply]; rfl
lemma basis_one : basis K 1 = y K := by rw [basis_apply]; simp

lemma finrank_eq_two : Module.finrank (RatFunc K) (E K) = 2 := by
  rw [Module.finrank_eq_card_basis (basis K),Fintype.card_fin]

def first : E K →ₗ[RatFunc K] RatFunc K :=
  (Finsupp.lapply (0 : Fin 2) : (Fin 2 →₀ RatFunc K) →ₗ[RatFunc K] RatFunc K).comp (basis K).repr.toLinearMap
def second : E K →ₗ[RatFunc K] RatFunc K :=
  (Finsupp.lapply (1 : Fin 2) : (Fin 2 →₀ RatFunc K) →ₗ[RatFunc K] RatFunc K).comp (basis K).repr.toLinearMap

lemma first_second_expansion (f : E K) :
    f = algebraMap (RatFunc K) (E K) (first K f) +
      algebraMap (RatFunc K) (E K) (second K f)*y K := by
  have h := (basis K).sum_repr f
  rw [Fin.sum_univ_two,basis_zero,basis_one] at h
  simpa only [first,second,LinearMap.comp_apply,Finsupp.lapply_apply,
    LinearEquiv.coe_coe,Algebra.smul_def,mul_one] using h.symm

lemma trace_y : Algebra.trace (RatFunc K) (E K) (y K) = 0 := by
  have h := (AdjoinRoot.powerBasis' (equation_monic K)).trace_gen_eq_nextCoeff_minpoly
  rw [show (AdjoinRoot.powerBasis' (equation_monic K)).gen = y K from rfl] at h
  have hm : minpoly (RatFunc K) (y K) = equation K := by
    simpa only [y,(equation_monic K).leadingCoeff,inv_one,C_1,mul_one] using
      AdjoinRoot.minpoly_root (equation_irreducible K).ne_zero
  rw [hm] at h
  rw [h]
  rw [Polynomial.nextCoeff,equation_natDegree]
  norm_num [equation_eq]
  rw [← map_pow,Polynomial.coeff_C,if_neg (by decide)]

lemma trace_expansion (f : E K) : Algebra.trace (RatFunc K) (E K) f = 2*first K f := by
  conv_lhs => rw [first_second_expansion K f]
  rw [map_add,Algebra.trace_algebraMap,finrank_eq_two]
  have hm : algebraMap (RatFunc K) (E K) (second K f)*y K = (second K f) • y K :=
    (Algebra.smul_def _ _).symm
  rw [hm,map_smul,trace_y,smul_zero,add_zero]
  simp [smul_eq_mul]

end CrossedElliptic
end
end

/- Source component: EllipticTranslationIdentities. -/
section

namespace CrossedEllipticTranslation
variable {R : Type*} [CommRing R]

def xNumerator (x y u v : R) : R := (y-v)^2-(x+u)*(x-u)^2
def yNumerator (x y u v : R) : R :=
  -y*(x-u)^3+(y-v)*(x*(x-u)^2-xNumerator x y u v)

lemma cleared_curve_identity (x y u v : R) :
    (yNumerator x y u v)^2-(xNumerator x y u v)^3+432*(x-u)^6=
      -(x-u)^3*(u^3-3*u^2*x+2*v*y+x^3-y^2+432)*(y^2-x^3+432)+
      (x-u)^3*(u^3-3*u*x^2-v^2+2*v*y+x^3+432)*(v^2-u^3+432) := by
  unfold yNumerator xNumerator
  ring

variable {L : Type*} [Field L]

def slope (x y u v : L) : L := (y-v)/(x-u)
def translatedX (x y u v : L) : L := (slope x y u v)^2-x-u
def translatedY (x y u v : L) : L := -y+slope x y u v*(x-translatedX x y u v)

lemma translatedX_fraction (x y u v : L) (h : x-u≠0) :
    translatedX x y u v=xNumerator x y u v/(x-u)^2 := by
  unfold translatedX slope xNumerator
  field_simp <;> ring

lemma translatedY_fraction (x y u v : L) (h : x-u≠0) :
    translatedY x y u v=yNumerator x y u v/(x-u)^3 := by
  rw [translatedY,translatedX_fraction x y u v h]
  unfold slope yNumerator
  field_simp <;> ring

lemma translated_curve (x y u v : L) (h : x-u≠0)
    (hp : y^2=x^3-432) (hq : v^2=u^3-432) :
    (translatedY x y u v)^2=(translatedX x y u v)^3-432 := by
  have hc := cleared_curve_identity x y u v
  rw [hp,hq] at hc
  have hc' : (yNumerator x y u v)^2-(xNumerator x y u v)^3+432*(x-u)^6=0 := by
    linear_combination hc
  rw [translatedX_fraction x y u v h,translatedY_fraction x y u v h]
  apply (mul_right_injective₀ (pow_ne_zero 6 h))
  field_simp
  linear_combination hc'

lemma inverse_slope (x y u v : L) (h : x-u≠0)
    (h' : translatedX x y u v-u≠0) :
    slope (translatedX x y u v) (translatedY x y u v) u (-v)= -slope x y u v := by
  unfold translatedY slope
  field_simp <;> ring

lemma inverse_x (x y u v : L) (h : x-u≠0)
    (h' : translatedX x y u v-u≠0) :
    translatedX (translatedX x y u v) (translatedY x y u v) u (-v)=x := by
  rw [translatedX,inverse_slope x y u v h h']
  unfold translatedX
  ring

lemma inverse_y (x y u v : L) (h : x-u≠0)
    (h' : translatedX x y u v-u≠0) :
    translatedY (translatedX x y u v) (translatedY x y u v) u (-v)=y := by
  rw [translatedY,inverse_x x y u v h h',inverse_slope x y u v h h']
  unfold translatedY
  ring

end CrossedEllipticTranslation
end

/- Source component: EllipticBasisCoordinates. -/
section

noncomputable section
namespace CrossedElliptic
open Polynomial CrossedRationalResidue
variable (K : Type*) [Field K]

lemma first_one : first K (1 : E K)=1 := by
  change (basis K).repr 1 0=1
  rw [← basis_zero,(basis K).repr_self]
  simp
lemma second_one : second K (1 : E K)=0 := by
  change (basis K).repr 1 1=0
  rw [← basis_zero,(basis K).repr_self]
  simp
lemma second_y : second K (y K)=1 := by
  change (basis K).repr (y K) 1=1
  rw [← basis_one,(basis K).repr_self]
  simp

lemma first_algebraMap (f : RatFunc K) : first K (algebraMap (RatFunc K) (E K) f)=f := by
  have hs : algebraMap (RatFunc K) (E K) f=f • (1 : E K) := by
    rw [Algebra.smul_def,mul_one]
  rw [hs,map_smul,first_one,smul_eq_mul,mul_one]
lemma second_algebraMap (f : RatFunc K) : second K (algebraMap (RatFunc K) (E K) f)=0 := by
  have hs : algebraMap (RatFunc K) (E K) f=f • (1 : E K) := by
    rw [Algebra.smul_def,mul_one]
  rw [hs,map_smul,second_one,smul_zero]
lemma second_coeff_y (f : RatFunc K) :
    second K (algebraMap (RatFunc K) (E K) f*y K)=f := by
  rw [← Algebra.smul_def,map_smul,second_y,smul_eq_mul,mul_one]

lemma x_transcendental : Transcendental K (x K) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc K) (E K)).injective).mpr RatFunc.transcendental_X

lemma map_constant (u : K) : algebraMap (RatFunc K) (E K) (RatFunc.C u)=algebraMap K (E K) u := by
  rw [← RatFunc.algebraMap_eq_C]
  exact (IsScalarTower.algebraMap_apply K (RatFunc K) (E K) u).symm

lemma x_sub_constant_ne_zero (u : K) : x K-algebraMap K (E K) u≠0 := by
  have h := (algebraMap (RatFunc K) (E K)).injective.ne (uniformizer_ne_zero u)
  simpa only [uniformizer,map_sub,map_zero,RatFunc.algebraMap_X,RatFunc.algebraMap_C,x,map_constant] using h

variable [CharZero K]
open CrossedEllipticTranslation

lemma translatedX_expansion (u v : K) :
    translatedX (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v)-algebraMap K (E K) u=
      algebraMap (RatFunc K) (E K)
        (((RatFunc.X : RatFunc K)^3-432+(RatFunc.C v)^2)/(RatFunc.X-RatFunc.C u)^2-
          RatFunc.X-2*RatFunc.C u)+
      algebraMap (RatFunc K) (E K)
        (-2*RatFunc.C v/(RatFunc.X-RatFunc.C u)^2)*y K := by
  have hd := x_sub_constant_ne_zero K u
  have hr := relation K
  simp only [translatedX,slope,map_sub,map_add,map_div₀,map_pow,map_mul,map_neg,map_ofNat,map_constant]
  change ((y K-algebraMap K (E K) v)/(x K-algebraMap K (E K) u))^2-x K-
    algebraMap K (E K) u-algebraMap K (E K) u=
    ((x K)^3-432+(algebraMap K (E K) v)^2)/(x K-algebraMap K (E K) u)^2-
      x K-2*algebraMap K (E K) u+
    (-2*algebraMap K (E K) v/(x K-algebraMap K (E K) u)^2)*y K
  field_simp
  linear_combination hr

lemma translatedX_sub_constant_ne_zero (u v : K) (hv : v≠0) :
    translatedX (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v)-
      algebraMap K (E K) u≠0 := by
  intro h
  rw [translatedX_expansion] at h
  have hs := congrArg (second K) h
  rw [map_add,second_algebraMap,second_coeff_y,map_zero,zero_add] at hs
  have hu : (RatFunc.X : RatFunc K)-RatFunc.C u≠0 := by
    simpa [uniformizer] using uniformizer_ne_zero u
  have hv' : (RatFunc.C v : RatFunc K)≠0 := by
    simpa only [map_zero] using RatFunc.C_injective.ne hv
  exact (div_ne_zero (mul_ne_zero (by norm_num) hv') (pow_ne_zero 2 hu)) hs

lemma translatedX_sub_constant_ne_zero_of_point (u v : K) (hp : v^2=u^3-432) :
    translatedX (x K) (y K) (algebraMap K (E K) u) (algebraMap K (E K) v)-
      algebraMap K (E K) u≠0 := by
  by_cases hv : v=0
  · subst v
    have hu : u≠0 := by intro h; rw [h] at hp; norm_num at hp
    have hu' : algebraMap K (E K) u≠0 := (_root_.map_ne_zero _).mpr hu
    have hd := x_sub_constant_ne_zero K u
    have hp' := congrArg (algebraMap K (E K)) hp
    simp only [map_pow,map_sub,map_zero] at hp'
    have h432 : algebraMap K (E K) (432 : K)=(432 : E K) := map_natCast _ 432
    rw [h432] at hp'
    have hr := relation K
    have he : (x K-algebraMap K (E K) u)^2*
        (translatedX (x K) (y K) (algebraMap K (E K) u) 0-algebraMap K (E K) u)=
        3*(algebraMap K (E K) u)^2*(x K-algebraMap K (E K) u) := by
      unfold translatedX slope
      field_simp
      linear_combination hr-hp'
    rw [map_zero]
    intro hz
    rw [hz,mul_zero] at he
    exact (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hu')) hd) he.symm
  · exact translatedX_sub_constant_ne_zero K u v hv

end CrossedElliptic
end
end

/- Source component: EllipticFermatTranscendence. -/
section

noncomputable section
namespace CrossedElliptic
variable {K : Type*} [Field K] [CharZero K]

lemma fermat_sum_relation : (a (K:=K)+b (K:=K))*x K= -12 := by
  unfold a b
  field_simp [x_ne_zero K]
  ring

lemma fermat_sum_ne_zero : a (K:=K)+b (K:=K)≠0 := by
  intro h
  have he := fermat_sum_relation (K:=K)
  rw [h,zero_mul] at he
  norm_num at he

lemma x_from_fermat : x K= -12/(a (K:=K)+b (K:=K)) := by
  apply (eq_div_iff (fermat_sum_ne_zero (K:=K))).mpr
  linear_combination fermat_sum_relation (K:=K)

lemma fermat_a_transcendental : Transcendental K (a (K:=K)) := by
  intro ha
  have hone : IsAlgebraic K (1 : E K) := by simpa using (isAlgebraic_algebraMap (1 : K) (A:=E K))
  have hb : IsAlgebraic K (b (K:=K)) := by
    apply IsAlgebraic.of_pow (by decide : 0<3)
    have he : b (K:=K)^3= -(a (K:=K))^3-1 := by linear_combination fermat_relation (K:=K)
    rw [he]
    exact (ha.pow 3).neg.sub hone
  apply x_transcendental K
  rw [x_from_fermat (K:=K),div_eq_mul_inv]
  have h12 : IsAlgebraic K (-12 : E K) := by
    have hh : IsAlgebraic K (algebraMap K (E K) (-12 : K)) := isAlgebraic_algebraMap (-12 : K)
    have hc : algebraMap K (E K) (-12 : K)=(-12 : E K) := by
      rw [map_neg]
      congr 1
      exact map_natCast _ 12
    simpa only [hc] using hh
  have hi : IsAlgebraic K ((a (K:=K)+b (K:=K))⁻¹) := IsAlgebraic.inv_iff.mpr (ha.add hb)
  exact h12.mul hi

lemma fermat_scaled_a_transcendental (u : K) (hu : u≠0) :
    Transcendental K (algebraMap K (E K) u*a (K:=K)) := by
  intro hs
  have hu' : algebraMap K (E K) u≠0 := (_root_.map_ne_zero _).mpr hu
  have ha : a (K:=K)=(algebraMap K (E K) u*a (K:=K))/algebraMap K (E K) u := by
    field_simp
  apply fermat_a_transcendental (K:=K)
  rw [ha,div_eq_mul_inv]
  exact hs.mul (IsAlgebraic.inv_iff.mpr (isAlgebraic_algebraMap u))

end CrossedElliptic
end
end
