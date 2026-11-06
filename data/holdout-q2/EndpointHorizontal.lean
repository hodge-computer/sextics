import Proposal.EndpointLift
import HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation
import Mathlib.Analysis.Complex.Basic

/-! Actual fraction-field derivations for the endpoint lift. In particular the
passive ratios are proved constant for every horizontal derivative. -/

noncomputable section
namespace HoldoutEndpointHorizontal
open MvPolynomial

abbrev BasePoly := MvPolynomial (Fin 6) ℂ
abbrev FunctionField := FractionRing BasePoly
abbrev baseMap : BasePoly →+* FunctionField := algebraMap BasePoly FunctionField
def coordinate (i : Fin 6) : FunctionField := baseMap (X i)
def constant (k : ℂ) : FunctionField := baseMap (C k)

theorem coordinate_ne_zero (i : Fin 6) : coordinate i ≠ 0 := by
  exact fun h => X_ne_zero i ((IsFractionRing.injective BasePoly FunctionField)
    (by simpa [coordinate] using h))

def polynomialHorizontal (k : ℂ) (j : Fin 4) : Derivation ℂ BasePoly BasePoly :=
  ![(X 0 : BasePoly) • pderiv 0+(X 3 : BasePoly) • pderiv 3,
    (X 1 : BasePoly) • pderiv 1+(X 4 : BasePoly) • pderiv 4,
    (X 2 : BasePoly) • pderiv 2-(X 5 : BasePoly) • pderiv 5,
    (-2*C k*X 5 : BasePoly) • pderiv 2+(2*C (k^2)*X 2 : BasePoly) • pderiv 5] j

def horizontal (k : ℂ) (j : Fin 4) : Derivation ℚ FunctionField FunctionField :=
  QuadricContactFraction.extend ((polynomialHorizontal k j).restrictScalars ℚ)

@[simp] theorem horizontal_map (k : ℂ) (j : Fin 4) (P : BasePoly) :
    horizontal k j (baseMap P)=baseMap (polynomialHorizontal k j P) :=
  QuadricContactFraction.extend_map _ _

@[simp] theorem horizontal_constant (k r : ℂ) (j : Fin 4) :
    horizontal k j (constant r)=0 := by
  rw [constant,horizontal_map]
  fin_cases j <;>
    simp [polynomialHorizontal,Derivation.sub_apply,Derivation.add_apply,
      Derivation.smul_apply,pderiv_C]

theorem horizontal_map_U (k : ℂ) (P : BasePoly) :
    horizontal k 0 (baseMap P)=baseMap (HoldoutEndpointLift.horizontalU P) := by
  rw [horizontal_map]; rfl
theorem horizontal_map_V (k : ℂ) (P : BasePoly) :
    horizontal k 1 (baseMap P)=baseMap (HoldoutEndpointLift.horizontalV P) := by
  rw [horizontal_map]; rfl
theorem horizontal_map_S (k : ℂ) (P : BasePoly) :
    horizontal k 2 (baseMap P)=baseMap (HoldoutEndpointLift.horizontalS P) := by
  rw [horizontal_map]; rfl
theorem horizontal_map_T (k : ℂ) (P : BasePoly) :
    horizontal k 3 (baseMap P)=baseMap (HoldoutEndpointLift.horizontalT k P) := by
  rw [horizontal_map]; rfl

def parameter (j : Fin 2) : FunctionField :=
  ![coordinate 3/coordinate 0,coordinate 4/coordinate 1] j

theorem horizontal_parameter (k : ℂ) (i : Fin 4) (j : Fin 2) :
    horizontal k i (parameter j)=0 := by
  fin_cases i <;> fin_cases j <;>
    simp [parameter,Derivation.leibniz_div,coordinate,horizontal_map,
      polynomialHorizontal,Derivation.sub_apply,Derivation.add_apply,
      Derivation.smul_apply,pderiv_X,Pi.single_apply,smul_eq_mul] <;> ring

def active (k : ℂ) (j : Fin 4) : FunctionField :=
  ![coordinate 0^2,coordinate 1^2,
    coordinate 2^2+constant k^2*coordinate 5^2,
    constant k*coordinate 2*coordinate 5] j

def scale (k : ℂ) (j : Fin 4) : FunctionField :=
  ![2*coordinate 0^2,2*coordinate 1^2,
    2*(coordinate 2^2-constant k^2*coordinate 5^2),
    2*(coordinate 2^2-constant k^2*coordinate 5^2)] j

theorem constant_cube {k : ℂ} (hk : k^2+k+1=0) : constant k^3=1 := by
  have h := congrArg (fun r : ℂ => baseMap (C r)) (HoldoutAlgebra.cube_eq_one hk)
  simpa only [map_pow,map_one,constant] using h

theorem horizontal_active {k : ℂ} (hk : k^2+k+1=0) (i j : Fin 4) :
    horizontal k i (active k j)=if j=i then scale k i else 0 := by
  have h3 := constant_cube hk
  fin_cases i <;> fin_cases j <;>
    simp [active,scale,Derivation.leibniz_pow,Derivation.leibniz,
      horizontal_constant,coordinate,horizontal_map,polynomialHorizontal,
      Derivation.sub_apply,Derivation.add_apply,Derivation.smul_apply,
      pderiv_X,Pi.single_apply,smul_eq_mul,constant,map_pow,map_ofNat] <;>
    try ring <;> try simp only [true_or]
  · change _ = 0
    dsimp [constant] at h3
    linear_combination 4*baseMap (C k)*baseMap (X 2)*baseMap (X 5)*h3
  · dsimp [constant] at h3
    linear_combination 2*baseMap (X 2)^2*h3

section ChainRule
variable {O : Type*} [CommRing O]
variable (f : O →+* FunctionField) (k : ℂ)

def activeMap : MvPolynomial (Fin 4) O →+* FunctionField := eval₂Hom f (active k)

theorem horizontal_activeMap (hk : k^2+k+1=0)
    (hc : ∀ i r, horizontal k i (f r)=0)
    (i : Fin 4) (P : MvPolynomial (Fin 4) O) :
    horizontal k i (activeMap f k P)=scale k i*activeMap f k (pderiv i P) :=
  HoldoutChainRule.eval₂_pderiv _ _ _ _ _ (hc i) (horizontal_active hk i) P

end ChainRule
end HoldoutEndpointHorizontal

#print axioms HoldoutEndpointHorizontal.horizontal_parameter
#print axioms HoldoutEndpointHorizontal.horizontal_activeMap
