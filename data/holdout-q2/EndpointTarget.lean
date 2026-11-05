import Proposal.EndpointFractionLift
import Proposal.ReflectionCombination
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
namespace HoldoutEndpointTarget
open MvPolynomial HoldoutEndpointHorizontal

def F : BasePoly := HoldoutAlgebra.sextic (X 0) (X 1) (X 2) (X 3) (X 4) (X 5)
def commonTarget : BasePoly := HoldoutAlgebra.commonTarget (X 0) (X 1) (X 3) (X 4)
def A : BasePoly := HoldoutAlgebra.target (X 0) (X 1) (X 2) (X 3) (X 4)
def reflectionTarget (k : ℂ) : BasePoly := commonTarget*HoldoutEndpointLift.delta k

abbrev Parameters := MvPolynomial (Fin 2) ℂ
def complexMap : ℂ →+* FunctionField := baseMap.comp C
def parameterMap : Parameters →+* FunctionField := eval₂Hom complexMap parameter

@[simp] theorem parameterMap_C (r : ℂ) : parameterMap (C r)=constant r := by
  simp [parameterMap,complexMap,constant]
@[simp] theorem parameterMap_X (i : Fin 2) : parameterMap (X i)=parameter i := by
  simp [parameterMap]

theorem horizontal_parameterMap (k : ℂ) (i : Fin 4) (P : Parameters) :
    horizontal k i (parameterMap P)=0 := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p j hp =>
      simp only [map_mul,Derivation.leibniz,smul_eq_mul,hp,parameterMap_X,
        horizontal_parameter,mul_zero,zero_add]

def cubic (k : ℂ) : MvPolynomial (Fin 4) Parameters :=
  HoldoutAlgebra.cubic
    (C (1+X 0^6)) (C (1+X 1^6)) (C (X 0*X 1)) (C (X 1*C (k^2)))
    (X 0) (X 1) (X 2) (X 3)

def source : MvPolynomial (Fin 4) Parameters :=
  C (C (1/2 : ℂ)*X 0^3*X 1^2)*X 0^3*X 1^2

def pullback (k : ℂ) : MvPolynomial (Fin 4) Parameters →+* FunctionField :=
  activeMap parameterMap k

@[simp] theorem pullback_C (k : ℂ) (r : Parameters) : pullback k (C r)=parameterMap r := by
  simp [pullback,activeMap]
@[simp] theorem pullback_X (k : ℂ) (i : Fin 4) : pullback k (X i)=active k i := by
  simp [pullback,activeMap]

theorem constant_root {k : ℂ} (hk : k^2+k+1=0) :
    constant k^2+constant k+1=0 := by
  simpa only [complexMap,RingHom.comp_apply,map_add,map_pow,map_one,map_zero,constant]
    using congrArg complexMap hk

/-- The polynomial map with passive ratios is exactly the immutable sextic. -/
theorem pullback_cubic {k : ℂ} (hk : k^2+k+1=0) : pullback k (cubic k)=baseMap F := by
  have he := HoldoutAlgebra.cubic_ratio_substitution (constant_root hk)
    (coordinate 0) (coordinate 1) (coordinate 2) (coordinate 3) (coordinate 4) (coordinate 5)
    (coordinate_ne_zero 0) (coordinate_ne_zero 1)
  simpa [pullback,cubic,activeMap,active,parameterMap,parameter,complexMap,
    HoldoutAlgebra.cubic,HoldoutAlgebra.sextic,F,coordinate,constant] using he

theorem constant_half : constant (1/2 : ℂ)=(1/2 : FunctionField) := by
  change complexMap (1/2 : ℂ)=_
  rw [map_div₀,map_one,map_ofNat]

theorem pullback_source : ∀ k : ℂ, pullback k source=baseMap commonTarget/2 := by
  intro k
  have he := HoldoutAlgebra.source_ratio_substitution
    (coordinate 0) (coordinate 1) (coordinate 3) (coordinate 4)
    (coordinate_ne_zero 0) (coordinate_ne_zero 1)
  simp only [source,map_mul,map_pow,pullback_C,pullback_X,parameterMap_C,
    parameterMap_X,constant_half,active,parameter,Matrix.cons_val] at ⊢
  simp only [commonTarget,HoldoutAlgebra.commonTarget,map_mul,map_pow,coordinate] at he ⊢
  linear_combination he/2

theorem pullback_source_density (k : ℂ) :
    2*baseMap (HoldoutEndpointLift.delta k)*pullback k source=baseMap (reflectionTarget k) := by
  rw [pullback_source]
  simp only [reflectionTarget,map_mul]
  ring

theorem target_combination {k : ℂ} (hk : k^2+k+1=0) :
    C ((2+k)/3)*reflectionTarget k+C ((2+k^2)/3)*reflectionTarget (k^2)=A := by
  have h1 := HoldoutReflectionCombination.target_decomposition_delta hk (1 : ℂ) 1 0
  have h2 := HoldoutReflectionCombination.target_decomposition_delta hk (1 : ℂ) 0 1
  simp only [HoldoutAlgebra.delta,one_pow,zero_pow (by decide : (2:ℕ)≠0),
    mul_zero,sub_zero,one_mul,mul_one,zero_sub] at h1 h2
  have hp1 := congrArg (C : ℂ →+* BasePoly) h1
  have hp2 := congrArg (C : ℂ →+* BasePoly) h2
  simp only [map_add,map_mul,map_pow,map_sub,map_zero,map_one,map_neg] at hp1 hp2
  dsimp [reflectionTarget,commonTarget,A,HoldoutAlgebra.commonTarget,
    HoldoutAlgebra.target,HoldoutEndpointLift.delta]
  simp only [map_pow]
  linear_combination
    -(X 0 : BasePoly)^3*X 1^2*X 3^3*X 4^2*X 2^2*hp1+
    -(X 0 : BasePoly)^3*X 1^2*X 3^3*X 4^2*X 5^2*hp2

theorem hasCertificate_of_endpoints {k : ℂ} (hk : k^2+k+1=0)
    (h1 : HodgeComputer.HasCertificate F (reflectionTarget k) 2)
    (h2 : HodgeComputer.HasCertificate F (reflectionTarget (k^2)) 2) :
    HodgeComputer.HasCertificate F A 2 := by
  have h := HoldoutReflectionCombination.hasCertificate_combine_q2
    ((2+k)/3) ((2+k^2)/3) h1 h2
  rwa [target_combination hk] at h

theorem exists_endpoint_root : ∃ k : ℂ, k^2+k+1=0 := by
  have hdeg : (Polynomial.X^2+Polynomial.X+1 : Polynomial ℂ).degree=2 := by
    compute_degree!
  obtain ⟨k,hk⟩ := Complex.exists_root (by rw [hdeg]; decide)
  exact ⟨k,by simpa only [Polynomial.IsRoot,Polynomial.eval_add,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_one] using hk⟩

theorem hasCertificate_of_endpoint_solver
    (solve : ∀ k : ℂ, k^2+k+1=0 → HodgeComputer.HasCertificate F (reflectionTarget k) 2) :
    HodgeComputer.HasCertificate F A 2 := by
  obtain ⟨k,hk⟩ := exists_endpoint_root
  exact hasCertificate_of_endpoints hk (solve k hk) (solve (k^2) (HoldoutAlgebra.square_is_root hk))

end HoldoutEndpointTarget

#print axioms HoldoutEndpointTarget.pullback_cubic
#print axioms HoldoutEndpointTarget.pullback_source_density
#print axioms HoldoutEndpointTarget.hasCertificate_of_endpoints
