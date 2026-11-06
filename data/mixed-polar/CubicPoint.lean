import HodgeComputer.Constructions.PolarCubic.Functorial
import Proposal.PhysicalCoordinates

/-! An exact Gaussian-rational point testing the proposed map's open chart.
It lies on the fixed sextic, has nonzero ratio denominators, and gives nonzero
H, J and U_x. This is a pointwise check; transferring nonvanishing to the
physical function field requires a localization/specialization argument.
Original cyclic construction by hodgepodgeconjecture and transitive adaptation by fqlx.
Adapted to mixed-polar for benediamond with OpenAI Codex assistance. -/
namespace CycleCubicPoint
open CyclePhysical PolarCovariants
local notation "ii" => Complex.I
def point (i : Fin 6) : ℂ :=
  if i=0 then 2 else if i=1 then 2*ii else if i=2 then 1-ii else if i=3 then 1+ii else 0
def value : Ambient →+* ℂ := MvPolynomial.eval₂Hom (RingHom.id ℂ) point

lemma on_sextic : value sextic=0 := by
  simp [value,sextic,point]
  apply Complex.ext <;> norm_num [pow_succ,Complex.mul_re,Complex.mul_im]

lemma denominators_nonzero : ∀ i : Fin 4,point i.castSucc.castSucc ≠ 0 := by
  intro i
  fin_cases i <;> simp [point]
  all_goals intro h; have hh := congrArg Complex.re h; norm_num at hh

lemma on_cubic : PolarCubic.cubic (1-ii/8) 1 1 0 0 0 (2*ii) (-2*ii) 1=0 := by
  apply Complex.ext <;>
    norm_num [PolarCubic.cubic,pow_succ,Complex.mul_re,Complex.mul_im]

lemma H_value : H (1-ii/8) 1 1 0 0 0 (2*ii) (-2*ii) 1=324-81*ii/2 := by
  rw [H_diagonal]
  apply Complex.ext <;> norm_num [pow_succ,Complex.mul_re,Complex.mul_im]
lemma J_value : J (1-ii/8) 1 1 0 0 0 (2*ii) (-2*ii) 1=
    -19586258055/64-126049833585*ii/256 := by
  rw [J_diagonal]
  apply Complex.ext <;> norm_num [pow_succ,Complex.mul_re,Complex.mul_im]
lemma H_nonzero : H (1-ii/8) 1 1 0 0 0 (2*ii) (-2*ii) 1≠0 := by
  rw [H_value]
  intro h
  have hh := congrArg Complex.re h
  norm_num at hh
lemma J_nonzero : J (1-ii/8) 1 1 0 0 0 (2*ii) (-2*ii) 1≠0 := by
  rw [J_value]
  intro h
  have hh := congrArg Complex.re h
  norm_num at hh
lemma normal_nonzero : 3*(1-ii/8)*(2*ii)^2≠0 := by
  intro h
  have hh := congrArg Complex.re h
  norm_num [pow_succ,Complex.mul_re,Complex.mul_im] at hh

end CycleCubicPoint
#print axioms CycleCubicPoint.on_sextic
#print axioms CycleCubicPoint.J_nonzero
