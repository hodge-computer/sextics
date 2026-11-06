import HodgeComputer.Constructions.FiniteAlgebra.RegularSpecialization
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic.NormNum

/-! The exact two-parameter coefficient ring for the quadric-contact cubic.
Only denominators nonzero at (alpha,beta)=(1,2) are inverted. -/
namespace ParameterSpecialization

abbrev PolynomialRing := MvPolynomial (Fin 2) ℚ

noncomputable def point : PolynomialRing →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) ![1, 2]

abbrev Coefficients := RegularSpecialization.Coefficients point

noncomputable def specialize : Coefficients →+* ℚ :=
  RegularSpecialization.specialize point

instance : Nontrivial Coefficients := specialize.domain_nontrivial

instance : IsDomain Coefficients :=
  IsLocalization.isDomain_of_le_nonZeroDivisors
    (M := RegularSpecialization.denominators point) Coefficients (by
    intro r hr
    apply mem_nonZeroDivisors_of_ne_zero
    intro hz
    exact hr (by rw [hz, map_zero]))

noncomputable def scalar (q : ℚ) : Coefficients :=
  algebraMap PolynomialRing Coefficients (MvPolynomial.C q)

noncomputable def alpha : Coefficients :=
  algebraMap PolynomialRing Coefficients (MvPolynomial.X 0)

noncomputable def beta : Coefficients :=
  algebraMap PolynomialRing Coefficients (MvPolynomial.X 1)

@[simp] theorem specialize_scalar (q : ℚ) : specialize (scalar q) = q := by
  change RegularSpecialization.specialize point
    (algebraMap PolynomialRing Coefficients (MvPolynomial.C q)) = q
  rw [RegularSpecialization.specialize_algebraMap]
  simp [point]

@[simp] theorem specialize_alpha : specialize alpha = 1 := by
  change RegularSpecialization.specialize point
    (algebraMap PolynomialRing Coefficients (MvPolynomial.X 0)) = 1
  rw [RegularSpecialization.specialize_algebraMap]
  simp [point]

@[simp] theorem specialize_beta : specialize beta = 2 := by
  change RegularSpecialization.specialize point
    (algebraMap PolynomialRing Coefficients (MvPolynomial.X 1)) = 2
  rw [RegularSpecialization.specialize_algebraMap]
  simp [point]

noncomputable def p : Coefficients := 40 * alpha^2
noncomputable def q : Coefficients := 40 * alpha * beta
noncomputable def s : Coefficients := 40 * beta^2
noncomputable def k : Coefficients := scalar (20/7) * alpha * (1+2*beta^2)
noncomputable def u : Coefficients := 16 * (1+alpha^6)
noncomputable def v : Coefficients := 16 * (1+beta^6)

@[simp] theorem specialize_p : specialize p = 40 := by norm_num [p, map_ofNat]
@[simp] theorem specialize_q : specialize q = 80 := by norm_num [q, map_ofNat]
@[simp] theorem specialize_s : specialize s = 160 := by norm_num [s, map_ofNat]
@[simp] theorem specialize_k : specialize k = 180/7 := by norm_num [k, map_ofNat]
@[simp] theorem specialize_u : specialize u = 32 := by norm_num [u, map_ofNat]
@[simp] theorem specialize_v : specialize v = 1040 := by norm_num [v, map_ofNat]

theorem isUnit_k : IsUnit k := by
  apply (RegularSpecialization.isUnit_iff_specialize_ne_zero point k).mpr
  change specialize k ≠ 0
  norm_num

theorem isUnit_u : IsUnit u := by
  apply (RegularSpecialization.isUnit_iff_specialize_ne_zero point u).mpr
  change specialize u ≠ 0
  norm_num

theorem isUnit_v : IsUnit v := by
  apply (RegularSpecialization.isUnit_iff_specialize_ne_zero point v).mpr
  change specialize v ≠ 0
  norm_num

theorem isUnit_leadingCoefficient : IsUnit (u^10*v) := isUnit_u.pow 10 |>.mul isUnit_v

end ParameterSpecialization
