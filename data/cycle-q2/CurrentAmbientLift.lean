import Proposal.Workspace

/-! Reciprocal-cubic, adjoint-current, and coordinate-transport identities.
Off-hypersurface errors and moving parameter derivatives are retained. -/
noncomputable section
namespace CycleQ2ActualLift
open scoped BigOperators
variable {K : Type*} [Field K]

/-- Exact binding of the reciprocal cubic to the actual six-term plane cubic. -/
theorem reciprocal_cubic_binding (a s L M N B : K) :
    L * (s*a+M)^3 + M*(s-3*L)*(s*a+M)^2 +
      (3*L*M^2-2*M^2*s+N*s^2)*(s*a+M) +
      (M^3*(s-L)-N*M*s^2+B*s^3) =
        s^3*(L*a^3+M*a^2+N*a+B) := by
  ring

/-- This is the numerator identity behind zeta*xi^3+xi+1=G*Gamma.
No relation defining the cubic has been imposed. -/
theorem reciprocal_defining_numerator (c E gamma C1 L : K) :
    (3*E+gamma*c)^3 +
      3*(3*E*C1-gamma^2)*(3*E+gamma*c)*c^2 +
      (27*L*E^2-9*E*C1*gamma+2*gamma^3)*c^3 =
        27*E^2*(L*c^3+C1*c^2+gamma*c+E) := by
  ring

def H (z x : K) := 1+3*z*x^2
 def S0 (z x : K) := z*x^3+x+1
 def nu (z x : K) := -x^3/H z x
 def nuX (z x : K) := -3*x^2*(1+z*x^2)/(H z x)^2
 def nuZ (z x : K) := 3*x^5/(H z x)^2
 def A0 (z : K) := z*(27*z+4)

/-- The universal ODE has this NONZERO off-cubic term, not zero. -/
theorem off_cubic_ode (z x : K) (hH : H z x ≠ 0) :
    A0 z * (nuZ z x + nuX z x * nu z x) +
      (54*z+6)*nu z x + 6*x =
        -6*x*(S0 z x-2)*S0 z x/(H z x)^3 := by
  unfold A0 nuZ nuX nu S0
  field_simp [hH]
  unfold H
  ring

/-- Full scalar adjoint current divergence. The last two inputs represent
sum_i D_i(H_i) and sum_i H_i D_i(Gamma); neither is frozen. -/
def adjointDiv (z x G GammaZ V Vz Vzz sumDHi sumHiGammaI : K) : K :=
  (A0 z*Vzz+(54*z+2)*Vz)*x +
  (A0 z*Vz-2*V)*(nu z x+G*GammaZ/H z x) -
  ((54*z+4)*V+A0 z*Vz)*nu z x -
  A0 z*V*(nuZ z x+nuX z x*(nu z x+G*GammaZ/H z x)) +
  x*sumDHi+G*sumHiGammaI/H z x

def forcing (z V Vz Vzz sumDHi : K) : K :=
  sumDHi+A0 z*Vzz+(54*z+2)*Vz+6*V

def regularCorrection (z x Gamma GammaZ V Vz sumHiGammaI : K) : K :=
  (sumHiGammaI+(A0 z*Vz-2*V-A0 z*V*nuX z x)*GammaZ)/H z x +
    6*V*Gamma*x*(S0 z x-2)/(H z x)^3

/-- Exact ambient identity, BEFORE setting S0-G*Gamma to zero. -/
theorem adjoint_ambient_with_defining_error
    (z x G Gamma GammaZ V Vz Vzz sumDHi sumHiGammaI : K)
    (hH : H z x ≠ 0) :
    adjointDiv z x G GammaZ V Vz Vzz sumDHi sumHiGammaI =
      x*forcing z V Vz Vzz sumDHi +
      G*regularCorrection z x Gamma GammaZ V Vz sumHiGammaI +
      6*V*x*(S0 z x-2)*(S0 z x-G*Gamma)/(H z x)^3 := by
  unfold adjointDiv forcing regularCorrection A0 nuZ nuX nu S0
  field_simp [hH]
  unfold H
  ring

theorem adjoint_ambient_of_actual_binding
    (z x G Gamma GammaZ V Vz Vzz sumDHi sumHiGammaI : K)
    (hH : H z x ≠ 0) (hbinding : S0 z x = G*Gamma) :
    adjointDiv z x G GammaZ V Vz Vzz sumDHi sumHiGammaI =
      x*forcing z V Vz Vzz sumDHi +
      G*regularCorrection z x Gamma GammaZ V Vz sumHiGammaI := by
  rw [adjoint_ambient_with_defining_error z x G Gamma GammaZ V Vz Vzz
    sumDHi sumHiGammaI hH, hbinding, sub_self]
  ring

/-- The mixed moving-Jacobian terms cancel, rather than being omitted. -/
theorem inverse_piola_four_directions
    (j Jzz : K) (zi ji Fi Fii Fiz : Fin 3 → K) :
    (∑ i : Fin 3, (ji i * Fi i + j * (Fii i + zi i * Fiz i))) + j*Jzz -
      (∑ i : Fin 3, (ji i * Fi i + zi i*j*Fiz i)) =
        j*((∑ i : Fin 3, Fii i)+Jzz) := by
  have h : (∑ i : Fin 3, (ji i * Fi i + j * (Fii i + zi i * Fiz i))) -
      (∑ i : Fin 3, (ji i * Fi i + zi i*j*Fiz i)) =
      ∑ i : Fin 3, j * Fii i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← Finset.mul_sum] at h
  linear_combination h

/-- Literal tangent lift with all four base directions and all mixed jets. -/
theorem tangent_lift_four_directions
    (g : K) (Gj gj uj duj duja : Fin 4 → K) (hg : g ≠ 0) :
    (∑ i : Fin 4, (gj i*uj i+g*duj i)) -
      (∑ i : Fin 4, (gj i*uj i+Gj i*duja i)) =
      g*(∑ i : Fin 4, (duj i-Gj i*duja i/g)) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hg]
  ring

#print axioms reciprocal_cubic_binding
#print axioms reciprocal_defining_numerator
#print axioms adjoint_ambient_with_defining_error
#print axioms inverse_piola_four_directions
#print axioms tangent_lift_four_directions
end CycleQ2ActualLift
