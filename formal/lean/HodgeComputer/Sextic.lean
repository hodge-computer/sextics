import HodgeComputer.Verify

/-! Polynomial notation for the sextic constructions in projective five-space.
The general certificate contract is defined independently in `Verify`. -/

namespace HodgeComputer.Sextic

abbrev Poly := MvPolynomial (Fin 6) ℂ
abbrev Coeff := MvPolynomial (Fin 5) ℂ

end HodgeComputer.Sextic
