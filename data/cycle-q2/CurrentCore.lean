import Proposal.Workspace

/-! Source-bound physical current. Generated definitions are polynomials,
not an assertion of the saved partial identity or a completed certificate.
Scalar divisions occur only inside constant coefficients in ℂ.
No native_decide, axioms, admissions, or external data-reading occurs here. -/
noncomputable section
namespace CycleQ2Concrete
open MvPolynomial
abbrev Poly := HodgeComputer.AmbientPoly 5
end CycleQ2Concrete
