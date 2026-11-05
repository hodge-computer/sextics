import Proposal.LineClosure
import Proposal.LineLifting
import Proposal.CubicLift
import Proposal.CoordinateOrder

/-! Assembly of the weighted-line family, polynomial integration, cubic pullback,
and homogeneous extraction. No explicit coefficient list for D is claimed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace CyclicTriple
open MvPolynomial HoldoutConstruction

def quotientSource : HodgeComputer.Poly := X 2*X 0^3
def physicalSource : HodgeComputer.Poly := X 2*X 5^2*X 0^3

theorem physical_homogeneous (k : ℂ) : (hypersurface k 6 3).IsHomogeneous 6 := by
  have hx (i : Fin 6) := MvPolynomial.isHomogeneous_X ℂ i
  have hp (i : Fin 6) (a : ℕ) := MvPolynomial.isHomogeneous_X_pow (R := ℂ) i a
  have h1 := (((hp 2 3).mul (hx 3)).mul (hx 0)).mul (hx 1)
  have h2 := (hp 2 3).mul (hp 5 3)
  have h3 := (((hp 2 2).mul (hx 0)).mul (hx 1)).mul (hp 4 2)
  have h4 := (((hx 2).mul (hx 3)).mul (hp 1 3)).mul (hx 4)
  have h5 := (((hx 2).mul (hp 5 3)).mul (hx 1)).mul (hx 4)
  have h6 := (((hx 3).mul (hp 5 3)).mul (hx 0)).mul (hx 1)
  exact ((((((hp 0 6).add (hp 1 6)).add (hp 2 6)).add (hp 3 6)).add
    (hp 4 6)).add (hp 5 6)).add ((((((h1.add h2).add h3).add h4).add h5).add h6).C_mul k)

theorem source_homogeneous : physicalSource.IsHomogeneous 6 :=
  (((isHomogeneous_X ℂ (2 : Fin 6)).mul (isHomogeneous_X_pow (5 : Fin 6) 2)).mul
    (isHomogeneous_X_pow (0 : Fin 6) 3))

theorem source_pullback : X 5^2*cubeLast quotientSource = physicalSource := by
  simp only [quotientSource, physicalSource, map_mul, map_pow, cubeVariable_X]
  simp only [show (0 : Fin 6) ≠ 5 by decide, show (2 : Fin 6) ≠ 5 by decide, if_false]
  ring

theorem quotient_certificate_data :
    ∃ d : HodgeComputer.Poly, ∃ N : Fin 6 → HodgeComputer.Poly,
      ∃ Q : HodgeComputer.Poly,
        d ≠ 0 ∧ IsRelPrime (hypersurface coupling 2 1) d ∧
        HodgeTestbed.directional (hypersurface coupling 2 1) N = quotientSource*d ∧
        HodgeTestbed.divergenceNumerator d N = hypersurface coupling 2 1*Q := by
  obtain ⟨I,hI,hfinite,_,_,_⟩ := Lifting.exists_field
  letI := hI
  letI := hfinite
  exact quotient_normalized_of_line_family (Lifting.family I) quotientSource

theorem physical_certificate :
    HodgeComputer.HasCertificate (hypersurface coupling 6 3) physicalSource 1 := by
  obtain ⟨d,N,Q,_,hlegal,hnormal,hdiv⟩ := quotient_certificate_data
  obtain ⟨hnormal',hdiv'⟩ := cubic_normalized_identities coupling quotientSource d Q N hnormal hdiv
  rw [source_pullback] at hnormal'
  exact hasCertificate_of_normalized (hypersurface coupling 6 3) physicalSource
    (cubeLast d) (liftNumerators N) (X 5^2*cubeLast Q)
    (physical_homogeneous coupling) source_homogeneous (physical_irreducible coupling).prime
    (cubeLast_legal coupling d hlegal) hnormal' hdiv' 0
    (hypersurface_not_dvd_pderiv_zero coupling 6 3 (by decide))

end CyclicTriple
#print axioms CyclicTriple.physical_certificate
