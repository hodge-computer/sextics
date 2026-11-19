import Proposal.GenericLineSpecialization
import Proposal.GenericSourceFamily
import Proposal.GenericMinorInverse
import Proposal.CoefficientFunctionalMap
import Proposal.CubicDenominatorEvaluation

/-! The generic degree-27 cubic contact certificate, over the coefficient ring
regular at (alpha,beta)=(1,2). All eight functional constraints are proved from
an exact specialized inverse and functorial quotient normal forms. -/
noncomputable section
open scoped BigOperators
namespace QuadricContact.GenericCubicCertificate
open MvPolynomial
open ParameterSpecialization ParameterEliminant GenericCubicLines

abbrev K := ParameterSpecialization.Coefficients
abbrev A := ParameterEliminant.E
abbrev Poly := MvPolynomial (Fin 4) K

def powerBasis : Module.Basis (Fin 27) K A :=
  AdjoinRootSpecialization.basis ParameterEliminant.P P_monic P_natDegree

def representation : A →ₐ[K] Matrix (Fin 27) (Fin 27) K :=
  Algebra.leftMulMatrix powerBasis

def sources : Fin 8 → A :=
  ConcreteLine.sourceCoefficients pe qe se ke x y z w

def minor : Matrix (Fin 8) (Fin 8) K := sourceMinor powerBasis sources

 theorem special_monic : GenericSpecialization.P.Monic := by
  rw [← P_specialize]
  exact P_monic.map ParameterSpecialization.specialize

 theorem special_natDegree : GenericSpecialization.P.natDegree = 27 := by
  rw [← P_specialize, P_monic.natDegree_map, P_natDegree]

 theorem sources_specialize (i : Fin 8) :
    toSpecial (sources i) =
      AdjoinRoot.mk GenericSpecialization.P (GenericSpecialization.sourcePolyFamily i) := by
  rw [sources, sourceCoefficients_map]
  simp only [pe, qe, se, ke, toSpecial_algebraMap, specialize_p, specialize_q,
    specialize_s, specialize_k, map_ofNat, toSpecial_x, toSpecial_y, toSpecial_z, toSpecial_w]
  exact GenericSpecialization.sourceCoefficients_mk i

 theorem minor_specialize : minor.map ParameterSpecialization.specialize =
    GenericSpecialization.sourceMinor := by
  unfold minor powerBasis
  rw [sourceMinor_map_named ParameterSpecialization.specialize ParameterEliminant.P
    P_monic P_natDegree GenericSpecialization.P P_specialize.symm special_monic
    special_natDegree (P_specialize ▸ dvd_refl GenericSpecialization.P) sources]
  ext i j : 2
  change (AdjoinRootSpecialization.basis GenericSpecialization.P special_monic
      special_natDegree).repr (toSpecial (sources i)) (Fin.castAdd 19 j) = _
  rw [sources_specialize, AdjoinRootSpecialization.basis_repr,
    AdjoinRoot.modByMonicHom_mk]
  rw [(Polynomial.modByMonic_eq_self_iff special_monic).mpr (by
    apply Polynomial.degree_lt_degree
    rw [special_natDegree]
    exact GenericSpecialization.sourcePolyFamily_natDegree i)]
  exact (GenericSpecialization.sourceMinor_coefficient i j).symm

 theorem minor_isUnit : IsUnit minor.det := by
  apply RegularSpecialization.isUnit_det_of_specialized_right_inverse
    ParameterSpecialization.point minor GenericSpecialization.sourceInverse
  change minor.map ParameterSpecialization.specialize * GenericSpecialization.sourceInverse = 1
  rw [minor_specialize]
  exact GenericSpecialization.source_inverse

def weights : Fin 27 → K := sourceWeights minor

def D : Poly := CubicMatrixCertificate.denominator representation x y

def N : Fin 4 → Poly :=
  CubicMatrixCertificate.numerators representation ParameterSpecialization.k x y z w weights 0

def F : Poly := ConcreteLine.cubic ParameterSpecialization.p ParameterSpecialization.q
  ParameterSpecialization.s ParameterSpecialization.k ParameterSpecialization.u
  ParameterSpecialization.v

 theorem powerBasis_zero : powerBasis 0 = 1 := by
  simp [powerBasis]

 theorem functional_sources (i : Fin 8) :
    CubicMatrixCertificate.coefficientFunctional representation weights 0 (sources i) =
      if i = 3 then 1 else 0 :=
  sourceWeights_matrix powerBasis sources minor_isUnit powerBasis_zero i

 theorem D_ne_zero : D ≠ 0 :=
  CubicMatrixCertificate.denominator_ne_zero representation x y

 theorem D_norm_fiber {R : Type*} [CommRing R] (g : K →+* R) :
    MvPolynomial.eval₂Hom (Polynomial.C.comp g)
      ![(2 : Polynomial R) * Polynomial.X ^ 2, 0, 1, 1] D =
      (((2 : Polynomial R) * Polynomial.X ^ 2) •
        (1 : Matrix (Fin 27) (Fin 27) (Polynomial R)) -
        ((representation (x+y)).map g).map (Polynomial.C : R →+* Polynomial R)).det :=
  CubicMatrixCertificate.denominator_norm_fiber representation x y g

/-- The localization instance paths have the same coefficient predicate. -/
 theorem homogeneous_instance (P : Poly) (d : ℕ)
    (h : @MvPolynomial.IsHomogeneous (Fin 4) K
      (inferInstance : CommRing K).toCommSemiring P d) : P.IsHomogeneous d := by
  simpa only [MvPolynomial.IsHomogeneous, MvPolynomial.IsWeightedHomogeneous] using h

 theorem D_homogeneous : D.IsHomogeneous 27 := by
  apply homogeneous_instance
  simpa only [D, Fintype.card_fin] using
    CubicMatrixCertificate.denominator_homogeneous representation x y

 theorem N_homogeneous (i : Fin 4) : (N i).IsHomogeneous 27 := by
  apply homogeneous_instance
  simpa only [N, Fintype.card_fin] using
    CubicMatrixCertificate.numerators_homogeneous representation
      ParameterSpecialization.k x y z w weights 0 i

 theorem equations : HodgeTestbed.Equations F (X 1 * X 2) D N 0 := by
  apply CubicMatrixCertificate.equations_of_coefficients representation
    ParameterSpecialization.p ParameterSpecialization.q ParameterSpecialization.s
    ParameterSpecialization.k ParameterSpecialization.u ParameterSpecialization.v
    x y z w weights 0
  · exact rel0_zero
  · exact rel1_zero
  · exact rel2_zero
  · exact rel3_zero
  · exact D_ne_zero
  · exact functional_sources

 theorem directional_identity : HodgeTestbed.directional F N = (X 1 * X 2) * D :=
  equations.e1

 theorem divergence_identity : HodgeTestbed.divergenceNumerator D N = 0 := by
  simpa using equations.e2

 theorem certificate : D ≠ 0 ∧ D.IsHomogeneous 27 ∧
    (∀ i, (N i).IsHomogeneous 27) ∧
    HodgeTestbed.Equations F (X 1 * X 2) D N 0 :=
  ⟨D_ne_zero, D_homogeneous, N_homogeneous, equations⟩

end QuadricContact.GenericCubicCertificate
#print axioms QuadricContact.GenericCubicCertificate.certificate
