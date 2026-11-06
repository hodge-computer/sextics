import Proposal.NewLineAlgebra
import Proposal.GoodFiberMinorLink
import Proposal.QuadraticSolver

/-! An actual quadratic-source solver on the full four-parameter holdout cubic.
All invertibility hypotheses are discharged at the exact rational good fiber. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
namespace HoldoutQ2.GenericQuadratic
open MvPolynomial NewLineAlgebra

abbrev K := NewLineAlgebra.Coefficients
abbrev A := NewLineAlgebra.E
abbrev Poly := MvPolynomial (Fin 4) K

def powerBasis : Module.Basis (Fin 27) K A :=
  AdjoinRootSpecialization.basis P P_monic P_natDegree

def representation : A →ₐ[K] Matrix (Fin 27) (Fin 27) K :=
  Algebra.leftMulMatrix powerBasis

def minor : Matrix (Fin 10) (Fin 10) K :=
  QuadraticSolver.sourceMinor powerBasis a b c d lineE lineF lineG lineH

theorem special_monic : NewSpecialization.P.Monic := by
  rw [← P_specialize]
  exact P_monic.map specialize

theorem special_natDegree : NewSpecialization.P.natDegree = 27 := by
  rw [← P_specialize, P_monic.natDegree_map, P_natDegree]

theorem sources_specialize (i : Fin 10) :
    toSpecial (HodgeComputer.CubicSurfaces.LineContact.sourceCoefficients de lineE lineF lineG lineH i) =
      AdjoinRoot.mk NewSpecialization.P (NewSpecialization.sourcePoly i) := by
  rw [HodgeComputer.CubicSurfaces.LineContact.sourceCoefficients_map]
  simp only [de, toSpecial_algebraMap, specialize_d, map_one,
    toSpecial_lineE, toSpecial_lineF, toSpecial_lineG, toSpecial_lineH]
  exact NewSpecialization.sourcePoly_mk i

theorem minor_specialize : minor.map specialize = NewSpecialization.sourceMinor := by
  unfold minor powerBasis
  rw [QuadraticSolver.sourceMinor_map_named specialize P P_monic P_natDegree
    NewSpecialization.P P_specialize.symm special_monic special_natDegree
    (P_specialize ▸ dvd_refl NewSpecialization.P) a b c d lineE lineF lineG lineH]
  change QuadraticSolver.sourceMinor
    (AdjoinRootSpecialization.basis NewSpecialization.P special_monic special_natDegree)
    (specialize a) (specialize b) (specialize c) (specialize d)
    (toSpecial lineE) (toSpecial lineF) (toSpecial lineG) (toSpecial lineH) = _
  rw [specialize_a, specialize_b, specialize_c, specialize_d,
    toSpecial_lineE, toSpecial_lineF, toSpecial_lineG, toSpecial_lineH]
  ext i j : 2
  cases j using Fin.addCases (m := 4) (n := 6) with
  | left j =>
    simp only [QuadraticSolver.sourceMinor, Fin.addCases_left]
    exact (NewSpecialization.sourceMinor_gradient i j).symm
  | right j =>
    simp only [QuadraticSolver.sourceMinor, Fin.addCases_right, map_one]
    rw [NewSpecialization.sourcePoly_mk, AdjoinRootSpecialization.basis_repr,
      AdjoinRoot.modByMonicHom_mk]
    rw [(Polynomial.modByMonic_eq_self_iff special_monic).mpr (by
      apply Polynomial.degree_lt_degree
      rw [special_natDegree]
      exact NewSpecialization.sourcePoly_degree i)]
    exact (NewSpecialization.sourceMinor_coefficient i j).symm

theorem minor_isUnit : IsUnit minor.det := by
  apply RegularSpecialization.isUnit_det_of_specialized_right_inverse
    point minor NewSpecialization.sourceInverse
  change minor.map specialize * NewSpecialization.sourceInverse = 1
  rw [minor_specialize]
  exact NewSpecialization.source_inverse

def F : Poly := HodgeComputer.CubicSurfaces.LineContact.cubic a b c d

def D : Poly := QuadraticSolver.denominator representation lineE lineF

def N (target : Fin 10 → K) : Fin 4 → Poly :=
  QuadraticSolver.combinedNumerators representation d lineE lineF lineG lineH
    (QuadraticSolver.solveCoefficients minor target)

theorem powerBasis_zero : powerBasis 0 = 1 := by simp [powerBasis]

theorem D_ne_zero : D ≠ 0 := QuadraticSolver.denominator_ne_zero representation lineE lineF

theorem D_homogeneous : D.IsHomogeneous 27 :=
  QuadraticSolver.denominator_homogeneous representation lineE lineF

theorem N_homogeneous (target : Fin 10 → K) (i : Fin 4) :
    (N target i).IsHomogeneous 27 :=
  QuadraticSolver.combinedNumerators_homogeneous representation d lineE lineF lineG lineH _ i

theorem equations (target : Fin 10 → K) :
    HodgeTestbed.Equations F (QuadraticSolver.quadratic target) D (N target) 0 := by
  apply QuadraticSolver.equations powerBasis powerBasis_zero a b c d
    lineE lineF lineG lineH target
  · exact NewLineAlgebra.rel0_zero
  · have hh := NewLineAlgebra.rel1_zero
    unfold NewLineChart.rel1 NewLineAlgebra.ce at hh
    unfold HodgeComputer.CubicSurfaces.LineContact.rel1
    linear_combination hh
  · have hh := NewLineAlgebra.rel2_zero
    unfold NewLineChart.rel2 NewLineAlgebra.de at hh
    unfold HodgeComputer.CubicSurfaces.LineContact.rel2
    linear_combination hh
  · exact NewLineAlgebra.rel3_zero
  · exact minor_isUnit

theorem D_norm_fiber {R : Type*} [CommRing R] (φ : K →+* R) :
    MvPolynomial.eval₂Hom (Polynomial.C.comp φ) ![1, 1, Polynomial.X, 0] D =
      ((Polynomial.X : Polynomial R) • (1 : Matrix (Fin 27) (Fin 27) (Polynomial R)) -
        ((representation (lineE+lineF)).map φ).map (Polynomial.C : R →+* Polynomial R)).det :=
  QuadraticSolver.denominator_norm_fiber representation lineE lineF φ

end HoldoutQ2.GenericQuadratic
#print axioms HoldoutQ2.GenericQuadratic.equations
