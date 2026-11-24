import Proposal.GeometricEtaleIncidenceCurve
import Proposal.GeometricSeedSurfaceGradient
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Flat

/-!
# Relative smooth Jacobian patches of the original incidence surface cone

Status: source-only proof draft. No elaboration or kernel replay was run.

The two original incidence equations define explicit standard-smooth
patches over their coefficient algebra after a two-by-two Jacobian minor
is inverted. This is a relative assertion, not only smoothness of a
complex fiber. The existing full-seed Jacobian cover is transported to
these minors by the actual coefficient specialization.

The relative dimension is three for the affine cone. Passing to the
degree-zero projective charts, and shrinking one open of the parameter
base for the whole projective fiber, are separate obligations.

The geometric strategy is due to Ben Diamond and the collaborators cited
in solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RelativeJacobianPatch

open MvPolynomial Matrix

variable {S : Type} [CommRing S]

abbrev EquationQuotient (v : Fin 2 → MvPolynomial (Fin 5) S) :=
  MvPolynomial (Fin 5) S ⧸ Ideal.span (Set.range v)

def equationMinor (v : Fin 2 → MvPolynomial (Fin 5) S)
    (p : Fin 2 → Fin 5) : MvPolynomial (Fin 5) S :=
  pderiv (p 0) (v 0) * pderiv (p 1) (v 1) -
    pderiv (p 1) (v 0) * pderiv (p 0) (v 1)

/-- Coefficient specialization preserves these actual geometric
derivatives. No derivative of a moving coefficient is substituted. -/
theorem equationMinor_map {T : Type} [CommRing T] (f : S →+* T)
    (v : Fin 2 → MvPolynomial (Fin 5) S) (p : Fin 2 → Fin 5) :
    MvPolynomial.map f (equationMinor v p) =
      equationMinor (fun a => MvPolynomial.map f (v a)) p := by
  simp only [equationMinor, map_sub, map_mul, MvPolynomial.pderiv_map]

def prePresentation (v : Fin 2 → MvPolynomial (Fin 5) S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Algebra.PreSubmersivePresentation S (EquationQuotient v) (Fin 5) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive (v := v) p hp

theorem prePresentation_jacobian (v : Fin 2 → MvPolynomial (Fin 5) S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    (prePresentation v p hp).jacobian =
      Ideal.Quotient.mk (Ideal.span (Set.range v)) (equationMinor v p) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_fin_two]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change Ideal.Quotient.mk (Ideal.span (Set.range v))
      (pderiv (p 0) (v 0) * pderiv (p 1) (v 1) -
        pderiv (p 0) (v 1) * pderiv (p 1) (v 0)) = _
  apply congrArg (Ideal.Quotient.mk (Ideal.span (Set.range v)))
  dsimp only [equationMinor]
  rw [mul_comm (pderiv (p 0) (v 1)) (pderiv (p 1) (v 0))]

abbrev JacobianPatch (v : Fin 2 → MvPolynomial (Fin 5) S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :=
  Localization.Away (prePresentation v p hp).jacobian

/-- The original two-equation quotient with the chosen determinant
inverted has an explicit finite submersive presentation over S. -/
def presentation (v : Fin 2 → MvPolynomial (Fin 5) S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Algebra.SubmersivePresentation S (JacobianPatch v p hp)
      (Unit ⊕ Fin 5) (Unit ⊕ Fin 2) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway
      (JacobianPatch v p hp) (prePresentation v p hp).jacobian).comp
        (prePresentation v p hp)
  jacobian_isUnit := by
    have hu : IsUnit (algebraMap (EquationQuotient v) (JacobianPatch v p hp)
        (prePresentation v p hp).jacobian) :=
      IsLocalization.Away.algebraMap_isUnit _
    simpa only [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
      using hu.mul hu

theorem presentation_dimension (v : Fin 2 → MvPolynomial (Fin 5) S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    (presentation v p hp).dimension = 3 := by
  change Nat.card (Unit ⊕ Fin 5) - Nat.card (Unit ⊕ Fin 2) = 3
  norm_num [Nat.card_eq_fintype_card]

theorem patch_standardSmooth (v : Fin 2 → MvPolynomial (Fin 5) S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Algebra.IsStandardSmoothOfRelativeDimension 3 S (JacobianPatch v p hp) :=
  (presentation v p hp).isStandardSmoothOfRelativeDimension
    (presentation_dimension v p hp)

theorem patch_smooth (v : Fin 2 → MvPolynomial (Fin 5) S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Algebra.Smooth S (JacobianPatch v p hp) := by
  letI : Algebra.IsStandardSmooth S (JacobianPatch v p hp) :=
    (presentation v p hp).isStandardSmooth
  infer_instance

theorem patch_flat (v : Fin 2 → MvPolynomial (Fin 5) S)
    (p : Fin 2 → Fin 5) (hp : Function.Injective p) :
    Module.Flat S (JacobianPatch v p hp) := by
  letI := patch_smooth v p hp
  infer_instance

end CycleQ2RelativeJacobianPatch

namespace CycleQ2IncidenceRelativeJacobian

open MvPolynomial Matrix
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj CycleQ2IncidenceEtaleParameter
  CycleQ2EtaleIncidenceCurve CycleQ2RelativeJacobianPatch

/-- The original ordered pair (F,h), retaining the same coefficient
algebra and every geometric coordinate. -/
def equations : Fin 2 → MvPolynomial (Fin 5) ParameterAlgebra :=
  ![pointEquationF incidencePoint, pointEquationH incidencePoint]

theorem equationIdeal_eq :
    Ideal.span (Set.range equations) = pointEquations incidencePoint := by
  change Ideal.span (Set.range equations) =
    Ideal.span {pointEquationH incidencePoint, pointEquationF incidencePoint}
  apply congrArg Ideal.span
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp [equations]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl)
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩

/-- The standard-smooth presentation uses exactly the original surface
quotient; the equation ordering changes only the displayed generators. -/
def equationQuotientEquiv : EquationQuotient equations ≃ₐ[ParameterAlgebra]
    PointSurface incidencePoint :=
  Ideal.quotientEquivAlgOfEq ParameterAlgebra equationIdeal_eq

theorem equations_seed (a : Fin 2) :
    MvPolynomial.map seedMap (equations a) =
      (![smoothF (57 : ℂ) Complex.I, smoothH Complex.I] : Fin 2 → MvPolynomial (Fin 5) ℂ) a := by
  fin_cases a
  · exact seed_sextic
  · exact seed_cubic

theorem equationMinor_seed (p : Fin 2 → Fin 5) :
    MvPolynomial.map seedMap (equationMinor equations p) =
      CycleQ2SeedSurfaceGradient.surfaceMinor (p 0) (p 1) := by
  rw [equationMinor_map]
  change pderiv (p 0) (MvPolynomial.map seedMap (pointEquationF incidencePoint)) *
      pderiv (p 1) (MvPolynomial.map seedMap (pointEquationH incidencePoint)) -
    pderiv (p 1) (MvPolynomial.map seedMap (pointEquationF incidencePoint)) *
      pderiv (p 0) (MvPolynomial.map seedMap (pointEquationH incidencePoint)) = _
  simp only [seed_sextic, seed_cubic, CycleQ2SeedSurfaceGradient.surfaceMinor]

/-- Every relevant prime of the original complex seed admits one of
these actual relative standard-smooth and flat cone patches. This is
not a deduction of family smoothness solely from smoothness of a fiber. -/
theorem seed_relative_jacobian_cover (P : Ideal (MvPolynomial (Fin 5) ℂ)) [P.IsPrime]
    (hF : smoothF (57 : ℂ) Complex.I ∈ P) (hh : smoothH Complex.I ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ (p : Fin 2 → Fin 5) (hp : Function.Injective p),
      MvPolynomial.map seedMap (equationMinor equations p) ∉ P ∧
      Algebra.IsStandardSmoothOfRelativeDimension 3 ParameterAlgebra
        (JacobianPatch equations p hp) ∧
      Module.Flat ParameterAlgebra (JacobianPatch equations p hp) := by
  obtain ⟨j, k, hm⟩ := CycleQ2SeedSurfaceGradient.prime_minor_cover P hF hh hx
  have hjk : j ≠ k := by
    intro h
    subst k
    apply hm
    simp only [CycleQ2SeedSurfaceGradient.surfaceMinor, sub_self]
    exact P.zero_mem
  let p : Fin 2 → Fin 5 := ![j, k]
  have hp : Function.Injective p := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [p]
  refine ⟨p, hp, ?_, patch_standardSmooth equations p hp, patch_flat equations p hp⟩
  rw [equationMinor_seed]
  exact hm

#print axioms equationIdeal_eq
#print axioms equationMinor_seed
#print axioms seed_relative_jacobian_cover

end CycleQ2IncidenceRelativeJacobian
end
