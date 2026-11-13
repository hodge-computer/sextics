import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/- Source component: JacobianEtale -/
section
/-!
Jacobian-localized square polynomial systems are étale.

This is a generic algebraic helper for the prospective holdout curve
construction. It asserts neither a curve seed nor a Hodge certificate.
Prepared with OpenAI ChatGPT assistance for contribution through fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} [Finite ι]

/-- Localizing a square presentation at its Jacobian gives a submersive
presentation of relative dimension zero. The extra variable and relation
present the inverse of the Jacobian. -/
def jacobianLocalizedPresentation (P : PreSubmersivePresentation R S ι ι) :
    SubmersivePresentation R (Localization.Away P.jacobian) (Unit ⊕ ι) (Unit ⊕ ι) where
  __ := (PreSubmersivePresentation.localizationAway
    (Localization.Away P.jacobian) P.jacobian).comp P
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away P.jacobian) P.jacobian).mul
      (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away P.jacobian) P.jacobian)

theorem jacobian_localized_etale (P : PreSubmersivePresentation R S ι ι) :
    Algebra.Etale R (Localization.Away P.jacobian) := by
  let : Algebra.IsStandardSmoothOfRelativeDimension 0 R
      (Localization.Away P.jacobian) :=
    (jacobianLocalizedPresentation P).isStandardSmoothOfRelativeDimension (by
      simp [Algebra.Presentation.dimension])
  infer_instance

/-- The quotient ring of a square polynomial system. -/
abbrev SquareSystemRing (equations : ι → MvPolynomial ι R) :=
  MvPolynomial ι R ⧸ Ideal.span (Set.range equations)

/-- The canonical square presentation of a polynomial system. -/
def squareSystemPresentation (equations : ι → MvPolynomial ι R) :
    PreSubmersivePresentation R (SquareSystemRing equations) ι ι :=
  PreSubmersivePresentation.naive (v := equations) id Function.injective_id

/-- The determinant in the quotient ring, with rows indexed by variables
and columns indexed by equations. This transpose convention has the same
determinant as the usual equation-by-variable Jacobian. -/
def squareSystemJacobian (equations : ι → MvPolynomial ι R) :
    SquareSystemRing equations :=
  (squareSystemPresentation equations).jacobian

/-- The complete square incidence localized at its Jacobian is étale over
its coefficient ring. No nontriviality hypothesis is needed for this lemma. -/
theorem square_system_jacobian_etale (equations : ι → MvPolynomial ι R) :
    Algebra.Etale R (Localization.Away (squareSystemJacobian equations)) :=
  jacobian_localized_etale (squareSystemPresentation equations)

section Evaluation

variable {T : Type*} [CommRing T] [Algebra R T]
variable [Fintype ι] [DecidableEq ι]

theorem squareSystemJacobian_eq_mk_det (equations : ι → MvPolynomial ι R) :
    squareSystemJacobian equations = Ideal.Quotient.mk _
      (Matrix.det (fun i j => MvPolynomial.pderiv i (equations j))) := by
  rw [squareSystemJacobian, PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  congr 1
  congr 1
  ext i j
  simp [squareSystemPresentation, PreSubmersivePresentation.jacobiMatrix_naive]

/-- A solution of the polynomial system induces evaluation on its quotient. -/
def squareSystemEval (equations : ι → MvPolynomial ι R) (x : ι → T)
    (hx : ∀ i, MvPolynomial.aeval x (equations i) = 0) :
    SquareSystemRing equations →ₐ[R] T :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval x) (by
    change Ideal.span (Set.range equations) ≤ RingHom.ker (MvPolynomial.aeval x)
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hx i)

theorem squareSystemEval_jacobian
    (equations : ι → MvPolynomial ι R) (x : ι → T)
    (hx : ∀ i, MvPolynomial.aeval x (equations i) = 0) :
    squareSystemEval equations x hx (squareSystemJacobian equations) =
      Matrix.det (fun i j => MvPolynomial.aeval x (MvPolynomial.pderiv i (equations j))) := by
  rw [squareSystemJacobian_eq_mk_det]
  change MvPolynomial.aeval x _ = _
  exact AlgHom.map_det _ _

/-- A solution with invertible evaluated Jacobian induces a map from the
Jacobian-localized incidence algebra. -/
def squareSystemEtaleEval
    (equations : ι → MvPolynomial ι R) (x : ι → T)
    (hx : ∀ i, MvPolynomial.aeval x (equations i) = 0)
    (hj : IsUnit (Matrix.det
      (fun i j => MvPolynomial.aeval x (MvPolynomial.pderiv i (equations j))))) :
    Localization.Away (squareSystemJacobian equations) →ₐ[R] T :=
  IsLocalization.Away.liftAlgHom (squareSystemJacobian equations)
    (f := squareSystemEval equations x hx)
    (by rwa [squareSystemEval_jacobian])

/-- A nonsingular solution in a nontrivial algebra proves that the localized
incidence algebra is nontrivial. -/
theorem square_system_jacobian_nontrivial [Nontrivial T]
    (equations : ι → MvPolynomial ι R) (x : ι → T)
    (hx : ∀ i, MvPolynomial.aeval x (equations i) = 0)
    (hj : IsUnit (Matrix.det
      (fun i j => MvPolynomial.aeval x (MvPolynomial.pderiv i (equations j))))) :
    Nontrivial (Localization.Away (squareSystemJacobian equations)) :=
  (squareSystemEtaleEval equations x hx hj).toRingHom.domain_nontrivial

end Evaluation

end HoldoutConstruction

#print axioms HoldoutConstruction.jacobian_localized_etale
#print axioms HoldoutConstruction.square_system_jacobian_etale
#print axioms HoldoutConstruction.squareSystemEtaleEval
#print axioms HoldoutConstruction.square_system_jacobian_nontrivial
end
end

/- Source component: GenericEtaleField -/
section
/-!
The generic-fiber step for a prospective rational-curve construction for holdout.

A nonzero étale algebra over a domain stays nonzero on passage to its fraction
field. Its generic fiber is finite and has a finite separable field quotient.
The statements below also apply to an étale incidence algebra after restricting
it to the hypersurface, provided that restricted algebra has been shown nonzero.

This file does not assert the existence of the incidence algebra, a curve family,
or a Hodge certificate. Prepared with OpenAI ChatGPT assistance for a contribution
through GitHub account fqlx.
-/

noncomputable section

namespace HoldoutConstruction

open scoped TensorProduct

variable (R K S : Type*) [CommRing R] [Field K] [CommRing S]
variable [Algebra R K] [Algebra R S] [Algebra.Etale R S]

/-- Flatness prevents a nonzero étale algebra from disappearing at an injective
field-valued generic point. This is where a nonzero seed fiber is used. -/
theorem genericEtale_nontrivial [Nontrivial S]
    (injective : Function.Injective (algebraMap R K)) :
    Nontrivial (K ⊗[R] S) := by
  exact Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right
    R K S injective

/-- An étale algebra over a field is a finite-dimensional vector space. No
choice of a particular irreducible component is needed for this assertion. -/
theorem genericEtale_finite : Module.Finite K (K ⊗[R] S) := by
  exact Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)

/-- The generic fiber has a maximal ideal with a finite separable field
quotient. The field structure is `Ideal.Quotient.field I` after installing
the returned `I.IsMaximal` proof as a local instance. -/
theorem genericEtale_exists_fieldFactor [Nontrivial S]
    (injective : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (K ⊗[R] S), I.IsMaximal ∧
      Module.Finite K ((K ⊗[R] S) ⧸ I) ∧
      Algebra.IsSeparable K ((K ⊗[R] S) ⧸ I) := by
  let := genericEtale_nontrivial R K S injective
  let := genericEtale_finite R K S
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (K ⊗[R] S)
  let := hI
  exact ⟨I, hI, inferInstance, inferInstance⟩

end HoldoutConstruction

#print axioms HoldoutConstruction.genericEtale_nontrivial
#print axioms HoldoutConstruction.genericEtale_finite
#print axioms HoldoutConstruction.genericEtale_exists_fieldFactor
end
end

/- Source component: SquareGenericPoint -/
section
/-!
Canonical coordinates in a finite field factor of a square incidence.
The nonsingular seed is used only to establish nontriviality of the
coordinate-ring incidence before passage to a generic coefficient field.
-/

noncomputable section

namespace HoldoutConstruction

open scoped TensorProduct

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev SquareEtaleRing (equations : ι → MvPolynomial ι R) :=
  Localization.Away (squareSystemJacobian equations)

abbrev SquareGenericAlgebra (K : Type*) [Field K] [Algebra R K]
    (equations : ι → MvPolynomial ι R) := K ⊗[R] SquareEtaleRing equations

def squareGenericEtaleMap (equations : ι → MvPolynomial ι R)
    (I : Ideal (SquareGenericAlgebra K equations)) :
    SquareEtaleRing equations →ₐ[R] (SquareGenericAlgebra K equations) ⧸ I :=
  (Ideal.Quotient.mkₐ R I).comp Algebra.TensorProduct.includeRight

def squareGenericMap (equations : ι → MvPolynomial ι R)
    (I : Ideal (SquareGenericAlgebra K equations)) :
    SquareSystemRing equations →ₐ[R] (SquareGenericAlgebra K equations) ⧸ I :=
  (squareGenericEtaleMap equations I).comp
    (IsScalarTower.toAlgHom R (SquareSystemRing equations) (SquareEtaleRing equations))

def squareGenericCoordinates (equations : ι → MvPolynomial ι R)
    (I : Ideal (SquareGenericAlgebra K equations)) (i : ι) :
    (SquareGenericAlgebra K equations) ⧸ I :=
  squareGenericMap equations I (Ideal.Quotient.mk _ (MvPolynomial.X i))

omit [DecidableEq ι] in
theorem squareGeneric_eval (equations : ι → MvPolynomial ι R)
    (I : Ideal (SquareGenericAlgebra K equations)) (p : MvPolynomial ι R) :
    MvPolynomial.aeval (squareGenericCoordinates equations I) p =
      squareGenericMap equations I (Ideal.Quotient.mk _ p) := by
  have h : MvPolynomial.aeval (squareGenericCoordinates equations I) =
      (squareGenericMap equations I).comp (Ideal.Quotient.mkₐ R _) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [squareGenericCoordinates]
  exact congrArg (fun f : MvPolynomial ι R →ₐ[R] _ => f p) h

omit [DecidableEq ι] in
theorem squareGeneric_solution (equations : ι → MvPolynomial ι R)
    (I : Ideal (SquareGenericAlgebra K equations)) (i : ι) :
    MvPolynomial.aeval (squareGenericCoordinates equations I) (equations i) = 0 := by
  rw [squareGeneric_eval]
  have h : Ideal.Quotient.mk (Ideal.span (Set.range equations)) (equations i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  rw [h, map_zero]

theorem squareGeneric_jacobian (equations : ι → MvPolynomial ι R)
    (I : Ideal (SquareGenericAlgebra K equations)) :
    IsUnit (Matrix.det (fun i j => MvPolynomial.aeval
      (squareGenericCoordinates equations I) (MvPolynomial.pderiv i (equations j)))) := by
  have hj := IsLocalization.Away.algebraMap_isUnit
    (S := SquareEtaleRing equations) (squareSystemJacobian equations)
  have hm := hj.map (squareGenericEtaleMap equations I).toRingHom
  change IsUnit (squareGenericMap equations I (squareSystemJacobian equations)) at hm
  have hcanon := congrArg (squareGenericMap equations I)
    (squareSystemJacobian_eq_mk_det equations)
  let e : MvPolynomial ι R →+* ((SquareGenericAlgebra K equations) ⧸ I) :=
    (squareGenericMap equations I).toRingHom.comp (Ideal.Quotient.mk _)
  let M : Matrix ι ι (MvPolynomial ι R) := fun i j => MvPolynomial.pderiv i (equations j)
  have hmap : e M.det = (e.mapMatrix M).det :=
    RingHom.map_det (R := MvPolynomial ι R)
      (S := (SquareGenericAlgebra K equations) ⧸ I) e M
  change squareGenericMap equations I
      (Ideal.Quotient.mk _ (Matrix.det (fun i j => MvPolynomial.pderiv i (equations j)))) =
    Matrix.det (fun i j => squareGenericMap equations I
      (Ideal.Quotient.mk _ (MvPolynomial.pderiv i (equations j)))) at hmap
  have he : squareGenericMap equations I (squareSystemJacobian equations) =
      Matrix.det (fun i j => MvPolynomial.aeval
        (squareGenericCoordinates equations I) (MvPolynomial.pderiv i (equations j))) := by
    rw [hcanon, hmap]
    congr 1
    funext i j
    exact (squareGeneric_eval equations I _).symm
  exact he ▸ hm

theorem squareGeneric_exists_fieldFactor
    (equations : ι → MvPolynomial ι R) [Nontrivial (SquareEtaleRing equations)]
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (SquareGenericAlgebra K equations), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K equations) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K equations) ⧸ I) ∧
      (∀ i, MvPolynomial.aeval (squareGenericCoordinates equations I) (equations i) = 0) ∧
      IsUnit (Matrix.det (fun i j => MvPolynomial.aeval
        (squareGenericCoordinates equations I) (MvPolynomial.pderiv i (equations j)))) := by
  let : Algebra.Etale R (SquareEtaleRing equations) := square_system_jacobian_etale equations
  obtain ⟨I, hI, hfin, hsep⟩ := genericEtale_exists_fieldFactor
    R K (SquareEtaleRing equations) hinj
  exact ⟨I, hI, hfin, hsep, squareGeneric_solution equations I,
    squareGeneric_jacobian equations I⟩

end HoldoutConstruction

#print axioms HoldoutConstruction.squareGeneric_solution
#print axioms HoldoutConstruction.squareGeneric_jacobian
#print axioms HoldoutConstruction.squareGeneric_exists_fieldFactor
end
end
