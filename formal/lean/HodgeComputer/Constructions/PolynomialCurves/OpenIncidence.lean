import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting

/-!
Extracted from fqlx's accepted PR #150. The original declaration namespace
is retained for compatibility; the hypotheses are independent of its target.

The square incidence restricted to a nonzero distinguished coefficient.
This second localization guarantees that the lifted curve is transverse to
the endpoint section. A nonzero seed value is needed in addition to the
Jacobian condition; transversality is not inferred from rank alone.
-/

noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
namespace ReflectionCoupledFano
open HoldoutConstruction
open scoped TensorProduct

variable {R K T : Type*} [CommRing R] [Field K] [CommRing T]
variable [Algebra R K] [Algebra R T]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def squareEtaleCoordinate (eqs : ι → MvPolynomial ι R) (i : ι) :
    SquareEtaleRing eqs :=
  algebraMap (SquareSystemRing eqs) (SquareEtaleRing eqs)
    (Ideal.Quotient.mk _ (MvPolynomial.X i))

abbrev OpenSquareEtale (eqs : ι → MvPolynomial ι R) (i : ι) :=
  Localization.Away (squareEtaleCoordinate eqs i)

instance openSquareEtale_commRing (eqs : ι → MvPolynomial ι R) (i : ι) :
    CommRing (OpenSquareEtale eqs i) := inferInstance

abbrev OpenSquareGeneric (K : Type*) [Field K] [Algebra R K]
    (eqs : ι → MvPolynomial ι R) (i : ι) := K ⊗[R] OpenSquareEtale eqs i

instance openSquareGeneric_commRing (eqs : ι → MvPolynomial ι R) (i : ι) :
    CommRing (OpenSquareGeneric K eqs i) := inferInstance

def openSquareEtaleEval (eqs : ι → MvPolynomial ι R) (x : ι → T)
    (hx : ∀ j, MvPolynomial.aeval x (eqs j) = 0)
    (hj : IsUnit (Matrix.det
      (fun j k => MvPolynomial.aeval x (MvPolynomial.pderiv j (eqs k)))))
    (i : ι) (hi : IsUnit (x i)) : OpenSquareEtale eqs i →ₐ[R] T :=
  IsLocalization.Away.liftAlgHom (squareEtaleCoordinate eqs i)
    (f := squareSystemEtaleEval eqs x hx hj) (by
      simp only [squareEtaleCoordinate, squareSystemEtaleEval,
        IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq]
      simpa [squareSystemEval] using hi)



def openGenericEtaleMap (eqs : ι → MvPolynomial ι R) (i : ι)
    (I : Ideal (OpenSquareGeneric K eqs i)) :
    SquareEtaleRing eqs →ₐ[R] (OpenSquareGeneric K eqs i) ⧸ I :=
  ((Ideal.Quotient.mkₐ R I).comp Algebra.TensorProduct.includeRight).comp
    (IsScalarTower.toAlgHom R (SquareEtaleRing eqs) (OpenSquareEtale eqs i))

def openGenericMap (eqs : ι → MvPolynomial ι R) (i : ι)
    (I : Ideal (OpenSquareGeneric K eqs i)) :
    SquareSystemRing eqs →ₐ[R] (OpenSquareGeneric K eqs i) ⧸ I :=
  (openGenericEtaleMap eqs i I).comp
    (IsScalarTower.toAlgHom R (SquareSystemRing eqs) (SquareEtaleRing eqs))

def openGenericCoordinates (eqs : ι → MvPolynomial ι R) (i : ι)
    (I : Ideal (OpenSquareGeneric K eqs i)) (j : ι) :
    (OpenSquareGeneric K eqs i) ⧸ I :=
  openGenericMap eqs i I (Ideal.Quotient.mk _ (MvPolynomial.X j))

theorem openGeneric_eval (eqs : ι → MvPolynomial ι R) (i : ι)
    (I : Ideal (OpenSquareGeneric K eqs i)) (p : MvPolynomial ι R) :
    MvPolynomial.aeval (openGenericCoordinates eqs i I) p =
      openGenericMap eqs i I (Ideal.Quotient.mk _ p) := by
  have h : MvPolynomial.aeval (openGenericCoordinates eqs i I) =
      (openGenericMap eqs i I).comp (Ideal.Quotient.mkₐ R _) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [openGenericCoordinates]
  exact congrArg (fun f : MvPolynomial ι R →ₐ[R] _ => f p) h

theorem openGeneric_solution (eqs : ι → MvPolynomial ι R) (i : ι)
    (I : Ideal (OpenSquareGeneric K eqs i)) (j : ι) :
    MvPolynomial.aeval (openGenericCoordinates eqs i I) (eqs j) = 0 := by
  rw [openGeneric_eval]
  have h : Ideal.Quotient.mk (Ideal.span (Set.range eqs)) (eqs j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  rw [h, map_zero]

theorem openGeneric_jacobian (eqs : ι → MvPolynomial ι R) (i : ι)
    (I : Ideal (OpenSquareGeneric K eqs i)) :
    IsUnit (Matrix.det (fun j k => MvPolynomial.aeval
      (openGenericCoordinates eqs i I) (MvPolynomial.pderiv j (eqs k)))) := by
  have hj := IsLocalization.Away.algebraMap_isUnit
    (S := SquareEtaleRing eqs) (squareSystemJacobian eqs)
  have hm := hj.map (openGenericEtaleMap eqs i I).toRingHom
  change IsUnit (openGenericMap eqs i I (squareSystemJacobian eqs)) at hm
  have hcanon := congrArg (openGenericMap eqs i I)
    (squareSystemJacobian_eq_mk_det eqs)
  let e : MvPolynomial ι R →+* ((OpenSquareGeneric K eqs i) ⧸ I) :=
    (openGenericMap eqs i I).toRingHom.comp (Ideal.Quotient.mk _)
  have hmap := RingHom.map_det e (fun j k => MvPolynomial.pderiv j (eqs k))
  change openGenericMap eqs i I
      (Ideal.Quotient.mk _ (Matrix.det (fun j k => MvPolynomial.pderiv j (eqs k)))) =
    Matrix.det (fun j k => openGenericMap eqs i I
      (Ideal.Quotient.mk _ (MvPolynomial.pderiv j (eqs k)))) at hmap
  have he : openGenericMap eqs i I (squareSystemJacobian eqs) =
      Matrix.det (fun j k => MvPolynomial.aeval
        (openGenericCoordinates eqs i I) (MvPolynomial.pderiv j (eqs k))) := by
    rw [hcanon, hmap]
    congr 1
    funext j k
    exact (openGeneric_eval eqs i I _).symm
  exact he ▸ hm

theorem openGeneric_coordinate_unit (eqs : ι → MvPolynomial ι R) (i : ι)
    (I : Ideal (OpenSquareGeneric K eqs i)) :
    IsUnit (openGenericCoordinates eqs i I i) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := OpenSquareEtale eqs i) (squareEtaleCoordinate eqs i)
  exact h.map (((Ideal.Quotient.mkₐ R I).comp
    (Algebra.TensorProduct.includeRight : OpenSquareEtale eqs i →ₐ[R]
      OpenSquareGeneric K eqs i)).toRingHom)

theorem openSquare_exists_fieldFactor [Nontrivial T]
    (eqs : ι → MvPolynomial ι R) (x : ι → T)
    (hx : ∀ j, MvPolynomial.aeval x (eqs j) = 0)
    (hj : IsUnit (Matrix.det
      (fun j k => MvPolynomial.aeval x (MvPolynomial.pderiv j (eqs k)))))
    (i : ι) (hi : IsUnit (x i))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (OpenSquareGeneric K eqs i), I.IsMaximal ∧
      Module.Finite K ((OpenSquareGeneric K eqs i) ⧸ I) ∧
      Algebra.IsSeparable K ((OpenSquareGeneric K eqs i) ⧸ I) ∧
      (∀ j, MvPolynomial.aeval (openGenericCoordinates eqs i I) (eqs j) = 0) ∧
      IsUnit (Matrix.det (fun j k => MvPolynomial.aeval
        (openGenericCoordinates eqs i I) (MvPolynomial.pderiv j (eqs k)))) ∧
      IsUnit (openGenericCoordinates eqs i I i) := by
  letI : Nontrivial (OpenSquareEtale eqs i) :=
    (openSquareEtaleEval eqs x hx hj i hi).toRingHom.domain_nontrivial
  letI : Algebra.Etale R (SquareEtaleRing eqs) := square_system_jacobian_etale eqs
  obtain ⟨I, hI, hfin, hsep⟩ := genericEtale_exists_fieldFactor
    R K (OpenSquareEtale eqs i) hinj
  exact ⟨I, hI, hfin, hsep, openGeneric_solution eqs i I,
    openGeneric_jacobian eqs i I, openGeneric_coordinate_unit eqs i I⟩

end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.openSquare_exists_fieldFactor
