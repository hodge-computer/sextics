import Proposal.GeometricTarget02
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Flat.Basic

/-!
# Polynomial charts for the actual incidence section

The existing rank-one matrix calculation makes the ideal of the three
components of `M T` principal on every unit-entry chart.  This file proves
the stronger statement that its quotient is a polynomial algebra in the
two remaining section parameters.  No domain or reducedness hypothesis is
needed.  This is the affine algebra of the projective-line bundle of
sections vanishing at a point; it does not assert smoothness of individual
curve fibers, a divisor-class comparison, or residue exactness.
-/

set_option Elab.async false
set_option autoImplicit false

noncomputable section

namespace CycleQ2IncidenceSection

open MvPolynomial
open CycleQ2GenericLinearSection CycleQ2SegreGenericSection

variable {R : Type*} [CommRing R]

/-- The two free coordinates after eliminating the selected pivot. -/
def freeLinearForm (a : Fin 3 → R) (p : Fin 3) : MvPolynomial (Fin 2) R :=
  ∑ j, C (a (p.succAbove j)) * X j

/-- Solve the literal linear equation for the unit-coefficient variable. -/
def eliminate (a : Fin 3 → R) (p : Fin 3) (u : Rˣ) :
    MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval (Fin.insertNth p
    (-C (↑(u⁻¹) : R) * freeLinearForm a p) X)

@[simp] theorem eliminate_pivot (a : Fin 3 → R) (p : Fin 3) (u : Rˣ) :
    eliminate a p u (X p) = -C (↑(u⁻¹) : R) * freeLinearForm a p := by
  simp [eliminate]

@[simp] theorem eliminate_free (a : Fin 3 → R) (p : Fin 3) (u : Rˣ)
    (j : Fin 2) : eliminate a p u (X (p.succAbove j)) = X j := by
  simp [eliminate]

theorem eliminate_linearForm (a : Fin 3 → R) (p : Fin 3) (u : Rˣ)
    (hu : (u : R) = a p) : eliminate a p u (linearForm a) = 0 := by
  rw [linearForm, map_sum, Fin.sum_univ_succAbove _ p]
  simp only [map_mul, MvPolynomial.algHom_C, eliminate_pivot, eliminate_free]
  change C (a p) * (-C (↑(u⁻¹) : R) * freeLinearForm a p) +
    freeLinearForm a p = 0
  rw [← hu]
  have hunit : C (u : R) * C (↑(u⁻¹) : R) =
      (1 : MvPolynomial (Fin 2) R) := by
    rw [← map_mul, Units.mul_inv, map_one]
  linear_combination -(freeLinearForm a p) * hunit

abbrev LinearQuotient (a : Fin 3 → R) :=
  MvPolynomial (Fin 3) R ⧸ Ideal.span {linearForm a}

def quotientEliminate (a : Fin 3 → R) (p : Fin 3) (u : Rˣ)
    (hu : (u : R) = a p) : LinearQuotient a →ₐ[R] MvPolynomial (Fin 2) R :=
  Ideal.Quotient.liftₐ _ (eliminate a p u) (by
    intro f hf
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hf
    simp [map_mul, eliminate_linearForm a p u hu])

def quotientFree (a : Fin 3 → R) (p : Fin 3) :
    MvPolynomial (Fin 2) R →ₐ[R] LinearQuotient a :=
  aeval (fun j => Ideal.Quotient.mkₐ R (Ideal.span {linearForm a})
    (X (p.succAbove j)))

@[simp] theorem quotientEliminate_mk (a : Fin 3 → R) (p : Fin 3) (u : Rˣ)
    (hu : (u : R) = a p) (f : MvPolynomial (Fin 3) R) :
    quotientEliminate a p u hu (Ideal.Quotient.mkₐ R _ f) =
      eliminate a p u f := rfl

theorem eliminate_free_comp (a : Fin 3 → R) (p : Fin 3) (u : Rˣ)
    (hu : (u : R) = a p) :
    (quotientEliminate a p u hu).comp (quotientFree a p) =
      AlgHom.id R (MvPolynomial (Fin 2) R) := by
  apply MvPolynomial.algHom_ext
  intro j
  change quotientEliminate a p u hu (quotientFree a p (X j)) = X j
  rw [quotientFree, aeval_X, quotientEliminate_mk, eliminate_free]

theorem free_eliminate_comp (a : Fin 3 → R) (p : Fin 3) (u : Rˣ)
    (hu : (u : R) = a p) :
    (quotientFree a p).comp (quotientEliminate a p u hu) =
      AlgHom.id R (LinearQuotient a) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.succAboveCases p ?_ (fun k => ?_) j
  · simp only [AlgHom.comp_apply, quotientEliminate_mk, eliminate_pivot,
      map_mul, map_neg, MvPolynomial.algHom_C, AlgHom.id_apply]
    have hrel : Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (linearForm a) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    have hsum : linearForm a = C (a p) * X p +
        ∑ k : Fin 2, C (a (p.succAbove k)) * X (p.succAbove k) :=
      Fin.sum_univ_succAbove _ p
    have hrel' :
        Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (C (a p)) *
          Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (X p) +
        ∑ k : Fin 2,
          Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (C (a (p.succAbove k))) *
          Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (X (p.succAbove k)) = 0 := by
      calc
        _ = Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (linearForm a) := by
          symm
          simpa only [map_add, map_mul, map_sum] using
            congrArg (Ideal.Quotient.mkₐ R (Ideal.span {linearForm a})) hsum
        _ = 0 := hrel
    have hfree : quotientFree a p (freeLinearForm a p) =
        ∑ k : Fin 2,
          Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (C (a (p.succAbove k))) *
          Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (X (p.succAbove k)) := by
      simp [quotientFree, freeLinearForm]
    rw [hfree]
    have hunit :
        Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (C (↑(u⁻¹) : R)) *
        Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (C (a p)) = 1 := by
      rw [← map_mul, ← map_mul, ← hu, Units.inv_mul, map_one, map_one]
    change -(Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (C (↑(u⁻¹) : R))) *
      (∑ k : Fin 2,
        Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (C (a (p.succAbove k))) *
        Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (X (p.succAbove k))) =
          Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (X p)
    linear_combination
      -(Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (C (↑(u⁻¹) : R))) * hrel' +
      (Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (X p)) * hunit
  · change quotientFree a p
      (quotientEliminate a p u hu
        (Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (X (p.succAbove k)))) =
      Ideal.Quotient.mkₐ R (Ideal.span {linearForm a}) (X (p.succAbove k))
    rw [quotientEliminate_mk, eliminate_free, quotientFree, aeval_X]

/-- The actual quotient by a unit-coefficient linear equation is exactly
a polynomial algebra in the two remaining coordinates. -/
def linearQuotientEquiv (a : Fin 3 → R) (p : Fin 3) (u : Rˣ)
    (hu : (u : R) = a p) :
    LinearQuotient a ≃ₐ[R] MvPolynomial (Fin 2) R :=
  AlgEquiv.ofAlgHom (quotientEliminate a p u hu) (quotientFree a p)
    (eliminate_free_comp a p u hu) (free_eliminate_comp a p u hu)

/-- A unit pivot on the rank-one matrix gives a polynomial chart for the
literal three-component zero scheme, with no separately assumed line
bundle or regular-section hypothesis. -/
def sectionQuotientEquiv (M : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p : CycleQ2SegreCech.Chart) (u : Rˣ) (hu : (u : R) = M p.1 p.2) :
    (MvPolynomial (Fin 3) R ⧸ sectionIdeal M) ≃ₐ[R]
      MvPolynomial (Fin 2) R :=
  (Ideal.quotientEquivAlgOfEq R (sectionIdeal_principal M hM p u hu)).trans
    (linearQuotientEquiv (M p.1) p.2 u hu)

/-- The affine universal section chart is smooth over its surface chart.
This is the direction toward the surface, not toward the parameter space. -/
theorem sectionQuotient_smooth (M : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p : CycleQ2SegreCech.Chart) (u : Rˣ) (hu : (u : R) = M p.1 p.2) :
    Algebra.Smooth R (MvPolynomial (Fin 3) R ⧸ sectionIdeal M) := by
  let : Algebra.Smooth R (MvPolynomial (Fin 2) R) := {}
  exact Algebra.Smooth.of_equiv (sectionQuotientEquiv M hM p u hu).symm

/-- Flatness of the same universal chart over the actual coefficient ring. -/
theorem sectionQuotient_flat (M : Matrix (Fin 3) (Fin 3) R)
    (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p : CycleQ2SegreCech.Chart) (u : Rˣ) (hu : (u : R) = M p.1 p.2) :
    Module.Flat R (MvPolynomial (Fin 3) R ⧸ sectionIdeal M) := by
  exact Module.Flat.of_linearEquiv (sectionQuotientEquiv M hM p u hu).toLinearEquiv

end CycleQ2IncidenceSection

#print axioms CycleQ2IncidenceSection.eliminate_linearForm
#print axioms CycleQ2IncidenceSection.linearQuotientEquiv
#print axioms CycleQ2IncidenceSection.sectionQuotientEquiv
#print axioms CycleQ2IncidenceSection.sectionQuotient_smooth
#print axioms CycleQ2IncidenceSection.sectionQuotient_flat
