import Proposal.GeometricTarget03Part01

/-! Continuation of GeometricTarget03.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: continuation_3/CurveRestrictionReflection.lean -/
section
/-! Soundness of the finite polynomial and coefficient checks used by the
curve restriction minors. All executable checks use natural numbers and lists. -/

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestrictionReflection

open MvPolynomial CycleQ2CurveRestriction CycleQ2SparseModularPolynomial

abbrev CurveTuple := ℕ × ℕ × ℕ × ℕ

def curveTuple (e : Exponent) : CurveTuple := (e.1,e.2.1,e.2.2.1,e.2.2.2.1)

def coefficient (e : CurveTuple) : Sparse → ℕ
  | [] => 0
  | a::p => ((if curveTuple a.1=e then a.2 else 0)+coefficient e p)%109

def goodTerm (s : Side) (d : ℕ) (a : Term) : Bool :=
  decide (a.1.1<xBound s ∧ a.1.2.2.1<zBound s ∧
    a.1.1+a.1.2.1+a.1.2.2.1+a.1.2.2.2.1=d)

def goodPolynomial (s : Side) (d : ℕ) (p : Sparse) : Bool := p.all (goodTerm s d)

def residual (p n a b q h : Sparse) : Sparse :=
  add p (neg (add n (add (mul a q) (mul b h))))

noncomputable section
variable {R : Type*} [CommRing R]

def tupleExponent (e : CurveTuple) : CurveExponent :=
  exponent ![e.1,e.2.1,e.2.2.1,e.2.2.2]

def sourceTupleExponent (e : Exponent) : CycleQ2IncidenceNormalForm.FullExponent :=
  Finsupp.equivFunOnFinite.symm ![e.1,e.2.1,e.2.2.1,e.2.2.2.1,e.2.2.2.2]

def sourceMonomial (e : Exponent) : MvPolynomial (Fin 5) R :=
  X 0^e.1*X 1^e.2.1*X 2^e.2.2.1*X 3^e.2.2.2.1*X 4^e.2.2.2.2

theorem sourceMonomial_eq_monomial (e : Exponent) :
    (sourceMonomial e : MvPolynomial (Fin 5) R) = MvPolynomial.monomial (sourceTupleExponent e) 1 := by
  simp only [sourceMonomial, X_pow_eq_monomial, monomial_mul, one_mul]
  apply congrArg (fun f : Fin 5 →₀ ℕ => MvPolynomial.monomial f (1 : R))
  ext i
  fin_cases i <;> simp [sourceTupleExponent,Finsupp.single_apply,Fin.ext_iff]

@[simp] theorem map_sourceMonomial {S : Type*} [CommRing S] (φ : R →+* S) (e : Exponent) :
    MvPolynomial.map φ (sourceMonomial e) = sourceMonomial e := by
  simp [sourceMonomial]

def curveVariables : Fin 5 → CurvePoly R := ![X 0,X 1,X 2,X 3,1]

def value [CharP R 109] (p : Sparse) : CurvePoly R := eval curveVariables p

@[simp] theorem value_nil [CharP R 109] : value (R:=R) []=0 := rfl

@[simp] theorem value_cons [CharP R 109] (a : Term) (p : Sparse) :
    value (R:=R) (a::p)=termValue curveVariables a+value p := rfl

theorem tupleExponent_injective : Function.Injective tupleExponent := by
  intro e f h
  have h0 := congrArg (fun q : CurveExponent => q 0) h
  have h1 := congrArg (fun q : CurveExponent => q 1) h
  have h2 := congrArg (fun q : CurveExponent => q 2) h
  have h3 := congrArg (fun q : CurveExponent => q 3) h
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))

theorem monomial_curveVariables [CharP R 109] (e : Exponent) :
    CycleQ2SparseModularPolynomial.monomial (curveVariables (R:=R)) e =
      MvPolynomial.monomial (tupleExponent (curveTuple e)) 1 := by
  change (X 0^e.1*X 1^e.2.1*X 2^e.2.2.1*X 3^e.2.2.2.1*(1 : CurvePoly R)^e.2.2.2.2)=_
  rw [one_pow,mul_one]
  exact mon_eq_monomial _ _ _ _

theorem termValue_curveVariables [CharP R 109] (a : Term) :
    termValue (curveVariables (R:=R)) a =
      MvPolynomial.monomial (tupleExponent (curveTuple a.1)) (a.2:R) := by
  rw [termValue,monomial_curveVariables]
  rw [←map_natCast (C : R →+* CurvePoly R) a.2,C_mul_monomial,mul_one]

theorem value_coefficient [CharP R 109] (e : CurveTuple) (p : Sparse) :
    (value (R:=R) p).coeff (tupleExponent e)=(coefficient e p:R) := by
  induction p with
  | nil => simp [coefficient]
  | cons a p ih =>
    rw [value_cons,coeff_add,termValue_curveVariables,coeff_monomial,ih]
    by_cases he : curveTuple a.1=e
    · simp [coefficient,he,←CharP.cast_eq_mod R 109,Nat.cast_add]
    · have he' : tupleExponent (curveTuple a.1)≠tupleExponent e :=
        fun h => he (tupleExponent_injective h)
      simp only [coefficient,if_neg he,if_neg he',←CharP.cast_eq_mod R 109,Nat.cast_add,Nat.cast_zero]

theorem goodTerm_value [CharP R 109] (s : Side) (d : ℕ) (a : Term)
    (ha : goodTerm s d a=true) :
    Standard s (termValue (curveVariables (R:=R)) a) ∧
      (termValue (curveVariables (R:=R)) a).IsHomogeneous d := by
  have h : a.1.1<xBound s ∧ a.1.2.2.1<zBound s ∧
      a.1.1+a.1.2.1+a.1.2.2.1+a.1.2.2.2.1=d := of_decide_eq_true ha
  rw [termValue_curveVariables]
  constructor
  · intro e he
    have heq : e=tupleExponent (curveTuple a.1) :=
      Finset.mem_singleton.mp (support_monomial_subset he)
    subst e
    exact ⟨h.1,h.2.1⟩
  · apply isHomogeneous_monomial
    simpa [tupleExponent,curveTuple,Finsupp.degree_eq_sum,Fin.sum_univ_succ,
      Matrix.cons_val_succ,Fin.reduceSucc,add_assoc] using h.2.2

theorem goodPolynomial_value [CharP R 109] (s : Side) (d : ℕ) (p : Sparse)
    (hp : goodPolynomial s d p=true) :
    Standard s (value (R:=R) p) ∧ (value (R:=R) p).IsHomogeneous d := by
  induction p with
  | nil => exact ⟨by simp [Standard],(homogeneousSubmodule (Fin 4) R d).zero_mem⟩
  | cons a p ih =>
    simp only [goodPolynomial,List.all_cons,Bool.and_eq_true] at hp
    have ha := goodTerm_value (R:=R) s d a hp.1
    have hb := ih hp.2
    rw [value_cons]
    exact ⟨standard_add ha.1 hb.1,ha.2.add hb.2⟩

theorem checked_normal [CharP R 109] [Nontrivial R]
    (s : Side) (r ι : R) (d : ℕ) (p n a b q h : Sparse)
    (hq : value (R:=R) q=quadric s r) (hh : value (R:=R) h=cubic s r ι)
    (hn : goodPolynomial s d n=true) (hc : checkZero (residual p n a b q h)=true) :
    normal s r ι (value p)=value n := by
  have hz := eval_eq_zero_of_check (curveVariables (R:=R)) _ hc
  simp only [residual,CycleQ2SparseModularPolynomial.eval_add,
    CycleQ2SparseModularPolynomial.eval_neg,CycleQ2SparseModularPolynomial.eval_mul] at hz
  change value p+ -(value n+(value a*value q+value b*value h))=0 at hz
  rw [hq,hh] at hz
  symm
  apply normal_unique
  · exact (goodPolynomial_value s d n hn).1
  · refine ⟨value a,value b,?_⟩
    linear_combination hz

def matrixCoefficient [Nontrivial R] (s : Side) (r ι : R)
    (row : CurveTuple) (column : Exponent) : R :=
  (restrictionNormal s r ι (sourceMonomial column)).coeff (tupleExponent row)

theorem matrixCoefficient_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (row : CurveTuple) (column : Exponent) :
    φ (matrixCoefficient s r ι row column)=matrixCoefficient s (φ r) (φ ι) row column := by
  unfold matrixCoefficient
  rw [←coeff_map,restrictionNormal_map,map_sourceMonomial]

end
end CycleQ2CurveRestrictionReflection

#print axioms CycleQ2CurveRestrictionReflection.checked_normal
#print axioms CycleQ2CurveRestrictionReflection.value_coefficient
#print axioms CycleQ2CurveRestrictionReflection.matrixCoefficient_map
end


/- Component: continuation_3/IncidenceJacobian.lean -/
section
/-! # The actual first-order coefficient equations

The normal-form derivative includes both moving equations.  The formula below
is proved by an equality of the actual incidence equations over every ring with
a square-zero element; it is not an assumed identification of a numerical matrix.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceJacobian

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder

variable {R : Type*} [CommRing R]

theorem fullStandard_add {p q : Poly R} (hp : FullStandard p) (hq : FullStandard q) :
    FullStandard (p + q) := by
  intro e he
  rcases Finset.mem_union.mp (support_add he) with h | h
  · exact hp e h
  · exact hq e h

theorem fullStandard_C_mul {p : Poly R} (hp : FullStandard p) (c : R) :
    FullStandard (C c * p) := by
  intro e he
  apply hp e
  apply mem_support_iff.mpr
  intro hz
  exact (mem_support_iff.mp he) (by rw [coeff_C_mul, hz, mul_zero])

theorem fullRemainder_add [Nontrivial R]
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex))
    (p q : Poly R) :
    fullRemainder hc Fc hu Fu (p + q) =
      fullRemainder hc Fc hu Fu p + fullRemainder hc Fc hu Fu q := by
  obtain ⟨hp, a, b, hab⟩ := fullRemainder_spec hc Fc hu Fu p
  obtain ⟨hq, c, d, hcd⟩ := fullRemainder_spec hc Fc hu Fu q
  symm
  apply (existsUnique_full_invariant_representative hc Fc hu Fu (p + q)).choose_spec.2
  refine ⟨fullStandard_add hp hq, a + c, b + d, ?_⟩
  linear_combination hab + hcd

theorem fullRemainder_C_mul [Nontrivial R]
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex))
    (c : R) (p : Poly R) :
    fullRemainder hc Fc hu Fu (C c * p) = C c * fullRemainder hc Fc hu Fu p := by
  obtain ⟨hp, a, b, hab⟩ := fullRemainder_spec hc Fc hu Fu p
  symm
  apply (existsUnique_full_invariant_representative hc Fc hu Fu (C c * p)).choose_spec.2
  refine ⟨fullStandard_C_mul hp c, C c * a, C c * b, ?_⟩
  linear_combination C c * hab

def fullRemainderLinear [Nontrivial R]
    (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
    (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex)) :
    Poly R →ₗ[R] Poly R where
  toFun := fullRemainder hc Fc hu Fu
  map_add' := fullRemainder_add hc Fc hu Fu
  map_smul' := fun c p ↦ by
    simpa only [smul_eq_C_mul, RingHom.id_apply] using fullRemainder_C_mul hc Fc hu Fu c p

def fullFirstOrderResidual (r ι : R) (H J : Poly R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R)) : Matrix (Fin 3) (Fin 3) (Poly R) :=
  fun i j ↦ firstOrderResidual r ι H N i j - J * rawCofactorQuotient r i j

theorem full_cofactor_seed_deformation (r ι : R) (H J t : Poly R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    CycleQ2SegreLocal.cofactors (fun i j ↦ rawSeedMatrix r i j + t * N i j) i j =
      -(smoothK ι * rawCofactorQuotient r i j) * (smoothH ι + t * H) +
        rawCofactorQuotient r i j * (smoothF r ι + t * J) +
        t * fullFirstOrderResidual r ι H J N i j +
        t ^ 2 * CycleQ2SegreLocal.cofactors N i j := by
  rw [cofactor_seed_deformation r ι H t N i j]
  unfold fullFirstOrderResidual
  ring

def deformedSexticCoefficients (r ι t : R) (ζ : FullInvariantIndex 6 → R) :
    FullInvariantIndex 6 → R := fun e ↦ seedSexticCoefficients r ι e + t * ζ e

theorem deformedSexticCoefficients_polynomial (r ι t : R) (ζ : FullInvariantIndex 6 → R) :
    fullInvariantPolynomial 6 (deformedSexticCoefficients r ι t ζ) =
      smoothF r ι + C t * fullInvariantPolynomial 6 ζ := by
  rw [← seedSexticCoefficients_polynomial]
  simp [fullInvariantPolynomial, deformedSexticCoefficients, map_add,
    Finset.sum_add_distrib, Finset.mul_sum, C_mul_monomial]

theorem deformedSexticCoefficients_unit (r ι t : R) (ζ : FullInvariantIndex 6 → R)
    (ht : t ^ 2 = 0) : IsUnit (deformedSexticCoefficients r ι t ζ fullSexticLeadingIndex) := by
  simp only [deformedSexticCoefficients, seedSexticCoefficients,
    fullSexticLeadingIndex_exponent, smoothF_leading_coefficient]
  apply IsUnit.of_mul_eq_one (1 - t * ζ fullSexticLeadingIndex)
  calc
    (1 + t * ζ fullSexticLeadingIndex) * (1 - t * ζ fullSexticLeadingIndex) =
        1 - t ^ 2 * (ζ fullSexticLeadingIndex) ^ 2 := by ring
    _ = 1 := by rw [ht]; ring

/-- The full first-order remainder, proved by the uniqueness of the concrete
normal form over the deformed leading-unit chart. -/
theorem infinitesimal_remainder_eq [Nontrivial R]
    (r ι t : R) (ht : t ^ 2 = 0)
    (η : FullInvariantIndex 3 → R) (ζ : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (i j : Fin 3) :
    fullRemainder (deformedCubicCoefficients ι t η) (deformedSexticCoefficients r ι t ζ)
      (deformedCubicCoefficients_unit ι t η ht) (deformedSexticCoefficients_unit r ι t ζ ht)
      (CycleQ2SegreLocal.cofactors (incidenceMatrix r (fun i j e ↦ t * δ i j e)) i j) =
        C t * fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
          (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
          (fullFirstOrderResidual r ι (fullInvariantPolynomial 3 η)
            (fullInvariantPolynomial 6 ζ) (perturbation δ) i j) := by
  obtain ⟨hstd, a, b, hab⟩ := fullRemainder_spec (seedCubicCoefficients ι)
    (seedSexticCoefficients r ι) (seedCubicCoefficients_unit ι)
    (seedSexticCoefficients_unit r ι)
    (fullFirstOrderResidual r ι (fullInvariantPolynomial 3 η)
      (fullInvariantPolynomial 6 ζ) (perturbation δ) i j)
  rw [seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial] at hab
  symm
  apply (existsUnique_full_invariant_representative
    (deformedCubicCoefficients ι t η) (deformedSexticCoefficients r ι t ζ)
    (deformedCubicCoefficients_unit ι t η ht) (deformedSexticCoefficients_unit r ι t ζ ht)
    (CycleQ2SegreLocal.cofactors (incidenceMatrix r (fun i j e ↦ t * δ i j e)) i j)).choose_spec.2
  refine ⟨fullStandard_C_mul hstd t,
    -(smoothK ι * rawCofactorQuotient r i j) + C t * a,
    rawCofactorQuotient r i j + C t * b, ?_⟩
  rw [deformedCubicCoefficients_polynomial, deformedSexticCoefficients_polynomial,
    incidenceMatrix_scaled, full_cofactor_seed_deformation r ι (fullInvariantPolynomial 3 η)
      (fullInvariantPolynomial 6 ζ) (C t) (perturbation δ) i j]
  have ht' : (C t : Poly R) ^ 2 = 0 := by rw [← map_pow, ht, map_zero]
  linear_combination C t * hab +
    (CycleQ2SegreLocal.cofactors (perturbation δ) i j -
      a * fullInvariantPolynomial 3 η - b * fullInvariantPolynomial 6 ζ) * ht'

def linearizedEquations [Nontrivial R] (r ι : R)
    (η : FullInvariantIndex 3 → R) (ζ : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (q : EquationIndex) : R :=
  (fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
    (fullFirstOrderResidual r ι (fullInvariantPolynomial 3 η)
      (fullInvariantPolynomial 6 ζ) (perturbation δ) q.1.1 q.1.2)).coeff (standardExponent q.2)

/-- Exact first-jet identity for each of the actual 9522 coefficient equations. -/
theorem infinitesimal_incidenceEquations_eq [Nontrivial R]
    (r ι t : R) (ht : t ^ 2 = 0)
    (η : FullInvariantIndex 3 → R) (ζ : FullInvariantIndex 6 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (q : EquationIndex) :
    incidenceEquations (deformedCubicCoefficients ι t η) (deformedSexticCoefficients r ι t ζ)
      (deformedCubicCoefficients_unit ι t η ht) (deformedSexticCoefficients_unit r ι t ζ ht)
      r (fun i j e ↦ t * δ i j e) q = t * linearizedEquations r ι η ζ δ q := by
  unfold incidenceEquations cofactorEquations linearizedEquations
  rw [infinitesimal_remainder_eq r ι t ht η ζ δ q.1.1 q.1.2, coeff_C_mul]

end CycleQ2IncidenceJacobian

#print axioms CycleQ2IncidenceJacobian.fullRemainderLinear
#print axioms CycleQ2IncidenceJacobian.infinitesimal_incidenceEquations_eq
end
end


/- Component: continuation_3/IncidencePolynomialPresentation.lean -/
section
/-!
# Genuine polynomial representatives of the actual incidence equations

Localization supplies an ordinary polynomial numerator for each of the
9522 universal remainder equations.  On the actual principal open, their
vanishing is exactly equivalent to incidence.  Differentiating the proved
denominator identity gives the expected nonzero row scaling at every seed
solution, rather than assuming that the localized remainders are globally
polynomial in unconstrained inverse variables.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CycleQ2IncidencePolynomialPresentation

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart

variable (R : Type*) [CommRing R] [IsDomain R]

def numerator (r : R) (q : EquationIndex) : ParameterPolynomial R :=
  (IsLocalization.Away.sec (leadingProduct R) (equations R r q)).1

def denominatorExponent (r : R) (q : EquationIndex) : ℕ :=
  (IsLocalization.Away.sec (leadingProduct R) (equations R r q)).2

theorem denominator_identity (r : R) (q : EquationIndex) :
    equations R r q * algebraMap (ParameterPolynomial R) (ParameterRing R)
      (leadingProduct R ^ denominatorExponent R r q) =
        algebraMap (ParameterPolynomial R) (ParameterRing R) (numerator R r q) :=
  IsLocalization.Away.sec_spec (leadingProduct R) (equations R r q)

theorem denominator_isUnit (r : R) (q : EquationIndex) :
    IsUnit (algebraMap (ParameterPolynomial R) (ParameterRing R)
      (leadingProduct R ^ denominatorExponent R r q)) := by
  rw [map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit (S := ParameterRing R) (leadingProduct R)).pow _

section Specialization

variable {R} {S : Type*} [CommRing S] [Nontrivial S] [Algebra R S]

theorem numerator_specialization
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) (q : EquationIndex) :
    polynomialSpecialization hcoeff Fcoeff δ (numerator R r q) =
      incidenceEquations hcoeff Fcoeff hu Fu (algebraMap R S r) δ q *
        (hcoeff fullCubicLeadingIndex * Fcoeff fullSexticLeadingIndex) ^
          denominatorExponent R r q := by
  have hm := congrArg (specialization hcoeff Fcoeff hu Fu δ) (denominator_identity R r q)
  rw [map_mul, specialization_equations, specialization_polynomial,
    specialization_polynomial, map_pow, polynomialSpecialization_leadingProduct] at hm
  exact hm.symm

theorem numerator_zero_iff
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) (q : EquationIndex) :
    polynomialSpecialization hcoeff Fcoeff δ (numerator R r q) = 0 ↔
      incidenceEquations hcoeff Fcoeff hu Fu (algebraMap R S r) δ q = 0 := by
  rw [numerator_specialization hcoeff Fcoeff hu Fu δ r q]
  have hd := (hu.mul Fu).pow (denominatorExponent R r q)
  exact hd.mul_left_eq_zero

/-- The chosen ordinary polynomial system has exactly the actual incidence
solutions on the two-leading-coefficient open. -/
theorem polynomial_system_zero_iff
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) :
    (∀ q, polynomialSpecialization hcoeff Fcoeff δ (numerator R r q) = 0) ↔
      ∀ i j, CycleQ2SegreLocal.cofactors (incidenceMatrix (algebraMap R S r) δ) i j ∈
        equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) := by
  rw [← incidenceEquations_zero_iff hcoeff Fcoeff hu Fu (algebraMap R S r) δ]
  exact forall_congr' (fun q => numerator_zero_iff hcoeff Fcoeff hu Fu δ r q)

end Specialization

theorem polynomial_seed_zero (r ι : R) (q : EquationIndex) :
    polynomialSpecialization (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (fun _ _ _ => 0) (numerator R r q) = 0 := by
  apply (numerator_zero_iff (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
    (fun _ _ _ => 0) r q).mpr
  simpa using smoothSeed_equations_zero r ι q

section Derivative

variable {S : Type*} [CommRing S] [Algebra (ParameterRing R) S]

/-- At an actual incidence solution, numerator differentiation differs from
the intrinsic localized equation only by its invertible denominator factor.
This applies simultaneously to every coordinate derivation of the parameter
space and justifies transferring a Jacobian minor to polynomial equations. -/
theorem numerator_differential_at_solution (r : R) (q : EquationIndex)
    (D : Derivation ℤ (ParameterRing R) S)
    (hzero : algebraMap (ParameterRing R) S (equations R r q) = 0) :
    D (algebraMap (ParameterPolynomial R) (ParameterRing R) (numerator R r q)) =
      algebraMap (ParameterRing R) S
        (algebraMap (ParameterPolynomial R) (ParameterRing R)
          (leadingProduct R ^ denominatorExponent R r q)) * D (equations R r q) := by
  rw [← denominator_identity, Derivation.leibniz]
  simp only [Algebra.smul_def, hzero, zero_mul, zero_add]

end Derivative

end CycleQ2IncidencePolynomialPresentation

#print axioms CycleQ2IncidencePolynomialPresentation.polynomial_system_zero_iff
#print axioms CycleQ2IncidencePolynomialPresentation.polynomial_seed_zero
#print axioms CycleQ2IncidencePolynomialPresentation.numerator_differential_at_solution
end
end


/- Component: continuation_3/cylinder_bridge/PointedCompatibleAffineLifting.lean -/
section
/-! A compatible affine incidence slice has a finite generic point on a
component through the actual nonsingular seed.  The extra conclusion is
an implication for the original parameter polynomials, obtained from the
proved containment of prime ideals in the Jacobian-localized algebra. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PointedCompatibleAffineLifting
open MvPolynomial Matrix HoldoutConstruction
  CycleQ2PolynomialAffineSlice CycleQ2CompatibleEquationCoordinates
  CycleQ2SlicedCompatibleSystem CycleQ2CompatibleAffineGenericLifting

variable {R S T K m l ι κ σ : Type*}
  [CommRing R] [CommRing S] [Algebra R S]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ] [Fintype σ]
  [DecidableEq m] [DecidableEq ι] [DecidableEq κ]

theorem affine_lift_semantics
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R)
    (hdecomp : Q*P+V*W=1) (hrelations : D*ᵥe=0)
    (x : ι → S) (hP : ∀q, aeval x (equations a B P e q)=0)
    (hopen : IsUnit (aeval x (substitute a B c*(relationA a B T₀ D V).det))) :
    (∀q, aeval (pointValue (algebraMap R S) a B x) (e q)=0) ∧
      IsUnit (aeval (pointValue (algebraMap R S) a B x) c) := by
  let φ : MvPolynomial ι R →+* S := (aeval x).toRingHom
  have hprod : IsUnit (aeval x (substitute a B c)*aeval x (relationA a B T₀ D V).det) :=
    (congrArg IsUnit ((aeval x).map_mul _ _)).mp hopen
  have heq : φ ∘ equations a B P e=0 := funext hP
  have hres := CycleQ2SegreRelations.evaluated_residual_eq_zero φ
    (relationA a B T₀ D V) (relationC a B T₀ D Q)
    (residual a B W e) (equations a B P e)
    (relation_identity a B P Q V W T₀ D hdecomp e hrelations) heq
    (isUnit_of_mul_isUnit_right hprod)
  refine ⟨evaluated_equations_zero (algebraMap R S) a B P Q V W hdecomp e x hP
    (fun q => congrFun hres q),?_⟩
  exact (congrArg IsUnit (eval_substitute (algebraMap R S) a B x c)).mp
    (isUnit_of_mul_isUnit_left hprod)

variable [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [Field T] [Algebra R T]

theorem pointed_lift_all_on_compatible_affine_slice
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R)
    (hdecomp : Q*P+V*W=1)
    (hrelations : D*ᵥe=0)
    (hseed : ∀q,eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) (e q)=0)
    (hjac : P.map (algebraMap R T)*
      jacobian (algebraMap R T) ((algebraMap R T) ∘ a) e*B.map (algebraMap R T)=1)
    (hcomplement : T₀.map (algebraMap R T)*
      D.map (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a))*V.map (algebraMap R T)=1)
    (hc : IsUnit (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) c)) :
    ∃ I : Ideal (GenericAlgebra K a B P T₀ D V e c), I.IsMaximal ∧
      Module.Finite K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      Algebra.IsSeparable K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      ∃ x : ι → ((GenericAlgebra K a B P T₀ D V e c) ⧸ I),
        (∀q,aeval (pointValue (algebraMap R _) a B x) (e q)=0) ∧
        IsUnit (aeval (pointValue (algebraMap R _) a B x) c) ∧
        (∀p : MvPolynomial σ R,
          aeval (pointValue (algebraMap R _) a B x) p=0 →
            eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) p=0) := by
  have hseed' (q : ι) : aeval (0 : ι → T) (equations a B P e q)=0 :=
    seed_equations_zero (algebraMap R T) a B P e hseed q
  have hjac' : IsUnit (Matrix.det (fun i j =>
      aeval (0 : ι → T) (pderiv i (equations a B P e j)))) := by
    change IsUnit (Matrix.det (fun i j =>
      eval₂Hom (algebraMap R T) (0 : ι → T) (pderiv i (equations a B P e j))))
    rw [seed_jacobian_det_one (algebraMap R T) a B P e hjac]
    exact isUnit_one
  have hcomplement' : IsUnit (aeval (0 : ι → T) (relationA a B T₀ D V).det) := by
    change IsUnit (eval₂Hom (algebraMap R T) (0 : ι → T) (relationA a B T₀ D V).det)
    rw [seed_relationA_det_one (algebraMap R T) a B T₀ D V hcomplement]
    exact isUnit_one
  have hc' : IsUnit (aeval (0 : ι → T) (substitute a B c)) := by
    change IsUnit (eval₂Hom (algebraMap R T) (0 : ι → T) (substitute a B c))
    rw [eval_zero_substitute]
    exact hc
  have hopen : IsUnit (aeval (0 : ι → T)
      (substitute a B c*(relationA a B T₀ D V).det)) := by
    rw [map_mul]
    exact hc'.mul hcomplement'
  obtain ⟨I,hI,hfinite,hsep,x,hP,ho,hspecializes⟩ :=
    CycleQ2PointedOpenLifting.square_system_pointed_lift_on_open (K := K)
      (equations a B P e) (substitute a B c*(relationA a B T₀ D V).det)
      (0 : ι → T) hseed' hjac' hopen
  have hsem := affine_lift_semantics a B P Q V W T₀ D e c hdecomp hrelations x hP ho
  refine ⟨I,hI,hfinite,hsep,x,hsem.1,hsem.2,?_⟩
  intro p hp
  have hp' : aeval x (substitute a B p)=0 :=
    (eval_substitute (algebraMap R _) a B x p).trans hp
  exact (eval_zero_substitute (algebraMap R T) a B p).symm.trans
    (hspecializes (substitute a B p) hp')

end CycleQ2PointedCompatibleAffineLifting

#print axioms CycleQ2PointedCompatibleAffineLifting.affine_lift_semantics
#print axioms CycleQ2PointedCompatibleAffineLifting.pointed_lift_all_on_compatible_affine_slice
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechNormalization.lean -/
section
/-! The normalization of the actual two-endpoint Čech functional is obtained
from a checked identity in the first infinitesimal neighborhood of the two
endpoints.  No residue value is supplied as a hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

def powerCoefficient (r : ℂ) (e : Bool) : PowerChart r e →ₗ[PS] PS :=
  coefficient (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)

theorem firstJet_powerCoefficient (r : ℂ) (e : Bool) (z : PowerChart r e) :
    firstJet (powerCoefficient r e z) = jetCoefficient r e (jetEmbedding r e z) := by
  symm
  exact coefficient_curveMap firstJet _ _ _ _ z

theorem uniformizer_inv_sq : (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ 2) =
    HahnSeries.single (-2 : ℤ) 1 := by
  simp [uniformizerUnit, seriesMap, HahnSeries.ofPowerSeries_X,
    HahnSeries.inv_single, HahnSeries.single_pow]

/-- The double pole in x₁x₃ extracts the linear coefficient of an integral
power-series chart, for every power of the other cover equation. -/
theorem fractionResidue_double_pole (r : ℂ) (e : Bool) (p : Poly) (m : ℕ) :
    fractionResidue r e p 2 m =
      PowerSeries.coeff 1 (powerCoefficient r e
        (powerEval r e p * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ m)) := by
  let z : PowerChart r e :=
    powerEval r e p * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ m
  have heq : fraction r e p 2 m =
      laurentBase r e (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ 2) * chartEmbedding r e z := by
    simp only [fraction, laurentEval, RingHom.comp_apply, z, map_mul, map_pow,
      laurentBase, chartAUnit, laurentX2Unit, Units.coe_map_inv, Units.coe_map,
      MonoidHom.coe_coe]
    ring
  change (laurentCoefficient r e (fraction r e p 2 m)).coeff (-1) = _
  rw [heq]
  unfold laurentCoefficient laurentBase chartEmbedding
  rw [coefficient_base_mul, coefficient_curveMap, uniformizer_inv_sq,
    HahnSeries.coeff_single_mul]
  norm_num [seriesMap, powerCoefficient, PowerSeries.coeff_coe, z]

def soclePower (r : ℂ) (e : Bool) : PowerChart r e :=
  powerEval r e (mon 1 8 0 0) * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ 4

theorem jetEmbedding_soclePower (r : ℂ) (e : Bool) :
    jetEmbedding r e (soclePower r e) =
      jetX0 r e * (jetBase r e (firstJet (endpointX e)))^8 *
        ((jetX2Unit r e)⁻¹ : (JetChart r e)ˣ) ^ 4 := by
  simp only [soclePower, mon, map_mul, map_pow, powerEval_X,
    powerCoordinates_zero, powerCoordinates_one, powerCoordinates_two,
    powerCoordinates_three, pow_zero, pow_one, mul_one,
    jetEmbedding, curveMap_x0, curveMap_base, jetX0, jetBase,
    jetX2Unit, Units.coe_map_inv, MonoidHom.coe_coe]

theorem jetEmbedding_soclePower_false (r : ℂ) :
    jetEmbedding r false (soclePower r false) =
      jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4 := by
  rw [jetEmbedding_soclePower]
  simp only [endpointX, map_one, one_pow, mul_one]

theorem jetEmbedding_soclePower_true (r : ℂ) :
    jetEmbedding r true (soclePower r true) = 0 := by
  have ht : firstJet (PowerSeries.X : PS) ^ 8 = 0 := by
    rw [show 8 = 2 * 4 from rfl, pow_mul, firstJet_X_sq, zero_pow (by decide)]
  have ht' : (jetBase r true (firstJet PowerSeries.X)) ^ 8 = 0 := by
    rw [← map_pow, ht, map_zero]
  rw [jetEmbedding_soclePower]
  change jetX0 r true * (jetBase r true (firstJet PowerSeries.X))^8 * _ = 0
  rw [ht', mul_zero, zero_mul]

theorem soclePower_false_coefficient (r : ℂ) :
    PowerSeries.coeff 1 (powerCoefficient r false (soclePower r false)) = 3*r := by
  have hh : firstJet (powerCoefficient r false (soclePower r false)) =
      -1 + 3 * firstJet (PowerSeries.C r) * firstJet PowerSeries.X := by
    rw [firstJet_powerCoefficient, jetEmbedding_soclePower_false, false_jet_coefficient]
  have hs := congrArg TrivSqZeroExt.snd hh
  norm_num [firstJet, smul_eq_mul, op_smul_eq_smul, TrivSqZeroExt.fst_natCast] at hs ⊢
  exact hs

theorem soclePower_true_coefficient (r : ℂ) :
    PowerSeries.coeff 1 (powerCoefficient r true (soclePower r true)) = 0 := by
  have hh : firstJet (powerCoefficient r true (soclePower r true)) = 0 := by
    rw [firstJet_powerCoefficient, jetEmbedding_soclePower_true, map_zero]
  exact congrArg TrivSqZeroExt.snd hh

/-- The actual Laurent-series functional evaluates the published socle
representative to 3r at denominator (x₁x₃)²x₂⁴. -/
theorem cechResidue_socle (r : ℂ) :
    cechResidue r (mon 1 8 0 0) 2 4 = 3*r := by
  simp only [cechResidue, fractionResidue_double_pole]
  change PowerSeries.coeff 1 (powerCoefficient r false (soclePower r false)) -
    PowerSeries.coeff 1 (powerCoefficient r true (soclePower r true)) = 3*r
  rw [soclePower_false_coefficient, soclePower_true_coefficient, sub_zero]

theorem endpointResidue_scalar (r : ℂ) (e : Bool) (c : ℂ) (z : LaurentChart r e) :
    endpointResidue r e (laurentBase r e (seriesMap (PowerSeries.C c)) * z) =
      c * endpointResidue r e z := by
  change (laurentCoefficient r e
    (laurentBase r e (seriesMap (PowerSeries.C c)) * z)).coeff (-1) = _
  unfold laurentCoefficient laurentBase
  rw [coefficient_base_mul]
  change (seriesMap (PowerSeries.C c) * laurentCoefficient r e z).coeff (-1) = _
  rw [show seriesMap (PowerSeries.C c) = HahnSeries.single (0 : ℤ) c from
    HahnSeries.ofPowerSeries_C c, HahnSeries.coeff_single_zero_mul]
  rfl

theorem cechResidue_C_mul (r : ℂ) (c : ℂ) (p : Poly) (n m : ℕ) :
    cechResidue r (C c * p) n m = c * cechResidue r p n m := by
  have he (e : Bool) : fraction r e (C c * p) n m =
      laurentBase r e (seriesMap (PowerSeries.C c)) * fraction r e p n m := by
    simp [fraction, laurentEval, powerEval, chartEmbedding, laurentBase, mul_assoc]
  simp only [cechResidue, fractionResidue, he, endpointResidue_scalar]
  ring

theorem cechResidue_sub (r : ℂ) (p q : Poly) (n m : ℕ) :
    cechResidue r (p-q) n m = cechResidue r p n m - cechResidue r q n m := by
  simp only [cechResidue, fractionResidue, fraction_sub, map_sub]
  ring

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.cechResidue_socle
end
end


