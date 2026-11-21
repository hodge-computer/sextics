import Proposal.IncidenceGradedNormalForms
import Proposal.SegreCartierEquations

/-! # The incidence equations, their Jacobian and coefficient relations -/

set_option Elab.async false

/- Component: continuation_3/IncidenceEquations.lean -/
section
/-! # The actual coefficient equations of the Segre incidence

The matrix is centered at the literal raw seed matrix.  Coefficients of its
cofactor remainders, indexed by the complete invariant standard monomials of
degree twenty-eight, are the incidence equations.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceEquations

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials

variable {R : Type*} [CommRing R]


private lemma regrade {p : Poly R} {a b : Grade} (hp : HG p a) (h : a = b) : HG p b := h ▸ hp

def standardExponent {d : ℕ} (q : StandardIndex d) : FullExponent :=
  Finsupp.equivFunOnFinite.symm (coordinates q)

@[simp] lemma standardExponent_apply {d : ℕ} (q : StandardIndex d) (i : Fin 5) :
    standardExponent q i = coordinates q i := rfl

theorem standardExponent_grade {d : ℕ} (q : StandardIndex d) :
    Finsupp.weight fullGrading (standardExponent q) = (d, 0) := by
  have hq := ((exponentEquiv d 3 3) q).property
  rw [fullGrading_eq_iff]
  exact ⟨hq.2.2.1, hq.2.2.2⟩

theorem standard_eq_zero_of_coefficients {d : ℕ} {p : Poly R}
    (hs : FullStandard p) (hp : HG p (d, 0))
    (hc : ∀ q : StandardIndex d, p.coeff (standardExponent q) = 0) : p = 0 := by
  ext e
  simp only [coeff_zero]
  by_contra he
  have hs' := hs e (mem_support_iff.mpr he)
  have hd := (fullGrading_eq_iff e d).mp (hp he)
  let v : Exponents d 3 3 := ⟨e, hs'.1, hs'.2, hd.1, hd.2⟩
  let q : StandardIndex d := (exponentEquiv d 3 3).symm v
  have hq : standardExponent q = e := by
    ext i
    change coordinates q i = e i
    exact congrArg (fun z : Exponents d 3 3 ↦ z.val i)
      ((exponentEquiv d 3 3).apply_symm_apply v)
  exact he (hq ▸ hc q)

def rawSeedMatrix (r : R) : Matrix (Fin 3) (Fin 3) (Poly R) :=
  CycleQ2SegreSeed.rawMatrix (C r) (X 0) (X 1) (X 2) (X 3) (X 4)

def perturbation (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    Matrix (Fin 3) (Fin 3) (Poly R) :=
  fun i j ↦ ∑ q, monomial (standardExponent q) (δ i j q)

/-- The raw seed is unchanged when the cubic and sextic parameters vary. -/
def incidenceMatrix (r : R) (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    Matrix (Fin 3) (Fin 3) (Poly R) := rawSeedMatrix r + perturbation δ

@[simp] theorem incidenceMatrix_zero (r : R) :
    incidenceMatrix r (fun _ _ _ ↦ 0) = rawSeedMatrix r := by
  ext i j
  simp [incidenceMatrix, perturbation]

theorem perturbation_homogeneous
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (i j : Fin 3) :
    HG (perturbation δ i j) (14, 0) := by
  apply (weightedHomogeneousSubmodule R fullGrading (14, 0)).sum_mem
  intro q _
  exact isWeightedHomogeneous_monomial _ _ _ (standardExponent_grade q)

private lemma hx0 : HG (X 0 : Poly R) (1, 2) := isWeightedHomogeneous_X R fullGrading 0
private lemma hx1 : HG (X 1 : Poly R) (1, 2) := isWeightedHomogeneous_X R fullGrading 1
private lemma hx2 : HG (X 2 : Poly R) (1, 1) := isWeightedHomogeneous_X R fullGrading 2
private lemma hx3 : HG (X 3 : Poly R) (1, 0) := isWeightedHomogeneous_X R fullGrading 3
private lemma hw : HG (X 4 : Poly R) (2, 0) := isWeightedHomogeneous_X R fullGrading 4

private theorem leftCoeff0_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.leftCoeff0 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (6, 2) := by
  fin_cases i
  · exact (regrade (((hw.pow 2).neg.mul hx1).mul hx3) (by decide)).add
      (regrade ((hx1.pow 2).mul (hx2.pow 4)) (by decide))
  · exact ((regrade (hw.neg.mul (hx1.pow 4)) (by decide)).add
      (regrade ((hx0.pow 2).mul (hx2.pow 4)) (by decide))).add
      (regrade ((hx1.mul (hx2.pow 3)).mul (hx3.pow 2)) (by decide))
  · exact ((regrade (((hw.pow 2).neg.mul hx0).mul hx3) (by decide)).add
      (regrade ((hx1.pow 4).mul (hx3.pow 2)) (by decide))).add
      (regrade ((hx2.pow 2).mul (hx3.pow 4)) (by decide))

private theorem leftCoeff1_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.leftCoeff1 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (4, 0) := by
  fin_cases i
  · exact (regrade ((hx0.mul hx1).mul (hx2.pow 2)) (by decide)).sub
      (regrade ((hx0.mul hx2).mul (hx3.pow 2)) (by decide))
  · exact regrade (hx3.pow 4) (by decide)
  · exact regrade (hx3.pow 4) (by decide)

private theorem rightCoeff0_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff0 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (4, 0) := by
  fin_cases i
  · change HG (2 * (X 4 : Poly R) ^ 2 + 2 * X 4 * X 3 ^ 2) (4, 0)
    have h0 : HG ((C (2 : R)) * X 4 ^ 2) (4, 0) := regrade ((hw.pow 2).C_mul 2) (by decide)
    have h1 : HG ((C (2 : R)) * X 4 * X 3 ^ 2) (4, 0) :=
      regrade ((hw.C_mul 2).mul (hx3.pow 2)) (by decide)
    simpa only [map_ofNat] using h0.add h1
  · exact (regrade ((hw.mul hx0).mul hx2) (by decide)).add
      (regrade ((hx0.pow 2).mul (hx2.pow 2)) (by decide))
  · exact (((regrade ((hx0.mul (hx1.pow 2)).mul hx3) (by decide)).add
      (regrade ((hx1.mul hx2).mul (hx3.pow 2)) (by decide))).sub
      (regrade ((hx2.pow 3).mul hx3) (by decide))).add
      (regrade (hx3.pow 4) (by decide))

private theorem rightCoeff2_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff2 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (2, 0) := by
  fin_cases i
  · exact hw.add (regrade (hx3.pow 2) (by decide))
  · exact hw
  · exact isWeightedHomogeneous_zero _ _ _

private theorem rightCoeff3_homogeneous (i : Fin 3) :
    HG (CycleQ2SegreSeed.rightCoeff3 (X 0) (X 1) (X 2) (X 3) (X 4) i : Poly R) (2, 2) := by
  fin_cases i
  · exact isWeightedHomogeneous_zero _ _ _
  · exact regrade (hx0.mul hx3) (by decide)
  · exact isWeightedHomogeneous_zero _ _ _

private theorem baseRow0_homogeneous (r : R) (j : Fin 3) :
    HG (CycleQ2SegreSeed.baseRow0 (C r) (X 0) (X 1) (X 2) (X 3) (X 4) j) (8, 1) := by
  have ha : HG (X 0 ^ 2 : Poly R) (2, 1) := regrade (hx0.pow 2) (by decide)
  have hb : HG (C r * X 1 * X 3) (2, 2) := regrade ((hx1.C_mul r).mul hx3) (by decide)
  have hd : HG (X 2 ^ 2 : Poly R) (2, 2) := regrade (hx2.pow 2) (by decide)
  have hP := (regrade (ha.mul hw) (by decide : ((2,1) : Grade)+(2,0)=(4,1))).add
    (regrade (hb.mul hd) (by decide))
  have hQ := (regrade ((ha.pow 2).mul hb) (by decide : 2 • ((2,1) : Grade)+(2,2)=(6,1))).sub
    (regrade (hw.mul (hd.pow 2)) (by decide))
  have hT := (regrade (ha.mul (hb.pow 2)) (by decide : ((2,1) : Grade)+2 • (2,2)=(6,2))).add
    (regrade ((hw.pow 2).mul hd) (by decide))
  exact ((regrade (hP.mul (rightCoeff0_homogeneous j)) (by decide)).add
    (regrade (hQ.mul (rightCoeff2_homogeneous j)) (by decide))).add
    (regrade (hT.mul (rightCoeff3_homogeneous j)) (by decide))

private theorem baseRow1_homogeneous (r : R) (j : Fin 3) :
    HG (CycleQ2SegreSeed.baseRow1 (C r) (X 0) (X 1) (X 2) (X 3) (X 4) j) (10, 0) := by
  have ha : HG (X 0 ^ 2 : Poly R) (2, 1) := regrade (hx0.pow 2) (by decide)
  have hb : HG (C r * X 1 * X 3) (2, 2) := regrade ((hx1.C_mul r).mul hx3) (by decide)
  have hd : HG (X 2 ^ 2 : Poly R) (2, 2) := regrade (hx2.pow 2) (by decide)
  have hP := (regrade (ha.pow 3) (by decide : 3 • ((2,1) : Grade)=(6,0))).sub
    (regrade (hb.pow 3) (by decide))
  have hQ := ((regrade ((ha.pow 2).neg.mul (hd.pow 2)) (by decide : 2 • ((2,1) : Grade)+2 • (2,2)=(8,0))).sub
    (regrade ((ha.mul hb).mul (hw.pow 2)) (by decide))).add
    (regrade (((hb.pow 2).mul hw).mul hd) (by decide))
  have hT := ((regrade (((ha.pow 2).mul hw).mul hd) (by decide : 2 • ((2,1) : Grade)+(2,0)+(2,2)=(8,1))).sub
    (regrade ((ha.mul hb).mul (hd.pow 2)) (by decide))).sub
    (regrade ((hb.pow 2).mul (hw.pow 2)) (by decide))
  exact ((regrade (hP.mul (rightCoeff0_homogeneous j)) (by decide)).add
    (regrade (hQ.mul (rightCoeff2_homogeneous j)) (by decide))).add
    (regrade (hT.mul (rightCoeff3_homogeneous j)) (by decide))

theorem rawSeedMatrix_homogeneous (r : R) (i j : Fin 3) :
    HG (rawSeedMatrix r i j) (14, 0) :=
  (regrade ((leftCoeff0_homogeneous i).mul (baseRow0_homogeneous r j)) (by decide)).add
    (regrade ((leftCoeff1_homogeneous i).mul (baseRow1_homogeneous r j)) (by decide))

theorem incidenceMatrix_homogeneous (r : R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (i j : Fin 3) :
    HG (incidenceMatrix r δ i j) (14, 0) :=
  (rawSeedMatrix_homogeneous r i j).add (perturbation_homogeneous δ i j)

theorem cofactors_homogeneous (M : Matrix (Fin 3) (Fin 3) (Poly R))
    (hM : ∀ i j, HG (M i j) (14, 0)) (i j : Fin 3) :
    HG (CycleQ2SegreLocal.cofactors M i j) (28, 0) := by
  have hprod (i j k l : Fin 3) : HG (M i j * M k l) (28, 0) :=
    regrade ((hM i j).mul (hM k l)) (by decide)
  rw [CycleQ2SegreLocal.cofactors, Matrix.adjugate_fin_three]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ']
  all_goals first
  | exact (hprod _ _ _ _).sub (hprod _ _ _ _)
  | exact (hprod _ _ _ _).neg.add (hprod _ _ _ _)

abbrev EquationIndex := (Fin 3 × Fin 3) × StandardIndex 28

theorem equationIndex_count : Fintype.card EquationIndex = 9522 := by
  simp only [EquationIndex, Fintype.card_prod, Fintype.card_fin, standard_degree28_count]

def cofactorEquations [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (q : EquationIndex) : R :=
  (fullRemainder hcoeff Fcoeff hu Fu (CycleQ2SegreLocal.cofactors M q.1.1 q.1.2)).coeff
    (standardExponent q.2)

def incidenceEquations [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (r : R) (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) : EquationIndex → R :=
  cofactorEquations hcoeff Fcoeff hu Fu (incidenceMatrix r δ)

theorem cofactorEquations_zero_iff [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (hM : ∀ i j, HG (M i j) (14, 0)) :
    (∀ q, cofactorEquations hcoeff Fcoeff hu Fu M q = 0) ↔
      ∀ i j, CycleQ2SegreLocal.cofactors M i j ∈
        equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) := by
  constructor
  · intro hq i j
    apply (fullRemainder_eq_zero_iff hcoeff Fcoeff hu Fu _).mp
    apply standard_eq_zero_of_coefficients
    · exact (fullRemainder_spec hcoeff Fcoeff hu Fu _).1
    · exact fullRemainder_preserves_grading hcoeff Fcoeff hu Fu (cofactors_homogeneous M hM i j)
    · intro q
      exact hq ((i,j),q)
  · intro hM q
    have hz := (fullRemainder_eq_zero_iff hcoeff Fcoeff hu Fu _).mpr (hM q.1.1 q.1.2)
    simp [cofactorEquations, hz]

theorem incidenceEquations_zero_iff [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (r : R) (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    (∀ q, incidenceEquations hcoeff Fcoeff hu Fu r δ q = 0) ↔
      ∀ i j, CycleQ2SegreLocal.cofactors (incidenceMatrix r δ) i j ∈
        equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) :=
  cofactorEquations_zero_iff hcoeff Fcoeff hu Fu (incidenceMatrix r δ)
    (incidenceMatrix_homogeneous r δ)

section Naturality

variable {S : Type*} [CommRing S]

theorem map_rawSeedMatrix (φ : R →+* S) (r : R) :
    (map φ).mapMatrix (rawSeedMatrix r) = rawSeedMatrix (φ r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rawSeedMatrix, CycleQ2SegreSeed.rawMatrix,
      CycleQ2SegreSeed.leftCoeff0, CycleQ2SegreSeed.leftCoeff1,
      CycleQ2SegreSeed.baseRow0, CycleQ2SegreSeed.baseRow1,
      CycleQ2SegreSeed.coreRight0, CycleQ2SegreSeed.coreRight1,
      CycleQ2SegreSeed.rightCoeff0, CycleQ2SegreSeed.rightCoeff2,
      CycleQ2SegreSeed.rightCoeff3, RingHom.mapMatrix_apply]

theorem map_perturbation (φ : R →+* S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    (map φ).mapMatrix (perturbation δ) = perturbation (fun i j q ↦ φ (δ i j q)) := by
  ext i j
  simp [perturbation, RingHom.mapMatrix_apply]

theorem map_incidenceMatrix (φ : R →+* S) (r : R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    (map φ).mapMatrix (incidenceMatrix r δ) =
      incidenceMatrix (φ r) (fun i j q ↦ φ (δ i j q)) := by
  unfold incidenceMatrix
  rw [map_add, map_rawSeedMatrix, map_perturbation]

theorem map_cofactors (φ : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    map φ (CycleQ2SegreLocal.cofactors M i j) =
      CycleQ2SegreLocal.cofactors ((map φ).mapMatrix M) i j := by
  exact congrArg (fun N : Matrix (Fin 3) (Fin 3) (Poly S) ↦ N j i)
    ((map φ).map_adjugate M)

/-- All 9522 equations commute with every coefficient specialization for which
the two leading coefficients remain units. -/
theorem cofactorEquations_map [Nontrivial R] [Nontrivial S]
    (φ : R →+* S)
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (q : EquationIndex) :
    φ (cofactorEquations hcoeff Fcoeff hu Fu M q) =
      cofactorEquations (φ ∘ hcoeff) (φ ∘ Fcoeff) (hu.map φ) (Fu.map φ)
        ((map φ).mapMatrix M) q := by
  unfold cofactorEquations
  rw [← coeff_map, fullRemainder_map, map_cofactors]

theorem incidenceEquations_map [Nontrivial R] [Nontrivial S]
    (φ : R →+* S)
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (r : R) (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) (q : EquationIndex) :
    φ (incidenceEquations hcoeff Fcoeff hu Fu r δ q) =
      incidenceEquations (φ ∘ hcoeff) (φ ∘ Fcoeff) (hu.map φ) (Fu.map φ)
        (φ r) (fun i j e ↦ φ (δ i j e)) q := by
  unfold incidenceEquations
  rw [cofactorEquations_map, map_incidenceMatrix]

end Naturality

/-! ## The literal smooth incidence seed

The parameter `ι` may be specialized to `Complex.I`.  The cubic used by the
incidence chart contains the additional term `x0^3`; the raw matrix itself is
exactly the published raw matrix.
-/



private def wOnly : Fin 5 → ℕ := fun i ↦ if i = 4 then 1 else 0

private theorem wOnly_X (i : Fin 5) (hi : i ≠ 4) :
    (X i : Poly R).IsWeightedHomogeneous wOnly 0 := by
  simpa only [wOnly, if_neg hi] using isWeightedHomogeneous_X R wOnly i

private theorem smoothB_no_w :
    (smoothB : Poly R).IsWeightedHomogeneous wOnly 0 := by
  have h0 := wOnly_X (R := R) 0 (by decide)
  have h1 := wOnly_X (R := R) 1 (by decide)
  have h2 := wOnly_X (R := R) 2 (by decide)
  have h3 := wOnly_X (R := R) 3 (by decide)
  exact (((((h3.pow 3).add (h2.pow 3)).add ((h1.mul h2).mul h3)).add
    ((h0.mul h2).mul h3)).add (h0.mul (h1.pow 2))).add (h0.pow 3)

private theorem smoothA_no_w :
    (smoothA : Poly R).IsWeightedHomogeneous wOnly 0 :=
  ((wOnly_X 1 (by decide)).pow 3).add ((wOnly_X 3 (by decide)).pow 3)

private theorem wOnly_leading_ne :
    Finsupp.weight wOnly (Finsupp.single 4 3) ≠ 0 := by
  simp [Finsupp.weight_single, wOnly]





/-- The literal cofactor factorization supplies the actual seed incidence,
without a numerical rank hypothesis or an assumed minor value. -/
theorem rawSeedMatrix_cofactor_mem (r ι : R) (i j : Fin 3) :
    CycleQ2SegreLocal.cofactors (rawSeedMatrix r) i j ∈
      equationsIdeal (smoothH ι) (smoothF r ι) := by
  have hid := congrArg (fun N : Matrix (Fin 3) (Fin 3) (Poly R) ↦ N i j)
    (CycleQ2SegreSeed.rawMatrix_cofactor_identity (C r) (X 0) (X 1) (X 2) (X 3) (X 4))
  change CycleQ2SegreLocal.cofactors (rawSeedMatrix r) i j =
    seedG r * CycleQ2SegreSeed.rawCofactorQuotient (C r) (X 0) (X 1) (X 2) (X 3) (X 4) i j at hid
  rw [hid, equationsIdeal, Ideal.mem_span_pair]
  let Q : Poly R := CycleQ2SegreSeed.rawCofactorQuotient (C r) (X 0) (X 1) (X 2) (X 3) (X 4) i j
  refine ⟨-(smoothK ι * Q), Q, ?_⟩
  dsimp [smoothF]
  ring

theorem smoothSeed_equations_zero [Nontrivial R] (r ι : R) (q : EquationIndex) :
    incidenceEquations (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
      r (fun _ _ _ ↦ 0) q = 0 := by
  apply (incidenceEquations_zero_iff _ _ _ _ r (fun _ _ _ ↦ 0)).mpr _ q
  intro i j
  rw [incidenceMatrix_zero, seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial]
  exact rawSeedMatrix_cofactor_mem r ι i j

theorem complexSmoothSeed_equations_zero (r : ℂ) (q : EquationIndex) :
    incidenceEquations (seedCubicCoefficients Complex.I) (seedSexticCoefficients r Complex.I)
      (seedCubicCoefficients_unit Complex.I) (seedSexticCoefficients_unit r Complex.I)
      r (fun _ _ _ ↦ 0) q = 0 :=
  smoothSeed_equations_zero r Complex.I q

end CycleQ2IncidenceEquations

#print axioms CycleQ2IncidenceEquations.incidenceEquations_zero_iff
#print axioms CycleQ2IncidenceEquations.incidenceEquations_map
#print axioms CycleQ2IncidenceEquations.complexSmoothSeed_equations_zero
end
end

/- Component: continuation_3/IncidenceFirstOrder.lean -/
section
/-! # First-order equations at the literal Segre seed

This file identifies the moving-cubic linearized residual directly from the
quadratic cofactor identity.  A residual in `(h,G)` produces an actual solution
of all 9522 incidence equations over any square-zero thickening.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceFirstOrder

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations

section Cofactors

variable {A : Type*} [CommRing A]

/-- Polarization of the quadratic cofactor polynomial. -/
def cofactorDifferential (M N : Matrix (Fin 3) (Fin 3) A) : Matrix (Fin 3) (Fin 3) A :=
  CycleQ2SegreLocal.cofactors (M + N) -
    CycleQ2SegreLocal.cofactors M - CycleQ2SegreLocal.cofactors N

theorem cofactor_quadratic (M N : Matrix (Fin 3) (Fin 3) A) (t : A) (i j : Fin 3) :
    CycleQ2SegreLocal.cofactors (fun i j ↦ M i j + t * N i j) i j =
      CycleQ2SegreLocal.cofactors M i j + t * cofactorDifferential M N i j +
        t ^ 2 * CycleQ2SegreLocal.cofactors N i j := by
  simp only [cofactorDifferential, CycleQ2SegreLocal.cofactors, Matrix.adjugate_fin_three,
    Matrix.add_apply, Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> ring

/-- Explicit bilinear entries, so sparse certificates need never expand a
product of two correction polynomials and subsequently cancel it. -/
theorem cofactorDifferential_fin_three (M N : Matrix (Fin 3) (Fin 3) A) :
    cofactorDifferential M N =
      ![![N 1 1 * M 2 2 + M 1 1 * N 2 2 - N 1 2 * M 2 1 - M 1 2 * N 2 1,
          -N 1 0 * M 2 2 - M 1 0 * N 2 2 + N 1 2 * M 2 0 + M 1 2 * N 2 0,
          N 1 0 * M 2 1 + M 1 0 * N 2 1 - N 1 1 * M 2 0 - M 1 1 * N 2 0],
        ![-N 0 1 * M 2 2 - M 0 1 * N 2 2 + N 0 2 * M 2 1 + M 0 2 * N 2 1,
          N 0 0 * M 2 2 + M 0 0 * N 2 2 - N 0 2 * M 2 0 - M 0 2 * N 2 0,
          -N 0 0 * M 2 1 - M 0 0 * N 2 1 + N 0 1 * M 2 0 + M 0 1 * N 2 0],
        ![N 0 1 * M 1 2 + M 0 1 * N 1 2 - N 0 2 * M 1 1 - M 0 2 * N 1 1,
          -N 0 0 * M 1 2 - M 0 0 * N 1 2 + N 0 2 * M 1 0 + M 0 2 * N 1 0,
          N 0 0 * M 1 1 + M 0 0 * N 1 1 - N 0 1 * M 1 0 - M 0 1 * N 1 0]] := by
  ext i j
  simp only [cofactorDifferential, CycleQ2SegreLocal.cofactors, Matrix.adjugate_fin_three,
    Matrix.add_apply, Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> ring

theorem cofactorDifferential_add (M N P : Matrix (Fin 3) (Fin 3) A) :
    cofactorDifferential M (N + P) = cofactorDifferential M N + cofactorDifferential M P := by
  ext i j
  simp only [cofactorDifferential, CycleQ2SegreLocal.cofactors, Matrix.adjugate_fin_three,
    Matrix.add_apply, Matrix.sub_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> ring

theorem cofactorDifferential_smul (M N : Matrix (Fin 3) (Fin 3) A) (t : A) :
    cofactorDifferential M (t • N) = t • cofactorDifferential M N := by
  ext i j
  simp only [cofactorDifferential, CycleQ2SegreLocal.cofactors, Matrix.adjugate_fin_three,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero',
      Matrix.cons_val_succ'] <;> ring

def cofactorDifferentialLinear (M : Matrix (Fin 3) (Fin 3) A) :
    Matrix (Fin 3) (Fin 3) A →ₗ[A] Matrix (Fin 3) (Fin 3) A where
  toFun := cofactorDifferential M
  map_add' := cofactorDifferential_add M
  map_smul' := fun t N ↦ cofactorDifferential_smul M N t

end Cofactors

variable {R : Type*} [CommRing R]

def rawCofactorQuotient (r : R) : Matrix (Fin 3) (Fin 3) (Poly R) :=
  CycleQ2SegreSeed.rawCofactorQuotient (C r) (X 0) (X 1) (X 2) (X 3) (X 4)

theorem rawSeedMatrix_cofactor (r : R) (i j : Fin 3) :
    CycleQ2SegreLocal.cofactors (rawSeedMatrix r) i j =
      seedG r * rawCofactorQuotient r i j :=
  congrArg (fun M : Matrix (Fin 3) (Fin 3) (Poly R) ↦ M i j)
    (CycleQ2SegreSeed.rawMatrix_cofactor_identity (C r) (X 0) (X 1) (X 2) (X 3) (X 4))

def firstOrderResidual (r ι : R) (H : Poly R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R)) : Matrix (Fin 3) (Fin 3) (Poly R) :=
  fun i j ↦ cofactorDifferential (rawSeedMatrix r) N i j +
    H * smoothK ι * rawCofactorQuotient r i j

/-- The plus sign in `Dcof + H*k*Q` follows from the actual seed identity
`Cof(Mraw)=G*Q` and the actual equation `F=G+h*k`. -/
theorem cofactor_seed_deformation (r ι : R) (H t : Poly R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    CycleQ2SegreLocal.cofactors (fun i j ↦ rawSeedMatrix r i j + t * N i j) i j =
      -(smoothK ι * rawCofactorQuotient r i j) * (smoothH ι + t * H) +
        rawCofactorQuotient r i j * smoothF r ι +
        t * firstOrderResidual r ι H N i j +
        t ^ 2 * CycleQ2SegreLocal.cofactors N i j := by
  rw [cofactor_quadratic, rawSeedMatrix_cofactor]
  unfold firstOrderResidual smoothF
  ring

theorem firstOrderResidual_vanishes_iff [Nontrivial R]
    (r ι : R) (H : Poly R) (N : Matrix (Fin 3) (Fin 3) (Poly R)) (i j : Fin 3) :
    fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
      (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
      (firstOrderResidual r ι H N i j) = 0 ↔
      ∃ a b : Poly R, a * smoothH ι + b * seedG r = firstOrderResidual r ι H N i j := by
  rw [fullRemainder_eq_zero_iff, seedCubicCoefficients_polynomial,
    seedSexticCoefficients_polynomial, smoothSeed_mem_iff_linkage]

theorem infinitesimal_cofactor_mem (r ι : R) (H t : Poly R)
    (N : Matrix (Fin 3) (Fin 3) (Poly R)) (ht : t ^ 2 = 0) (i j : Fin 3)
    (hD : firstOrderResidual r ι H N i j ∈ equationsIdeal (smoothH ι) (smoothF r ι)) :
    CycleQ2SegreLocal.cofactors (fun i j ↦ rawSeedMatrix r i j + t * N i j) i j ∈
      equationsIdeal (smoothH ι + t * H) (smoothF r ι) := by
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hD
  rw [equationsIdeal, Ideal.mem_span_pair, cofactor_seed_deformation, ← hab]
  refine ⟨-(smoothK ι * rawCofactorQuotient r i j) + t * a,
    rawCofactorQuotient r i j + t * b, ?_⟩
  linear_combination (a * H - CycleQ2SegreLocal.cofactors N i j) * ht

def deformedCubicCoefficients (ι t : R) (η : FullInvariantIndex 3 → R) :
    FullInvariantIndex 3 → R := fun e ↦ seedCubicCoefficients ι e + t * η e

theorem deformedCubicCoefficients_polynomial (ι t : R) (η : FullInvariantIndex 3 → R) :
    fullInvariantPolynomial 3 (deformedCubicCoefficients ι t η) =
      smoothH ι + C t * fullInvariantPolynomial 3 η := by
  rw [← seedCubicCoefficients_polynomial]
  simp [fullInvariantPolynomial, deformedCubicCoefficients, map_add,
    Finset.sum_add_distrib, Finset.mul_sum, C_mul_monomial]

theorem deformedCubicCoefficients_unit (ι t : R) (η : FullInvariantIndex 3 → R)
    (ht : t ^ 2 = 0) : IsUnit (deformedCubicCoefficients ι t η fullCubicLeadingIndex) := by
  simp only [deformedCubicCoefficients, seedCubicCoefficients,
    fullCubicLeadingIndex_exponent, smoothH_leading_coefficient]
  apply IsUnit.of_mul_eq_one (1 - t * η fullCubicLeadingIndex)
  calc
    (1 + t * η fullCubicLeadingIndex) * (1 - t * η fullCubicLeadingIndex) =
        1 - t ^ 2 * (η fullCubicLeadingIndex) ^ 2 := by ring
    _ = 1 := by rw [ht]; ring

theorem incidenceMatrix_scaled (r t : R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    incidenceMatrix r (fun i j e ↦ t * δ i j e) =
      fun i j ↦ rawSeedMatrix r i j + C t * perturbation δ i j := by
  ext i j
  simp [incidenceMatrix, perturbation, Finset.mul_sum, C_mul_monomial]

/-- A vanishing first-order residual gives a genuine square-zero solution of
the already-defined coefficient equations, with its leading unit proved. -/
theorem infinitesimal_incidenceEquations_zero [Nontrivial R]
    (r ι t : R) (ht : t ^ 2 = 0) (η : FullInvariantIndex 3 → R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R)
    (hD : ∀ i j, firstOrderResidual r ι (fullInvariantPolynomial 3 η) (perturbation δ) i j ∈
      equationsIdeal (smoothH ι) (smoothF r ι)) (q : EquationIndex) :
    incidenceEquations (deformedCubicCoefficients ι t η) (seedSexticCoefficients r ι)
      (deformedCubicCoefficients_unit ι t η ht) (seedSexticCoefficients_unit r ι)
      r (fun i j e ↦ t * δ i j e) q = 0 := by
  apply (incidenceEquations_zero_iff _ _ _ _ r (fun i j e ↦ t * δ i j e)).mpr _ q
  intro i j
  rw [deformedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial,
    incidenceMatrix_scaled]
  apply infinitesimal_cofactor_mem r ι _ _ _ _ i j (hD i j)
  rw [← map_pow, ht, map_zero]

end CycleQ2IncidenceFirstOrder

#print axioms CycleQ2IncidenceFirstOrder.cofactor_seed_deformation
#print axioms CycleQ2IncidenceFirstOrder.firstOrderResidual_vanishes_iff
#print axioms CycleQ2IncidenceFirstOrder.infinitesimal_incidenceEquations_zero
end
end

/- Component: continuation_3/IncidenceUniversalChart.lean -/
section
/-!
# The concrete localized universal incidence coefficient ring

Every raw cubic coefficient, every raw sextic coefficient, and every matrix
perturbation coefficient is an independent polynomial variable.  The two
leading coefficient variables are genuinely inverted by localization.  The
9522 equations are elements of this ring, with their actual specialization
maps and a proved literal seed.  No polynomial identity is asserted before
imposing the inverse equations or performing this localization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CycleQ2IncidenceUniversalChart

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations






variable (R : Type*) [CommRing R] [IsDomain R]





def equations (r : R) : EquationIndex → ParameterRing R :=
  incidenceEquations (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (algebraMap R (ParameterRing R) r) (matrixCoefficient R)

section Specialization

variable {R} {S : Type*} [CommRing S] [Algebra R S]








theorem specialization_equations [Nontrivial S]
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (r : R) (q : EquationIndex) :
    specialization hcoeff Fcoeff hu Fu δ (equations R r q) =
      incidenceEquations hcoeff Fcoeff hu Fu (algebraMap R S r) δ q := by
  let φ := specialization (R := R) hcoeff Fcoeff hu Fu δ
  have hh : φ.toRingHom ∘ cubicCoefficient R = hcoeff := by
    funext e
    exact specialization_cubicCoefficient hcoeff Fcoeff hu Fu δ e
  have hF : φ.toRingHom ∘ sexticCoefficient R = Fcoeff := by
    funext e
    exact specialization_sexticCoefficient hcoeff Fcoeff hu Fu δ e
  have hδ : (fun i j e => φ.toRingHom (matrixCoefficient R i j e)) = δ := by
    funext i j e
    exact specialization_matrixCoefficient hcoeff Fcoeff hu Fu δ i j e
  have hr : φ.toRingHom (algebraMap R (ParameterRing R) r) = algebraMap R S r :=
    φ.commutes r
  have hm := incidenceEquations_map φ.toRingHom
    (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (algebraMap R (ParameterRing R) r) (matrixCoefficient R) q
  change φ.toRingHom (incidenceEquations (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (algebraMap R (ParameterRing R) r) (matrixCoefficient R) q) = _
  simpa only [hh, hF, hδ, hr] using hm

end Specialization


theorem seedSpecialization_equations (r ι : R) (q : EquationIndex) :
    seedSpecialization R r ι (equations R r q) = 0 := by
  rw [seedSpecialization, specialization_equations]
  simpa using smoothSeed_equations_zero r ι q

end CycleQ2IncidenceUniversalChart

#print axioms CycleQ2IncidenceUniversalChart.leading_coefficients_units
#print axioms CycleQ2IncidenceUniversalChart.specialization_equations
#print axioms CycleQ2IncidenceUniversalChart.seedSpecialization_equations
end
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

/- Component: continuation_3/IncidenceCoefficientRelations.lean -/
section
/-!
# The actual coefficient-level relations among the incidence equations

The sixteen universal Segre identities are reduced in the same moving
cubic/sextic quotient as the incidence equations.  Expanding in the proved
degree-28 and degree-42 standard bases produces a genuine 39440-by-9522
relation matrix over the localized coefficient ring.  Its identity is
universal, not restricted to the numerical seed or to points on one fiber.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2IncidenceCoefficientRelations

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceJacobian
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem standardExponent_injective {d : ℕ} :
    Function.Injective (@standardExponent d) := by
  intro a b hab
  apply (exponentEquiv d 3 3).injective
  apply Subtype.ext
  funext i
  exact congrArg (fun e : FullExponent => e i) hab

def standardExpansion (d : ℕ) (p : Poly R) : Poly R :=
  ∑ e : StandardIndex d, p.coeff (standardExponent e) • monomial (standardExponent e) 1

theorem standardExpansion_coeff (d : ℕ) (p : Poly R) (e : StandardIndex d) :
    (standardExpansion d p).coeff (standardExponent e) = p.coeff (standardExponent e) := by
  classical
  have heq (f : StandardIndex d) : standardExponent f = standardExponent e ↔ f = e :=
    standardExponent_injective.eq_iff
  simp [standardExpansion, coeff_sum, coeff_smul, coeff_monomial, heq]

theorem standardExpansion_eq (d : ℕ) (p : Poly R)
    (hp : FullStandard p) (hg : HG p (d, 0)) : standardExpansion d p = p := by
  classical
  ext e
  by_cases he : ∃ q : StandardIndex d, standardExponent q = e
  · obtain ⟨q, rfl⟩ := he
    exact standardExpansion_coeff d p q
  · have hz : p.coeff e = 0 := by
      by_contra hne
      have hb := hp e (mem_support_iff.mpr hne)
      have hd := (fullGrading_eq_iff e d).mp (hg hne)
      let v : Exponents d 3 3 := ⟨e, hb.1, hb.2, hd.1, hd.2⟩
      let q := (exponentEquiv d 3 3).symm v
      apply he
      refine ⟨q, ?_⟩
      ext i
      exact congrArg (fun z : Exponents d 3 3 => z.val i)
        ((exponentEquiv d 3 3).apply_symm_apply v)
    rw [hz]
    simp only [standardExpansion, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro q _
    have hq : standardExponent q ≠ e := fun hq => he ⟨q, hq⟩
    simp [hq]

section NormalMultiplication

variable [Nontrivial R]
variable (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
  (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex))

theorem sub_fullRemainder_mem (p : Poly R) :
    p - fullRemainder hc Fc hu Fu p ∈
      equationsIdeal (fullInvariantPolynomial 3 hc) (fullInvariantPolynomial 6 Fc) := by
  obtain ⟨_, a, b, hp⟩ := fullRemainder_spec hc Fc hu Fu p
  apply Ideal.mem_span_pair.mpr
  exact ⟨a, b, (sub_eq_iff_eq_add.mpr hp).symm⟩

/-- Multiplication in the actual quotient is computed by remaindering a
product of a polynomial with the other factor's normal form. -/
theorem fullRemainder_mul_remainder (a b : Poly R) :
    fullRemainder hc Fc hu Fu (a * fullRemainder hc Fc hu Fu b) =
      fullRemainder hc Fc hu Fu (a * b) := by
  let N := fullRemainderLinear hc Fc hu Fu
  have hz : fullRemainder hc Fc hu Fu (a * (b - fullRemainder hc Fc hu Fu b)) = 0 :=
    (fullRemainder_eq_zero_iff hc Fc hu Fu _).mpr
      (Ideal.mul_mem_left _ a (sub_fullRemainder_mem hc Fc hu Fu b))
  have hsub : N (a * b) - N (a * fullRemainder hc Fc hu Fu b) = 0 := by
    rw [← map_sub, ← mul_sub]
    exact hz
  exact (sub_eq_zero.mp hsub).symm

end NormalMultiplication

def cofactorPosition : Fin 9 ≃ Fin 3 × Fin 3 :=
  (finProdFinEquiv (m := 3) (n := 3)).symm

theorem cofactor_position (M : Matrix (Fin 3) (Fin 3) R) (k : Fin 9) :
    CycleQ2SegreRelations.cofactors M k =
      CycleQ2SegreLocal.cofactors M (cofactorPosition k).1 (cofactorPosition k).2 := by
  unfold CycleQ2SegreLocal.cofactors
  rw [← CycleQ2SegreRelations.cofactorMatrix_eq_transpose_adjugate]
  fin_cases k <;> rfl

abbrev RelationIndex := Fin 16 × StandardIndex 42
abbrev ColumnIndex := Fin 9 × StandardIndex 28

def columnEquiv : ColumnIndex ≃ EquationIndex :=
  Equiv.prodCongr cofactorPosition (Equiv.refl _)

theorem relationIndex_count : Fintype.card RelationIndex = 39440 := by
  simp only [RelationIndex, Fintype.card_prod, Fintype.card_fin, standard_degree42_count]

theorem columnIndex_count : Fintype.card ColumnIndex = 9522 := by
  simp only [ColumnIndex, Fintype.card_prod, Fintype.card_fin, standard_degree28_count]

section Relations

variable [Nontrivial R]
variable (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
  (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex))

def coefficientRelations (M : Matrix (Fin 3) (Fin 3) (Poly R)) :
    Matrix RelationIndex ColumnIndex R := fun row col =>
  (fullRemainder hc Fc hu Fu
    (CycleQ2SegreRelations.relations M row.1 col.1 *
      monomial (standardExponent col.2) 1)).coeff (standardExponent row.2)

theorem normal_cofactor_relations (M : Matrix (Fin 3) (Fin 3) (Poly R)) (k : Fin 16) :
    ∑ j : Fin 9, fullRemainder hc Fc hu Fu
      (CycleQ2SegreRelations.relations M k j *
        fullRemainder hc Fc hu Fu (CycleQ2SegreRelations.cofactors M j)) = 0 := by
  let N := fullRemainderLinear hc Fc hu Fu
  have hm := congrFun (CycleQ2SegreRelations.relations_cofactors M) k
  change (∑ j, CycleQ2SegreRelations.relations M k j *
    CycleQ2SegreRelations.cofactors M j) = 0 at hm
  simp_rw [fullRemainder_mul_remainder]
  change (∑ j, N (CycleQ2SegreRelations.relations M k j *
    CycleQ2SegreRelations.cofactors M j)) = 0
  rw [← map_sum, hm, map_zero]

theorem coefficientRelations_cofactorEquations
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (hM : ∀ i j, HG (M i j) (14, 0)) :
    coefficientRelations hc Fc hu Fu M *ᵥ
      (fun q : ColumnIndex => cofactorEquations hc Fc hu Fu M (columnEquiv q)) = 0 := by
  let N := fullRemainderLinear hc Fc hu Fu
  have hexp (j : Fin 9) :
      fullRemainder hc Fc hu Fu (CycleQ2SegreRelations.cofactors M j) =
        ∑ e : StandardIndex 28,
          cofactorEquations hc Fc hu Fu M (columnEquiv (j, e)) •
            monomial (standardExponent e) 1 := by
    rw [cofactor_position]
    exact (standardExpansion_eq 28 _ (fullRemainder_spec hc Fc hu Fu _).1
      (fullRemainder_preserves_grading hc Fc hu Fu
        (cofactors_homogeneous M hM _ _))).symm
  have hterm (k : Fin 16) (j : Fin 9) :
      fullRemainder hc Fc hu Fu
        (CycleQ2SegreRelations.relations M k j *
          fullRemainder hc Fc hu Fu (CycleQ2SegreRelations.cofactors M j)) =
        ∑ e : StandardIndex 28, cofactorEquations hc Fc hu Fu M (columnEquiv (j, e)) •
          fullRemainder hc Fc hu Fu
            (CycleQ2SegreRelations.relations M k j * monomial (standardExponent e) 1) := by
    rw [hexp, Finset.mul_sum]
    change N (∑ e : StandardIndex 28, _) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [mul_smul_comm, map_smul]
    rfl
  funext row
  have hh := congrArg (fun p : Poly R => p.coeff (standardExponent row.2))
    (normal_cofactor_relations hc Fc hu Fu M row.1)
  simp_rw [hterm] at hh
  simp only [coeff_sum, coeff_smul, smul_eq_mul, coeff_zero] at hh
  change (∑ q : ColumnIndex, coefficientRelations hc Fc hu Fu M row q *
    cofactorEquations hc Fc hu Fu M (columnEquiv q)) = 0
  simpa only [coefficientRelations, Fintype.sum_prod_type, mul_comm] using hh

/-- The actual moving incidence equations satisfy every coefficient relation,
over any leading-unit coefficient ring and before solving any subsystem. -/
theorem coefficientRelations_incidenceEquations (r : R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    coefficientRelations hc Fc hu Fu (incidenceMatrix r δ) *ᵥ
      (fun q : ColumnIndex => incidenceEquations hc Fc hu Fu r δ (columnEquiv q)) = 0 :=
  coefficientRelations_cofactorEquations hc Fc hu Fu (incidenceMatrix r δ)
    (incidenceMatrix_homogeneous r δ)

end Relations

end CycleQ2IncidenceCoefficientRelations

#print axioms CycleQ2IncidenceCoefficientRelations.standardExpansion_eq
#print axioms CycleQ2IncidenceCoefficientRelations.coefficientRelations_incidenceEquations
end
end
