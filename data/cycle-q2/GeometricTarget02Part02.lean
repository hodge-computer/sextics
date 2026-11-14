import Proposal.GeometricSurfaceBindings
import Proposal.GeometricSurfaceCoordinates
import Proposal.GeometricCurveCoordinates
import Proposal.GeometricTarget02Part01

/-! Continuation of GeometricTarget02.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: continuation_3/SparseGaussianLayers.lean -/
section
/-! Horner blocks for small independent kernel checks of sparse identities. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

abbrev Layers := List Sparse

def addLayers : Layers → Layers → Layers
  | [], q => q
  | p, [] => p
  | a::p, b::q => add a b :: addLayers p q

def mulLayers (p q : Layers) : Layers :=
  p.foldr (fun a acc => addLayers (q.map (mul a)) ([]::acc)) []

def negLayers (p : Layers) : Layers := p.map neg

def checkLayer (p : Layers) (n : ℕ) : Bool := checkZero (p[n]?.getD [])

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

def evalLayers (φ : GaussianInt →+* R) (x : Fin 5 → R) (z : R) : Layers → R
  | [] => 0
  | a::p => eval φ x a + z * evalLayers φ x z p

theorem eval_addLayers (x : Fin 5 → R) (z : R) (p q : Layers) :
    evalLayers φ x z (addLayers p q) = evalLayers φ x z p + evalLayers φ x z q := by
  induction p generalizing q with
  | nil => simp [addLayers, evalLayers]
  | cons a p ih =>
    cases q with
    | nil => simp [addLayers, evalLayers]
    | cons b q => simp only [addLayers, evalLayers, eval_add, ih]; ring

theorem eval_scaleLayers (x : Fin 5 → R) (z : R) (a : Sparse) (q : Layers) :
    evalLayers φ x z (q.map (mul a)) = eval φ x a * evalLayers φ x z q := by
  induction q with
  | nil => simp [evalLayers]
  | cons b q ih => simp only [List.map_cons, evalLayers, eval_mul, ih]; ring

theorem eval_mulLayers (x : Fin 5 → R) (z : R) (p q : Layers) :
    evalLayers φ x z (mulLayers p q) = evalLayers φ x z p * evalLayers φ x z q := by
  induction p with
  | nil => simp [mulLayers, evalLayers]
  | cons a p ih =>
    change evalLayers φ x z (addLayers (q.map (mul a)) ([]::mulLayers p q)) = _
    rw [eval_addLayers, eval_scaleLayers, evalLayers, eval_nil, ih, evalLayers]
    ring

theorem eval_negLayers (x : Fin 5 → R) (z : R) (p : Layers) :
    evalLayers φ x z (negLayers p) = -evalLayers φ x z p := by
  induction p with
  | nil => simp [negLayers, evalLayers]
  | cons a p ih =>
    change eval φ x (neg a) + z * evalLayers φ x z (negLayers p) = _
    rw [eval_neg, ih, evalLayers]
    ring

/-- Separate checked coefficient blocks imply the whole polynomial identity.
The bound concerns only the list of Horner blocks, never an arithmetic rank. -/
theorem evalLayers_eq_zero_of_checks (x : Fin 5 → R) (z : R) (N : ℕ) (p : Layers)
    (hlen : p.length ≤ N) (h : ∀ n : Fin N, checkLayer p n = true) :
    evalLayers φ x z p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalLayers]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have ha : checkZero a = true := by
        simpa only [checkLayer, Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using h 0
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hh : ∀ n : Fin N, checkLayer p n = true := by
        intro n
        simpa only [checkLayer, Fin.val_succ, List.getElem?_cons_succ] using h n.succ
      rw [evalLayers, eval_eq_zero_of_check φ x a ha, ih p hp hh, mul_zero, add_zero]

end Soundness
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.evalLayers_eq_zero_of_checks
#print axioms CycleQ2SparseGaussianPolynomial.eval_mulLayers
end


/- Component: continuation_3/SparseModularLayers.lean -/
section
/-! Horner blocks for small independent kernel checks of sparse identities. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseModularPolynomial

abbrev Layers := List Sparse

def addLayers : Layers → Layers → Layers
  | [], q => q
  | p, [] => p
  | a::p, b::q => add a b :: addLayers p q

def mulLayers (p q : Layers) : Layers :=
  p.foldr (fun a acc => addLayers (q.map (mul a)) ([]::acc)) []

def negLayers (p : Layers) : Layers := p.map neg

def checkLayer (p : Layers) (n : ℕ) : Bool := checkZero (p[n]?.getD [])

section Soundness
variable {R : Type*} [CommRing R] [CharP R 109]

def evalLayers (x : Fin 5 → R) (z : R) : Layers → R
  | [] => 0
  | a::p => eval x a + z * evalLayers x z p

theorem eval_addLayers (x : Fin 5 → R) (z : R) (p q : Layers) :
    evalLayers x z (addLayers p q) = evalLayers x z p + evalLayers x z q := by
  induction p generalizing q with
  | nil => simp [addLayers, evalLayers]
  | cons a p ih =>
    cases q with
    | nil => simp [addLayers, evalLayers]
    | cons b q => simp only [addLayers, evalLayers, eval_add, ih]; ring

theorem eval_scaleLayers (x : Fin 5 → R) (z : R) (a : Sparse) (q : Layers) :
    evalLayers x z (q.map (mul a)) = eval x a * evalLayers x z q := by
  induction q with
  | nil => simp [evalLayers]
  | cons b q ih => simp only [List.map_cons, evalLayers, eval_mul, ih]; ring

theorem eval_mulLayers (x : Fin 5 → R) (z : R) (p q : Layers) :
    evalLayers x z (mulLayers p q) = evalLayers x z p * evalLayers x z q := by
  induction p with
  | nil => simp [mulLayers, evalLayers]
  | cons a p ih =>
    change evalLayers x z (addLayers (q.map (mul a)) ([]::mulLayers p q)) = _
    rw [eval_addLayers, eval_scaleLayers, evalLayers, eval_nil, ih, evalLayers]
    ring

theorem eval_negLayers (x : Fin 5 → R) (z : R) (p : Layers) :
    evalLayers x z (negLayers p) = -evalLayers x z p := by
  induction p with
  | nil => simp [negLayers, evalLayers]
  | cons a p ih =>
    change eval x (neg a) + z * evalLayers x z (negLayers p) = _
    rw [eval_neg, ih, evalLayers]
    ring

/-- Separate checked coefficient blocks imply the whole polynomial identity.
The bound concerns only the list of Horner blocks, never an arithmetic rank. -/
theorem evalLayers_eq_zero_of_checks (x : Fin 5 → R) (z : R) (N : ℕ) (p : Layers)
    (hlen : p.length ≤ N) (h : ∀ n : Fin N, checkLayer p n = true) :
    evalLayers x z p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalLayers]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have ha : checkZero a = true := by
        simpa only [checkLayer, Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using h 0
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hh : ∀ n : Fin N, checkLayer p n = true := by
        intro n
        simpa only [checkLayer, Fin.val_succ, List.getElem?_cons_succ] using h n.succ
      rw [evalLayers, eval_eq_zero_of_check x a ha, ih p hp hh, mul_zero, add_zero]

end Soundness
end CycleQ2SparseModularPolynomial

#print axioms CycleQ2SparseModularPolynomial.evalLayers_eq_zero_of_checks
#print axioms CycleQ2SparseModularPolynomial.eval_mulLayers
end


/- Component: continuation_3/cylinder_bridge/CechLiftRelation.lean -/
section
/-! # Linear descent for a two-stage Čech lifting relation

The simultaneous lifts form a linear submodule. Surjectivity of its first
projection and the actual boundary criterion induce an injection between
the two cohomology quotients, independently of any chosen lifts.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CechLiftRelation

variable {R P F C X G : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup F] [Module R F]
  [AddCommGroup C] [Module R C] [AddCommGroup X] [Module R X]
  [AddCommGroup G] [Module R G]

variable (u : P →ₗ[R] X) (v : F →ₗ[R] X) (d : F →ₗ[R] G) (g : C →ₗ[R] G)

def lifts : Submodule R (P × F × C) where
  carrier L := v L.2.1=u L.1 ∧ d L.2.1=g L.2.2
  zero_mem' := by
    change v 0=u 0 ∧ d 0=g 0
    simp only [map_zero,and_self]
  add_mem' {L M} hL hM := by
    constructor
    · change v (L.2.1+M.2.1)=u (L.1+M.1)
      rw [map_add,map_add,hL.1,hM.1]
    · change d (L.2.1+M.2.1)=g (L.2.2+M.2.2)
      rw [map_add,map_add,hL.2,hM.2]
  smul_mem' a L hL := by
    constructor
    · change v (a • L.2.1)=u (a • L.1)
      rw [map_smul,map_smul,hL.1]
    · change d (a • L.2.1)=g (a • L.2.2)
      rw [map_smul,map_smul,hL.2]

def firstProjection : lifts u v d g →ₗ[R] P :=
  (LinearMap.fst R P (F×C)).comp (lifts u v d g).subtype

def lastProjection : lifts u v d g →ₗ[R] C :=
  (LinearMap.snd R F C).comp
    ((LinearMap.snd R P (F×C)).comp (lifts u v d g).subtype)

variable (K : Submodule R P) (H : Submodule R C)

def topClass : lifts u v d g →ₗ[R] C ⧸ H :=
  H.mkQ.comp (lastProjection u v d g)

variable (hex : ∀ p : P, ∃ f c, v f=u p ∧ d f=g c)
  (hzero : ∀ p f c, v f=u p → d f=g c → (c∈H ↔ p∈K))

include hex in
theorem firstProjection_surjective : Function.Surjective (firstProjection u v d g) := by
  intro p
  obtain ⟨f,c,hf,hc⟩ := hex p
  exact ⟨⟨(p,f,c),hf,hc⟩,rfl⟩

include hzero in
theorem ker_firstProjection_le :
    LinearMap.ker (firstProjection u v d g) ≤ LinearMap.ker (topClass u v d g H) := by
  intro L hL
  change H.mkQ L.val.2.2=0
  change (Submodule.Quotient.mk L.val.2.2 : C ⧸ H)=0
  rw [Submodule.Quotient.mk_eq_zero]
  apply (hzero L.val.1 L.val.2.1 L.val.2.2 L.property.1 L.property.2).mpr
  have hz : L.val.1=0 := hL
  rw [hz]
  exact K.zero_mem

def connecting : P →ₗ[R] C ⧸ H :=
  CycleQ2CechLinearAlgebra.descendSurjective
    (firstProjection u v d g) (topClass u v d g H)
    (ker_firstProjection_le u v d g K H hzero)
    (firstProjection_surjective u v d g hex)

theorem connecting_apply (p : P) (f : F) (c : C)
    (hf : v f=u p) (hc : d f=g c) :
    connecting u v d g K H hex hzero p=H.mkQ c := by
  exact CycleQ2CechLinearAlgebra.descendSurjective_apply
    (firstProjection u v d g) (topClass u v d g H)
    (ker_firstProjection_le u v d g K H hzero)
    (firstProjection_surjective u v d g hex) ⟨(p,f,c),hf,hc⟩

theorem ker_connecting : LinearMap.ker (connecting u v d g K H hex hzero)=K := by
  ext p
  change connecting u v d g K H hex hzero p=0 ↔ p∈K
  obtain ⟨f,c,hf,hc⟩ := hex p
  rw [connecting_apply u v d g K H hex hzero p f c hf hc]
  change (Submodule.Quotient.mk c : C ⧸ H)=0 ↔ p∈K
  rw [Submodule.Quotient.mk_eq_zero]
  exact hzero p f c hf hc

def quotientInjection : (P ⧸ K) →ₗ[R] (C ⧸ H) :=
  CycleQ2LinearRangeDescent.kernelQuotientInjection
    (connecting u v d g K H hex hzero) K (ker_connecting u v d g K H hex hzero)

theorem quotientInjection_injective :
    Function.Injective (quotientInjection u v d g K H hex hzero) :=
  CycleQ2LinearRangeDescent.kernelQuotientInjection_injective
    (connecting u v d g K H hex hzero) K (ker_connecting u v d g K H hex hzero)

end CycleQ2CechLiftRelation

#print axioms CycleQ2CechLiftRelation.quotientInjection_injective
end
end


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


theorem smoothH_leading_coefficient (ι : R) :
    (smoothH ι).coeff (Finsupp.single 0 3) = 1 := by
  simp only [smoothH, smoothB, smoothA, coeff_sub, coeff_add, coeff_C_mul,
    X_pow_eq_monomial]
  simp only [X, monomial_mul, coeff_monomial]
  have h3 : (Finsupp.single (3 : Fin 5) 3 : FullExponent) ≠ Finsupp.single 0 3 := by
    intro he
    have h0 := congrArg (fun e : FullExponent ↦ e 0) he
    have h30 : (3 : Fin 5) ≠ 0 := by decide
    rw [Finsupp.single_eq_of_ne' h30, Finsupp.single_eq_same] at h0
    omega
  simp only [if_neg h3]
  norm_num [Finsupp.ext_iff, Fin.forall_fin_succ]

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

theorem smoothF_leading_coefficient (r ι : R) :
    (smoothF r ι).coeff (Finsupp.single 4 3) = 1 := by
  have hprod : (smoothH ι * smoothK ι).IsWeightedHomogeneous wOnly 0 :=
    (smoothB_no_w.sub (smoothA_no_w.C_mul ι)).mul
      (smoothB_no_w.add (smoothA_no_w.C_mul ι))
  have h0 := wOnly_X (R := R) 0 (by decide)
  have h1 := wOnly_X (R := R) 1 (by decide)
  have h2 := wOnly_X (R := R) 2 (by decide)
  have h3 := wOnly_X (R := R) 3 (by decide)
  have hpart : IsWeightedHomogeneous wOnly
      ((X 0 : Poly R)^6 - (C r)^3 * X 1^3 * X 3^3 + X 2^6) 0 :=
    ((h0.pow 6).sub ((((isWeightedHomogeneous_C wOnly r).pow 3).mul
      (h1.pow 3)).mul (h3.pow 3))).add (h2.pow 6)
  rw [smoothF, coeff_add, hprod.coeff_eq_zero _ wOnly_leading_ne, add_zero,
    seedG, CycleQ2SegreSeed.seedG_expanded, coeff_add,
    hpart.coeff_eq_zero _ wOnly_leading_ne, zero_add, coeff_X_pow, if_pos rfl]


theorem seedCubicCoefficients_unit (ι : R) :
    IsUnit (seedCubicCoefficients ι fullCubicLeadingIndex) := by
  have he := fullCubicLeadingIndex_exponent
  simpa only [seedCubicCoefficients, he, smoothH_leading_coefficient] using (isUnit_one : IsUnit (1 : R))

theorem seedSexticCoefficients_unit (r ι : R) :
    IsUnit (seedSexticCoefficients r ι fullSexticLeadingIndex) := by
  have he := fullSexticLeadingIndex_exponent
  simpa only [seedSexticCoefficients, he, smoothF_leading_coefficient] using (isUnit_one : IsUnit (1 : R))

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


/- Component: continuation_3/PointedOpenLifting.lean -/
section
/-! A generic solution on a prescribed polynomial open, chosen on a
component through the actual nonsingular seed.  The field quotient and
coordinates are those of the same Jacobian-localized open-square system
used by the original lifting construction. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PointedOpenLifting

open MvPolynomial HoldoutConstruction CycleQ2OpenSquareLifting
  CycleQ2PointedSquareGeneric

variable {R K T ι : Type*} [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field T] [Algebra R T] [Fintype ι] [DecidableEq ι]

theorem square_system_pointed_lift_on_open
    (e : ι → MvPolynomial ι R) (c : MvPolynomial ι R)
    (seed : ι → T) (he : ∀i,aeval seed (e i)=0)
    (hj : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (e j)))))
    (hc : IsUnit (aeval seed c)) :
    ∃ I : Ideal (SquareGenericAlgebra K (openSystem e c)), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K (openSystem e c)) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K (openSystem e c)) ⧸ I) ∧
      ∃ x : ι → ((SquareGenericAlgebra K (openSystem e c)) ⧸ I),
        (∀i,aeval x (e i)=0) ∧ IsUnit (aeval x c) ∧
        (∀p : MvPolynomial ι R,aeval x p=0 → aeval seed p=0) := by
  obtain ⟨u,hu⟩ := hc.exists_left_inv
  have haug := openSystem_seed e c seed u he hu
  have hjaug : IsUnit (Matrix.det (fun i j =>
      aeval (extendedPoint seed u) (pderiv i (openSystem e c j)))) := by
    rw [openSystem_jacobian_det]
    exact hc.mul hj
  obtain ⟨I,hmax,hfin,hsep,hpoint,hsol,hjac,hspecializes⟩ :=
    exists_pointed_square_fieldFactor (K := K) (openSystem e c)
      (extendedPoint seed u) haug hjaug
  let z := squareGenericCoordinates (openSystem e c) I
  let x : ι → ((SquareGenericAlgebra K (openSystem e c)) ⧸ I) :=
    fun i => z (Sum.inr i)
  have hx := solution_on_open e c z hsol
  refine ⟨I,hmax,hfin,hsep,x,hx.1,hx.2,?_⟩
  intro p hp
  have hp' : aeval z (rename (Sum.inr : ι → Unit ⊕ ι) p)=0 := by
    rw [aeval_rename]
    exact hp
  have hs := hspecializes (rename (Sum.inr : ι → Unit ⊕ ι) p) hp'
  rwa [aeval_extended_rename] at hs

end CycleQ2PointedOpenLifting

#print axioms CycleQ2PointedOpenLifting.square_system_pointed_lift_on_open
end
end


/- Component: continuation_3/cylinder_bridge/PolynomialImplicitTrace.lean -/
section
/-! The implicit trace numerator is a literal polynomial in the original
parameters.  At a compatible seed and a trace-one kernel direction it has
value one.  On a genuine differentiated solution, its being a unit forces
the fixed linear trace of that derivative to be a unit. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialImplicitTrace
open Matrix MvPolynomial CycleQ2PolynomialAffineSlice
  CycleQ2PolynomialDerivationChainRule CycleQ2ImplicitTraceNumerator

variable {R S σ m ι : Type*} [CommRing R] [CommRing S]
  [Fintype σ] [Fintype m] [Fintype ι] [DecidableEq ι]

def polynomialJacobian (e : m → MvPolynomial σ R) : Matrix m σ (MvPolynomial σ R) :=
  fun q k => pderiv k (e q)

def retainedJacobian (P : Matrix ι m R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) : Matrix ι ι (MvPolynomial σ R) :=
  P.map C * polynomialJacobian e * B.map C

def directionDerivative (P : Matrix ι m R) (direction : σ → R)
    (e : m → MvPolynomial σ R) : ι → MvPolynomial σ R :=
  (P.map C * polynomialJacobian e) *ᵥ (C ∘ direction)

def tracePolynomial (P : Matrix ι m R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) (weights direction : σ → R) : MvPolynomial σ R :=
  traceNumerator (retainedJacobian P B e) (directionDerivative P direction e)
    (C ∘ weights) (C ∘ direction) (B.map C)

theorem eval_polynomialJacobian (φ : R →+* S) (x : σ → S)
    (e : m → MvPolynomial σ R) :
    (polynomialJacobian e).map (eval₂Hom φ x)=jacobian φ x e := rfl

theorem eval_retainedJacobian (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R) :
    (retainedJacobian P B e).map (eval₂Hom φ x)=
      P.map φ * jacobian φ x e * B.map φ := by
  simp only [retainedJacobian,Matrix.map_mul,eval_polynomialJacobian,Matrix.map_map,
    Function.comp_def,eval₂Hom_C]

theorem eval_directionDerivative (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (direction : σ → R) (e : m → MvPolynomial σ R) :
    (eval₂Hom φ x) ∘ directionDerivative P direction e =
      (P.map φ * jacobian φ x e) *ᵥ (φ ∘ direction) := by
  funext i
  simp only [directionDerivative,Function.comp_apply,RingHom.map_mulVec,
    Matrix.map_mul,eval_polynomialJacobian,Matrix.map_map,Function.comp_def,eval₂Hom_C]

theorem eval_tracePolynomial (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R) :
    eval₂Hom φ x (tracePolynomial P B e weights direction) =
      traceNumerator (P.map φ * jacobian φ x e * B.map φ)
        ((P.map φ * jacobian φ x e) *ᵥ (φ ∘ direction))
        (φ ∘ weights) (φ ∘ direction) (B.map φ) := by
  rw [tracePolynomial,traceNumerator_map,eval_retainedJacobian,eval_directionDerivative]
  simp only [Function.comp_def,eval₂Hom_C,Matrix.map_map]

theorem seed_tracePolynomial_one (φ : R →+* S) (x : σ → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R)
    (hJ : P.map φ * jacobian φ x e * B.map φ=1)
    (hkernel : jacobian φ x e *ᵥ (φ ∘ direction)=0)
    (htrace : (φ ∘ weights) ⬝ᵥ (φ ∘ direction)=1) :
    eval₂Hom φ x (tracePolynomial P B e weights direction)=1 := by
  rw [eval_tracePolynomial,hJ,← mulVec_mulVec,hkernel,mulVec_zero]
  exact traceNumerator_seed _ _ _ htrace

theorem derivative_trace_isUnit [Algebra R S]
    (D : Derivation R S S) (x : σ → S) (z : ι → S)
    (P : Matrix ι m R) (B : Matrix σ ι R) (e : m → MvPolynomial σ R)
    (weights direction : σ → R)
    (he : ∀ q, aeval x (e q)=0)
    (hder : ∀ k, D (x k)=algebraMap R S (direction k)+
      (B.map (algebraMap R S) *ᵥ (fun j => D (z j))) k)
    (hN : IsUnit (aeval x (tracePolynomial P B e weights direction))) :
    IsUnit ((algebraMap R S ∘ weights) ⬝ᵥ (fun k => D (x k))) := by
  have hu := implicit_derivative_relation D x z P B ((algebraMap R S) ∘ direction) e he hder
  change IsUnit (eval₂Hom (algebraMap R S) x (tracePolynomial P B e weights direction)) at hN
  rw [eval_tracePolynomial] at hN
  have ht := trace_isUnit_of_numerator_isUnit
    (P.map (algebraMap R S) * jacobian (algebraMap R S) x e * B.map (algebraMap R S))
    ((P.map (algebraMap R S) * jacobian (algebraMap R S) x e) *ᵥ ((algebraMap R S) ∘ direction))
    (fun j => D (z j)) ((algebraMap R S) ∘ weights) ((algebraMap R S) ∘ direction)
    (B.map (algebraMap R S)) hu hN
  have hx : (fun k => D (x k))=((algebraMap R S) ∘ direction)+
      B.map (algebraMap R S) *ᵥ (fun j => D (z j)) := funext hder
  rw [hx]
  exact ht

end CycleQ2PolynomialImplicitTrace

#print axioms CycleQ2PolynomialImplicitTrace.seed_tracePolynomial_one
#print axioms CycleQ2PolynomialImplicitTrace.derivative_trace_isUnit
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechFractions.lean -/
section
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

def powerCoordinates (r : ℂ) (e : Bool) : Fin 4 → PowerChart r e :=
  ![x0 (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e),
    base (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e) (endpointX e),
    x2 (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e),
    base (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e) (endpointY e)]

def powerEval (r : ℂ) (e : Bool) : Poly →+* PowerChart r e :=
  MvPolynomial.eval₂Hom
    ((base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e)).comp PowerSeries.C)
    (powerCoordinates r e)

def laurentEval (r : ℂ) (e : Bool) : Poly →+* LaurentChart r e :=
  (chartEmbedding r e).comp (powerEval r e)

@[simp] theorem powerCoordinates_zero (r : ℂ) (e : Bool) :
    powerCoordinates r e 0 = x0 (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) := rfl
@[simp] theorem powerCoordinates_one (r : ℂ) (e : Bool) :
    powerCoordinates r e 1 = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (endpointX e) := rfl
@[simp] theorem powerCoordinates_two (r : ℂ) (e : Bool) :
    powerCoordinates r e 2 = x2 (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) := rfl
@[simp] theorem powerCoordinates_three (r : ℂ) (e : Bool) :
    powerCoordinates r e 3 = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (endpointY e) := rfl

@[simp] theorem powerEval_X (r : ℂ) (e : Bool) (j : Fin 4) :
    powerEval r e (X j) = powerCoordinates r e j := by simp [powerEval]

@[simp] theorem powerEval_C (r : ℂ) (e : Bool) (c : ℂ) :
    powerEval r e (C c) = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (PowerSeries.C c) := by simp [powerEval]

theorem powerEval_curveF1 (r : ℂ) (e : Bool) : powerEval r e (curveF1 r) = 0 := by
  simp only [curveF1, relation, Matrix.cons_val_zero, map_sub, map_mul, map_pow,
    powerEval_X, powerEval_C, powerCoordinates_zero, powerCoordinates_one, powerCoordinates_three]
  rw [x0_sq, sub_eq_zero]
  simp [map_mul]

theorem powerEval_curveH (r : ℂ) (e : Bool) : powerEval r e curveH = 0 := by
  have h2 := x2_cubic (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e)
  simp only [map_sub, map_mul, map_pow, map_one] at h2
  simp only [curveH, h, b, map_sub, map_add, map_mul, map_pow,
    powerEval_X, powerEval_C, powerCoordinates_zero, powerCoordinates_one,
    powerCoordinates_two, powerCoordinates_three]
  linear_combination h2

theorem powerEval_zero_of_curveIdeal (r : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r) : powerEval r e p = 0 := by
  obtain ⟨u,v,hp⟩ := Ideal.mem_span_pair.mp hp
  rw [← hp, map_add, map_mul, map_mul, powerEval_curveF1, powerEval_curveH]
  ring

theorem laurentEval_zero_of_curveIdeal (r : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r) : laurentEval r e p = 0 := by
  change chartEmbedding r e (powerEval r e p) = 0
  rw [powerEval_zero_of_curveIdeal r e hp, map_zero]


theorem uniformizer_ne_zero : seriesMap (PowerSeries.X : PS) ≠ 0 := by
  intro hh
  have hc := congrArg (fun f : LS => f.coeff 1) hh
  simpa [seriesMap, HahnSeries.ofPowerSeries_X] using hc

def uniformizerUnit : LSˣ := Units.mk0 _ uniformizer_ne_zero

def chartAUnit (r : ℂ) (e : Bool) : (LaurentChart r e)ˣ :=
  Units.map (base (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))) uniformizerUnit

theorem laurentEval_curveA (r : ℂ) (e : Bool) :
    laurentEval r e curveA = (chartAUnit r e : LaurentChart r e) := by
  have hp : powerEval r e curveA = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) PowerSeries.X := by
    simp only [curveA, map_mul, powerEval_X, powerCoordinates_one, powerCoordinates_three]
    rw [← map_mul]
    congr 1
    cases e <;> simp [endpointX, endpointY]
  change chartEmbedding r e (powerEval r e curveA) = _
  rw [hp]
  exact curveMap_base seriesMap _ _ _ _ _

theorem laurentEval_curveB (r : ℂ) (e : Bool) :
    laurentEval r e curveB = (laurentX2Unit r e : LaurentChart r e) := by
  change chartEmbedding r e (powerEval r e (X 2)) =
    chartEmbedding r e (powerX2Unit r e : PowerChart r e)
  congr 1
  simp only [powerEval_X, powerCoordinates_two, powerX2Unit, coe_x2Unit]

def fraction (r : ℂ) (e : Bool) (p : Poly) (n m : ℕ) : LaurentChart r e :=
  laurentEval r e p * ((chartAUnit r e)⁻¹ : (LaurentChart r e)ˣ) ^ n *
    ((laurentX2Unit r e)⁻¹ : (LaurentChart r e)ˣ) ^ m

def fractionResidue (r : ℂ) (e : Bool) (p : Poly) (n m : ℕ) : ℂ :=
  endpointResidue r e (fraction r e p n m)

def cechResidue (r : ℂ) (p : Poly) (n m : ℕ) : ℂ :=
  fractionResidue r false p n m - fractionResidue r true p n m

theorem fraction_add (r : ℂ) (e : Bool) (p q : Poly) (n m : ℕ) :
    fraction r e (p+q) n m = fraction r e p n m + fraction r e q n m := by
  simp [fraction, add_mul]

theorem fraction_sub (r : ℂ) (e : Bool) (p q : Poly) (n m : ℕ) :
    fraction r e (p-q) n m = fraction r e p n m - fraction r e q n m := by
  simp [fraction, sub_mul]

theorem cechResidue_add (r : ℂ) (p q : Poly) (n m : ℕ) :
    cechResidue r (p+q) n m = cechResidue r p n m + cechResidue r q n m := by
  simp only [cechResidue, fractionResidue, fraction_add, map_add]
  ring

theorem unit_pow_cancel {A : Type*} [CommRing A] (u : Aˣ) (n N : ℕ) (hn : n ≤ N) :
    (u : A) ^ (N-n) * ((u⁻¹ : Aˣ) : A) ^ N = ((u⁻¹ : Aˣ) : A) ^ n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, pow_add]
  calc
    _ = ((u : A) * ((u⁻¹ : Aˣ) : A)) ^ k * ((u⁻¹ : Aˣ) : A) ^ n := by
      rw [mul_pow]
      ring
    _ = _ := by simp

theorem fraction_change_denominator (r : ℂ) (e : Bool) (p : Poly)
    (n m N M : ℕ) (hn : n ≤ N) (hm : m ≤ M) :
    fraction r e (p * curveA ^ (N-n) * curveB ^ (M-m)) N M =
      fraction r e p n m := by
  unfold fraction
  simp only [map_mul, map_pow, laurentEval_curveA, laurentEval_curveB]
  calc
    _ = laurentEval r e p *
        (((chartAUnit r e : (LaurentChart r e)ˣ) : LaurentChart r e) ^ (N-n) *
          (((chartAUnit r e)⁻¹ : (LaurentChart r e)ˣ) : LaurentChart r e) ^ N) *
        (((laurentX2Unit r e : (LaurentChart r e)ˣ) : LaurentChart r e) ^ (M-m) *
          (((laurentX2Unit r e)⁻¹ : (LaurentChart r e)ˣ) : LaurentChart r e) ^ M) := by ring
    _ = _ := by rw [unit_pow_cancel _ n N hn, unit_pow_cancel _ m M hm]

theorem fraction_first_open_term (r : ℂ) (e : Bool) (p : Poly) (N M : ℕ) :
    fraction r e (p * curveA^N) N M = fraction r e p 0 M := by
  simpa using fraction_change_denominator r e p 0 M N M (Nat.zero_le _) le_rfl

theorem fraction_second_open_term (r : ℂ) (e : Bool) (p : Poly) (N M : ℕ) :
    fraction r e (p * curveB^M) N M = fraction r e p N 0 := by
  simpa using fraction_change_denominator r e p N 0 N M le_rfl (Nat.zero_le _)

theorem fractionResidue_x2_open (r : ℂ) (e : Bool) (p : Poly) (m : ℕ) :
    fractionResidue r e p 0 m = 0 := by
  simpa [fractionResidue, fraction, laurentEval] using
    endpointResidue_x2_open r e (powerEval r e p) m

theorem cechResidue_x2_open (r : ℂ) (p : Poly) (m : ℕ) : cechResidue r p 0 m = 0 := by
  simp [cechResidue, fractionResidue_x2_open]

theorem fraction_zero_of_curveIdeal (r : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r) (n m : ℕ) : fraction r e p n m = 0 := by
  simp [fraction, laurentEval_zero_of_curveIdeal r e hp]

/-- Exact denominator-clearing definition of the degree-one Čech coboundaries
for the cover D₊(x₁x₃), D₊(x₂) of the projective sparse curve.  The two numerator
degrees enforce sections of its canonical bundle O(1). -/
def CechBoundary (r : ℂ) (p : Poly) (n m : ℕ) : Prop :=
  ∃ N M q s, n ≤ N ∧ m ≤ M ∧ q.IsHomogeneous (M + 1) ∧
    s.IsHomogeneous (2 * N + 1) ∧
    p * curveA ^ (N - n) * curveB ^ (M - m) -
      (q * curveA ^ N + s * curveB ^ M) ∈ curveIdeal r

/-- Clearing arbitrary powers gives exactly the same two endpoint values as
the sum of the two single-open cochains. -/
theorem fraction_of_boundary_witness (r : ℂ) (e : Bool) (p q s : Poly)
    (n m N M : ℕ) (hn : n ≤ N) (hm : m ≤ M)
    (hmem : p * curveA^(N-n) * curveB^(M-m) -
      (q * curveA^N + s * curveB^M) ∈ curveIdeal r) :
    fraction r e p n m = fraction r e q 0 M + fraction r e s N 0 := by
  have hz := fraction_zero_of_curveIdeal r e hmem N M
  rw [fraction_sub, fraction_add, fraction_change_denominator r e p n m N M hn hm,
    fraction_first_open_term, fraction_second_open_term, sub_eq_zero] at hz
  exact hz

end CycleQ2SeedCech
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechGeneralCubic.lean -/
section
/-! A monic cubic over the actual quadratic curve algebra, allowing an
arbitrary coefficient of x₀ in the constant term.  This covers the whole
family h+θx₀³ after reduction modulo x₀²-rx₁x₃. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2CechLinearCubic
open Polynomial CycleQ2SeedCech
variable {R S : Type*} [CommRing R] [CommRing S]

def cubic (r i x y q : R) : (Quadratic r x y)[X] :=
  X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ q +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))

theorem cubic_monic (r i x y q : R) : (cubic r i x y q).Monic := by
  unfold cubic
  rw [add_assoc]
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (degree_mul_le _ _)
    calc
      _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
      _ < (3 : WithBot ℕ) := by norm_num
  · exact lt_of_le_of_lt degree_C_le (by norm_num)

abbrev CurveAlgebra (r i x y q : R) := AdjoinRoot (cubic r i x y q)

def x0 (r i x y q : R) : CurveAlgebra r i x y q :=
  algebraMap (Quadratic r x y) _ (a r x y)

def x2 (r i x y q : R) : CurveAlgebra r i x y q := AdjoinRoot.root _

def base (r i x y q : R) : R →+* CurveAlgebra r i x y q :=
  (algebraMap (Quadratic r x y) _).comp (algebraMap R _)

theorem x0_sq (r i x y q : R) : x0 r i x y q ^ 2 = base r i x y q (r * x * y) := by
  rw [x0, ← map_pow, a_sq]
  rfl

theorem x2_cubic (r i x y q : R) :
    x2 r i x y q ^ 3 + (x0 r i x y q + base r i x y q x) *
        base r i x y q y * x2 r i x y q +
      x0 r i x y q * base r i x y q q +
        base r i x y q ((1 - i) * y ^ 3 - i * x ^ 3) = 0 := by
  have hh := AdjoinRoot.mk_self (f := cubic r i x y q)
  change AdjoinRoot.mk (cubic r i x y q)
    (X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
      C (a r x y * algebraMap R _ q +
        algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))) = 0 at hh
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  simpa only [x0, x2, base, RingHom.comp_apply, AdjoinRoot.algebraMap_eq,
    map_pow, add_assoc] using hh

def coefficient (r i x y q : R) : CurveAlgebra r i x y q →ₗ[R] R :=
  (Polynomial.lcoeff R 1).comp
    ((AdjoinRoot.modByMonicHom (quadratic_monic r x y)).comp
      (((Polynomial.lcoeff (Quadratic r x y) 2).comp
        (AdjoinRoot.modByMonicHom (cubic_monic r i x y q))).restrictScalars R))

theorem cubic_map (f : R →+* S) (r i x y q : R) :
    (cubic r i x y q).map (quadraticMap f r x y) =
      cubic (f r) (f i) (f x) (f y) (f q) := by
  simp [cubic]

def curveMap (f : R →+* S) (r i x y q : R) :
    CurveAlgebra r i x y q →+* CurveAlgebra (f r) (f i) (f x) (f y) (f q) :=
  AdjoinRoot.map (quadraticMap f r x y) _ _
    (by rw [cubic_map])

@[simp] theorem curveMap_x0 (f : R →+* S) (r i x y q : R) :
    curveMap f r i x y q (x0 r i x y q) = x0 (f r) (f i) (f x) (f y) (f q) := by
  simp [curveMap, x0, AdjoinRoot.algebraMap_eq]

@[simp] theorem curveMap_x2 (f : R →+* S) (r i x y q : R) :
    curveMap f r i x y q (x2 r i x y q) = x2 (f r) (f i) (f x) (f y) (f q) := by
  simp [curveMap, x2]

@[simp] theorem curveMap_base (f : R →+* S) (r i x y q z : R) :
    curveMap f r i x y q (base r i x y q z) = base (f r) (f i) (f x) (f y) (f q) (f z) := by
  simp [curveMap, base, AdjoinRoot.algebraMap_eq]

@[simp] theorem coefficient_curveMap (f : R →+* S) (r i x y q : R)
    (z : CurveAlgebra r i x y q) :
    coefficient (f r) (f i) (f x) (f y) (f q) (curveMap f r i x y q z) =
      f (coefficient r i x y q z) := by
  change ((AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
    (((AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y) (f q)))
      (curveMap f r i x y q z)).coeff 2)).coeff 1 =
    f (((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
      (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).coeff 2)).coeff 1)
  rw [show (AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y) (f q)))
      (curveMap f r i x y q z) =
      ((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).map
        (quadraticMap f r x y) from
    modByMonicHom_map_eq _ _ _ (cubic_monic r i x y q)
      (cubic_monic (f r) (f i) (f x) (f y) (f q)) (cubic_map f r i x y q) z]
  rw [coeff_map]
  rw [show (AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
      (quadraticMap f r x y
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).coeff 2)) =
      ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).coeff 2)).map f from
    modByMonicHom_map_eq _ _ _ (quadratic_monic r x y)
      (quadratic_monic (f r) (f x) (f y)) (quadratic_map f r x y) _]
  rw [coeff_map]

def norm (r i x y q : R) : R :=
  ((1 - i) * y ^ 3 - i * x ^ 3) ^ 2 - r * x * y * q ^ 2

def inverseNumerator (r i x y q : R) : CurveAlgebra r i x y q :=
  -(x2 r i x y q ^ 2 + (x0 r i x y q + base r i x y q x) * base r i x y q y) *
    (base r i x y q ((1 - i) * y ^ 3 - i * x ^ 3) -
      x0 r i x y q * base r i x y q q)

/-- An explicit inverse numerator for x₂; no irreducibility or smoothness is
needed.  The only scalar denominator is the displayed binary sextic. -/
theorem x2_mul_inverseNumerator (r i x y q : R) :
    x2 r i x y q * inverseNumerator r i x y q = base r i x y q (norm r i x y q) := by
  have h0 := x0_sq r i x y q
  have h2 := x2_cubic r i x y q
  simp only [map_sub, map_mul, map_pow, map_one] at h0 h2 ⊢
  unfold inverseNumerator norm
  simp only [map_sub, map_mul, map_pow, map_one]
  linear_combination
    -((1 - base r i x y q i) * base r i x y q y ^ 3 -
      base r i x y q i * base r i x y q x ^ 3 -
      x0 r i x y q * base r i x y q q) * h2 -
    base r i x y q q ^ 2 * h0

def x2Unit (r i x y q : R) (u : Rˣ) (hu : (u : R) = norm r i x y q) :
    (CurveAlgebra r i x y q)ˣ where
  val := x2 r i x y q
  inv := inverseNumerator r i x y q * base r i x y q (↑(u⁻¹) : R)
  val_inv := by
    rw [← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp
  inv_val := by
    rw [mul_comm, ← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp

@[simp] theorem coe_x2Unit (r i x y q : R) (u : Rˣ) (hu : (u : R) = norm r i x y q) :
    (x2Unit r i x y q u hu : CurveAlgebra r i x y q) = x2 r i x y q := rfl

variable [Nontrivial R]

theorem cubic_degree (r i x y q : R) : (cubic r i x y q).degree = 3 := by
  unfold cubic
  rw [add_assoc]
  have hl : (C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ q +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))).degree < 3 := by
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  rw [degree_add_eq_left_of_degree_lt (by simpa using hl)]
  simp

theorem coefficient_small_monomial (r i x y q z : R) (j k : ℕ)
    (hj : j < 2) (hk : k < 3) :
    coefficient r i x y q (base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k) =
      if j = 1 ∧ k = 2 then z else 0 := by
  have hc : AdjoinRoot.modByMonicHom (cubic_monic r i x y q)
      (base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k) =
      C (algebraMap R (Quadratic r x y) z * a r x y ^ j) * X ^ k := by
    have heq : base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k =
        AdjoinRoot.mk (cubic r i x y q)
          (C (algebraMap R (Quadratic r x y) z * a r x y ^ j) * X ^ k) := by
      simp [base, x0, x2, AdjoinRoot.algebraMap_eq]
    rw [heq, AdjoinRoot.modByMonicHom_mk]
    apply (modByMonic_eq_self_iff (cubic_monic r i x y q)).mpr
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by
      rw [cubic_degree]
      exact_mod_cast hk)
  have hq : AdjoinRoot.modByMonicHom (quadratic_monic r x y)
      (algebraMap R (Quadratic r x y) z * a r x y ^ j) = C z * X ^ j := by
    have heq : algebraMap R (Quadratic r x y) z * a r x y ^ j =
        AdjoinRoot.mk (quadratic r x y) (C z * X ^ j) := by
      simp [a, AdjoinRoot.algebraMap_eq]
    rw [heq, AdjoinRoot.modByMonicHom_mk]
    apply (modByMonic_eq_self_iff (quadratic_monic r x y)).mpr
    apply lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
    rw [quadratic, degree_X_pow_sub_C (by decide)]
    exact_mod_cast hj
  change ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
    (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q))
      (base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k)).coeff 2)).coeff 1 = _
  rw [hc]
  simp only [coeff_C_mul_X_pow]
  by_cases hk2 : k = 2
  · subst k
    simp only [ite_true, hq, coeff_C_mul_X_pow]
    simp [eq_comm]
  · simp [hk2, eq_comm]

theorem coefficient_base_mul (r i x y q z : R) (v : CurveAlgebra r i x y q) :
    coefficient r i x y q (base r i x y q z * v) = z * coefficient r i x y q v := by
  unfold base
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R
    (Quadratic r x y) (CurveAlgebra r i x y q)]
  simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
    (coefficient r i x y q).map_smul z v

end CycleQ2CechLinearCubic

#print axioms CycleQ2CechLinearCubic.x2_mul_inverseNumerator
#print axioms CycleQ2CechLinearCubic.coefficient_small_monomial
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechJets.lean -/
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open TrivSqZeroExt

abbrev Jet := TrivSqZeroExt ℂ ℂ

def firstJet : PS →+* Jet where
  toFun f := (PowerSeries.constantCoeff f, PowerSeries.coeff 1 f)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' f g := by apply TrivSqZeroExt.ext <;> simp
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [PowerSeries.coeff_one_mul, smul_eq_mul, op_smul_eq_smul]
      ring

@[simp] theorem firstJet_fst (f : PS) : (firstJet f).fst = PowerSeries.constantCoeff f := rfl
@[simp] theorem firstJet_snd (f : PS) : (firstJet f).snd = PowerSeries.coeff 1 f := rfl

theorem firstJet_X_sq : firstJet (PowerSeries.X : PS) ^ 2 = 0 := by
  apply TrivSqZeroExt.ext <;> simp [firstJet, pow_two, smul_eq_mul, op_smul_eq_smul]

theorem firstJet_I_sq : firstJet (PowerSeries.C Complex.I) ^ 2 = -1 := by
  rw [← map_pow, ← map_pow, Complex.I_sq, map_neg, map_one, map_neg, map_one]

/-- The finite second-order identity used to normalize the actual Čech
residue.  It is an identity in every commutative ring with the displayed four
relations; all coefficients are checked by `linear_combination`. -/
theorem inverse_fourth_jet_identity {A : Type*} [CommRing A]
    (a b t j r : A) (hb : b ^ 3 + (a+1)*t*b + a-j = 0)
    (ha : a ^ 2-r*t = 0) (ht : t^2=0) (hj : j^2+1=0) :
    b^4 * (-a*b^2 + 2*j*r*t*b^2 + 3*r*a*t*b^2 - 2*a*t) = a := by
  linear_combination
    (-3*a^2*b*r*t^2 + a^2*b*t - 3*a^2*r*t + a^2 +
      3*a*b^3*r*t - a*b^3 - 2*a*b*j*r*t^2 - 3*a*b*r*t^2 -
      a*b*t + a*j*r*t - a*j + 2*b^3*j*r*t - 2*b*j*r*t^2 +
      2*j^2*r*t) * hb +
    (3*a*b^2*r*t^3 - a*b^2*t^2 + 6*a*b*r*t^2 - 2*a*b*t +
      3*a*r*t - a + 2*b^2*j*r*t^3 + 6*b^2*r*t^3 -
      2*b*j*r*t^2 + 2*b*j*t + 6*b*r*t^2 - 4*j*r*t + 2*j) * ha +
    (4*a*b^2*j*r*t + 3*a*b^2*r^2*t^2 + 2*a*b^2*r*t + a*b^2 -
      4*a*b*j^2*r - 2*a*b*j*r + 6*a*b*r^2*t - 2*a*b*r +
      3*a*r^2 + 2*b^2*j*r^2*t^2 + 2*b^2*j*r*t + 6*b^2*r^2*t^2 -
      4*b*j^2*r - 2*b*j*r^2*t + 2*b*j*r + 6*b*r^2*t - 4*j*r^2) * ht +
    (-a*r*t - a + 2*j*r*t) * hj

abbrev JetChart (r : ℂ) (e : Bool) :=
  CurveAlgebra (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetEmbedding (r : ℂ) (e : Bool) : PowerChart r e →+* JetChart r e :=
  curveMap firstJet (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)

def jetX2Unit (r : ℂ) (e : Bool) : (JetChart r e)ˣ :=
  Units.map (jetEmbedding r e) (powerX2Unit r e)

def jetBase (r : ℂ) (e : Bool) : Jet →+* JetChart r e :=
  base (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetX0 (r : ℂ) (e : Bool) : JetChart r e :=
  x0 (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetX2 (r : ℂ) (e : Bool) : JetChart r e :=
  x2 (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetCoefficient (r : ℂ) (e : Bool) : JetChart r e →ₗ[Jet] Jet :=
  coefficient (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

@[simp] theorem coe_jetX2Unit (r : ℂ) (e : Bool) :
    (jetX2Unit r e : JetChart r e) = jetX2 r e := by
  simp [jetX2Unit, jetEmbedding, powerX2Unit, jetX2]

theorem false_jet_relations (r : ℂ) :
    let A := jetX0 r false
    let B := jetX2 r false
    let T := jetBase r false (firstJet PowerSeries.X)
    let J := jetBase r false (firstJet (PowerSeries.C Complex.I))
    let R := jetBase r false (firstJet (PowerSeries.C r))
    (B^3+(A+1)*T*B+A-J=0) ∧ (A^2-R*T=0) ∧ T^2=0 ∧ J^2+1=0 := by
  dsimp only
  have ht : (jetBase r false (firstJet PowerSeries.X)) ^ 2 = 0 := by
    rw [← map_pow, firstJet_X_sq, map_zero]
  have ht3 : (jetBase r false (firstJet PowerSeries.X)) ^ 3 = 0 := by
    rw [pow_succ, ht, zero_mul]
  refine ⟨?_, ?_, ht, ?_⟩
  · have hh := x2_cubic (firstJet (PowerSeries.C r))
      (firstJet (PowerSeries.C Complex.I)) (firstJet (endpointX false))
      (firstJet (endpointY false))
    change jetX2 r false ^ 3 +
      (jetX0 r false + jetBase r false (firstJet (endpointX false))) *
        jetBase r false (firstJet (endpointY false)) * jetX2 r false +
      jetX0 r false * jetBase r false ((firstJet (endpointX false)) ^ 2) +
      jetBase r false ((1-firstJet (PowerSeries.C Complex.I)) *
        (firstJet (endpointY false)) ^ 3 - firstJet (PowerSeries.C Complex.I) *
        (firstJet (endpointX false)) ^ 3) = 0 at hh
    simpa only [endpointX, endpointY, map_one, map_sub, map_mul, map_pow,
      one_pow, mul_one, ht3, mul_zero, zero_sub, sub_eq_add_neg, map_add, map_neg, zero_add] using hh
  · have hh := x0_sq (firstJet (PowerSeries.C r))
      (firstJet (PowerSeries.C Complex.I)) (firstJet (endpointX false))
      (firstJet (endpointY false))
    change jetX0 r false ^ 2 = jetBase r false
      (firstJet (PowerSeries.C r) * firstJet (endpointX false) *
        firstJet (endpointY false)) at hh
    simpa only [endpointX, endpointY, map_one, mul_one, map_mul, sub_eq_zero] using hh
  · rw [← map_pow, firstJet_I_sq, map_neg, map_one]
    ring

theorem false_jet_inverse_fourth (r : ℂ) :
    jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4 =
      -jetX0 r false * jetX2 r false ^ 2 +
      2 * jetBase r false (firstJet (PowerSeries.C Complex.I)) *
        jetBase r false (firstJet (PowerSeries.C r)) *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 +
      3 * jetBase r false (firstJet (PowerSeries.C r)) * jetX0 r false *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 -
      2 * jetX0 r false * jetBase r false (firstJet PowerSeries.X) := by
  obtain ⟨hb,ha,ht,hj⟩ := false_jet_relations r
  have hh := inverse_fourth_jet_identity _ _ _ _ _ hb ha ht hj
  let H : JetChart r false :=
    -jetX0 r false * jetX2 r false ^ 2 +
      2 * jetBase r false (firstJet (PowerSeries.C Complex.I)) *
        jetBase r false (firstJet (PowerSeries.C r)) *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 +
      3 * jetBase r false (firstJet (PowerSeries.C r)) * jetX0 r false *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 -
      2 * jetX0 r false * jetBase r false (firstJet PowerSeries.X)
  change jetX2 r false ^ 4 * H = jetX0 r false at hh
  change jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4 = H
  rw [← hh]
  calc
    _ = (jetX2 r false ^ 4 * (((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) :
      JetChart r false) ^ 4) * H := by ring
    _ = H := by
      rw [← coe_jetX2Unit, ← mul_pow]
      rw [(jetX2Unit r false).mul_inv, one_pow, one_mul]

theorem false_jet_coefficient (r : ℂ) :
    jetCoefficient r false
      (jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4) =
      -1 + 3 * firstJet (PowerSeries.C r) * firstJet PowerSeries.X := by
  rw [false_jet_inverse_fourth]
  let rr := firstJet (PowerSeries.C r)
  let ii := firstJet (PowerSeries.C Complex.I)
  let tt := firstJet (PowerSeries.X : PS)
  have heq :
      -jetX0 r false * jetX2 r false ^ 2 +
      2 * jetBase r false ii * jetBase r false rr * jetBase r false tt * jetX2 r false ^ 2 +
      3 * jetBase r false rr * jetX0 r false * jetBase r false tt * jetX2 r false ^ 2 -
      2 * jetX0 r false * jetBase r false tt =
      jetBase r false (-1 + 3*rr*tt) * jetX0 r false ^ 1 * jetX2 r false ^ 2 +
      jetBase r false (2*ii*rr*tt) * jetX0 r false ^ 0 * jetX2 r false ^ 2 +
      jetBase r false (-2*tt) * jetX0 r false ^ 1 * jetX2 r false ^ 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pow_zero, pow_one]
    ring
  rw [heq, map_add, map_add]
  unfold jetCoefficient jetBase jetX0 jetX2
  rw [coefficient_small_monomial _ _ _ _ _ 1 2 (by decide) (by decide),
    coefficient_small_monomial _ _ _ _ _ 0 2 (by decide) (by decide),
    coefficient_small_monomial _ _ _ _ _ 1 0 (by decide) (by decide)]
  simp [rr, tt]

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.inverse_fourth_jet_identity
#print axioms CycleQ2SeedCech.false_jet_coefficient
end
end


/- Component: continuation_3/cylinder_bridge/SlicedCompatibleSystem.lean -/
section
/-! The square subsystem, complementary relation determinant and prescribed
open after an affine parameter slice.  Both seed determinants are exactly
one whenever the compatible linear splitting has identity seed blocks. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SlicedCompatibleSystem
open MvPolynomial Matrix CycleQ2PolynomialAffineSlice CycleQ2CompatibleEquationCoordinates

variable {R S m l ι κ σ : Type*} [CommRing R] [CommRing S]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ] [Fintype σ]
  [DecidableEq m] [DecidableEq ι] [DecidableEq κ]

def equations (a : σ → R) (B : Matrix σ ι R) (P : Matrix ι m R)
    (e : m → MvPolynomial σ R) : ι → MvPolynomial ι R :=
  fun q => substitute a B (retained P e q)

def residual (a : σ → R) (B : Matrix σ ι R) (W : Matrix κ m R)
    (e : m → MvPolynomial σ R) : κ → MvPolynomial ι R :=
  fun q => substitute a B (retained W e q)

def relationA (a : σ → R) (B : Matrix σ ι R) (T : Matrix κ l R)
    (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R) :
    Matrix κ κ (MvPolynomial ι R) :=
  (complementary T D V).map (substitute a B)

def relationC (a : σ → R) (B : Matrix σ ι R) (T : Matrix κ l R)
    (D : Matrix l m (MvPolynomial σ R)) (Q : Matrix m ι R) :
    Matrix κ ι (MvPolynomial ι R) :=
  (crossBlock T D Q).map (substitute a B)

theorem relation_identity
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (h : Q*P+V*W=1) (e : m → MvPolynomial σ R) (he : D*ᵥe=0) :
    relationA a B T D V *ᵥ residual a B W e +
      relationC a B T D Q *ᵥ equations a B P e = 0 := by
  have hr := polynomial_relations P Q V W T D h e he
  funext q
  have hq := congrArg (substitute a B) (congrFun hr q)
  simpa only [relationA,relationC,equations,residual,Pi.add_apply,Pi.zero_apply,
    Matrix.mulVec,dotProduct,Matrix.map_apply,map_add,map_sum,map_mul,map_zero] using hq

theorem seed_equations_zero (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R)
    (he : ∀ q, eval₂Hom φ (φ ∘ a) (e q)=0) (q : ι) :
    eval₂Hom φ (0 : ι → S) (equations a B P e q)=0 := by
  rw [equations,eval_zero_substitute]
  have hev := congrFun (eval_retained φ (φ ∘ a) P e) q
  have hz : (fun k => eval₂Hom φ (φ ∘ a) (e k))=0 := funext he
  rw [hz,mulVec_zero] at hev
  exact hev

theorem seed_relationA (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R) :
    (relationA a B T D V).map (eval₂Hom φ (0 : ι → S)) =
      T.map φ * D.map (eval₂Hom φ (φ ∘ a)) * V.map φ := by
  have hm : (relationA a B T D V).map (eval₂Hom φ (0 : ι → S)) =
      (complementary T D V).map (eval₂Hom φ (φ ∘ a)) := by
    funext i j
    exact eval_zero_substitute φ a B (complementary T D V i j)
  rw [hm,eval_complementary]

theorem seed_relationA_det_one (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (T : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R)
    (h : T.map φ * D.map (eval₂Hom φ (φ ∘ a)) * V.map φ=1) :
    eval₂Hom φ (0 : ι → S) (relationA a B T D V).det=1 := by
  rw [RingHom.map_det]
  change ((relationA a B T D V).map (eval₂Hom φ (0 : ι → S))).det=1
  rw [seed_relationA,h,Matrix.det_one]

/-- The derivative convention used by the generic lifting theorem has
variables as rows.  Its transpose is still the identity seed block. -/
theorem seed_jacobian_one (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R)
    (h : P.map φ * jacobian φ (φ ∘ a) e * B.map φ=1) :
    (fun i j => eval₂Hom φ (0 : ι → S) (pderiv i (equations a B P e j))) =
      (1 : Matrix ι ι S) := by
  have hj : jacobian φ (0 : ι → S) (equations a B P e)=1 := by
    exact (sliced_jacobian φ a B P e).trans h
  funext i j
  have hji := congrFun (congrFun hj j) i
  simpa only [jacobian,Matrix.one_apply,eq_comm] using hji

theorem seed_jacobian_det_one (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (e : m → MvPolynomial σ R)
    (h : P.map φ * jacobian φ (φ ∘ a) e * B.map φ=1) :
    Matrix.det (fun i j => eval₂Hom φ (0 : ι → S) (pderiv i (equations a B P e j)))=1 := by
  rw [seed_jacobian_one φ a B P e h,Matrix.det_one]

theorem evaluated_equations_zero
    (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (h : Q*P+V*W=1) (e : m → MvPolynomial σ R) (x : ι → S)
    (hP : ∀ q, eval₂Hom φ x (equations a B P e q)=0)
    (hW : ∀ q, eval₂Hom φ x (residual a B W e q)=0) :
    ∀ q, eval₂Hom φ (pointValue φ a B x) (e q)=0 := by
  have hP' : P.map φ *ᵥ (fun q => eval₂Hom φ (pointValue φ a B x) (e q))=0 := by
    rw [← eval_retained]
    funext q
    exact (eval_substitute φ a B x (retained P e q)).symm.trans (hP q)
  have hW' : W.map φ *ᵥ (fun q => eval₂Hom φ (pointValue φ a B x) (e q))=0 := by
    rw [← eval_retained]
    funext q
    exact (eval_substitute φ a B x (retained W e q)).symm.trans (hW q)
  have hz := (equations_zero_iff (P.map φ) (Q.map φ) (V.map φ) (W.map φ)
    (mapped_decomposition φ P Q V W h) _).mp ⟨hP',hW'⟩
  exact fun q => congrFun hz q

end CycleQ2SlicedCompatibleSystem

#print axioms CycleQ2SlicedCompatibleSystem.relation_identity
#print axioms CycleQ2SlicedCompatibleSystem.seed_relationA_det_one
#print axioms CycleQ2SlicedCompatibleSystem.seed_jacobian_det_one
#print axioms CycleQ2SlicedCompatibleSystem.evaluated_equations_zero
end
end


/- Component: continuation_3/SparseGaussianBlocks.lean -/
section
/-! Two independent Horner variables keep concrete kernel reductions small. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseGaussianPolynomial

abbrev Blocks := List Layers

def addBlocks : Blocks → Blocks → Blocks
  | [], q => q
  | p, [] => p
  | a::p, b::q => addLayers a b :: addBlocks p q

def mulBlocks (p q : Blocks) : Blocks :=
  p.foldr (fun a acc => addBlocks (q.map (mulLayers a)) ([]::acc)) []

def negBlocks (p : Blocks) : Blocks := p.map negLayers

def checkBlock (p : Blocks) (n m : ℕ) : Bool := checkLayer (p[n]?.getD []) m

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

def evalBlocks (φ : GaussianInt →+* R) (x : Fin 5 → R) (z w : R) : Blocks → R
  | [] => 0
  | a::p => evalLayers φ x w a + z * evalBlocks φ x z w p

theorem eval_addBlocks (x : Fin 5 → R) (z w : R) (p q : Blocks) :
    evalBlocks φ x z w (addBlocks p q) = evalBlocks φ x z w p + evalBlocks φ x z w q := by
  induction p generalizing q with
  | nil => simp [addBlocks, evalBlocks]
  | cons a p ih =>
    cases q with
    | nil => simp [addBlocks, evalBlocks]
    | cons b q => simp only [addBlocks, evalBlocks, eval_addLayers, ih]; ring

theorem eval_scaleBlocks (x : Fin 5 → R) (z w : R) (a : Layers) (q : Blocks) :
    evalBlocks φ x z w (q.map (mulLayers a)) = evalLayers φ x w a * evalBlocks φ x z w q := by
  induction q with
  | nil => simp [evalBlocks]
  | cons b q ih => simp only [List.map_cons, evalBlocks, eval_mulLayers, ih]; ring

theorem eval_mulBlocks (x : Fin 5 → R) (z w : R) (p q : Blocks) :
    evalBlocks φ x z w (mulBlocks p q) = evalBlocks φ x z w p * evalBlocks φ x z w q := by
  induction p with
  | nil => simp [mulBlocks, evalBlocks]
  | cons a p ih =>
    change evalBlocks φ x z w (addBlocks (q.map (mulLayers a)) ([]::mulBlocks p q)) = _
    rw [eval_addBlocks, eval_scaleBlocks, evalBlocks, evalLayers, ih, evalBlocks]
    ring

theorem eval_negBlocks (x : Fin 5 → R) (z w : R) (p : Blocks) :
    evalBlocks φ x z w (negBlocks p) = -evalBlocks φ x z w p := by
  induction p with
  | nil => simp [negBlocks, evalBlocks]
  | cons a p ih =>
    change evalLayers φ x w (negLayers a) + z * evalBlocks φ x z w (negBlocks p) = _
    rw [eval_negLayers, ih, evalBlocks]
    ring

/-- Independently checked scalar blocks imply the complete identity. -/
theorem evalBlocks_eq_zero_of_checks (x : Fin 5 → R) (z w : R) (N M : ℕ) (p : Blocks)
    (hlen : p.length ≤ N)
    (hinner : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M)
    (h : ∀ n : Fin N, ∀ m : Fin M, checkBlock p n m = true) :
    evalBlocks φ x z w p = 0 := by
  induction N generalizing p with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    rw [hp, evalBlocks]
  | succ N ih =>
    cases p with
    | nil => rfl
    | cons a p =>
      have hla : a.length ≤ M := by
        simpa only [Fin.val_zero, List.getElem?_cons_zero, Option.getD_some] using hinner 0
      have ha : evalLayers φ x w a = 0 :=
        evalLayers_eq_zero_of_checks φ x w M a hla (fun m => by
          simpa only [checkBlock, Fin.val_zero, List.getElem?_cons_zero, Option.getD_some]
            using h 0 m)
      have hp : p.length ≤ N := Nat.succ_le_succ_iff.mp hlen
      have hli : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M := by
        intro n
        simpa only [Fin.val_succ, List.getElem?_cons_succ] using hinner n.succ
      have hh : ∀ n : Fin N, ∀ m : Fin M, checkBlock p n m = true := by
        intro n m
        simpa only [checkBlock, Fin.val_succ, List.getElem?_cons_succ] using h n.succ m
      rw [evalBlocks, ha, ih p hp hli hh, mul_zero, add_zero]

end Soundness
end CycleQ2SparseGaussianPolynomial

#print axioms CycleQ2SparseGaussianPolynomial.evalBlocks_eq_zero_of_checks
#print axioms CycleQ2SparseGaussianPolynomial.eval_mulBlocks
end


