import Proposal.GeometricSurfaceCoordinates
import Proposal.GeometricTarget02Part02

/-! Continuation of GeometricTarget02.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: continuation_3/SparseModularBlocks.lean -/
section
/-! Two independent Horner variables keep concrete kernel reductions small. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SparseModularPolynomial

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
variable {R : Type*} [CommRing R] [CharP R 109]

def evalBlocks (x : Fin 5 → R) (z w : R) : Blocks → R
  | [] => 0
  | a::p => evalLayers x w a + z * evalBlocks x z w p

theorem eval_addBlocks (x : Fin 5 → R) (z w : R) (p q : Blocks) :
    evalBlocks x z w (addBlocks p q) = evalBlocks x z w p + evalBlocks x z w q := by
  induction p generalizing q with
  | nil => simp [addBlocks, evalBlocks]
  | cons a p ih =>
    cases q with
    | nil => simp [addBlocks, evalBlocks]
    | cons b q => simp only [addBlocks, evalBlocks, eval_addLayers, ih]; ring

theorem eval_scaleBlocks (x : Fin 5 → R) (z w : R) (a : Layers) (q : Blocks) :
    evalBlocks x z w (q.map (mulLayers a)) = evalLayers x w a * evalBlocks x z w q := by
  induction q with
  | nil => simp [evalBlocks]
  | cons b q ih => simp only [List.map_cons, evalBlocks, eval_mulLayers, ih]; ring

theorem eval_mulBlocks (x : Fin 5 → R) (z w : R) (p q : Blocks) :
    evalBlocks x z w (mulBlocks p q) = evalBlocks x z w p * evalBlocks x z w q := by
  induction p with
  | nil => simp [mulBlocks, evalBlocks]
  | cons a p ih =>
    change evalBlocks x z w (addBlocks (q.map (mulLayers a)) ([]::mulBlocks p q)) = _
    rw [eval_addBlocks, eval_scaleBlocks, evalBlocks, evalLayers, ih, evalBlocks]
    ring

theorem eval_negBlocks (x : Fin 5 → R) (z w : R) (p : Blocks) :
    evalBlocks x z w (negBlocks p) = -evalBlocks x z w p := by
  induction p with
  | nil => simp [negBlocks, evalBlocks]
  | cons a p ih =>
    change evalLayers x w (negLayers a) + z * evalBlocks x z w (negBlocks p) = _
    rw [eval_negLayers, ih, evalBlocks]
    ring

/-- Independently checked scalar blocks imply the complete identity. -/
theorem evalBlocks_eq_zero_of_checks (x : Fin 5 → R) (z w : R) (N M : ℕ) (p : Blocks)
    (hlen : p.length ≤ N)
    (hinner : ∀ n : Fin N, (p[n.val]?.getD []).length ≤ M)
    (h : ∀ n : Fin N, ∀ m : Fin M, checkBlock p n m = true) :
    evalBlocks x z w p = 0 := by
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
      have ha : evalLayers x w a = 0 :=
        evalLayers_eq_zero_of_checks x w M a hla (fun m => by
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
end CycleQ2SparseModularPolynomial

#print axioms CycleQ2SparseModularPolynomial.evalBlocks_eq_zero_of_checks
#print axioms CycleQ2SparseModularPolynomial.eval_mulBlocks
end


/- Component: continuation_3/cylinder_bridge/CompatibleAffineGenericLifting.lean -/
section
/-! A compatible equation splitting and affine parameter directions give
an actual finite separable generic solution of the entire polynomial
system.  The two nonsingular blocks used in lifting are proved to be the
identity, rather than supplied as additional minor hypotheses. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CompatibleAffineGenericLifting
open MvPolynomial Matrix HoldoutConstruction
open CycleQ2PolynomialAffineSlice CycleQ2CompatibleEquationCoordinates
open CycleQ2SlicedCompatibleSystem

variable {R T K m l ι κ σ : Type*}
  [CommRing R] [CommRing T] [Nontrivial T] [Algebra R T]
  [Field K] [Algebra R K]
  [Fintype m] [Fintype l] [Fintype ι] [Fintype κ] [Fintype σ]
  [DecidableEq m] [DecidableEq ι] [DecidableEq κ]

abbrev GenericAlgebra (K : Type*) [Field K] [Algebra R K]
    (a : σ → R) (B : Matrix σ ι R) (P : Matrix ι m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R)) (V : Matrix m κ R)
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R) :=
  SquareGenericAlgebra K (CycleQ2OpenSquareLifting.openSystem (equations a B P e)
    (substitute a B c * (relationA a B T₀ D V).det))

/-- The coefficient ring may contain the external family parameters.  The
only varied variables are the affine slice coordinates; the resulting
point satisfies every original equation and the original prescribed open. -/
theorem lift_all_on_compatible_affine_slice
    (a : σ → R) (B : Matrix σ ι R)
    (P : Matrix ι m R) (Q : Matrix m ι R) (V : Matrix m κ R) (W : Matrix κ m R)
    (T₀ : Matrix κ l R) (D : Matrix l m (MvPolynomial σ R))
    (e : m → MvPolynomial σ R) (c : MvPolynomial σ R)
    (hdecomp : Q*P+V*W=1)
    (hrelations : D*ᵥe=0)
    (hseed : ∀ q, eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) (e q)=0)
    (hjac : P.map (algebraMap R T) *
      jacobian (algebraMap R T) ((algebraMap R T) ∘ a) e *
      B.map (algebraMap R T)=1)
    (hcomplement : T₀.map (algebraMap R T) *
      D.map (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a)) *
      V.map (algebraMap R T)=1)
    (hc : IsUnit (eval₂Hom (algebraMap R T) ((algebraMap R T) ∘ a) c))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (GenericAlgebra K a B P T₀ D V e c),
      I.IsMaximal ∧
      Module.Finite K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      Algebra.IsSeparable K ((GenericAlgebra K a B P T₀ D V e c) ⧸ I) ∧
      ∃ x : ι → ((GenericAlgebra K a B P T₀ D V e c) ⧸ I),
        (∀ q, aeval (pointValue (algebraMap R _) a B x) (e q)=0) ∧
        IsUnit (aeval (pointValue (algebraMap R _) a B x) c) := by
  have hseed' (q : ι) : aeval (0 : ι → T) (equations a B P e q)=0 := by
    exact seed_equations_zero (algebraMap R T) a B P e hseed q
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
  obtain ⟨I,hI,hfinite,hsep,x,hP,hW,hopen,_⟩ :=
    CycleQ2SegreGenericLifting.lift_all_equations_on_open (K := K)
      (equations a B P e) (residual a B W e)
      (relationA a B T₀ D V) (relationC a B T₀ D Q) (substitute a B c)
      (relation_identity a B P Q V W T₀ D hdecomp e hrelations)
      (0 : ι → T) hseed' hjac' hcomplement' hc' hinj
  refine ⟨I,hI,hfinite,hsep,x,?_,?_⟩
  · exact evaluated_equations_zero (algebraMap R _) a B P Q V W hdecomp e x hP hW
  · change IsUnit (eval₂Hom (algebraMap R _) (pointValue (algebraMap R _) a B x) c)
    rw [← eval_substitute (algebraMap R _) a B x c]
    exact hopen

end CycleQ2CompatibleAffineGenericLifting

#print axioms CycleQ2CompatibleAffineGenericLifting.lift_all_on_compatible_affine_slice
end
end


/- Component: continuation_3/CurveRestrictionNormalForm.lean -/
section
/-! Integral normal forms for both actual curve restrictions.  The right curve
uses a scaled linear change of coordinates, so every formula is integral. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestriction

open MvPolynomial CycleQ2IncidenceNormalForm
open scoped MonomialOrder

variable {R : Type*} [CommRing R]

@[simp] private lemma vec4_two {α : Type*} (a b c d : α) :
    ![a,b,c,d] (2 : Fin 4) = c := rfl
@[simp] private lemma vec4_three {α : Type*} (a b c d : α) :
    ![a,b,c,d] (3 : Fin 4) = d := rfl

@[simp] private lemma vec5_two {α : Type*} (a b c d e : α) :
    ![a,b,c,d,e] (2 : Fin 5) = c := rfl
@[simp] private lemma vec5_three {α : Type*} (a b c d e : α) :
    ![a,b,c,d,e] (3 : Fin 5) = d := rfl
@[simp] private lemma vec5_four {α : Type*} (a b c d e : α) :
    ![a,b,c,d,e] (4 : Fin 5) = e := rfl

abbrev CurvePoly (R : Type*) [CommRing R] := MvPolynomial (Fin 4) R
abbrev CurveExponent := Fin 4 →₀ ℕ

def exponent (v : Fin 4 → ℕ) : CurveExponent := Finsupp.equivFunOnFinite.symm v
@[simp] theorem exponent_apply (v : Fin 4 → ℕ) (i : Fin 4) : exponent v i = v i := rfl

def mon (a b c d : ℕ) : CurvePoly R := X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d

theorem mon_eq_monomial (a b c d : ℕ) :
    (mon a b c d : CurvePoly R) = monomial (exponent ![a,b,c,d]) 1 := by
  simp only [mon, X_pow_eq_monomial, monomial_mul, one_mul]
  apply congrArg (fun e : CurveExponent => monomial e (1 : R))
  ext i
  fin_cases i <;> simp [exponent, Finsupp.single_apply, Fin.ext_iff]

theorem monomial_eq_C_mul_mon (a b c d : ℕ) (r : R) :
    monomial (exponent ![a,b,c,d]) r = C r * mon a b c d := by
  rw [mon_eq_monomial, C_mul_monomial, mul_one]

theorem mon_homogeneous (a b c d : ℕ) :
    (mon a b c d : CurvePoly R).IsHomogeneous (a+b+c+d) := by
  rw [mon_eq_monomial]
  apply isHomogeneous_monomial
  norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ, add_assoc,
    Matrix.cons_val_succ, Fin.reduceSucc]

inductive Side | left | right deriving DecidableEq, Fintype

def xBound : Side → ℕ | .left => 2 | .right => 3
def zBound : Side → ℕ | .left => 3 | .right => 2

def curveWeight : Side → CurveExponent →+ ℕ
  | .left =>
    { toFun := fun d => 3*d 0+d 1+3*d 2+d 3
      map_zero' := by simp
      map_add' := by intro a b; simp only [Finsupp.add_apply]; omega }
  | .right =>
    { toFun := fun d => 3*d 0+d 1+4*d 2+d 3
      map_zero' := by simp
      map_add' := by intro a b; simp only [Finsupp.add_apply]; omega }

def curveOrder (s : Side) : MonomialOrder (Fin 4) :=
  weightedOrder MonomialOrder.lex (curveWeight s)

def quadric (s : Side) (r : R) : CurvePoly R :=
  match s with
  | .left => X 0 ^ 2 - C r * X 1 * X 3
  | .right => X 2 ^ 2 + X 0 ^ 2

def cubic (s : Side) (r ι : R) : CurvePoly R :=
  match s with
  | .left => X 2 ^ 3 + X 0*X 2*X 3 + X 1*X 2*X 3 + X 0*X 1^2 +
      C r*X 0*X 1*X 3 + C (1-ι)*X 3^3 - C ι*X 1^3
  | .right => X 0 ^ 3 - X 0^2*X 3 - X 0*X 1*X 3 + X 2*X 1*X 3 -
      X 0*X 1^2 - X 2*X 1^2 - C (2*(1-ι))*X 3^3 + C (2*ι)*X 1^3

def quadricLead : Side → CurveExponent
  | .left => Finsupp.single 0 2
  | .right => Finsupp.single 2 2

def cubicLead : Side → CurveExponent
  | .left => Finsupp.single 2 3
  | .right => Finsupp.single 0 3

def leftTailExponent (j : Fin 6) : CurveExponent :=
  ![exponent ![1,0,1,1], exponent ![0,1,1,1], exponent ![1,2,0,0],
    exponent ![1,1,0,1], exponent ![0,0,0,3], exponent ![0,3,0,0]] j

def leftTailCoefficient (r ι : R) (j : Fin 6) : R := ![1,1,1,r,1-ι,-ι] j

def rightTailExponent (j : Fin 7) : CurveExponent :=
  ![exponent ![2,0,0,1], exponent ![1,1,0,1], exponent ![0,1,1,1],
    exponent ![1,2,0,0], exponent ![0,2,1,0], exponent ![0,0,0,3],
    exponent ![0,3,0,0]] j

def rightTailCoefficient (ι : R) (j : Fin 7) : R :=
  ![-1,-1,1,-1,-1,-(2*(1-ι)),2*ι] j

theorem left_quadric_shape (r : R) :
    quadric .left r = monomial (quadricLead .left) 1 +
      ∑ _j : Fin 1, monomial (exponent ![0,1,0,1]) (-r) := by
  simp only [Fin.sum_univ_one, quadricLead]
  rw [← X_pow_eq_monomial, monomial_eq_C_mul_mon]
  simp [quadric, mon] <;> ring

theorem right_quadric_shape (r : R) :
    quadric .right r = monomial (quadricLead .right) 1 +
      ∑ _j : Fin 1, monomial (exponent ![2,0,0,0]) 1 := by
  simp only [Fin.sum_univ_one, quadricLead]
  rw [← X_pow_eq_monomial, monomial_eq_C_mul_mon]
  simp [quadric, mon]

theorem left_cubic_shape (r ι : R) :
    cubic .left r ι = monomial (cubicLead .left) 1 +
      ∑ j : Fin 6, monomial (leftTailExponent j) (leftTailCoefficient r ι j) := by
  simp only [cubicLead, ← X_pow_eq_monomial]
  simp only [Fin.sum_univ_succ, leftTailExponent, leftTailCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceSucc,
    Matrix.head_cons, Matrix.tail_cons, monomial_eq_C_mul_mon]
  norm_num [cubic, mon, Matrix.cons_val_succ, Fin.reduceSucc]
  ring

theorem right_cubic_shape (r ι : R) :
    cubic .right r ι = monomial (cubicLead .right) 1 +
      ∑ j : Fin 7, monomial (rightTailExponent j) (rightTailCoefficient ι j) := by
  simp only [cubicLead, ← X_pow_eq_monomial]
  simp only [Fin.sum_univ_succ, rightTailExponent, rightTailCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceSucc,
    Matrix.head_cons, Matrix.tail_cons, monomial_eq_C_mul_mon]
  norm_num [cubic, mon, Matrix.cons_val_succ, Fin.reduceSucc]
  ring

theorem quadric_leading [Nontrivial R] (s : Side) (r : R) :
    (curveOrder s).degree (quadric s r) = quadricLead s ∧
      (curveOrder s).Monic (quadric s r) := by
  cases s
  · rw [left_quadric_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]
  · rw [right_quadric_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]

theorem cubic_leading [Nontrivial R] (s : Side) (r ι : R) :
    (curveOrder s).degree (cubic s r ι) = cubicLead s ∧
      (curveOrder s).Monic (cubic s r ι) := by
  cases s
  · rw [left_cubic_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, cubicLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      fin_cases j <;> norm_num [curveWeight, leftTailExponent, cubicLead,
        Matrix.cons_val_succ, Fin.reduceSucc, Finsupp.single_apply, Fin.ext_iff]
  · rw [right_cubic_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, cubicLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      fin_cases j <;> norm_num [curveWeight, rightTailExponent, cubicLead,
        Matrix.cons_val_succ, Fin.reduceSucc, Finsupp.single_apply, Fin.ext_iff]

theorem leading_coprime [Nontrivial R] (s : Side) (r ι : R) :
    ∀ j, (curveOrder s).degree (quadric s r) j = 0 ∨
      (curveOrder s).degree (cubic s r ι) j = 0 := by
  rw [(quadric_leading s r).1, (cubic_leading s r ι).1]
  intro j
  cases s <;> fin_cases j <;> simp [quadricLead, cubicLead]

def Standard (s : Side) (p : CurvePoly R) : Prop :=
  ∀ e ∈ p.support, e 0 < xBound s ∧ e 2 < zBound s

theorem standard_iff [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    Standard s p ↔ Reduced (curveOrder s) (quadric s r) (cubic s r ι) p := by
  simp only [Standard, Reduced, (quadric_leading s r).1, (cubic_leading s r ι).1]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  cases s <;> simp only [quadricLead, cubicLead, Finsupp.single_le_iff, xBound, zBound]
  · omega
  · omega

theorem quadric_homogeneous (s : Side) (r : R) :
    (quadric s r).IsHomogeneous 2 := by
  cases s
  · rw [left_quadric_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [quadricLead])
    · apply (homogeneousSubmodule (Fin 4) R 2).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ,
        Matrix.cons_val_succ, Fin.reduceSucc]
  · rw [right_quadric_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [quadricLead])
    · apply (homogeneousSubmodule (Fin 4) R 2).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ,
        Matrix.cons_val_succ, Fin.reduceSucc]

theorem cubic_homogeneous (s : Side) (r ι : R) :
    (cubic s r ι).IsHomogeneous 3 := by
  cases s
  · rw [left_cubic_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [cubicLead])
    · apply (homogeneousSubmodule (Fin 4) R 3).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      fin_cases j <;> norm_num [leftTailExponent, Finsupp.degree_eq_sum,
        Fin.sum_univ_succ, Matrix.cons_val_succ, Fin.reduceSucc]
  · rw [right_cubic_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [cubicLead])
    · apply (homogeneousSubmodule (Fin 4) R 3).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      fin_cases j <;> norm_num [rightTailExponent, Finsupp.degree_eq_sum,
        Fin.sum_univ_succ, Matrix.cons_val_succ, Fin.reduceSucc]

def curveIdeal (s : Side) (r ι : R) : Ideal (CurvePoly R) :=
  equationsIdeal (quadric s r) (cubic s r ι)

abbrev CurveRing (s : Side) (r ι : R) := CurvePoly R ⧸ curveIdeal s r ι

theorem existsUnique_normal [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    ∃! q, Standard s q ∧ ∃ a b, p = a * quadric s r + b * cubic s r ι + q := by
  simpa only [standard_iff s r ι] using
    existsUnique_reduced_representative (curveOrder s) (quadric s r) (cubic s r ι) p
      (quadric_leading s r).2 (cubic_leading s r ι).2 (leading_coprime s r ι)

def normal [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) : CurvePoly R :=
  (existsUnique_normal s r ι p).choose

theorem normal_spec [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    Standard s (normal s r ι p) ∧
      ∃ a b, p = a * quadric s r + b * cubic s r ι + normal s r ι p :=
  (existsUnique_normal s r ι p).choose_spec.1

theorem normal_unique [Nontrivial R] (s : Side) (r ι : R) (p q : CurvePoly R)
    (hq : Standard s q) (hrep : ∃ a b, p = a * quadric s r + b * cubic s r ι + q) :
    q = normal s r ι p :=
  (existsUnique_normal s r ι p).choose_spec.2 q ⟨hq, hrep⟩

theorem normal_homogeneous [Nontrivial R] (s : Side) (r ι : R)
    {p : CurvePoly R} {d : ℕ} (hp : p.IsHomogeneous d) :
    (normal s r ι p).IsHomogeneous d := by
  obtain ⟨hr, a, b, heq⟩ := normal_spec s r ι p
  exact reduced_isHomogeneous (curveOrder s) (quadric_leading s r).2
    (cubic_leading s r ι).2 (leading_coprime s r ι)
    (quadric_homogeneous s r) (cubic_homogeneous s r ι) hp
    ((standard_iff s r ι _).mp hr) heq

theorem normal_eq_self [Nontrivial R] (s : Side) (r ι : R)
    {p : CurvePoly R} (hp : Standard s p) : normal s r ι p = p := by
  exact (normal_unique s r ι p p hp ⟨0,0,by simp⟩).symm

@[simp] theorem map_quadric {S : Type*} [CommRing S] (φ : R →+* S) (s : Side) (r : R) :
    MvPolynomial.map φ (quadric s r) = quadric s (φ r) := by
  cases s <;> simp [quadric]

@[simp] theorem map_cubic {S : Type*} [CommRing S] (φ : R →+* S) (s : Side) (r ι : R) :
    MvPolynomial.map φ (cubic s r ι) = cubic s (φ r) (φ ι) := by
  cases s <;> simp [cubic, map_ofNat]

theorem standard_map {S : Type*} [CommRing S] (φ : R →+* S)
    {s : Side} {p : CurvePoly R} (hp : Standard s p) :
    Standard s (MvPolynomial.map φ p) := by
  intro e he
  exact hp e (MvPolynomial.support_map_subset φ p he)

theorem normal_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (p : CurvePoly R) :
    MvPolynomial.map φ (normal s r ι p) =
      normal s (φ r) (φ ι) (MvPolynomial.map φ p) := by
  obtain ⟨hr,a,b,hp⟩ := normal_spec s r ι p
  apply normal_unique
  · exact standard_map φ hr
  · refine ⟨MvPolynomial.map φ a, MvPolynomial.map φ b, ?_⟩
    simpa only [map_add, map_mul, map_quadric, map_cubic] using congrArg (MvPolynomial.map φ) hp

/-- The left restriction eliminates w.  The right restriction is the integral
scaled coordinate change (x₀,x₁,x₂,x₃,w)=(u+v,2y₁,u-v,2y₃,4ry₁y₃). -/
def restrictionValues (s : Side) (r : R) : Fin 5 → CurvePoly R :=
  match s with
  | .left => ![X 0, X 1, X 2, X 3, -(X 2^2)]
  | .right => ![X 0+X 2, 2*X 1, X 0-X 2, 2*X 3, C (4*r)*X 1*X 3]

def substitution (s : Side) (r : R) : MvPolynomial (Fin 5) R →ₐ[R] CurvePoly R :=
  aeval (restrictionValues s r)

@[simp] theorem substitution_X (s : Side) (r : R) (i : Fin 5) :
    substitution s r (X i) = restrictionValues s r i := by
  simp [substitution]

@[simp] theorem substitution_C (s : Side) (r c : R) :
    substitution s r (C c) = C c := by
  simp [substitution]

theorem left_h_identity (r ι : R) :
    substitution .left r (CycleQ2IncidenceEquations.smoothH ι) =
      cubic .left r ι + X 0 * quadric .left r := by
  simp only [CycleQ2IncidenceEquations.smoothH, CycleQ2IncidenceEquations.smoothB,
    CycleQ2IncidenceEquations.smoothA, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, cubic, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem right_h_identity (r ι : R) :
    substitution .right r (CycleQ2IncidenceEquations.smoothH ι) =
      -4 * cubic .right r ι + (6*X 0-2*X 3) * quadric .right r := by
  simp only [CycleQ2IncidenceEquations.smoothH, CycleQ2IncidenceEquations.smoothB,
    CycleQ2IncidenceEquations.smoothA, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, cubic, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem left_G_identity (r : R) :
    substitution .left r (CycleQ2IncidenceEquations.seedG r) =
      quadric .left r * (X 0^4+C r*X 0^2*X 1*X 3+C (r^2)*X 1^2*X 3^2) := by
  simp only [CycleQ2IncidenceEquations.seedG, CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem right_G_identity (r : R) :
    substitution .right r (CycleQ2IncidenceEquations.seedG r) =
      2 * quadric .right r * (X 0^4+14*X 0^2*X 2^2+X 2^4) := by
  simp only [CycleQ2IncidenceEquations.seedG, CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem substitution_h_mem (s : Side) (r ι : R) :
    substitution s r (CycleQ2IncidenceEquations.smoothH ι) ∈ curveIdeal s r ι := by
  cases s
  · rw [left_h_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨X 0, 1, by ring⟩
  · rw [right_h_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨6*X 0-2*X 3, -4, by ring⟩

theorem substitution_G_mem (s : Side) (r ι : R) :
    substitution s r (CycleQ2IncidenceEquations.seedG r) ∈ curveIdeal s r ι := by
  cases s
  · rw [left_G_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨X 0^4+C r*X 0^2*X 1*X 3+C (r^2)*X 1^2*X 3^2, 0, by ring⟩
  · rw [right_G_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨2*(X 0^4+14*X 0^2*X 2^2+X 2^4), 0, by ring⟩

theorem substitution_F_mem (s : Side) (r ι : R) :
    substitution s r (CycleQ2IncidenceEquations.smoothF r ι) ∈ curveIdeal s r ι := by
  rw [CycleQ2IncidenceEquations.smoothF, map_add, map_mul]
  exact Ideal.add_mem _ (substitution_G_mem s r ι)
    (Ideal.mul_mem_right _ _ (substitution_h_mem s r ι))

theorem standard_add {s : Side} {p q : CurvePoly R}
    (hp : Standard s p) (hq : Standard s q) : Standard s (p+q) := by
  intro e he
  rcases Finset.mem_union.mp (support_add he) with h | h
  · exact hp e h
  · exact hq e h

theorem standard_C_mul {s : Side} {p : CurvePoly R} (hp : Standard s p) (c : R) :
    Standard s (C c*p) := by
  intro e he
  apply hp e
  apply mem_support_iff.mpr
  intro hz
  exact (mem_support_iff.mp he) (by rw [coeff_C_mul, hz, mul_zero])

theorem normal_add [Nontrivial R] (s : Side) (r ι : R) (p q : CurvePoly R) :
    normal s r ι (p+q) = normal s r ι p + normal s r ι q := by
  obtain ⟨hp,a,b,hab⟩ := normal_spec s r ι p
  obtain ⟨hq,c,d,hcd⟩ := normal_spec s r ι q
  symm
  apply normal_unique
  · exact standard_add hp hq
  · refine ⟨a+c,b+d,?_⟩
    linear_combination hab+hcd

theorem normal_C_mul [Nontrivial R] (s : Side) (r ι c : R) (p : CurvePoly R) :
    normal s r ι (C c*p) = C c*normal s r ι p := by
  obtain ⟨hp,a,b,hab⟩ := normal_spec s r ι p
  symm
  apply normal_unique
  · exact standard_C_mul hp c
  · refine ⟨C c*a,C c*b,?_⟩
    linear_combination C c*hab

def normalLinear [Nontrivial R] (s : Side) (r ι : R) : CurvePoly R →ₗ[R] CurvePoly R where
  toFun := normal s r ι
  map_add' := normal_add s r ι
  map_smul' := fun c p => by
    simpa only [smul_eq_C_mul, RingHom.id_apply] using normal_C_mul s r ι c p

theorem normal_sub_mem [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    p-normal s r ι p ∈ curveIdeal s r ι := by
  obtain ⟨_,a,b,hp⟩ := normal_spec s r ι p
  apply Ideal.mem_span_pair.mpr
  exact ⟨a,b,by linear_combination -hp⟩

theorem normal_eq_zero_iff [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    normal s r ι p = 0 ↔ p ∈ curveIdeal s r ι := by
  constructor
  · intro hp
    simpa only [hp, sub_zero] using normal_sub_mem s r ι p
  · intro hp
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    symm
    exact normal_unique s r ι p 0 (by simp [Standard])
      ⟨a,b,by simpa only [add_zero] using hab.symm⟩

@[simp] theorem map_restrictionValues {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (j : Fin 5) :
    MvPolynomial.map φ (restrictionValues s r j) = restrictionValues s (φ r) j := by
  cases s <;> fin_cases j <;>
    norm_num [restrictionValues, map_ofNat, Matrix.cons_val_succ, Fin.reduceSucc]

theorem substitution_map {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map φ (substitution s r p) =
      substitution s (φ r) (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, map_X, substitution_X, map_restrictionValues]

/-- A linear map representing the genuine restriction, with the canonical
curve representative chosen by the proved normal-form theorem. -/
def restrictionNormal [Nontrivial R] (s : Side) (r ι : R) :
    MvPolynomial (Fin 5) R →ₗ[R] CurvePoly R :=
  (normalLinear s r ι).comp (substitution s r).toLinearMap

@[simp] theorem restrictionNormal_apply [Nontrivial R]
    (s : Side) (r ι : R) (p : MvPolynomial (Fin 5) R) :
    restrictionNormal s r ι p = normal s r ι (substitution s r p) := rfl

theorem restrictionNormal_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map φ (restrictionNormal s r ι p) =
      restrictionNormal s (φ r) (φ ι) (MvPolynomial.map φ p) := by
  simp only [restrictionNormal_apply, normal_map, substitution_map]

end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.quadric_leading
#print axioms CycleQ2CurveRestriction.cubic_leading
#print axioms CycleQ2CurveRestriction.normal_homogeneous
#print axioms CycleQ2CurveRestriction.substitution_F_mem
#print axioms CycleQ2CurveRestriction.restrictionNormal_map
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

abbrev MatrixParameter := (Fin 3 × Fin 3) × StandardIndex 14
abbrev ParameterIndex := FullInvariantIndex 3 ⊕ (FullInvariantIndex 6 ⊕ MatrixParameter)
abbrev ParameterPolynomial (R : Type*) [CommRing R] := MvPolynomial ParameterIndex R

def leadingProduct (R : Type*) [CommRing R] : ParameterPolynomial R :=
  X (Sum.inl fullCubicLeadingIndex) * X (Sum.inr (Sum.inl fullSexticLeadingIndex))

theorem leadingProduct_ne_zero (R : Type*) [CommRing R] [IsDomain R] :
    leadingProduct R ≠ 0 := mul_ne_zero (X_ne_zero _) (X_ne_zero _)

abbrev ParameterRing (R : Type*) [CommRing R] := Localization.Away (leadingProduct R)

instance parameterRingDomain (R : Type*) [CommRing R] [IsDomain R] :
    IsDomain (ParameterRing R) := Localization.Away.isDomain (leadingProduct_ne_zero R)

variable (R : Type*) [CommRing R] [IsDomain R]

def cubicCoefficient (e : FullInvariantIndex 3) : ParameterRing R :=
  algebraMap (ParameterPolynomial R) (ParameterRing R) (X (Sum.inl e))

def sexticCoefficient (e : FullInvariantIndex 6) : ParameterRing R :=
  algebraMap (ParameterPolynomial R) (ParameterRing R) (X (Sum.inr (Sum.inl e)))

def matrixCoefficient (i j : Fin 3) (e : StandardIndex 14) : ParameterRing R :=
  algebraMap (ParameterPolynomial R) (ParameterRing R) (X (Sum.inr (Sum.inr ((i, j), e))))

theorem leading_coefficients_units :
    IsUnit (cubicCoefficient R fullCubicLeadingIndex) ∧
      IsUnit (sexticCoefficient R fullSexticLeadingIndex) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := ParameterRing R) (leadingProduct R)
  have hp : IsUnit (cubicCoefficient R fullCubicLeadingIndex *
      sexticCoefficient R fullSexticLeadingIndex) := by
    simpa only [leadingProduct, map_mul, cubicCoefficient, sexticCoefficient] using hu
  exact ⟨isUnit_of_mul_isUnit_left hp, isUnit_of_mul_isUnit_right hp⟩

def equations (r : R) : EquationIndex → ParameterRing R :=
  incidenceEquations (cubicCoefficient R) (sexticCoefficient R)
    (leading_coefficients_units R).1 (leading_coefficients_units R).2
    (algebraMap R (ParameterRing R) r) (matrixCoefficient R)

section Specialization

variable {R} {S : Type*} [CommRing S] [Algebra R S]

def coefficientPoint (hcoeff : FullInvariantIndex 3 → S)
    (Fcoeff : FullInvariantIndex 6 → S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) : ParameterIndex → S :=
  Sum.elim hcoeff (Sum.elim Fcoeff (fun q => δ q.1.1 q.1.2 q.2))

def polynomialSpecialization (hcoeff : FullInvariantIndex 3 → S)
    (Fcoeff : FullInvariantIndex 6 → S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) : ParameterPolynomial R →ₐ[R] S :=
  aeval (coefficientPoint hcoeff Fcoeff δ)

theorem polynomialSpecialization_leadingProduct
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) :
    polynomialSpecialization hcoeff Fcoeff δ (leadingProduct R) =
      hcoeff fullCubicLeadingIndex * Fcoeff fullSexticLeadingIndex := by
  simp [polynomialSpecialization, leadingProduct, coefficientPoint]

/-- Every actual coefficient point in the two-leading-coefficient open has
its canonical specialization from the universal localized coefficient ring. -/
def specialization (hcoeff : FullInvariantIndex 3 → S)
    (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) : ParameterRing R →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (leadingProduct R)
    (f := polynomialSpecialization hcoeff Fcoeff δ)
    (by rw [polynomialSpecialization_leadingProduct]; exact hu.mul Fu)

@[simp] theorem specialization_polynomial
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (p : ParameterPolynomial R) :
    specialization hcoeff Fcoeff hu Fu δ
      (algebraMap (ParameterPolynomial R) (ParameterRing R) p) =
        polynomialSpecialization hcoeff Fcoeff δ p := by
  simp [specialization, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem specialization_cubicCoefficient
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (e : FullInvariantIndex 3) :
    specialization hcoeff Fcoeff hu Fu δ (cubicCoefficient R e) = hcoeff e := by
  simp [specialization, cubicCoefficient, IsLocalization.Away.liftAlgHom_apply,
    polynomialSpecialization, coefficientPoint]

@[simp] theorem specialization_sexticCoefficient
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (e : FullInvariantIndex 6) :
    specialization hcoeff Fcoeff hu Fu δ (sexticCoefficient R e) = Fcoeff e := by
  simp [specialization, sexticCoefficient, IsLocalization.Away.liftAlgHom_apply,
    polynomialSpecialization, coefficientPoint]

@[simp] theorem specialization_matrixCoefficient
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S)
    (i j : Fin 3) (e : StandardIndex 14) :
    specialization hcoeff Fcoeff hu Fu δ (matrixCoefficient R i j e) = δ i j e := by
  simp [specialization, matrixCoefficient, IsLocalization.Away.liftAlgHom_apply,
    polynomialSpecialization, coefficientPoint]

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

/-- The literal raw smooth seed is an actual point of the universal chart. -/
def seedSpecialization (r ι : R) : ParameterRing R →ₐ[R] R :=
  specialization (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
    (fun _ _ _ => 0)

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


