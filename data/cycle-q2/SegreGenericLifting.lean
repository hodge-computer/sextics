import Proposal.SegreCartierEquations
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting
import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.RingTheory.Nullstellensatz

/-! # Generic point selection and formal lifting of the Segre equations -/

set_option Elab.async false

/- Component: continuation_2/VeryGeneralPoint.lean -/
section
/-!
Actual very-general-point selection in affine coefficient spaces.

The countable-proper-image specialization argument requires a complex point
outside countably many proper algebraic conditions. This module proves that
selection statement for genuine polynomial equations. It does not assert
that any moving cycle, supported projector, or primitive exists.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2VeryGeneral

open MvPolynomial

variable {K : Type*} [Field K] [Uncountable K]

theorem exists_avoiding_univariate {ι : Type*} [Countable ι]
    (p : ι → Polynomial K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : K, ∀ i, (p i).eval x ≠ 0 := by
  classical
  let roots : ι → Set K := fun i => {x | (p i).eval x = 0}
  have hroots (i : ι) : (roots i).Finite := by
    simpa only [roots, Polynomial.IsRoot] using
      (Polynomial.finite_setOfPred_isRoot (hp i))
  have hcount : (⋃ i, roots i).Countable :=
    Set.countable_iUnion (fun i => (hroots i).countable)
  have hout : ∃ x : K, x ∉ ⋃ i, roots i := by
    by_contra h
    push Not at h
    have heq : (⋃ i, roots i) = Set.univ := Set.eq_univ_of_forall h
    exact Set.not_countable_univ (heq ▸ hcount)
  obtain ⟨x, hx⟩ := hout
  refine ⟨x, fun i hi => hx ?_⟩
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Countably many genuine nonzero multivariate polynomials have a common
nonvanishing point over an uncountable field. -/
theorem exists_avoiding_polynomials (n : ℕ) {ι : Type*} [Countable ι]
    (p : ι → MvPolynomial (Fin n) K) (hp : ∀ i, p i ≠ 0) :
    ∃ x : Fin n → K, ∀ i, eval x (p i) ≠ 0 := by
  classical
  induction n with
  | zero =>
      refine ⟨Fin.elim0, ?_⟩
      intro i hi
      obtain ⟨c, hc⟩ := (isEmptyAlgEquiv K (Fin 0)).symm.surjective (p i)
      have hpi : p i = C c := by simpa using hc.symm
      rw [hpi, eval_C] at hi
      exact hp i (by simp [hpi, hi])
  | succ n ih =>
      let q : ι → Polynomial (MvPolynomial (Fin n) K) :=
        fun i => finSuccEquiv K n (p i)
      have hq (i : ι) : q i ≠ 0 := by
        intro hz
        apply hp i
        apply (finSuccEquiv K n).injective
        simpa only [q, map_zero] using hz
      have hlc (i : ι) : (q i).leadingCoeff ≠ 0 := by
        simpa only [ne_eq, Polynomial.leadingCoeff_eq_zero] using hq i
      obtain ⟨y, hy⟩ := ih (fun i => (q i).leadingCoeff) hlc
      let s : ι → Polynomial K := fun i => (q i).map (eval y)
      have hs (i : ι) : s i ≠ 0 := by
        intro hz
        have hc := congrArg (fun z : Polynomial K => z.coeff (q i).natDegree) hz
        simp only [s, Polynomial.coeff_map, Polynomial.coeff_zero] at hc
        exact hy i hc
      obtain ⟨x, hx⟩ := exists_avoiding_univariate s hs
      refine ⟨Fin.cons x y, ?_⟩
      intro i
      simpa only [eval_eq_eval_mv_eval', q, s] using hx i

/-- A very general complex coefficient point can also be required to lie in
any prescribed nonempty principal open, without a coefficient bound. -/
theorem complex_point_in_principal_open_avoiding (n : ℕ)
    {ι : Type*} [Countable ι] (g : MvPolynomial (Fin n) ℂ) (hg : g ≠ 0)
    (p : ι → MvPolynomial (Fin n) ℂ) (hp : ∀ i, p i ≠ 0) :
    ∃ x : Fin n → ℂ, eval x g ≠ 0 ∧ ∀ i, eval x (p i) ≠ 0 := by
  letI : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  let family : Option ι → MvPolynomial (Fin n) ℂ := fun i => Option.elim i g p
  have hn (i : Option ι) : family i ≠ 0 := by
    cases i with
    | none => exact hg
    | some i => exact hp i
  obtain ⟨x, hx⟩ := exists_avoiding_polynomials n family hn
  exact ⟨x, hx none, fun i => hx (some i)⟩

/-- A countable family of genuine affine algebraic zero loci covering a
nonempty principal open has a member equal to the whole affine space.
This is the countability step in proper-image specialization, without any
assumed existence of projectors or cycle families. -/
theorem complex_countable_algebraic_cover (n : ℕ)
    {ι : Type*} [Countable ι]
    (I : ι → Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin n) ℂ) (hg : g ≠ 0)
    (hcover : ∀ x : Fin n → ℂ, eval x g ≠ 0 →
      ∃ i, x ∈ zeroLocus ℂ (I i)) :
    ∃ i, zeroLocus ℂ (I i) = Set.univ := by
  classical
  by_contra h
  push Not at h
  have hn (i : ι) : I i ≠ ⊥ := by
    intro hi
    apply h i
    simp only [hi, zeroLocus_bot, Set.top_eq_univ]
  have hp (i : ι) : ∃ p : MvPolynomial (Fin n) ℂ, p ∈ I i ∧ p ≠ 0 := by
    by_contra hh
    push Not at hh
    apply hn i
    apply le_antisymm
    · intro p hp
      exact (Ideal.mem_bot).mpr (hh p hp)
    · exact bot_le
  choose p hpI hpne using hp
  obtain ⟨x, hxg, hxp⟩ := complex_point_in_principal_open_avoiding n g hg p hpne
  obtain ⟨i, hxi⟩ := hcover x hxg
  apply hxp i
  exact hxi (p i) (hpI i)

end CycleQ2VeryGeneral

#print axioms CycleQ2VeryGeneral.exists_avoiding_polynomials
#print axioms CycleQ2VeryGeneral.complex_point_in_principal_open_avoiding
#print axioms CycleQ2VeryGeneral.complex_countable_algebraic_cover
end
end


/- Component: continuation_2/OpenSquareLifting.lean -/
section
/-!
A nonsingular square polynomial system has a finite separable generic point
inside any principal open containing the seed.  The open condition is imposed
by an actual additional equation u * c(x) - 1, whose Jacobian is block triangular.
This is an algebraic existence statement, not a formal-series lifting premise.
It creates no particular incidence seed or rank certificate.
-/

noncomputable section

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2OpenSquareLifting

open MvPolynomial HoldoutConstruction

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The inverse coordinate is the left summand; the original coordinates are
in the right summand. -/
def extendedPoint (x : ι → T) (u : T) : Unit ⊕ ι → T :=
  Sum.elim (fun _ => u) x

/-- Actual polynomial equations for the chosen square system on the principal
open defined by c. -/
def openSystem (equations : ι → MvPolynomial ι R) (c : MvPolynomial ι R) :
    Unit ⊕ ι → MvPolynomial (Unit ⊕ ι) R :=
  Sum.elim (fun _ => X (Sum.inl ()) * rename Sum.inr c - 1)
    (fun i => rename Sum.inr (equations i))

@[simp] theorem aeval_extended_rename (x : ι → T) (u : T)
    (p : MvPolynomial ι R) :
    aeval (extendedPoint x u) (rename (Sum.inr : ι → Unit ⊕ ι) p) = aeval x p := by
  rw [aeval_rename]
  rfl

@[simp] theorem pderiv_inverse_rename (p : MvPolynomial ι R) :
    pderiv (Sum.inl ()) (rename (Sum.inr : ι → Unit ⊕ ι) p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [pderiv_mul, hp, pderiv_X, Pi.single_apply]

@[simp] theorem pderiv_original_rename (i : ι) (p : MvPolynomial ι R) :
    pderiv (Sum.inr i) (rename (Sum.inr : ι → Unit ⊕ ι) p) =
      rename Sum.inr (pderiv i p) :=
  pderiv_rename Sum.inr_injective i p

/-- An actual solution with an inverse for c evaluates every augmented
polynomial equation to zero. -/
theorem openSystem_seed (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (x : ι → T) (u : T)
    (hx : ∀ i, aeval x (equations i) = 0) (hu : u * aeval x c = 1) :
    ∀ i, aeval (extendedPoint x u) (openSystem equations c i) = 0 := by
  intro i
  cases i with
  | inl z => cases z; simpa [openSystem, aeval_rename, extendedPoint, Function.comp_def] using sub_eq_zero.mpr hu
  | inr i => simpa [openSystem] using hx i

/-- The full augmented Jacobian is a triangular block matrix.  This equality
holds at every point, independently of the polynomial equations. -/
theorem openSystem_jacobian_det (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (x : ι → T) (u : T) :
    Matrix.det (fun i j => aeval (extendedPoint x u)
      (pderiv i (openSystem equations c j))) =
    aeval x c * Matrix.det (fun i j => aeval x (pderiv i (equations j))) := by
  have hmatrix :
      (fun i j => aeval (extendedPoint x u) (pderiv i (openSystem equations c j))) =
      Matrix.fromBlocks (fun (_ _ : Unit) => aeval x c)
        (0 : Matrix Unit ι T)
        (fun i (_ : Unit) => u * aeval x (pderiv i c))
        (fun i j => aeval x (pderiv i (equations j))) := by
    ext i j
    cases i with
    | inl z =>
      cases z
      cases j with
      | inl w => cases w; simp [openSystem, aeval_rename, extendedPoint, Function.comp_def, Matrix.fromBlocks]
      | inr j => simp [openSystem, Matrix.fromBlocks]
    | inr i =>
      cases j with
      | inl w =>
        cases w
        simp [openSystem, aeval_rename, extendedPoint, Function.comp_def, Matrix.fromBlocks, pderiv_X]
      | inr j => simp [openSystem, Matrix.fromBlocks]
  rw [hmatrix, Matrix.det_fromBlocks_zero₁₂, Matrix.det_unique]

/-- Every solution of the augmented system solves the original system, and
its value of c is a unit. -/
theorem solution_on_open (equations : ι → MvPolynomial ι R)
    (c : MvPolynomial ι R) (z : Unit ⊕ ι → T)
    (hz : ∀ i, aeval z (openSystem equations c i) = 0) :
    (∀ i, aeval (fun i => z (Sum.inr i)) (equations i) = 0) ∧
      IsUnit (aeval (fun i => z (Sum.inr i)) c) := by
  have hrename (p : MvPolynomial ι R) :
      aeval z (rename (Sum.inr : ι → Unit ⊕ ι) p) =
        aeval (fun i => z (Sum.inr i)) p := by rw [aeval_rename]; rfl
  constructor
  · intro i
    simpa only [openSystem, Sum.elim_inr, hrename] using hz (Sum.inr i)
  · have hi := hz (Sum.inl ())
    simp only [openSystem, Sum.elim_inl, map_sub, map_mul, aeval_X, map_one,
      hrename, sub_eq_zero] at hi
    refine ⟨⟨aeval (fun i => z (Sum.inr i)) c, z (Sum.inl ()), ?_, hi⟩, rfl⟩
    exact (mul_comm (aeval (fun i => z (Sum.inr i)) c) (z (Sum.inl ()))).trans hi

section GenericPoint

set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] [Algebra R K] [Nontrivial T]

/-- A genuine finite separable generic solution inside the specified open
locus, obtained from a nonsingular special-fiber seed.  Coefficients must
embed in K; the special-fiber coefficient map need not be injective. -/
theorem square_system_generic_lift_on_open
    (equations : ι → MvPolynomial ι R) (c : MvPolynomial ι R)
    (seed : ι → T)
    (hseed : ∀ i, aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det
      (fun i j => aeval seed (pderiv i (equations j)))))
    (hc : IsUnit (aeval seed c))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (SquareGenericAlgebra K (openSystem equations c)), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I) ∧
      ∃ x : ι → ((SquareGenericAlgebra K (openSystem equations c)) ⧸ I),
        (∀ i, aeval x (equations i) = 0) ∧ IsUnit (aeval x c) := by
  obtain ⟨u, hu⟩ := hc.exists_left_inv
  have haug := openSystem_seed equations c seed u hseed hu
  have hjaug : IsUnit (Matrix.det (fun i j => aeval (extendedPoint seed u)
      (pderiv i (openSystem equations c j)))) := by
    rw [openSystem_jacobian_det]
    exact hc.mul hjac
  obtain ⟨I, hI, hfinite, hsep, hsol, hj⟩ :=
    ReflectionCoupledFano.square_system_generic_lift (K := K)
      (openSystem equations c) (extendedPoint seed u) haug hjaug hinj
  clear hj
  generalize hcoords : squareGenericCoordinates (K := K) (openSystem equations c) I = z at hsol
  refine ⟨I, hI, hfinite, hsep, (fun i => z (Sum.inr i)), ?_, ?_⟩
  · intro i
    have hi := hsol (Sum.inr i)
    change aeval z (rename (Sum.inr : ι → Unit ⊕ ι) (equations i)) = 0 at hi
    rw [aeval_rename] at hi
    exact hi
  · have hi := hsol (Sum.inl ())
    change aeval z (X (Sum.inl ()) * rename (Sum.inr : ι → Unit ⊕ ι) c - 1) = 0 at hi
    simp only [map_sub, map_mul, aeval_X, map_one, aeval_rename, sub_eq_zero] at hi
    refine ⟨⟨aeval (fun i => z (Sum.inr i)) c, z (Sum.inl ()), ?_, hi⟩, rfl⟩
    exact (mul_comm (aeval (fun i => z (Sum.inr i)) c) (z (Sum.inl ()))).trans hi

end GenericPoint

end CycleQ2OpenSquareLifting

#print axioms CycleQ2OpenSquareLifting.openSystem_jacobian_det
#print axioms CycleQ2OpenSquareLifting.square_system_generic_lift_on_open
end
end


/- Component: continuation_2/SquareAdicLifting.lean -/
section
/-!
Actual adic lifting of square polynomial systems with invertible seed Jacobian.
The proof uses the established étale Jacobian localization and mathlib's
compatible infinitesimal lifts into an adically complete ring.  The seed is
preserved.  No existence of a formal solution is assumed.
-/

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SquareAdicLifting

open MvPolynomial HoldoutConstruction

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual polynomial presentation map into its Jacobian localization. -/
def polynomialToEtale (equations : ι → MvPolynomial ι R) :
    MvPolynomial ι R →ₐ[R] SquareEtaleRing equations :=
  (IsScalarTower.toAlgHom R (SquareSystemRing equations) (SquareEtaleRing equations)).comp
    (Ideal.Quotient.mkₐ R (Ideal.span (Set.range equations)))

@[simp] theorem polynomialToEtale_equation (equations : ι → MvPolynomial ι R) (i : ι) :
    polynomialToEtale equations (equations i) = 0 := by
  have hz : Ideal.Quotient.mk (Ideal.span (Set.range equations)) (equations i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  change algebraMap (SquareSystemRing equations) (SquareEtaleRing equations)
    (Ideal.Quotient.mk _ (equations i)) = 0
  rw [hz, map_zero]

/-- The square system lifts from the residue ring into any complete adic
algebra, while retaining its specified residue coordinates. -/
theorem square_system_adic_lift (equations : ι → MvPolynomial ι R)
    (I : Ideal S) [IsAdicComplete I S] (seed : ι → S ⧸ I)
    (hseed : ∀ i, aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det
      (fun i j => aeval seed (pderiv i (equations j))))) :
    ∃ x : ι → S,
      (∀ i, Ideal.Quotient.mk I (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) := by
  letI : Algebra.Etale R (SquareEtaleRing equations) :=
    square_system_jacobian_etale equations
  let f : SquareEtaleRing equations →ₐ[R] S ⧸ I :=
    squareSystemEtaleEval equations seed hseed hjac
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete f
  let x : ι → S := fun i => g (polynomialToEtale equations (X i))
  have heval : aeval x = g.comp (polynomialToEtale equations) := by
    ext i
    simp [x]
  have hres : f.comp (polynomialToEtale equations) = aeval seed := by
    ext i
    simp [f, polynomialToEtale, squareSystemEtaleEval, squareSystemEval,
      IsLocalization.Away.liftAlgHom, Ideal.Quotient.lift_mk]
  refine ⟨x, ?_, ?_⟩
  · intro i
    have h := AlgHom.congr_fun hg (polynomialToEtale equations (X i))
    change Ideal.Quotient.mk I (x i) = f (polynomialToEtale equations (X i)) at h
    rw [h]
    have hs := AlgHom.congr_fun hres (X i)
    simpa only [AlgHom.comp_apply, aeval_X] using hs
  · intro i
    rw [heval, AlgHom.comp_apply, polynomialToEtale_equation, map_zero]

section PowerSeries

variable {K : Type*} [CommRing K]

/-- Square equations with arbitrary formal coefficients have an actual
formal solution through each nonsingular constant seed.  The hypotheses
are polynomial evaluation and the actual partial-derivative Jacobian. -/
theorem square_system_powerSeries_lift
    (equations : ι → MvPolynomial ι (PowerSeries K)) (seed : ι → K)
    (hseed : ∀ i, eval₂ PowerSeries.constantCoeff seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det (fun i j =>
      eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j))))) :
    ∃ x : ι → PowerSeries K,
      (∀ i, PowerSeries.constantCoeff (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) := by
  letI : Algebra (PowerSeries K) K := PowerSeries.constantCoeff.toAlgebra
  let cc : PowerSeries K →ₐ[PowerSeries K] K :=
    { PowerSeries.constantCoeff with commutes' := by intro r; rfl }
  let I : Ideal (PowerSeries K) := RingHom.ker cc
  have hI : I = Ideal.span {PowerSeries.X} := by
    ext z
    simp only [I, RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    rfl
  letI : IsAdicComplete I (PowerSeries K) := by
    rw [hI]
    infer_instance
  let e : ((PowerSeries K) ⧸ I) ≃ₐ[PowerSeries K] K :=
    Ideal.quotientKerAlgEquivOfSurjective (f := cc) PowerSeries.constantCoeff_surj
  let seed' : ι → (PowerSeries K) ⧸ I := fun i => e.symm (seed i)
  have heval (p : MvPolynomial ι (PowerSeries K)) :
      aeval seed' p = e.symm (eval₂ PowerSeries.constantCoeff seed p) := by
    exact (MvPolynomial.comp_aeval_apply seed e.symm.toAlgHom p).symm
  have hs : ∀ i, aeval seed' (equations i) = 0 := by
    intro i
    rw [heval, hseed i, map_zero]
  have hj : IsUnit (Matrix.det (fun i j => aeval seed' (pderiv i (equations j)))) := by
    simp only [heval]
    have hd :
        Matrix.det (fun i j => e.symm
          (eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))) =
        e.symm (Matrix.det (fun i j =>
          eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))) :=
      (e.symm.toAlgHom.map_det (fun i j =>
        eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))).symm
    rw [hd]
    exact hjac.map e.symm.toRingEquiv.toRingHom
  obtain ⟨x, hx, heq⟩ := square_system_adic_lift equations I seed' hs hj
  refine ⟨x, ?_, heq⟩
  intro i
  have hi := congrArg e (hx i)
  change cc (x i) = e (e.symm (seed i)) at hi
  have hcc (z : PowerSeries K) : cc z = PowerSeries.constantCoeff z := rfl
  simpa only [AlgEquiv.apply_symm_apply, hcc] using hi

end PowerSeries

end CycleQ2SquareAdicLifting

#print axioms CycleQ2SquareAdicLifting.square_system_adic_lift
#print axioms CycleQ2SquareAdicLifting.square_system_powerSeries_lift
end
end


/- Component: continuation_2/SegreFormalLifting.lean -/
section
/-!
# Formal lifting with genuine redundant polynomial equations

A nonsingular square subsystem lifts through its seed. If the residual
polynomials satisfy actual polynomial relations whose complementary block
is invertible at the seed, every omitted equation vanishes along that lift.
All coefficient series may vary: the theorem is not a tangent-only statement.
No seed or minor of the particular large incidence system is assumed proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace CycleQ2SegreFormalLifting

open MvPolynomial Matrix

variable {K ι κ : Type*} [CommRing K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The complete nonlinear system has a seed-preserving formal solution.
The premises concern polynomial identities and the two actual seed minors;
none assumes a formal solution of either the full or square system. -/
theorem lift_all_equations
    (equations : ι → MvPolynomial ι (PowerSeries K))
    (residual : κ → MvPolynomial ι (PowerSeries K))
    (A : Matrix κ κ (MvPolynomial ι (PowerSeries K)))
    (B : Matrix κ ι (MvPolynomial ι (PowerSeries K)))
    (hrelations : A *ᵥ residual + B *ᵥ equations = 0)
    (seed : ι → K)
    (hseed : ∀ i, eval₂ PowerSeries.constantCoeff seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det (fun i j =>
      eval₂ PowerSeries.constantCoeff seed (pderiv i (equations j)))))
    (hcomplement : IsUnit (eval₂ PowerSeries.constantCoeff seed A.det)) :
    ∃ x : ι → PowerSeries K,
      (∀ i, PowerSeries.constantCoeff (x i) = seed i) ∧
      (∀ i, aeval x (equations i) = 0) ∧
      (∀ j, aeval x (residual j) = 0) := by
  obtain ⟨x, hx, heq⟩ :=
    CycleQ2SquareAdicLifting.square_system_powerSeries_lift equations seed hseed hjac
  have hcc (p : MvPolynomial ι (PowerSeries K)) :
      PowerSeries.constantCoeff (aeval x p) = eval₂ PowerSeries.constantCoeff seed p := by
    induction p using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, aeval_X, eval₂_mul, eval₂_X, hp, hx]
  have hunit : IsUnit (aeval x A.det) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [hcc]
    exact hcomplement
  let φ : MvPolynomial ι (PowerSeries K) →+* PowerSeries K :=
    (aeval x).toRingHom
  have heq' : φ ∘ equations = 0 := by
    funext i
    exact heq i
  have hr : φ ∘ residual = 0 :=
    CycleQ2SegreRelations.evaluated_residual_eq_zero
      φ A B residual equations hrelations heq' hunit
  refine ⟨x, hx, heq, ?_⟩
  intro j
  exact congrFun hr j

end CycleQ2SegreFormalLifting

#print axioms CycleQ2SegreFormalLifting.lift_all_equations
end
end
