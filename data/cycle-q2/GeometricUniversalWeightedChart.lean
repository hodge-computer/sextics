import Proposal.GeometricHodgeThreefoldCubicChart
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.MvPolynomial.CommRing
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.HigherResidues.HigherResidue
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.AlgebraicIndependent.Defs

section
/-!
# The normalized sextic on the affine chart `x₀ = 1`

Separating the weight-two coordinate from the three affine base coordinates
writes the actual normalized sextic as a monic cubic. Its tail has degree
at most two over any coefficient ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2MonicWeightedAffineEquation

open MvPolynomial CycleQ2IncidenceNormalForm
open CycleQ2GeometricHodgeThreefoldCubic (baseMonomial expand expand_monomial pack pack_X pack_dehom)

abbrev Coeff := MvPolynomial FullSexticTailIndex ℂ
abbrev Coords (R : Type) [CommRing R] := MvPolynomial (Fin 3) R
abbrev Affine (R : Type) [CommRing R] := Polynomial (Coords R)

variable {R : Type} [CommRing R]

/-- Coordinates on the affine chart, in the order `x₁, x₂, x₃, w`. -/
def chart : MvPolynomial (Fin 5) R →ₐ[R] MvPolynomial (Fin 4) R :=
  aeval (Fin.cases 1 X)

/-- The last affine coordinate is the indeterminate over the first three. -/
abbrev separate : MvPolynomial (Fin 4) R ≃ₐ[R] Affine R := pack

theorem separate_castSucc (j : Fin 3) :
    separate (X j.castSucc : MvPolynomial (Fin 4) R) = Polynomial.C (X j) := by
  rw [separate, pack_X, Fin.snoc_castSucc]

theorem separate_last :
    separate (X (Fin.last 3) : MvPolynomial (Fin 4) R) = Polynomial.X := by
  rw [separate, pack_X, Fin.snoc_last]

theorem chart_eq_dehom : chart (R := R) = CycleQ2HodgeEuler.dehom 0 := by
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [chart, CycleQ2HodgeEuler.dehom]

theorem separate_chart : (separate (R := R)).toAlgHom.comp chart = expand 0 := by
  apply AlgHom.ext
  intro p
  exact (congrArg separate (DFunLike.congr_fun chart_eq_dehom p)).trans (pack_dehom 0 p)

def equation (c : FullSexticTailIndex → R) : Affine R :=
  expand 0 (normalizedFullSextic c)

theorem separate_chart_equation (c : FullSexticTailIndex → R) :
    separate (chart (normalizedFullSextic c)) = equation c :=
  DFunLike.congr_fun (separate_chart (R := R)) _

def tail (c : FullSexticTailIndex → R) : Affine R :=
  ∑ e : FullSexticTailIndex, Polynomial.monomial (e.val.val 4).val
    (baseMonomial 0 (fullExponentOf e.val.val) (c e))

theorem equation_eq (c : FullSexticTailIndex → R) :
    equation c = Polynomial.X ^ 3 + tail c := by
  simp only [equation, normalizedFullSextic, map_add, map_sum, expand_monomial, tail,
    fullExponentOf_apply, Finsupp.single_eq_same]
  congr 1
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  have hz (j : Fin 4) : Finsupp.single (4 : Fin 5) (3 : ℕ) j.castSucc = 0 :=
    Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j)
  simp [baseMonomial, hz]

theorem tail_degree (c : FullSexticTailIndex → R) : (tail c).degree < 3 := by
  apply (Polynomial.degree_sum_le _ _).trans_lt
  refine (Finset.sup_lt_iff (show (⊥ : WithBot ℕ) < 3 by decide)).mpr ?_
  intro e _
  exact (Polynomial.degree_monomial_le _ _).trans_lt (WithBot.coe_lt_coe.mpr e.property)

theorem monic (c : FullSexticTailIndex → R) : (equation c).Monic := by
  rw [equation_eq]
  exact Polynomial.monic_X_pow_add (tail_degree c)

theorem natDegree [Nontrivial R] (c : FullSexticTailIndex → R) : (equation c).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [equation_eq, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact (tail_degree c).trans_le (by norm_num)

abbrev universalEquation : Affine Coeff := equation (fun e : FullSexticTailIndex => (X e : Coeff))

end CycleQ2MonicWeightedAffineEquation

end

#print axioms CycleQ2MonicWeightedAffineEquation.separate_chart_equation
#print axioms CycleQ2MonicWeightedAffineEquation.monic
#print axioms CycleQ2MonicWeightedAffineEquation.natDegree
end

section
/-!
# Integrality of the universal affine weighted sextic

The coefficient of the pure sixth power of the chart coordinate varies
independently. Giving it value `T` and setting all other tails to zero
specializes the monic equation to `w³ + T`, Eisenstein at `T`.
Monic specialization reflects irreducibility over the full parameter ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2MonicWeightedAffineEquation

open MvPolynomial CycleQ2IncidenceNormalForm
open CycleQ2GeometricHodgeThreefoldCubic (baseValue baseMonomial)

def constantIndex : FullSexticTailIndex :=
  ⟨⟨![6, 0, 0, 0, 0], by decide⟩, by decide⟩

private def coefficientValue (e : FullSexticTailIndex) : Polynomial ℂ :=
  if e = constantIndex then Polynomial.X else 0

private def specializeCoeff : Coeff →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C coefficientValue

def specialize : Coords Coeff →+* Polynomial ℂ :=
  eval₂Hom specializeCoeff (fun _ => 1)

private theorem specialize_baseValue (i : Fin 4) :
    specialize (baseValue 0 i) = 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [baseValue]
  · simp [baseValue, specialize]

private theorem specialize_baseMonomial (e : FullSexticTailIndex) :
    specialize (baseMonomial 0 (fullExponentOf e.val.val) (X e)) = coefficientValue e := by
  simp only [baseMonomial, map_mul, map_prod, map_pow, specialize_baseValue, one_pow, Finset.prod_const_one,
    mul_one]
  simp [specialize, specializeCoeff]

theorem universalEquation_specialize :
    universalEquation.map specialize = Polynomial.X ^ 3 + Polynomial.C Polynomial.X := by
  classical
  rw [universalEquation, equation_eq, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X]
  congr 1
  simp only [tail, Polynomial.map_sum, Polynomial.map_monomial, specialize_baseMonomial]
  rw [Finset.sum_eq_single constantIndex]
  · simp [coefficientValue, constantIndex]
  · intro e _ he
    simp [coefficientValue, he]
  · simp

theorem universalEquation_irreducible : Irreducible universalEquation := by
  apply (monic (fun e : FullSexticTailIndex => (X e : Coeff))).irreducible_of_irreducible_map specialize
  rw [universalEquation_specialize]
  exact HoldoutConstruction.irreducible_power_add_constant (Polynomial.X : Polynomial ℂ)
    (by simp) (by simp) 3 (by decide)

instance universalEquation_domain : IsDomain (AdjoinRoot universalEquation) :=
  AdjoinRoot.isDomain_of_prime universalEquation_irreducible.prime

section

/-- A parameter with only the coefficient of the pure sixth power of the
first spatial coordinate nonzero. -/
private def spatialIndex : FullSexticTailIndex :=
  ⟨⟨![0, 6, 0, 0, 0], by decide⟩, by decide⟩

private def spatialCoefficient : Coeff →+* ℂ :=
  eval (fun e => if e = spatialIndex then 1 else 0)

private def spatialBase : Coords Coeff →+* ℂ :=
  eval₂Hom spatialCoefficient (fun _ => 1)

private def spatialPoint : Fin 4 → ℂ := Fin.snoc (fun _ => 1) (-1)

private theorem separate_eval (p : MvPolynomial (Fin 4) Coeff) :
    (separate p).eval₂ spatialBase (-1) = eval spatialPoint (MvPolynomial.map spatialCoefficient p) := by
  suffices h : (Polynomial.eval₂RingHom spatialBase (-1)).comp separate.toRingHom =
      (eval spatialPoint).comp (MvPolynomial.map spatialCoefficient) from DFunLike.congr_fun h p
  apply MvPolynomial.ringHom_ext
  · intro a
    change (separate (C a)).eval₂ spatialBase (-1) = _
    rw [show separate (C a) = Polynomial.C (C a) from separate.commutes a]
    simp [spatialBase]
  · intro i
    change (separate (X i)).eval₂ spatialBase (-1) = _
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [separate_last]
      simp [spatialPoint, Fin.snoc]
    · rw [separate_castSucc]
      simp [spatialBase, spatialPoint]

private theorem spatial_chart :
    MvPolynomial.map spatialCoefficient (chart (normalizedFullSextic (fun e => (X e : Coeff)))) =
      (X 3 : MvPolynomial (Fin 4) ℂ)^3 + X 0^6 := by
  classical
  have hchart : (MvPolynomial.map spatialCoefficient (σ := Fin 4)).comp chart.toRingHom =
      chart.toRingHom.comp (MvPolynomial.map spatialCoefficient (σ := Fin 5)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [chart]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [chart]
  have hf : MvPolynomial.map spatialCoefficient (normalizedFullSextic (fun e => (X e : Coeff))) =
      (X 4 : MvPolynomial (Fin 5) ℂ)^3 + X 1^6 := by
    rw [CycleQ2UniversalSurfaceCoefficientMap.map_sextic, normalizedFullSextic]
    simp only [spatialCoefficient, eval_X]
    rw [Finset.sum_eq_single spatialIndex]
    · have he : fullExponentOf spatialIndex.val.val = Finsupp.single 1 6 := by
        ext i
        fin_cases i <;> simp [spatialIndex]
      simp [he, X_pow_eq_monomial]
    · intro e _ he
      simp [he]
    · simp
  have h4 : Fin.cases (motive := fun _ : Fin 5 => MvPolynomial (Fin 4) ℂ)
      1 X 4 = X 3 := by
    rw [show (4 : Fin 5) = (3 : Fin 4).succ from by decide, Fin.cases_succ]
  have h1 : Fin.cases (motive := fun _ : Fin 5 => MvPolynomial (Fin 4) ℂ)
      1 X 1 = X 0 := by
    rw [show (1 : Fin 5) = (0 : Fin 4).succ from by decide, Fin.cases_succ]
  have h := DFunLike.congr_fun hchart (normalizedFullSextic (fun e => (X e : Coeff)))
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    hf, map_add, map_pow, chart, aeval_X, h4, h1] using h

theorem normal_nonzero :
    AdjoinRoot.mk universalEquation
      (separate (pderiv 0 (chart (normalizedFullSextic (fun e => (X e : Coeff)))))) ≠ 0 := by
  have hroot : universalEquation.eval₂ spatialBase (-1) = 0 := by
    rw [show universalEquation = separate (chart (normalizedFullSextic (fun e => (X e : Coeff)))) from
      (separate_chart_equation _).symm, separate_eval, spatial_chart]
    norm_num [spatialPoint, Fin.snoc]
  intro he
  have hp := congrArg (AdjoinRoot.lift spatialBase (-1) hroot) he
  rw [AdjoinRoot.lift_mk, map_zero, separate_eval, ← pderiv_map, spatial_chart] at hp
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  norm_num [pderiv_pow, pderiv_X, Pi.single_apply, spatialPoint, Fin.snoc, h30] at hp

end

end CycleQ2MonicWeightedAffineEquation

end

#print axioms CycleQ2MonicWeightedAffineEquation.universalEquation_irreducible
#print axioms CycleQ2MonicWeightedAffineEquation.universalEquation_domain
#print axioms CycleQ2MonicWeightedAffineEquation.normal_nonzero
end

section
/-!
# Specializing finitely many rational functions on a monic cubic chart

The denominator is an element of the hypersurface ring. Its remainder after division
by the equation has three coefficients in the spatial variables. A nonzero scalar
coefficient of one of these polynomials controls specialization of the denominator.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2MonicWeightedDenominator
open scoped nonZeroDivisors
open Polynomial

abbrev Spatial (A : Type*) [CommRing A] := MvPolynomial (Fin 3) A

variable {A B : Type*} [CommRing A] [CommRing B]

abbrev fiber (φ : A →+* B) (f : Polynomial (Spatial A)) := f.map (MvPolynomial.map φ)

def specialize (φ : A →+* B) (f : Polynomial (Spatial A)) :
    AdjoinRoot f →+* AdjoinRoot (fiber φ f) :=
  Ideal.quotientMap _ (Polynomial.mapRingHom (MvPolynomial.map φ)) (by
    apply Ideal.span_le.mpr
    rintro _ (rfl : _ = f)
    exact Ideal.subset_span (Set.mem_singleton _))

@[simp] theorem specialize_mk (φ : A →+* B) (f p : Polynomial (Spatial A)) :
    specialize φ f (AdjoinRoot.mk f p) = AdjoinRoot.mk (fiber φ f) (fiber φ p) := rfl

def slot {f : Polynomial (Spatial A)} (hf : f.Monic) (x : AdjoinRoot f) (i : Fin 3) :
    Spatial A := (AdjoinRoot.modByMonicHom hf x).coeff i.val

theorem slot_specialize (φ : A →+* B) {f : Polynomial (Spatial A)} (hf : f.Monic)
    (x : AdjoinRoot f) (i : Fin 3) :
    slot (hf.map (MvPolynomial.map φ)) (specialize φ f x) i = MvPolynomial.map φ (slot hf x i) := by
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
  change ((AdjoinRoot.modByMonicHom (hf.map (MvPolynomial.map φ)))
      (AdjoinRoot.mk _ (p.map (MvPolynomial.map φ)))).coeff i.val =
    MvPolynomial.map φ (((AdjoinRoot.modByMonicHom hf) (AdjoinRoot.mk f p)).coeff i.val)
  rw [AdjoinRoot.modByMonicHom_mk,AdjoinRoot.modByMonicHom_mk,← Polynomial.map_modByMonic _ hf,
    Polynomial.coeff_map]

theorem exists_detecting_coefficient {f : Polynomial (Spatial A)} (hf : f.Monic)
    (hd : f.natDegree = 3) (x : AdjoinRoot f) (hx : x ≠ 0) :
    ∃ (i : Fin 3) (m : Fin 3 →₀ ℕ), (slot hf x i).coeff m ≠ 0 ∧
      ∀ {B : Type*} [CommRing B] (φ : A →+* B),
        φ ((slot hf x i).coeff m) ≠ 0 → specialize φ f x ≠ 0 := by
  have ex : ∃ j : Fin f.natDegree, (AdjoinRoot.powerBasisAux' hf).repr x j ≠ 0 := by
    by_contra! h
    apply hx
    apply (AdjoinRoot.powerBasisAux' hf).repr.injective
    rw [map_zero]
    apply Finsupp.ext
    intro j
    exact h j
  obtain ⟨j,hj⟩ := ex
  let i : Fin 3 := ⟨j.val, lt_of_lt_of_eq j.isLt hd⟩
  have hs : slot hf x i ≠ 0 := by
    change ((AdjoinRoot.modByMonicHom hf) x).coeff j.val ≠ 0
    simpa only [AdjoinRoot.powerBasisAux'_repr_apply_to_fun] using hj
  obtain ⟨m,hm⟩ := MvPolynomial.exists_coeff_ne_zero hs
  refine ⟨i,m,hm,?_⟩
  intro B _ φ hφ he
  apply hφ
  rw [← MvPolynomial.coeff_map, ← slot_specialize, he]
  change MvPolynomial.coeff m (((AdjoinRoot.modByMonicHom (hf.map (MvPolynomial.map φ)))
    (0 : AdjoinRoot (f.map (MvPolynomial.map φ)))).coeff i.val) = 0
  rw [(AdjoinRoot.modByMonicHom (hf.map (MvPolynomial.map φ))).map_zero,
    Polynomial.coeff_zero, MvPolynomial.coeff_zero]

/-- In the integral cubic chart, a nonzero denominator divides a nonzero
polynomial involving just the three independent spatial coordinates. -/
theorem exists_spatial_multiple {f : Polynomial (Spatial A)} [Nontrivial A]
    [IsDomain (AdjoinRoot f)] (hf : f.Monic) (d : AdjoinRoot f) (hd : d ≠ 0) :
    ∃ (q : Spatial A) (m : Fin 3 →₀ ℕ), q.coeff m ≠ 0 ∧ d ∣ AdjoinRoot.of f q := by
  let I : Ideal (AdjoinRoot f) := Ideal.span {d}
  letI := hf.finite_adjoinRoot
  have hi := Ideal.comap_ne_bot_of_integral_mem (R := Spatial A) (I := I) hd
    (Ideal.subset_span (Set.mem_singleton d)) (Algebra.IsIntegral.isIntegral d)
  obtain ⟨q,hq,hn⟩ := (I.comap (algebraMap (Spatial A) (AdjoinRoot f))).ne_bot_iff.mp hi
  obtain ⟨m,hm⟩ := MvPolynomial.exists_coeff_ne_zero hn
  exact ⟨q,m,hm,Ideal.mem_span_singleton.mp hq⟩

/-- Clear every coefficient of the input rational functions by one regular
element of the cubic chart. Its nonvanishing after specialization is detected
on a principal open of the coefficient base. -/
theorem spread_fractions {f : Polynomial (Spatial A)} [Nontrivial (AdjoinRoot f)]
    (hf : f.Monic) (hd : f.natDegree = 3) {ι : Type*} [Finite ι]
    (x : ι → FractionRing (AdjoinRoot f)) :
    ∃ (d : (AdjoinRoot f)⁰) (n : ι → AdjoinRoot f) (a : A), a ≠ 0 ∧
      (∀ i, algebraMap _ (FractionRing (AdjoinRoot f)) (n i) =
        algebraMap _ (FractionRing (AdjoinRoot f)) d.val * x i) ∧
      ∀ {B : Type*} [CommRing B] (φ : A →+* B), φ a ≠ 0 → specialize φ f d.val ≠ 0 := by
  classical
  obtain ⟨d,hdx⟩ := IsLocalization.exist_integer_multiples_of_finite (AdjoinRoot f)⁰ x
  choose n hn using hdx
  obtain ⟨i,m,ha,hφ⟩ := exists_detecting_coefficient hf hd d.val (nonZeroDivisors.coe_ne_zero d)
  refine ⟨d,n,(slot hf d.val i).coeff m,ha,?_,hφ⟩
  intro i
  simpa only [Algebra.smul_def] using hn i

end CycleQ2MonicWeightedDenominator
end

#print axioms CycleQ2MonicWeightedDenominator.exists_detecting_coefficient
#print axioms CycleQ2MonicWeightedDenominator.spread_fractions
#print axioms CycleQ2MonicWeightedDenominator.exists_spatial_multiple
end

section
/-!
# A polynomial identity for a primitive of the weighted pole-three residue

On the chart with coordinates (s₁,s₂,s₃,w), eliminate s₁ using its normal
derivative. The three operators are the actual implicit tangent derivations
of the hypersurface function field. For three rational primitive coefficients
with a shared denominator, their divergence equation is equivalent to a
polynomial multiple of the defining equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2MonicWeightedPrimitiveIdentity

open MvPolynomial
abbrev Pol (A : Type*) [CommRing A] := MvPolynomial (Fin 4) A
variable {A B : Type*} [CommRing A] [CommRing B]

def b : Pol A := X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2 * X 3 ^ 2

def normal (f : Pol A) := pderiv 0 f

def tangentNumerator (f : Pol A) (j : Fin 3) (p : Pol A) :=
  normal f * pderiv j.succ p - pderiv j.succ f * normal p

def primitiveNumerator (f d : Pol A) (p : Fin 3 → Pol A) :=
  ∑ j, (tangentNumerator f j (p j) * d - p j * tangentNumerator f j d)

def sourceNumerator (f : Pol A) :=
  normal (normal b) * (normal f)^2 -
    (3 * normal b * normal (normal f) + b * normal (normal (normal f))) * normal f +
    3 * b * (normal (normal f))^2

def cleared (f d : Pol A) (p : Fin 3 → Pol A) :=
  2 * (normal f)^4 * primitiveNumerator f d p - d^2 * sourceNumerator f

theorem map_cleared (φ : A →+* B) (f d : Pol A) (p : Fin 3 → Pol A) :
    MvPolynomial.map φ (cleared f d p) =
      cleared (MvPolynomial.map φ f) (MvPolynomial.map φ d) (fun j => MvPolynomial.map φ (p j)) := by
  simp [cleared, primitiveNumerator, tangentNumerator, sourceNumerator, normal, b,
    ← MvPolynomial.pderiv_map, map_sum]

private theorem density_iff {K : Type*} [Field K] [CharZero K]
    (T d n a a₁ a₂ n₁ n₂ : K) (hn : n ≠ 0) (hd : d ≠ 0) :
    T / (n * d^2) = SplitHigherResidue.normalSourceTwo a a₁ a₂ n n₁ n₂ / n ↔
      2*n^4*T - d^2 * (a₂*n^2 - (3*a₁*n₁+a*n₂)*n + 3*a*n₁^2) = 0 := by
  have he : 2*n^5*d^2 * (T / (n*d^2) -
      SplitHigherResidue.normalSourceTwo a a₁ a₂ n n₁ n₂ / n) =
        2*n^4*T - d^2 * (a₂*n^2 - (3*a₁*n₁+a*n₂)*n + 3*a*n₁^2) := by
    unfold SplitHigherResidue.normalSourceTwo
    field_simp [hn,hd]
  have coeff_ne : 2*n^5*d^2 ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (pow_ne_zero _ hn)) (pow_ne_zero _ hd)
  rw [← he, mul_eq_zero, or_iff_right coeff_ne, sub_eq_zero]

def density {K : Type*} [Field K] (v : Pol A →+* K) (f : Pol A) :=
  SplitHigherResidue.normalSourceTwo (v b) (v (normal b)) (v (normal (normal b)))
    (v (normal f)) (v (normal (normal f))) (v (normal (normal (normal f)))) / v (normal f)

/-- The pole-three divergence identity over an arbitrary field of evaluation.
The coordinate rule identifies the derivations on polynomial classes; the
quotient rule determines them on the spatial rational functions. -/
theorem divergence_iff_cleared {R K : Type*} [CommRing R] [Field K] [CharZero K] [Algebra R K]
    (v : Pol A →+* K) (D : Fin 3 → Derivation R K K) (f d : Pol A) (p : Fin 3 → Pol A)
    (hn : v (normal f) ≠ 0) (hd : v d ≠ 0)
    (hD : ∀ j q, D j (v q) = v (pderiv j.succ q) -
      v (pderiv j.succ f) / v (normal f) * v (normal q)) :
    (∑ j, D j (v (p j) / v d)) = density v f ↔ v (cleared f d p) = 0 := by
  have step (j : Fin 3) :
      D j (v (p j) / v d) =
        v (tangentNumerator f j (p j) * d - p j * tangentNumerator f j d) /
          (v (normal f) * v d ^ 2) := by
    rw [Derivation.leibniz_div, hD, hD]
    simp only [tangentNumerator, map_sub, map_mul, smul_eq_mul]
    field_simp [hn,hd]
  simp_rw [step]
  rw [← Finset.sum_div, ← map_sum]
  change v (primitiveNumerator f d p) / (v (normal f) * v d^2) = _ ↔ _
  rw [density, density_iff _ _ _ _ _ _ _ _ hn hd]
  simp only [cleared, sourceNumerator, map_sub, map_add, map_mul, map_pow, map_ofNat]

section Field
variable {S K : Type*} [CommRing S] [IsDomain S] [Field K] [CharZero K]
  [Algebra S K] [IsFractionRing S K]
variable (π : Pol A →+* S) (surj : Function.Surjective π) (f : Pol A)
  (kernel : ∀ q, π q = 0 ↔ f ∣ q)

def value : Pol A →+* K := (algebraMap S K).comp π

variable (hn : value (K := K) π (normal f) ≠ 0)

def tangent (j : Fin 3) : Derivation ℤ K K :=
  HoldoutConstruction.residueTangent π surj ((pderiv 0).restrictScalars ℤ)
    ((pderiv j.succ).restrictScalars ℤ) f kernel hn

omit [CharZero K] in
theorem tangent_apply (j : Fin 3) (q : Pol A) :
    tangent π surj f kernel hn j (value π q) =
      value π (pderiv j.succ q) - value π (pderiv j.succ f) / value π (normal f) * value π (normal q) :=
  HoldoutConstruction.residueTangent_apply π surj _ _ f kernel hn q

theorem primitive_iff_divides (p : Fin 3 → Pol A) (d : Pol A) (hd : value (K := K) π d ≠ 0) :
    (∑ j, tangent π surj f kernel hn j (value π (p j) / value π d)) = density (value π) f ↔
      f ∣ cleared f d p := by
  rw [divergence_iff_cleared (value π) (tangent π surj f kernel hn) f d p hn hd
    (tangent_apply π surj f kernel hn), ← kernel]
  exact IsFractionRing.to_map_eq_zero_iff

end Field
end CycleQ2MonicWeightedPrimitiveIdentity
end

#print axioms CycleQ2MonicWeightedPrimitiveIdentity.divergence_iff_cleared
#print axioms CycleQ2MonicWeightedPrimitiveIdentity.primitive_iff_divides
#print axioms CycleQ2MonicWeightedPrimitiveIdentity.map_cleared
end

section
/-!
# The principal open of a rational primitive

Starting with three rational coefficients in the generic hypersurface, take one
common spatial denominator and record a base coefficient detecting it. A second
base coefficient detects the normal to the chart. The same polynomial numerators
and denominator specialize throughout their intersection. On every integral
characteristic-zero fiber there they again give a rational primitive.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2MonicWeightedPrimitiveSpecialization

open MvPolynomial CycleQ2MonicWeightedAffineEquation
open CycleQ2MonicWeightedPrimitiveIdentity
open CycleQ2MonicWeightedDenominator (fiber slot)
open scoped nonZeroDivisors
variable {A B : Type} [CommRing A] [CommRing B]

abbrev ChartRing (f : Pol A) := AdjoinRoot (separate f)
abbrev Fld (f : Pol A) := FractionRing (ChartRing f)

def projection (f : Pol A) : Pol A →+* ChartRing f :=
  (AdjoinRoot.mk _).comp separate.toRingEquiv.toRingHom

theorem projection_surjective (f : Pol A) : Function.Surjective (projection f) :=
  AdjoinRoot.mk_surjective.comp separate.surjective

theorem projection_kernel (f q : Pol A) : projection f q = 0 ↔ f ∣ q := by
  change AdjoinRoot.mk _ (separate q) = 0 ↔ _
  rw [AdjoinRoot.mk_eq_zero]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨separate.symm p, separate.injective (by simpa only [map_mul, AlgEquiv.apply_symm_apply] using hp)⟩
  · rintro ⟨p,rfl⟩
    exact ⟨separate p, map_mul _ _ _⟩

theorem separate_map (φ : A →+* B) (q : Pol A) :
    separate (MvPolynomial.map φ q) = fiber φ (separate q) := by
  have hC {R : Type} [CommRing R] (a : R) :
      separate (C a : Pol R) = Polynomial.C (C a) := separate.commutes a
  have hX (j : Fin 4) : separate (X j : Pol B) = fiber φ (separate (X j : Pol A)) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [separate_last, fiber, Polynomial.map_X]
    · simp only [separate_castSucc, fiber, Polynomial.map_C, MvPolynomial.map_X]
  induction q using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.map_C, hC, fiber, Polynomial.map_C]
  | add p q hp hq => simp only [map_add, hp, hq, fiber, Polynomial.map_add]
  | mul_X p j hp => simp only [map_mul, MvPolynomial.map_X, hp, hX, fiber, Polynomial.map_mul]

private theorem specialization_nonzero (φ : A →+* B) (f q : Pol A)
    (h : CycleQ2MonicWeightedDenominator.specialize φ (separate f) (projection f q) ≠ 0) :
    projection (MvPolynomial.map φ f) (MvPolynomial.map φ q) ≠ 0 := by
  intro he
  apply h
  change AdjoinRoot.mk _ (fiber φ (separate q)) = 0
  apply AdjoinRoot.mk_eq_zero.mpr
  simpa only [← separate_map] using
    (AdjoinRoot.mk_eq_zero.mp he : separate (MvPolynomial.map φ f) ∣ separate (MvPolynomial.map φ q))

def fieldValue (f : Pol A) [IsDomain (ChartRing f)] : Pol A →+* Fld f :=
  value (K := Fld f) (projection f)

def direction (f : Pol A) [IsDomain (ChartRing f)] [CharZero (Fld f)]
    (hn : fieldValue f (normal f) ≠ 0) (j : Fin 3) :=
  tangent (K := Fld f) (projection f) (projection_surjective f) f (projection_kernel f) hn j

/-- Extract a single principal open and polynomial representatives from the
actual input elements of the function field and their divergence identity. -/
theorem spread {f : Pol A} [IsDomain A] [IsDomain (ChartRing f)] [CharZero (Fld f)]
    (hm : (separate f).Monic) (h3 : (separate f).natDegree = 3)
    (hn : fieldValue f (normal f) ≠ 0) (v : Fin 3 → Fld f)
    (hv : (∑ j, direction f hn j (v j)) = density (fieldValue f) f) :
    ∃ (a : A) (d : Pol A) (p : Fin 3 → Pol A), a ≠ 0 ∧
      (∀ j, v j = fieldValue f (p j) / fieldValue f d) ∧ f ∣ cleared f d p ∧
      ∀ {B : Type} [CommRing B] (φ : A →+* B), φ a ≠ 0 →
        projection (MvPolynomial.map φ f) (MvPolynomial.map φ d) ≠ 0 ∧
        projection (MvPolynomial.map φ f) (normal (MvPolynomial.map φ f)) ≠ 0 := by
  classical
  obtain ⟨d,n,a,ha,hnumer,hspec⟩ := CycleQ2MonicWeightedDenominator.spread_fractions hm h3 v
  obtain ⟨q,hq⟩ := projection_surjective f d.val
  choose p hp using fun j => projection_surjective f (n j)
  have hd : fieldValue f q ≠ 0 := by
    change algebraMap (ChartRing f) (Fld f) (projection f q) ≠ 0
    rw [hq]
    exact (IsFractionRing.to_map_eq_zero_iff).not.mpr (nonZeroDivisors.coe_ne_zero d)
  have frac (j : Fin 3) : v j = fieldValue f (p j) / fieldValue f q := by
    apply (eq_div_iff hd).mpr
    change v j * algebraMap _ (Fld f) (projection f q) = algebraMap _ (Fld f) (projection f (p j))
    rw [hq,hp,mul_comm,← hnumer j]
  have hnormal : projection f (normal f) ≠ 0 := by
    intro he
    apply hn
    exact (congrArg (algebraMap (ChartRing f) (Fld f)) he).trans (map_zero _)
  obtain ⟨i,m,hb,hs⟩ := CycleQ2MonicWeightedDenominator.exists_detecting_coefficient hm h3
    (projection f (normal f)) hnormal
  refine ⟨a * (slot hm (projection f (normal f)) i).coeff m,q,p,mul_ne_zero ha hb,frac,?_,?_⟩
  · apply (primitive_iff_divides (K := Fld f) (projection f) (projection_surjective f) f (projection_kernel f) hn p q hd).mp
    change (∑ j, direction f hn j (fieldValue f (p j) / fieldValue f q)) =
      density (fieldValue f) f
    simp only [frac] at hv
    exact hv
  · intro B _ φ hφ
    rw [map_mul] at hφ
    constructor
    · apply specialization_nonzero
      rw [hq]
      exact hspec φ (left_ne_zero_of_mul hφ)
    · rw [normal,MvPolynomial.pderiv_map]
      exact specialization_nonzero φ f (normal f) (hs φ (right_ne_zero_of_mul hφ))

/-- The spatial multiple remains nonzero at each generic point of the three
weight-one coordinates. This also controls evaluation on the ordinary double
cover of the weighted pencil. -/
theorem spread_with_spatial_multiple {f : Pol A} [IsDomain A] [IsDomain (ChartRing f)]
    [CharZero (Fld f)] (hm : (separate f).Monic) (h3 : (separate f).natDegree = 3)
    (hn : fieldValue f (normal f) ≠ 0) (v : Fin 3 → Fld f)
    (hv : (∑ j, direction f hn j (v j)) = density (fieldValue f) f) :
    ∃ (a : A) (d : Pol A) (p : Fin 3 → Pol A) (q : Coords A), a ≠ 0 ∧
      (∀ j, v j = fieldValue f (p j) / fieldValue f d) ∧ f ∣ cleared f d p ∧
      projection f d ∣ AdjoinRoot.of (separate f) q ∧
      ∀ {B : Type} [CommRing B] (φ : A →+* B), φ a ≠ 0 →
        MvPolynomial.map φ q ≠ 0 ∧
        projection (MvPolynomial.map φ f) (normal (MvPolynomial.map φ f)) ≠ 0 := by
  obtain ⟨a,d,p,ha,hv',hdiv,hspec⟩ := spread hm h3 hn v hv
  have hd : projection f d ≠ 0 := by
    have h : ∀ f d : Pol A, projection (MvPolynomial.map (RingHom.id A) f)
        (MvPolynomial.map (RingHom.id A) d) ≠ 0 → projection f d ≠ 0 := by
      intro f d
      rw [MvPolynomial.map_id, MvPolynomial.map_id]
      exact id
    exact h f d (hspec (RingHom.id A) ha).1
  obtain ⟨q,m,hq,hD⟩ := CycleQ2MonicWeightedDenominator.exists_spatial_multiple hm _ hd
  refine ⟨a * q.coeff m,d,p,q,mul_ne_zero ha hq,hv',hdiv,hD,?_⟩
  intro B _ φ hφ
  rw [map_mul] at hφ
  refine ⟨?_,(hspec φ (left_ne_zero_of_mul hφ)).2⟩
  intro h
  apply right_ne_zero_of_mul hφ
  rw [← MvPolynomial.coeff_map, h, MvPolynomial.coeff_zero]

theorem separate_spatial (q : Coords A) :
    separate (MvPolynomial.rename Fin.castSucc q) = Polynomial.C q := by
  induction q using MvPolynomial.induction_on with
  | C c => rw [rename_C]; exact separate.commutes c
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, rename_X, hp]
    exact congrArg (fun z => Polynomial.C p * z) (separate_castSucc (R := A) j)

/-- Evaluate the cubic quotient at an actual weighted point. -/
def evaluate {L : Type} [CommRing L] {f : Pol A} (v : Pol A →+* L) (hf : v f = 0) :
    ChartRing f →+* L :=
  Ideal.Quotient.lift _ (v.comp separate.symm.toRingEquiv.toRingHom) (by
    intro p hp
    obtain ⟨q,rfl⟩ := Ideal.mem_span_singleton.mp hp
    change v (separate.symm (separate f * q)) = 0
    rw [map_mul, AlgEquiv.symm_apply_apply, map_mul, hf, zero_mul])

@[simp] theorem evaluate_projection {L : Type} [CommRing L] {f : Pol A} (v : Pol A →+* L)
    (hf : v f = 0) (p : Pol A) : evaluate v hf (projection f p) = v p := by
  change v (separate.symm (separate p)) = v p
  rw [AlgEquiv.symm_apply_apply]

/-- The spatial multiple protects the actual denominator in any weighted
point with algebraically independent spatial coordinates over its coefficients. -/
theorem evaluated_denominator_ne_zero {L : Type} [Field L] [Algebra B L]
    {f d : Pol A} {q : Coords A} (H : projection f d ∣ AdjoinRoot.of (separate f) q)
    (φ : A →+* B) (hq : MvPolynomial.map φ q ≠ 0)
    (v : Pol A →+* L) (hf : v f = 0) (x : Fin 3 → L)
    (hx : AlgebraicIndependent B x) (hc : ∀ a, v (C a) = algebraMap B L (φ a))
    (hX : ∀ j : Fin 3, v (X j.castSucc) = x j) : v d ≠ 0 := by
  have hval (r : Coords A) : v (rename Fin.castSucc r) = aeval x (MvPolynomial.map φ r) := by
    induction r using MvPolynomial.induction_on with
    | C c => simp only [rename_C, MvPolynomial.map_C, aeval_C, hc]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp => simp only [map_mul, rename_X, MvPolynomial.map_X, aeval_X, hp, hX]
  have he : AdjoinRoot.of (separate f) q = projection f (rename Fin.castSucc q) :=
    congrArg (AdjoinRoot.mk (separate f)) (separate_spatial q).symm
  obtain ⟨k,hk⟩ := H
  have hk' := congrArg (evaluate v hf) hk
  rw [he,map_mul,evaluate_projection,evaluate_projection,hval] at hk'
  intro h
  rw [h,zero_mul] at hk'
  exact hq (hx.eq_zero_of_aeval_eq_zero _ hk')

/-- Evaluate the same rational primitive on the chosen fiber, preserving the
normal density and its second-order derivatives. -/
theorem specialize_primitive {f d : Pol A} {p : Fin 3 → Pol A}
    (H : f ∣ cleared f d p) (φ : A →+* B)
    [IsDomain (ChartRing (MvPolynomial.map φ f))] [CharZero (Fld (MvPolynomial.map φ f))]
    (hn : fieldValue (MvPolynomial.map φ f) (normal (MvPolynomial.map φ f)) ≠ 0)
    (hd : projection (MvPolynomial.map φ f) (MvPolynomial.map φ d) ≠ 0) :
    (∑ j, direction (MvPolynomial.map φ f) hn j
      (fieldValue (MvPolynomial.map φ f) (MvPolynomial.map φ (p j)) /
       fieldValue (MvPolynomial.map φ f) (MvPolynomial.map φ d))) =
      density (fieldValue (MvPolynomial.map φ f)) (MvPolynomial.map φ f) := by
  apply (primitive_iff_divides (K := Fld (MvPolynomial.map φ f)) _ (projection_surjective _) _ (projection_kernel _) hn _ _
    (IsFractionRing.to_map_eq_zero_iff.not.mpr hd)).mpr
  simpa only [map_cleared] using map_dvd (MvPolynomial.map φ) H

end CycleQ2MonicWeightedPrimitiveSpecialization
end

#print axioms CycleQ2MonicWeightedPrimitiveSpecialization.spread
#print axioms CycleQ2MonicWeightedPrimitiveSpecialization.spread_with_spatial_multiple
#print axioms CycleQ2MonicWeightedPrimitiveSpecialization.evaluated_denominator_ne_zero
#print axioms CycleQ2MonicWeightedPrimitiveSpecialization.specialize_primitive
end

section
/-!
# Rational primitives on the universal monic weighted hypersurface

The normalized affine equation is a monic cubic over a polynomial ring in
three spatial coordinates and the universal coefficients. Its nonzero first
spatial derivative defines the three tangent derivations of the function field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GenericWeightedSpatialDenominator

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2MonicWeightedAffineEquation
  CycleQ2MonicWeightedPrimitiveIdentity

abbrev universalAffine : Pol Coeff :=
  chart (normalizedFullSextic (fun e : FullSexticTailIndex => (X e : Coeff)))

end CycleQ2GenericWeightedSpatialDenominator

namespace CycleQ2UniversalWeightedTransfer

open MvPolynomial CycleQ2MonicWeightedAffineEquation CycleQ2MonicWeightedPrimitiveSpecialization
  CycleQ2GenericWeightedSpatialDenominator
open CycleQ2MonicWeightedPrimitiveIdentity (normal density)
open scoped BigOperators

theorem separate_universal : separate universalAffine = universalEquation :=
  separate_chart_equation _

instance universalChart_domain : IsDomain (ChartRing universalAffine) := by
  unfold ChartRing
  rw [separate_universal]
  infer_instance

instance universalField_charZero : CharZero (Fld universalAffine) := by
  let φ : ℂ →+* Fld universalAffine := (fieldValue universalAffine).comp
    ((MvPolynomial.C : Coeff →+* MvPolynomial (Fin 4) Coeff).comp MvPolynomial.C)
  exact charZero_of_injective_ringHom φ.injective

theorem universal_normal_ne_zero : fieldValue universalAffine (normal universalAffine) ≠ 0 := by
  change algebraMap (ChartRing universalAffine) (Fld universalAffine)
    (projection universalAffine (normal universalAffine)) ≠ 0
  apply IsFractionRing.to_map_eq_zero_iff.not.mpr
  change AdjoinRoot.mk (separate universalAffine) (separate (normal universalAffine)) ≠ 0
  rw [separate_universal]
  exact CycleQ2MonicWeightedAffineEquation.normal_nonzero

/-- Exactness in the universal three-variable weighted hypersurface function field. -/
def UniversalWeightedPrimitiveExists : Prop :=
  ∃ v : Fin 3 → Fld universalAffine,
    ∑ j, direction universalAffine universal_normal_ne_zero j (v j) =
      density (fieldValue universalAffine) universalAffine

end CycleQ2UniversalWeightedTransfer
end

#print axioms CycleQ2UniversalWeightedTransfer.universal_normal_ne_zero
#print axioms CycleQ2UniversalWeightedTransfer.UniversalWeightedPrimitiveExists
end
