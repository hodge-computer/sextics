import Proposal.GeometricSurfaceCoordinates
import Proposal.GeometricCurveCoordinates
import Proposal.SolutionSupport01Part06
import Proposal.GeometricSeedNormalIdeals
import Proposal.GeometricNormalConnecting

/-! Components extracted from SolutionSupport01.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_3/SeedCechTopCohomology.lean -/
section
/-!
# The seven-dimensional top coordinate Čech quotient

The quotient by the three pair-open images keeps exactly the monomials whose
three base exponents are all negative. In total degree zero and invariant
character, the actual nine shifts leave precisely seven such monomials.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechTopCohomology

open CycleQ2SeedCechThreeOpen
open scoped BigOperators

abbrev SmallExponents := Fin 4 × Fin 4 × Fin 4

def topExponent (e : SmallExponents) : LaurentExponent :=
  ![-((e.1.val : ℤ) + 1), -((e.2.1.val : ℤ) + 1), -((e.2.2.val : ℤ) + 1)]

abbrev TopIndex := {q : ShiftIndex × SmallExponents // shiftedGrade q.1 (topExponent q.2) = 0}

theorem topIndex_count : Fintype.card TopIndex = 7 := by decide

theorem topExponent_negative (e : SmallExponents) (i : Fin 3) : topExponent e i < 0 := by
  fin_cases i
  · change -((e.1.val : ℤ) + 1) < 0; omega
  · change -((e.2.1.val : ℤ) + 1) < 0; omega
  · change -((e.2.2.val : ℤ) + 1) < 0; omega

theorem topExponent_injective : Function.Injective topExponent := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  have h2 := congrFun hab 2
  change -((a.1.val : ℤ) + 1) = -((b.1.val : ℤ) + 1) at h0
  change -((a.2.1.val : ℤ) + 1) = -((b.2.1.val : ℤ) + 1) at h1
  change -((a.2.2.val : ℤ) + 1) = -((b.2.2.val : ℤ) + 1) at h2
  apply Prod.ext
  · apply Fin.ext; omega
  · apply Prod.ext <;> apply Fin.ext <;> omega

def topCoordinate (q : TopIndex) : ShiftIndex × LaurentExponent := (q.val.1, topExponent q.val.2)

theorem topCoordinate_injective : Function.Injective topCoordinate := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q : ShiftIndex × LaurentExponent ↦ q.1) hab
  · exact topExponent_injective
      (congrArg (fun q : ShiftIndex × LaurentExponent ↦ q.2) hab)

/-- Completeness of the finite index, derived from actual degree zero. -/
theorem exists_topIndex (ab : ShiftIndex) (e : LaurentExponent)
    (he : ∀ i, e i < 0) (hg : shiftedGrade ab e = 0) :
    ∃ q : TopIndex, topCoordinate q = (ab, e) := by
  have hd := congrArg Prod.fst hg
  change (ab.1.val : ℤ) + 2 * ab.2.val + ∑ i, e i = 0 at hd
  rw [Fin.sum_univ_three] at hd
  have ha := ab.1.isLt
  have hb := ab.2.isLt
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have bounds (i : Fin 3) : (-e i - 1).toNat < 4 := by
    fin_cases i
    · change (-e 0 - 1).toNat < 4; omega
    · change (-e 1 - 1).toNat < 4; omega
    · change (-e 2 - 1).toNat < 4; omega
  let v : SmallExponents :=
    (⟨(-e 0 - 1).toNat, bounds 0⟩,
     ⟨(-e 1 - 1).toNat, bounds 1⟩,
     ⟨(-e 2 - 1).toNat, bounds 2⟩)
  have hv : topExponent v = e := by
    ext i
    fin_cases i
    · change -(((-e 0 - 1).toNat : ℤ) + 1) = e 0; omega
    · change -(((-e 1 - 1).toNat : ℤ) + 1) = e 1; omega
    · change -(((-e 2 - 1).toNat : ℤ) + 1) = e 2; omega
  refine ⟨⟨(ab, v), ?_⟩, ?_⟩
  · simpa only [hv] using hg
  · exact Prod.ext rfl hv

variable (R : Type*) [CommRing R]

abbrev Family := ShiftIndex → Laurent (R := R)

def gradedFamilies : Submodule R (Family R) where
  carrier := {p | ∀ ab, HasGrade ab 0 (p ab)}
  zero_mem' := by intro ab e he; simp
  add_mem' hp hq ab := hasGrade_add ab 0 (hp ab) (hq ab)
  smul_mem' c p hp ab := by
    intro e he
    simp [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, hp ab e he]

def topProjection : gradedFamilies R →ₗ[R] (TopIndex →₀ R) where
  toFun p := Finsupp.equivFunOnFinite.symm
    (fun q ↦ (p.val q.val.1).coeff (topExponent q.val.2))
  map_add' p q := by ext i; simp [AddMonoidAlgebra.coeff_add]
  map_smul' c p := by ext i; simp [AddMonoidAlgebra.coeff_smul]

@[simp] theorem topProjection_apply (p : gradedFamilies R) (q : TopIndex) :
    topProjection R p q = (p.val q.val.1).coeff (topExponent q.val.2) := rfl

def basisFamily (q : TopIndex) : Family R := fun ab ↦
  if ab = q.val.1 then AddMonoidAlgebra.single (topExponent q.val.2) 1 else 0

@[simp] theorem basisFamily_coeff (q : TopIndex) (ab : ShiftIndex) (e : LaurentExponent) :
    (basisFamily R q ab).coeff e = if topCoordinate q = (ab, e) then 1 else 0 := by
  classical
  by_cases ha : ab = q.val.1
  · subst ab
    by_cases he : e = topExponent q.val.2
    · subst e; simp [basisFamily, topCoordinate]
    · simp [basisFamily, topCoordinate, he, Ne.symm he]
  · have ha' : q.val.1 ≠ ab := Ne.symm ha
    simp [basisFamily, topCoordinate, ha, ha']

def basisSection (q : TopIndex) : gradedFamilies R := ⟨basisFamily R q, by
  intro ab e he
  rw [basisFamily_coeff]
  split
  · next h =>
      have ha : q.val.1 = ab := congrArg Prod.fst h
      have h_exp : topExponent q.val.2 = e := congrArg Prod.snd h
      exact False.elim (he (ha ▸ h_exp ▸ q.property))
  · rfl⟩

@[simp] theorem topProjection_basisSection (q : TopIndex) :
    topProjection R (basisSection R q) = Finsupp.single q 1 := by
  ext j
  change (basisFamily R q j.val.1).coeff (topExponent j.val.2) = _
  rw [basisFamily_coeff]
  change (if topCoordinate q = topCoordinate j then 1 else 0) = _
  simp only [topCoordinate_injective.eq_iff, Finsupp.single_apply]

theorem topProjection_surjective : Function.Surjective (topProjection R) := by
  intro p
  refine ⟨∑ q : TopIndex, p q • basisSection R q, ?_⟩
  ext q
  simp

def poleSubmodule (s : Finset (Fin 3)) : Submodule R (gradedFamilies R) where
  carrier := {p | ∀ ab, HasPoles s (p.val ab)}
  zero_mem' := by intro ab e i hi hneg; simp
  add_mem' hp hq := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_add, hp ab e i hi hneg, hq ab e i hi hneg]
  smul_mem' c p hp := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_smul, hp ab e i hi hneg]

/-- The sum of the three pair-open images in the triple-open graded space. -/
def topBoundary : Submodule R (gradedFamilies R) :=
  poleSubmodule R {0, 1} ⊔ poleSubmodule R {0, 2} ⊔ poleSubmodule R {1, 2}

theorem topProjection_zero_iff (p : gradedFamilies R) :
    topProjection R p = 0 ↔
      ∀ ab e, (∀ i, e i < 0) → (p.val ab).coeff e = 0 := by
  constructor
  · intro hp ab e he
    by_cases hg : shiftedGrade ab e = 0
    · obtain ⟨q, hq⟩ := exists_topIndex ab e he hg
      have ha : q.val.1 = ab := congrArg Prod.fst hq
      have hx : topExponent q.val.2 = e := congrArg Prod.snd hq
      have hh := congrArg (fun f : TopIndex →₀ R ↦ f q) hp
      simpa only [topProjection_apply, ha, hx, Finsupp.zero_apply] using hh
    · exact p.property ab e hg
  · intro hp
    ext q
    exact hp q.val.1 (topExponent q.val.2) (topExponent_negative q.val.2)

theorem poleSubmodule_le_ker (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∉ s) :
    poleSubmodule R s ≤ LinearMap.ker (topProjection R) := by
  intro p hp
  rw [LinearMap.mem_ker, topProjection_zero_iff]
  intro ab e he
  exact hp ab e i hi (he i)

theorem topBoundary_le_ker : topBoundary R ≤ LinearMap.ker (topProjection R) :=
  sup_le (sup_le (poleSubmodule_le_ker R {0, 1} 2 (by decide))
    (poleSubmodule_le_ker R {0, 2} 1 (by decide)))
      (poleSubmodule_le_ker R {1, 2} 0 (by decide))

def filterSection (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R) : gradedFamilies R :=
  ⟨fun ab ↦ AddMonoidAlgebra.ofCoeff ((p.val ab).coeff.filter P), by
    intro ab e he
    change (if P e then (p.val ab).coeff e else 0) = 0
    split <;> simp [p.property ab e he]⟩

@[simp] theorem filterSection_coeff (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R) (ab : ShiftIndex) (e : LaurentExponent) :
    ((filterSection R P p).val ab).coeff e = if P e then (p.val ab).coeff e else 0 := rfl

theorem filterSection_mem_poleSubmodule (P : LaurentExponent → Prop) [DecidablePred P]
    (s : Finset (Fin 3))
    (hP : ∀ e, P e → ∀ i, i ∉ s → 0 ≤ e i) (p : gradedFamilies R) :
    filterSection R P p ∈ poleSubmodule R s := by
  intro ab e i hi hneg
  rw [filterSection_coeff]
  split
  · next he => exact False.elim ((not_le.mpr hneg) (hP e he i hi))
  · rfl

/-- Projection onto negative exponents loses exactly the three pair-open images. -/
theorem topBoundary_eq_ker : topBoundary R = LinearMap.ker (topProjection R) := by
  apply le_antisymm (topBoundary_le_ker R)
  intro p hp
  have hz := (topProjection_zero_iff R p).mp hp
  let p01 := filterSection R (fun e ↦ 0 ≤ e 2) p
  let p02 := filterSection R (fun e ↦ e 2 < 0 ∧ 0 ≤ e 1) p
  let p12 := filterSection R (fun e ↦ e 2 < 0 ∧ e 1 < 0 ∧ 0 ≤ e 0) p
  have h01 : p01 ∈ poleSubmodule R {0, 1} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · exact he
  have h02 : p02 ∈ poleSubmodule R {0, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · exact he.2
    · simp at hi
  have h12 : p12 ∈ poleSubmodule R {1, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · exact he.2.2
    · simp at hi
    · simp at hi
  have heq : p = p01 + p02 + p12 := by
    apply Subtype.ext
    funext ab
    apply AddMonoidAlgebra.ext
    ext e
    change (p.val ab).coeff e =
      ((p01.val ab + p02.val ab + p12.val ab).coeff e)
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      p01, p02, p12, filterSection_coeff]
    by_cases h2 : 0 ≤ e 2
    · simp [h2, not_lt.mpr h2]
    · by_cases h1 : 0 ≤ e 1
      · simp [lt_of_not_ge h2, h1, not_lt.mpr h1]
      · by_cases h0 : 0 ≤ e 0
        · simp [h2, h1, lt_of_not_ge h2, lt_of_not_ge h1, h0]
        · have hn : ∀ i, e i < 0 := by
            intro i
            fin_cases i
            · exact lt_of_not_ge h0
            · exact lt_of_not_ge h1
            · exact lt_of_not_ge h2
          simp [lt_of_not_ge h2, lt_of_not_ge h1, h0, hz ab e hn]
  rw [heq]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact (show poleSubmodule R {0, 1} ≤ topBoundary R from
        le_sup_of_le_left le_sup_left) h01
    · exact (show poleSubmodule R {0, 2} ≤ topBoundary R from
        le_sup_of_le_left le_sup_right) h02
  · exact (show poleSubmodule R {1, 2} ≤ topBoundary R from le_sup_right) h12

abbrev TopCechQuotient := gradedFamilies R ⧸ topBoundary R

def topCechEquiv : TopCechQuotient R ≃ₗ[R] (TopIndex →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (topBoundary_eq_ker R)).trans
    ((topProjection R).quotKerEquivOfSurjective (topProjection_surjective R))

@[simp] theorem topCechEquiv_mk (p : gradedFamilies R) :
    topCechEquiv R (Submodule.Quotient.mk p) = topProjection R p := by
  simp [topCechEquiv]

def topCechBasis : Module.Basis TopIndex R (TopCechQuotient R) :=
  Finsupp.basisSingleOne.map (topCechEquiv R).symm

@[simp] theorem topCechBasis_apply (q : TopIndex) :
    topCechBasis R q = Submodule.Quotient.mk (basisSection R q) := by
  apply (topCechEquiv R).injective
  simp [topCechBasis]

theorem topCech_rank_seven [Nontrivial R] : Module.finrank R (TopCechQuotient R) = 7 := by
  rw [Module.finrank_eq_card_basis (topCechBasis R), topIndex_count]

end CycleQ2SeedCechTopCohomology

#print axioms CycleQ2SeedCechTopCohomology.topIndex_count
#print axioms CycleQ2SeedCechTopCohomology.topProjection_surjective

#print axioms CycleQ2SeedCechTopCohomology.topCechBasis_apply
#print axioms CycleQ2SeedCechTopCohomology.topCech_rank_seven
end
end


/- Component: continuation_3/cylinder_bridge/SeedNormalConnecting.lean -/
section
/-! # The actual equation-normal connecting cocycle

The equation map is the dual of the displayed conormal relation for
`F=f₁g₁+f₂g₂+hk`.  Its two explicit local splittings have difference
`(kL-A)/(g₁g₂)` times `(g₂,-g₁,0)`.  The coefficients are then bound to the
literal smooth seed and its already constructed Laurent quotient charts.

The sign convention is fixed: normal fields follow `F+εA,h+εL`, hence their
images are `(-A,-L)`, and the overlap difference is first chart minus second
chart.  For fixed h the paired numerator is `-Aσ`, the negative of the
previously checked derivative numerator after substituting `w=-x₂²`.
No identification with a sheaf connecting morphism or an Abel--Jacobi map is
asserted here.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2NormalConnecting



section Seed

open MvPolynomial CycleQ2SeedTrace
open CycleQ2SeedCechTheta
open CycleQ2SeedCech (curveA curveB)

def thetaEquation (θ : ℂ) : WeightedPoly :=
  X 0^6+X 1^6+X 2^6+X 3^6+X 4^3+(originalB+C θ*X 0^3)^2

theorem thetaEquation_decomposition (r θ : ℂ) (hr : r^3=2) :
    thetaEquation θ = originalF1 r*originalG1 r+originalF2*originalG2+
      thetaH θ*thetaK θ := by
  have hh := seedEquation_decomposition r hr
  unfold thetaEquation thetaH thetaK seedEquation originalH originalK at *
  linear_combination hh

theorem smoothF_eq_thetaEquation (r : ℂ) (hr : r^3=2) :
    CycleQ2IncidenceEquations.smoothF r Complex.I = thetaEquation 1 := by
  rw [thetaEquation_decomposition r 1 hr]
  unfold CycleQ2IncidenceEquations.smoothF
  rw [smoothH_eq_thetaH]
  have hk : CycleQ2IncidenceEquations.smoothK Complex.I = thetaK 1 := by
    simp [CycleQ2IncidenceEquations.smoothK, CycleQ2IncidenceEquations.smoothB,
      CycleQ2IncidenceEquations.smoothA, thetaK, originalK, originalB]
    ring
  rw [hk]
  apply congrArg (fun q : WeightedPoly => q+thetaH 1*thetaK 1)
  unfold CycleQ2IncidenceEquations.seedG
  rw [CycleQ2SegreSeed.seedG_expanded]
  unfold originalF1 originalG1 originalF2 originalG2
  simp only [map_pow]
  ring

@[simp] theorem ambientCurveMap_F (r θ : ℂ) (hr : r^3=2) :
    ambientCurveMap r θ (thetaEquation θ)=0 := by
  rw [thetaEquation_decomposition r θ hr]
  simp


/-- This is the actual equation-normal map on the curve quotient. -/
def seedEquationMap (r θ : ℂ) :
    (Fin 3 → CurveRing r θ) →ₗ[CurveRing r θ] (Fin 2 → CurveRing r θ) :=
  equationMap (ambientCurveMap r θ (originalG1 r))
    (ambientCurveMap r θ originalG2) (ambientCurveMap r θ (thetaK θ))

theorem substitute_derivativeA (p : Poly) :
    substitute derivativeA*p=derivativeNumerator p := by
  simp only [derivativeA, substitute, derivativeNumerator, map_mul, map_pow,
    aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The fixed-h normal cocycle has the opposite sign to the previously
defined derivative numerator.  The source `A=x₂x₃³w` is unchanged. -/
theorem fixed_h_paired_numerator (p : Poly) :
    -(substitute derivativeA)*p= -derivativeNumerator p := by
  rw [neg_mul, substitute_derivativeA]

theorem thetaEquation_mem (r θ : ℂ) (hr : r^3=2) :
    thetaEquation θ ∈ ambientCurveIdeal r θ := by
  rw [thetaEquation_decomposition r θ hr]
  exact Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 0))
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 1)))
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 2))

/-- The equation map uses the literal class of F in the actual ideal modulo
its square.  No abstract normal-bundle presentation is supplied as a premise. -/
theorem conormal_relation (r θ : ℂ) (hr : r^3=2) :
    (ambientCurveIdeal r θ).toCotangent ⟨thetaEquation θ,thetaEquation_mem r θ hr⟩ =
      originalG1 r • conormalGenerator r θ 0+
      originalG2 • conormalGenerator r θ 1+thetaK θ • conormalGenerator r θ 2 := by
  have hh : (⟨thetaEquation θ,thetaEquation_mem r θ hr⟩ : ambientCurveIdeal r θ) =
      originalG1 r • ⟨curveEquations r θ 0,curveEquation_mem r θ 0⟩+
      originalG2 • ⟨curveEquations r θ 1,curveEquation_mem r θ 1⟩+
      thetaK θ • ⟨curveEquations r θ 2,curveEquation_mem r θ 2⟩ := by
    apply Subtype.ext
    change thetaEquation θ = originalG1 r*originalF1 r+originalG2*originalF2+
      thetaK θ*thetaH θ
    rw [thetaEquation_decomposition r θ hr]
    ring
  rw [hh, map_add, map_add, map_smul, map_smul, map_smul]
  rfl


end Seed

end CycleQ2NormalConnecting

#print axioms CycleQ2NormalConnecting.local_lift_difference
#print axioms CycleQ2NormalConnecting.smoothF_eq_thetaEquation
#print axioms CycleQ2NormalConnecting.ambientCurveMap_g1
#print axioms CycleQ2NormalConnecting.conormal_relation
#print axioms CycleQ2NormalConnecting.restricted_local_lifts_difference
end
end


/- Component: continuation_3/cylinder_bridge/SegreFactorExact.lean -/
section
/-! # Denominator-free exactness of the Segre factor sequence

For a regular linkage pairing `a_i*b_j=p*M_ij`, entries of `M` generating
the unit ideal give factor lifts and the unique scalar gauge ambiguity.
The proof uses scaled lifts followed by a Bezout sum and works in arbitrary
commutative rings, without choosing an invertible matrix entry.
-/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreFactorExact

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
open scoped BigOperators

variable {A : Type*} [CommRing A]

def scaledLeftLift (a : Fin 3 → A) (N : Matrix (Fin 3) (Fin 3) A)
    (i0 j0 i : Fin 3) : A := a i0*N i j0-a i*N i0 j0

def scaledRightLift (b : Fin 3 → A) (N : Matrix (Fin 3) (Fin 3) A)
    (i0 j0 j : Fin 3) : A := b j0*N i0 j

theorem scaled_factor_lift (p : A) (M N : Matrix (Fin 3) (Fin 3) A)
    (a b : Fin 3 → A) (hab : ∀ i j, a i*b j=p*M i j)
    (hM : CycleQ2SegreLocal.cofactors M=0) (hN : cofactorDifferential M N=0)
    (i0 j0 i j : Fin 3) :
    scaledLeftLift a N i0 j0 i*b j+a i*scaledRightLift b N i0 j0 j=
      p*M i0 j0*N i j := by
  have hlin := linearized_minors_of_cofactorDifferential_zero M N hM hN i j i0 j0
  calc
    _ = (a i0*b j)*N i j0-(a i*b j)*N i0 j0+(a i*b j0)*N i0 j := by
      unfold scaledLeftLift scaledRightLift
      ring
    _ = p*M i0 j*N i j0-p*M i j*N i0 j0+p*M i j0*N i0 j := by
      rw [hab,hab,hab]
    _ = p*M i0 j0*N i j := by linear_combination -p*hlin

def bezoutLeftLift (a : Fin 3 → A) (N : Matrix (Fin 3) (Fin 3) A)
    (ξ : Fin 3 × Fin 3 → A) (i : Fin 3) : A :=
  ∑ q, ξ q*scaledLeftLift a N q.1 q.2 i

def bezoutRightLift (b : Fin 3 → A) (N : Matrix (Fin 3) (Fin 3) A)
    (ξ : Fin 3 × Fin 3 → A) (j : Fin 3) : A :=
  ∑ q, ξ q*scaledRightLift b N q.1 q.2 j

theorem bezout_factor_lift (p : A) (M N : Matrix (Fin 3) (Fin 3) A)
    (a b : Fin 3 → A) (hab : ∀ i j, a i*b j=p*M i j)
    (hM : CycleQ2SegreLocal.cofactors M=0) (hN : cofactorDifferential M N=0)
    (ξ : Fin 3 × Fin 3 → A) (hξ : ∑ q, ξ q*M q.1 q.2=1) (i j : Fin 3) :
    bezoutLeftLift a N ξ i*b j+a i*bezoutRightLift b N ξ j=p*N i j := by
  calc
    _ = ∑ q, ξ q*(scaledLeftLift a N q.1 q.2 i*b j+
        a i*scaledRightLift b N q.1 q.2 j) := by
      unfold bezoutLeftLift bezoutRightLift
      rw [Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = ∑ q, ξ q*(p*M q.1 q.2*N i j) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [scaled_factor_lift p M N a b hab hM hN]
    _ = (∑ q, ξ q*M q.1 q.2)*(p*N i j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = p*N i j := by rw [hξ,one_mul]

theorem bezoutLeftLift_mem (I : Ideal A) (a : Fin 3 → A)
    (ha : ∀ i, a i∈I) (N : Matrix (Fin 3) (Fin 3) A)
    (ξ : Fin 3 × Fin 3 → A) (i : Fin 3) : bezoutLeftLift a N ξ i∈I := by
  apply Ideal.sum_mem
  intro q hq
  exact I.mul_mem_left _ (I.sub_mem (I.mul_mem_right _ (ha q.1)) (I.mul_mem_right _ (ha i)))

theorem bezoutRightLift_mem (J : Ideal A) (b : Fin 3 → A)
    (hb : ∀ j, b j∈J) (N : Matrix (Fin 3) (Fin 3) A)
    (ξ : Fin 3 × Fin 3 → A) (j : Fin 3) : bezoutRightLift b N ξ j∈J := by
  apply Ideal.sum_mem
  intro q hq
  exact J.mul_mem_left _ (J.mul_mem_right _ (hb q.2))

/-- Every cofactor-kernel section has actual ideal-valued factor lifts on
any chart where the matrix entries generate the unit ideal. -/
theorem exists_factor_lift (I J : Ideal A) (p : A)
    (M N : Matrix (Fin 3) (Fin 3) A) (a b : Fin 3 → A)
    (ha : ∀ i, a i∈I) (hb : ∀ j, b j∈J)
    (hab : ∀ i j, a i*b j=p*M i j)
    (hM : CycleQ2SegreLocal.cofactors M=0) (hN : cofactorDifferential M N=0)
    (hspan : Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2))=⊤) :
    ∃ v w : Fin 3 → A, (∀ i, v i∈I) ∧ (∀ j, w j∈J) ∧
      ∀ i j, v i*b j+a i*w j=p*N i j := by
  have hmem : (1 : A) ∈ Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨ξ,hξ⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  exact ⟨bezoutLeftLift a N ξ,bezoutRightLift b N ξ,
    bezoutLeftLift_mem I a ha N ξ,bezoutRightLift_mem J b hb N ξ,
    bezout_factor_lift p M N a b hab hM hN ξ hξ⟩

/-- The vanishing numerator has only the scalar gauge ambiguity. This uses
regularity of the actual linkage element, not that the entire ring is a domain. -/
theorem factor_gauge (I J : Ideal A) (p : A)
    (hp : Function.Injective (fun z : A => p*z))
    (M : Matrix (Fin 3) (Fin 3) A) (a b v w : Fin 3 → A)
    (hb : ∀ j, b j∈J) (hv : ∀ i, v i∈I)
    (hab : ∀ i j, a i*b j=p*M i j)
    (hpair : I*J≤Ideal.span {p})
    (hspan : Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2))=⊤)
    (hzero : ∀ i j, v i*b j+a i*w j=0) :
    ∃ c : A, (∀ i, v i=c*a i) ∧ (∀ j, w j=-(c*b j)) := by
  have hdiv (q : Fin 3 × Fin 3) : p ∣ v q.1*b q.2 :=
    Ideal.mem_span_singleton.mp (hpair (Ideal.mul_mem_mul (hv q.1) (hb q.2)))
  choose c hc using hdiv
  have hl (i j k : Fin 3) : M i j*v k=a k*c (i,j) := by
    apply hp
    linear_combination -v k*hab i j+a k*hc (i,j)+a i*hzero k j-a k*hzero i j
  have hr (i j l : Fin 3) : M i j*w l=-(b l*c (i,j)) := by
    apply hp
    linear_combination -w l*hab i j-b l*hc (i,j)+b j*hzero i l
  have hmem : (1 : A) ∈ Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨ξ,hξ⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  refine ⟨∑ q, ξ q*c q,?_,?_⟩
  · intro k
    calc
      v k = (∑ q, ξ q*M q.1 q.2)*v k := by rw [hξ,one_mul]
      _ = ∑ q, ξ q*(M q.1 q.2*v k) := by simp only [Finset.sum_mul,mul_assoc]
      _ = ∑ q, ξ q*(a k*c q) := by simp only [hl]
      _ = (∑ q, ξ q*c q)*a k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro q hq
        ring
  · intro l
    calc
      w l = (∑ q, ξ q*M q.1 q.2)*w l := by rw [hξ,one_mul]
      _ = ∑ q, ξ q*(M q.1 q.2*w l) := by simp only [Finset.sum_mul,mul_assoc]
      _ = ∑ q, ξ q*(-(b l*c q)) := by simp only [hr]
      _ = -((∑ q, ξ q*c q)*b l) := by
        rw [Finset.sum_mul,← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        ring

theorem gauge_scalar_unique (p : A) (hp : Function.Injective (fun z : A => p*z))
    (M : Matrix (Fin 3) (Fin 3) A) (a b : Fin 3 → A)
    (hab : ∀ i j, a i*b j=p*M i j)
    (hspan : Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2))=⊤)
    (c d : A) (h : ∀ i, c*a i=d*a i) : c=d := by
  have hM (q : Fin 3 × Fin 3) : M q.1 q.2*c=M q.1 q.2*d := by
    apply hp
    linear_combination (d-c)*hab q.1 q.2+b q.2*h q.1
  have hmem : (1 : A) ∈ Ideal.span (Set.range (fun q : Fin 3 × Fin 3 => M q.1 q.2)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨ξ,hξ⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  calc
    c = (∑ q, ξ q*M q.1 q.2)*c := by rw [hξ,one_mul]
    _ = ∑ q, ξ q*(M q.1 q.2*c) := by simp only [Finset.sum_mul,mul_assoc]
    _ = ∑ q, ξ q*(M q.1 q.2*d) := by simp only [hM]
    _ = (∑ q, ξ q*M q.1 q.2)*d := by
      simp only [Finset.sum_mul,mul_assoc]
    _ = d := by rw [hξ,one_mul]

theorem differential_comm (M N : Matrix (Fin 3) (Fin 3) A) :
    cofactorDifferential M N=cofactorDifferential N M := by
  unfold cofactorDifferential
  rw [add_comm M N]
  abel

theorem differential_left_smul (c : A) (M N : Matrix (Fin 3) (Fin 3) A) :
    cofactorDifferential (c • M) N=c • cofactorDifferential M N := by
  rw [differential_comm]
  have h := map_smul (cofactorDifferentialLinear N) c M
  change cofactorDifferential N (c • M)=c • cofactorDifferential N M at h
  rw [h,differential_comm N M]

/-- Actual ideal-valued factor variations are in the cofactor kernel. -/
theorem factor_lift_in_kernel (p : A) (hp : Function.Injective (fun z : A => p*z))
    (M N : Matrix (Fin 3) (Fin 3) A) (a b v w : Fin 3 → A)
    (hab : ∀ i j, a i*b j=p*M i j)
    (hN : ∀ i j, v i*b j+a i*w j=p*N i j) :
    cofactorDifferential M N=0 := by
  have hM' : p • M=(fun i j => a i*b j) := by funext i j; exact (hab i j).symm
  have hN' : p • N=(fun i j => v i*b j+a i*w j) := by funext i j; exact (hN i j).symm
  have hz : cofactorDifferential (p • M) (p • N)=0 := by
    rw [hM',hN']
    exact cofactorDifferential_factor_variation a b v w
  have hlin := map_smul (cofactorDifferentialLinear (p • M)) p N
  change cofactorDifferential (p • M) (p • N)=p • cofactorDifferential (p • M) N at hlin
  rw [hlin,differential_left_smul] at hz
  funext i j
  change cofactorDifferential M N i j = 0
  apply hp
  apply hp
  have hh := congrArg (fun T => T i j) hz
  change p*(p*cofactorDifferential M N i j)=0 at hh
  simpa only [mul_zero] using hh

end CycleQ2SegreFactorExact

#print axioms CycleQ2SegreFactorExact.exists_factor_lift
#print axioms CycleQ2SegreFactorExact.factor_gauge
#print axioms CycleQ2SegreFactorExact.gauge_scalar_unique
#print axioms CycleQ2SegreFactorExact.factor_lift_in_kernel
end
end


/- Component: continuation_3/SegreGaussianActionBinding.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
namespace CycleQ2SegreGaussianActionData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
variable (hz : z^3 = evalLayers φ x v a0 + evalLayers φ x v a1*z)
variable (hw : w^3 = evalLayers φ x v b0-z^6)
include hz hw

theorem eval_action00 (a b : ℕ) :
    evalTowers φ x w z v (action00 a b) = evalTowers φ x w z v m00 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m00 (action00 a b) a b (action_check00 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action00 a b = normalizeTower a0 a1 b0 32
        (mulTowers m00 (monomialTower oneLayers a b)) := by
      unfold action00
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action01 (a b : ℕ) :
    evalTowers φ x w z v (action01 a b) = evalTowers φ x w z v m01 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m01 (action01 a b) a b (action_check01 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action01 a b = normalizeTower a0 a1 b0 32
        (mulTowers m01 (monomialTower oneLayers a b)) := by
      unfold action01
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action02 (a b : ℕ) :
    evalTowers φ x w z v (action02 a b) = evalTowers φ x w z v m02 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m02 (action02 a b) a b (action_check02 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action02 a b = normalizeTower a0 a1 b0 32
        (mulTowers m02 (monomialTower oneLayers a b)) := by
      unfold action02
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action10 (a b : ℕ) :
    evalTowers φ x w z v (action10 a b) = evalTowers φ x w z v m10 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m10 (action10 a b) a b (action_check10 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action10 a b = normalizeTower a0 a1 b0 32
        (mulTowers m10 (monomialTower oneLayers a b)) := by
      unfold action10
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action11 (a b : ℕ) :
    evalTowers φ x w z v (action11 a b) = evalTowers φ x w z v m11 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m11 (action11 a b) a b (action_check11 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action11 a b = normalizeTower a0 a1 b0 32
        (mulTowers m11 (monomialTower oneLayers a b)) := by
      unfold action11
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action12 (a b : ℕ) :
    evalTowers φ x w z v (action12 a b) = evalTowers φ x w z v m12 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m12 (action12 a b) a b (action_check12 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action12 a b = normalizeTower a0 a1 b0 32
        (mulTowers m12 (monomialTower oneLayers a b)) := by
      unfold action12
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action20 (a b : ℕ) :
    evalTowers φ x w z v (action20 a b) = evalTowers φ x w z v m20 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m20 (action20 a b) a b (action_check20 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action20 a b = normalizeTower a0 a1 b0 32
        (mulTowers m20 (monomialTower oneLayers a b)) := by
      unfold action20
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action21 (a b : ℕ) :
    evalTowers φ x w z v (action21 a b) = evalTowers φ x w z v m21 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m21 (action21 a b) a b (action_check21 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action21 a b = normalizeTower a0 a1 b0 32
        (mulTowers m21 (monomialTower oneLayers a b)) := by
      unfold action21
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring

theorem eval_action22 (a b : ℕ) :
    evalTowers φ x w z v (action22 a b) = evalTowers φ x w z v m22 * z^a * w^b := by
  by_cases h : a<3 ∧ b<3
  · exact monomial_action_of_fast_normal_error_check φ x w z v a0 a1 b0 hz hw 32
      m22 (action22 a b) a b (action_check22 ⟨a,h.1⟩ ⟨b,h.2⟩)
  · have hf : action22 a b = normalizeTower a0 a1 b0 32
        (mulTowers m22 (monomialTower oneLayers a b)) := by
      unfold action22
      split <;> first | omega | rfl
    rw [hf, eval_normalizeTower φ x w z v a0 a1 b0 hz hw,
      eval_mulTowers,eval_monomialTower,eval_oneLayers]
    ring
end CycleQ2SegreGaussianActionData
#print axioms CycleQ2SegreGaussianActionData.eval_action00
end


/- Component: continuation_3/SegreModularChartExact.lean -/
section
/-!
# Exactness on the actual coordinate opens of the modular seed

The five explicit basepoint identities and the general entry-ideal exactness
theorem apply to the same coordinate localizations used in the seed Čech
complex. This proves local existence of matrix lifts on every nonempty
coordinate open, including all overlaps. Global homogeneous lifting still
requires the connecting-obstruction argument.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreModularChartExact

open MvPolynomial Matrix CycleQ2SegreModularBasepoint CycleQ2SegreTangentLocal
  CycleQ2IncidenceFirstOrder CycleQ2SegreRelationsLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis

variable {R : Type*} [CommRing R] [CharP R 109]

theorem coordinate_remaining (j : Fin 3) :
    coordinate (R := R) (remainingIndex j) =
      algebraMap (Base R) (ActualSeedRing (R := R)) (X j) := by
  change Ideal.Quotient.mk _ (X (remainingIndex j)) =
    Ideal.Quotient.mk _ (remainingInclusion R (X j))
  simp [remainingInclusion]

theorem base_coordinate_unit (s : Finset (Fin 3)) (j : Fin 3) (hj : j ∈ s) :
    IsUnit (algebraMap (Base R) (coordinateLocalization R s) (X j)) := by
  have hd : (X j : Base R) ∣ baseProduct R s := Finset.dvd_prod_of_mem X hj
  exact isUnit_of_dvd_unit ((algebraMap (Base R) (coordinateLocalization R s)).map_dvd hd)
    (IsLocalization.Away.algebraMap_isUnit (S := coordinateLocalization R s) _)

theorem seed_coordinate_unit (s : Finset (Fin 3)) (j : Fin 3) (hj : j ∈ s) :
    IsUnit (algebraMap (ActualSeedRing (R := R)) (SeedLocal R 57 33 s)
      (coordinate (remainingIndex j))) := by
  rw [coordinate_remaining, ← IsScalarTower.algebraMap_apply (Base R)
    (ActualSeedRing (R := R)) (SeedLocal R 57 33 s)]
  rw [IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s)
    (SeedLocal R 57 33 s)]
  exact (base_coordinate_unit s j hj).map
    (algebraMap (coordinateLocalization R s) (SeedLocal R 57 33 s))

def chartMatrix (s : Finset (Fin 3)) : Matrix (Fin 3) (Fin 3) (SeedLocal R 57 33 s) :=
  (algebraMap (ActualSeedRing (R := R)) (SeedLocal R 57 33 s)).mapMatrix
    (matrix (R := R))

theorem chartMatrix_cofactors (s : Finset (Fin 3)) :
    CycleQ2SegreLocal.cofactors (chartMatrix (R := R) s) = 0 := by
  rw [chartMatrix, ← map_cofactors]
  change (algebraMap (ActualSeedRing (R := R)) (SeedLocal R 57 33 s)).mapMatrix
    (CycleQ2SegreLocal.cofactors (seedQuotientMatrix (57 : R) 33)) = 0
  rw [seedQuotientMatrix_cofactors]
  ext i j
  change algebraMap (ActualSeedRing (R := R)) (SeedLocal R 57 33 s) 0 = 0
  exact map_zero _

theorem chartMatrix_entries_generate (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 =>
      chartMatrix (R := R) s ij.1 ij.2)) = ⊤ := by
  obtain ⟨j, hj⟩ := hs
  let φ := algebraMap (ActualSeedRing (R := R)) (SeedLocal R 57 33 s)
  have hm := Ideal.mem_map_of_mem φ
    (seed_coordinate_power_mem (R := R) (remainingIndex j))
  have hu : IsUnit (φ (coordinate (remainingIndex j) ^
      CycleQ2SegreModularBasepoint.degrees (remainingIndex j))) := by
    rw [map_pow]
    exact (seed_coordinate_unit (R := R) s j hj).pow _
  have ht := Ideal.eq_top_of_isUnit_mem _ hm hu
  simpa only [entryIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def, φ, chartMatrix,
    RingHom.mapMatrix_apply, Matrix.map_apply]
    using ht

/-- The literal relation kernel equals the image of the actual cofactor
differential on every nonempty open in the three-coordinate Čech cover. -/
theorem coordinate_chart_relations_exact (s : Finset (Fin 3)) (hs : s.Nonempty)
    (C : Matrix (Fin 3) (Fin 3) (SeedLocal R 57 33 s)) :
    CycleQ2SegreRelations.relations (chartMatrix (R := R) s) *ᵥ vector C = 0 ↔
      ∃ N : Matrix (Fin 3) (Fin 3) (SeedLocal R 57 33 s),
        cofactorDifferential (chartMatrix (R := R) s) N = C :=
  entry_ideal_relations_exact _ _ (chartMatrix_cofactors s) (chartMatrix_entries_generate s hs)

theorem coordinate_chart_ker_eq_range (s : Finset (Fin 3)) (hs : s.Nonempty) :
    LinearMap.ker (relationsLinear (chartMatrix (R := R) s)) =
      LinearMap.range (cofactorDifferentialLinear (chartMatrix (R := R) s)) :=
  entry_ideal_ker_eq_range _ (chartMatrix_cofactors s) (chartMatrix_entries_generate s hs)

end CycleQ2SegreModularChartExact

#print axioms CycleQ2SegreModularChartExact.chartMatrix_entries_generate
#print axioms CycleQ2SegreModularChartExact.coordinate_chart_relations_exact
#print axioms CycleQ2SegreModularChartExact.coordinate_chart_ker_eq_range
end
end


/- Component: continuation_3/SegreModularCubicChecks.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCubicData
open CycleQ2SparseGaussianPolynomial CycleQ2SegreGaussianTangentData

theorem eval_cubicTable {R : Type*} [CommRing R]
    (φ : GaussianInt →+* R) (x : Fin 5 → R) (w z v : R)
    (hz : z^3=evalLayers φ x v a0+evalLayers φ x v a1*z)
    (hw : w^3=evalLayers φ x v b0-z^6) (s : Fin 3) (q : Fin 9) :
    evalTowers φ x w z v (cubicTable s q)=evalTowers φ x w z v (monomialCubic q) *
      evalTowers φ x w z v k * evalTowers φ x w z v (literalQ s) := by
  fin_cases s <;> fin_cases q
  · exact eval_cubic0_0 φ x w z v hz hw
  · exact eval_cubic0_1 φ x w z v hz hw
  · exact eval_cubic0_2 φ x w z v hz hw
  · exact eval_cubic0_3 φ x w z v hz hw
  · exact eval_cubic0_4 φ x w z v hz hw
  · exact eval_cubic0_5 φ x w z v hz hw
  · exact eval_cubic0_6 φ x w z v hz hw
  · exact eval_cubic0_7 φ x w z v hz hw
  · exact eval_cubic0_8 φ x w z v hz hw
  · exact eval_cubic1_0 φ x w z v hz hw
  · exact eval_cubic1_1 φ x w z v hz hw
  · exact eval_cubic1_2 φ x w z v hz hw
  · exact eval_cubic1_3 φ x w z v hz hw
  · exact eval_cubic1_4 φ x w z v hz hw
  · exact eval_cubic1_5 φ x w z v hz hw
  · exact eval_cubic1_6 φ x w z v hz hw
  · exact eval_cubic1_7 φ x w z v hz hw
  · exact eval_cubic1_8 φ x w z v hz hw
  · exact eval_cubic2_0 φ x w z v hz hw
  · exact eval_cubic2_1 φ x w z v hz hw
  · exact eval_cubic2_2 φ x w z v hz hw
  · exact eval_cubic2_3 φ x w z v hz hw
  · exact eval_cubic2_4 φ x w z v hz hw
  · exact eval_cubic2_5 φ x w z v hz hw
  · exact eval_cubic2_6 φ x w z v hz hw
  · exact eval_cubic2_7 φ x w z v hz hw
  · exact eval_cubic2_8 φ x w z v hz hw
end CycleQ2SegreModularCubicData
#print axioms CycleQ2SegreModularCubicData.eval_cubicTable
end


/- Component: continuation_3/SegreModularCubicMonomialBinding.lean -/
section
/-! The nine supplied cubic towers are the actual indexed monomials. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreModularCubicMonomialBinding

open MvPolynomial CycleQ2SparseGaussianPolynomial CycleQ2SparseModularFunctional
  CycleQ2SegreModularCubicData CycleQ2SegreModularDetectorData
  CycleQ2SegreModularGaussianBinding CycleQ2IncidenceGaussianArithmetic

theorem monomialCubic_flatten (q : Fin 9) :
    flattenTowersData (monomialCubic q)=[(cubicExponents q,1)] := by
  fin_cases q <;> rfl

theorem flatten_value (p : Towers) :
    eval coeffHom (MvPolynomial.X : Fin 5 → CycleQ2SegreModularGaussianBinding.P)
      (flattenTowersData p)=value p := by
  rw [flattenTowersData_eq,eval_flattenTowers]
  rfl

theorem value_monomialCubic (q : Fin 9) :
    value (monomialCubic q)=
      MvPolynomial.monomial (tupleExponent (cubicExponents q)) (1:F109) := by
  rw [←flatten_value,monomialCubic_flatten]
  change eval (MvPolynomial.C.comp reduction)
    (MvPolynomial.X : Fin 5 → CycleQ2SegreModularGaussianBinding.P)
      [(cubicExponents q,1)]=_
  simp only [eval_cons,eval_nil,termValue_variables,map_one,add_zero]

end CycleQ2SegreModularCubicMonomialBinding

#print axioms CycleQ2SegreModularCubicMonomialBinding.value_monomialCubic
end
end


/- Component: continuation_3/SegreModularCubicPairingExpressions.lean -/
section
namespace CycleQ2SegreModularCubicPairing
open CycleQ2SparseModularFunctional CycleQ2SegreModularCubicData

def cubicDot (W : WeightData) (c : Fin 9) : ℕ :=
  (dot W 0 0 (0,0,0,0,0) (flattenTowersData (cubicTable 0 c)) +
   dot W 0 1 (0,0,0,0,0) (flattenTowersData (cubicTable 1 c)) +
   dot W 0 2 (0,0,0,0,0) (flattenTowersData (cubicTable 2 c))) % 109

end CycleQ2SegreModularCubicPairing
end


