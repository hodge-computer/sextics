import Proposal.CurveAndSeedCechCoordinates
import Proposal.GeometricSeedSurfaceGradient

/-!
# The universal surface Čech quotient and coefficient base change
-/

set_option Elab.async false

/- Component: continuation_20261112/UniversalSurfaceFiniteFree.lean -/
section
/-!
# The normalized universal incidence surface is finite free over three coordinates

The two equations are the actual full invariant cubic and sextic, with their
distinguished coefficients normalized to one.  No seed specialization, smoothness,
or cohomological flatness is assumed.  The nine basis vectors are the original
classes of x0^a*w^b.  This supplies the missing relative input for the explicit
three-coordinate Cech calculation.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurface

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree
open scoped MonomialOrder

variable (R : Type*) [CommRing R]



























end CycleQ2UniversalSurface

#print axioms CycleQ2UniversalSurface.surfaceBasis_apply
#print axioms CycleQ2UniversalSurface.surfaceQuotient_rank_nine
end
end

/- Component: continuation_20261112/CharacterTopCech.lean -/
section
/-!
# Top Cech coordinates in all three characters

The degree remains zero.  The character is retained as an explicit parameter,
so the ambient-test character-one piece is computed rather than identified
with the previously checked character-zero piece.  Their respective ranks
are eight and seven.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CharacterTopCech

open CycleQ2SeedCechThreeOpen
open CycleQ2SeedCechTopCohomology (SmallExponents topExponent topExponent_negative
  topExponent_injective)
open scoped BigOperators

section Indices
variable (χ : ZMod 3)

abbrev TopIndex :=
  {q : ShiftIndex × SmallExponents // shiftedGrade q.1 (topExponent q.2) = (0,χ)}

theorem topIndex_count : Fintype.card (TopIndex χ) = if χ=0 then 7 else 8 := by
  fin_cases χ <;> decide

def topCoordinate (q : TopIndex χ) : ShiftIndex × LaurentExponent :=
  (q.val.1, topExponent q.val.2)

theorem topCoordinate_injective : Function.Injective (topCoordinate χ) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q : ShiftIndex × LaurentExponent => q.1) hab
  · exact topExponent_injective
      (congrArg (fun q : ShiftIndex × LaurentExponent => q.2) hab)

/-- The finite exponent bound uses degree zero and is uniform in the character. -/
theorem exists_topIndex (ab : ShiftIndex) (e : LaurentExponent)
    (he : ∀ i, e i < 0) (hg : shiftedGrade ab e = (0,χ)) :
    ∃ q : TopIndex χ, topCoordinate χ q = (ab,e) := by
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
  refine ⟨⟨(ab,v), ?_⟩, ?_⟩
  · simpa only [hv] using hg
  · exact Prod.ext rfl hv

end Indices

variable (R : Type*) [CommRing R] (χ : ZMod 3)



def topProjection : gradedFamilies R χ →ₗ[R] ((TopIndex χ) →₀ R) where
  toFun p := Finsupp.equivFunOnFinite.symm
    (fun q ↦ (p.val q.val.1).coeff (topExponent q.val.2))
  map_add' p q := by ext i; simp [AddMonoidAlgebra.coeff_add]
  map_smul' c p := by ext i; simp [AddMonoidAlgebra.coeff_smul]

@[simp] theorem topProjection_apply (p : gradedFamilies R χ) (q : (TopIndex χ)) :
    topProjection R χ p q = (p.val q.val.1).coeff (topExponent q.val.2) := rfl

def basisFamily (q : (TopIndex χ)) : Family R := fun ab ↦
  if ab = q.val.1 then AddMonoidAlgebra.single (topExponent q.val.2) 1 else 0

@[simp] theorem basisFamily_coeff (q : (TopIndex χ)) (ab : ShiftIndex) (e : LaurentExponent) :
    (basisFamily R χ q ab).coeff e = if topCoordinate χ q = (ab, e) then 1 else 0 := by
  classical
  by_cases ha : ab = q.val.1
  · subst ab
    by_cases he : e = topExponent q.val.2
    · subst e; simp [basisFamily, topCoordinate]
    · simp [basisFamily, topCoordinate, he, Ne.symm he]
  · have ha' : q.val.1 ≠ ab := Ne.symm ha
    simp [basisFamily, topCoordinate, ha, ha']

def basisSection (q : (TopIndex χ)) : gradedFamilies R χ := ⟨basisFamily R χ q, by
  intro ab e he
  rw [basisFamily_coeff]
  split
  · next h =>
      have ha : q.val.1 = ab := congrArg Prod.fst h
      have h_exp : topExponent q.val.2 = e := congrArg Prod.snd h
      exact False.elim (he (ha ▸ h_exp ▸ q.property))
  · rfl⟩

@[simp] theorem topProjection_basisSection (q : (TopIndex χ)) :
    topProjection R χ (basisSection R χ q) = Finsupp.single q 1 := by
  ext j
  change (basisFamily R χ q j.val.1).coeff (topExponent j.val.2) = _
  rw [basisFamily_coeff]
  change (if topCoordinate χ q = topCoordinate χ j then 1 else 0) = _
  simp only [(topCoordinate_injective χ).eq_iff, Finsupp.single_apply]

theorem topProjection_surjective : Function.Surjective (topProjection R χ) := by
  intro p
  refine ⟨∑ q : (TopIndex χ), p q • basisSection R χ q, ?_⟩
  ext q
  simp

def poleSubmodule (s : Finset (Fin 3)) : Submodule R (gradedFamilies R χ) where
  carrier := {p | ∀ ab, HasPoles s (p.val ab)}
  zero_mem' := by intro ab e i hi hneg; simp
  add_mem' hp hq := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_add, hp ab e i hi hneg, hq ab e i hi hneg]
  smul_mem' c p hp := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_smul, hp ab e i hi hneg]

/-- The sum of the three pair-open images in the triple-open graded space. -/
def topBoundary : Submodule R (gradedFamilies R χ) :=
  poleSubmodule R χ {0, 1} ⊔ poleSubmodule R χ {0, 2} ⊔ poleSubmodule R χ {1, 2}

theorem topProjection_zero_iff (p : gradedFamilies R χ) :
    topProjection R χ p = 0 ↔
      ∀ ab e, (∀ i, e i < 0) → (p.val ab).coeff e = 0 := by
  constructor
  · intro hp ab e he
    by_cases hg : shiftedGrade ab e = (0,χ)
    · obtain ⟨q, hq⟩ := exists_topIndex χ ab e he hg
      have ha : q.val.1 = ab := congrArg Prod.fst hq
      have hx : topExponent q.val.2 = e := congrArg Prod.snd hq
      have hh := congrArg (fun f : (TopIndex χ) →₀ R ↦ f q) hp
      simpa only [topProjection_apply, ha, hx, Finsupp.zero_apply] using hh
    · exact p.property ab e hg
  · intro hp
    ext q
    exact hp q.val.1 (topExponent q.val.2) (topExponent_negative q.val.2)

theorem poleSubmodule_le_ker (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∉ s) :
    poleSubmodule R χ s ≤ LinearMap.ker (topProjection R χ) := by
  intro p hp
  rw [LinearMap.mem_ker, topProjection_zero_iff]
  intro ab e he
  exact hp ab e i hi (he i)

theorem topBoundary_le_ker : topBoundary R χ ≤ LinearMap.ker (topProjection R χ) :=
  sup_le (sup_le (poleSubmodule_le_ker R χ {0, 1} 2 (by decide))
    (poleSubmodule_le_ker R χ {0, 2} 1 (by decide)))
      (poleSubmodule_le_ker R χ {1, 2} 0 (by decide))

def filterSection (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R χ) : gradedFamilies R χ :=
  ⟨fun ab ↦ AddMonoidAlgebra.ofCoeff ((p.val ab).coeff.filter P), by
    intro ab e he
    change (if P e then (p.val ab).coeff e else 0) = 0
    split <;> simp [p.property ab e he]⟩

@[simp] theorem filterSection_coeff (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R χ) (ab : ShiftIndex) (e : LaurentExponent) :
    ((filterSection R χ P p).val ab).coeff e = if P e then (p.val ab).coeff e else 0 := rfl

theorem filterSection_mem_poleSubmodule (P : LaurentExponent → Prop) [DecidablePred P]
    (s : Finset (Fin 3))
    (hP : ∀ e, P e → ∀ i, i ∉ s → 0 ≤ e i) (p : gradedFamilies R χ) :
    filterSection R χ P p ∈ poleSubmodule R χ s := by
  intro ab e i hi hneg
  rw [filterSection_coeff]
  split
  · next he => exact False.elim ((not_le.mpr hneg) (hP e he i hi))
  · rfl

/-- Projection onto negative exponents loses exactly the three pair-open images. -/
theorem topBoundary_eq_ker : topBoundary R χ = LinearMap.ker (topProjection R χ) := by
  apply le_antisymm (topBoundary_le_ker R χ)
  intro p hp
  have hz := (topProjection_zero_iff R χ p).mp hp
  let p01 := filterSection R χ (fun e ↦ 0 ≤ e 2) p
  let p02 := filterSection R χ (fun e ↦ e 2 < 0 ∧ 0 ≤ e 1) p
  let p12 := filterSection R χ (fun e ↦ e 2 < 0 ∧ e 1 < 0 ∧ 0 ≤ e 0) p
  have h01 : p01 ∈ poleSubmodule R χ {0, 1} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · exact he
  have h02 : p02 ∈ poleSubmodule R χ {0, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · exact he.2
    · simp at hi
  have h12 : p12 ∈ poleSubmodule R χ {1, 2} := by
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
    · exact (show poleSubmodule R χ {0, 1} ≤ topBoundary R χ from
        le_sup_of_le_left le_sup_left) h01
    · exact (show poleSubmodule R χ {0, 2} ≤ topBoundary R χ from
        le_sup_of_le_left le_sup_right) h02
  · exact (show poleSubmodule R χ {1, 2} ≤ topBoundary R χ from le_sup_right) h12

abbrev TopCechQuotient := gradedFamilies R χ ⧸ topBoundary R χ

def topCechEquiv : TopCechQuotient R χ ≃ₗ[R] ((TopIndex χ) →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (topBoundary_eq_ker R χ)).trans
    ((topProjection R χ).quotKerEquivOfSurjective (topProjection_surjective R χ))

@[simp] theorem topCechEquiv_mk (p : gradedFamilies R χ) :
    topCechEquiv R χ (Submodule.Quotient.mk p) = topProjection R χ p := by
  simp [topCechEquiv]

def topCechBasis : Module.Basis (TopIndex χ) R (TopCechQuotient R χ) :=
  Finsupp.basisSingleOne.map (topCechEquiv R χ).symm

@[simp] theorem topCechBasis_apply (q : (TopIndex χ)) :
    topCechBasis R χ q = Submodule.Quotient.mk (basisSection R χ q) := by
  apply (topCechEquiv R χ).injective
  simp [topCechBasis]

theorem topCech_rank [Nontrivial R] : Module.finrank R (TopCechQuotient R χ) = if χ=0 then 7 else 8 := by
  rw [Module.finrank_eq_card_basis (topCechBasis R χ), topIndex_count χ]

end CycleQ2CharacterTopCech

#print axioms CycleQ2CharacterTopCech.topIndex_count
#print axioms CycleQ2CharacterTopCech.topCechBasis_apply
#print axioms CycleQ2CharacterTopCech.topCech_rank
end
end


/- Source component moved verbatim to Proposal.GeometricSeedSurfaceSparseBase. -/

/- Component: continuation_20261112/UniversalSurfaceLocalizedBasis.lean -/
section
/-! # The actual localized universal surface quotient in the nine Laurent coordinates -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceLocalizedBasis

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization

variable (R : Type*) [CommRing R]













/-- Exactness of the three-open complex on actual localized universal surface rings,
expressed through their injective common Laurent coordinates. -/
theorem localized_nineSummand_kernel [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (g : LaurentGrade)
    (p01 : SurfaceLocal R hcoeff Fcoeff {0, 1}) (p02 : SurfaceLocal R hcoeff Fcoeff {0, 2})
    (p12 : SurfaceLocal R hcoeff Fcoeff {1, 2})
    (hg01 : ∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {0, 1} p01 ab))
    (hg02 : ∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {0, 2} p02 ab))
    (hg12 : ∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {1, 2} p12 ab))
    (hc : ∀ ab, localizedCoordinates R hcoeff Fcoeff {0, 1} p01 ab -
      localizedCoordinates R hcoeff Fcoeff {0, 2} p02 ab +
      localizedCoordinates R hcoeff Fcoeff {1, 2} p12 ab = 0) :
    ∃ (q0 : SurfaceLocal R hcoeff Fcoeff {0}) (q1 : SurfaceLocal R hcoeff Fcoeff {1})
      (q2 : SurfaceLocal R hcoeff Fcoeff {2}),
      (∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {0} q0 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {1} q1 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {2} q2 ab)) ∧
      (∀ ab, localizedCoordinates R hcoeff Fcoeff {0, 1} p01 ab =
        localizedCoordinates R hcoeff Fcoeff {1} q1 ab - localizedCoordinates R hcoeff Fcoeff {0} q0 ab) ∧
      (∀ ab, localizedCoordinates R hcoeff Fcoeff {0, 2} p02 ab =
        localizedCoordinates R hcoeff Fcoeff {2} q2 ab - localizedCoordinates R hcoeff Fcoeff {0} q0 ab) ∧
      (∀ ab, localizedCoordinates R hcoeff Fcoeff {1, 2} p12 ab =
        localizedCoordinates R hcoeff Fcoeff {2} q2 ab - localizedCoordinates R hcoeff Fcoeff {1} q1 ab) := by
  obtain ⟨q0, q1, q2, h0, h1, h2, hg0, hg1, hg2, he01, he02, he12⟩ :=
    nineSummand_kernel g
      (localizedCoordinates R hcoeff Fcoeff {0, 1} p01)
      (localizedCoordinates R hcoeff Fcoeff {0, 2} p02)
      (localizedCoordinates R hcoeff Fcoeff {1, 2} p12)
      (localizedCoordinates_hasPoles R hcoeff Fcoeff {0, 1} p01)
      (localizedCoordinates_hasPoles R hcoeff Fcoeff {0, 2} p02)
      (localizedCoordinates_hasPoles R hcoeff Fcoeff {1, 2} p12)
      hg01 hg02 hg12 hc
  obtain ⟨q0', hq0⟩ := (mem_range_localizedCoordinates R hcoeff Fcoeff {0} q0).mpr h0
  obtain ⟨q1', hq1⟩ := (mem_range_localizedCoordinates R hcoeff Fcoeff {1} q1).mpr h1
  obtain ⟨q2', hq2⟩ := (mem_range_localizedCoordinates R hcoeff Fcoeff {2} q2).mpr h2
  refine ⟨q0', q1', q2', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hq0, hq1, hq2] <;> assumption

end CycleQ2UniversalSurfaceLocalizedBasis

#print axioms CycleQ2UniversalSurfaceLocalizedBasis.mem_range_localizedCoordinates

#print axioms CycleQ2UniversalSurfaceLocalizedBasis.localized_nineSummand_kernel
end
end

/- Component: continuation_20261112/UniversalSurfaceCoordinateCover.lean -/
section
/-!
# The three coordinate charts cover the entire relative projective surface

The three actual opens used by the Cech computation are x1, x2, x3.
They cover every relevant prime of every normalized universal surface,
over any commutative coefficient ring.  No smoothness is required.
This is a statement about the original polynomial quotient and its primes;
it is not yet a comparison with derived sheaf cohomology.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceCoordinateCover

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree CycleQ2UniversalSurface

theorem cubic_tail_has_base_coordinate (e : FullCubicTailIndex) :
    ∃ j : Fin 3, fullExponentOf e.val.val (remainingIndex j) ≠ 0 := by
  by_contra hn
  have hz (j : Fin 3) : fullExponentOf e.val.val (remainingIndex j) = 0 := by
    by_contra hj
    exact hn ⟨j,hj⟩
  have h1 : (e.val.val 1).val = 0 := by simpa [remainingIndex] using hz 0
  have h2 : (e.val.val 2).val = 0 := by simpa [remainingIndex] using hz 1
  have h3 : (e.val.val 3).val = 0 := by simpa [remainingIndex] using hz 2
  have hd := e.val.property.1
  have hc := e.val.property.2
  have ht := e.property
  simp only [fullDegree, fullCharacter] at hd hc
  omega

theorem sextic_tail_has_non_w_coordinate (e : FullSexticTailIndex) :
    ∃ j : Fin 4, fullExponentOf e.val.val j.castSucc ≠ 0 := by
  by_contra hn
  have hz (j : Fin 4) : fullExponentOf e.val.val j.castSucc = 0 := by
    by_contra hj
    exact hn ⟨j,hj⟩
  have h0 : (e.val.val 0).val = 0 := by simpa using hz 0
  have h1 : (e.val.val 1).val = 0 := by simpa using hz 1
  have h2 : (e.val.val 2).val = 0 := by simpa using hz 2
  have h3 : (e.val.val 3).val = 0 := by simpa using hz 3
  have hd := e.val.property.1
  have ht := e.property
  simp only [fullDegree] at hd
  omega

variable {R : Type*} [CommRing R]

theorem all_coordinates_mem_of_base_coordinates
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : Ideal (Poly R)) [p.IsPrime]
    (hh : normalizedFullCubic hcoeff ∈ p) (hF : normalizedFullSextic Fcoeff ∈ p)
    (hx : ∀ j : Fin 3, X (remainingIndex j) ∈ p) :
    ∀ j : Fin 5, X j ∈ p := by
  classical
  have hctail : (∑ e : FullCubicTailIndex,
      monomial (fullExponentOf e.val.val) (hcoeff e)) ∈ p := by
    apply Ideal.sum_mem
    intro e _
    obtain ⟨j,hj⟩ := cubic_tail_has_base_coordinate e
    exact p.mem_of_dvd (X_dvd_monomial.mpr (Or.inr hj)) (hx j)
  have h0pow : (X 0 : Poly R) ^ 3 ∈ p := by
    simpa only [normalizedFullCubic, add_sub_cancel_right, X_pow_eq_monomial] using
      p.sub_mem hh hctail
  have h0 : (X 0 : Poly R) ∈ p := (inferInstance : p.IsPrime).mem_of_pow_mem 3 h0pow
  have hnonw (j : Fin 4) : (X j.castSucc : Poly R) ∈ p := by
    fin_cases j
    · exact h0
    · exact hx 0
    · exact hx 1
    · exact hx 2
  have hFtail : (∑ e : FullSexticTailIndex,
      monomial (fullExponentOf e.val.val) (Fcoeff e)) ∈ p := by
    apply Ideal.sum_mem
    intro e _
    obtain ⟨j,hj⟩ := sextic_tail_has_non_w_coordinate e
    exact p.mem_of_dvd (X_dvd_monomial.mpr (Or.inr hj)) (hnonw j)
  have h4pow : (X 4 : Poly R) ^ 3 ∈ p := by
    simpa only [normalizedFullSextic, add_sub_cancel_right, X_pow_eq_monomial] using
      p.sub_mem hF hFtail
  have h4 : (X 4 : Poly R) ∈ p := (inferInstance : p.IsPrime).mem_of_pow_mem 3 h4pow
  intro j
  fin_cases j
  · exact h0
  · exact hx 0
  · exact hx 1
  · exact hx 2
  · exact h4

theorem polynomial_prime_coordinate_cover
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : Ideal (Poly R)) [p.IsPrime]
    (hI : surfaceIdeal R hcoeff Fcoeff ≤ p)
    (hrelevant : ∃ j : Fin 5, X j ∉ p) :
    ∃ j : Fin 3, X (remainingIndex j) ∉ p := by
  by_contra hn
  have hx (j : Fin 3) : (X (remainingIndex j) : Poly R) ∈ p := by
    by_contra hj
    exact hn ⟨j,hj⟩
  have hh := hI (Ideal.subset_span (show normalizedFullCubic hcoeff ∈
    ({normalizedFullCubic hcoeff, normalizedFullSextic Fcoeff} : Set (Poly R)) from
      by simp))
  have hF := hI (Ideal.subset_span (show normalizedFullSextic Fcoeff ∈
    ({normalizedFullCubic hcoeff, normalizedFullSextic Fcoeff} : Set (Poly R)) from
      by simp))
  obtain ⟨j,hj⟩ := hrelevant
  exact hj (all_coordinates_mem_of_base_coordinates hcoeff Fcoeff p hh hF hx j)

/-- Consequently the exact three opens used by the relative Cech model
cover all relevant primes of the actual surface quotient. -/
theorem surface_prime_coordinate_cover
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : Ideal (SurfaceRing R hcoeff Fcoeff)) [p.IsPrime]
    (hrelevant : ∃ j : Fin 5, Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff) (X j) ∉ p) :
    ∃ j : Fin 3, Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff)
      (X (remainingIndex j)) ∉ p := by
  let q : Ideal (Poly R) := p.comap (Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff))
  haveI : q.IsPrime := Ideal.IsPrime.comap _
  have hI : surfaceIdeal R hcoeff Fcoeff ≤ q := by
    intro a ha
    change Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff) a ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact p.zero_mem
  exact polynomial_prime_coordinate_cover hcoeff Fcoeff q hI hrelevant

end CycleQ2UniversalSurfaceCoordinateCover

#print axioms CycleQ2UniversalSurfaceCoordinateCover.surface_prime_coordinate_cover
end
end

/- Component: continuation_20261112/UniversalSurfaceRestrictions.lean -/
section
/-! # Canonical restriction maps and the actual coordinate Čech kernel -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceRestrictions

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis

variable (R : Type*) [CommRing R]








/-- Every graded one-cocycle for the canonical three-coordinate localization
complex of the actual universal normalized quotient is an actual coboundary. -/
theorem coordinateCech_exact [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (g : LaurentGrade)
    (p01 : SurfaceLocal R hcoeff Fcoeff {0, 1}) (p02 : SurfaceLocal R hcoeff Fcoeff {0, 2})
    (p12 : SurfaceLocal R hcoeff Fcoeff {1, 2})
    (hg01 : ∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {0, 1} p01 ab))
    (hg02 : ∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {0, 2} p02 ab))
    (hg12 : ∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {1, 2} p12 ab))
    (hc : restriction R hcoeff Fcoeff (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by decide) p01 -
      restriction R hcoeff Fcoeff (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide) p02 +
      restriction R hcoeff Fcoeff (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide) p12 = 0) :
    ∃ (q0 : SurfaceLocal R hcoeff Fcoeff {0}) (q1 : SurfaceLocal R hcoeff Fcoeff {1})
      (q2 : SurfaceLocal R hcoeff Fcoeff {2}),
      (∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {0} q0 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {1} q1 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R hcoeff Fcoeff {2} q2 ab)) ∧
      p01 = restriction R hcoeff Fcoeff (show ({1} : Finset (Fin 3)) ⊆ {0, 1} by decide) q1 -
        restriction R hcoeff Fcoeff (show ({0} : Finset (Fin 3)) ⊆ {0, 1} by decide) q0 ∧
      p02 = restriction R hcoeff Fcoeff (show ({2} : Finset (Fin 3)) ⊆ {0, 2} by decide) q2 -
        restriction R hcoeff Fcoeff (show ({0} : Finset (Fin 3)) ⊆ {0, 2} by decide) q0 ∧
      p12 = restriction R hcoeff Fcoeff (show ({2} : Finset (Fin 3)) ⊆ {1, 2} by decide) q2 -
        restriction R hcoeff Fcoeff (show ({1} : Finset (Fin 3)) ⊆ {1, 2} by decide) q1 := by
  have hc' (ab : ShiftIndex) : localizedCoordinates R hcoeff Fcoeff {0, 1} p01 ab -
      localizedCoordinates R hcoeff Fcoeff {0, 2} p02 ab +
      localizedCoordinates R hcoeff Fcoeff {1, 2} p12 ab = 0 := by
    have hh := congrArg (fun z ↦ localizedCoordinates R hcoeff Fcoeff Finset.univ z ab) hc
    simpa only [map_add, map_sub, map_zero, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
      coordinates_restriction] using hh
  obtain ⟨q0, q1, q2, hg0, hg1, hg2, he01, he02, he12⟩ :=
    localized_nineSummand_kernel R hcoeff Fcoeff g p01 p02 p12 hg01 hg02 hg12 hc'
  refine ⟨q0, q1, q2, hg0, hg1, hg2, ?_, ?_, ?_⟩
  · apply localizedCoordinates_injective R hcoeff Fcoeff {0, 1}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he01 ab
  · apply localizedCoordinates_injective R hcoeff Fcoeff {0, 2}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he02 ab
  · apply localizedCoordinates_injective R hcoeff Fcoeff {1, 2}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he12 ab

end CycleQ2UniversalSurfaceRestrictions

#print axioms CycleQ2UniversalSurfaceRestrictions.coordinateCech_exact
end
end


/- Source component moved verbatim to Proposal.GeometricSeedSurfaceGradient. -/

/- Component: continuation_20261112/UniversalSurfaceLinearCoordinates.lean -/
section
/-! # Scalar compatibility of the actual localized universal surface coordinates -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceLinearCoordinates

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions

variable (R : Type*) [CommRing R]







end CycleQ2UniversalSurfaceLinearCoordinates

#print axioms CycleQ2UniversalSurfaceLinearCoordinates.linearCoordinates
#print axioms CycleQ2UniversalSurfaceLinearCoordinates.restrictionLinear
end
end


/- Source component moved verbatim to Proposal.GeometricSeedSurfaceGradient. -/

/- Component: continuation_20261112/UniversalSurfaceTopCech.lean -/
section
/-! # The seven-dimensional quotient of the actual universal normalized localization complex -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceTopCech

open CycleQ2IncidenceNormalForm CycleQ2UniversalSurface CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates CycleQ2SeedCechTopCohomology

variable (R : Type*) [CommRing R] [Nontrivial R]

/-- Degree-zero, character-zero sections inside the actual coordinate localization. -/
def gradedLocal (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) : Submodule R (SurfaceLocal R hcoeff Fcoeff s) :=
  (gradedFamilies R).comap (linearCoordinates R hcoeff Fcoeff s)

def gradedCoordinates (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    gradedLocal R hcoeff Fcoeff s →ₗ[R] gradedFamilies R where
  toFun p := ⟨linearCoordinates R hcoeff Fcoeff s p.val, p.property⟩
  map_add' p q := by apply Subtype.ext; exact map_add (linearCoordinates R hcoeff Fcoeff s) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (linearCoordinates R hcoeff Fcoeff s) c p.val

@[simp] theorem gradedCoordinates_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (p : gradedLocal R hcoeff Fcoeff s) :
    (gradedCoordinates R hcoeff Fcoeff s p).val = localizedCoordinates R hcoeff Fcoeff s p.val := rfl

theorem gradedCoordinates_injective (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    Function.Injective (gradedCoordinates R hcoeff Fcoeff s) := by
  intro p q hpq
  apply Subtype.ext
  exact localizedCoordinates_injective R hcoeff Fcoeff s (congrArg Subtype.val hpq)

theorem gradedCoordinates_range (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    LinearMap.range (gradedCoordinates R hcoeff Fcoeff s) = poleSubmodule R s := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ ab
    exact localizedCoordinates_hasPoles R hcoeff Fcoeff s q.val ab
  · intro hp
    obtain ⟨q, hq⟩ := (mem_range_localizedCoordinates R hcoeff Fcoeff s p.val).mpr hp
    have hqg : q ∈ gradedLocal R hcoeff Fcoeff s := by
      change linearCoordinates R hcoeff Fcoeff s q ∈ gradedFamilies R
      rw [linearCoordinates_apply, hq]
      exact p.property
    refine ⟨⟨q, hqg⟩, ?_⟩
    exact Subtype.ext hq

def totalEquiv (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : gradedLocal R hcoeff Fcoeff Finset.univ ≃ₗ[R] gradedFamilies R :=
  LinearEquiv.ofBijective (gradedCoordinates R hcoeff Fcoeff Finset.univ)
    ⟨gradedCoordinates_injective R hcoeff Fcoeff Finset.univ, by
      intro p
      have hp : p ∈ poleSubmodule R Finset.univ := by
        intro ab e i hi _
        exact False.elim (hi (Finset.mem_univ i))
      rw [← gradedCoordinates_range R hcoeff Fcoeff Finset.univ] at hp
      exact hp⟩

@[simp] theorem totalEquiv_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (p : gradedLocal R hcoeff Fcoeff Finset.univ) :
    totalEquiv R hcoeff Fcoeff p = gradedCoordinates R hcoeff Fcoeff Finset.univ p := rfl

def gradedRestriction (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    gradedLocal R hcoeff Fcoeff s →ₗ[R] gradedLocal R hcoeff Fcoeff t where
  toFun p := ⟨restrictionLinear R hcoeff Fcoeff hst p.val, by
    intro ab
    change HasGrade ab 0 (localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst p.val) ab)
    rw [coordinates_restriction]
    exact p.property ab⟩
  map_add' p q := by apply Subtype.ext; exact map_add (restrictionLinear R hcoeff Fcoeff hst) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (restrictionLinear R hcoeff Fcoeff hst) c p.val

theorem gradedCoordinates_restriction (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    (gradedCoordinates R hcoeff Fcoeff t).comp (gradedRestriction R hcoeff Fcoeff hst) =
      gradedCoordinates R hcoeff Fcoeff s := by
  ext p ab e
  change (localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst p.val) ab).coeff e =
    (localizedCoordinates R hcoeff Fcoeff s p.val ab).coeff e
  rw [coordinates_restriction]

/-- The boundary submodule is the sum of the images of the actual three
canonical ring restrictions from pair-open sections. -/
def actualBoundary (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : Submodule R (gradedLocal R hcoeff Fcoeff Finset.univ) :=
  LinearMap.range (gradedRestriction R hcoeff Fcoeff (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R hcoeff Fcoeff (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R hcoeff Fcoeff (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide))

theorem map_actualBoundary (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    (actualBoundary R hcoeff Fcoeff).map (totalEquiv R hcoeff Fcoeff).toLinearMap = topBoundary R := by
  change (actualBoundary R hcoeff Fcoeff).map (gradedCoordinates R hcoeff Fcoeff Finset.univ) = _
  simp only [actualBoundary, Submodule.map_sup, ← LinearMap.range_comp,
    gradedCoordinates_restriction, gradedCoordinates_range, topBoundary]

abbrev ActualTopCechQuotient (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :=
  gradedLocal R hcoeff Fcoeff Finset.univ ⧸ actualBoundary R hcoeff Fcoeff

def actualTopEquiv (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : ActualTopCechQuotient R hcoeff Fcoeff ≃ₗ[R] TopCechQuotient R :=
  Submodule.Quotient.equiv _ _ (totalEquiv R hcoeff Fcoeff) (map_actualBoundary R hcoeff Fcoeff)

def actualTopBasis (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : Module.Basis TopIndex R (ActualTopCechQuotient R hcoeff Fcoeff) :=
  (topCechBasis R).map (actualTopEquiv R hcoeff Fcoeff).symm

@[simp] theorem actualTopBasis_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (q : TopIndex) :
    actualTopEquiv R hcoeff Fcoeff (actualTopBasis R hcoeff Fcoeff q) =
      Submodule.Quotient.mk (basisSection R q) := by
  simp [actualTopBasis]

theorem actualTop_rank_seven (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (ActualTopCechQuotient R hcoeff Fcoeff) = 7 := by
  rw [Module.finrank_eq_card_basis (actualTopBasis R hcoeff Fcoeff), topIndex_count]

end CycleQ2UniversalSurfaceTopCech

#print axioms CycleQ2UniversalSurfaceTopCech.actualTop_rank_seven
end
end

/- Component: continuation_20261112/UniversalSurfaceCharacterCech.lean -/
section
/-! # The actual universal localization complex in every character -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceCharacterCech

open CycleQ2IncidenceNormalForm CycleQ2UniversalSurface CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates CycleQ2CharacterTopCech

variable (R : Type*) [CommRing R] [Nontrivial R] (χ : ZMod 3)


def gradedCoordinates (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    gradedLocal R χ hcoeff Fcoeff s →ₗ[R] gradedFamilies R χ where
  toFun p := ⟨linearCoordinates R hcoeff Fcoeff s p.val, p.property⟩
  map_add' p q := by apply Subtype.ext; exact map_add (linearCoordinates R hcoeff Fcoeff s) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (linearCoordinates R hcoeff Fcoeff s) c p.val

@[simp] theorem gradedCoordinates_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (p : gradedLocal R χ hcoeff Fcoeff s) :
    (gradedCoordinates R χ hcoeff Fcoeff s p).val = localizedCoordinates R hcoeff Fcoeff s p.val := rfl

theorem gradedCoordinates_injective (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    Function.Injective (gradedCoordinates R χ hcoeff Fcoeff s) := by
  intro p q hpq
  apply Subtype.ext
  exact localizedCoordinates_injective R hcoeff Fcoeff s (congrArg Subtype.val hpq)

theorem gradedCoordinates_range (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    LinearMap.range (gradedCoordinates R χ hcoeff Fcoeff s) = poleSubmodule R χ s := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ ab
    exact localizedCoordinates_hasPoles R hcoeff Fcoeff s q.val ab
  · intro hp
    obtain ⟨q, hq⟩ := (mem_range_localizedCoordinates R hcoeff Fcoeff s p.val).mpr hp
    have hqg : q ∈ gradedLocal R χ hcoeff Fcoeff s := by
      change linearCoordinates R hcoeff Fcoeff s q ∈ gradedFamilies R χ
      rw [linearCoordinates_apply, hq]
      exact p.property
    refine ⟨⟨q, hqg⟩, ?_⟩
    exact Subtype.ext hq

def totalEquiv (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : gradedLocal R χ hcoeff Fcoeff Finset.univ ≃ₗ[R] gradedFamilies R χ :=
  LinearEquiv.ofBijective (gradedCoordinates R χ hcoeff Fcoeff Finset.univ)
    ⟨gradedCoordinates_injective R χ hcoeff Fcoeff Finset.univ, by
      intro p
      have hp : p ∈ poleSubmodule R χ Finset.univ := by
        intro ab e i hi _
        exact False.elim (hi (Finset.mem_univ i))
      rw [← gradedCoordinates_range R χ hcoeff Fcoeff Finset.univ] at hp
      exact hp⟩

@[simp] theorem totalEquiv_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (p : gradedLocal R χ hcoeff Fcoeff Finset.univ) :
    totalEquiv R χ hcoeff Fcoeff p = gradedCoordinates R χ hcoeff Fcoeff Finset.univ p := rfl


theorem gradedCoordinates_restriction (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    (gradedCoordinates R χ hcoeff Fcoeff t).comp (gradedRestriction R χ hcoeff Fcoeff hst) =
      gradedCoordinates R χ hcoeff Fcoeff s := by
  ext p ab e
  change (localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst p.val) ab).coeff e =
    (localizedCoordinates R hcoeff Fcoeff s p.val ab).coeff e
  rw [coordinates_restriction]


theorem map_actualBoundary (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    (actualBoundary R χ hcoeff Fcoeff).map (totalEquiv R χ hcoeff Fcoeff).toLinearMap = topBoundary R χ := by
  change (actualBoundary R χ hcoeff Fcoeff).map (gradedCoordinates R χ hcoeff Fcoeff Finset.univ) = _
  simp only [actualBoundary, Submodule.map_sup, ← LinearMap.range_comp,
    gradedCoordinates_restriction, gradedCoordinates_range, topBoundary]


def actualTopEquiv (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : ActualTopCechQuotient R χ hcoeff Fcoeff ≃ₗ[R] TopCechQuotient R χ :=
  Submodule.Quotient.equiv _ _ (totalEquiv R χ hcoeff Fcoeff) (map_actualBoundary R χ hcoeff Fcoeff)

def actualTopBasis (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : Module.Basis (TopIndex χ) R (ActualTopCechQuotient R χ hcoeff Fcoeff) :=
  (topCechBasis R χ).map (actualTopEquiv R χ hcoeff Fcoeff).symm

@[simp] theorem actualTopBasis_apply (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (q : (TopIndex χ)) :
    actualTopEquiv R χ hcoeff Fcoeff (actualTopBasis R χ hcoeff Fcoeff q) =
      Submodule.Quotient.mk (basisSection R χ q) := by
  simp [actualTopBasis]

theorem actualTop_rank (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (ActualTopCechQuotient R χ hcoeff Fcoeff) = if χ=0 then 7 else 8 := by
  rw [Module.finrank_eq_card_basis (actualTopBasis R χ hcoeff Fcoeff), topIndex_count χ]

theorem actualTop_rank_characterOne (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank R (ActualTopCechQuotient R (1 : ZMod 3) hcoeff Fcoeff) = 8 := by
  simpa using actualTop_rank R (1 : ZMod 3) hcoeff Fcoeff

end CycleQ2UniversalSurfaceCharacterCech

#print axioms CycleQ2UniversalSurfaceCharacterCech.actualTop_rank

#print axioms CycleQ2UniversalSurfaceCharacterCech.actualTop_rank_characterOne
end
end


/- Source component moved verbatim to Proposal.GeometricSeedSurfaceGradient. -/

/- Component: continuation_20261112/UniversalSurfaceCoefficientMap.lean -/
section
/-!
# Canonical coefficient specialization on the universal surface and its charts

All maps below are induced by the coefficient homomorphism on the actual
polynomial quotient and its actual coordinate localizations.  The Laurent
coordinate compatibility is a theorem about those maps, not their definition.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceCoefficientMap

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree CycleQ2UniversalSurface
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions

variable {R S : Type*} [CommRing R] [CommRing S]


















end CycleQ2UniversalSurfaceCoefficientMap

#print axioms CycleQ2UniversalSurfaceCoefficientMap.coordinates_surfaceMap
#print axioms CycleQ2UniversalSurfaceCoefficientMap.coordinates_localMap
#print axioms CycleQ2UniversalSurfaceCoefficientMap.localMap_restriction
end
end

/- Component: continuation_20261112/UniversalSurfaceCechPersistence.lean -/
section
/-!
# Base change and pointed persistence for actual top Cech classes

The cohomology is the quotient of the triple coordinate localization by
the images of the three actual pair-coordinate restriction maps, in degree
zero and invariant character.  Coefficient specialization is induced on
those actual localizations.  Thus the final nonvanishing implication is
about genuine classes in this complex, not a replacement scalar functional.

An application to a moving connecting class must still prove that its
specialization is the previously computed seed class.  No such comparison
is assumed or asserted here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceCechPersistence

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree CycleQ2UniversalSurface
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2SeedCechTopCohomology CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates
  CycleQ2UniversalSurfaceTopCech CycleQ2UniversalSurfaceCoefficientMap
open scoped TensorProduct

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem localMap_smul (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (c : R) (z : SurfaceLocal R hcoeff Fcoeff s) :
    localMap f hcoeff Fcoeff s (c • z) = f c • localMap f hcoeff Fcoeff s z := by
  simp only [Algebra.smul_def, map_mul]
  congr 1
  rw [IsScalarTower.algebraMap_apply R (SurfaceRing R hcoeff Fcoeff)
    (SurfaceLocal R hcoeff Fcoeff s), localMap_algebraMap]
  change algebraMap _ _ (Ideal.Quotient.mk _ (MvPolynomial.map f (C c))) = _
  rw [MvPolynomial.map_C]
  rfl

def gradedLocalMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) :
    gradedLocal R hcoeff Fcoeff s →ₛₗ[f]
      gradedLocal S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s where
  toFun p := ⟨localMap f hcoeff Fcoeff s p.val, by
    intro ab e he
    change (localizedCoordinates S _ _ s (localMap f hcoeff Fcoeff s p.val) ab).coeff e = 0
    rw [coordinates_localMap, laurentMap_coeff]
    exact (congrArg f (p.property ab e he)).trans (map_zero f)⟩
  map_add' p q := by apply Subtype.ext; exact map_add (localMap f hcoeff Fcoeff s) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact localMap_smul f hcoeff Fcoeff s c p.val

def actualCoordinates [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ActualTopCechQuotient R hcoeff Fcoeff ≃ₗ[R] (TopIndex →₀ R) :=
  (actualTopEquiv R hcoeff Fcoeff).trans (topCechEquiv R)

@[simp] theorem actualCoordinates_mk [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R hcoeff Fcoeff Finset.univ) :
    actualCoordinates hcoeff Fcoeff (Submodule.Quotient.mk p) =
      topProjection R (gradedCoordinates R hcoeff Fcoeff Finset.univ p) := by
  change topCechEquiv R (Submodule.Quotient.mk
    (gradedCoordinates R hcoeff Fcoeff Finset.univ p)) = _
  exact topCechEquiv_mk R _

theorem mem_actualBoundary_iff [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R hcoeff Fcoeff Finset.univ) :
    p ∈ actualBoundary R hcoeff Fcoeff ↔
      topProjection R (gradedCoordinates R hcoeff Fcoeff Finset.univ p) = 0 := by
  rw [← actualCoordinates_mk]
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

theorem gradedLocalMap_mem_boundary [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R hcoeff Fcoeff Finset.univ)
    (hp : p ∈ actualBoundary R hcoeff Fcoeff) :
    gradedLocalMap f hcoeff Fcoeff Finset.univ p ∈
      actualBoundary S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) := by
  apply (mem_actualBoundary_iff _ _ _).mpr
  ext q
  change (localizedCoordinates S _ _ Finset.univ
      (localMap f hcoeff Fcoeff Finset.univ p.val) q.val.1).coeff
      (topExponent q.val.2) = 0
  rw [coordinates_localMap, laurentMap_coeff]
  have hz := congrArg (fun z : TopIndex →₀ R => z q)
    ((mem_actualBoundary_iff hcoeff Fcoeff p).mp hp)
  change (localizedCoordinates R hcoeff Fcoeff Finset.univ p.val q.val.1).coeff
    (topExponent q.val.2) = 0 at hz
  rw [hz, map_zero]

/-- The map on actual cohomology induced by coefficient specialization. -/
def actualTopMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ActualTopCechQuotient R hcoeff Fcoeff →ₛₗ[f]
      ActualTopCechQuotient S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) :=
  (actualBoundary R hcoeff Fcoeff).mapQ
    (actualBoundary S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)))
    (gradedLocalMap f hcoeff Fcoeff Finset.univ)
    (by intro p hp; exact gradedLocalMap_mem_boundary f hcoeff Fcoeff p hp)

@[simp] theorem actualTopMap_mk [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R hcoeff Fcoeff Finset.univ) :
    actualTopMap f hcoeff Fcoeff (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (gradedLocalMap f hcoeff Fcoeff Finset.univ p) := rfl

theorem coordinates_actualTopMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R hcoeff Fcoeff) (q : TopIndex) :
    actualCoordinates (fun i => f (hcoeff i)) (fun i => f (Fcoeff i))
        (actualTopMap f hcoeff Fcoeff z) q =
      f (actualCoordinates hcoeff Fcoeff z q) := by
  refine Submodule.Quotient.induction_on _ z ?_
  intro p
  rw [actualTopMap_mk, actualCoordinates_mk, actualCoordinates_mk]
  change (localizedCoordinates S _ _ Finset.univ
      (localMap f hcoeff Fcoeff Finset.univ p.val) q.val.1).coeff
      (topExponent q.val.2) = _
  rw [coordinates_localMap, laurentMap_coeff]
  rfl

/-- In particular, faithful coefficient extension is faithful on these actual
cohomology classes.  No generic flatness theorem is a hypothesis. -/
theorem actualTopMap_injective [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hf : Function.Injective f)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Function.Injective (actualTopMap f hcoeff Fcoeff) := by
  intro z w hzw
  apply (actualCoordinates hcoeff Fcoeff).injective
  ext q
  apply hf
  simpa only [coordinates_actualTopMap] using
    congrArg (fun u => actualCoordinates (fun i => f (hcoeff i))
      (fun i => f (Fcoeff i)) u q) hzw

/-- The pointed generic-component condition, applied to actual cohomology.
Only the scalar kernel containment is supplied; freeness and coefficient
compatibility of this concrete Cech quotient were proved above. -/
theorem nonzero_generic_of_nonzero_specialization
    [Nontrivial R] [Nontrivial S] [Nontrivial T]
    (generic : R →+* S) (specialization : R →+* T)
    (hpointed : ∀ c : R, generic c = 0 → specialization c = 0)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R hcoeff Fcoeff)
    (hz : actualTopMap specialization hcoeff Fcoeff z ≠ 0) :
    actualTopMap generic hcoeff Fcoeff z ≠ 0 := by
  intro hzero
  apply hz
  apply (actualCoordinates (fun i => specialization (hcoeff i))
    (fun i => specialization (Fcoeff i))).injective
  ext q
  rw [coordinates_actualTopMap, map_zero, Finsupp.zero_apply]
  apply hpointed
  have hq := congrArg (fun u => actualCoordinates (fun i => generic (hcoeff i))
    (fun i => generic (Fcoeff i)) u q) hzero
  simpa only [coordinates_actualTopMap, map_zero, Finsupp.zero_apply] using hq

/-- Every coordinate functional of the actual top cohomology is natural
under coefficient specialization; these are the seven relative trace coordinates. -/
def traceCoordinate [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (q : TopIndex) : ActualTopCechQuotient R hcoeff Fcoeff →ₗ[R] R :=
  (Finsupp.lapply q).comp (actualCoordinates hcoeff Fcoeff).toLinearMap

@[simp] theorem traceCoordinate_specialization [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R hcoeff Fcoeff) (q : TopIndex) :
    traceCoordinate (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) q
      (actualTopMap f hcoeff Fcoeff z) = f (traceCoordinate hcoeff Fcoeff q z) :=
  coordinates_actualTopMap f hcoeff Fcoeff z q

end CycleQ2UniversalSurfaceCechPersistence

#print axioms CycleQ2UniversalSurfaceCechPersistence.actualTopMap_injective
#print axioms CycleQ2UniversalSurfaceCechPersistence.nonzero_generic_of_nonzero_specialization
#print axioms CycleQ2UniversalSurfaceCechPersistence.traceCoordinate_specialization
end
end

/- Component: continuation_20261112/UniversalSurfaceBaseChange.lean -/
section
/-!
# Tensor base change for the actual seven-dimensional Cech quotient

The equivalence below is proved to send s tensor z to s times the class
induced by the actual coefficient-specialization maps on the localized
surface.  Thus it is the canonical base-change map of this explicit complex,
not merely an unrelated equivalence between free modules of the same rank.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceBaseChange

open CycleQ2IncidenceNormalForm CycleQ2UniversalSurfaceTopCech
  CycleQ2SeedCechTopCohomology CycleQ2UniversalSurfaceCechPersistence
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Nontrivial R] [Nontrivial S]

def coordinateBasis (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Basis TopIndex R (ActualTopCechQuotient R hcoeff Fcoeff) :=
  Module.Basis.ofRepr (actualCoordinates hcoeff Fcoeff)

def actualBaseChange (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    (S ⊗[R] ActualTopCechQuotient R hcoeff Fcoeff) ≃ₗ[S]
      ActualTopCechQuotient S (fun i => algebraMap R S (hcoeff i))
        (fun i => algebraMap R S (Fcoeff i)) :=
  ((coordinateBasis hcoeff Fcoeff).baseChange S).repr.trans
    (actualCoordinates (fun i => algebraMap R S (hcoeff i))
      (fun i => algebraMap R S (Fcoeff i))).symm

@[simp] theorem actualBaseChange_tmul (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) (s : S)
    (z : ActualTopCechQuotient R hcoeff Fcoeff) :
    actualBaseChange hcoeff Fcoeff (s ⊗ₜ[R] z) =
      s • actualTopMap (algebraMap R S) hcoeff Fcoeff z := by
  apply (actualCoordinates (fun i => algebraMap R S (hcoeff i))
    (fun i => algebraMap R S (Fcoeff i))).injective
  ext q
  simp only [actualBaseChange, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.baseChange_repr_tmul, map_smul, Finsupp.smul_apply,
    coordinates_actualTopMap]
  change actualCoordinates hcoeff Fcoeff z q • s =
    s * algebraMap R S (actualCoordinates hcoeff Fcoeff z q)
  rw [Algebra.smul_def, mul_comm]

end CycleQ2UniversalSurfaceBaseChange

#print axioms CycleQ2UniversalSurfaceBaseChange.actualBaseChange_tmul
end
end

/- Component: continuation_20261112/UniversalSurfaceNormalization.lean -/
section
/-!
# The literal universal incidence surface and its normalized Cech model

The original cubic and sextic leading coefficients are inverted in the
existing universal parameter ring.  Dividing the equations by these units
does not change their ideal.  The same equality holds after every coefficient
specialization, so the finite free surface and its Cech complex above concern
the literal incidence surface, with no change of its coordinate functions.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceNormalization

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2SeedQuotientFiniteFree
  CycleQ2UniversalSurface CycleQ2UniversalSurfaceCoefficientMap

variable {R : Type*} [CommRing R]









variable (R) [IsDomain R]






end CycleQ2UniversalSurfaceNormalization

#print axioms CycleQ2UniversalSurfaceNormalization.fullSurfaceEquiv_mk
#print axioms CycleQ2UniversalSurfaceNormalization.mapped_universalIdeal_normalized
#print axioms CycleQ2UniversalSurfaceNormalization.seed_normalized_ideal
end
end

/- Component: continuation_20261112/UniversalSurfaceCharacterPersistence.lean -/
section
/-!
# Actual coefficient maps, persistence, and tensor base change in every character

All maps are induced by the original quotient/localization coefficient maps.
The character-one specialization is the rank-eight piece required by the
ambient test; the already checked character-zero modules remain unchanged.
The construction and seed identification of the geometric ambient-test
class are still separate tasks.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceCharacterPersistence

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree CycleQ2UniversalSurface
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2CharacterTopCech CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates
  CycleQ2UniversalSurfaceCharacterCech CycleQ2UniversalSurfaceCoefficientMap
open CycleQ2SeedCechTopCohomology (topExponent)
open CycleQ2UniversalSurfaceCechPersistence (localMap_smul)
open scoped TensorProduct

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (χ : ZMod 3)

def gradedLocalMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) :
    gradedLocal R χ hcoeff Fcoeff s →ₛₗ[f]
      gradedLocal S χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s where
  toFun p := ⟨localMap f hcoeff Fcoeff s p.val, by
    intro ab e he
    change (localizedCoordinates S _ _ s (localMap f hcoeff Fcoeff s p.val) ab).coeff e = 0
    rw [coordinates_localMap, laurentMap_coeff]
    exact (congrArg f (p.property ab e he)).trans (map_zero f)⟩
  map_add' p q := by apply Subtype.ext; exact map_add (localMap f hcoeff Fcoeff s) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact localMap_smul f hcoeff Fcoeff s c p.val

def actualCoordinates [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ActualTopCechQuotient R χ hcoeff Fcoeff ≃ₗ[R] ((TopIndex χ) →₀ R) :=
  (actualTopEquiv R χ hcoeff Fcoeff).trans (topCechEquiv R χ)

@[simp] theorem actualCoordinates_mk [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R χ hcoeff Fcoeff Finset.univ) :
    actualCoordinates χ hcoeff Fcoeff (Submodule.Quotient.mk p) =
      topProjection R χ (gradedCoordinates R χ hcoeff Fcoeff Finset.univ p) := by
  change topCechEquiv R χ (Submodule.Quotient.mk
    (gradedCoordinates R χ hcoeff Fcoeff Finset.univ p)) = _
  exact topCechEquiv_mk R χ _

theorem mem_actualBoundary_iff [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R χ hcoeff Fcoeff Finset.univ) :
    p ∈ actualBoundary R χ hcoeff Fcoeff ↔
      topProjection R χ (gradedCoordinates R χ hcoeff Fcoeff Finset.univ p) = 0 := by
  rw [← actualCoordinates_mk]
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

theorem gradedLocalMap_mem_boundary [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R χ hcoeff Fcoeff Finset.univ)
    (hp : p ∈ actualBoundary R χ hcoeff Fcoeff) :
    gradedLocalMap χ f hcoeff Fcoeff Finset.univ p ∈
      actualBoundary S χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) := by
  apply (mem_actualBoundary_iff χ _ _ _).mpr
  ext q
  change (localizedCoordinates S _ _ Finset.univ
      (localMap f hcoeff Fcoeff Finset.univ p.val) q.val.1).coeff
      (topExponent q.val.2) = 0
  rw [coordinates_localMap, laurentMap_coeff]
  have hz := congrArg (fun z : (TopIndex χ) →₀ R => z q)
    ((mem_actualBoundary_iff χ hcoeff Fcoeff p).mp hp)
  change (localizedCoordinates R hcoeff Fcoeff Finset.univ p.val q.val.1).coeff
    (topExponent q.val.2) = 0 at hz
  rw [hz, map_zero]

/-- The map on actual cohomology induced by coefficient specialization. -/
def actualTopMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ActualTopCechQuotient R χ hcoeff Fcoeff →ₛₗ[f]
      ActualTopCechQuotient S χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) :=
  (actualBoundary R χ hcoeff Fcoeff).mapQ
    (actualBoundary S χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)))
    (gradedLocalMap χ f hcoeff Fcoeff Finset.univ)
    (by intro p hp; exact gradedLocalMap_mem_boundary χ f hcoeff Fcoeff p hp)

@[simp] theorem actualTopMap_mk [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R χ hcoeff Fcoeff Finset.univ) :
    actualTopMap χ f hcoeff Fcoeff (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (gradedLocalMap χ f hcoeff Fcoeff Finset.univ p) := rfl

theorem coordinates_actualTopMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R χ hcoeff Fcoeff) (q : (TopIndex χ)) :
    actualCoordinates χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i))
        (actualTopMap χ f hcoeff Fcoeff z) q =
      f (actualCoordinates χ hcoeff Fcoeff z q) := by
  refine Submodule.Quotient.induction_on _ z ?_
  intro p
  rw [actualTopMap_mk, actualCoordinates_mk, actualCoordinates_mk]
  change (localizedCoordinates S _ _ Finset.univ
      (localMap f hcoeff Fcoeff Finset.univ p.val) q.val.1).coeff
      (topExponent q.val.2) = _
  rw [coordinates_localMap, laurentMap_coeff]
  rfl

/-- In particular, faithful coefficient extension is faithful on these actual
cohomology classes.  No generic flatness theorem is a hypothesis. -/
theorem actualTopMap_injective [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hf : Function.Injective f)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Function.Injective (actualTopMap χ f hcoeff Fcoeff) := by
  intro z w hzw
  apply (actualCoordinates χ hcoeff Fcoeff).injective
  ext q
  apply hf
  simpa only [coordinates_actualTopMap] using
    congrArg (fun u => actualCoordinates χ (fun i => f (hcoeff i))
      (fun i => f (Fcoeff i)) u q) hzw

/-- The pointed generic-component condition, applied to actual cohomology.
Only the scalar kernel containment is supplied; freeness and coefficient
compatibility of this concrete Cech quotient were proved above. -/
theorem nonzero_generic_of_nonzero_specialization
    [Nontrivial R] [Nontrivial S] [Nontrivial T]
    (generic : R →+* S) (specialization : R →+* T)
    (hpointed : ∀ c : R, generic c = 0 → specialization c = 0)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R χ hcoeff Fcoeff)
    (hz : actualTopMap χ specialization hcoeff Fcoeff z ≠ 0) :
    actualTopMap χ generic hcoeff Fcoeff z ≠ 0 := by
  intro hzero
  apply hz
  apply (actualCoordinates χ (fun i => specialization (hcoeff i))
    (fun i => specialization (Fcoeff i))).injective
  ext q
  rw [coordinates_actualTopMap, map_zero, Finsupp.zero_apply]
  apply hpointed
  have hq := congrArg (fun u => actualCoordinates χ (fun i => generic (hcoeff i))
    (fun i => generic (Fcoeff i)) u q) hzero
  simpa only [coordinates_actualTopMap, map_zero, Finsupp.zero_apply] using hq

/-- Every coordinate functional of the actual top cohomology is natural
under coefficient specialization, in the specified character. -/
def traceCoordinate [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (q : (TopIndex χ)) : ActualTopCechQuotient R χ hcoeff Fcoeff →ₗ[R] R :=
  (Finsupp.lapply q).comp (actualCoordinates χ hcoeff Fcoeff).toLinearMap

@[simp] theorem traceCoordinate_specialization [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R χ hcoeff Fcoeff) (q : (TopIndex χ)) :
    traceCoordinate χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) q
      (actualTopMap χ f hcoeff Fcoeff z) = f (traceCoordinate χ hcoeff Fcoeff q z) :=
  coordinates_actualTopMap χ f hcoeff Fcoeff z q


section TensorBaseChange
variable [Algebra R S] [Nontrivial R] [Nontrivial S]

def coordinateBasis (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Basis (TopIndex χ) R (ActualTopCechQuotient R χ hcoeff Fcoeff) :=
  Module.Basis.ofRepr (actualCoordinates χ hcoeff Fcoeff)

def actualBaseChange (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    (S ⊗[R] ActualTopCechQuotient R χ hcoeff Fcoeff) ≃ₗ[S]
      ActualTopCechQuotient S χ (fun i => algebraMap R S (hcoeff i))
        (fun i => algebraMap R S (Fcoeff i)) :=
  ((coordinateBasis χ hcoeff Fcoeff).baseChange S).repr.trans
    (actualCoordinates χ (fun i => algebraMap R S (hcoeff i))
      (fun i => algebraMap R S (Fcoeff i))).symm

@[simp] theorem actualBaseChange_tmul (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) (s : S)
    (z : ActualTopCechQuotient R χ hcoeff Fcoeff) :
    actualBaseChange χ hcoeff Fcoeff (s ⊗ₜ[R] z) =
      s • actualTopMap χ (algebraMap R S) hcoeff Fcoeff z := by
  apply (actualCoordinates χ (fun i => algebraMap R S (hcoeff i))
    (fun i => algebraMap R S (Fcoeff i))).injective
  ext q
  simp only [actualBaseChange, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.baseChange_repr_tmul, map_smul, Finsupp.smul_apply,
    coordinates_actualTopMap]
  change actualCoordinates χ hcoeff Fcoeff z q • s =
    s * algebraMap R S (actualCoordinates χ hcoeff Fcoeff z q)
  rw [Algebra.smul_def, mul_comm]

end TensorBaseChange

end CycleQ2UniversalSurfaceCharacterPersistence

#print axioms CycleQ2UniversalSurfaceCharacterPersistence.actualTopMap_injective
#print axioms CycleQ2UniversalSurfaceCharacterPersistence.nonzero_generic_of_nonzero_specialization
#print axioms CycleQ2UniversalSurfaceCharacterPersistence.actualBaseChange_tmul
end
end
