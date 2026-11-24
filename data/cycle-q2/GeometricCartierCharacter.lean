import Proposal.GeometricSurfaceCoordinates
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Proposal.GeometricCartierCoordinateDescent
import Proposal.GeometricCartierCechNonboundary
import Proposal.GeometricHomogeneousCartierDescent

section SourceCartierPolynomialWeight

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricCoordinateWeight

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalizedBasis

variable (R : Type*) [CommRing R]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- Standard means that the original x0 and w exponents are below three. -/
def Standard (p : Poly R) : Prop :=
  ∀ e, p.coeff e ≠ 0 → e 0 < 3 ∧ e 4 < 3

def mergeExponent (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![e 0,d 0,d 1,d 2,e 1]

def outerExponent (ab : ShiftIndex) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ab.1.val + Finsupp.single 1 ab.2.val

theorem regroup_coeff_coeff (p : Poly R) (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) :
    ((regroup R p).coeff e).coeff d = p.coeff (mergeExponent e d) := by
  change ((AddMonoidAlgebra.curryAlgEquiv R
    (AddMonoidAlgebra.domCongr R R Finsupp.sumFinsuppAddEquivProdFinsupp
      (renameEquiv R splitIndex p))).coeff e).coeff d = _
  change (AddMonoidAlgebra.domCongr R R Finsupp.sumFinsuppAddEquivProdFinsupp
      (renameEquiv R splitIndex p)).coeff (e,d) = _
  rw [AddMonoidAlgebra.coeff_domCongr]
  have heq : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e,d) =
      (mergeExponent e d).mapDomain splitIndex := by
    ext z
    obtain ⟨j,rfl⟩ := splitIndex.surjective z
    rw [Finsupp.mapDomain_apply splitIndex.injective]
    fin_cases j <;> rfl
  rw [heq]
  exact coeff_rename_mapDomain splitIndex splitIndex.injective p (mergeExponent e d)

private theorem regroup_standard {p : Poly R} (hp : Standard R p) :
    ∀ e, (regroup R p).coeff e ≠ 0 → e 0 < 3 ∧ e 1 < 3 := by
  intro e he
  obtain ⟨d,hd⟩ := exists_coeff_ne_zero he
  rw [regroup_coeff_coeff] at hd
  exact hp (mergeExponent e d) hd

private theorem standard_of_regroup {p : Poly R}
    (hp : ∀ e, (regroup R p).coeff e ≠ 0 → e 0 < 3 ∧ e 1 < 3) : Standard R p := by
  intro e he
  let u : Fin 2 →₀ ℕ := Finsupp.single 0 (e 0) + Finsupp.single 1 (e 4)
  let d : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e 1,e 2,e 3]
  have hmerge : mergeExponent u d = e := by
    ext i
    fin_cases i <;> simp [mergeExponent,u,d]
  have hu : (regroup R p).coeff u ≠ 0 := by
    intro hz
    have hd := regroup_coeff_coeff R p u d
    rw [hz, coeff_zero, hmerge] at hd
    exact he hd.symm
  have hh := hp u hu
  simpa [u] using hh

private theorem nested_reduced_of_standard [Nontrivial R] (r ι : R)
    {p : Poly R} (hp : Standard R p) :
    Reduced auxiliaryOrder (nestedH R ι) (nestedG R r) (regroup R p) := by
  intro e he
  rw [(nestedH_leading R ι).1, (nestedG_leading R r).1,
    single_three_le_iff, single_three_le_iff]
  have hh := regroup_standard R hp e (mem_support_iff.mp he)
  exact ⟨Nat.not_le_of_lt hh.1,Nat.not_le_of_lt hh.2⟩

/-- Uniqueness of standard representatives follows from the actual
rank-nine quotient equivalence, not a new division hypothesis. -/
theorem standard_quotient_injective [Nontrivial R] (r ι : R)
    {p q : Poly R} (hp : Standard R p) (hq : Standard R q)
    (he : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p =
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) q) : p = q := by
  let E := reducedQuotientEquiv auxiliaryOrder (nestedH R ι) (nestedG R r)
    (nestedH_leading R ι).2 (nestedG_leading R r).2 (nested_coprime R r ι)
  have hE : E ⟨regroup R p,nested_reduced_of_standard R r ι hp⟩ =
      E ⟨regroup R q,nested_reduced_of_standard R r ι hq⟩ :=
    congrArg (quotientRegroup R r ι) he
  exact (regroup R).injective (congrArg Subtype.val (E.injective hE))

/-- Every original polynomial class has an actual standard representative,
obtained through the already proved nested quotient equivalence. -/
theorem exists_standard_representative [Nontrivial R] (r ι : R) (p : Poly R) :
    ∃ N : Poly R, Standard R N ∧
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) N =
        Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p := by
  let E := reducedQuotientEquiv auxiliaryOrder (nestedH R ι) (nestedG R r)
    (nestedH_leading R ι).2 (nestedG_leading R r).2 (nested_coprime R r ι)
  obtain ⟨n,hn⟩ := E.surjective (quotientRegroup R r ι
    (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p))
  refine ⟨(regroup R).symm n.val,?_,?_⟩
  · apply standard_of_regroup R
    intro e he
    rw [AlgEquiv.apply_symm_apply] at he
    have hred := n.property (mem_support_iff.mpr he)
    change ¬ auxiliaryOrder.degree (nestedH R ι) ≤ e ∧
      ¬ auxiliaryOrder.degree (nestedG R r) ≤ e at hred
    rw [(nestedH_leading R ι).1, (nestedG_leading R r).1,
      single_three_le_iff, single_three_le_iff] at hred
    exact ⟨Nat.lt_of_not_ge hred.1,Nat.lt_of_not_ge hred.2⟩
  · apply (quotientRegroup R r ι).injective
    change Ideal.Quotient.mk (nestedIdeal R r ι) (regroup R ((regroup R).symm n.val)) = _
    rw [AlgEquiv.apply_symm_apply]
    exact hn

/-- Homogeneous projection preserves the standard exponent bounds. -/
theorem standard_component {M : Type*} [AddCommMonoid M] [DecidableEq M]
    (w : Fin 5 → M) (d : M) {p : Poly R} (hp : Standard R p) :
    Standard R (weightedHomogeneousComponent w d p) := by
  intro e he
  have hs : e ∈ p.support := by
    have hm := mem_support_iff.mpr he
    rw [support_weightedHomogeneousComponent] at hm
    exact (Finset.mem_filter.mp hm).1
  exact hp e (mem_support_iff.mp hs)

/-- The actual standard representative of a homogeneous class remains
homogeneous. The proof uses the given homogeneous defining ideal and the
proved injectivity of the original standard quotient presentation. -/
theorem standard_preserves_homogeneous [Nontrivial R]
    {M : Type*} [AddCommMonoid M] [DecidableEq M] (w : Fin 5 → M) (r ι : R)
    (hI : (equationsIdeal (smoothH ι) (smoothF r ι)).IsHomogeneous
      (weightedHomogeneousSubmodule R w))
    {p N : Poly R} {d : M} (hp : p.IsWeightedHomogeneous w d)
    (hN : Standard R N)
    (hq : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) N =
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) :
    N.IsWeightedHomogeneous w d := by
  letI := MvPolynomial.weightedGradedAlgebra R w
  have hmem : p - N ∈ equationsIdeal (smoothH ι) (smoothF r ι) :=
    Ideal.Quotient.eq.mp hq.symm
  have hcomp := weightedHomogeneousComponent_mem_of_mem R w hI hmem d
  rw [map_sub, weightedHomogeneousComponent_eq_self hp] at hcomp
  have hq' : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) N =
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
        (weightedHomogeneousComponent w d N) := hq.trans (Ideal.Quotient.eq.mpr hcomp)
  have hN' := standard_quotient_injective R r ι hN (standard_component R w d hN) hq'
  rw [hN']
  exact weightedHomogeneousComponent_isWeightedHomogeneous (w := w) d N

private theorem quotientBasis_repr_reduced {A σ : Type*} [CommRing A]
    (m : MonomialOrder σ) (h F p : MvPolynomial σ A)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hp : Reduced m h F p) (d : reducedExponents m h F) :
    (quotientBasis m h F hh hF hcop).repr (Ideal.Quotient.mk (equationsIdeal h F) p) d =
      p.coeff d.val := by
  let E := reducedQuotientEquiv m h F hh hF hcop
  have he : E ⟨p,hp⟩ = Ideal.Quotient.mk (equationsIdeal h F) p := rfl
  change (MvPolynomial.basisRestrictSupport A (reducedExponents m h F)).repr
    (E.symm (Ideal.Quotient.mk (equationsIdeal h F) p)) d = _
  rw [← he, LinearEquiv.symm_apply_apply]
  rfl

theorem seedBasis_repr_standard_coeff [Nontrivial R] (r ι : R) (p : Poly R)
    (hp : Standard R p) (ab : ShiftIndex) (d : Fin 3 →₀ ℕ) :
    ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab).coeff d =
        p.coeff (mergeExponent (outerExponent ab) d) := by
  have hrepr : (seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab =
        (regroup R p).coeff (outerExponent ab) := by
    change (nestedBasis R r ι).repr
      (Ideal.Quotient.mk (nestedIdeal R r ι) (regroup R p)) ab = _
    unfold nestedBasis
    erw [Module.Basis.repr_reindex_apply,
      quotientBasis_repr_reduced auxiliaryOrder (nestedH R ι) (nestedG R r) (regroup R p)
        (nestedH_leading R ι).2 (nestedG_leading R r).2 (nested_coprime R r ι)
        (nested_reduced_of_standard R r ι hp)]
    rfl
  rw [hrepr,regroup_coeff_coeff]

/-- The original ambient weights; no character assertion is built in. -/
def weight : Fin 5 → ℕ := ![1,1,1,1,2]

theorem merged_weight (ab : ShiftIndex) (d : Fin 3 →₀ ℕ) :
    Finsupp.weight weight (mergeExponent (outerExponent ab) d) =
      ab.1.val + 2 * ab.2.val + ∑ i, d i := by
  rw [Finsupp.weight_eq_sum]
  simp [weight,mergeExponent,outerExponent,Fin.sum_univ_succ,Finsupp.sum_fintype]
  ring

/-- A nonzero coefficient in the fixed rank-nine coordinates has precisely
the original weighted degree, including its x0,w basis shift. -/
theorem seedCoordinates_weight [Nontrivial R] (r ι : R)
    (hI : (equationsIdeal (smoothH ι) (smoothF r ι)).IsHomogeneous
      (weightedHomogeneousSubmodule R weight))
    (p : Poly R) (n : ℕ) (hp : p.IsWeightedHomogeneous weight n)
    (ab : ShiftIndex) (d : Fin 3 →₀ ℕ)
    (hne : ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab).coeff d ≠ 0) :
    ab.1.val + 2 * ab.2.val + ∑ i, d i = n := by
  obtain ⟨N,hN,hq⟩ := exists_standard_representative R r ι p
  have hNg := standard_preserves_homogeneous R weight r ι hI hp hN hq
  rw [← hq,seedBasis_repr_standard_coeff R r ι N hN ab d] at hne
  have hd := hNg hne
  rw [merged_weight] at hd
  exact hd

end CycleQ2GeometricCoordinateWeight

#print axioms CycleQ2GeometricCoordinateWeight.exists_standard_representative
#print axioms CycleQ2GeometricCoordinateWeight.standard_preserves_homogeneous
#print axioms CycleQ2GeometricCoordinateWeight.seedCoordinates_weight

end
end SourceCartierPolynomialWeight

section SourceCartierLocalWeight

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricCoordinateWeight

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2GeometricLaurentTop

variable (R : Type*) [CommRing R]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

private theorem x0 : (X (0 : Fin 5) : Poly R).IsWeightedHomogeneous weight 1 := by
  simpa [weight] using isWeightedHomogeneous_X R weight (0 : Fin 5)
private theorem x1 : (X (1 : Fin 5) : Poly R).IsWeightedHomogeneous weight 1 := by
  simpa [weight] using isWeightedHomogeneous_X R weight (1 : Fin 5)
private theorem x2 : (X (2 : Fin 5) : Poly R).IsWeightedHomogeneous weight 1 := by
  simpa [weight] using isWeightedHomogeneous_X R weight (2 : Fin 5)
private theorem x3 : (X (3 : Fin 5) : Poly R).IsWeightedHomogeneous weight 1 := by
  simpa [weight] using isWeightedHomogeneous_X R weight (3 : Fin 5)
private theorem x4 : (X (4 : Fin 5) : Poly R).IsWeightedHomogeneous weight 2 := by
  simpa [weight] using isWeightedHomogeneous_X R weight (4 : Fin 5)

theorem smoothB_homogeneous : (smoothB : Poly R).IsWeightedHomogeneous weight 3 :=
  ((((((x3 R).pow 3).add ((x2 R).pow 3)).add (((x1 R).mul (x2 R)).mul (x3 R))).add
    (((x0 R).mul (x2 R)).mul (x3 R))).add ((x0 R).mul ((x1 R).pow 2))).add ((x0 R).pow 3)

theorem smoothH_homogeneous (ι : R) : (smoothH ι).IsWeightedHomogeneous weight 3 :=
  (smoothB_homogeneous R).sub ((((x1 R).pow 3).add ((x3 R).pow 3)).C_mul ι)

theorem smoothK_homogeneous (ι : R) : (smoothK ι).IsWeightedHomogeneous weight 3 :=
  (smoothB_homogeneous R).add ((((x1 R).pow 3).add ((x3 R).pow 3)).C_mul ι)

theorem seedG_homogeneous (r : R) : (seedG r).IsWeightedHomogeneous weight 6 := by
  rw [seedG,CycleQ2SegreSeed.seedG_expanded]
  have h13 : ((C r)^3 * X (1 : Fin 5)^3 * X 3^3 : Poly R).IsWeightedHomogeneous
      weight 6 :=
    (((isWeightedHomogeneous_C weight r).pow 3).mul ((x1 R).pow 3)).mul
      ((x3 R).pow 3)
  exact ((((x0 R).pow 6).sub h13).add ((x2 R).pow 6)).add ((x4 R).pow 3)

theorem smoothF_homogeneous (r ι : R) :
    (smoothF r ι).IsWeightedHomogeneous weight 6 :=
  (seedG_homogeneous R r).add ((smoothH_homogeneous R ι).mul (smoothK_homogeneous R ι))

/-- Homogeneity of the original two defining equations is proved directly. -/
theorem seedIdeal_homogeneous (r ι : R) :
    (equationsIdeal (smoothH ι) (smoothF r ι)).IsHomogeneous
      (weightedHomogeneousSubmodule R weight) := by
  apply Ideal.homogeneous_span
  rintro p (rfl | hp)
  · exact ⟨3,smoothH_homogeneous R ι⟩
  · obtain rfl := hp
    exact ⟨6,smoothF_homogeneous R r ι⟩

/-- Actual weighted homogeneity constrains every nonzero Laurent coefficient
of the polynomial class in the fixed original nine coordinates. -/
theorem globalLaurent_weight [Nontrivial R] (r ι : R)
    (p : Poly R) (n : ℕ) (hp : p.IsWeightedHomogeneous weight n)
    (ab : ShiftIndex) (e : LaurentExponent)
    (hne : (baseToLaurent R ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)).coeff e ≠ 0) :
    (shiftedGrade ab e).1 = (n : ℤ) := by
  have hpos : ∀ i, 0 ≤ e i := by
    intro i
    by_contra hi
    exact hne (baseToLaurent_hasPoles R _ e i (by simp) (lt_of_not_ge hi))
  obtain ⟨d,rfl⟩ := (mem_range_castExponent e).mpr hpos
  have hcoeff (u : Base R) (d : Fin 3 →₀ ℕ) :
      (baseToLaurent R u).coeff (castExponent d) = u.coeff d :=
    Finsupp.mapDomain_apply castExponent_injective _ _
  have hc : ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab).coeff d ≠ 0 := by
    simpa only [hcoeff] using hne
  have hw := seedCoordinates_weight R r ι (seedIdeal_homogeneous R r ι) p n hp ab d hc
  change (ab.1.val : ℤ) + 2 * ab.2.val + ∑ i, (d i : ℤ) = n
  exact_mod_cast hw

end CycleQ2GeometricCoordinateWeight

namespace CycleQ2GeometricLaurentTop

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCoordinateWeight

/-- The same actual polynomial weight is retained after division by the
coordinate-product denominator. This permits arbitrary pole orders. -/
theorem seed_fraction_weight (r : ℂ) (q : SeedLocal ℂ r Complex.I Finset.univ)
    (p : Poly ℂ) (n D : ℕ) (hp : p.IsWeightedHomogeneous weight (3*n+D))
    (hfrac : q * algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I Finset.univ)
      (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ Finset.univ ^ n)) =
      algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I Finset.univ)
        (Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF r Complex.I)) p))
    (ab : ShiftIndex) (e : LaurentExponent)
    (hne : (localizedCoordinates ℂ r Complex.I Finset.univ q ab).coeff e ≠ 0) :
    (shiftedGrade ab e).1 = (D : ℤ) := by
  have hh := congrArg (fun z => localizedCoordinates ℂ r Complex.I Finset.univ z ab) hfrac
  rw [seed_coordinates_mul_base,localizedCoordinates_algebraMap] at hh
  simp only [map_pow,baseToLaurent_baseProduct,T_pow] at hh
  have hh' := congrArg (fun z : Laurent (R := ℂ) =>
    z.coeff (e + n • openExponent Finset.univ)) hh
  have hn : (baseToLaurent ℂ ((seedBasis ℂ r Complex.I).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF r Complex.I)) p) ab)).coeff
      (e + n • openExponent Finset.univ) ≠ 0 := by
    rw [← hh']
    rw [mul_comm (T ℂ (n • openExponent Finset.univ)),coeff_mul_T,
      add_sub_cancel_right]
    exact hne
  have hw := globalLaurent_weight ℂ r Complex.I p (3*n+D) hp ab
    (e + n • openExponent Finset.univ) hn
  have hshift : n • openExponent (Finset.univ : Finset (Fin 3)) =
      fun _ => (n : ℤ) := by
    funext i
    change n • (if i ∈ (Finset.univ : Finset (Fin 3)) then (1 : ℤ) else 0) = _
    simp
  rw [hshift] at hw
  simp only [shiftedGrade,Fin.sum_univ_three,Pi.add_apply,
    Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hw ⊢
  omega

/-- The fraction criterion applied to the actual surface coordinate ring;
the comparison to the seed coordinates preserves every original polynomial. -/
theorem coordinate_fraction_weight (r : ℂ)
    (q : CoordinateLocal r 1 Finset.univ) (p : Poly ℂ) (n D : ℕ)
    (hp : p.IsWeightedHomogeneous weight (3*n+D))
    (hfrac : q * algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)
      (coordinateProduct r 1 Finset.univ ^ n) =
      algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ) (quotientMap r 1 p))
    (ab : ShiftIndex) (e : LaurentExponent)
    (hne : (coordinateLaurent r Finset.univ q ab).coeff e ≠ 0) :
    (shiftedGrade ab e).1 = (D : ℤ) := by
  apply seed_fraction_weight r (seedCoordinateEquiv r Finset.univ q) p n D hp ?_ ab e hne
  have hh := congrArg (seedCoordinateEquiv r Finset.univ) hfrac
  simp only [map_mul,seedCoordinateEquiv_base,map_pow,seedRingEquiv_coordinateProduct,
    seedRingEquiv_quotient] at hh
  simpa only [map_pow] using hh

end CycleQ2GeometricLaurentTop

#print axioms CycleQ2GeometricCoordinateWeight.seedIdeal_homogeneous
#print axioms CycleQ2GeometricCoordinateWeight.globalLaurent_weight
#print axioms CycleQ2GeometricLaurentTop.coordinate_fraction_weight

end
end SourceCartierLocalWeight

section SourceCartierCharacterWeight

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricCoordinateCharacter

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2GeometricCoordinateWeight CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricLaurentTop CycleQ2GeometricSeedNormalIdeals

variable (R : Type*) [CommRing R]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- The action on the original five variables, with values in its character group. -/
def characterWeight : Fin 5 → ZMod 3 := ![2,2,1,0,0]

private theorem x0 : (X (0 : Fin 5) : Poly R).IsWeightedHomogeneous characterWeight 2 := by
  simpa [characterWeight] using isWeightedHomogeneous_X R characterWeight (0 : Fin 5)
private theorem x1 : (X (1 : Fin 5) : Poly R).IsWeightedHomogeneous characterWeight 2 := by
  simpa [characterWeight] using isWeightedHomogeneous_X R characterWeight (1 : Fin 5)
private theorem x2 : (X (2 : Fin 5) : Poly R).IsWeightedHomogeneous characterWeight 1 := by
  simpa [characterWeight] using isWeightedHomogeneous_X R characterWeight (2 : Fin 5)
private theorem x3 : (X (3 : Fin 5) : Poly R).IsWeightedHomogeneous characterWeight 0 := by
  simpa [characterWeight] using isWeightedHomogeneous_X R characterWeight (3 : Fin 5)
private theorem x4 : (X (4 : Fin 5) : Poly R).IsWeightedHomogeneous characterWeight 0 := by
  simpa [characterWeight] using isWeightedHomogeneous_X R characterWeight (4 : Fin 5)

private theorem regrade {p : Poly R} {a b : ZMod 3}
    (hp : p.IsWeightedHomogeneous characterWeight a) (h : a = b) :
    p.IsWeightedHomogeneous characterWeight b := h ▸ hp

theorem smoothB_character : (smoothB : Poly R).IsWeightedHomogeneous characterWeight 0 := by
  have h3 : (X (3 : Fin 5) ^ 3 : Poly R).IsWeightedHomogeneous characterWeight 0 := by
    exact regrade R ((x3 R).pow 3) (by decide)
  have h2 : (X (2 : Fin 5) ^ 3 : Poly R).IsWeightedHomogeneous characterWeight 0 := by
    exact regrade R ((x2 R).pow 3) (by decide)
  have h123 : (X (1 : Fin 5) * X 2 * X 3 : Poly R).IsWeightedHomogeneous characterWeight 0 := by
    exact regrade R (((x1 R).mul (x2 R)).mul (x3 R)) (by decide)
  have h023 : (X (0 : Fin 5) * X 2 * X 3 : Poly R).IsWeightedHomogeneous characterWeight 0 := by
    exact regrade R (((x0 R).mul (x2 R)).mul (x3 R)) (by decide)
  have h011 : (X (0 : Fin 5) * X 1 ^ 2 : Poly R).IsWeightedHomogeneous characterWeight 0 := by
    exact regrade R ((x0 R).mul ((x1 R).pow 2)) (by decide)
  have h000 : (X (0 : Fin 5) ^ 3 : Poly R).IsWeightedHomogeneous characterWeight 0 := by
    exact regrade R ((x0 R).pow 3) (by decide)
  exact ((((h3.add h2).add h123).add h023).add h011).add h000

theorem smoothA_character : (smoothA : Poly R).IsWeightedHomogeneous characterWeight 0 :=
  (regrade R ((x1 R).pow 3) (by decide)).add
    (regrade R ((x3 R).pow 3) (by decide))

theorem smoothH_character (ι : R) :
    (smoothH ι).IsWeightedHomogeneous characterWeight 0 := by
  exact (smoothB_character R).sub ((smoothA_character R).C_mul ι)

theorem smoothK_character (ι : R) :
    (smoothK ι).IsWeightedHomogeneous characterWeight 0 := by
  exact (smoothB_character R).add ((smoothA_character R).C_mul ι)

theorem seedG_character (r : R) :
    (seedG r).IsWeightedHomogeneous characterWeight 0 := by
  have h0 : (X (0 : Fin 5) ^ 6 : Poly R).IsWeightedHomogeneous characterWeight 0 := by
    exact regrade R ((x0 R).pow 6) (by decide)
  have h13 : ((C r)^3 * X (1 : Fin 5)^3 * X 3^3 : Poly R).IsWeightedHomogeneous
      characterWeight 0 := by
    exact regrade R ((((isWeightedHomogeneous_C characterWeight r).pow 3).mul
      ((x1 R).pow 3)).mul ((x3 R).pow 3)) (by decide)
  have h2 : (X (2 : Fin 5) ^ 6 : Poly R).IsWeightedHomogeneous characterWeight 0 := by
    exact regrade R ((x2 R).pow 6) (by decide)
  have h4 : (X (4 : Fin 5) ^ 3 : Poly R).IsWeightedHomogeneous characterWeight 0 := by
    exact regrade R ((x4 R).pow 3) (by decide)
  rw [seedG,CycleQ2SegreSeed.seedG_expanded]
  exact ((h0.sub h13).add h2).add h4

theorem smoothF_character (r ι : R) :
    (smoothF r ι).IsWeightedHomogeneous characterWeight 0 := by
  simpa only [smoothF,add_zero] using
    (seedG_character R r).add ((smoothH_character R ι).mul (smoothK_character R ι))

/-- Both original surface relations are character zero, including every mixed term. -/
theorem seedIdeal_character (r ι : R) :
    (equationsIdeal (smoothH ι) (smoothF r ι)).IsHomogeneous
      (weightedHomogeneousSubmodule R characterWeight) := by
  apply Ideal.homogeneous_span
  rintro p (rfl | hp)
  · exact ⟨0,smoothH_character R ι⟩
  · obtain rfl := hp
    exact ⟨0,smoothF_character R r ι⟩

theorem merged_character (ab : ShiftIndex) (d : Fin 3 →₀ ℕ) :
    Finsupp.weight characterWeight (mergeExponent (outerExponent ab) d) =
      (2 * ab.1.val : ℕ) + (2 * (d 0 : ℤ) + d 1 : ℤ) := by
  rw [Finsupp.weight_eq_sum]
  simp [characterWeight,mergeExponent,outerExponent,Fin.sum_univ_succ,Finsupp.sum_fintype]
  ring

/-- Character is preserved by the unique standard representative in the original rank-nine basis. -/
theorem seedCoordinates_character [Nontrivial R] (r ι : R)
    (p : Poly R) (χ : ZMod 3) (hp : p.IsWeightedHomogeneous characterWeight χ)
    (ab : ShiftIndex) (d : Fin 3 →₀ ℕ)
    (hne : ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab).coeff d ≠ 0) :
    (2 * ab.1.val : ℕ) + (2 * (d 0 : ℤ) + d 1 : ℤ) = χ := by
  obtain ⟨N,hN,hq⟩ := exists_standard_representative R r ι p
  have hNg := standard_preserves_homogeneous R characterWeight r ι
    (seedIdeal_character R r ι) hp hN hq
  rw [← hq,seedBasis_repr_standard_coeff R r ι N hN ab d] at hne
  have hd := hNg hne
  rw [merged_character] at hd
  exact hd

theorem globalLaurent_character [Nontrivial R] (r ι : R)
    (p : Poly R) (χ : ZMod 3) (hp : p.IsWeightedHomogeneous characterWeight χ)
    (ab : ShiftIndex) (e : LaurentExponent)
    (hne : (baseToLaurent R ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)).coeff e ≠ 0) :
    (shiftedGrade ab e).2 = χ := by
  have hpos : ∀ i, 0 ≤ e i := by
    intro i
    by_contra hi
    exact hne (baseToLaurent_hasPoles R _ e i (by simp) (lt_of_not_ge hi))
  obtain ⟨d,rfl⟩ := (mem_range_castExponent e).mpr hpos
  have hcoeff (u : Base R) (d : Fin 3 →₀ ℕ) :
      (baseToLaurent R u).coeff (castExponent d) = u.coeff d :=
    Finsupp.mapDomain_apply castExponent_injective _ _
  have hc : ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab).coeff d ≠ 0 := by
    simpa only [hcoeff] using hne
  exact seedCoordinates_character R r ι p χ hp ab d hc

end CycleQ2GeometricCoordinateCharacter

namespace CycleQ2GeometricLaurentTop

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCoordinateCharacter

theorem shifted_character_univ (ab : ShiftIndex) (e : LaurentExponent) (n : ℕ) :
    (shiftedGrade ab (e + n • openExponent Finset.univ)).2 =
      (shiftedGrade ab e).2 := by
  have hshift : n • openExponent (Finset.univ : Finset (Fin 3)) =
      fun _ => (n : ℤ) := by
    funext i
    change n • (if i ∈ (Finset.univ : Finset (Fin 3)) then (1 : ℤ) else 0) = _
    simp
  rw [hshift]
  simp only [shiftedGrade,Pi.add_apply,Int.cast_add,Int.cast_mul,
    Int.cast_ofNat,Int.cast_natCast]
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination (n : ZMod 3) * h3

theorem seed_fraction_character (r : ℂ) (q : SeedLocal ℂ r Complex.I Finset.univ)
    (p : Poly ℂ) (n : ℕ) (χ : ZMod 3)
    (hp : p.IsWeightedHomogeneous characterWeight χ)
    (hfrac : q * algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I Finset.univ)
      (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ Finset.univ ^ n)) =
      algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I Finset.univ)
        (Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF r Complex.I)) p))
    (ab : ShiftIndex) (e : LaurentExponent)
    (hne : (localizedCoordinates ℂ r Complex.I Finset.univ q ab).coeff e ≠ 0) :
    (shiftedGrade ab e).2 = χ := by
  have hh := congrArg (fun z => localizedCoordinates ℂ r Complex.I Finset.univ z ab) hfrac
  rw [seed_coordinates_mul_base,localizedCoordinates_algebraMap] at hh
  simp only [map_pow,baseToLaurent_baseProduct,T_pow] at hh
  have hh' := congrArg (fun z : Laurent (R := ℂ) =>
    z.coeff (e + n • openExponent Finset.univ)) hh
  have hn : (baseToLaurent ℂ ((seedBasis ℂ r Complex.I).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF r Complex.I)) p) ab)).coeff
      (e + n • openExponent Finset.univ) ≠ 0 := by
    rw [← hh']
    rw [mul_comm (T ℂ (n • openExponent Finset.univ)),coeff_mul_T,
      add_sub_cancel_right]
    exact hne
  have hw := globalLaurent_character ℂ r Complex.I p χ hp ab
    (e + n • openExponent Finset.univ) hn
  rwa [shifted_character_univ] at hw

theorem coordinate_fraction_character (r : ℂ)
    (q : CoordinateLocal r 1 Finset.univ) (p : Poly ℂ) (n : ℕ) (χ : ZMod 3)
    (hp : p.IsWeightedHomogeneous characterWeight χ)
    (hfrac : q * algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)
      (coordinateProduct r 1 Finset.univ ^ n) =
      algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ) (quotientMap r 1 p))
    (ab : ShiftIndex) (e : LaurentExponent)
    (hne : (coordinateLaurent r Finset.univ q ab).coeff e ≠ 0) :
    (shiftedGrade ab e).2 = χ := by
  apply seed_fraction_character r (seedCoordinateEquiv r Finset.univ q) p n χ hp ?_ ab e hne
  have hh := congrArg (seedCoordinateEquiv r Finset.univ) hfrac
  simp only [map_mul,seedCoordinateEquiv_base,map_pow,seedRingEquiv_coordinateProduct,
    seedRingEquiv_quotient] at hh
  simpa only [map_pow] using hh

end CycleQ2GeometricLaurentTop

#print axioms CycleQ2GeometricCoordinateCharacter.seedIdeal_character
#print axioms CycleQ2GeometricCoordinateCharacter.seedCoordinates_character
#print axioms CycleQ2GeometricLaurentTop.coordinate_fraction_character

end
end SourceCartierCharacterWeight

section SourceCartierCharacterProjection

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricCoordinateCharacter

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedCechThreeOpen CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricLaurentTop CycleQ2GeometricSeedNormalIdeals

variable {R : Type*} [CommRing R]

/-- Character projection in the fixed Laurent coordinates of the original surface. -/
def characterPart (χ : ZMod 3) (ab : ShiftIndex) (p : Laurent (R := R)) :
    Laurent (R := R) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.filter (fun e => (shiftedGrade ab e).2 = χ))

@[simp] theorem characterPart_coeff (χ : ZMod 3) (ab : ShiftIndex)
    (p : Laurent (R := R)) (e : LaurentExponent) :
    (characterPart χ ab p).coeff e =
      if (shiftedGrade ab e).2 = χ then p.coeff e else 0 := rfl

@[simp] theorem characterPart_zero (χ : ZMod 3) (ab : ShiftIndex) :
    characterPart χ ab (0 : Laurent (R := R)) = 0 := by
  ext e
  simp

@[simp] theorem characterPart_add (χ : ZMod 3) (ab : ShiftIndex)
    (p q : Laurent (R := R)) : characterPart χ ab (p+q) =
      characterPart χ ab p + characterPart χ ab q := by
  ext e
  by_cases h : (shiftedGrade ab e).2 = χ <;>
    simp [h,AddMonoidAlgebra.coeff_add,Finsupp.add_apply]

theorem characterPart_hasPoles (χ : ZMod 3) (ab : ShiftIndex)
    {s : Finset (Fin 3)} {p : Laurent (R := R)} (hp : HasPoles s p) :
    HasPoles s (characterPart χ ab p) := by
  intro e i hi he
  simp only [characterPart_coeff]
  split
  · exact hp e i hi he
  · rfl

theorem characterPart_sum (ab : ShiftIndex) (p : ZMod 3 → Laurent (R := R))
    (hp : ∀ χ e, (shiftedGrade ab e).2 ≠ χ → (p χ).coeff e = 0) (χ : ZMod 3) :
    characterPart χ ab (∑ τ, p τ) = p χ := by
  ext e
  by_cases he : (shiftedGrade ab e).2 = χ
  · simp only [characterPart_coeff,if_pos he,AddMonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
    apply Finset.sum_eq_single χ
    · intro τ _ hτ
      exact hp τ e (by simpa only [he] using Ne.symm hτ)
    · simp
  · simp only [characterPart_coeff,if_neg he]
    exact (hp χ e he).symm

theorem characterPart_grade (χ : ZMod 3) (ab : ShiftIndex)
    (p : Laurent (R := R))
    (hp : ∀ e, p.coeff e ≠ 0 → (shiftedGrade ab e).1 = 0) :
    HasGrade ab (0,χ) (characterPart χ ab p) := by
  intro e he
  by_cases hc : (shiftedGrade ab e).2 = χ
  · rw [characterPart_coeff,if_pos hc]
    by_contra hn
    exact he (Prod.ext (hp e hn) hc)
  · exact if_neg hc

private theorem exists_coordinateProject (r : ℂ) (s : Finset (Fin 3))
    (χ : ZMod 3) (q : CoordinateLocal r 1 s) :
    ∃ z : CoordinateLocal r 1 s, coordinateLaurent r s z =
      fun ab => characterPart χ ab (coordinateLaurent r s q ab) := by
  apply (coordinateLaurent_range r s _).mpr
  intro ab
  exact characterPart_hasPoles χ ab (coordinateLaurent_hasPoles r s q ab)

/-- The projection is an actual element of the same coordinate localization. -/
def coordinateProject (r : ℂ) (s : Finset (Fin 3)) (χ : ZMod 3)
    (q : CoordinateLocal r 1 s) : CoordinateLocal r 1 s :=
  (exists_coordinateProject r s χ q).choose

@[simp] theorem coordinateProject_coordinates (r : ℂ) (s : Finset (Fin 3))
    (χ : ZMod 3) (q : CoordinateLocal r 1 s) :
    coordinateLaurent r s (coordinateProject r s χ q) =
      fun ab => characterPart χ ab (coordinateLaurent r s q ab) :=
  (exists_coordinateProject r s χ q).choose_spec

@[simp] theorem coordinateProject_zero (r : ℂ) (s : Finset (Fin 3)) (χ : ZMod 3) :
    coordinateProject r s χ 0 = 0 := by
  apply coordinateLaurent_injective r s
  ext ab e
  simp

@[simp] theorem coordinateProject_add (r : ℂ) (s : Finset (Fin 3)) (χ : ZMod 3)
    (q z : CoordinateLocal r 1 s) :
    coordinateProject r s χ (q+z) = coordinateProject r s χ q + coordinateProject r s χ z := by
  apply coordinateLaurent_injective r s
  simp only [coordinateProject_coordinates,map_add,Pi.add_apply,characterPart_add]
  rfl

def coordinateProjectHom (r : ℂ) (s : Finset (Fin 3)) (χ : ZMod 3) :
    CoordinateLocal r 1 s →+ CoordinateLocal r 1 s where
  toFun := coordinateProject r s χ
  map_zero' := coordinateProject_zero r s χ
  map_add' := coordinateProject_add r s χ

/-- The projection respects the actual coordinate-cover restriction maps. -/
theorem coordinateProject_restriction (r : ℂ) (χ : ZMod 3)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (q : CoordinateLocal r 1 s) :
    coordinateProject r t χ (coordinateRestriction r 1 hst q) =
      coordinateRestriction r 1 hst (coordinateProject r s χ q) := by
  apply coordinateLaurent_injective r t
  simp only [coordinateProject_coordinates,coordinateLaurent_restriction]

/-- A fraction in the actual triple chart, retaining its original polynomial numerator. -/
def polynomialFraction (r : ℂ) (n : ℕ) (p : Poly ℂ) :
    CoordinateLocal r 1 Finset.univ :=
  IsLocalization.mk' _ (quotientMap r 1 p)
    (⟨coordinateProduct r 1 Finset.univ ^ n,⟨n,rfl⟩⟩ :
      Submonoid.powers (coordinateProduct r 1 Finset.univ))

theorem polynomialFraction_spec (r : ℂ) (n : ℕ) (p : Poly ℂ) :
    polynomialFraction r n p *
      algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)
        (coordinateProduct r 1 Finset.univ ^ n) =
      algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ) (quotientMap r 1 p) :=
  IsLocalization.mk'_spec _ _ _

theorem exists_polynomialFraction (r : ℂ) (q : CoordinateLocal r 1 Finset.univ) :
    ∃ n p, q = polynomialFraction r n p := by
  obtain ⟨n,a,ha⟩ := IsLocalization.Away.surj (coordinateProduct r 1 Finset.univ) q
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨n,p,IsLocalization.eq_mk'_iff_mul_eq.mpr ?_⟩
  simpa only [map_pow,quotientMap] using ha

theorem polynomial_character_sum (p : Poly ℂ) :
    ∑ χ : ZMod 3, weightedHomogeneousComponent characterWeight χ p = p := by
  ext1 e
  simp only [coeff_sum,coeff_weightedHomogeneousComponent]
  simp

theorem polynomialFraction_character_sum (r : ℂ) (n : ℕ) (p : Poly ℂ) :
    ∑ χ : ZMod 3, polynomialFraction r n
      (weightedHomogeneousComponent characterWeight χ p) = polynomialFraction r n p := by
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  simp only [Finset.sum_mul,polynomialFraction_spec,← map_sum,polynomial_character_sum]

/-- The actual localization projection agrees with projecting a cleared numerator;
the product of all three coordinate denominators has character zero. -/
theorem coordinateProject_polynomialFraction (r : ℂ) (n : ℕ) (p : Poly ℂ) (χ : ZMod 3) :
    coordinateProject r Finset.univ χ (polynomialFraction r n p) =
      polynomialFraction r n (weightedHomogeneousComponent characterWeight χ p) := by
  apply coordinateLaurent_injective r Finset.univ
  rw [coordinateProject_coordinates]
  conv_lhs => rw [← polynomialFraction_character_sum r n p]
  simp only [map_sum,Finset.sum_apply]
  funext ab
  apply characterPart_sum
  intro τ e he
  by_contra hn
  exact he (coordinate_fraction_character r _ _ n τ
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := characterWeight) τ p)
    (polynomialFraction_spec r n _) ab e hn)

theorem polynomialFraction_mul (r : ℂ) (n : ℕ) (σ p : Poly ℂ) :
    algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ) (quotientMap r 1 σ) *
      polynomialFraction r n p = polynomialFraction r n (σ*p) := by
  apply IsLocalization.eq_mk'_iff_mul_eq.mpr
  rw [mul_assoc,polynomialFraction_spec]
  simp only [map_mul]

theorem characterComponent_mul_invariant (σ p : Poly ℂ) (χ : ZMod 3)
    (hσ : σ.IsWeightedHomogeneous characterWeight 0) :
    weightedHomogeneousComponent characterWeight χ (σ*p) =
      σ * weightedHomogeneousComponent characterWeight χ p := by
  letI := MvPolynomial.weightedGradedAlgebra ℂ characterWeight
  have he (u : Poly ℂ) (τ : ZMod 3) :
      (DirectSum.decompose (weightedHomogeneousSubmodule ℂ characterWeight) u τ : Poly ℂ) =
        weightedHomogeneousComponent characterWeight τ u :=
    MvPolynomial.decompose'_apply ℂ characterWeight u τ
  have hm := DirectSum.coe_decompose_mul_of_left_mem_zero
    (weightedHomogeneousSubmodule ℂ characterWeight) (b := p) (j := χ) hσ
  simpa only [he] using hm

/-- The genuine coordinate projection commutes with every invariant polynomial,
in particular with the cubic used in the original normal-pairing test. -/
theorem coordinateProject_mul_invariant (r : ℂ) (q : CoordinateLocal r 1 Finset.univ)
    (σ : Poly ℂ) (χ : ZMod 3) (hσ : σ.IsWeightedHomogeneous characterWeight 0) :
    coordinateProject r Finset.univ χ
      (algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ) (quotientMap r 1 σ) * q) =
      algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ) (quotientMap r 1 σ) *
        coordinateProject r Finset.univ χ q := by
  obtain ⟨n,p,rfl⟩ := exists_polynomialFraction r q
  rw [polynomialFraction_mul,coordinateProject_polynomialFraction,
    coordinateProject_polynomialFraction,polynomialFraction_mul,
    characterComponent_mul_invariant σ p χ hσ]

end CycleQ2GeometricCoordinateCharacter

#print axioms CycleQ2GeometricCoordinateCharacter.coordinateProject_restriction
#print axioms CycleQ2GeometricCoordinateCharacter.coordinateProject_polynomialFraction
#print axioms CycleQ2GeometricCoordinateCharacter.coordinateProject_mul_invariant

end
end SourceCartierCharacterProjection

section SourceCartierHomogeneousWeight

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricHomogeneousWeight

open MvPolynomial CycleQ2SeedTrace CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricCartierCech
  CycleQ2GeometricFourOpenCech CycleQ2GeometricLaurentTop
  CycleQ2GeometricCoordinateWeight CycleQ2CartierSurfaceGrading
  CycleQ2SeedCechThreeOpen CycleQ2NormalConnecting

/-- The genuine projective coordinate triple uses the existing surface
quotient grading and the original three-coordinate product. -/
abbrev HomogeneousCoordinateTop (r : ℂ) :=
  HomogeneousLocalization.Away (surfaceGrade r 1) (coordinateProduct r 1 Finset.univ)

theorem coordinateProduct_univ_mem_grade (r : ℂ) :
    coordinateProduct r 1 Finset.univ ∈ surfaceGrade r 1 3 := by
  have hx1 : (X (1 : Fin 5) : WeightedPoly).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 := by
    simpa [CycleQ2CartierSurfaceGrading.weight] using
      isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight (1 : Fin 5)
  have hx2 : (X (2 : Fin 5) : WeightedPoly).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 := by
    simpa [CycleQ2CartierSurfaceGrading.weight] using
      isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight (2 : Fin 5)
  have hx3 : (X (3 : Fin 5) : WeightedPoly).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 := by
    simpa [CycleQ2CartierSurfaceGrading.weight] using
      isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight (3 : Fin 5)
  have hprod : coordinateProduct r 1 Finset.univ =
      surfaceQuotient r 1 (X 1 * X 2 * X 3) := by
    simp only [coordinateProduct,Fin.prod_univ_three]
    change quotientMap r 1 (X 1) * quotientMap r 1 (X 2) * quotientMap r 1 (X 3) = _
    rw [map_mul,map_mul]
    rfl
  rw [hprod]
  exact surfaceQuotient_mem_grade r 1 ((hx1.mul hx2).mul hx3)

/-- A genuine homogeneous-localization section has an actual polynomial
numerator of the corresponding coordinate-product weight. -/
theorem homogeneous_coordinate_fraction (r : ℂ) (q : HomogeneousCoordinateTop r) :
    ∃ n : ℕ, ∃ p : WeightedPoly,
      p.IsWeightedHomogeneous CycleQ2GeometricCoordinateWeight.weight (3*n) ∧
      q.val * algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)
        (coordinateProduct r 1 Finset.univ ^ n) =
        algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ) (quotientMap r 1 p) := by
  obtain ⟨n,a,ha,hq⟩ := HomogeneousLocalization.Away.mk_surjective
    (surfaceGrade r 1) (coordinateProduct_univ_mem_grade r) q
  have hspec : q.val * algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)
      (coordinateProduct r 1 Finset.univ ^ n) =
      algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ) a := by
    rw [← hq,HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  obtain ⟨p,hp,hpa⟩ := ha
  change quotientMap r 1 p = a at hpa
  refine ⟨n,p,?_,?_⟩
  · change p.IsWeightedHomogeneous CycleQ2GeometricCoordinateWeight.weight (n • 3) at hp
    simpa only [nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using hp
  · rw [hpa]
    exact hspec

/-- Degree zero on the actual projective coordinate chart means weight
zero in the same nine Laurent coordinates. -/
theorem homogeneous_coordinate_weight (r : ℂ) (q : HomogeneousCoordinateTop r)
    (ab : ShiftIndex) (e : LaurentExponent)
    (hne : (coordinateLaurent r Finset.univ q.val ab).coeff e ≠ 0) :
    (shiftedGrade ab e).1 = 0 := by
  obtain ⟨n,p,hp,hfrac⟩ := homogeneous_coordinate_fraction r q
  exact coordinate_fraction_weight r q.val p n 0 (by simpa using hp) hfrac ab e hne

/-- Multiplication by the original cubic gives weight three in those same
coordinates. The input remains the actual homogeneous section. -/
theorem homogeneous_coordinate_cubic_weight (r : ℂ) (q : HomogeneousCoordinateTop r)
    (ab : ShiftIndex) (e : LaurentExponent)
    (hne : (coordinateLaurent r Finset.univ
      (surfaceQuotient r 1 detectorCubic • q.val) ab).coeff e ≠ 0) :
    (shiftedGrade ab e).1 = 3 := by
  obtain ⟨n,p,hp,hfrac⟩ := homogeneous_coordinate_fraction r q
  have hx0 : (X (0 : Fin 5) : WeightedPoly).IsWeightedHomogeneous
      CycleQ2GeometricCoordinateWeight.weight 1 := by
    simpa [CycleQ2GeometricCoordinateWeight.weight] using
      isWeightedHomogeneous_X ℂ CycleQ2GeometricCoordinateWeight.weight (0 : Fin 5)
  have hnum : (detectorCubic*p).IsWeightedHomogeneous
      CycleQ2GeometricCoordinateWeight.weight (3*n+3) := by
    simpa only [detectorCubic,nsmul_eq_mul,Nat.cast_id,mul_one,Nat.add_comm] using (hx0.pow 3).mul hp
  apply coordinate_fraction_weight r (surfaceQuotient r 1 detectorCubic • q.val)
    (detectorCubic*p) n 3 hnum ?_ ab e hne
  have hsmul : surfaceQuotient r 1 detectorCubic • q.val =
      algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)
        (surfaceQuotient r 1 detectorCubic) * q.val :=
    Algebra.smul_def (surfaceQuotient r 1 detectorCubic) q.val
  rw [hsmul,mul_assoc,hfrac]
  change algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)
      (quotientMap r 1 detectorCubic) *
        algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ) (quotientMap r 1 p) = _
  simp only [map_mul]

/-- The fixed cubic tests the unique weight-three negative coordinate;
its character is the required character one. -/
theorem homogeneous_cubic_negative_unique (r : ℂ) (q : HomogeneousCoordinateTop r)
    (ab : ShiftIndex) (e : LaurentExponent) (he : ∀ i, e i < 0)
    (hne : (coordinateLaurent r Finset.univ
      (surfaceQuotient r 1 detectorCubic • q.val) ab).coeff e ≠ 0) :
    ab = (2,2) ∧ e = (fun _ => -1) ∧ (shiftedGrade ab e).2 = 1 := by
  have hw := homogeneous_coordinate_cubic_weight r q ab e hne
  exact ⟨(strictlyNegative_weight_three_unique ab e he hw).1,
    (strictlyNegative_weight_three_unique ab e he hw).2,
    strictlyNegative_weight_three_character ab e he hw⟩

/-- Any actual homogeneous coordinate descendant of the original literal
Cartier class has a nonzero value in this precise cubic-test coordinate. -/
theorem literal_homogeneous_cubic_coefficient
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d)
    (q : HomogeneousCoordinateTop 57)
    (hq : q.val = coordinateTopRepresentative 57 d) :
    (coordinateLaurent 57 Finset.univ
      (surfaceQuotient 57 1 detectorCubic • q.val) (2,2)).coeff (fun _ => -1) ≠ 0 := by
  have hσ : classOf (coordinateScalarSystem 57)
      (surfaceQuotient 57 1 detectorCubic • d) ≠ 0 := by
    simpa only [map_smul] using literal_descent_cubic_ne_zero d hcd
  obtain ⟨ab,e,he,hne⟩ :=
    (coordinate_class_ne_zero_iff_negative_coefficient 57 _).mp hσ
  have hn : (coordinateLaurent 57 Finset.univ
      (surfaceQuotient 57 1 detectorCubic • q.val) ab).coeff e ≠ 0 := by
    simpa only [coordinateTopRepresentative_smul,hq] using hne
  obtain ⟨rfl,rfl,_⟩ := homogeneous_cubic_negative_unique 57 q ab e he hn
  exact hn

end CycleQ2GeometricHomogeneousWeight

#print axioms CycleQ2GeometricHomogeneousWeight.homogeneous_coordinate_weight
#print axioms CycleQ2GeometricHomogeneousWeight.homogeneous_cubic_negative_unique
#print axioms CycleQ2GeometricHomogeneousWeight.literal_homogeneous_cubic_coefficient

end
end SourceCartierHomogeneousWeight

section SourceCartierHomogeneousProjection

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricCoordinateCharacter

open MvPolynomial CycleQ2SeedTrace CycleQ2IncidenceNormalForm
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricHomogeneousWeight CycleQ2CartierSurfaceGrading

/-- Taking a component for one grading preserves homogeneity for a second
grading because it only removes monomials. -/
theorem component_preserves_homogeneity {R M N : Type*} [CommRing R]
    [AddCommMonoid M] [AddCommMonoid N]
    (w : Fin 5 → M) (v : Fin 5 → N) (m : M) (n : N) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous w m) :
    (weightedHomogeneousComponent v n p).IsWeightedHomogeneous w m := by
  classical
  intro e he
  apply hp
  intro hz
  apply he
  rw [coeff_weightedHomogeneousComponent]
  split <;> simp only [hz]

/-- The actual character projection of a genuine projective chart section
again has a genuine degree-zero homogeneous fraction representative. -/
theorem exists_homogeneous_project (r : ℂ) (χ : ZMod 3)
    (q : HomogeneousCoordinateTop r) :
    ∃ qχ : HomogeneousCoordinateTop r,
      qχ.val = coordinateProject r Finset.univ χ q.val := by
  obtain ⟨n,p,hp,hfrac⟩ := homogeneous_coordinate_fraction r q
  let pχ := weightedHomogeneousComponent characterWeight χ p
  have hpχ : pχ.IsWeightedHomogeneous CycleQ2GeometricCoordinateWeight.weight (3*n) :=
    component_preserves_homogeneity CycleQ2GeometricCoordinateWeight.weight
      characterWeight (3*n) χ p hp
  have hnum : quotientMap r 1 pχ ∈ surfaceGrade r 1 (n • (3 : ℕ)) := by
    have hpχ' : pχ ∈ CycleQ2CartierSurfaceGrading.PolynomialGrade (3*n) := by
      change pχ.IsWeightedHomogeneous CycleQ2GeometricCoordinateWeight.weight (3*n)
      exact hpχ
    have h := surfaceQuotient_mem_grade r 1 hpχ'
    change quotientMap r 1 pχ ∈ surfaceGrade r 1 (3*n) at h
    simpa only [nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using h
  let qχ : HomogeneousCoordinateTop r := HomogeneousLocalization.Away.mk
    (surfaceGrade r 1) (coordinateProduct_univ_mem_grade r) n (quotientMap r 1 pχ) hnum
  have hval : qχ.val = polynomialFraction r n pχ := by
    dsimp only [qχ]
    rw [HomogeneousLocalization.Away.val_mk,Localization.mk_eq_mk']
    rfl
  have hq : q.val = polynomialFraction r n p :=
    IsLocalization.eq_mk'_iff_mul_eq.mpr hfrac
  refine ⟨qχ,?_⟩
  rw [hq,coordinateProject_polynomialFraction]
  exact hval

/-- The uniquely determined homogeneous section above the actual coordinate
character projection. Its value is fixed by the original section. -/
def homogeneousProject (r : ℂ) (χ : ZMod 3) (q : HomogeneousCoordinateTop r) :
    HomogeneousCoordinateTop r := (exists_homogeneous_project r χ q).choose

@[simp] theorem homogeneousProject_val (r : ℂ) (χ : ZMod 3)
    (q : HomogeneousCoordinateTop r) :
    (homogeneousProject r χ q).val = coordinateProject r Finset.univ χ q.val :=
  (exists_homogeneous_project r χ q).choose_spec

end CycleQ2GeometricCoordinateCharacter

#print axioms CycleQ2GeometricCoordinateCharacter.component_preserves_homogeneity
#print axioms CycleQ2GeometricCoordinateCharacter.exists_homogeneous_project
#print axioms CycleQ2GeometricCoordinateCharacter.homogeneousProject_val

end
end SourceCartierHomogeneousProjection

section SourceCartierCharacterNonzero

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricCoordinateCharacter

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2SeedTrace
  CycleQ2NormalConnecting CycleQ2SeedCechThreeOpen
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricCartierCech CycleQ2GeometricFourOpenCech
  CycleQ2GeometricLaurentTop CycleQ2GeometricHomogeneousWeight

theorem detectorCubic_character :
    detectorCubic.IsWeightedHomogeneous characterWeight 0 := by
  have hx := (isWeightedHomogeneous_X ℂ characterWeight (0 : Fin 5)).pow 3
  have hdegree : 3 • characterWeight (0 : Fin 5) = (0 : ZMod 3) := by decide
  simpa only [detectorCubic,hdegree] using hx

/-- The original invariant cubic commutes with the actual coordinate projection. -/
theorem coordinateProject_detectorCubic (r : ℂ) (χ : ZMod 3)
    (q : CoordinateLocal r 1 Finset.univ) :
    coordinateProject r Finset.univ χ (surfaceQuotient r 1 detectorCubic • q) =
      surfaceQuotient r 1 detectorCubic • coordinateProject r Finset.univ χ q := by
  have hsmul (v : CoordinateLocal r 1 Finset.univ) :
      surfaceQuotient r 1 detectorCubic • v =
        algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 Finset.univ)
          (surfaceQuotient r 1 detectorCubic) * v :=
    Algebra.smul_def (surfaceQuotient r 1 detectorCubic) v
  rw [hsmul q,hsmul (coordinateProject r Finset.univ χ q)]
  have hquot : surfaceQuotient r 1 detectorCubic = quotientMap r 1 detectorCubic := rfl
  rw [hquot]
  exact coordinateProject_mul_invariant r q detectorCubic χ detectorCubic_character

theorem negative_zero_mul (r : ℂ) (z : SurfaceRing r 1)
    (q : CoordinateLocal r 1 Finset.univ)
    (hq : ∀ ab e, (∀ i, e i < 0) → (coordinateLaurent r Finset.univ q ab).coeff e = 0) :
    ∀ ab e, (∀ i, e i < 0) →
      (coordinateLaurent r Finset.univ (z • q) ab).coeff e = 0 := by
  obtain ⟨p01,p02,p12,hp⟩ := (coordinate_all_negative_zero_iff r q).mp hq
  apply (coordinate_all_negative_zero_iff r (z • q)).mpr
  refine ⟨z • p01,z • p02,z • p12,?_⟩
  let r01 := coordinateRestriction r 1
    (show ({0,1} : Finset (Fin 3)) ⊆ Finset.univ by simp) p01
  let r02 := coordinateRestriction r 1
    (show ({0,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p02
  let r12 := coordinateRestriction r 1
    (show ({1,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p12
  have hsub : z • (r12-r02) = z • r12-z • r02 := smul_sub z r12 r02
  have hadd : z • (r12-r02+r01) = z • (r12-r02)+z • r01 :=
    smul_add z (r12-r02) r01
  have hh := congrArg (fun v : CoordinateLocal r 1 Finset.univ => z • v) hp
  change z • (r12-r02+r01) = z • q at hh
  rw [hadd,hsub] at hh
  simpa only [map_smul] using hh

/-- The coefficient of the projected cubic test is literally the original
nonzero coefficient, since that unique weight-three monomial has character one. -/
theorem projected_cubic_coefficient
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d)
    (q : HomogeneousCoordinateTop 57)
    (hq : q.val = coordinateTopRepresentative 57 d) :
    (coordinateLaurent 57 Finset.univ
      (surfaceQuotient 57 1 detectorCubic • coordinateProject 57 Finset.univ 1 q.val)
      (2,2)).coeff (fun _ => -1) ≠ 0 := by
  rw [← coordinateProject_detectorCubic,coordinateProject_coordinates,characterPart_coeff]
  have hc : (shiftedGrade (2,2) (fun _ => -1)).2 = (1 : ZMod 3) := by
    decide
  rw [if_pos hc]
  exact literal_homogeneous_cubic_coefficient d hcd q hq

/-- The character-one projection of the SAME actual descendant has a nonzero
top coordinate. Its nonvanishing is forced by the original cubic test. -/
theorem literal_character_one_negative
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d)
    (q : HomogeneousCoordinateTop 57)
    (hq : q.val = coordinateTopRepresentative 57 d) :
    ∃ ab e, (∀ i, e i < 0) ∧
      (coordinateLaurent 57 Finset.univ (coordinateProject 57 Finset.univ 1 q.val) ab).coeff e ≠ 0 := by
  by_contra hn
  have hz : ∀ ab e, (∀ i, e i < 0) →
      (coordinateLaurent 57 Finset.univ (coordinateProject 57 Finset.univ 1 q.val) ab).coeff e = 0 := by
    intro ab e he
    by_contra hc
    exact hn ⟨ab,e,he,hc⟩
  have hσ := negative_zero_mul 57 (surfaceQuotient 57 1 detectorCubic)
    (coordinateProject 57 Finset.univ 1 q.val) hz (2,2) (fun _ => -1) (by intro i; norm_num)
  exact projected_cubic_coefficient d hcd q hq hσ

theorem projected_homogeneous_grade (r : ℂ) (χ : ZMod 3)
    (q : HomogeneousCoordinateTop r) (ab : ShiftIndex) :
    HasGrade ab (0,χ)
      (coordinateLaurent r Finset.univ (coordinateProject r Finset.univ χ q.val) ab) := by
  rw [coordinateProject_coordinates]
  exact characterPart_grade χ ab _ (fun e hn => homogeneous_coordinate_weight r q ab e hn)

/-- A closed, literal character-one seed result retaining both the original
Cartier descent witnesses and the genuine homogeneous coordinate section. -/
theorem literal_homogeneous_character_one_nonzero :
    ∃ (d : TwoCocycles (coordinateScalarSystem 57)) (q : HomogeneousCoordinateTop 57),
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d ∧
      q.val = coordinateTopRepresentative 57 d ∧
      (∀ ab, HasGrade ab (0,1)
        (coordinateLaurent 57 Finset.univ (coordinateProject 57 Finset.univ 1 q.val) ab)) ∧
      ∃ ab e, (∀ i, e i < 0) ∧
        (coordinateLaurent 57 Finset.univ (coordinateProject 57 Finset.univ 1 q.val) ab).coeff e ≠ 0 := by
  obtain ⟨d,q,hcd,hq,_,_⟩ := literal_homogeneous_coordinate_cubic_nonzero
  exact ⟨d,q,hcd,hq,projected_homogeneous_grade 57 1 q,
    literal_character_one_negative d hcd q hq⟩

end CycleQ2GeometricCoordinateCharacter

#print axioms CycleQ2GeometricCoordinateCharacter.coordinateProject_detectorCubic
#print axioms CycleQ2GeometricCoordinateCharacter.literal_character_one_negative
#print axioms CycleQ2GeometricCoordinateCharacter.literal_homogeneous_character_one_nonzero

end
end SourceCartierCharacterNonzero
