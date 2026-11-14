import Proposal.SolutionSupport02Part02

/-! Components extracted from SolutionSupport02.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_3/SeedLinkageReflection.lean -/
section
/-! Sound sparse checks for actual five-variable normal forms of the literal
linkage sections.  Polynomial equality is proved over every ring of
characteristic109; finite computations do not assume any matrix rank. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageReflection

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceJacobian CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection
  CycleQ2SeedLinkageIdeals CycleQ2SparseModularPolynomial

def fullCoefficient (e : SourceTuple) : Sparse → ℕ
  | [] => 0
  | a::p => ((if a.1=e then a.2 else 0)+fullCoefficient e p)%109

def fullGood (d ch : ℕ) (p : Sparse) : Bool := p.all (fun a => sourceGood d ch a.1)

noncomputable section
variable {R : Type*} [CommRing R]

def fullValue [CharP R 109] (p : Sparse) : Poly R :=
  CycleQ2SparseModularPolynomial.eval (fun i : Fin 5 => X i) p

@[simp] theorem fullValue_nil [CharP R 109] : fullValue (R:=R) []=0 := rfl

@[simp] theorem fullValue_cons [CharP R 109] (a : Term) (p : Sparse) :
    fullValue (R:=R) (a::p)=termValue (fun i : Fin 5 => (X i : Poly R)) a+fullValue p := rfl

theorem sourceTupleExponent_injective : Function.Injective sourceTupleExponent := by
  intro e f h
  have h0 := congrArg (fun q : FullExponent => q 0) h
  have h1 := congrArg (fun q : FullExponent => q 1) h
  have h2 := congrArg (fun q : FullExponent => q 2) h
  have h3 := congrArg (fun q : FullExponent => q 3) h
  have h4 := congrArg (fun q : FullExponent => q 4) h
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4)))

theorem termValue_variables [CharP R 109] (a : Term) :
    termValue (fun i : Fin 5 => (X i : Poly R)) a =
      MvPolynomial.monomial (sourceTupleExponent a.1) (a.2:R) := by
  change (a.2 : Poly R)*sourceMonomial a.1=_
  rw [sourceMonomial_eq_monomial]
  rw [←map_natCast (C : R →+* Poly R) a.2,C_mul_monomial,mul_one]

theorem fullValue_coefficient [CharP R 109] (e : SourceTuple) (p : Sparse) :
    (fullValue (R:=R) p).coeff (sourceTupleExponent e)=(fullCoefficient e p:R) := by
  induction p with
  | nil => simp [fullCoefficient]
  | cons a p ih =>
    rw [fullValue_cons,coeff_add,termValue_variables,coeff_monomial,ih]
    by_cases he : a.1=e
    · simp [fullCoefficient,he,←CharP.cast_eq_mod R 109,Nat.cast_add]
    · have he' : sourceTupleExponent a.1≠sourceTupleExponent e :=
        fun h => he (sourceTupleExponent_injective h)
      simp only [fullCoefficient,if_neg he,if_neg he',←CharP.cast_eq_mod R 109,Nat.cast_add,Nat.cast_zero]

theorem fullGood_term [CharP R 109] (d ch : ℕ) (a : Term)
    (ha : sourceGood d ch a.1=true) :
    FullStandard (termValue (fun i : Fin 5 => (X i : Poly R)) a) ∧
      HG (termValue (fun i : Fin 5 => (X i : Poly R)) a) (d,(ch:ZMod 3)) := by
  have hm : termValue (fun i : Fin 5 => (X i : Poly R)) a=C (a.2:R)*sourceMonomial a.1 := by
    rw [termValue_variables,sourceMonomial_eq_monomial,C_mul_monomial,mul_one]
  rw [hm]
  have h := sourceGood_evaluation (R:=R) d ch a.1 ha
  exact ⟨fullStandard_C_mul h.1 _,h.2.C_mul _⟩

theorem fullGood_value [CharP R 109] (d ch : ℕ) (p : Sparse)
    (hp : fullGood d ch p=true) :
    FullStandard (fullValue (R:=R) p) ∧ HG (fullValue (R:=R) p) (d,(ch:ZMod 3)) := by
  induction p with
  | nil => exact ⟨by simp [FullStandard],(weightedHomogeneousSubmodule R fullGrading (d,(ch:ZMod 3))).zero_mem⟩
  | cons a p ih =>
    simp only [fullGood,List.all_cons,Bool.and_eq_true] at hp
    have ha := fullGood_term (R:=R) d ch a hp.1
    have hb := ih hp.2
    rw [fullValue_cons]
    exact ⟨fullStandard_add ha.1 hb.1,ha.2.add hb.2⟩

theorem checked_seedNormal [CharP R 109] [Nontrivial R]
    (r ι : R) (d ch : ℕ) (p n a b h g : Sparse)
    (hh : fullValue (R:=R) h=smoothH ι) (hg : fullValue (R:=R) g=seedG r)
    (hn : fullGood d ch n=true) (hc : checkZero (CycleQ2CurveRestrictionReflection.residual p n a b h g)=true) :
    seedNormal r ι (fullValue p)=fullValue n := by
  have hz := eval_eq_zero_of_check (fun i : Fin 5 => (X i : Poly R)) _ hc
  simp only [CycleQ2CurveRestrictionReflection.residual,CycleQ2SparseModularPolynomial.eval_add,
    CycleQ2SparseModularPolynomial.eval_neg,CycleQ2SparseModularPolynomial.eval_mul] at hz
  change fullValue p+ -(fullValue n+(fullValue a*fullValue h+fullValue b*fullValue g))=0 at hz
  rw [hh,hg] at hz
  symm
  apply seedNormal_unique r ι (fullValue p) (fullValue n) (fullValue a) (fullValue b)
  · exact (fullGood_value d ch n hn).1
  · linear_combination hz

end
end CycleQ2SeedLinkageReflection

#print axioms CycleQ2SeedLinkageReflection.checked_seedNormal
#print axioms CycleQ2SeedLinkageReflection.fullValue_coefficient
end


/- Component: continuation_3/SeedLinkageSections.lean -/
section
/-! Homogeneous monomial multiples of the literal linkage generators, and
the exact finite-minor criterion for their independence in the seed quotient. -/

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageSections

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection CycleQ2SeedLinkageIdeals

abbrev SectionColumn := Fin 5 × SourceTuple

def tupleDegree (e : SourceTuple) : ℕ :=
  e.1+e.2.1+e.2.2.1+e.2.2.2.1+2*e.2.2.2.2

def tupleCharacter (e : SourceTuple) : ℕ := 2*e.1+2*e.2.1+e.2.2.1

def sectionGood (d ch : ℕ) (c : SectionColumn) : Bool :=
  decide (tupleDegree c.2+generatorDegree c.1=d ∧
    (tupleCharacter c.2+generatorCharacter c.1)%3=ch)

noncomputable section
variable {R : Type*} [CommRing R]

def sectionPolynomial (s : Side) (r : R) (c : SectionColumn) : Poly R :=
  sourceMonomial c.2*linkageGenerator s r c.1

@[simp] theorem map_sectionPolynomial {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (c : SectionColumn) :
    MvPolynomial.map φ (sectionPolynomial s r c)=sectionPolynomial s (φ r) c := by
  simp only [sectionPolynomial,map_mul,map_sourceMonomial,map_linkageGenerator]

theorem sourceMonomial_grade (e : SourceTuple) :
    HG (sourceMonomial e : Poly R) (tupleDegree e,(tupleCharacter e:ZMod 3)) := by
  rw [sourceMonomial_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [fullGrading_weight]
  rfl

theorem sectionPolynomial_homogeneous (s : Side) (r : R) (d ch : ℕ)
    (c : SectionColumn) (hc : sectionGood d ch c=true) :
    HG (sectionPolynomial s r c) (d,(ch:ZMod 3)) := by
  have h : tupleDegree c.2+generatorDegree c.1=d ∧
      (tupleCharacter c.2+generatorCharacter c.1)%3=ch := of_decide_eq_true hc
  have hg := (sourceMonomial_grade (R:=R) c.2).mul (linkageGenerator_homogeneous s r c.1)
  have he : (tupleDegree c.2,(tupleCharacter c.2:ZMod 3))+
      (generatorDegree c.1,(generatorCharacter c.1:ZMod 3))=(d,(ch:ZMod 3)) := by
    apply Prod.ext
    · exact h.1
    · have hh := congrArg (fun n : ℕ => (n:ZMod 3)) h.2
      simpa using hh
  exact he ▸ hg

def sectionClass (s : Side) (r ι : R) (d ch : ℕ) (c : SectionColumn)
    (hc : sectionGood d ch c=true) : SeedPiece r ι d ch :=
  ⟨Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (sectionPolynomial s r c),
    Submodule.mem_map.mpr ⟨sectionPolynomial s r c,sectionPolynomial_homogeneous s r d ch c hc,rfl⟩⟩

def idealSection (s : Side) (r ι : R) (d ch : ℕ) (c : SectionColumn)
    (hc : sectionGood d ch c=true) : linkagePiece s r ι d ch :=
  ⟨sectionClass s r ι d ch c hc,by
    change Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (sectionPolynomial s r c) ∈ linkageIdeal s r ι
    rw [sectionPolynomial,map_mul]
    exact Ideal.mul_mem_left _ _ (linkageGenerator_mem s r ι c.1)⟩

def sectionCoefficient [Nontrivial R] (s : Side) (r ι : R)
    (row : SourceTuple) (c : SectionColumn) : R :=
  (seedNormal r ι (sectionPolynomial s r c)).coeff (sourceTupleExponent row)

theorem sectionCoefficient_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (row : SourceTuple) (c : SectionColumn) :
    φ (sectionCoefficient s r ι row c)=sectionCoefficient s (φ r) (φ ι) row c := by
  unfold sectionCoefficient
  rw [←coeff_map,seedNormal_map,map_sectionPolynomial]

section Field
variable {K : Type*} [Field K]

theorem idealSections_independent_of_minor (s : Side) (r ι : K) (d ch n : ℕ)
    (rows : Fin n → SourceTuple) (columns : Fin n → SectionColumn)
    (hcolumns : ∀ j, sectionGood d ch (columns j)=true)
    (hdet : Matrix.det (fun i j : Fin n => sectionCoefficient s r ι (rows i) (columns j))≠0) :
    LinearIndependent K (fun j => idealSection s r ι d ch (columns j) (hcolumns j)) := by
  classical
  let A : Matrix (Fin n) (Fin n) K := fun i j => sectionCoefficient s r ι (rows i) (columns j)
  have hA : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (A.isUnit_iff_isUnit_det.mpr ((isUnit_iff_ne_zero).mpr hdet))
  refine (Fintype.linearIndependent_iff (R:=K)
    (v:=fun j => idealSection s r ι d ch (columns j) (hcolumns j))).mpr ?_
  intro v hv j
  let P : Poly K := ∑ k, v k • sectionPolynomial s r (columns k)
  have hz : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) P=0 := by
    have h := congrArg (fun q : linkagePiece s r ι d ch => q.val.val) hv
    change (Ideal.Quotient.mkₐ K (equationsIdeal (smoothH ι) (smoothF r ι))) P=0
    simp only [P,map_sum,map_smul]
    simpa only [Submodule.coe_sum,Submodule.coe_smul,Submodule.coe_zero,
      idealSection,sectionClass,Ideal.Quotient.mkₐ_eq_mk] using h
  have hn : seedNormal r ι P=0 :=
    (seedNormal_eq_zero_iff r ι P).mpr (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hAv : A.mulVec v=0 := by
    funext i
    have hcoeff := congrArg (fun p : Poly K => p.coeff (sourceTupleExponent (rows i))) hn
    have hsum : (seedNormal r ι P).coeff (sourceTupleExponent (rows i))=A.mulVec v i := by
      simp only [P,map_sum,map_smul,coeff_sum,coeff_smul,RingHom.id_apply,
        Matrix.mulVec,dotProduct,A,sectionCoefficient]
      apply Finset.sum_congr rfl
      intro k hk
      exact mul_comm _ _
    rw [hsum,coeff_zero] at hcoeff
    exact hcoeff
  have hv0 : v=0 := hA (by simpa using hAv)
  exact congrFun hv0 j

theorem linkagePiece_rank_lower_bound (s : Side) (r ι : K) (d ch n : ℕ) (hch : ch<3)
    (rows : Fin n → SourceTuple) (columns : Fin n → SectionColumn)
    (hcolumns : ∀ j, sectionGood d ch (columns j)=true)
    (hdet : Matrix.det (fun i j : Fin n => sectionCoefficient s r ι (rows i) (columns j))≠0) :
    n ≤ Module.finrank K (linkagePiece s r ι d ch) := by
  letI : FiniteDimensional K (SeedPiece r ι d ch) :=
    Module.Finite.of_basis (seedPieceBasis r ι d ch hch)
  simpa using (idealSections_independent_of_minor s r ι d ch n rows columns hcolumns hdet).fintype_card_le_finrank

end Field
end
end CycleQ2SeedLinkageSections

#print axioms CycleQ2SeedLinkageSections.idealSections_independent_of_minor
#print axioms CycleQ2SeedLinkageSections.linkagePiece_rank_lower_bound
end


/- Component: continuation_3/SeedQuotientGrading.lean -/
section
/-! # Agreement of the coordinate grading with the polynomial grading -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedQuotientGrading

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechLinearCoordinates
  CycleQ2SeedCechRestrictions

variable (R : Type*) [CommRing R]

def mergeExponent (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) : FullExponent :=
  Finsupp.equivFunOnFinite.symm ![e 0, d 0, d 1, d 2, e 1]

lemma coeff_curry (p : AddMonoidAlgebra R ((Fin 2 →₀ ℕ) × (Fin 3 →₀ ℕ)))
    (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) :
    ((AddMonoidAlgebra.curryAlgEquiv R p).coeff e).coeff d = p.coeff (e, d) := rfl

lemma regroup_coeff_coeff (p : Poly R) (e : Fin 2 →₀ ℕ) (d : Fin 3 →₀ ℕ) :
    ((regroup R p).coeff e).coeff d = p.coeff (mergeExponent e d) := by
  change ((AddMonoidAlgebra.curryAlgEquiv R
    (AddMonoidAlgebra.domCongr R R Finsupp.sumFinsuppAddEquivProdFinsupp
      (renameEquiv R splitIndex p))).coeff e).coeff d = _
  rw [coeff_curry, AddMonoidAlgebra.coeff_domCongr]
  have heq : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e, d) =
      (mergeExponent e d).mapDomain splitIndex := by
    ext z
    obtain ⟨j, rfl⟩ := splitIndex.surjective z
    rw [Finsupp.mapDomain_apply splitIndex.injective]
    fin_cases j <;> rfl
  rw [heq]
  exact coeff_rename_mapDomain splitIndex splitIndex.injective p (mergeExponent e d)

def outerExponent (ab : ShiftIndex) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ab.1.val + Finsupp.single 1 ab.2.val

lemma regroup_standard {p : Poly R} (hp : FullStandard p) : Standard (regroup R p) := by
  intro e he
  obtain ⟨d, hd⟩ := exists_coeff_ne_zero (MvPolynomial.mem_support_iff.mp he)
  rw [regroup_coeff_coeff] at hd
  have hb := hp (mergeExponent e d) (MvPolynomial.mem_support_iff.mpr hd)
  exact ⟨hb.1, hb.2⟩

lemma nested_reduced [Nontrivial R] (r ι : R) {p : Nested R} (hp : Standard p) :
    Reduced auxiliaryOrder (nestedH R ι) (nestedG R r) p := by
  intro e he
  rw [(nestedH_leading R ι).1, (nestedG_leading R r).1,
    single_three_le_iff, single_three_le_iff]
  exact ⟨Nat.not_le_of_lt (hp e he).1, Nat.not_le_of_lt (hp e he).2⟩

lemma quotientBasis_repr_reduced {A σ : Type*} [CommRing A]
    (m : MonomialOrder σ) (h F p : MvPolynomial σ A)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hp : Reduced m h F p) (d : reducedExponents m h F) :
    (quotientBasis m h F hh hF hcop).repr (Ideal.Quotient.mk (equationsIdeal h F) p) d =
      p.coeff d.val := by
  let E := reducedQuotientEquiv m h F hh hF hcop
  have he : E ⟨p, hp⟩ = Ideal.Quotient.mk (equationsIdeal h F) p := rfl
  change (MvPolynomial.basisRestrictSupport A (reducedExponents m h F)).repr
    (E.symm (Ideal.Quotient.mk (equationsIdeal h F) p)) d = _
  rw [← he, LinearEquiv.symm_apply_apply]
  rfl

lemma nestedBasis_repr_standard [Nontrivial R] (r ι : R) (p : Nested R)
    (hp : Standard p) (ab : ShiftIndex) :
    (nestedBasis R r ι).repr (Ideal.Quotient.mk (nestedIdeal R r ι) p) ab =
      p.coeff (outerExponent ab) := by
  unfold nestedBasis
  erw [Module.Basis.repr_reindex_apply,
    quotientBasis_repr_reduced auxiliaryOrder (nestedH R ι) (nestedG R r) p
      (nestedH_leading R ι).2 (nestedG_leading R r).2 (nested_coprime R r ι)
      (nested_reduced R r ι hp)]
  rfl

lemma seedBasis_repr_standard [Nontrivial R] (r ι : R) (p : Poly R)
    (hp : FullStandard p) (ab : ShiftIndex) :
    (seedBasis R r ι).repr (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab =
      (regroup R p).coeff (outerExponent ab) := by
  change (nestedBasis R r ι).repr
    (Ideal.Quotient.mk (nestedIdeal R r ι) (regroup R p)) ab = _
  exact nestedBasis_repr_standard R r ι (regroup R p) (regroup_standard R hp) ab

lemma seedBasis_repr_standard_coeff [Nontrivial R] (r ι : R) (p : Poly R)
    (hp : FullStandard p) (ab : ShiftIndex) (d : Fin 3 →₀ ℕ) :
    ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab).coeff d =
        p.coeff (mergeExponent (outerExponent ab) d) := by
  rw [seedBasis_repr_standard R r ι p hp, regroup_coeff_coeff]

def signedGrade (g : Grade) : LaurentGrade := ((g.1 : ℤ), g.2)

theorem mergeExponent_grade (ab : ShiftIndex) (d : Fin 3 →₀ ℕ) :
    signedGrade (Finsupp.weight fullGrading (mergeExponent (outerExponent ab) d)) =
      shiftedGrade ab (castExponent d) := by
  rw [fullGrading_weight]
  apply Prod.ext <;>
    simp [signedGrade, fullDegree, mergeExponent, outerExponent, shiftedGrade,
      Fin.sum_univ_succ, castExponent] <;> ring

@[simp] theorem baseToLaurent_coeff_cast (p : Base R) (d : Fin 3 →₀ ℕ) :
    (baseToLaurent R p).coeff (castExponent d) = p.coeff d :=
  Finsupp.mapDomain_apply castExponent_injective _ _

lemma standard_seedCoordinates_homogeneous [Nontrivial R] (r ι : R)
    (p : Poly R) (g : Grade) (hs : FullStandard p) (hp : HG p g) (ab : ShiftIndex) :
    HasGrade ab (signedGrade g)
      (baseToLaurent R ((seedBasis R r ι).repr
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  intro e he
  by_contra hne
  have hpos : ∀ i, 0 ≤ e i := by
    intro i
    by_contra hi
    exact hne (baseToLaurent_hasPoles R _ e i (by simp) (lt_of_not_ge hi))
  obtain ⟨d, rfl⟩ := (mem_range_castExponent e).mpr hpos
  rw [baseToLaurent_coeff_cast, seedBasis_repr_standard_coeff R r ι p hs] at hne
  have hh := congrArg signedGrade (hp hne)
  rw [mergeExponent_grade] at hh
  exact he hh

/-- Original five-variable homogeneity gives exactly the declared shifts in
all nine canonical quotient coordinates. -/
theorem seedCoordinates_homogeneous [Nontrivial R] (r ι : R)
    (p : Poly R) (g : Grade) (hp : HG p g) (ab : ShiftIndex) :
    HasGrade ab (signedGrade g)
      (baseToLaurent R ((seedBasis R r ι).repr
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  let N := fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  obtain ⟨hN, a, b, hab⟩ := fullRemainder_spec
    (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  have hQ : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p =
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) N := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    simp only [seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial] at hab
    exact (sub_eq_iff_eq_add.mpr hab).symm
  have hNg : HG N g := fullRemainder_preserves_grading
    (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) hp
  rw [hQ]
  exact standard_seedCoordinates_homogeneous R r ι N g hN hNg ab

theorem localized_polynomial_homogeneous [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (p : Poly R) (g : Grade) (hp : HG p g) (ab : ShiftIndex) :
    HasGrade ab (signedGrade g)
      (localizedCoordinates R r ι s (algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p)) ab) := by
  rw [localizedCoordinates_algebraMap]
  exact seedCoordinates_homogeneous R r ι p g hp ab

theorem signedGrade_injective : Function.Injective signedGrade := by
  intro a b hab
  apply Prod.ext
  · exact Nat.cast_injective (congrArg Prod.fst hab)
  · exact congrArg (fun g : LaurentGrade ↦ g.2) hab

/-- The original polynomial grading, allowing a signed target degree. -/
def SignedHomogeneous (p : Poly R) (g : LaurentGrade) : Prop :=
  ∀ e, p.coeff e ≠ 0 → signedGrade (Finsupp.weight fullGrading e) = g

theorem signedHomogeneous_iff (p : Poly R) (g : Grade) :
    SignedHomogeneous R p (signedGrade g) ↔ HG p g := by
  constructor
  · intro hp e he
    exact signedGrade_injective (hp e he)
  · intro hp e he
    exact congrArg signedGrade (hp he)

theorem seedCoordinates_signedHomogeneous [Nontrivial R] (r ι : R)
    (p : Poly R) (g : LaurentGrade) (hp : SignedHomogeneous R p g) (ab : ShiftIndex) :
    HasGrade ab g (baseToLaurent R ((seedBasis R r ι).repr
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  by_cases hz : p = 0
  · subst p
    intro e he
    simp
  · obtain ⟨e, he⟩ := exists_coeff_ne_zero hz
    have hg := hp e he
    have hh : HG p (Finsupp.weight fullGrading e) := by
      apply (signedHomogeneous_iff R p _).mp
      exact hg.symm ▸ hp
    exact hg ▸ seedCoordinates_homogeneous R r ι p _ hh ab

/-- The standard normal form is homogeneous exactly when all nine
canonical coefficient polynomials have the corresponding shifted grades. -/
theorem standard_signedHomogeneous_iff_coordinates [Nontrivial R] (r ι : R)
    (p : Poly R) (g : LaurentGrade) (hs : FullStandard p) :
    SignedHomogeneous R p g ↔
      ∀ ab, HasGrade ab g (baseToLaurent R ((seedBasis R r ι).repr
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab)) := by
  constructor
  · intro hp ab
    exact seedCoordinates_signedHomogeneous R r ι p g hp ab
  · intro hc e he
    have hb := hs e (MvPolynomial.mem_support_iff.mpr he)
    let ab : ShiftIndex := (⟨e 0, hb.1⟩, ⟨e 4, hb.2⟩)
    let d : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e 1, e 2, e 3]
    have heq : mergeExponent (outerExponent ab) d = e := by
      ext i
      fin_cases i <;> simp [mergeExponent, outerExponent, ab, d]
    rw [← heq, mergeExponent_grade]
    by_contra hg
    have hz := hc ab (castExponent d) hg
    rw [baseToLaurent_coeff_cast, seedBasis_repr_standard_coeff R r ι p hs] at hz
    exact he (heq ▸ hz)

/-- Every homogeneous quotient class has a genuinely homogeneous polynomial
representative, with no grading assumption on a chosen initial lift. -/
theorem exists_signed_homogeneous_representative [Nontrivial R] (r ι : R)
    (q : SeedRing r ι) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g (baseToLaurent R ((seedBasis R r ι).repr q ab))) :
    ∃ p : Poly R, FullStandard p ∧ SignedHomogeneous R p g ∧
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p = q := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  let N := fullRemainder (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  obtain ⟨hN, a, b, hab⟩ := fullRemainder_spec
    (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι) p
  have hQ : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p =
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) N := by
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_pair.mpr
    refine ⟨a, b, ?_⟩
    simp only [seedCubicCoefficients_polynomial, seedSexticCoefficients_polynomial] at hab
    exact (sub_eq_iff_eq_add.mpr hab).symm
  refine ⟨N, hN, ?_, hQ.symm⟩
  apply (standard_signedHomogeneous_iff_coordinates R r ι N g hN).mpr
  rw [← hQ]
  exact hq

/-- Signed degree and cubic character of a Laurent monomial in the base variables. -/
def baseGrade : LaurentExponent →+ LaurentGrade where
  toFun e := (∑ i, e i, (2 * e 0 + e 1 : ℤ))
  map_zero' := by simp
  map_add' e f := by
    apply Prod.ext <;> simp [Finset.sum_add_distrib] <;> ring

theorem shiftedGrade_add (ab : ShiftIndex) (e f : LaurentExponent) :
    shiftedGrade ab (e + f) = shiftedGrade ab e + baseGrade f := by
  apply Prod.ext <;> simp [shiftedGrade, baseGrade, Finset.sum_add_distrib] <;> ring

theorem hasGrade_mul_T (ab : ShiftIndex) (g : LaurentGrade) (e : LaurentExponent)
    (p : Laurent (R := R)) (hp : HasGrade ab g p) :
    HasGrade ab (g + baseGrade e) (p * T R e) := by
  intro f hf
  rw [coeff_mul_T]
  apply hp
  intro hh
  apply hf
  calc
    shiftedGrade ab f = shiftedGrade ab ((f - e) + e) := by rw [sub_add_cancel]
    _ = shiftedGrade ab (f - e) + baseGrade e := shiftedGrade_add ab _ _
    _ = g + baseGrade e := by rw [hh]

theorem coordinates_fraction [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (q : SeedLocal R r ι s) (num : SeedRing r ι) (n : ℕ)
    (h : q * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
      algebraMap (SeedRing r ι) (SeedLocal R r ι s) num) (ab : ShiftIndex) :
    baseToLaurent R ((seedBasis R r ι).repr num ab) =
      localizedCoordinates R r ι s q ab * T R (n • openExponent s) := by
  have hh := congrArg (fun z ↦ localizedCoordinates R r ι s z ab) h
  rw [coordinates_mul_base, localizedCoordinates_algebraMap] at hh
  simp only [map_pow, baseToLaurent_baseProduct, T_pow] at hh
  exact hh.symm.trans (mul_comm _ _)

/-- The coordinate definition of a graded local section agrees with an
actual fraction having a polynomial numerator of the required original grade. -/
theorem localized_homogeneous_iff_fraction [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (q : SeedLocal R r ι s) (g : LaurentGrade) :
    (∀ ab, HasGrade ab g (localizedCoordinates R r ι s q ab)) ↔
      ∃ (n : ℕ) (p : Poly R),
        SignedHomogeneous R p (g + baseGrade (n • openExponent s)) ∧
        q * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
          (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
          algebraMap (SeedRing r ι) (SeedLocal R r ι s)
            (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) := by
  constructor
  · intro hq
    obtain ⟨n, num, hn⟩ := IsLocalization.Away.surj
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s)) q
    have hn' : q * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
        algebraMap (SeedRing r ι) (SeedLocal R r ι s) num := by
      simpa only [map_pow] using hn
    have hnum (ab : ShiftIndex) :
        HasGrade ab (g + baseGrade (n • openExponent s))
          (baseToLaurent R ((seedBasis R r ι).repr num ab)) := by
      rw [coordinates_fraction R r ι s q num n hn' ab]
      exact hasGrade_mul_T R ab g _ _ (hq ab)
    obtain ⟨p, _, hp, hpn⟩ := exists_signed_homogeneous_representative R r ι num _ hnum
    refine ⟨n, p, hp, ?_⟩
    simpa only [hpn] using hn'
  · rintro ⟨n, p, hp, hfrac⟩ ab
    have hh := coordinates_fraction R r ι s q
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) n hfrac ab
    have hnum := seedCoordinates_signedHomogeneous R r ι p _ hp ab
    have hrep : localizedCoordinates R r ι s q ab =
        baseToLaurent R ((seedBasis R r ι).repr
          (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p) ab) *
          T R (-(n • openExponent s)) := by
      have hm := congrArg (fun z ↦ z * T R (-(n • openExponent s))) hh
      simpa only [mul_assoc, T_mul, add_neg_cancel, T_zero, mul_one] using hm.symm
    rw [hrep]
    have hz := hasGrade_mul_T R ab _ (-(n • openExponent s)) _ hnum
    simpa only [map_neg, add_neg_cancel_right] using hz

end CycleQ2SeedQuotientGrading

#print axioms CycleQ2SeedQuotientGrading.localized_polynomial_homogeneous

#print axioms CycleQ2SeedQuotientGrading.localized_homogeneous_iff_fraction
end
end


/- Component: continuation_3/SegreComplexChartExact.lean -/
section
/-! # Actual complex Segre exactness on the coordinate Čech cover -/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreComplexChartExact

open MvPolynomial Matrix CycleQ2SegreComplexBasepoint CycleQ2SegreTangentLocal
  CycleQ2IncidenceFirstOrder CycleQ2SegreRelationsLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis

abbrev Chart (s : Finset (Fin 3)) := SeedLocal ℂ 57 Complex.I s

theorem coordinate_remaining (j : Fin 3) :
    coordinate (remainingIndex j) = algebraMap (Base ℂ) ComplexSeedRing (X j) := by
  change Ideal.Quotient.mk _ (X (remainingIndex j)) =
    Ideal.Quotient.mk _ (remainingInclusion ℂ (X j))
  simp [remainingInclusion]

theorem base_coordinate_unit (s : Finset (Fin 3)) (j : Fin 3) (hj : j ∈ s) :
    IsUnit (algebraMap (Base ℂ) (coordinateLocalization ℂ s) (X j)) := by
  have hd : (X j : Base ℂ) ∣ baseProduct ℂ s := Finset.dvd_prod_of_mem X hj
  exact isUnit_of_dvd_unit ((algebraMap (Base ℂ) (coordinateLocalization ℂ s)).map_dvd hd)
    (IsLocalization.Away.algebraMap_isUnit (S := coordinateLocalization ℂ s) _)

theorem seed_coordinate_unit (s : Finset (Fin 3)) (j : Fin 3) (hj : j ∈ s) :
    IsUnit (algebraMap ComplexSeedRing (Chart s) (coordinate (remainingIndex j))) := by
  rw [coordinate_remaining, ← IsScalarTower.algebraMap_apply (Base ℂ) ComplexSeedRing (Chart s)]
  rw [IsScalarTower.algebraMap_apply (Base ℂ) (coordinateLocalization ℂ s) (Chart s)]
  exact (base_coordinate_unit s j hj).map
    (algebraMap (coordinateLocalization ℂ s) (Chart s))

def chartMatrix (s : Finset (Fin 3)) : Matrix (Fin 3) (Fin 3) (Chart s) :=
  (algebraMap ComplexSeedRing (Chart s)).mapMatrix matrix

theorem chartMatrix_cofactors (s : Finset (Fin 3)) :
    CycleQ2SegreLocal.cofactors (chartMatrix s) = 0 := by
  rw [chartMatrix, ← map_cofactors]
  change (algebraMap ComplexSeedRing (Chart s)).mapMatrix
    (CycleQ2SegreLocal.cofactors (seedQuotientMatrix (57 : ℂ) Complex.I)) = 0
  rw [seedQuotientMatrix_cofactors]
  ext i j
  change algebraMap ComplexSeedRing (Chart s) 0 = 0
  exact map_zero _

theorem chartMatrix_entries_generate (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => chartMatrix s ij.1 ij.2)) = ⊤ := by
  obtain ⟨j,hj⟩ := hs
  let φ := algebraMap ComplexSeedRing (Chart s)
  have hm := Ideal.mem_map_of_mem φ (seed_coordinate_power_mem (remainingIndex j))
  have hu : IsUnit (φ (coordinate (remainingIndex j)^coordinatePower (remainingIndex j))) := by
    rw [map_pow]
    exact (seed_coordinate_unit s j hj).pow _
  have ht := Ideal.eq_top_of_isUnit_mem _ hm hu
  simpa only [entryIdeal, Ideal.map_span, ← Set.range_comp, Function.comp_def, φ,
    chartMatrix, RingHom.mapMatrix_apply, Matrix.map_apply] using ht

/-- Actual complex local exactness with its basepoint-freeness premise
discharged by the nonconstructive arithmetic argument. -/
theorem coordinate_chart_relations_exact (s : Finset (Fin 3)) (hs : s.Nonempty)
    (C : Matrix (Fin 3) (Fin 3) (Chart s)) :
    CycleQ2SegreRelations.relations (chartMatrix s) *ᵥ vector C = 0 ↔
      ∃ N : Matrix (Fin 3) (Fin 3) (Chart s), cofactorDifferential (chartMatrix s) N = C :=
  entry_ideal_relations_exact _ _ (chartMatrix_cofactors s) (chartMatrix_entries_generate s hs)

theorem coordinate_chart_ker_eq_range (s : Finset (Fin 3)) (hs : s.Nonempty) :
    LinearMap.ker (relationsLinear (chartMatrix s)) =
      LinearMap.range (cofactorDifferentialLinear (chartMatrix s)) :=
  entry_ideal_ker_eq_range _ (chartMatrix_cofactors s) (chartMatrix_entries_generate s hs)

end CycleQ2SegreComplexChartExact

#print axioms CycleQ2SegreComplexChartExact.chartMatrix_entries_generate
#print axioms CycleQ2SegreComplexChartExact.coordinate_chart_relations_exact
#print axioms CycleQ2SegreComplexChartExact.coordinate_chart_ker_eq_range
end
end


/- Component: continuation_3/cylinder_bridge/SegreLinkageDuality.lean -/
section
/-! The literal regular linkage pairing is perfect wherever the actual
matrix entries generate the unit ideal.  The inverse is an explicit finite
sum coming from that unit-ideal identity; no duality or invertibility of
the two factor ideals is assumed. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreLinkageDuality
open Matrix CycleQ2SegreFactorSequence

variable {A : Type*} [CommRing A] (F : FactorData A)

def leftElement (i : Fin 3) : F.leftIdeal := ⟨F.left i,F.left_mem i⟩
def rightElement (j : Fin 3) : F.rightIdeal := ⟨F.right j,F.right_mem j⟩

theorem pair_divisible (x : F.leftIdeal) (y : F.rightIdeal) :
    F.linkage ∣ (x:A)*(y:A) :=
  Ideal.mem_span_singleton.mp (F.ideals_product (Ideal.mul_mem_mul x.property y.property))

def pairValue (x : F.leftIdeal) (y : F.rightIdeal) : A := (pair_divisible F x y).choose

theorem linkage_pair (x : F.leftIdeal) (y : F.rightIdeal) :
    F.linkage*pairValue F x y=(x:A)*(y:A) :=
  (pair_divisible F x y).choose_spec.symm

def pairing : F.rightIdeal →ₗ[A] (F.leftIdeal →ₗ[A] A) where
  toFun y :=
    { toFun := fun x => pairValue F x y
      map_add' x z := by
        apply F.regular
        change F.linkage*pairValue F (x+z) y=F.linkage*(pairValue F x y+pairValue F z y)
        rw [mul_add,linkage_pair,linkage_pair,linkage_pair]
        change ((x:A)+(z:A))*(y:A)=(x:A)*(y:A)+(z:A)*(y:A)
        ring
      map_smul' c x := by
        apply F.regular
        change F.linkage*pairValue F (c • x) y=F.linkage*(c*pairValue F x y)
        rw [show F.linkage*(c*pairValue F x y)=c*(F.linkage*pairValue F x y) by ring,
          linkage_pair,linkage_pair]
        change (c*(x:A))*(y:A)=c*((x:A)*(y:A))
        ring }
  map_add' y z := by
    ext x
    apply F.regular
    change F.linkage*pairValue F x (y+z)=F.linkage*(pairValue F x y+pairValue F x z)
    rw [mul_add,linkage_pair,linkage_pair,linkage_pair]
    change (x:A)*((y:A)+(z:A))=(x:A)*(y:A)+(x:A)*(z:A)
    ring
  map_smul' c y := by
    ext x
    apply F.regular
    change F.linkage*pairValue F x (c • y)=F.linkage*(c*pairValue F x y)
    rw [show F.linkage*(c*pairValue F x y)=c*(F.linkage*pairValue F x y) by ring,
      linkage_pair,linkage_pair]
    change (x:A)*(c*(y:A))=c*((x:A)*(y:A))
    ring

theorem pairing_selected (i j : Fin 3) :
    pairing F (rightElement F j) (leftElement F i)=F.matrix i j := by
  apply F.regular
  exact (linkage_pair F (leftElement F i) (rightElement F j)).trans (F.product i j)

theorem exists_weights :
    ∃ ξ : Fin 3 × Fin 3 → A, ∑ q, ξ q*F.matrix q.1 q.2=1 := by
  apply Ideal.mem_span_range_iff_exists_fun.mp
  rw [F.entries_generate]
  exact Submodule.mem_top

def weights : Fin 3 × Fin 3 → A := (exists_weights F).choose

theorem weights_sum : ∑ q, weights F q*F.matrix q.1 q.2=1 :=
  (exists_weights F).choose_spec

theorem left_reconstruction (x : F.leftIdeal) :
    (x:A)=∑ q, (weights F q*pairing F (rightElement F q.2) x)*F.left q.1 := by
  apply F.regular
  calc
    F.linkage*(x:A)=(∑ q, weights F q*F.matrix q.1 q.2)*(F.linkage*(x:A)) := by
      rw [weights_sum,one_mul]
    _=∑ q, (weights F q*F.matrix q.1 q.2)*(F.linkage*(x:A)) := by rw [Finset.sum_mul]
    _=∑ q, F.linkage*((weights F q*pairing F (rightElement F q.2) x)*F.left q.1) := by
      apply Finset.sum_congr rfl
      intro q _
      have hpair := linkage_pair F x (rightElement F q.2)
      change F.linkage*pairing F (rightElement F q.2) x=(x:A)*F.right q.2 at hpair
      linear_combination
        -weights F q*(x:A)*(F.product q.1 q.2)-weights F q*F.left q.1*hpair
    _=F.linkage*(∑ q, (weights F q*pairing F (rightElement F q.2) x)*F.left q.1) :=
      (Finset.mul_sum ..).symm

theorem right_reconstruction (y : F.rightIdeal) :
    (y:A)=∑ q, (weights F q*pairing F y (leftElement F q.1))*F.right q.2 := by
  apply F.regular
  calc
    F.linkage*(y:A)=(∑ q, weights F q*F.matrix q.1 q.2)*(F.linkage*(y:A)) := by
      rw [weights_sum,one_mul]
    _=∑ q, (weights F q*F.matrix q.1 q.2)*(F.linkage*(y:A)) := by rw [Finset.sum_mul]
    _=∑ q, F.linkage*((weights F q*pairing F y (leftElement F q.1))*F.right q.2) := by
      apply Finset.sum_congr rfl
      intro q _
      have hpair := linkage_pair F (leftElement F q.1) y
      change F.linkage*pairing F y (leftElement F q.1)=F.left q.1*(y:A) at hpair
      linear_combination
        -weights F q*(y:A)*(F.product q.1 q.2)-weights F q*F.right q.2*hpair
    _=F.linkage*(∑ q, (weights F q*pairing F y (leftElement F q.1))*F.right q.2) :=
      (Finset.mul_sum ..).symm

theorem pairing_injective : Function.Injective (pairing F) := by
  intro y z hyz
  apply Subtype.ext
  rw [right_reconstruction F y,right_reconstruction F z]
  apply Finset.sum_congr rfl
  intro q _
  rw [show pairing F y (leftElement F q.1)=pairing F z (leftElement F q.1) from
    congrArg (fun f : F.leftIdeal →ₗ[A] A => f (leftElement F q.1)) hyz]

def dualInverse (φ : F.leftIdeal →ₗ[A] A) : F.rightIdeal :=
  ∑ q, (weights F q*φ (leftElement F q.1)) • rightElement F q.2

theorem pairing_dualInverse (φ : F.leftIdeal →ₗ[A] A) :
    pairing F (dualInverse F φ)=φ := by
  ext x
  have hx : x=∑ q, (weights F q*pairing F (rightElement F q.2) x) • leftElement F q.1 := by
    apply Subtype.ext
    simpa only [Submodule.coe_sum,Submodule.coe_smul,smul_eq_mul,leftElement] using
      left_reconstruction F x
  have hφ := congrArg φ hx
  simp only [map_sum,map_smul,smul_eq_mul] at hφ
  rw [dualInverse,map_sum,LinearMap.sum_apply]
  calc
    _=∑ q, (weights F q*φ (leftElement F q.1))*pairing F (rightElement F q.2) x := by
      apply Finset.sum_congr rfl
      intro q _
      rw [map_smul,LinearMap.smul_apply,smul_eq_mul]
    _=φ x := by
      rw [hφ]
      apply Finset.sum_congr rfl
      intro q _
      ring

def rightEquivLeftDual : F.rightIdeal ≃ₗ[A] (F.leftIdeal →ₗ[A] A) :=
  LinearEquiv.ofBijective (pairing F)
    ⟨pairing_injective F,fun φ => ⟨dualInverse F φ,pairing_dualInverse F φ⟩⟩

end CycleQ2SegreLinkageDuality

#print axioms CycleQ2SegreLinkageDuality.pairing_selected
#print axioms CycleQ2SegreLinkageDuality.rightEquivLeftDual
end
end


