import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import HodgeTarget
import Proposal.GeometricTarget
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs
import Proposal.Normalization
import Proposal.SolutionSupport02

/-! Source partition of Solution.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_3/SegreModularCorrelationExpressions.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SegreModularCorrelationExpressions
open CycleQ2SparseModularFunctional CycleQ2SparseModularFastDot
  CycleQ2SparseModularCorrelation CycleQ2SegreModularFastActions
  CycleQ2SegreModularFastExpressions CycleQ2SegreModularDetectorExpressions

def base : ℕ := 1099511627776
def extent : ℕ := 840

def negativeSlot : Fin 3 → Fin 3 → Fin 3 :=
  ![![0,0,0],![1,2,0],![2,0,1]]

def positiveSlot : Fin 3 → Fin 3 → Fin 3 :=
  ![![0,0,0],![2,0,1],![1,2,0]]

def emptyTable (_ _ : Fin 3) : List FastBlock := []

def negativeTable : Fin 3 → Fin 3 → Fin 3 → Fin 3 → List FastBlock :=
  ![![emptyTable,emptyTable,emptyTable],![fast22,fast20,fast21],![fast11,fast12,fast10]]

def positiveTable : Fin 3 → Fin 3 → Fin 3 → Fin 3 → List FastBlock :=
  ![![emptyTable,emptyTable,emptyTable],![fast21,fast22,fast20],![fast12,fast10,fast11]]

def pairFast (W : WeightData) (i j a b : Fin 3) (u v : ℕ) : ℕ :=
  (108*groupedDot W 0 (negativeSlot i j) (u+29*v) (negativeTable i j a b)+
    groupedDot W 0 (positiveSlot i j) (u+29*v) (positiveTable i j a b))%109

theorem fastEntry_eq_pair (W : WeightData) (i j a b : Fin 3) (u v : ℕ) :
    fastEntry i j W a b u v=pairFast W i j a b u v := by
  fin_cases i <;> fin_cases j
  · rfl
  · rfl
  · rfl
  · rfl
  · exact congrArg (fun n : ℕ => n%109) (Nat.add_comm _ _)
  · rfl
  · exact congrArg (fun n : ℕ => n%109) (Nat.add_comm _ _)
  · rfl
  · exact congrArg (fun n : ℕ => n%109) (Nat.add_comm _ _)

def packedEntry (W : WeightData) (i j a b : Fin 3) : ℕ :=
  108*packedDot base extent W 0 (negativeSlot i j) (negativeTable i j a b)+
    packedDot base extent W 0 (positiveSlot i j) (positiveTable i j a b)

def digit (n s : ℕ) : ℕ :=
  ((n/CycleQ2BinaryNaturalPower.power base 12 (extent-s))%base)%109

def codeBound (a b : Fin 3) : ℕ := extent-29*(14-a.val-2*b.val)

def codeCheck (a b : Fin 3) (p : List FastBlock) : Bool :=
  p.all (fun c => c.2.2.all (fun t => decide (t.1≤codeBound a b)))

def boundCheck (i j a b : Fin 3) : Bool :=
  decide (255*(108*totalCoefficients (negativeTable i j a b)+
    totalCoefficients (positiveTable i j a b))<base) &&
    (codeCheck a b (negativeTable i j a b) && codeCheck a b (positiveTable i j a b))

def checkBlock (W : WeightData) (i j a b : Fin 3) : Bool :=
  boundCheck i j a b &&
    (List.range 15).all (fun u => (List.range 15).all (fun v =>
      if allowed14 a b u v then digit (packedEntry W i j a b) (u+29*v)==0 else true))

theorem code_le_of_check (a b : Fin 3) (p : List FastBlock)
    (h : codeCheck a b p=true) (c : FastBlock) (hc : c∈p)
    (t : WordTerm) (ht : t∈c.2.2) : t.1≤codeBound a b := by
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h c hc) t ht)

theorem digit_eq_entryDot (W : WeightData) (i j a b : Fin 3) (u v : ℕ)
    (ha : allowed14 a b u v=true) (hb : boundCheck i j a b=true) :
    digit (packedEntry W i j a b) (u+29*v)=entryDot i j W a b u v := by
  have hav : a.val+u+v+2*b.val≤14 ∧ (2*a.val+2*u+v)%3=0 := of_decide_eq_true ha
  have hshift : u+29*v≤29*(14-a.val-2*b.val) := by omega
  have hlimit : 29*(14-a.val-2*b.val)≤extent := by unfold extent; omega
  have hs : u+29*v≤extent := hshift.trans hlimit
  have hh := Bool.and_eq_true_iff.mp hb
  have hco : 255*(108*totalCoefficients (negativeTable i j a b)+
      totalCoefficients (positiveTable i j a b))<base := of_decide_eq_true hh.1
  have hc := Bool.and_eq_true_iff.mp hh.2
  have hp : ∀ c∈negativeTable i j a b,∀t∈c.2.2,t.1+(u+29*v)≤extent := by
    intro c hcm t htm
    have h := code_le_of_check a b _ hc.1 c hcm t htm
    unfold codeBound at h
    omega
  have hq : ∀ c∈positiveTable i j a b,∀t∈c.2.2,t.1+(u+29*v)≤extent := by
    intro c hcm t htm
    have h := code_le_of_check a b _ hc.2 c hcm t htm
    unfold codeBound at h
    omega
  rw [←fastEntry_eq,fastEntry_eq_pair]
  unfold digit packedEntry pairFast
  rw [CycleQ2BinaryNaturalPower.power_eq]
  exact packed_pair_coefficient base extent 108 (u+29*v) (by decide)
    W 0 (negativeSlot i j) 0 (positiveSlot i j)
    (negativeTable i j a b) (positiveTable i j a b) hco hs hp hq

theorem checkEntryBlock_of_correlation (W : WeightData) (i j a b : Fin 3)
    (h : checkBlock W i j a b=true) : checkEntryBlock W i j a b=true := by
  have hb := (Bool.and_eq_true_iff.mp h).1
  have hn := (Bool.and_eq_true_iff.mp h).2
  apply List.all_eq_true.mpr
  intro u hu
  apply List.all_eq_true.mpr
  intro v hv
  have hc := List.all_eq_true.mp (List.all_eq_true.mp hn u hu) v hv
  by_cases ha : allowed14 a b u v=true
  · simpa only [ha,ite_true,digit_eq_entryDot W i j a b u v ha hb] using hc
  · simp [ha]

end CycleQ2SegreModularCorrelationExpressions

#print axioms CycleQ2SegreModularCorrelationExpressions.checkEntryBlock_of_correlation
end


/- Component: continuation_3/SegreModularCubicPairingChecks.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false

namespace CycleQ2SegreModularCubicPairing
open CycleQ2SegreModularDetectorData

theorem all_pairing_checks (k : Fin 7) (c : Fin 9) :
    cubicDot (weights k) c=cubicPairing k c := by
  fin_cases k
  · exact pairing0 c
  · exact pairing1 c
  · exact pairing2 c
  · exact pairing3 c
  · exact pairing4 c
  · exact pairing5 c
  · exact pairing6 c

end CycleQ2SegreModularCubicPairing
#print axioms CycleQ2SegreModularCubicPairing.all_pairing_checks
end


/- Component: continuation_3/SegreModularDetectorDifferential.lean -/
section
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreModularDetectorExpressions
open MvPolynomial CycleQ2SparseModularFunctional CycleQ2IncidenceFirstOrder

def basisMatrix (i j : Fin 3) (p : P) : Matrix (Fin 3) (Fin 3) P :=
  fun r s => if r=i ∧ s=j then p else 0

theorem firstRow_basisDifferential (M : Matrix (Fin 3) (Fin 3) P) (p : P)
    (L : Fin 3 → P →ₗ[F] F) (i j : Fin 3) :
    (∑ c, L c (cofactorDifferential M (basisMatrix i j p) 0 c)) =
      signedEntry i j (fun s k l => L s (M k l*p)) := by
  fin_cases i <;> fin_cases j <;>
    simp [basisMatrix,cofactorDifferential_fin_three,Fin.sum_univ_three,
      signedEntry,signed00,signed01,signed02,signed10,signed11,signed12,
      signed20,signed21,signed22,Matrix.cons_val_zero',Matrix.cons_val_succ',
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,mul_comm] <;> abel

end CycleQ2SegreModularDetectorExpressions
#print axioms CycleQ2SegreModularDetectorExpressions.firstRow_basisDifferential
end
end


/- Component: continuation_3/CurveQuotientGrading.lean -/
section
/-! # The actual polynomial grading in the six curve coordinates -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveQuotientGrading

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2CurveRestriction
  CycleQ2CurveQuotientFiniteFree CycleQ2CurveCechTwoOpen CycleQ2CurveCechLocalization
  CycleQ2CurveCechLocalizedBasis CycleQ2CurveCechRestrictions

variable (R : Type*) [CommRing R]

def mergeExponent (e d : Fin 2 →₀ ℕ) : CurveExponent :=
  Finsupp.equivFunOnFinite.symm ![e 0,d 0,e 1,d 1]

lemma regroup_coeff_coeff (p : CurvePoly R) (e d : Fin 2 →₀ ℕ) :
    ((regroup R p).coeff e).coeff d=p.coeff (mergeExponent e d) := by
  change ((AddMonoidAlgebra.curryAlgEquiv R
    (AddMonoidAlgebra.domCongr R R Finsupp.sumFinsuppAddEquivProdFinsupp
      (renameEquiv R splitIndex p))).coeff e).coeff d=_
  change (AddMonoidAlgebra.domCongr R R Finsupp.sumFinsuppAddEquivProdFinsupp
    (renameEquiv R splitIndex p)).coeff (e,d)=_
  rw [AddMonoidAlgebra.coeff_domCongr]
  have he : Finsupp.sumFinsuppAddEquivProdFinsupp.symm (e,d)=
      (mergeExponent e d).mapDomain splitIndex := by
    ext z
    obtain ⟨j,rfl⟩ := splitIndex.surjective z
    rw [Finsupp.mapDomain_apply splitIndex.injective]
    fin_cases j <;> rfl
  rw [he]
  exact coeff_rename_mapDomain splitIndex splitIndex.injective p (mergeExponent e d)

def outerExponent {s : Side} (ab : ShiftIndex s) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ab.1.val+Finsupp.single 1 ab.2.val

lemma regroup_reduced [Nontrivial R] (s : Side) (r ι : R) {p : CurvePoly R}
    (hp : Standard s p) : Reduced nestedOrder (nestedQ R s r) (nestedH R s r ι) (regroup R p) := by
  intro e he
  obtain ⟨d,hd⟩ := exists_coeff_ne_zero (MvPolynomial.mem_support_iff.mp he)
  rw [regroup_coeff_coeff] at hd
  have hb := hp (mergeExponent e d) (MvPolynomial.mem_support_iff.mpr hd)
  apply (reduced_iff R s r ι e).mpr
  exact ⟨hb.1,hb.2⟩

lemma nestedBasis_repr_reduced [Nontrivial R] (s : Side) (r ι : R) (p : Nested R)
    (hp : Reduced nestedOrder (nestedQ R s r) (nestedH R s r ι) p) (ab : ShiftIndex s) :
    (nestedBasis R s r ι).repr (Ideal.Quotient.mk (nestedIdeal R s r ι) p) ab=
      p.coeff (outerExponent ab) := by
  unfold nestedBasis
  erw [Module.Basis.repr_reindex_apply,
    CycleQ2SeedQuotientGrading.quotientBasis_repr_reduced nestedOrder
      (nestedQ R s r) (nestedH R s r ι) p (nestedQ_leading R s r).2
      (nestedH_leading R s r ι).2 (nested_coprime R s r ι) hp]
  rfl

lemma curveBasis_repr_standard [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R)
    (hp : Standard s p) (ab : ShiftIndex s) :
    (curveBasis R s r ι).repr (Ideal.Quotient.mk (curveIdeal s r ι) p) ab=
      (regroup R p).coeff (outerExponent ab) := by
  change (nestedBasis R s r ι).repr
    (Ideal.Quotient.mk (nestedIdeal R s r ι) (regroup R p)) ab=_
  exact nestedBasis_repr_reduced R s r ι (regroup R p) (regroup_reduced R s r ι hp) ab

lemma curveBasis_repr_standard_coeff [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R)
    (hp : Standard s p) (ab : ShiftIndex s) (d : Fin 2 →₀ ℕ) :
    ((curveBasis R s r ι).repr (Ideal.Quotient.mk (curveIdeal s r ι) p) ab).coeff d=
      p.coeff (mergeExponent (outerExponent ab) d) := by
  rw [curveBasis_repr_standard R s r ι p hp,regroup_coeff_coeff]

def ordinaryDegree (e : CurveExponent) : ℕ := Finsupp.weight (fun _ : Fin 4 => 1) e

theorem ordinaryDegree_eq (e : CurveExponent) : ordinaryDegree e=e 0+e 1+e 2+e 3 := by
  simp [ordinaryDegree,Finsupp.weight, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype,Fin.sum_univ_succ,add_assoc]

theorem mergeExponent_degree {s : Side} (ab : ShiftIndex s) (d : Fin 2 →₀ ℕ) :
    (ordinaryDegree (mergeExponent (outerExponent ab) d):ℤ)=shiftedDegree ab (castExponent d) := by
  rw [ordinaryDegree_eq]
  simp [mergeExponent,outerExponent,shiftedDegree,castExponent]
  ring

@[simp] theorem baseToLaurent_coeff_cast (p : Base R) (d : Fin 2 →₀ ℕ) :
    (baseToLaurent R p).coeff (castExponent d)=p.coeff d :=
  Finsupp.mapDomain_apply castExponent_injective _ _

def SignedHomogeneous (p : CurvePoly R) (d : ℤ) : Prop :=
  ∀ e, p.coeff e≠0 → (ordinaryDegree e:ℤ)=d

theorem signedHomogeneous_iff (p : CurvePoly R) (d : ℕ) :
    SignedHomogeneous R p (d:ℤ) ↔ p.IsWeightedHomogeneous (fun _ : Fin 4 => 1) d := by
  constructor
  · intro hp e he
    exact Nat.cast_injective (hp e he)
  · intro hp e he
    exact congrArg (fun n : ℕ => (n:ℤ)) (hp he)

lemma standard_coordinates_homogeneous [Nontrivial R] (s : Side) (r ι : R)
    (p : CurvePoly R) (d : ℤ) (hs : Standard s p) (hp : SignedHomogeneous R p d)
    (ab : ShiftIndex s) :
    HasDegree ab d (baseToLaurent R ((curveBasis R s r ι).repr
      (Ideal.Quotient.mk (curveIdeal s r ι) p) ab)) := by
  intro e he
  by_contra hne
  have hpos : ∀ i,0≤e i := by
    intro i
    by_contra hi
    exact hne (baseToLaurent_hasPoles R _ e i (by simp) (lt_of_not_ge hi))
  obtain ⟨a,rfl⟩ := (mem_range_castExponent e).mpr hpos
  rw [baseToLaurent_coeff_cast,curveBasis_repr_standard_coeff R s r ι p hs] at hne
  have hh := hp _ hne
  rw [mergeExponent_degree] at hh
  exact he hh

theorem quotient_normal [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    Ideal.Quotient.mk (curveIdeal s r ι) p=
      Ideal.Quotient.mk (curveIdeal s r ι) (normal s r ι p) := by
  obtain ⟨_,a,b,hab⟩ := normal_spec s r ι p
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_span_pair.mpr
  refine ⟨a,b,?_⟩
  exact (sub_eq_iff_eq_add.mpr hab).symm

theorem coordinates_homogeneous [Nontrivial R] (s : Side) (r ι : R)
    (p : CurvePoly R) (d : ℕ) (hp : p.IsWeightedHomogeneous (fun _ : Fin 4 => 1) d)
    (ab : ShiftIndex s) :
    HasDegree ab (d:ℤ) (baseToLaurent R ((curveBasis R s r ι).repr
      (Ideal.Quotient.mk (curveIdeal s r ι) p) ab)) := by
  rw [quotient_normal]
  exact standard_coordinates_homogeneous R s r ι (normal s r ι p) d
    (normal_spec s r ι p).1 ((signedHomogeneous_iff R _ d).mpr (normal_homogeneous s r ι hp)) ab

theorem coordinates_signedHomogeneous [Nontrivial R] (s : Side) (r ι : R)
    (p : CurvePoly R) (d : ℤ) (hp : SignedHomogeneous R p d) (ab : ShiftIndex s) :
    HasDegree ab d (baseToLaurent R ((curveBasis R s r ι).repr
      (Ideal.Quotient.mk (curveIdeal s r ι) p) ab)) := by
  by_cases hz : p=0
  · subst p
    intro e he
    simp
  · obtain ⟨e,he⟩ := exists_coeff_ne_zero hz
    have hd := hp e he
    have hh : p.IsWeightedHomogeneous (fun _ : Fin 4 => 1) (ordinaryDegree e) :=
      (signedHomogeneous_iff R p _).mp (hd.symm ▸ hp)
    exact hd ▸ coordinates_homogeneous R s r ι p _ hh ab

theorem standard_signedHomogeneous_iff_coordinates [Nontrivial R] (s : Side) (r ι : R)
    (p : CurvePoly R) (d : ℤ) (hs : Standard s p) :
    SignedHomogeneous R p d ↔ ∀ ab, HasDegree ab d
      (baseToLaurent R ((curveBasis R s r ι).repr (Ideal.Quotient.mk (curveIdeal s r ι) p) ab)) := by
  constructor
  · intro hp ab
    exact standard_coordinates_homogeneous R s r ι p d hs hp ab
  · intro hc e he
    have hb := hs e (MvPolynomial.mem_support_iff.mpr he)
    let ab : ShiftIndex s := (⟨e 0,hb.1⟩,⟨e 2,hb.2⟩)
    let a : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e 1,e 3]
    have heq : mergeExponent (outerExponent ab) a=e := by
      ext i
      fin_cases i <;> simp [mergeExponent,outerExponent,ab,a]
    rw [← heq,mergeExponent_degree]
    by_contra hg
    have hz := hc ab (castExponent a) hg
    rw [baseToLaurent_coeff_cast,curveBasis_repr_standard_coeff R s r ι p hs] at hz
    exact he (heq ▸ hz)

theorem exists_signed_homogeneous_representative [Nontrivial R] (s : Side) (r ι : R)
    (q : CurveRing s r ι) (d : ℤ)
    (hq : ∀ ab,HasDegree ab d (baseToLaurent R ((curveBasis R s r ι).repr q ab))) :
    ∃ p : CurvePoly R, Standard s p ∧ SignedHomogeneous R p d ∧
      Ideal.Quotient.mk (curveIdeal s r ι) p=q := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨normal s r ι p,(normal_spec s r ι p).1,?_,(quotient_normal R s r ι p).symm⟩
  apply (standard_signedHomogeneous_iff_coordinates R s r ι _ d (normal_spec s r ι p).1).mpr
  rw [← quotient_normal]
  exact hq

def baseDegree : LaurentExponent →+ ℤ where
  toFun e := e 0+e 1
  map_zero' := by simp
  map_add' e f := by simp; ring

theorem shiftedDegree_add {side : Side} (ab : ShiftIndex side) (e f : LaurentExponent) :
    shiftedDegree ab (e+f)=shiftedDegree ab e+baseDegree f := by
  simp [shiftedDegree,baseDegree]
  ring

theorem hasDegree_mul_T {side : Side} (ab : ShiftIndex side) (d : ℤ) (e : LaurentExponent)
    (p : Laurent (R:=R)) (hp : HasDegree ab d p) :
    HasDegree ab (d+baseDegree e) (p*T R e) := by
  intro f hf
  rw [coeff_mul_T]
  apply hp
  intro hh
  apply hf
  calc
    shiftedDegree ab f=shiftedDegree ab ((f-e)+e) := by rw [sub_add_cancel]
    _ =shiftedDegree ab (f-e)+baseDegree e := shiftedDegree_add ab _ _
    _ =d+baseDegree e := by rw [hh]

theorem coordinates_fraction [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2))
    (q : CurveLocal R side r ι s) (num : CurveRing side r ι) (n : ℕ)
    (h : q * algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
      (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s ^ n)) =
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) num) (ab : (ShiftIndex side)) :
    baseToLaurent R ((curveBasis R side r ι).repr num ab) =
      localizedCoordinates R side r ι s q ab * T R (n • openExponent s) := by
  have hh := congrArg (fun z ↦ localizedCoordinates R side r ι s z ab) h
  rw [coordinates_mul_base, localizedCoordinates_algebraMap] at hh
  simp only [map_pow, baseToLaurent_baseProduct, T_pow] at hh
  exact hh.symm.trans (mul_comm _ _)

/-- The coordinate definition of a graded local section agrees with an
actual fraction having a polynomial numerator of the required original grade. -/
theorem localized_homogeneous_iff_fraction [Nontrivial R] (side : Side) (r ι : R)
    (s : Finset (Fin 2)) (q : CurveLocal R side r ι s) (g : ℤ) :
    (∀ ab, HasDegree ab g (localizedCoordinates R side r ι s q ab)) ↔
      ∃ (n : ℕ) (p : CurvePoly R),
        SignedHomogeneous R p (g + baseDegree (n • openExponent s)) ∧
        q * algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
          (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s ^ n)) =
          algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
            (Ideal.Quotient.mk (curveIdeal side r ι) p) := by
  constructor
  · intro hq
    obtain ⟨n, num, hn⟩ := IsLocalization.Away.surj
      (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s)) q
    have hn' : q * algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
        (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s ^ n)) =
        algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) num := by
      simpa only [map_pow] using hn
    have hnum (ab : (ShiftIndex side)) :
        HasDegree ab (g + baseDegree (n • openExponent s))
          (baseToLaurent R ((curveBasis R side r ι).repr num ab)) := by
      rw [coordinates_fraction R side r ι s q num n hn' ab]
      exact hasDegree_mul_T R ab g _ _ (hq ab)
    obtain ⟨p, _, hp, hpn⟩ := exists_signed_homogeneous_representative R side r ι num _ hnum
    refine ⟨n, p, hp, ?_⟩
    simpa only [hpn] using hn'
  · rintro ⟨n, p, hp, hfrac⟩ ab
    have hh := coordinates_fraction R side r ι s q
      (Ideal.Quotient.mk (curveIdeal side r ι) p) n hfrac ab
    have hnum := coordinates_signedHomogeneous R side r ι p _ hp ab
    have hrep : localizedCoordinates R side r ι s q ab =
        baseToLaurent R ((curveBasis R side r ι).repr
          (Ideal.Quotient.mk (curveIdeal side r ι) p) ab) *
          T R (-(n • openExponent s)) := by
      have hm := congrArg (fun z ↦ z * T R (-(n • openExponent s))) hh
      simpa only [mul_assoc, T_mul, add_neg_cancel, T_zero, mul_one] using hm.symm
    rw [hrep]
    have hz := hasDegree_mul_T R ab _ (-(n • openExponent s)) _ hnum
    simpa only [map_neg, add_neg_cancel_right] using hz


end CycleQ2CurveQuotientGrading

#print axioms CycleQ2CurveQuotientGrading.coordinates_homogeneous
#print axioms CycleQ2CurveQuotientGrading.exists_signed_homogeneous_representative

#print axioms CycleQ2CurveQuotientGrading.localized_homogeneous_iff_fraction
end
end


/- Component: continuation_3/IncidenceBasepointChart.lean -/
section
/-! The actual two-leading-coefficient incidence chart intersected with the
proved basepoint-free polynomial open. The literal seed remains a point of
this localization, and every relevant prime of its moving (h,F) quotient
has a nonzero matrix pivot. -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceBasepointChart

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceBasepointOpen
open CycleQ2SegreComplexBasepoint (coordinatePower)

def chartDenominator : Coeff := leadingProduct ℂ*basepointPolynomial

theorem chartDenominator_ne_zero : chartDenominator≠0 :=
  mul_ne_zero (leadingProduct_ne_zero ℂ) basepointPolynomial_ne_zero

abbrev OpenCoefficients := Localization.Away chartDenominator

instance : IsDomain OpenCoefficients :=
  Localization.Away.isDomain chartDenominator_ne_zero

def coefficientMap : Coeff →+* OpenCoefficients := algebraMap _ _

theorem denominator_isUnit : IsUnit (coefficientMap chartDenominator) :=
  IsLocalization.Away.algebraMap_isUnit chartDenominator

theorem basepoint_isUnit : IsUnit (coefficientMap basepointPolynomial) := by
  apply isUnit_of_mul_isUnit_right
  simpa only [chartDenominator,map_mul] using denominator_isUnit

theorem leading_coefficients_units :
    IsUnit (coefficientMap (rawCubicCoefficient fullCubicLeadingIndex)) ∧
      IsUnit (coefficientMap (rawSexticCoefficient fullSexticLeadingIndex)) := by
  have hlead : IsUnit (coefficientMap (leadingProduct ℂ)) := by
    apply isUnit_of_mul_isUnit_left
    simpa only [chartDenominator,map_mul] using denominator_isUnit
  have hpair : IsUnit (coefficientMap (rawCubicCoefficient fullCubicLeadingIndex)*
      coefficientMap (rawSexticCoefficient fullSexticLeadingIndex)) := by
    simpa only [leadingProduct,rawCubicCoefficient,rawSexticCoefficient,map_mul] using hlead
  exact ⟨isUnit_of_mul_isUnit_left hpair,isUnit_of_mul_isUnit_right hpair⟩

theorem seed_leadingProduct : seedEvaluation (leadingProduct ℂ)=1 := by
  change polynomialSpecialization (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (fun _ _ _ => 0) (leadingProduct ℂ)=1
  rw [polynomialSpecialization_leadingProduct]
  simp only [seedCubicCoefficients,seedSexticCoefficients,fullCubicLeadingIndex_exponent,
    fullSexticLeadingIndex_exponent,smoothH_leading_coefficient,smoothF_leading_coefficient,one_mul]

theorem seed_denominator : seedEvaluation chartDenominator=1 := by
  rw [chartDenominator,map_mul,seed_leadingProduct,seed_basepointPolynomial,one_mul]

def seedChart : OpenCoefficients →+* ℂ :=
  IsLocalization.Away.lift chartDenominator
    (show IsUnit (seedEvaluation chartDenominator) by rw [seed_denominator]; exact isUnit_one)

theorem seedChart_coefficientMap (p : Coeff) : seedChart (coefficientMap p)=seedEvaluation p :=
  IsLocalization.Away.lift_eq chartDenominator _ p

theorem universal_coordinate_power_mem (j : Fin 5) :
    curveCoordinate coefficientMap j^coordinatePower j∈entryIdeal coefficientMap :=
  specialized_coordinate_power_mem coefficientMap basepoint_isUnit j

theorem universal_prime_pivot_cover (P : Ideal (CurveRing coefficientMap)) [P.IsPrime]
    (hx : ∃j,curveCoordinate coefficientMap j∉P) :
    ∃i j,curveMatrix coefficientMap i j∉P :=
  specialized_prime_pivot_cover coefficientMap basepoint_isUnit P hx

theorem universal_entries_generate_if_coordinate_unit {T : Type*} [CommRing T]
    (φ : CurveRing coefficientMap →+* T) (j : Fin 5)
    (hu : IsUnit (φ (curveCoordinate coefficientMap j))) :
    Ideal.span (Set.range (fun ij : Fin 3 × Fin 3 => φ (curveMatrix coefficientMap ij.1 ij.2)))=⊤ :=
  entries_generate_if_coordinate_unit coefficientMap basepoint_isUnit φ j hu

end CycleQ2IncidenceBasepointChart

#print axioms CycleQ2IncidenceBasepointChart.seed_denominator
#print axioms CycleQ2IncidenceBasepointChart.universal_prime_pivot_cover
end
end


/- Component: continuation_3/LinkageComponentAlgebra.lean -/
section
/-! Coefficient maps, the second linkage ideal, and an actual complex cube
root for the elementary component decomposition. -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2LinkageComponentAlgebra

open CycleQ2SegreSeed CycleQ2LinkageComponentDecomposition
variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_linkageE (φ : R →+* S) (a b c d : R) (j : Fin 5) :
    φ (linkageE a b c d j)=linkageE (φ a) (φ b) (φ c) (φ d) j := by
  fin_cases j <;> simp [linkageE,linkageP]

theorem map_linkageEprime (φ : R →+* S) (a b c d : R) (j : Fin 5) :
    φ (linkageEprime a b c d j)=linkageEprime (φ a) (φ b) (φ c) (φ d) j := by
  fin_cases j <;> simp [linkageEprime,linkageP]

theorem map_leftIdeal (φ : R →+* S) (a b c d : R) :
    (leftIdeal a b c d).map φ=leftIdeal (φ a) (φ b) (φ c) (φ d) := by
  simp only [leftIdeal,Ideal.map_span,← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext j
  exact map_linkageE φ a b c d j

theorem right_generator_transformed (a b c d : R) (j : Fin 5) :
    linkageE a (-d) c (-b) j=if j=2 then -linkageEprime a b c d j else linkageEprime a b c d j := by
  fin_cases j <;> simp [linkageE,linkageEprime,linkageP] <;> ring

theorem rightIdeal_eq_leftIdeal (a b c d : R) :
    Ideal.span (Set.range (linkageEprime a b c d))=leftIdeal a (-d) c (-b) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨j,rfl⟩
    have h := leftGenerator_mem a (-d) c (-b) j
    rw [right_generator_transformed] at h
    split_ifs at h with hj
    · exact (leftIdeal a (-d) c (-b)).neg_mem_iff.mp h
    · exact h
  · apply Ideal.span_le.mpr
    rintro x ⟨j,rfl⟩
    rw [right_generator_transformed]
    have h : linkageEprime a b c d j∈Ideal.span (Set.range (linkageEprime a b c d)) :=
      Ideal.subset_span ⟨j,rfl⟩
    split_ifs
    · exact (Ideal.span (Set.range (linkageEprime a b c d))).neg_mem h
    · exact h

theorem map_componentIdeal (φ : R →+* S) (z a b c d : R) :
    (componentIdeal z a b c d).map φ=componentIdeal (φ z) (φ a) (φ b) (φ c) (φ d) := by
  simp only [componentIdeal,Ideal.map_span,← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext j
  fin_cases j <;> simp [componentGenerator]

theorem rootValues_eq_pow (z : R) (i : Fin 3) : rootValues z i=z^i.val := by
  fin_cases i <;> simp [rootValues]

def complexRoot : ℂ := Complex.exp (2*(Real.pi:ℂ)*Complex.I/3)

theorem complexRoot_primitive : IsPrimitiveRoot complexRoot 3 :=
  Complex.isPrimitiveRoot_exp 3 (by decide)

theorem complexRoot_quadratic : complexRoot^2+complexRoot+1=0 := by
  have h := complexRoot_primitive.geom_sum_eq_zero (by decide : 1<3)
  norm_num [Finset.sum_range_succ] at h
  linear_combination h

theorem complexRoot_cube : complexRoot^3=1 := complexRoot_primitive.pow_eq_one

theorem complexRoot_units (i j : Fin 3) (hij : i≠j) :
    IsUnit (rootValues complexRoot i-rootValues complexRoot j) ∧
      IsUnit (rootValues complexRoot i^2-rootValues complexRoot j^2) := by
  constructor
  · apply isUnit_iff_ne_zero.mpr
    intro h
    apply hij
    apply Fin.ext
    apply complexRoot_primitive.pow_inj i.isLt j.isLt
    simpa only [rootValues_eq_pow] using sub_eq_zero.mp h
  · apply isUnit_iff_ne_zero.mpr
    intro h
    apply hij
    apply Fin.ext
    apply (complexRoot_primitive.pow_of_coprime 2 (by decide)).pow_inj i.isLt j.isLt
    have he := sub_eq_zero.mp h
    simp only [rootValues_eq_pow] at he
    calc
      (complexRoot^2)^i.val=(complexRoot^i.val)^2 := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
      _=(complexRoot^j.val)^2 := he
      _=(complexRoot^2)^j.val := by rw [←pow_mul,←pow_mul,Nat.mul_comm]

theorem mapped_rootValues (φ : ℂ →+* R) (i : Fin 3) :
    φ (rootValues complexRoot i)=rootValues (φ complexRoot) i := by
  fin_cases i <;> simp [rootValues]

theorem mapped_root_units (φ : ℂ →+* R) (i j : Fin 3) (hij : i≠j) :
    IsUnit (rootValues (φ complexRoot) i-rootValues (φ complexRoot) j) ∧
      IsUnit (rootValues (φ complexRoot) i^2-rootValues (φ complexRoot) j^2) := by
  have h := complexRoot_units i j hij
  constructor
  · simpa only [map_sub,mapped_rootValues] using h.1.map φ
  · simpa only [map_sub,map_pow,mapped_rootValues] using h.2.map φ

end CycleQ2LinkageComponentAlgebra

#print axioms CycleQ2LinkageComponentAlgebra.rightIdeal_eq_leftIdeal
#print axioms CycleQ2LinkageComponentAlgebra.complexRoot_units
end
end


/- Component: continuation_3/cylinder_bridge/ModularFactorChartExact.lean -/
section
/-! # Factor exactness on the actual modular coordinate charts

Every hypothesis of the factor sequence is discharged for the literal
smooth incidence seed at r=57 and i=33 over F109. The two modules are the
actual localized linkage ideals.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ModularFactorChartExact

open CycleQ2IncidenceGaussianArithmetic

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedLinkageIdeals
  CycleQ2SegreFactorSequence

abbrev Chart (s : Finset (Fin 3)) := SeedLocal F109 57 33 s

def chartMap (s : Finset (Fin 3)) : SeedRing (57:F109) 33 →+* Chart s :=
  algebraMap (SeedRing (57:F109) 33) (Chart s)

def leftIdeal (s : Finset (Fin 3)) : Ideal (Chart s) :=
  (linkageIdeal .left (57:F109) 33).map (chartMap s)

def rightIdeal (s : Finset (Fin 3)) : Ideal (Chart s) :=
  (linkageIdeal .right (57:F109) 33).map (chartMap s)

def leftSection (s : Finset (Fin 3)) (i : Fin 3) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.leftSection (57:F109) 33 i)

def rightSection (s : Finset (Fin 3)) (j : Fin 3) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.rightSection (57:F109) 33 j)

def linkage (s : Finset (Fin 3)) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.linkage (57:F109) 33)

theorem linkage_regular (s : Finset (Fin 3)) :
    Function.Injective (fun z : Chart s => linkage s*z) := by
  apply CycleQ2LinkageIdealPrincipal.localization_mul_injective
    (Algebra.algebraMapSubmonoid (SeedRing (57:F109) 33)
      (Submonoid.powers (baseProduct F109 s))) (Chart s)
    (CycleQ2SeedLinkagePrincipal.linkage (57:F109) 33)
  apply CycleQ2SeedLinkageRegular.linkage_mul_injective
  exact (by decide : (33:F109)≠1)

theorem chart_ideals_pairing (s : Finset (Fin 3)) :
    leftIdeal s*rightIdeal s≤Ideal.span {linkage s} := by
  dsimp only [leftIdeal,rightIdeal,linkage]
  exact @CycleQ2SeedLinkagePrincipal.mapped_ideals_pairing F109 inferInstance
    (Chart s) inferInstance (57:F109) 33 (chartMap s)

def factorData (s : Finset (Fin 3)) (hs : s.Nonempty) : FactorData (Chart s) where
  leftIdeal := leftIdeal s
  rightIdeal := rightIdeal s
  linkage := linkage s
  matrix := CycleQ2SegreModularChartExact.chartMatrix (R:=F109) s
  left := leftSection s
  right := rightSection s
  left_mem i := Ideal.mem_map_of_mem (chartMap s)
    (CycleQ2SeedLinkagePrincipal.leftSection_mem (57:F109) 33 i)
  right_mem j := Ideal.mem_map_of_mem (chartMap s)
    (CycleQ2SeedLinkagePrincipal.rightSection_mem (57:F109) 33 j)
  product i j := by
    have h := congrArg (chartMap s)
      (CycleQ2SeedLinkagePrincipal.selected_product (57:F109) 33 i j)
    simpa only [map_mul,leftSection,rightSection,linkage,
      CycleQ2SegreModularChartExact.chartMatrix,CycleQ2SegreModularBasepoint.matrix,
      RingHom.mapMatrix_apply,Matrix.map_apply,chartMap] using h
  ideals_product := chart_ideals_pairing s
  regular := linkage_regular s
  cofactors_zero := CycleQ2SegreModularChartExact.chartMatrix_cofactors (R:=F109) s
  entries_generate := CycleQ2SegreModularChartExact.chartMatrix_entries_generate (R:=F109) s hs

abbrev FactorSections (s : Finset (Fin 3)) :=
  (Fin 3 → leftIdeal s) × (Fin 3 → rightIdeal s)

def chartFactorMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    FactorSections s →ₗ[Chart s] Matrix (Fin 3) (Fin 3) (Chart s) :=
  factorMap (factorData s hs)

def chartGaugeMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Chart s →ₗ[Chart s] FactorSections s := gaugeMap (factorData s hs)

theorem chartFactorMap_formula (s : Finset (Fin 3)) (hs : s.Nonempty)
    (v : FactorSections s) (i j : Fin 3) :
    linkage s*chartFactorMap s hs v i j=
      (v.1 i:Chart s)*rightSection s j+leftSection s i*(v.2 j:Chart s) :=
  linkage_factorMap (factorData s hs) v i j

/-- The literal local short exact factor sequence, without a rank,
local-pivot, ideal-pairing or regularity hypothesis. -/
theorem actual_factor_sequence (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Function.Injective (chartGaugeMap s hs) ∧
    LinearMap.ker (chartFactorMap s hs)=LinearMap.range (chartGaugeMap s hs) ∧
    LinearMap.range (chartFactorMap s hs)=
      LinearMap.ker (cofactorDifferentialLinear (CycleQ2SegreModularChartExact.chartMatrix (R:=F109) s)) :=
  ⟨gaugeMap_injective (factorData s hs),
    ker_factorMap_eq_range_gaugeMap (factorData s hs),
    range_factorMap_eq_ker_differential (factorData s hs)⟩

end CycleQ2ModularFactorChartExact

#print axioms CycleQ2ModularFactorChartExact.linkage_regular
#print axioms CycleQ2ModularFactorChartExact.actual_factor_sequence
end
end


/- Component: continuation_3/ModularGlobalFactorSpaces.lean -/
section
/-! The actual finite-field source and global factor ambient spaces. The
factor ambient spaces are the literal curve restriction kernels; no equality
with the global linkage ideal pieces is needed for the dimension argument. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2ModularGlobalFactorSpaces

open Matrix MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2IncidenceGradedBasis CycleQ2SegreTangentLocal
  CycleQ2CurveRestriction CycleQ2CurveRestrictionModularData
  CycleQ2CurveRestrictionModularChecks CycleQ2SeedLinkageIdeals

abbrev K := CycleQ2IncidenceGaussianArithmetic.F109
abbrev A := SeedRing (57:K) 33
abbrev Input14 := Matrix (Fin 3) (Fin 3) (SeedPiece (57:K) 33 14 0)
abbrev LeftPiece := LinearMap.ker (seedRestrictionPiece .left (57:K) 33 10 0)
abbrev RightPiece := LinearMap.ker (seedRestrictionPiece .right (57:K) 33 8 1)
abbrev Domain := (Fin 3 → LeftPiece) × (Fin 3 → RightPiece)

instance leftPiece_finite : Module.Finite K LeftPiece := by
  letI : Module.Finite K (SeedPiece (57:K) 33 10 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 10 0 (by decide))
  exact Module.Finite.of_injective (LinearMap.ker (seedRestrictionPiece .left (57:K) 33 10 0)).subtype
    Subtype.val_injective

instance rightPiece_finite : Module.Finite K RightPiece := by
  letI : Module.Finite K (SeedPiece (57:K) 33 8 1) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 8 1 (by decide))
  exact Module.Finite.of_injective (LinearMap.ker (seedRestrictionPiece .right (57:K) 33 8 1)).subtype
    Subtype.val_injective

instance input14_finite : Module.Finite K Input14 := by
  letI : Module.Finite K (SeedPiece (57:K) 33 14 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 14 0 (by decide))
  exact Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => Fin 3 → SeedPiece (57:K) 33 14 0)

instance domain_finite : Module.Finite K Domain := by
  letI : Module.Finite K (Fin 3 → LeftPiece) := Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => LeftPiece)
  letI : Module.Finite K (Fin 3 → RightPiece) := Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => RightPiece)
  exact Module.Finite.prod

theorem left_restriction_surjective :
    Function.Surjective (seedRestrictionPiece .left (57:K) 33 10 0) :=
  seedRestrictionPiece_surjective_of_minor .left 57 33 10 0 57
    leftRows leftSources left_rows_cover left_sources_good (left_minor_det_ne_zero (R:=K))

theorem right_restriction_surjective :
    Function.Surjective (seedRestrictionPiece .right (57:K) 33 8 1) :=
  seedRestrictionPiece_surjective_of_minor .right 57 33 8 1 45
    rightRows rightSources right_rows_cover right_sources_good (right_minor_det_ne_zero (R:=K))

theorem leftPiece_finrank : Module.finrank K LeftPiece=56 := by
  letI : Module.Finite K (SeedPiece (57:K) 33 10 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 10 0 (by decide))
  have h := (seedRestrictionPiece .left (57:K) 33 10 0).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr left_restriction_surjective,finrank_top,
    left_seedPiece_rank,left_curvePiece_rank] at h
  change 57+Module.finrank K LeftPiece=113 at h
  omega

theorem rightPiece_finrank : Module.finrank K RightPiece=23 := by
  letI : Module.Finite K (SeedPiece (57:K) 33 8 1) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 8 1 (by decide))
  have h := (seedRestrictionPiece .right (57:K) 33 8 1).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr right_restriction_surjective,finrank_top,
    right_seedPiece_rank,right_curvePiece_rank] at h
  change 45+Module.finrank K RightPiece=68 at h
  omega

theorem domain_finrank : Module.finrank K Domain=237 := by
  letI : Module.Free K LeftPiece := Module.Free.of_divisionRing K LeftPiece
  letI : Module.Free K RightPiece := Module.Free.of_divisionRing K RightPiece
  letI : Module.Finite K (Fin 3 → LeftPiece) := Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => LeftPiece)
  letI : Module.Finite K (Fin 3 → RightPiece) := Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => RightPiece)
  letI : Module.Free K (Fin 3 → LeftPiece) := Module.Free.of_divisionRing K (Fin 3 → LeftPiece)
  letI : Module.Free K (Fin 3 → RightPiece) := Module.Free.of_divisionRing K (Fin 3 → RightPiece)
  change Module.finrank K ((Fin 3 → LeftPiece) × (Fin 3 → RightPiece))=237
  rw [Module.finrank_prod]
  simp only [Module.finrank_pi_fintype,leftPiece_finrank,rightPiece_finrank,
    Finset.sum_const,Fintype.card_fin,Finset.card_univ,smul_eq_mul]

theorem degree14Piece_finrank : Module.finrank K (SeedPiece (57:K) 33 14 0)=239 := by
  change Module.finrank K (quotientPiece fullGrading (smoothH (33:K)) (smoothF (57:K) 33) (14,0))=239
  rw [seed_h_normalized,seed_F_normalized]
  exact fullPiece_degree14_finrank _ _

theorem input14_finrank : Module.finrank K Input14=2151 := by
  letI : Module.Finite K (SeedPiece (57:K) 33 14 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:K) 33 14 0 (by decide))
  letI : Module.Finite K (Fin 3 → SeedPiece (57:K) 33 14 0) :=
    Module.Finite.pi (R:=K) (M:=fun _ : Fin 3 => SeedPiece (57:K) 33 14 0)
  letI : Module.Free K (SeedPiece (57:K) 33 14 0) :=
    Module.Free.of_divisionRing K (SeedPiece (57:K) 33 14 0)
  letI : Module.Free K (Fin 3 → SeedPiece (57:K) 33 14 0) :=
    Module.Free.of_divisionRing K (Fin 3 → SeedPiece (57:K) 33 14 0)
  change Module.finrank K (Fin 3 → Fin 3 → SeedPiece (57:K) 33 14 0)=2151
  simp only [Module.finrank_pi_fintype,degree14Piece_finrank,Finset.sum_const,Fintype.card_fin,
    Finset.card_univ,smul_eq_mul]

def inputToGlobal : Input14 →ₗ[K] Matrix (Fin 3) (Fin 3) A where
  toFun N i j := (N i j).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem inputToGlobal_injective : Function.Injective inputToGlobal := by
  intro N P h
  funext i j
  apply Subtype.ext
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M i j) h

def entryDifferential : Input14 →ₗ[K] Matrix (Fin 3) (Fin 3) A :=
  ((cofactorDifferentialLinear (seedQuotientMatrix (57:K) 33)).restrictScalars K).comp inputToGlobal

def leftValue (v : Domain) (i : Fin 3) : A := (v.1 i).val.val
def rightValue (v : Domain) (j : Fin 3) : A := (v.2 j).val.val
def left (i : Fin 3) : A := CycleQ2SeedLinkagePrincipal.leftSection (57:K) 33 i
def right (j : Fin 3) : A := CycleQ2SeedLinkagePrincipal.rightSection (57:K) 33 j
def linkage : A := CycleQ2SeedLinkagePrincipal.linkage (57:K) 33

theorem linkage_regular : Function.Injective (fun z : A => linkage*z) :=
  CycleQ2SeedLinkageRegular.linkage_mul_injective (57:K) 33 (by decide)

def leftClass (i : Fin 3) : LeftPiece :=
  ⟨⟨left i,Submodule.mem_map.mpr ⟨CycleQ2SeedFactorHomogeneous.polynomialLeft (57:K) i,
    CycleQ2SeedFactorHomogeneous.polynomialLeft_homogeneous (57:K) i,rfl⟩⟩,by
    apply Subtype.ext
    exact linkageIdeal_le_restrictionKernel .left (57:K) 33
      (CycleQ2SeedLinkagePrincipal.leftSection_mem (57:K) 33 i)⟩

def rightClass (j : Fin 3) : RightPiece :=
  ⟨⟨right j,Submodule.mem_map.mpr ⟨CycleQ2SeedFactorHomogeneous.polynomialRight (57:K) j,
    CycleQ2SeedFactorHomogeneous.polynomialRight_homogeneous (57:K) j,rfl⟩⟩,by
    apply Subtype.ext
    exact linkageIdeal_le_restrictionKernel .right (57:K) 33
      (CycleQ2SeedLinkagePrincipal.rightSection_mem (57:K) 33 j)⟩

def gaugeVector : Domain := (leftClass,fun j => -rightClass j)

end CycleQ2ModularGlobalFactorSpaces

#print axioms CycleQ2ModularGlobalFactorSpaces.domain_finrank
#print axioms CycleQ2ModularGlobalFactorSpaces.input14_finrank
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechGlobalGluing.lean -/
section
/-! # Augmented degree-zero exactness for the actual three-open seed complex

Compatible sections in the actual coordinate localizations glue uniquely to
the actual seed quotient. The proof uses the checked nine free coordinates:
compatibility removes every possible negative base exponent. The same proof
preserves the original signed degree and cubic character and produces an
actual homogeneous polynomial representative.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SeedCechGlobalGluing

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechLinearCoordinates
  CycleQ2SeedCechRestrictions CycleQ2SeedQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]

def globalCoordinates (r ι : R) (q : SeedRing r ι) : ShiftIndex → Laurent (R := R) :=
  fun ab => baseToLaurent R ((seedBasis R r ι).repr q ab)

theorem globalCoordinates_injective (r ι : R) :
    Function.Injective (globalCoordinates R r ι) := by
  intro p q hpq
  apply (seedBasis R r ι).repr.injective
  apply Finsupp.ext
  intro ab
  exact baseToLaurent_injective R (congrFun hpq ab)

theorem mem_range_globalCoordinates (r ι : R) (p : ShiftIndex → Laurent (R := R)) :
    p ∈ Set.range (globalCoordinates R r ι) ↔ ∀ ab, HasPoles ∅ (p ab) := by
  constructor
  · rintro ⟨q,rfl⟩ ab
    exact baseToLaurent_hasPoles R _
  · intro hp
    choose a ha using fun ab => (mem_range_baseToLaurent R (p ab)).mpr (hp ab)
    refine ⟨(seedBasis R r ι).repr.symm (Finsupp.equivFunOnFinite.symm a),?_⟩
    funext ab
    simpa only [globalCoordinates,LinearEquiv.apply_symm_apply,
      Finsupp.coe_equivFunOnFinite_symm] using ha ab

theorem localization_injective (r ι : R) (s : Finset (Fin 3)) :
    Function.Injective (algebraMap (SeedRing r ι) (SeedLocal R r ι s)) := by
  intro p q hpq
  apply globalCoordinates_injective R r ι
  funext ab
  have hh := congrArg (fun z => localizedCoordinates R r ι s z ab) hpq
  simpa only [localizedCoordinates_algebraMap,globalCoordinates] using hh

abbrev Sections (r ι : R) := (i : Fin 3) → SeedLocal R r ι {i}

def pairRestriction (r ι : R) (i j : Fin 3) :
    SeedLocal R r ι {i} →+* SeedLocal R r ι {i,j} :=
  restriction R r ι (by simp)

def secondPairRestriction (r ι : R) (i j : Fin 3) :
    SeedLocal R r ι {j} →+* SeedLocal R r ι {i,j} :=
  restriction R r ι (by simp)

def Compatible (r ι : R) (q : Sections R r ι) : Prop :=
  ∀ i j, pairRestriction R r ι i j (q i)=secondPairRestriction R r ι i j (q j)

theorem compatible_coordinates (r ι : R) (q : Sections R r ι)
    (hq : Compatible R r ι q) (i j : Fin 3) :
    localizedCoordinates R r ι {i} (q i)=localizedCoordinates R r ι {j} (q j) := by
  funext ab
  have hh := congrArg (fun z => localizedCoordinates R r ι {i,j} z ab) (hq i j)
  simpa only [pairRestriction,secondPairRestriction,coordinates_restriction] using hh

/-- The actual coordinate opens satisfy the augmented H0 gluing property. -/
theorem existsUnique_gluing (r ι : R) (q : Sections R r ι)
    (hq : Compatible R r ι q) :
    ∃! p : SeedRing r ι, ∀ i,
      algebraMap (SeedRing r ι) (SeedLocal R r ι {i}) p=q i := by
  let c := localizedCoordinates R r ι {0} (q 0)
  have hpoles (ab : ShiftIndex) : HasPoles ∅ (c ab) := by
    intro e i _ hi
    by_cases hi0 : i=0
    · subst i
      change (localizedCoordinates R r ι {0} (q 0) ab).coeff e=0
      rw [compatible_coordinates R r ι q hq 0 1]
      exact localizedCoordinates_hasPoles R r ι {1} (q 1) ab e 0 (by decide) hi
    · exact localizedCoordinates_hasPoles R r ι {0} (q 0) ab e i (by simpa using hi0) hi
  obtain ⟨p,hp⟩ := (mem_range_globalCoordinates R r ι c).mpr hpoles
  have hm (i : Fin 3) : algebraMap (SeedRing r ι) (SeedLocal R r ι {i}) p=q i := by
    apply localizedCoordinates_injective R r ι {i}
    funext ab
    rw [localizedCoordinates_algebraMap]
    change globalCoordinates R r ι p ab=_
    rw [hp]
    exact congrFun (compatible_coordinates R r ι q hq 0 i) ab
  refine ⟨p,hm,?_⟩
  intro p' hp'
  exact localization_injective R r ι {0} ((hp' 0).trans (hm 0).symm)

/-- Grading is inherited by the glued quotient class from any chart. -/
theorem gluing_preserves_grade (r ι : R) (q : Sections R r ι) (p : SeedRing r ι)
    (hp : ∀ i, algebraMap (SeedRing r ι) (SeedLocal R r ι {i}) p=q i)
    (g : LaurentGrade) (hg : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0} (q 0) ab)) :
    ∀ ab, HasGrade ab g (globalCoordinates R r ι p ab) := by
  intro ab
  have hh := congrArg (fun z => localizedCoordinates R r ι {0} z ab) (hp 0)
  rw [localizedCoordinates_algebraMap] at hh
  change HasGrade ab g (baseToLaurent R ((seedBasis R r ι).repr p ab))
  rw [hh]
  exact hg ab

/-- Compatible graded local sections have an actual globally homogeneous
polynomial representative in the original five variables. -/
theorem exists_homogeneous_polynomial_gluing (r ι : R) (q : Sections R r ι)
    (hq : Compatible R r ι q) (g : LaurentGrade)
    (hg : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0} (q 0) ab)) :
    ∃ p : Poly R, FullStandard p ∧ SignedHomogeneous R p g ∧ ∀ i,
      algebraMap (SeedRing r ι) (SeedLocal R r ι {i})
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p)=q i := by
  obtain ⟨p,hp,_⟩ := existsUnique_gluing R r ι q hq
  obtain ⟨P,hP,hPg,hPp⟩ := exists_signed_homogeneous_representative R r ι p g
    (gluing_preserves_grade R r ι q p hp g hg)
  exact ⟨P,hP,hPg,by simpa only [hPp] using hp⟩

end CycleQ2SeedCechGlobalGluing

#print axioms CycleQ2SeedCechGlobalGluing.existsUnique_gluing
#print axioms CycleQ2SeedCechGlobalGluing.exists_homogeneous_polynomial_gluing
end
end


/- Component: continuation_3/SeedCyclicAction.lean -/
section
/-! The literal diagonal cubic-root action and its eigenvalue on every
polynomial of the actual degree/character grading. -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCyclicAction

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientGrading

variable {R : Type*} [CommRing R]

def actionValues (ζ : R) : Fin 5 → Poly R :=
  ![C (ζ^2)*X 0,C (ζ^2)*X 1,C ζ*X 2,X 3,X 4]

def polynomialAction (ζ : R) : Poly R →ₐ[R] Poly R := aeval (actionValues ζ)

@[simp] theorem polynomialAction_X (ζ : R) (i : Fin 5) :
    polynomialAction ζ (X i)=actionValues ζ i := aeval_X _ _

@[simp] theorem polynomialAction_C (ζ c : R) : polynomialAction ζ (C c)=C c := aeval_C _ _

def characterExponent (e : FullExponent) : ℕ := 2*e 0+2*e 1+e 2

theorem polynomialAction_monomial (ζ : R) (e : FullExponent) (c : R) :
    polynomialAction ζ (monomial e c)=C (ζ^characterExponent e)*monomial e c := by
  rw [polynomialAction,aeval_monomial,monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [actionValues,characterExponent,Fin.prod_univ_succ,Fin.prod_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,Matrix.head_cons,Matrix.tail_cons,
    mul_one,MvPolynomial.algebraMap_eq,map_pow,map_mul,mul_pow,pow_add,pow_mul]
  ring

theorem pow_eq_mod_three (ζ : R) (hζ : ζ^3=1) (n : ℕ) : ζ^n=ζ^(n%3) := by
  calc
    ζ^n=ζ^(n%3+3*(n/3)) := congrArg (fun k : ℕ => ζ^k) (Nat.mod_add_div n 3).symm
    _=ζ^(n%3) := by rw [pow_add,pow_mul,hζ,one_pow,mul_one]

theorem polynomialAction_homogeneous (ζ : R) (hζ : ζ^3=1)
    (p : Poly R) (d : ℕ) (ch : ZMod 3) (hp : HG p (d,ch)) :
    polynomialAction ζ p=C (ζ^ch.val)*p := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  conv_rhs => rw [p.as_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [polynomialAction_monomial]
  have hg := hp (mem_support_iff.mp he)
  rw [fullGrading_weight] at hg
  have hc : characterExponent e%3=ch.val := by
    simpa only [characterExponent,ZMod.val_natCast] using
      congrArg (fun g : ℕ × ZMod 3 => g.2.val) hg
  rw [pow_eq_mod_three ζ hζ,hc]

theorem polynomialAction_signedHomogeneous (ζ : R) (hζ : ζ^3=1)
    (p : Poly R) (g : CycleQ2SeedCechThreeOpen.LaurentGrade)
    (hp : SignedHomogeneous R p g) : polynomialAction ζ p=C (ζ^g.2.val)*p := by
  by_cases hz : p=0
  · simp [hz]
  · obtain ⟨e,he⟩ := exists_coeff_ne_zero hz
    have hg := hp e he
    have hh : HG p (Finsupp.weight fullGrading e) := by
      apply (signedHomogeneous_iff R p _).mp
      exact hg.symm ▸ hp
    have hact := polynomialAction_homogeneous ζ hζ p
      (Finsupp.weight fullGrading e).1 (Finsupp.weight fullGrading e).2 hh
    have hch : (Finsupp.weight fullGrading e).2=g.2 := congrArg Prod.snd hg
    simpa only [hch] using hact

theorem polynomialAction_smoothH (ζ : R) (hζ : ζ^3=1) (ι : R) :
    polynomialAction ζ (smoothH ι)=smoothH ι := by
  simpa using polynomialAction_homogeneous ζ hζ (smoothH ι) 3 0 (smoothH_homogeneous ι)

theorem polynomialAction_smoothF (ζ : R) (hζ : ζ^3=1) (r ι : R) :
    polynomialAction ζ (smoothF r ι)=smoothF r ι := by
  simpa using polynomialAction_homogeneous ζ hζ (smoothF r ι) 6 0 (smoothF_homogeneous r ι)

def seedAction (ζ : R) (hζ : ζ^3=1) (r ι : R) : SeedRing r ι →ₐ[R] SeedRing r ι :=
  Ideal.quotientMapₐ (equationsIdeal (smoothH ι) (smoothF r ι)) (polynomialAction ζ) (by
    apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl | ⟨rfl⟩
    · change polynomialAction ζ (smoothH ι) ∈ equationsIdeal (smoothH ι) (smoothF r ι)
      rw [polynomialAction_smoothH ζ hζ]
      exact Ideal.subset_span (by simp [equationsIdeal])
    · change polynomialAction ζ (smoothF r ι) ∈ equationsIdeal (smoothH ι) (smoothF r ι)
      rw [polynomialAction_smoothF ζ hζ]
      exact Ideal.subset_span (by simp [equationsIdeal]))

@[simp] theorem seedAction_mk (ζ : R) (hζ : ζ^3=1) (r ι : R) (p : Poly R) :
    seedAction ζ hζ r ι (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p)=
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (polynomialAction ζ p) := rfl

end CycleQ2SeedCyclicAction

#print axioms CycleQ2SeedCyclicAction.polynomialAction_homogeneous
#print axioms CycleQ2SeedCyclicAction.seedAction
end
end


/- Component: continuation_3/SeedLinkageModularData.lean -/
section
/-! Literal coefficients for the selected actual linkage-generator sections.
No rank assertion is trusted here; the separate check modules prove every
normal form and an explicit square inverse product in the ordinary kernel. -/

set_option maxRecDepth 100000

set_option Elab.async false

namespace CycleQ2SeedLinkageModularData

open CycleQ2SparseModularPolynomial CycleQ2CurveRestriction CycleQ2SeedLinkageSections

def seedH : Sparse := [((3,0,0,0,0),1),((1,2,0,0,0),1),((0,3,0,0,0),76),((0,0,3,0,0),1),((1,0,1,1,0),1),((0,1,1,1,0),1),((0,0,0,3,0),77)]

def seedG : Sparse := [((6,0,0,0,0),1),((0,0,6,0,0),1),((0,3,0,3,0),107),((0,0,0,0,3),1)]

def leftInput0 : Sparse := [((0,1,4,5,0),57),((2,0,2,4,1),1)]

def leftNormal0 : Sparse := [((0,1,4,5,0),57),((2,0,2,4,1),1)]

def leftH0 : Sparse := []

def leftG0 : Sparse := []

def leftInput1 : Sparse := [((0,1,7,2,0),57),((2,0,5,1,1),1)]

def leftNormal1 : Sparse := [((0,1,7,2,0),57),((2,0,5,1,1),1)]

def leftH1 : Sparse := []

def leftG1 : Sparse := []

def leftInput2 : Sparse := [((0,2,2,6,0),57),((2,1,0,5,1),1)]

def leftNormal2 : Sparse := [((0,2,2,6,0),57),((2,1,0,5,1),1)]

def leftH2 : Sparse := []

def leftG2 : Sparse := []

def leftInput3 : Sparse := [((0,2,5,3,0),57),((2,1,3,2,1),1)]

def leftNormal3 : Sparse := [((0,2,5,3,0),57),((2,1,3,2,1),1)]

def leftH3 : Sparse := []

def leftG3 : Sparse := []

def leftInput4 : Sparse := [((0,3,3,4,0),57),((2,2,1,3,1),1)]

def leftNormal4 : Sparse := [((0,3,3,4,0),57),((2,2,1,3,1),1)]

def leftH4 : Sparse := []

def leftG4 : Sparse := []

def leftInput5 : Sparse := [((0,3,6,1,0),57),((2,2,4,0,1),1)]

def leftNormal5 : Sparse := [((0,3,6,1,0),57),((2,2,4,0,1),1)]

def leftH5 : Sparse := []

def leftG5 : Sparse := []

def leftInput6 : Sparse := [((0,4,4,2,0),57),((2,3,2,1,1),1)]

def leftNormal6 : Sparse := [((0,4,4,2,0),57),((2,3,2,1,1),1)]

def leftH6 : Sparse := []

def leftG6 : Sparse := []

def leftInput7 : Sparse := [((0,5,2,3,0),57),((2,4,0,2,1),1)]

def leftNormal7 : Sparse := [((0,5,2,3,0),57),((2,4,0,2,1),1)]

def leftH7 : Sparse := []

def leftG7 : Sparse := []

def leftInput8 : Sparse := [((0,6,3,1,0),57),((2,5,1,0,1),1)]

def leftNormal8 : Sparse := [((0,6,3,1,0),57),((2,5,1,0,1),1)]

def leftH8 : Sparse := []

def leftG8 : Sparse := []

def leftInput9 : Sparse := [((0,1,4,3,1),57),((2,0,2,2,2),1)]

def leftNormal9 : Sparse := [((0,1,4,3,1),57),((2,0,2,2,2),1)]

def leftH9 : Sparse := []

def leftG9 : Sparse := []

def leftInput10 : Sparse := [((0,2,2,4,1),57),((2,1,0,3,2),1)]

def leftNormal10 : Sparse := [((0,2,2,4,1),57),((2,1,0,3,2),1)]

def leftH10 : Sparse := []

def leftG10 : Sparse := []

def leftInput11 : Sparse := [((0,2,5,1,1),57),((2,1,3,0,2),1)]

def leftNormal11 : Sparse := [((0,2,5,1,1),57),((2,1,3,0,2),1)]

def leftH11 : Sparse := []

def leftG11 : Sparse := []

def leftInput12 : Sparse := [((0,3,3,2,1),57),((2,2,1,1,2),1)]

def leftNormal12 : Sparse := [((0,3,3,2,1),57),((2,2,1,1,2),1)]

def leftH12 : Sparse := []

def leftG12 : Sparse := []

def leftInput13 : Sparse := [((0,5,2,1,1),57),((2,4,0,0,2),1)]

def leftNormal13 : Sparse := [((0,5,2,1,1),57),((2,4,0,0,2),1)]

def leftH13 : Sparse := []

def leftG13 : Sparse := []

def leftInput14 : Sparse := [((0,1,4,1,2),57),((2,0,2,0,3),1)]

def leftNormal14 : Sparse := [((2,6,2,0,0),2),((1,7,2,0,0),10),((0,8,2,0,0),107),((2,3,5,0,0),66),((1,4,5,0,0),3),((0,5,5,0,0),86),((2,0,8,0,0),107),((0,2,8,0,0),2),((2,4,3,1,0),69),((1,5,3,1,0),23),((0,6,3,1,0),84),((2,1,6,1,0),107),((1,2,6,1,0),6),((0,3,6,1,0),90),((0,0,9,1,0),2),((2,2,4,2,0),2),((1,3,4,2,0),16),((0,4,4,2,0),88),((1,0,7,2,0),3),((0,1,7,2,0),4),((2,3,2,3,0),70),((1,4,2,3,0),13),((0,5,2,3,0),82),((2,0,5,3,0),65),((1,1,5,3,0),3),((0,2,5,3,0),92),((2,1,3,4,0),64),((1,2,3,4,0),26),((0,3,3,4,0),63),((0,0,6,4,0),90),((1,0,4,5,0),13),((0,1,4,5,0),90),((2,0,2,6,0),66),((0,2,2,6,0),86),((0,0,3,7,0),86),((0,1,4,1,2),57)]

def leftH14 : Sparse := [((5,0,2,0,0),108),((3,2,2,0,0),1),((2,3,2,0,0),76),((1,4,2,0,0),108),((0,5,2,0,0),66),((2,0,5,0,0),1),((0,2,5,0,0),107),((3,0,3,1,0),1),((2,1,3,1,0),1),((1,2,3,1,0),107),((0,3,3,1,0),64),((0,0,6,1,0),107),((1,0,4,2,0),108),((0,1,4,2,0),107),((2,0,2,3,0),77),((0,2,2,3,0),64),((0,0,3,4,0),64)]

def leftG14 : Sparse := [((2,0,2,0,0),1)]

def leftInput15 : Sparse := [((0,2,2,2,2),57),((2,1,0,1,3),1)]

def leftNormal15 : Sparse := [((2,7,0,1,0),2),((1,8,0,1,0),10),((0,9,0,1,0),107),((2,4,3,1,0),66),((1,5,3,1,0),3),((0,6,3,1,0),86),((2,1,6,1,0),107),((0,3,6,1,0),2),((2,5,1,2,0),69),((1,6,1,2,0),23),((0,7,1,2,0),84),((2,2,4,2,0),107),((1,3,4,2,0),6),((0,4,4,2,0),90),((0,1,7,2,0),2),((2,3,2,3,0),2),((1,4,2,3,0),16),((0,5,2,3,0),88),((1,1,5,3,0),3),((0,2,5,3,0),4),((2,4,0,4,0),70),((1,5,0,4,0),13),((0,6,0,4,0),82),((2,1,3,4,0),65),((1,2,3,4,0),3),((0,3,3,4,0),92),((2,2,1,5,0),64),((1,3,1,5,0),26),((0,4,1,5,0),63),((0,1,4,5,0),90),((1,1,2,6,0),13),((0,2,2,6,0),90),((2,1,0,7,0),66),((0,3,0,7,0),86),((0,1,1,8,0),86),((0,2,2,2,2),57)]

def leftH15 : Sparse := [((5,1,0,1,0),108),((3,3,0,1,0),1),((2,4,0,1,0),76),((1,5,0,1,0),108),((0,6,0,1,0),66),((2,1,3,1,0),1),((0,3,3,1,0),107),((3,1,1,2,0),1),((2,2,1,2,0),1),((1,3,1,2,0),107),((0,4,1,2,0),64),((0,1,4,2,0),107),((1,1,2,3,0),108),((0,2,2,3,0),107),((2,1,0,4,0),77),((0,3,0,4,0),64),((0,1,1,5,0),64)]

def leftG15 : Sparse := [((2,1,0,1,0),1)]

def leftInput16 : Sparse := [((1,1,2,6,0),57),((3,0,0,5,1),1)]

def leftNormal16 : Sparse := [((1,1,2,6,0),57),((1,2,0,5,1),108),((0,3,0,5,1),33),((0,0,3,5,1),108),((1,0,1,6,1),108),((0,1,1,6,1),108),((0,0,0,8,1),32)]

def leftH16 : Sparse := [((0,0,0,5,1),1)]

def leftG16 : Sparse := []

def leftInput17 : Sparse := [((1,1,5,3,0),57),((3,0,3,2,1),1)]

def leftNormal17 : Sparse := [((1,1,5,3,0),57),((1,2,3,2,1),108),((0,3,3,2,1),33),((0,0,6,2,1),108),((1,0,4,3,1),108),((0,1,4,3,1),108),((0,0,3,5,1),32)]

def leftH17 : Sparse := [((0,0,3,2,1),1)]

def leftG17 : Sparse := []

def leftInput18 : Sparse := [((1,2,3,4,0),57),((3,1,1,3,1),1)]

def leftNormal18 : Sparse := [((1,2,3,4,0),57),((1,3,1,3,1),108),((0,4,1,3,1),33),((0,1,4,3,1),108),((1,1,2,4,1),108),((0,2,2,4,1),108),((0,1,1,6,1),32)]

def leftH18 : Sparse := [((0,1,1,3,1),1)]

def leftG18 : Sparse := []

def leftInput19 : Sparse := [((1,2,6,1,0),57),((3,1,4,0,1),1)]

def leftNormal19 : Sparse := [((1,2,6,1,0),57),((1,3,4,0,1),108),((0,4,4,0,1),33),((0,1,7,0,1),108),((1,1,5,1,1),108),((0,2,5,1,1),108),((0,1,4,3,1),32)]

def leftH19 : Sparse := [((0,1,4,0,1),1)]

def leftG19 : Sparse := []

def leftInput20 : Sparse := [((1,3,4,2,0),57),((3,2,2,1,1),1)]

def leftNormal20 : Sparse := [((1,3,4,2,0),57),((1,4,2,1,1),108),((0,5,2,1,1),33),((0,2,5,1,1),108),((1,2,3,2,1),108),((0,3,3,2,1),108),((0,2,2,4,1),32)]

def leftH20 : Sparse := [((0,2,2,1,1),1)]

def leftG20 : Sparse := []

def leftInput21 : Sparse := [((1,4,2,3,0),57),((3,3,0,2,1),1)]

def leftNormal21 : Sparse := [((1,4,2,3,0),57),((1,5,0,2,1),108),((0,6,0,2,1),33),((0,3,3,2,1),108),((1,3,1,3,1),108),((0,4,1,3,1),108),((0,3,0,5,1),32)]

def leftH21 : Sparse := [((0,3,0,2,1),1)]

def leftG21 : Sparse := []

def leftInput22 : Sparse := [((1,5,3,1,0),57),((3,4,1,0,1),1)]

def leftNormal22 : Sparse := [((1,5,3,1,0),57),((1,6,1,0,1),108),((0,7,1,0,1),33),((0,4,4,0,1),108),((1,4,2,1,1),108),((0,5,2,1,1),108),((0,4,1,3,1),32)]

def leftH22 : Sparse := [((0,4,1,0,1),1)]

def leftG22 : Sparse := []

def leftInput23 : Sparse := [((1,1,2,4,1),57),((3,0,0,3,2),1)]

def leftNormal23 : Sparse := [((1,1,2,4,1),57),((1,2,0,3,2),108),((0,3,0,3,2),33),((0,0,3,3,2),108),((1,0,1,4,2),108),((0,1,1,4,2),108),((0,0,0,6,2),32)]

def leftH23 : Sparse := [((0,0,0,3,2),1)]

def leftG23 : Sparse := []

def leftInput24 : Sparse := [((1,1,5,1,1),57),((3,0,3,0,2),1)]

def leftNormal24 : Sparse := [((1,1,5,1,1),57),((1,2,3,0,2),108),((0,3,3,0,2),33),((0,0,6,0,2),108),((1,0,4,1,2),108),((0,1,4,1,2),108),((0,0,3,3,2),32)]

def leftH24 : Sparse := [((0,0,3,0,2),1)]

def leftG24 : Sparse := []

def leftInput25 : Sparse := [((1,2,3,2,1),57),((3,1,1,1,2),1)]

def leftNormal25 : Sparse := [((1,2,3,2,1),57),((1,3,1,1,2),108),((0,4,1,1,2),33),((0,1,4,1,2),108),((1,1,2,2,2),108),((0,2,2,2,2),108),((0,1,1,4,2),32)]

def leftH25 : Sparse := [((0,1,1,1,2),1)]

def leftG25 : Sparse := []

def leftInput26 : Sparse := [((1,4,2,1,1),57),((3,3,0,0,2),1)]

def leftNormal26 : Sparse := [((1,4,2,1,1),57),((1,5,0,0,2),108),((0,6,0,0,2),33),((0,3,3,0,2),108),((1,3,1,1,2),108),((0,4,1,1,2),108),((0,3,0,3,2),32)]

def leftH26 : Sparse := [((0,3,0,0,2),1)]

def leftG26 : Sparse := []

def leftInput27 : Sparse := [((1,1,2,2,2),57),((3,0,0,1,3),1)]

def leftNormal27 : Sparse := [((2,7,0,1,0),10),((1,8,0,1,0),105),((0,9,0,1,0),66),((2,4,3,1,0),3),((1,5,3,1,0),20),((0,6,3,1,0),105),((1,2,6,1,0),4),((0,3,6,1,0),86),((0,0,9,1,0),2),((2,5,1,2,0),23),((1,6,1,2,0),13),((0,7,1,2,0),95),((2,2,4,2,0),6),((1,3,4,2,0),26),((0,4,4,2,0),17),((1,0,7,2,0),4),((0,1,7,2,0),4),((2,3,2,3,0),16),((1,4,2,3,0),17),((0,5,2,3,0),106),((2,0,5,3,0),3),((1,1,5,3,0),6),((2,4,0,4,0),13),((1,5,0,4,0),12),((0,6,0,4,0),85),((2,1,3,4,0),3),((1,2,3,4,0),25),((0,3,3,4,0),43),((0,0,6,4,0),89),((2,2,1,5,0),26),((1,3,1,5,0),38),((0,4,1,5,0),108),((1,0,4,5,0),25),((0,1,4,5,0),25),((2,0,2,6,0),13),((1,1,2,6,0),26),((1,2,0,7,0),20),((0,3,0,7,0),58),((0,0,3,7,0),52),((1,0,1,8,0),20),((0,1,1,8,0),20),((0,0,0,10,0),41),((1,1,2,2,2),57)]

def leftH27 : Sparse := [((4,2,0,1,0),1),((3,3,0,1,0),76),((2,4,0,1,0),108),((1,5,0,1,0),66),((0,6,0,1,0),2),((3,0,3,1,0),1),((1,2,3,1,0),107),((0,3,3,1,0),66),((0,0,6,1,0),108),((4,0,1,2,0),1),((3,1,1,2,0),1),((2,2,1,2,0),107),((1,3,1,2,0),64),((0,4,1,2,0),69),((1,0,4,2,0),107),((0,1,4,2,0),107),((2,0,2,3,0),108),((1,1,2,3,0),107),((0,2,2,3,0),2),((3,0,0,4,0),77),((1,2,0,4,0),64),((0,3,0,4,0),68),((0,0,3,4,0),65),((1,0,1,5,0),64),((0,1,1,5,0),64),((0,0,0,7,0),66),((0,0,0,1,3),1)]

def leftG27 : Sparse := [((1,2,0,1,0),108),((0,3,0,1,0),33),((0,0,3,1,0),108),((1,0,1,2,0),108),((0,1,1,2,0),108),((0,0,0,4,0),32)]

def leftInput28 : Sparse := [((2,1,3,4,0),57),((4,0,1,3,1),1)]

def leftNormal28 : Sparse := [((2,1,3,4,0),57),((2,2,1,3,1),108),((1,3,1,3,1),33),((1,0,4,3,1),108),((2,0,2,4,1),108),((1,1,2,4,1),108),((1,0,1,6,1),32)]

def leftH28 : Sparse := [((1,0,1,3,1),1)]

def leftG28 : Sparse := []

def leftInput29 : Sparse := [((2,1,6,1,0),57),((4,0,4,0,1),1)]

def leftNormal29 : Sparse := [((2,1,6,1,0),57),((2,2,4,0,1),108),((1,3,4,0,1),33),((1,0,7,0,1),108),((2,0,5,1,1),108),((1,1,5,1,1),108),((1,0,4,3,1),32)]

def leftH29 : Sparse := [((1,0,4,0,1),1)]

def leftG29 : Sparse := []

def leftInput30 : Sparse := [((2,2,4,2,0),57),((4,1,2,1,1),1)]

def leftNormal30 : Sparse := [((2,2,4,2,0),57),((2,3,2,1,1),108),((1,4,2,1,1),33),((1,1,5,1,1),108),((2,1,3,2,1),108),((1,2,3,2,1),108),((1,1,2,4,1),32)]

def leftH30 : Sparse := [((1,1,2,1,1),1)]

def leftG30 : Sparse := []

def leftInput31 : Sparse := [((2,3,2,3,0),57),((4,2,0,2,1),1)]

def leftNormal31 : Sparse := [((2,3,2,3,0),57),((2,4,0,2,1),108),((1,5,0,2,1),33),((1,2,3,2,1),108),((2,2,1,3,1),108),((1,3,1,3,1),108),((1,2,0,5,1),32)]

def leftH31 : Sparse := [((1,2,0,2,1),1)]

def leftG31 : Sparse := []

def leftInput32 : Sparse := [((2,4,3,1,0),57),((4,3,1,0,1),1)]

def leftNormal32 : Sparse := [((2,4,3,1,0),57),((2,5,1,0,1),108),((1,6,1,0,1),33),((1,3,4,0,1),108),((2,3,2,1,1),108),((1,4,2,1,1),108),((1,3,1,3,1),32)]

def leftH32 : Sparse := [((1,3,1,0,1),1)]

def leftG32 : Sparse := []

def leftInput33 : Sparse := [((2,1,3,2,1),57),((4,0,1,1,2),1)]

def leftNormal33 : Sparse := [((2,1,3,2,1),57),((2,2,1,1,2),108),((1,3,1,1,2),33),((1,0,4,1,2),108),((2,0,2,2,2),108),((1,1,2,2,2),108),((1,0,1,4,2),32)]

def leftH33 : Sparse := [((1,0,1,1,2),1)]

def leftG33 : Sparse := []

def leftInput34 : Sparse := [((2,3,2,1,1),57),((4,2,0,0,2),1)]

def leftNormal34 : Sparse := [((2,3,2,1,1),57),((2,4,0,0,2),108),((1,5,0,0,2),33),((1,2,3,0,2),108),((2,2,1,1,2),108),((1,3,1,1,2),108),((1,2,0,3,2),32)]

def leftH34 : Sparse := [((1,2,0,0,2),1)]

def leftG34 : Sparse := []

def leftInput35 : Sparse := [((6,0,0,4,0),1),((0,3,0,7,0),107)]

def leftNormal35 : Sparse := [((2,4,0,4,0),1),((1,5,0,4,0),43),((0,6,0,4,0),108),((1,2,3,4,0),2),((0,3,3,4,0),43),((0,0,6,4,0),1),((2,2,1,5,0),2),((1,3,1,5,0),45),((0,4,1,5,0),43),((1,0,4,5,0),2),((0,1,4,5,0),2),((2,0,2,6,0),1),((1,1,2,6,0),2),((0,2,2,6,0),1),((1,2,0,7,0),45),((0,3,0,7,0),39),((0,0,3,7,0),45),((1,0,1,8,0),45),((0,1,1,8,0),45),((0,0,0,10,0),43)]

def leftH35 : Sparse := [((3,0,0,4,0),1),((1,2,0,4,0),108),((0,3,0,4,0),33),((0,0,3,4,0),108),((1,0,1,5,0),108),((0,1,1,5,0),108),((0,0,0,7,0),32)]

def leftG35 : Sparse := []

def leftInput36 : Sparse := [((6,0,3,1,0),1),((0,3,3,4,0),107)]

def leftNormal36 : Sparse := [((2,4,3,1,0),1),((1,5,3,1,0),43),((0,6,3,1,0),108),((1,2,6,1,0),2),((0,3,6,1,0),43),((0,0,9,1,0),1),((2,2,4,2,0),2),((1,3,4,2,0),45),((0,4,4,2,0),43),((1,0,7,2,0),2),((0,1,7,2,0),2),((2,0,5,3,0),1),((1,1,5,3,0),2),((0,2,5,3,0),1),((1,2,3,4,0),45),((0,3,3,4,0),39),((0,0,6,4,0),45),((1,0,4,5,0),45),((0,1,4,5,0),45),((0,0,3,7,0),43)]

def leftH36 : Sparse := [((3,0,3,1,0),1),((1,2,3,1,0),108),((0,3,3,1,0),33),((0,0,6,1,0),108),((1,0,4,2,0),108),((0,1,4,2,0),108),((0,0,3,4,0),32)]

def leftG36 : Sparse := []

def leftInput37 : Sparse := [((6,1,1,2,0),1),((0,4,1,5,0),107)]

def leftNormal37 : Sparse := [((2,5,1,2,0),1),((1,6,1,2,0),43),((0,7,1,2,0),108),((1,3,4,2,0),2),((0,4,4,2,0),43),((0,1,7,2,0),1),((2,3,2,3,0),2),((1,4,2,3,0),45),((0,5,2,3,0),43),((1,1,5,3,0),2),((0,2,5,3,0),2),((2,1,3,4,0),1),((1,2,3,4,0),2),((0,3,3,4,0),1),((1,3,1,5,0),45),((0,4,1,5,0),39),((0,1,4,5,0),45),((1,1,2,6,0),45),((0,2,2,6,0),45),((0,1,1,8,0),43)]

def leftH37 : Sparse := [((3,1,1,2,0),1),((1,3,1,2,0),108),((0,4,1,2,0),33),((0,1,4,2,0),108),((1,1,2,3,0),108),((0,2,2,3,0),108),((0,1,1,5,0),32)]

def leftG37 : Sparse := []

def leftInput38 : Sparse := [((6,2,2,0,0),1),((0,5,2,3,0),107)]

def leftNormal38 : Sparse := [((2,6,2,0,0),1),((1,7,2,0,0),43),((0,8,2,0,0),108),((1,4,5,0,0),2),((0,5,5,0,0),43),((0,2,8,0,0),1),((2,4,3,1,0),2),((1,5,3,1,0),45),((0,6,3,1,0),43),((1,2,6,1,0),2),((0,3,6,1,0),2),((2,2,4,2,0),1),((1,3,4,2,0),2),((0,4,4,2,0),1),((1,4,2,3,0),45),((0,5,2,3,0),39),((0,2,5,3,0),45),((1,2,3,4,0),45),((0,3,3,4,0),45),((0,2,2,6,0),43)]

def leftH38 : Sparse := [((3,2,2,0,0),1),((1,4,2,0,0),108),((0,5,2,0,0),33),((0,2,5,0,0),108),((1,2,3,1,0),108),((0,3,3,1,0),108),((0,2,2,3,0),32)]

def leftG38 : Sparse := []

def leftInput39 : Sparse := [((6,3,0,1,0),1),((0,6,0,4,0),107)]

def leftNormal39 : Sparse := [((2,7,0,1,0),1),((1,8,0,1,0),43),((0,9,0,1,0),108),((1,5,3,1,0),2),((0,6,3,1,0),43),((0,3,6,1,0),1),((2,5,1,2,0),2),((1,6,1,2,0),45),((0,7,1,2,0),43),((1,3,4,2,0),2),((0,4,4,2,0),2),((2,3,2,3,0),1),((1,4,2,3,0),2),((0,5,2,3,0),1),((1,5,0,4,0),45),((0,6,0,4,0),39),((0,3,3,4,0),45),((1,3,1,5,0),45),((0,4,1,5,0),45),((0,3,0,7,0),43)]

def leftH39 : Sparse := [((3,3,0,1,0),1),((1,5,0,1,0),108),((0,6,0,1,0),33),((0,3,3,1,0),108),((1,3,1,2,0),108),((0,4,1,2,0),108),((0,3,0,4,0),32)]

def leftG39 : Sparse := []

def leftInput40 : Sparse := [((6,0,0,2,1),1),((0,3,0,5,1),107)]

def leftNormal40 : Sparse := [((2,4,0,2,1),1),((1,5,0,2,1),43),((0,6,0,2,1),108),((1,2,3,2,1),2),((0,3,3,2,1),43),((0,0,6,2,1),1),((2,2,1,3,1),2),((1,3,1,3,1),45),((0,4,1,3,1),43),((1,0,4,3,1),2),((0,1,4,3,1),2),((2,0,2,4,1),1),((1,1,2,4,1),2),((0,2,2,4,1),1),((1,2,0,5,1),45),((0,3,0,5,1),39),((0,0,3,5,1),45),((1,0,1,6,1),45),((0,1,1,6,1),45),((0,0,0,8,1),43)]

def leftH40 : Sparse := [((3,0,0,2,1),1),((1,2,0,2,1),108),((0,3,0,2,1),33),((0,0,3,2,1),108),((1,0,1,3,1),108),((0,1,1,3,1),108),((0,0,0,5,1),32)]

def leftG40 : Sparse := []

def leftInput41 : Sparse := [((6,1,1,0,1),1),((0,4,1,3,1),107)]

def leftNormal41 : Sparse := [((2,5,1,0,1),1),((1,6,1,0,1),43),((0,7,1,0,1),108),((1,3,4,0,1),2),((0,4,4,0,1),43),((0,1,7,0,1),1),((2,3,2,1,1),2),((1,4,2,1,1),45),((0,5,2,1,1),43),((1,1,5,1,1),2),((0,2,5,1,1),2),((2,1,3,2,1),1),((1,2,3,2,1),2),((0,3,3,2,1),1),((1,3,1,3,1),45),((0,4,1,3,1),39),((0,1,4,3,1),45),((1,1,2,4,1),45),((0,2,2,4,1),45),((0,1,1,6,1),43)]

def leftH41 : Sparse := [((3,1,1,0,1),1),((1,3,1,0,1),108),((0,4,1,0,1),33),((0,1,4,0,1),108),((1,1,2,1,1),108),((0,2,2,1,1),108),((0,1,1,3,1),32)]

def leftG41 : Sparse := []

def leftInput42 : Sparse := [((6,0,0,0,2),1),((0,3,0,3,2),107)]

def leftNormal42 : Sparse := [((2,4,0,0,2),1),((1,5,0,0,2),43),((0,6,0,0,2),108),((1,2,3,0,2),2),((0,3,3,0,2),43),((0,0,6,0,2),1),((2,2,1,1,2),2),((1,3,1,1,2),45),((0,4,1,1,2),43),((1,0,4,1,2),2),((0,1,4,1,2),2),((2,0,2,2,2),1),((1,1,2,2,2),2),((0,2,2,2,2),1),((1,2,0,3,2),45),((0,3,0,3,2),39),((0,0,3,3,2),45),((1,0,1,4,2),45),((0,1,1,4,2),45),((0,0,0,6,2),43)]

def leftH42 : Sparse := [((3,0,0,0,2),1),((1,2,0,0,2),108),((0,3,0,0,2),33),((0,0,3,0,2),108),((1,0,1,1,2),108),((0,1,1,1,2),108),((0,0,0,3,2),32)]

def leftG42 : Sparse := []

def leftInput43 : Sparse := [((7,0,1,2,0),1),((1,3,1,5,0),107)]

def leftNormal43 : Sparse := [((2,5,1,2,0),43),((1,6,1,2,0),107),((0,7,1,2,0),33),((2,2,4,2,0),2),((1,3,4,2,0),43),((0,4,4,2,0),108),((1,0,7,2,0),1),((2,3,2,3,0),45),((1,4,2,3,0),40),((0,5,2,3,0),65),((2,0,5,3,0),2),((1,1,5,3,0),2),((0,2,5,3,0),107),((2,1,3,4,0),2),((1,2,3,4,0),107),((0,3,3,4,0),31),((0,0,6,4,0),108),((2,2,1,5,0),45),((1,3,1,5,0),39),((0,4,1,5,0),32),((1,0,4,5,0),44),((0,1,4,5,0),108),((2,0,2,6,0),45),((1,1,2,6,0),45),((0,2,2,6,0),64),((0,0,3,7,0),32),((1,0,1,8,0),43)]

def leftH43 : Sparse := [((4,0,1,2,0),1),((2,2,1,2,0),108),((1,3,1,2,0),33),((0,4,1,2,0),1),((1,0,4,2,0),108),((2,0,2,3,0),108),((1,1,2,3,0),108),((0,2,2,3,0),2),((0,0,3,4,0),1),((1,0,1,5,0),32)]

def leftG43 : Sparse := []

def leftInput44 : Sparse := [((7,1,2,0,0),1),((1,4,2,3,0),107)]

def leftNormal44 : Sparse := [((2,6,2,0,0),43),((1,7,2,0,0),107),((0,8,2,0,0),33),((2,3,5,0,0),2),((1,4,5,0,0),43),((0,5,5,0,0),108),((1,1,8,0,0),1),((2,4,3,1,0),45),((1,5,3,1,0),40),((0,6,3,1,0),65),((2,1,6,1,0),2),((1,2,6,1,0),2),((0,3,6,1,0),107),((2,2,4,2,0),2),((1,3,4,2,0),107),((0,4,4,2,0),31),((0,1,7,2,0),108),((2,3,2,3,0),45),((1,4,2,3,0),39),((0,5,2,3,0),32),((1,1,5,3,0),44),((0,2,5,3,0),108),((2,1,3,4,0),45),((1,2,3,4,0),45),((0,3,3,4,0),64),((0,1,4,5,0),32),((1,1,2,6,0),43)]

def leftH44 : Sparse := [((4,1,2,0,0),1),((2,3,2,0,0),108),((1,4,2,0,0),33),((0,5,2,0,0),1),((1,1,5,0,0),108),((2,1,3,1,0),108),((1,2,3,1,0),108),((0,3,3,1,0),2),((0,1,4,2,0),1),((1,1,2,3,0),32)]

def leftG44 : Sparse := []

def leftInput45 : Sparse := [((7,2,0,1,0),1),((1,5,0,4,0),107)]

def leftNormal45 : Sparse := [((2,7,0,1,0),43),((1,8,0,1,0),107),((0,9,0,1,0),33),((2,4,3,1,0),2),((1,5,3,1,0),43),((0,6,3,1,0),108),((1,2,6,1,0),1),((2,5,1,2,0),45),((1,6,1,2,0),40),((0,7,1,2,0),65),((2,2,4,2,0),2),((1,3,4,2,0),2),((0,4,4,2,0),107),((2,3,2,3,0),2),((1,4,2,3,0),107),((0,5,2,3,0),31),((0,2,5,3,0),108),((2,4,0,4,0),45),((1,5,0,4,0),39),((0,6,0,4,0),32),((1,2,3,4,0),44),((0,3,3,4,0),108),((2,2,1,5,0),45),((1,3,1,5,0),45),((0,4,1,5,0),64),((0,2,2,6,0),32),((1,2,0,7,0),43)]

def leftH45 : Sparse := [((4,2,0,1,0),1),((2,4,0,1,0),108),((1,5,0,1,0),33),((0,6,0,1,0),1),((1,2,3,1,0),108),((2,2,1,2,0),108),((1,3,1,2,0),108),((0,4,1,2,0),2),((0,2,2,3,0),1),((1,2,0,4,0),32)]

def leftG45 : Sparse := []

def leftInput46 : Sparse := [((7,0,1,0,1),1),((1,3,1,3,1),107)]

def leftNormal46 : Sparse := [((2,5,1,0,1),43),((1,6,1,0,1),107),((0,7,1,0,1),33),((2,2,4,0,1),2),((1,3,4,0,1),43),((0,4,4,0,1),108),((1,0,7,0,1),1),((2,3,2,1,1),45),((1,4,2,1,1),40),((0,5,2,1,1),65),((2,0,5,1,1),2),((1,1,5,1,1),2),((0,2,5,1,1),107),((2,1,3,2,1),2),((1,2,3,2,1),107),((0,3,3,2,1),31),((0,0,6,2,1),108),((2,2,1,3,1),45),((1,3,1,3,1),39),((0,4,1,3,1),32),((1,0,4,3,1),44),((0,1,4,3,1),108),((2,0,2,4,1),45),((1,1,2,4,1),45),((0,2,2,4,1),64),((0,0,3,5,1),32),((1,0,1,6,1),43)]

def leftH46 : Sparse := [((4,0,1,0,1),1),((2,2,1,0,1),108),((1,3,1,0,1),33),((0,4,1,0,1),1),((1,0,4,0,1),108),((2,0,2,1,1),108),((1,1,2,1,1),108),((0,2,2,1,1),2),((0,0,3,2,1),1),((1,0,1,3,1),32)]

def leftG46 : Sparse := []

def leftInput47 : Sparse := [((8,0,2,0,0),1),((2,3,2,3,0),107)]

def leftNormal47 : Sparse := [((2,6,2,0,0),107),((1,7,2,0,0),99),((0,8,2,0,0),2),((2,3,5,0,0),43),((1,4,5,0,0),106),((0,5,5,0,0),23),((2,0,8,0,0),1),((0,2,8,0,0),107),((2,4,3,1,0),40),((1,5,3,1,0),86),((0,6,3,1,0),25),((2,1,6,1,0),2),((1,2,6,1,0),103),((0,3,6,1,0),19),((0,0,9,1,0),107),((2,2,4,2,0),107),((1,3,4,2,0),93),((0,4,4,2,0),21),((1,0,7,2,0),106),((0,1,7,2,0),105),((2,3,2,3,0),39),((1,4,2,3,0),96),((0,5,2,3,0),27),((2,0,5,3,0),44),((1,1,5,3,0),106),((0,2,5,3,0),17),((2,1,3,4,0),45),((1,2,3,4,0),83),((0,3,3,4,0),46),((0,0,6,4,0),19),((1,0,4,5,0),96),((0,1,4,5,0),19),((2,0,2,6,0),43),((0,2,2,6,0),23),((0,0,3,7,0),23)]

def leftH47 : Sparse := [((5,0,2,0,0),1),((3,2,2,0,0),108),((2,3,2,0,0),33),((1,4,2,0,0),1),((0,5,2,0,0),43),((2,0,5,0,0),108),((0,2,5,0,0),2),((3,0,3,1,0),108),((2,1,3,1,0),108),((1,2,3,1,0),2),((0,3,3,1,0),45),((0,0,6,1,0),2),((1,0,4,2,0),1),((0,1,4,2,0),2),((2,0,2,3,0),32),((0,2,2,3,0),45),((0,0,3,4,0),45)]

def leftG47 : Sparse := []

def leftInput48 : Sparse := [((8,1,0,1,0),1),((2,4,0,4,0),107)]

def leftNormal48 : Sparse := [((2,7,0,1,0),107),((1,8,0,1,0),99),((0,9,0,1,0),2),((2,4,3,1,0),43),((1,5,3,1,0),106),((0,6,3,1,0),23),((2,1,6,1,0),1),((0,3,6,1,0),107),((2,5,1,2,0),40),((1,6,1,2,0),86),((0,7,1,2,0),25),((2,2,4,2,0),2),((1,3,4,2,0),103),((0,4,4,2,0),19),((0,1,7,2,0),107),((2,3,2,3,0),107),((1,4,2,3,0),93),((0,5,2,3,0),21),((1,1,5,3,0),106),((0,2,5,3,0),105),((2,4,0,4,0),39),((1,5,0,4,0),96),((0,6,0,4,0),27),((2,1,3,4,0),44),((1,2,3,4,0),106),((0,3,3,4,0),17),((2,2,1,5,0),45),((1,3,1,5,0),83),((0,4,1,5,0),46),((0,1,4,5,0),19),((1,1,2,6,0),96),((0,2,2,6,0),19),((2,1,0,7,0),43),((0,3,0,7,0),23),((0,1,1,8,0),23)]

def leftH48 : Sparse := [((5,1,0,1,0),1),((3,3,0,1,0),108),((2,4,0,1,0),33),((1,5,0,1,0),1),((0,6,0,1,0),43),((2,1,3,1,0),108),((0,3,3,1,0),2),((3,1,1,2,0),108),((2,2,1,2,0),108),((1,3,1,2,0),2),((0,4,1,2,0),45),((0,1,4,2,0),2),((1,1,2,3,0),1),((0,2,2,3,0),2),((2,1,0,4,0),32),((0,3,0,4,0),45),((0,1,1,5,0),45)]

def leftG48 : Sparse := []

def leftInput49 : Sparse := [((4,0,4,2,0),1),((0,2,2,4,1),88)]

def leftNormal49 : Sparse := [((2,2,4,2,0),108),((1,3,4,2,0),33),((1,0,7,2,0),108),((2,0,5,3,0),108),((1,1,5,3,0),108),((1,0,4,5,0),32),((0,2,2,4,1),88)]

def leftH49 : Sparse := [((1,0,4,2,0),1)]

def leftG49 : Sparse := []

def leftInput50 : Sparse := [((4,1,5,0,0),1),((0,3,3,2,1),88)]

def leftNormal50 : Sparse := [((2,3,5,0,0),108),((1,4,5,0,0),33),((1,1,8,0,0),108),((2,1,6,1,0),108),((1,2,6,1,0),108),((1,1,5,3,0),32),((0,3,3,2,1),88)]

def leftH50 : Sparse := [((1,1,5,0,0),1)]

def leftG50 : Sparse := []

def leftInput51 : Sparse := [((4,4,2,0,0),1),((0,6,0,2,1),88)]

def leftNormal51 : Sparse := [((2,6,2,0,0),108),((1,7,2,0,0),33),((1,4,5,0,0),108),((2,4,3,1,0),108),((1,5,3,1,0),108),((1,4,2,3,0),32),((0,6,0,2,1),88)]

def leftH51 : Sparse := [((1,4,2,0,0),1)]

def leftG51 : Sparse := []

def leftInput52 : Sparse := [((5,0,2,3,0),1),((1,2,0,5,1),88)]

def leftNormal52 : Sparse := [((2,3,2,3,0),33),((1,4,2,3,0),1),((0,5,2,3,0),76),((2,0,5,3,0),108),((0,2,5,3,0),1),((2,1,3,4,0),108),((1,2,3,4,0),2),((0,3,3,4,0),77),((0,0,6,4,0),1),((1,0,4,5,0),1),((0,1,4,5,0),1),((2,0,2,6,0),32),((0,2,2,6,0),77),((0,0,3,7,0),77),((1,2,0,5,1),88)]

def leftH52 : Sparse := [((2,0,2,3,0),1),((0,2,2,3,0),108),((0,0,3,4,0),108)]

def leftG52 : Sparse := []

def leftInput53 : Sparse := [((5,0,2,1,1),1),((1,2,0,3,2),88)]

def leftNormal53 : Sparse := [((2,3,2,1,1),33),((1,4,2,1,1),1),((0,5,2,1,1),76),((2,0,5,1,1),108),((0,2,5,1,1),1),((2,1,3,2,1),108),((1,2,3,2,1),2),((0,3,3,2,1),77),((0,0,6,2,1),1),((1,0,4,3,1),1),((0,1,4,3,1),1),((2,0,2,4,1),32),((0,2,2,4,1),77),((0,0,3,5,1),77),((1,2,0,3,2),88)]

def leftH53 : Sparse := [((2,0,2,1,1),1),((0,2,2,1,1),108),((0,0,3,2,1),108)]

def leftG53 : Sparse := []

def leftInput54 : Sparse := [((2,0,5,3,0),1),((0,1,1,4,2),52)]

def leftNormal54 : Sparse := [((2,0,5,3,0),1),((0,1,1,4,2),52)]

def leftH54 : Sparse := []

def leftG54 : Sparse := []

def leftInput55 : Sparse := [((2,3,5,0,0),1),((0,4,1,1,2),52)]

def leftNormal55 : Sparse := [((2,3,5,0,0),1),((0,4,1,1,2),52)]

def leftH55 : Sparse := []

def leftG55 : Sparse := []

def leftColumns : Fin 56 → SectionColumn := ![(0,(0,0,2,4,0)),(0,(0,0,5,1,0)),(0,(0,1,0,5,0)),(0,(0,1,3,2,0)),(0,(0,2,1,3,0)),(0,(0,2,4,0,0)),(0,(0,3,2,1,0)),(0,(0,4,0,2,0)),(0,(0,5,1,0,0)),(0,(0,0,2,2,1)),(0,(0,1,0,3,1)),(0,(0,1,3,0,1)),(0,(0,2,1,1,1)),(0,(0,4,0,0,1)),(0,(0,0,2,0,2)),(0,(0,1,0,1,2)),(0,(1,0,0,5,0)),(0,(1,0,3,2,0)),(0,(1,1,1,3,0)),(0,(1,1,4,0,0)),(0,(1,2,2,1,0)),(0,(1,3,0,2,0)),(0,(1,4,1,0,0)),(0,(1,0,0,3,1)),(0,(1,0,3,0,1)),(0,(1,1,1,1,1)),(0,(1,3,0,0,1)),(0,(1,0,0,1,2)),(0,(2,0,1,3,0)),(0,(2,0,4,0,0)),(0,(2,1,2,1,0)),(0,(2,2,0,2,0)),(0,(2,3,1,0,0)),(0,(2,0,1,1,1)),(0,(2,2,0,0,1)),(1,(0,0,0,4,0)),(1,(0,0,3,1,0)),(1,(0,1,1,2,0)),(1,(0,2,2,0,0)),(1,(0,3,0,1,0)),(1,(0,0,0,2,1)),(1,(0,1,1,0,1)),(1,(0,0,0,0,2)),(1,(1,0,1,2,0)),(1,(1,1,2,0,0)),(1,(1,2,0,1,0)),(1,(1,0,1,0,1)),(1,(2,0,2,0,0)),(1,(2,1,0,1,0)),(2,(0,0,2,2,0)),(2,(0,1,3,0,0)),(2,(0,4,0,0,0)),(2,(1,0,0,3,0)),(2,(1,0,0,1,1)),(3,(0,0,1,3,0)),(3,(0,3,1,0,0))]

def leftRows : Fin 56 → SourceTuple := ![(0,0,0,10,0),(0,0,3,7,0),(0,0,6,4,0),(0,1,1,8,0),(0,1,4,5,0),(0,1,7,2,0),(0,2,2,6,0),(0,2,5,3,0),(0,2,8,0,0),(0,3,0,7,0),(0,3,3,4,0),(0,3,6,1,0),(0,4,1,5,0),(0,4,4,2,0),(0,5,2,3,0),(0,5,5,0,0),(0,6,0,4,0),(0,6,3,1,0),(0,7,1,2,0),(0,0,0,8,1),(0,0,3,5,1),(0,1,1,6,1),(0,1,4,3,1),(0,1,7,0,1),(0,2,2,4,1),(0,2,5,1,1),(0,3,0,5,1),(0,3,3,2,1),(0,4,1,3,1),(0,4,4,0,1),(0,5,2,1,1),(0,6,0,2,1),(0,0,0,6,2),(0,0,3,3,2),(0,1,1,4,2),(0,1,4,1,2),(0,2,2,2,2),(0,3,0,3,2),(0,3,3,0,2),(0,4,1,1,2),(1,0,4,5,0),(1,1,2,6,0),(1,1,5,3,0),(1,1,8,0,0),(1,2,3,4,0),(1,2,6,1,0),(1,3,4,2,0),(1,5,3,1,0),(1,0,1,6,1),(1,0,4,3,1),(1,1,2,4,1),(1,2,0,5,1),(1,2,3,2,1),(1,3,1,3,1),(1,0,1,4,2),(1,2,0,3,2)]

def leftNormals : Fin 56 → Sparse := ![leftNormal0,leftNormal1,leftNormal2,leftNormal3,leftNormal4,leftNormal5,leftNormal6,leftNormal7,leftNormal8,leftNormal9,leftNormal10,leftNormal11,leftNormal12,leftNormal13,leftNormal14,leftNormal15,leftNormal16,leftNormal17,leftNormal18,leftNormal19,leftNormal20,leftNormal21,leftNormal22,leftNormal23,leftNormal24,leftNormal25,leftNormal26,leftNormal27,leftNormal28,leftNormal29,leftNormal30,leftNormal31,leftNormal32,leftNormal33,leftNormal34,leftNormal35,leftNormal36,leftNormal37,leftNormal38,leftNormal39,leftNormal40,leftNormal41,leftNormal42,leftNormal43,leftNormal44,leftNormal45,leftNormal46,leftNormal47,leftNormal48,leftNormal49,leftNormal50,leftNormal51,leftNormal52,leftNormal53,leftNormal54,leftNormal55]

def leftMinorRows : Fin 56 → List ℕ := ![[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,41,0,0,0,0,0,0,0,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,86,0,0,0,0,0,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,45,43,0,0,0,0,0,0,32,0,0,0,23,0,0,0,0,77,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,90,0,0,0,0,0,0,0,0,0,0,0,0,89,0,0,0,0,0,0,0,1,45,0,0,0,0,0,0,108,0,0,0,19,0,0,0,0,1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,86,0,0,0,0,0,0,0,0,0,0,0,20,0,0,0,0,0,0,0,45,0,43,0,0,0,0,0,0,0,0,0,0,23,0,0,0,0,0,0,0],[57,0,0,0,0,0,0,0,0,0,0,0,0,0,90,90,0,0,0,0,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,2,45,45,0,0,0,0,0,108,32,0,0,19,19,0,0,0,1,0,0,0],[0,57,0,0,0,0,0,0,0,0,0,0,0,0,4,2,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,2,1,0,0,0,0,0,0,108,0,0,105,107,0,0,0,0,0,0,0],[0,0,57,0,0,0,0,0,0,0,0,0,0,0,86,90,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,45,43,0,0,0,0,64,0,32,0,23,19,0,0,0,77,0,0,0],[0,0,0,57,0,0,0,0,0,0,0,0,0,0,92,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,45,0,0,0,0,107,108,108,0,17,105,0,0,0,1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,107,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,86,0,0,0,0,0,0,0,0,0,0,0,58,0,0,0,0,0,0,0,39,0,0,0,43,0,0,0,0,0,0,0,0,23,0,0,0,0,0,0,0],[0,0,0,0,57,0,0,0,0,0,0,0,0,0,63,92,0,0,0,0,0,0,0,0,0,0,0,43,0,0,0,0,0,0,0,43,39,1,45,45,0,0,0,31,64,108,0,46,17,0,0,0,77,0,0,0],[0,0,0,0,0,57,0,0,0,0,0,0,0,0,90,2,0,0,0,0,0,0,0,0,0,0,0,86,0,0,0,0,0,0,0,0,43,0,2,1,0,0,0,0,107,0,0,19,107,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,63,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,43,0,39,0,45,0,0,0,32,0,64,0,0,46,0,0,0,0,0,0,0],[0,0,0,0,0,0,57,0,0,0,0,0,0,0,88,90,0,0,0,0,0,0,0,0,0,0,0,17,0,0,0,0,0,0,0,0,43,43,1,2,0,0,0,108,31,107,0,21,19,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,57,0,0,0,0,0,0,82,88,0,0,0,0,0,0,0,0,0,0,0,106,0,0,0,0,0,0,0,0,0,43,39,1,0,0,0,65,32,31,0,27,21,0,0,0,76,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,86,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,0,0,0,0,0,108,0,0,23,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,82,0,0,0,0,0,0,0,0,0,0,0,85,0,0,0,0,0,0,0,108,0,0,0,39,0,0,0,0,0,32,0,0,27,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,57,0,0,0,0,0,84,86,0,0,0,0,0,0,0,0,0,0,0,105,0,0,0,0,0,0,0,0,108,0,43,43,0,0,0,0,65,108,0,25,23,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,84,0,0,0,0,0,0,0,0,0,0,0,95,0,0,0,0,0,0,0,0,0,108,0,43,0,0,0,33,0,65,0,0,25,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,0,0,0,0,0,32,0,0,0,0,0,0,77,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,43,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,57,0,0,0,0,0,0,0,108,108,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,45,0,0,0,0,108,0,0,0,0,0,0,1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,57,0,0,0,0,0,0,0,108,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,45,0,0,0,0,64,0,0,88,0,0,0,77,0,0],[0,0,0,0,0,0,0,0,0,0,0,57,0,0,0,0,0,0,0,108,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,107,0,0,0,0,0,0,1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,39,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,57,0,0,0,0,33,0,0,108,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,1,0,0,0,0,31,0,0,0,88,0,0,77,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,0,108,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,39,0,0,0,0,32,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,0,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,0,0,0,0,108,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,57,0,0,0,0,0,0,33,0,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,0,0,0,0,65,0,0,0,0,0,0,76,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,0,88,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,0,0,0,0,0,0,0,0,0,0,0,52,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,57,0,0,0,0,0,0,0,0,0,108,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,57,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,39,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,0,0,0,0,0,0,0,0,0,0,0,0,52],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,2,45,0,0,0,0,0,0,44,0,0,0,96,0,32,0,0,1,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,13,57,0,0,0,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,2,0,45,0,0,0,0,0,45,43,0,0,0,96,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,0,57,0,0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,0,2,2,0,0,0,0,0,2,44,0,0,106,106,108,32,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,108,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,26,3,0,0,57,0,0,0,0,0,0,0,0,25,0,0,0,0,0,0,0,2,45,2,45,0,0,0,0,107,45,44,0,83,106,0,0,0,2,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,0,57,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,2,0,2,0,0,0,0,0,2,1,0,103,0,0,108,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,6,0,0,0,0,57,0,0,0,0,0,0,26,0,0,0,0,0,0,0,0,45,2,2,2,0,0,0,43,107,2,0,93,103,33,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,23,3,0,0,0,0,0,0,57,0,0,0,0,20,0,0,0,0,0,0,0,0,43,0,45,2,0,0,0,0,40,43,0,86,106,0,0,108,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,45,0,0,0,0,0,43,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,0,108,32,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,44,0,0,0,0,0,0,1,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,57,0,0,0,0,108,0,32,0,0,0,0,0,0,0,0,0,2,45,0,0,0,0,45,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,45,0,0,0,0,0,0,0,0,0,0,0,88,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,108,0,0,0,0,57,0,0,0,0,108,108,0,0,0,0,0,0,0,0,2,2,0,0,0,0,107,0,0,0,0,0,0,2,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,108,0,0,0,0,0,0,33,0,0,108,32,0,0,0,0,0,0,0,45,45,0,0,0,0,39,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,45,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,45,0,0,0,0,0,0,0,0,0,0,88,0,0]]

def leftInverseColumns : Fin 56 → List ℕ := ![[14,54,6,47,90,93,18,32,104,0,42,25,97,47,72,72,54,6,92,19,24,79,64,0,0,71,0,26,31,72,91,52,99,0,21,31,66,28,1,93,46,19,0,16,0,99,72,18,107,12,0,96,87,32,15,87],[60,74,88,81,96,65,86,48,107,0,45,62,62,25,79,79,0,74,0,0,104,0,93,0,0,34,0,43,33,16,16,39,9,0,25,68,28,66,76,2,0,0,0,66,0,66,16,8,79,104,0,0,75,90,21,100],[44,0,100,50,60,0,9,35,15,0,85,14,14,83,88,88,0,94,0,0,29,0,9,0,0,2,0,34,70,100,100,79,23,0,66,107,58,75,0,32,0,0,0,75,0,75,100,88,88,92,0,0,1,85,91,70],[82,49,33,28,0,40,18,16,85,0,73,78,22,42,11,11,67,73,98,70,73,96,90,0,0,82,0,30,4,107,68,59,16,0,103,88,43,106,103,74,49,70,0,94,0,49,107,8,98,106,0,107,36,22,25,36],[44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[60,39,70,21,35,99,55,21,42,0,102,2,2,43,88,88,67,88,98,70,78,96,52,0,0,2,0,0,96,36,106,49,38,0,39,0,107,0,108,0,49,70,0,0,43,0,36,87,88,108,43,107,0,75,91,70],[6,102,79,28,26,50,19,36,59,0,58,100,66,79,83,83,29,49,5,97,84,105,32,0,0,44,0,37,72,37,25,26,26,0,2,94,80,10,45,31,57,97,0,98,0,94,37,51,52,92,0,100,41,29,40,14],[0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[58,5,68,71,19,53,34,63,17,0,95,43,88,107,81,81,61,47,3,80,91,63,52,0,0,39,0,67,90,33,4,46,105,0,43,73,5,50,30,39,56,80,0,79,0,97,33,96,85,22,0,60,73,24,85,57],[0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[100,65,0,65,91,21,56,100,26,0,69,83,83,95,55,55,39,74,18,44,21,51,51,0,0,83,0,0,36,23,67,9,108,0,85,0,0,0,0,0,9,44,0,0,108,0,23,55,55,0,108,33,0,88,16,71],[51,104,41,38,43,56,75,108,92,0,84,28,95,57,100,100,23,73,19,107,9,72,107,0,0,32,0,42,68,68,66,74,0,0,88,36,18,4,102,15,64,107,0,30,0,12,68,42,14,44,0,53,36,77,39,30],[0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[29,57,56,28,82,81,68,83,67,0,101,40,65,97,66,66,46,46,38,105,97,35,106,0,0,56,0,88,59,26,22,59,54,0,45,91,48,76,6,16,19,105,0,38,0,4,26,69,39,58,0,106,35,53,41,107],[76,93,34,17,17,92,75,63,16,35,40,37,31,87,56,56,0,93,11,62,29,94,3,0,0,31,0,69,92,6,68,1,25,0,47,28,103,40,23,97,71,62,0,40,0,40,22,13,56,106,0,108,81,82,48,104],[0,0,0,0,0,0,0,0,0,15,65,15,65,50,12,12,0,0,0,0,0,0,0,0,0,30,0,0,0,71,0,0,0,0,35,0,0,0,0,0,0,0,0,0,0,0,0,12,12,0,0,0,0,17,57,69],[17,71,108,54,92,55,1,65,38,15,36,103,103,89,84,84,0,71,21,101,9,0,7,0,0,101,0,14,60,39,102,33,50,0,79,12,6,95,34,26,0,101,0,95,0,95,39,101,84,3,0,0,97,1,72,47],[0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[32,108,43,76,79,33,66,41,1,100,35,13,57,46,53,53,0,108,1,16,48,0,4,0,0,78,0,52,61,56,73,107,5,0,94,29,17,57,12,81,0,17,0,57,0,57,56,59,53,63,0,0,80,55,61,5],[0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,92,0,0,92,0,0,73,6,21,20,46,46,0,0,55,63,63,92,86,0,0,6,0,0,65,15,78,0,1,0,95,0,6,0,6,0,0,63,0,0,0,0,15,49,46,3,0,20,0,15,55,101],[0,0,0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,1,0,0,1,0,0,62,11,11,73,48,48,0,0,16,54,54,0,98,0,0,11,0,0,101,82,27,0,10,0,47,0,83,0,83,0,0,54,0,0,0,0,82,35,48,96,0,0,0,82,10,58],[0,0,0,0,32,0,0,32,0,0,13,90,90,38,36,36,0,0,76,93,93,0,84,0,0,90,0,0,103,7,100,0,60,0,8,0,40,0,40,0,0,93,0,0,0,0,7,56,36,20,0,0,0,7,62,98],[0,0,0,0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,50,87,87,72,13,13,0,0,0,0,0,0,55,0,0,87,0,0,16,54,54,0,88,0,15,0,0,0,0,0,0,0,0,0,0,0,54,13,13,0,0,83,0,54,89,102],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,37,0,0,0,0,0,0,0,59,55,22,37,0,0,0,55,0,0,55,55,0,0,0,0,0,0,0,93,0,0,0,0,0,37,0,0,0,0,0,79,44],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,0,0,0,0,0,17,54,71,39,0,0,0,14,0,0,71,71,0,0,0,0,0,0,0,71,0,0,0,0,15,0,0,0,0,0,0,0,50],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,65,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,54,54,71,0,0,0,26,0,0,54,54,0,0,0,0,0,0,0,54,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,76,93,93,91,0,0,0,69,0,0,93,93,0,0,0,0,0,0,0,93,0,0,0,0,0,0,0,0,0,0,0,0,44],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,65],[0,0,0,0,0,0,0,0,0,0,85,14,14,83,71,71,0,15,0,0,50,0,0,0,0,14,0,0,0,0,0,0,0,0,95,0,0,0,0,0,0,0,0,0,0,0,0,71,71,92,0,0,0,15,92,54],[15,37,44,22,0,87,65,98,72,0,69,83,69,95,93,93,44,37,79,72,87,24,50,0,0,69,0,38,9,81,44,59,86,0,43,17,0,71,76,55,94,72,0,71,0,71,81,22,93,0,0,54,92,24,33,17],[0,0,0,0,0,0,0,0,0,0,40,26,26,14,54,54,0,44,0,0,0,0,0,0,0,26,0,0,0,0,0,0,0,0,97,0,0,0,0,0,0,0,0,0,0,0,0,54,54,0,0,0,0,44,93,38],[9,44,70,35,42,74,39,79,65,0,86,57,5,81,2,2,0,35,0,0,53,0,39,0,0,5,0,1,49,70,70,88,27,0,11,32,107,108,0,33,0,0,0,108,0,108,70,2,2,108,108,0,77,105,64,66],[44,94,100,50,30,59,9,5,15,0,90,106,106,99,103,103,0,94,0,0,44,0,12,0,0,94,0,17,57,97,97,79,6,0,47,108,92,92,17,16,0,0,0,92,0,92,97,57,103,46,0,0,1,82,26,20],[100,65,39,74,67,35,70,30,44,0,104,12,12,40,91,91,0,65,0,0,56,0,70,0,0,64,0,108,60,39,39,21,82,0,41,77,2,1,0,76,0,0,0,1,0,1,39,91,91,1,0,0,32,104,78,60],[0,0,0,0,0,0,0,0,0,0,69,83,83,95,55,55,0,0,0,0,44,0,0,0,0,83,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,55,55,0,0,0,0,0,16,71],[0,0,0,0,0,0,0,0,0,0,40,26,26,14,54,54,0,0,0,0,0,0,44,0,0,26,0,0,100,65,65,0,5,0,12,0,0,0,0,0,0,0,0,0,0,0,65,54,54,0,0,0,0,65,93,38],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,0,0,0,0,0,0,0,72,0,0,92,71,71,0,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,7,0,0,0,0,0,6,13],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,92,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,6,0,0,0,0,0,0,0,0,0,15,0,0,0,0,92,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,6,0,0,0,0,0,83,89],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,6,0,0,0,0,0,0,0,0,0,15,0,0,0,0,0,92,71,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,6,0,0,0,0,0,83,89],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,83,83,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,83,83,0,0,0,0,0,40,14],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,92,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,92,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,92,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]

def rightInput0 : Sparse := [((0,1,2,5,0),57),((2,0,0,4,1),1)]

def rightNormal0 : Sparse := [((0,1,2,5,0),57),((2,0,0,4,1),1)]

def rightH0 : Sparse := []

def rightG0 : Sparse := []

def rightInput1 : Sparse := [((0,1,5,2,0),57),((2,0,3,1,1),1)]

def rightNormal1 : Sparse := [((0,1,5,2,0),57),((2,0,3,1,1),1)]

def rightH1 : Sparse := []

def rightG1 : Sparse := []

def rightInput2 : Sparse := [((0,2,3,3,0),57),((2,1,1,2,1),1)]

def rightNormal2 : Sparse := [((0,2,3,3,0),57),((2,1,1,2,1),1)]

def rightH2 : Sparse := []

def rightG2 : Sparse := []

def rightInput3 : Sparse := [((0,3,4,1,0),57),((2,2,2,0,1),1)]

def rightNormal3 : Sparse := [((0,3,4,1,0),57),((2,2,2,0,1),1)]

def rightH3 : Sparse := []

def rightG3 : Sparse := []

def rightInput4 : Sparse := [((0,4,2,2,0),57),((2,3,0,1,1),1)]

def rightNormal4 : Sparse := [((0,4,2,2,0),57),((2,3,0,1,1),1)]

def rightH4 : Sparse := []

def rightG4 : Sparse := []

def rightInput5 : Sparse := [((0,1,2,3,1),57),((2,0,0,2,2),1)]

def rightNormal5 : Sparse := [((0,1,2,3,1),57),((2,0,0,2,2),1)]

def rightH5 : Sparse := []

def rightG5 : Sparse := []

def rightInput6 : Sparse := [((0,2,3,1,1),57),((2,1,1,0,2),1)]

def rightNormal6 : Sparse := [((0,2,3,1,1),57),((2,1,1,0,2),1)]

def rightH6 : Sparse := []

def rightG6 : Sparse := []

def rightInput7 : Sparse := [((0,1,2,1,2),57),((2,0,0,0,3),1)]

def rightNormal7 : Sparse := [((2,6,0,0,0),2),((1,7,0,0,0),10),((0,8,0,0,0),107),((2,3,3,0,0),66),((1,4,3,0,0),3),((0,5,3,0,0),86),((2,0,6,0,0),107),((0,2,6,0,0),2),((2,4,1,1,0),69),((1,5,1,1,0),23),((0,6,1,1,0),84),((2,1,4,1,0),107),((1,2,4,1,0),6),((0,3,4,1,0),90),((0,0,7,1,0),2),((2,2,2,2,0),2),((1,3,2,2,0),16),((0,4,2,2,0),88),((1,0,5,2,0),3),((0,1,5,2,0),4),((2,3,0,3,0),70),((1,4,0,3,0),13),((0,5,0,3,0),82),((2,0,3,3,0),65),((1,1,3,3,0),3),((0,2,3,3,0),92),((2,1,1,4,0),64),((1,2,1,4,0),26),((0,3,1,4,0),63),((0,0,4,4,0),90),((1,0,2,5,0),13),((0,1,2,5,0),90),((2,0,0,6,0),66),((0,2,0,6,0),86),((0,0,1,7,0),86),((0,1,2,1,2),57)]

def rightH7 : Sparse := [((5,0,0,0,0),108),((3,2,0,0,0),1),((2,3,0,0,0),76),((1,4,0,0,0),108),((0,5,0,0,0),66),((2,0,3,0,0),1),((0,2,3,0,0),107),((3,0,1,1,0),1),((2,1,1,1,0),1),((1,2,1,1,0),107),((0,3,1,1,0),64),((0,0,4,1,0),107),((1,0,2,2,0),108),((0,1,2,2,0),107),((2,0,0,3,0),77),((0,2,0,3,0),64),((0,0,1,4,0),64)]

def rightG7 : Sparse := [((2,0,0,0,0),1)]

def rightInput8 : Sparse := [((1,1,3,3,0),57),((3,0,1,2,1),1)]

def rightNormal8 : Sparse := [((1,1,3,3,0),57),((1,2,1,2,1),108),((0,3,1,2,1),33),((0,0,4,2,1),108),((1,0,2,3,1),108),((0,1,2,3,1),108),((0,0,1,5,1),32)]

def rightH8 : Sparse := [((0,0,1,2,1),1)]

def rightG8 : Sparse := []

def rightInput9 : Sparse := [((1,2,4,1,0),57),((3,1,2,0,1),1)]

def rightNormal9 : Sparse := [((1,2,4,1,0),57),((1,3,2,0,1),108),((0,4,2,0,1),33),((0,1,5,0,1),108),((1,1,3,1,1),108),((0,2,3,1,1),108),((0,1,2,3,1),32)]

def rightH9 : Sparse := [((0,1,2,0,1),1)]

def rightG9 : Sparse := []

def rightInput10 : Sparse := [((1,3,2,2,0),57),((3,2,0,1,1),1)]

def rightNormal10 : Sparse := [((1,3,2,2,0),57),((1,4,0,1,1),108),((0,5,0,1,1),33),((0,2,3,1,1),108),((1,2,1,2,1),108),((0,3,1,2,1),108),((0,2,0,4,1),32)]

def rightH10 : Sparse := [((0,2,0,1,1),1)]

def rightG10 : Sparse := []

def rightInput11 : Sparse := [((1,1,3,1,1),57),((3,0,1,0,2),1)]

def rightNormal11 : Sparse := [((1,1,3,1,1),57),((1,2,1,0,2),108),((0,3,1,0,2),33),((0,0,4,0,2),108),((1,0,2,1,2),108),((0,1,2,1,2),108),((0,0,1,3,2),32)]

def rightH11 : Sparse := [((0,0,1,0,2),1)]

def rightG11 : Sparse := []

def rightInput12 : Sparse := [((2,1,4,1,0),57),((4,0,2,0,1),1)]

def rightNormal12 : Sparse := [((2,1,4,1,0),57),((2,2,2,0,1),108),((1,3,2,0,1),33),((1,0,5,0,1),108),((2,0,3,1,1),108),((1,1,3,1,1),108),((1,0,2,3,1),32)]

def rightH12 : Sparse := [((1,0,2,0,1),1)]

def rightG12 : Sparse := []

def rightInput13 : Sparse := [((2,2,2,2,0),57),((4,1,0,1,1),1)]

def rightNormal13 : Sparse := [((2,2,2,2,0),57),((2,3,0,1,1),108),((1,4,0,1,1),33),((1,1,3,1,1),108),((2,1,1,2,1),108),((1,2,1,2,1),108),((1,1,0,4,1),32)]

def rightH13 : Sparse := [((1,1,0,1,1),1)]

def rightG13 : Sparse := []

def rightInput14 : Sparse := [((6,0,1,1,0),1),((0,0,7,1,0),1)]

def rightNormal14 : Sparse := [((2,4,1,1,0),1),((1,5,1,1,0),43),((0,6,1,1,0),108),((1,2,4,1,0),2),((0,3,4,1,0),43),((0,0,7,1,0),2),((2,2,2,2,0),2),((1,3,2,2,0),45),((0,4,2,2,0),43),((1,0,5,2,0),2),((0,1,5,2,0),2),((2,0,3,3,0),1),((1,1,3,3,0),2),((0,2,3,3,0),1),((1,2,1,4,0),45),((0,3,1,4,0),41),((0,0,4,4,0),45),((1,0,2,5,0),45),((0,1,2,5,0),45),((0,0,1,7,0),43)]

def rightH14 : Sparse := [((3,0,1,1,0),1),((1,2,1,1,0),108),((0,3,1,1,0),33),((0,0,4,1,0),108),((1,0,2,2,0),108),((0,1,2,2,0),108),((0,0,1,4,0),32)]

def rightG14 : Sparse := []

def rightInput15 : Sparse := [((6,2,0,0,0),1),((0,2,6,0,0),1)]

def rightNormal15 : Sparse := [((2,6,0,0,0),1),((1,7,0,0,0),43),((0,8,0,0,0),108),((1,4,3,0,0),2),((0,5,3,0,0),43),((0,2,6,0,0),2),((2,4,1,1,0),2),((1,5,1,1,0),45),((0,6,1,1,0),43),((1,2,4,1,0),2),((0,3,4,1,0),2),((2,2,2,2,0),1),((1,3,2,2,0),2),((0,4,2,2,0),1),((1,4,0,3,0),45),((0,5,0,3,0),41),((0,2,3,3,0),45),((1,2,1,4,0),45),((0,3,1,4,0),45),((0,2,0,6,0),43)]

def rightH15 : Sparse := [((3,2,0,0,0),1),((1,4,0,0,0),108),((0,5,0,0,0),33),((0,2,3,0,0),108),((1,2,1,1,0),108),((0,3,1,1,0),108),((0,2,0,3,0),32)]

def rightG15 : Sparse := []

def rightInput16 : Sparse := [((7,1,0,0,0),1),((1,1,6,0,0),1)]

def rightNormal16 : Sparse := [((2,6,0,0,0),43),((1,7,0,0,0),107),((0,8,0,0,0),33),((2,3,3,0,0),2),((1,4,3,0,0),43),((0,5,3,0,0),108),((1,1,6,0,0),2),((2,4,1,1,0),45),((1,5,1,1,0),40),((0,6,1,1,0),65),((2,1,4,1,0),2),((1,2,4,1,0),2),((0,3,4,1,0),107),((2,2,2,2,0),2),((1,3,2,2,0),107),((0,4,2,2,0),31),((0,1,5,2,0),108),((2,3,0,3,0),45),((1,4,0,3,0),41),((0,5,0,3,0),32),((1,1,3,3,0),44),((0,2,3,3,0),108),((2,1,1,4,0),45),((1,2,1,4,0),45),((0,3,1,4,0),64),((0,1,2,5,0),32),((1,1,0,6,0),43)]

def rightH16 : Sparse := [((4,1,0,0,0),1),((2,3,0,0,0),108),((1,4,0,0,0),33),((0,5,0,0,0),1),((1,1,3,0,0),108),((2,1,1,1,0),108),((1,2,1,1,0),108),((0,3,1,1,0),2),((0,1,2,2,0),1),((1,1,0,3,0),32)]

def rightG16 : Sparse := []

def rightInput17 : Sparse := [((8,0,0,0,0),1),((2,0,6,0,0),1)]

def rightNormal17 : Sparse := [((2,6,0,0,0),107),((1,7,0,0,0),99),((0,8,0,0,0),2),((2,3,3,0,0),43),((1,4,3,0,0),106),((0,5,3,0,0),23),((2,0,6,0,0),2),((0,2,6,0,0),107),((2,4,1,1,0),40),((1,5,1,1,0),86),((0,6,1,1,0),25),((2,1,4,1,0),2),((1,2,4,1,0),103),((0,3,4,1,0),19),((0,0,7,1,0),107),((2,2,2,2,0),107),((1,3,2,2,0),93),((0,4,2,2,0),21),((1,0,5,2,0),106),((0,1,5,2,0),105),((2,3,0,3,0),41),((1,4,0,3,0),96),((0,5,0,3,0),27),((2,0,3,3,0),44),((1,1,3,3,0),106),((0,2,3,3,0),17),((2,1,1,4,0),45),((1,2,1,4,0),83),((0,3,1,4,0),46),((0,0,4,4,0),19),((1,0,2,5,0),96),((0,1,2,5,0),19),((2,0,0,6,0),43),((0,2,0,6,0),23),((0,0,1,7,0),23)]

def rightH17 : Sparse := [((5,0,0,0,0),1),((3,2,0,0,0),108),((2,3,0,0,0),33),((1,4,0,0,0),1),((0,5,0,0,0),43),((2,0,3,0,0),108),((0,2,3,0,0),2),((3,0,1,1,0),108),((2,1,1,1,0),108),((1,2,1,1,0),2),((0,3,1,1,0),45),((0,0,4,1,0),2),((1,0,2,2,0),1),((0,1,2,2,0),2),((2,0,0,3,0),32),((0,2,0,3,0),45),((0,0,1,4,0),45)]

def rightG17 : Sparse := []

def rightInput18 : Sparse := [((4,1,0,3,0),57),((0,0,4,2,1),108)]

def rightNormal18 : Sparse := [((2,3,0,3,0),52),((1,4,0,3,0),28),((1,1,3,3,0),52),((2,1,1,4,0),52),((1,2,1,4,0),52),((1,1,0,6,0),80),((0,0,4,2,1),108)]

def rightH18 : Sparse := [((1,1,0,3,0),57)]

def rightG18 : Sparse := []

def rightInput19 : Sparse := [((4,2,1,1,0),57),((0,1,5,0,1),108)]

def rightNormal19 : Sparse := [((2,4,1,1,0),52),((1,5,1,1,0),28),((1,2,4,1,0),52),((2,2,2,2,0),52),((1,3,2,2,0),52),((1,2,1,4,0),80),((0,1,5,0,1),108)]

def rightH19 : Sparse := [((1,2,1,1,0),57)]

def rightG19 : Sparse := []

def rightInput20 : Sparse := [((4,1,0,1,1),57),((0,0,4,0,2),108)]

def rightNormal20 : Sparse := [((2,3,0,1,1),52),((1,4,0,1,1),28),((1,1,3,1,1),52),((2,1,1,2,1),52),((1,2,1,2,1),52),((1,1,0,4,1),80),((0,0,4,0,2),108)]

def rightH20 : Sparse := [((1,1,0,1,1),57)]

def rightG20 : Sparse := []

def rightInput21 : Sparse := [((5,1,1,1,0),57),((1,0,5,0,1),108)]

def rightNormal21 : Sparse := [((2,4,1,1,0),28),((1,5,1,1,0),57),((0,6,1,1,0),81),((2,1,4,1,0),52),((0,3,4,1,0),57),((2,2,2,2,0),52),((1,3,2,2,0),5),((0,4,2,2,0),29),((0,1,5,2,0),57),((1,1,3,3,0),57),((0,2,3,3,0),57),((2,1,1,4,0),80),((0,3,1,4,0),29),((0,1,2,5,0),29),((1,0,5,0,1),108)]

def rightH21 : Sparse := [((2,1,1,1,0),57),((0,3,1,1,0),52),((0,1,2,2,0),52)]

def rightG21 : Sparse := []

def rightInput22 : Sparse := [((3,2,0,3,0),88),((1,0,2,1,2),1)]

def rightNormal22 : Sparse := [((1,4,0,3,0),21),((0,5,0,3,0),70),((0,2,3,3,0),21),((1,2,1,4,0),21),((0,3,1,4,0),21),((0,2,0,6,0),91),((1,0,2,1,2),1)]

def rightH22 : Sparse := [((0,2,0,3,0),88)]

def rightG22 : Sparse := []

def rightColumns : Fin 23 → SectionColumn := ![(0,(0,0,0,4,0)),(0,(0,0,3,1,0)),(0,(0,1,1,2,0)),(0,(0,2,2,0,0)),(0,(0,3,0,1,0)),(0,(0,0,0,2,1)),(0,(0,1,1,0,1)),(0,(0,0,0,0,2)),(0,(1,0,1,2,0)),(0,(1,1,2,0,0)),(0,(1,2,0,1,0)),(0,(1,0,1,0,1)),(0,(2,0,2,0,0)),(0,(2,1,0,1,0)),(1,(0,0,1,1,0)),(1,(0,2,0,0,0)),(1,(1,1,0,0,0)),(1,(2,0,0,0,0)),(2,(0,0,0,2,0)),(2,(0,1,1,0,0)),(2,(0,0,0,0,1)),(2,(1,0,1,0,0)),(3,(1,0,0,1,0))]

def rightRows : Fin 23 → SourceTuple := ![(0,0,1,7,0),(0,0,7,1,0),(0,1,2,5,0),(0,1,5,2,0),(0,2,0,6,0),(0,2,3,3,0),(0,2,6,0,0),(0,3,1,4,0),(0,3,4,1,0),(0,4,2,2,0),(0,5,0,3,0),(0,0,1,5,1),(0,0,4,2,1),(0,1,2,3,1),(0,1,5,0,1),(0,2,0,4,1),(0,2,3,1,1),(0,4,2,0,1),(0,0,1,3,2),(0,0,4,0,2),(0,1,2,1,2),(1,0,2,3,1),(1,1,0,4,1)]

def rightNormals : Fin 23 → Sparse := ![rightNormal0,rightNormal1,rightNormal2,rightNormal3,rightNormal4,rightNormal5,rightNormal6,rightNormal7,rightNormal8,rightNormal9,rightNormal10,rightNormal11,rightNormal12,rightNormal13,rightNormal14,rightNormal15,rightNormal16,rightNormal17,rightNormal18,rightNormal19,rightNormal20,rightNormal21,rightNormal22]

def rightMinorRows : Fin 23 → List ℕ := ![[0,0,0,0,0,0,0,86,0,0,0,0,0,0,43,0,0,23,0,0,0,0,0],[0,0,0,0,0,0,0,2,0,0,0,0,0,0,2,0,0,107,0,0,0,0,0],[57,0,0,0,0,0,0,90,0,0,0,0,0,0,45,0,32,19,0,0,0,29,0],[0,57,0,0,0,0,0,4,0,0,0,0,0,0,2,0,108,105,0,0,0,57,0],[0,0,0,0,0,0,0,86,0,0,0,0,0,0,0,43,0,23,0,0,0,0,91],[0,0,57,0,0,0,0,92,0,0,0,0,0,0,1,45,108,17,0,0,0,57,21],[0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,2,0,107,0,0,0,0,0],[0,0,0,0,0,0,0,63,0,0,0,0,0,0,41,45,64,46,0,0,0,29,21],[0,0,0,57,0,0,0,90,0,0,0,0,0,0,43,2,107,19,0,0,0,57,0],[0,0,0,0,57,0,0,88,0,0,0,0,0,0,43,1,31,21,0,0,0,29,0],[0,0,0,0,0,0,0,82,0,0,0,0,0,0,0,41,32,27,0,0,0,0,70],[0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,108,0,0,0,0],[0,0,0,0,0,57,0,0,108,32,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,0,108,0,0,0],[0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,57,0,0,108,108,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,33,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0,0,0,0,0,108,0,0],[0,0,0,0,0,0,0,57,0,0,0,108,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,108,0,0,0,32,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,80,0,0]]

def rightInverseColumns : Fin 23 → List ℕ := ![[74,59,37,37,59,0,0,0,0,0,0,0,0,0,38,38,55,38,0,0,0,37,103],[65,15,74,22,50,0,0,0,0,0,0,0,0,0,1,55,71,55,0,0,0,57,20],[44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[35,50,65,72,57,0,0,0,0,0,0,0,0,0,0,0,55,0,0,0,0,81,6],[0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[44,94,35,87,59,0,0,0,0,0,0,0,0,0,0,55,38,0,0,0,0,52,89],[65,15,15,15,65,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,94,0],[0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[44,94,94,0,59,0,0,0,0,0,0,0,0,0,0,0,92,0,0,0,0,30,0],[0,0,0,0,0,15,0,0,92,0,0,0,71,0,0,0,0,0,17,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0,0],[0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,108,0,0,0],[0,0,0,0,0,0,15,0,0,0,92,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,30,74,0,0,76,0,0,0,0,0,0,0,0,0,33,0,0,0],[0,0,0,0,0,0,0,15,0,0,0,92,0,12,0,0,0,15,0,0,17,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,57,0,0,0,0,0,0,108,0,0],[0,0,0,0,0,0,0,44,0,0,0,0,0,0,0,0,0,44,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,92,0,0,0,0,0,0,0,0,0,0],[0,0,0,0,0,0,0,0,0,0,0,0,0,92,0,0,0,0,0,0,0,0,0]]

end CycleQ2SeedLinkageModularData
end


/- Component: continuation_3/SeedLinkageOrbitCover.lean -/
section
/-! The common vertex of the three explicit linkage components is absent
from every nonempty actual seed coordinate chart. -/

noncomputable section
set_option maxHeartbeats 100000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageOrbitCover

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedLinkageIdeals CycleQ2SeedLinkagePrincipal
  CycleQ2CurveRestriction CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechLocalization

variable {K : Type*} [Field K]

def seedCoordinate (r ι : K) (i : Fin 5) : SeedRing r ι := quotientMap r ι (X i)
def linkageA (r ι : K) : SeedRing r ι := quotientMap r ι (X 0^2)
def linkageB (r ι : K) : SeedRing r ι := quotientMap r ι (C r*X 1*X 3)
def linkageC (r ι : K) : SeedRing r ι := quotientMap r ι (X 4)
def linkageD (r ι : K) : SeedRing r ι := quotientMap r ι (X 2^2)

theorem variables_zero_of_vertex (s : Side) (r ι : K)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1)
    {D : Type*} [CommRing D] [IsDomain D] (f : Poly K →+* D)
    (hb0 : f (C r*X 1*X 3)=0) (hd0 : f (X 2^2)=0)
    (hgen : ∀ j : Fin 5, f (linkageGenerator s r j)=0) (hH : f (smoothH ι)=0) :
    ∀ i : Fin 5, f (X i)=0 := by
  have hconst (c : K) (hc : c≠0) : f (C c)≠0 := by
    exact (map_ne_zero (f.comp C)).mpr hc
  have h2 : f (X 2)=0 := eq_zero_of_pow_eq_zero (by simpa only [map_pow] using hd0)
  have h0pow : f (X 0)^6=0 := by
    have hh := hgen 1
    cases s
    · change f ((X 0^2)^3-(C r*X 1*X 3)^3)=0 at hh
      simpa [map_sub,map_pow,hb0,←pow_mul] using hh
    · change f ((X 0^2)^3+(X 2^2)^3)=0 at hh
      simpa [map_add,map_pow,h2,←pow_mul] using hh
  have h0 : f (X 0)=0 := eq_zero_of_pow_eq_zero h0pow
  have hwpow : f (X 4)^3=0 := by
    have hh := hgen 4
    cases s
    · change f (X 4^3+(X 2^2)^3)=0 at hh
      simpa [map_add,map_pow,h2] using hh
    · change f (-(C r*X 1*X 3)^3+X 4^3)=0 at hh
      simpa [map_add,map_neg,map_pow,hb0] using hh
  have hw : f (X 4)=0 := eq_zero_of_pow_eq_zero hwpow
  have h13 : f (X 1)*f (X 3)=0 := by
    rw [map_mul,map_mul,mul_assoc] at hb0
    exact (mul_eq_zero.mp hb0).resolve_left (hconst r hr)
  have hred : f (C (1-ι))*f (X 3)^3-f (C ι)*f (X 1)^3=0 := by
    simp only [smoothH,smoothB,smoothA,map_sub,map_add,map_mul,map_pow,h0,h2,
      zero_pow (by decide : 3≠0),zero_mul,mul_zero,add_zero,zero_add] at hH
    simp only [map_sub,map_one]
    linear_combination hH
  have h1h3 : f (X 1)=0 ∧ f (X 3)=0 := by
    rcases mul_eq_zero.mp h13 with h1 | h3
    · refine ⟨h1,?_⟩
      rw [h1,zero_pow (by decide : 3≠0),mul_zero,sub_zero] at hred
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hred).resolve_left (hconst (1-ι) (sub_ne_zero.mpr (Ne.symm hι1))))
    · refine ⟨?_,h3⟩
      rw [h3,zero_pow (by decide : 3≠0),mul_zero,zero_sub,neg_eq_zero] at hred
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hred).resolve_left (hconst ι hι))
  intro i
  fin_cases i
  · exact h0
  · exact h1h3.1
  · exact h2
  · exact h1h3.2
  · exact hw

theorem seedCoordinates_mem_of_vertex (s : Side) (r ι : K)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1)
    (P : Ideal (SeedRing r ι)) [P.IsPrime]
    (hE : linkageIdeal s r ι≤P) (hb : linkageB r ι∈P) (hd : linkageD r ι∈P) :
    ∀ i : Fin 5, seedCoordinate r ι i∈P := by
  let f : Poly K →+* SeedRing r ι ⧸ P := (Ideal.Quotient.mk P).comp (quotientMap r ι)
  have hH : f (smoothH ι)=0 := by
    have hh : quotientMap r ι (smoothH ι)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (by simp [equationsIdeal]))
    change Ideal.Quotient.mk P (quotientMap r ι (smoothH ι))=0
    rw [hh,map_zero]
  have hb0 : f (C r*X 1*X 3)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hb
  have hd0 : f (X 2^2)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr hd
  have hgen : ∀ j : Fin 5, f (linkageGenerator s r j)=0 := fun j =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (hE (linkageGenerator_mem s r ι j))
  have hz : ∀ i : Fin 5, f (X i)=0 :=
    @variables_zero_of_vertex K _ s r ι hr hι hι1 (SeedRing r ι ⧸ P) _ _ f hb0 hd0 hgen hH
  intro i
  exact Ideal.Quotient.eq_zero_iff_mem.mp (hz i)

theorem mapped_vertex_cover (s : Side) (r ι : K)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1)
    {S : Type*} [CommRing S] (φ : SeedRing r ι →+* S)
    (hcoord : ∃ i : Fin 5, IsUnit (φ (seedCoordinate r ι i))) :
    (linkageIdeal s r ι).map φ ⊔ Ideal.span {φ (linkageB r ι),φ (linkageD r ι)}=⊤ := by
  by_contra hne
  obtain ⟨M,hM,hJM⟩ := Ideal.exists_le_maximal
    ((linkageIdeal s r ι).map φ ⊔ Ideal.span {φ (linkageB r ι),φ (linkageD r ι)}) hne
  letI : M.IsMaximal := hM
  have hE : linkageIdeal s r ι≤M.comap φ := by
    intro q hq
    exact hJM ((le_sup_left : (linkageIdeal s r ι).map φ ≤ _) (Ideal.mem_map_of_mem φ hq))
  have hb : linkageB r ι∈M.comap φ :=
    hJM ((le_sup_right : Ideal.span {φ (linkageB r ι),φ (linkageD r ι)} ≤ _) (Ideal.subset_span (by simp)))
  have hd : linkageD r ι∈M.comap φ :=
    hJM ((le_sup_right : Ideal.span {φ (linkageB r ι),φ (linkageD r ι)} ≤ _) (Ideal.subset_span (by simp)))
  obtain ⟨i,hi⟩ := hcoord
  have hz := seedCoordinates_mem_of_vertex s r ι hr hι hι1 (M.comap φ) hE hb hd i
  exact hM.ne_top (M.eq_top_of_isUnit_mem hz hi)

theorem coordinate_isUnit (r ι : K) (t : Finset (Fin 3)) (i : Fin 3) (hi : i∈t) :
    IsUnit (algebraMap (SeedRing r ι) (SeedLocal K r ι t)
      (seedCoordinate r ι (remainingIndex i))) := by
  have hu := seedProduct_isUnit K r ι (show ({i} : Finset (Fin 3))⊆t by simpa using hi)
  simp only [baseProduct,Finset.prod_singleton] at hu
  change IsUnit (algebraMap (SeedRing r ι) (SeedLocal K r ι t)
    (quotientMap r ι (remainingInclusion K (X i)))) at hu
  simpa only [remainingInclusion,rename_X,seedCoordinate] using hu

theorem localized_vertex_cover (s : Side) (r ι : K)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1)
    (t : Finset (Fin 3)) (ht : t.Nonempty) :
    (linkageIdeal s r ι).map (algebraMap (SeedRing r ι) (SeedLocal K r ι t)) ⊔
      Ideal.span {algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageB r ι),
        algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageD r ι)}=⊤ := by
  let φ : SeedRing r ι →+* SeedLocal K r ι t :=
    algebraMap (SeedRing r ι) (SeedLocal K r ι t)
  have hcoord : ∃ i : Fin 5, IsUnit (φ (seedCoordinate r ι i)) := by
    obtain ⟨i,hi⟩ := ht
    exact ⟨remainingIndex i,coordinate_isUnit r ι t i hi⟩
  exact @mapped_vertex_cover K (inferInstance : Field K) s r ι hr hι hι1
    (SeedLocal K r ι t) (inferInstance : CommRing (SeedLocal K r ι t)) φ hcoord

end CycleQ2SeedLinkageOrbitCover

#print axioms CycleQ2SeedLinkageOrbitCover.localized_vertex_cover
end
end


/- Component: continuation_3/cylinder_bridge/SegreFactorChartExact.lean -/
section
/-! # Factor exactness on the actual complex coordinate charts

Every hypothesis of the factor sequence is discharged for the literal
smooth incidence seed at r=57 and i=sqrt(-1). The two modules are the
actual localized linkage ideals.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreFactorChartExact

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedLinkageIdeals
  CycleQ2SegreFactorSequence

abbrev Chart (s : Finset (Fin 3)) := SeedLocal ℂ 57 Complex.I s

def chartMap (s : Finset (Fin 3)) : SeedRing (57:ℂ) Complex.I →+* Chart s :=
  algebraMap (SeedRing (57:ℂ) Complex.I) (Chart s)

def leftIdeal (s : Finset (Fin 3)) : Ideal (Chart s) :=
  (linkageIdeal .left (57:ℂ) Complex.I).map (chartMap s)

def rightIdeal (s : Finset (Fin 3)) : Ideal (Chart s) :=
  (linkageIdeal .right (57:ℂ) Complex.I).map (chartMap s)

def leftSection (s : Finset (Fin 3)) (i : Fin 3) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.leftSection (57:ℂ) Complex.I i)

def rightSection (s : Finset (Fin 3)) (j : Fin 3) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.rightSection (57:ℂ) Complex.I j)

def linkage (s : Finset (Fin 3)) : Chart s :=
  chartMap s (CycleQ2SeedLinkagePrincipal.linkage (57:ℂ) Complex.I)

theorem linkage_regular (s : Finset (Fin 3)) :
    Function.Injective (fun z : Chart s => linkage s*z) := by
  apply CycleQ2LinkageIdealPrincipal.localization_mul_injective
    (Algebra.algebraMapSubmonoid (SeedRing (57:ℂ) Complex.I)
      (Submonoid.powers (baseProduct ℂ s))) (Chart s)
    (CycleQ2SeedLinkagePrincipal.linkage (57:ℂ) Complex.I)
  apply CycleQ2SeedLinkageRegular.linkage_mul_injective
  intro h
  have hh := congrArg Complex.im h
  norm_num at hh

theorem chart_ideals_pairing (s : Finset (Fin 3)) :
    leftIdeal s*rightIdeal s≤Ideal.span {linkage s} := by
  dsimp only [leftIdeal,rightIdeal,linkage]
  exact @CycleQ2SeedLinkagePrincipal.mapped_ideals_pairing ℂ inferInstance
    (Chart s) inferInstance (57:ℂ) Complex.I (chartMap s)

def factorData (s : Finset (Fin 3)) (hs : s.Nonempty) : FactorData (Chart s) where
  leftIdeal := leftIdeal s
  rightIdeal := rightIdeal s
  linkage := linkage s
  matrix := CycleQ2SegreComplexChartExact.chartMatrix s
  left := leftSection s
  right := rightSection s
  left_mem i := Ideal.mem_map_of_mem (chartMap s)
    (CycleQ2SeedLinkagePrincipal.leftSection_mem (57:ℂ) Complex.I i)
  right_mem j := Ideal.mem_map_of_mem (chartMap s)
    (CycleQ2SeedLinkagePrincipal.rightSection_mem (57:ℂ) Complex.I j)
  product i j := by
    have h := congrArg (chartMap s)
      (CycleQ2SeedLinkagePrincipal.selected_product (57:ℂ) Complex.I i j)
    simpa only [map_mul,leftSection,rightSection,linkage,
      CycleQ2SegreComplexChartExact.chartMatrix,CycleQ2SegreComplexBasepoint.matrix,
      RingHom.mapMatrix_apply,Matrix.map_apply,chartMap] using h
  ideals_product := chart_ideals_pairing s
  regular := linkage_regular s
  cofactors_zero := CycleQ2SegreComplexChartExact.chartMatrix_cofactors s
  entries_generate := CycleQ2SegreComplexChartExact.chartMatrix_entries_generate s hs

abbrev FactorSections (s : Finset (Fin 3)) :=
  (Fin 3 → leftIdeal s) × (Fin 3 → rightIdeal s)

def chartFactorMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    FactorSections s →ₗ[Chart s] Matrix (Fin 3) (Fin 3) (Chart s) :=
  factorMap (factorData s hs)

def chartGaugeMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Chart s →ₗ[Chart s] FactorSections s := gaugeMap (factorData s hs)

theorem chartFactorMap_formula (s : Finset (Fin 3)) (hs : s.Nonempty)
    (v : FactorSections s) (i j : Fin 3) :
    linkage s*chartFactorMap s hs v i j=
      (v.1 i:Chart s)*rightSection s j+leftSection s i*(v.2 j:Chart s) :=
  linkage_factorMap (factorData s hs) v i j

/-- The literal local short exact factor sequence, without a rank,
local-pivot, ideal-pairing or regularity hypothesis. -/
theorem actual_factor_sequence (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Function.Injective (chartGaugeMap s hs) ∧
    LinearMap.ker (chartFactorMap s hs)=LinearMap.range (chartGaugeMap s hs) ∧
    LinearMap.range (chartFactorMap s hs)=
      LinearMap.ker (cofactorDifferentialLinear (CycleQ2SegreComplexChartExact.chartMatrix s)) :=
  ⟨gaugeMap_injective (factorData s hs),
    ker_factorMap_eq_range_gaugeMap (factorData s hs),
    range_factorMap_eq_ker_differential (factorData s hs)⟩

end CycleQ2SegreFactorChartExact

#print axioms CycleQ2SegreFactorChartExact.linkage_regular
#print axioms CycleQ2SegreFactorChartExact.actual_factor_sequence
end
end


/- Component: continuation_3/cylinder_bridge/SegreLinkageImage.lean -/
section
/-! The actual regular linkage pairing identifies the right factor ideal
with the actual matrix image.  The three selected generators become the
literal columns; surjectivity and injectivity follow from the same
unit-ideal reconstruction that proved perfect duality. -/

noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreLinkageImage
open Matrix CycleQ2SegreFactorSequence CycleQ2SegreLinkageDuality

variable {A : Type*} [CommRing A] (F : FactorData A)

def imageMap : F.rightIdeal →ₗ[A] (Fin 3 → A) where
  toFun y i := pairing F y (leftElement F i)
  map_add' y z := by
    funext i
    exact LinearMap.congr_fun ((pairing F).map_add y z) (leftElement F i)
  map_smul' c y := by
    funext i
    exact LinearMap.congr_fun ((pairing F).map_smul c y) (leftElement F i)

theorem imageMap_selected (j : Fin 3) :
    imageMap F (rightElement F j)=F.matrix.col j := by
  funext i
  exact pairing_selected F i j

theorem right_reconstruction_ideal (y : F.rightIdeal) :
    y=∑ q, (weights F q*pairing F y (leftElement F q.1)) • rightElement F q.2 := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum,Submodule.coe_smul,smul_eq_mul,rightElement] using
    right_reconstruction F y

theorem imageMap_injective : Function.Injective (imageMap F) := by
  intro y z he
  rw [right_reconstruction_ideal F y,right_reconstruction_ideal F z]
  apply Finset.sum_congr rfl
  intro q _
  have hh := congrFun he q.1
  change pairing F y (leftElement F q.1)=pairing F z (leftElement F q.1) at hh
  rw [hh]

theorem range_imageMap : LinearMap.range (imageMap F)=LinearMap.range F.matrix.mulVecLin := by
  rw [Matrix.range_mulVecLin]
  apply le_antisymm
  · rintro _ ⟨y,rfl⟩
    rw [right_reconstruction_ideal F y,map_sum]
    apply Submodule.sum_mem
    intro q _
    rw [map_smul,imageMap_selected]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q.2))
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨rightElement F j,imageMap_selected F j⟩

def rightEquivImage : F.rightIdeal ≃ₗ[A] LinearMap.range F.matrix.mulVecLin :=
  (LinearEquiv.ofInjective (imageMap F) (imageMap_injective F)).trans
    (LinearEquiv.ofEq _ _ (range_imageMap F))

theorem rightEquivImage_apply (y : F.rightIdeal) (i : Fin 3) :
    (rightEquivImage F y).val i=pairing F y (leftElement F i) := rfl

theorem rightEquivImage_selected (j : Fin 3) :
    (rightEquivImage F (rightElement F j)).val=F.matrix.col j :=
  imageMap_selected F j

end CycleQ2SegreLinkageImage

#print axioms CycleQ2SegreLinkageImage.rightEquivImage
#print axioms CycleQ2SegreLinkageImage.rightEquivImage_selected
end
end


/- Component: continuation_3/SegreModularCorrelationChecks0_10.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric0_10 : ∀a b : Fin 3,checkBlock weights0 1 0 a b=true := by
  decide +kernel

theorem entry0_10 : checkEntry weights0 1 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights0 1 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric0_10 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_10
end


/- Component: continuation_3/SegreModularCorrelationChecks0_11.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric0_11 : ∀a b : Fin 3,checkBlock weights0 1 1 a b=true := by
  decide +kernel

theorem entry0_11 : checkEntry weights0 1 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights0 1 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric0_11 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_11
end


/- Component: continuation_3/SegreModularCorrelationChecks0_12.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric0_12 : ∀a b : Fin 3,checkBlock weights0 1 2 a b=true := by
  decide +kernel

theorem entry0_12 : checkEntry weights0 1 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights0 1 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric0_12 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_12
end


/- Component: continuation_3/SegreModularCorrelationChecks0_20.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric0_20 : ∀a b : Fin 3,checkBlock weights0 2 0 a b=true := by
  decide +kernel

theorem entry0_20 : checkEntry weights0 2 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights0 2 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric0_20 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_20
end


/- Component: continuation_3/SegreModularCorrelationChecks0_21.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric0_21 : ∀a b : Fin 3,checkBlock weights0 2 1 a b=true := by
  decide +kernel

theorem entry0_21 : checkEntry weights0 2 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights0 2 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric0_21 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_21
end


/- Component: continuation_3/SegreModularCorrelationChecks0_22.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric0_22 : ∀a b : Fin 3,checkBlock weights0 2 2 a b=true := by
  decide +kernel

theorem entry0_22 : checkEntry weights0 2 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights0 2 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric0_22 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry0_22
end


/- Component: continuation_3/SegreModularCorrelationChecks1_10.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric1_10 : ∀a b : Fin 3,checkBlock weights1 1 0 a b=true := by
  decide +kernel

theorem entry1_10 : checkEntry weights1 1 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights1 1 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric1_10 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_10
end


/- Component: continuation_3/SegreModularCorrelationChecks1_11.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric1_11 : ∀a b : Fin 3,checkBlock weights1 1 1 a b=true := by
  decide +kernel

theorem entry1_11 : checkEntry weights1 1 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights1 1 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric1_11 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_11
end


/- Component: continuation_3/SegreModularCorrelationChecks1_12.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric1_12 : ∀a b : Fin 3,checkBlock weights1 1 2 a b=true := by
  decide +kernel

theorem entry1_12 : checkEntry weights1 1 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights1 1 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric1_12 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_12
end


/- Component: continuation_3/SegreModularCorrelationChecks1_20.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric1_20 : ∀a b : Fin 3,checkBlock weights1 2 0 a b=true := by
  decide +kernel

theorem entry1_20 : checkEntry weights1 2 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights1 2 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric1_20 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_20
end


/- Component: continuation_3/SegreModularCorrelationChecks1_21.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric1_21 : ∀a b : Fin 3,checkBlock weights1 2 1 a b=true := by
  decide +kernel

theorem entry1_21 : checkEntry weights1 2 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights1 2 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric1_21 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_21
end


/- Component: continuation_3/SegreModularCorrelationChecks1_22.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric1_22 : ∀a b : Fin 3,checkBlock weights1 2 2 a b=true := by
  decide +kernel

theorem entry1_22 : checkEntry weights1 2 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights1 2 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric1_22 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry1_22
end


/- Component: continuation_3/SegreModularCorrelationChecks2_10.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric2_10 : ∀a b : Fin 3,checkBlock weights2 1 0 a b=true := by
  decide +kernel

theorem entry2_10 : checkEntry weights2 1 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights2 1 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric2_10 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_10
end


/- Component: continuation_3/SegreModularCorrelationChecks2_11.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric2_11 : ∀a b : Fin 3,checkBlock weights2 1 1 a b=true := by
  decide +kernel

theorem entry2_11 : checkEntry weights2 1 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights2 1 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric2_11 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_11
end


/- Component: continuation_3/SegreModularCorrelationChecks2_12.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric2_12 : ∀a b : Fin 3,checkBlock weights2 1 2 a b=true := by
  decide +kernel

theorem entry2_12 : checkEntry weights2 1 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights2 1 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric2_12 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_12
end


/- Component: continuation_3/SegreModularCorrelationChecks2_20.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric2_20 : ∀a b : Fin 3,checkBlock weights2 2 0 a b=true := by
  decide +kernel

theorem entry2_20 : checkEntry weights2 2 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights2 2 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric2_20 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_20
end


/- Component: continuation_3/SegreModularCorrelationChecks2_21.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric2_21 : ∀a b : Fin 3,checkBlock weights2 2 1 a b=true := by
  decide +kernel

theorem entry2_21 : checkEntry weights2 2 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights2 2 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric2_21 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_21
end


/- Component: continuation_3/SegreModularCorrelationChecks2_22.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric2_22 : ∀a b : Fin 3,checkBlock weights2 2 2 a b=true := by
  decide +kernel

theorem entry2_22 : checkEntry weights2 2 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights2 2 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric2_22 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry2_22
end


/- Component: continuation_3/SegreModularCorrelationChecks3_10.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric3_10 : ∀a b : Fin 3,checkBlock weights3 1 0 a b=true := by
  decide +kernel

theorem entry3_10 : checkEntry weights3 1 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights3 1 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric3_10 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_10
end


/- Component: continuation_3/SegreModularCorrelationChecks3_11.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric3_11 : ∀a b : Fin 3,checkBlock weights3 1 1 a b=true := by
  decide +kernel

theorem entry3_11 : checkEntry weights3 1 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights3 1 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric3_11 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_11
end


/- Component: continuation_3/SegreModularCorrelationChecks3_12.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric3_12 : ∀a b : Fin 3,checkBlock weights3 1 2 a b=true := by
  decide +kernel

theorem entry3_12 : checkEntry weights3 1 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights3 1 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric3_12 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_12
end


/- Component: continuation_3/SegreModularCorrelationChecks3_20.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric3_20 : ∀a b : Fin 3,checkBlock weights3 2 0 a b=true := by
  decide +kernel

theorem entry3_20 : checkEntry weights3 2 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights3 2 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric3_20 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_20
end


/- Component: continuation_3/SegreModularCorrelationChecks3_21.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric3_21 : ∀a b : Fin 3,checkBlock weights3 2 1 a b=true := by
  decide +kernel

theorem entry3_21 : checkEntry weights3 2 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights3 2 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric3_21 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_21
end


/- Component: continuation_3/SegreModularCorrelationChecks3_22.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric3_22 : ∀a b : Fin 3,checkBlock weights3 2 2 a b=true := by
  decide +kernel

theorem entry3_22 : checkEntry weights3 2 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights3 2 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric3_22 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry3_22
end


/- Component: continuation_3/SegreModularCorrelationChecks4_10.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric4_10 : ∀a b : Fin 3,checkBlock weights4 1 0 a b=true := by
  decide +kernel

theorem entry4_10 : checkEntry weights4 1 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights4 1 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric4_10 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_10
end


/- Component: continuation_3/SegreModularCorrelationChecks4_11.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric4_11 : ∀a b : Fin 3,checkBlock weights4 1 1 a b=true := by
  decide +kernel

theorem entry4_11 : checkEntry weights4 1 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights4 1 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric4_11 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_11
end


/- Component: continuation_3/SegreModularCorrelationChecks4_12.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric4_12 : ∀a b : Fin 3,checkBlock weights4 1 2 a b=true := by
  decide +kernel

theorem entry4_12 : checkEntry weights4 1 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights4 1 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric4_12 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_12
end


/- Component: continuation_3/SegreModularCorrelationChecks4_20.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric4_20 : ∀a b : Fin 3,checkBlock weights4 2 0 a b=true := by
  decide +kernel

theorem entry4_20 : checkEntry weights4 2 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights4 2 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric4_20 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_20
end


/- Component: continuation_3/SegreModularCorrelationChecks4_21.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric4_21 : ∀a b : Fin 3,checkBlock weights4 2 1 a b=true := by
  decide +kernel

theorem entry4_21 : checkEntry weights4 2 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights4 2 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric4_21 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_21
end


/- Component: continuation_3/SegreModularCorrelationChecks4_22.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric4_22 : ∀a b : Fin 3,checkBlock weights4 2 2 a b=true := by
  decide +kernel

theorem entry4_22 : checkEntry weights4 2 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights4 2 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric4_22 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry4_22
end


/- Component: continuation_3/SegreModularCorrelationChecks5_10.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric5_10 : ∀a b : Fin 3,checkBlock weights5 1 0 a b=true := by
  decide +kernel

theorem entry5_10 : checkEntry weights5 1 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights5 1 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric5_10 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_10
end


/- Component: continuation_3/SegreModularCorrelationChecks5_11.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric5_11 : ∀a b : Fin 3,checkBlock weights5 1 1 a b=true := by
  decide +kernel

theorem entry5_11 : checkEntry weights5 1 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights5 1 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric5_11 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_11
end


/- Component: continuation_3/SegreModularCorrelationChecks5_12.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric5_12 : ∀a b : Fin 3,checkBlock weights5 1 2 a b=true := by
  decide +kernel

theorem entry5_12 : checkEntry weights5 1 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights5 1 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric5_12 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_12
end


/- Component: continuation_3/SegreModularCorrelationChecks5_20.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric5_20 : ∀a b : Fin 3,checkBlock weights5 2 0 a b=true := by
  decide +kernel

theorem entry5_20 : checkEntry weights5 2 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights5 2 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric5_20 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_20
end


/- Component: continuation_3/SegreModularCorrelationChecks5_21.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric5_21 : ∀a b : Fin 3,checkBlock weights5 2 1 a b=true := by
  decide +kernel

theorem entry5_21 : checkEntry weights5 2 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights5 2 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric5_21 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_21
end


/- Component: continuation_3/SegreModularCorrelationChecks5_22.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric5_22 : ∀a b : Fin 3,checkBlock weights5 2 2 a b=true := by
  decide +kernel

theorem entry5_22 : checkEntry weights5 2 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights5 2 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric5_22 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry5_22
end


/- Component: continuation_3/SegreModularCorrelationChecks6_10.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_10 : ∀a b : Fin 3,checkBlock weights6 1 0 a b=true := by
  decide +kernel

theorem entry6_10 : checkEntry weights6 1 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 1 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_10 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_10
end


/- Component: continuation_3/SegreModularCorrelationChecks6_11.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_11 : ∀a b : Fin 3,checkBlock weights6 1 1 a b=true := by
  decide +kernel

theorem entry6_11 : checkEntry weights6 1 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 1 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_11 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_11
end


/- Component: continuation_3/SegreModularCorrelationChecks6_12.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_12 : ∀a b : Fin 3,checkBlock weights6 1 2 a b=true := by
  decide +kernel

theorem entry6_12 : checkEntry weights6 1 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 1 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_12 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_12
end


/- Component: continuation_3/SegreModularCorrelationChecks6_20.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_20 : ∀a b : Fin 3,checkBlock weights6 2 0 a b=true := by
  decide +kernel

theorem entry6_20 : checkEntry weights6 2 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 2 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_20 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_20
end


/- Component: continuation_3/SegreModularCorrelationChecks6_21.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_21 : ∀a b : Fin 3,checkBlock weights6 2 1 a b=true := by
  decide +kernel

theorem entry6_21 : checkEntry weights6 2 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 2 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_21 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_21
end


/- Component: continuation_3/SegreModularCorrelationChecks6_22.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_22 : ∀a b : Fin 3,checkBlock weights6 2 2 a b=true := by
  decide +kernel

theorem entry6_22 : checkEntry weights6 2 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 2 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_22 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_22
end


/- Component: continuation_3/SegreModularDetectorEntryBinding.lean -/
section
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreModularDetectorEntryBinding
open MvPolynomial CycleQ2SparseModularFunctional CycleQ2SparseGaussianPolynomial
  CycleQ2SegreModularDetectorExpressions CycleQ2SegreModularDetectorData
  CycleQ2IncidenceMonomials CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
  CycleQ2IncidenceUniversalChart CycleQ2GenericEntryCoefficientBinding

 theorem dotAction_eq_nf (W : WeightData) (r s i j a b : Fin 3) (u v : ℕ) :
    (dotAction W r s i j a b u v : F)=functional W r s
      (nf (57:F) 33 (rawSeedMatrix (57:F) i j*MvPolynomial.monomial
        (tupleExponent (a.val,u,v,14-(a.val+u+v+2*b.val),b.val)) 1)) := by
  unfold dotAction
  rw [flatActionTable_eq]
  exact CycleQ2SegreModularActionSemantics.dot_flat_action_eq_nf W r s i j a b u v

 theorem standardIndex_exponent (e : StandardIndex 14) :
    tupleExponent (e.val.1.1.val,e.val.2.1.val,e.val.2.2.val,
      14-(e.val.1.1.val+e.val.2.1.val+e.val.2.2.val+2*e.val.1.2.val),e.val.1.2.val)=
      standardExponent e := by
  ext l
  fin_cases l <;> rfl

 theorem basisMatrix_eq (i j : Fin 3) (e : StandardIndex 14) :
    CycleQ2SegreModularDetectorMatrixBinding.basisMatrix ((i,j),e)=
      CycleQ2SegreModularDetectorExpressions.basisMatrix i j
        (MvPolynomial.monomial (standardExponent e) (1:F)) := by
  funext r s
  rw [CycleQ2SegreModularDetectorMatrixBinding.basisMatrix_apply]
  simp only [CycleQ2SegreModularDetectorExpressions.basisMatrix,Prod.mk.injEq]

 theorem entry_column_eq_dot (k : Fin 7) (c : MatrixParameter) :
    (CycleQ2SegreModularDetectorMatrixBinding.detectorMatrix*entryJacobianBlock (57:F) 33) k c=
      (entryDot c.1.1 c.1.2 (weights k) c.2.val.1.1.val c.2.val.1.2.val
        c.2.val.2.1.val c.2.val.2.2.val : F) := by
  rcases c with ⟨⟨i,j⟩,e⟩
  rw [CycleQ2SegreModularDetectorMatrixBinding.detector_entry_column,basisMatrix_eq]
  have hd := firstRow_basisDifferential (rawSeedMatrix (57:F))
    (MvPolynomial.monomial (standardExponent e) (1:F))
    (fun s => (functional (weights k) 0 s).comp (nf (57:F) 33)) i j
  simp only [LinearMap.comp_apply] at hd
  rw [hd]
  symm
  rw [cast_entryDot]
  apply congrArg (signedEntry i j)
  funext s r t
  rw [dotAction_eq_nf,standardIndex_exponent]

 theorem annihilates_entry_of_checks
    (hc : ∀k : Fin 7,∀i j : Fin 3,checkEntry (weights k) i j=true) :
    CycleQ2SegreModularDetectorMatrixBinding.detectorMatrix*entryJacobianBlock (57:F) 33=0 := by
  ext k c
  rw [entry_column_eq_dot]
  have h := entryDot_zero_of_check (weights k) c.1.1 c.1.2 (hc k c.1.1 c.1.2)
    c.2.val.1.1.val c.2.val.1.2.val c.2.val.2.1.val c.2.val.2.2.val
    c.2.val.1.1.isLt c.2.val.1.2.isLt c.2.val.2.1.isLt c.2.val.2.2.isLt c.2.property
  rw [h,Nat.cast_zero]
  rfl

end CycleQ2SegreModularDetectorEntryBinding
#print axioms CycleQ2SegreModularDetectorEntryBinding.entry_column_eq_dot
#print axioms CycleQ2SegreModularDetectorEntryBinding.annihilates_entry_of_checks
end
end


/- Component: continuation_3/CurveCechGlobalGluing.lean -/
section
/-! # Augmented degree-zero exactness for the actual two-open seed complex

Compatible sections in the actual coordinate localizations glue uniquely to
the actual seed quotient. The proof uses the checked six free coordinates:
compatibility removes every possible negative base exponent. The same proof
preserves the original signed degree and produces an
actual homogeneous polynomial representative.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2CurveCechGlobalGluing

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2CurveRestriction CycleQ2CurveQuotientFiniteFree CycleQ2CurveCechTwoOpen
  CycleQ2CurveCechLocalization CycleQ2CurveCechLocalizedBasis
  CycleQ2CurveCechRestrictions CycleQ2CurveQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]

def globalCoordinates (side : Side) (r ι : R) (q : CurveRing side r ι) : (ShiftIndex side) → Laurent (R := R) :=
  fun ab => baseToLaurent R ((curveBasis R side r ι).repr q ab)

theorem globalCoordinates_injective (side : Side) (r ι : R) :
    Function.Injective (globalCoordinates R side r ι) := by
  intro p q hpq
  apply (curveBasis R side r ι).repr.injective
  apply Finsupp.ext
  intro ab
  exact baseToLaurent_injective R (congrFun hpq ab)

theorem mem_range_globalCoordinates (side : Side) (r ι : R) (p : (ShiftIndex side) → Laurent (R := R)) :
    p ∈ Set.range (globalCoordinates R side r ι) ↔ ∀ ab, HasPoles ∅ (p ab) := by
  constructor
  · rintro ⟨q,rfl⟩ ab
    exact baseToLaurent_hasPoles R _
  · intro hp
    choose a ha using fun ab => (mem_range_baseToLaurent R (p ab)).mpr (hp ab)
    refine ⟨(curveBasis R side r ι).repr.symm (Finsupp.equivFunOnFinite.symm a),?_⟩
    funext ab
    simpa only [globalCoordinates,LinearEquiv.apply_symm_apply,
      Finsupp.coe_equivFunOnFinite_symm] using ha ab

theorem localization_injective (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    Function.Injective (algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)) := by
  intro p q hpq
  apply globalCoordinates_injective R side r ι
  funext ab
  have hh := congrArg (fun z => localizedCoordinates R side r ι s z ab) hpq
  simpa only [localizedCoordinates_algebraMap,globalCoordinates] using hh

abbrev Sections (side : Side) (r ι : R) := (i : Fin 2) → CurveLocal R side r ι {i}

def pairRestriction (side : Side) (r ι : R) (i j : Fin 2) :
    CurveLocal R side r ι {i} →+* CurveLocal R side r ι {i,j} :=
  restriction R side r ι (by simp)

def secondPairRestriction (side : Side) (r ι : R) (i j : Fin 2) :
    CurveLocal R side r ι {j} →+* CurveLocal R side r ι {i,j} :=
  restriction R side r ι (by simp)

def Compatible (side : Side) (r ι : R) (q : Sections R side r ι) : Prop :=
  ∀ i j, pairRestriction R side r ι i j (q i)=secondPairRestriction R side r ι i j (q j)

theorem compatible_coordinates (side : Side) (r ι : R) (q : Sections R side r ι)
    (hq : Compatible R side r ι q) (i j : Fin 2) :
    localizedCoordinates R side r ι {i} (q i)=localizedCoordinates R side r ι {j} (q j) := by
  funext ab
  have hh := congrArg (fun z => localizedCoordinates R side r ι {i,j} z ab) (hq i j)
  simpa only [pairRestriction,secondPairRestriction,coordinates_restriction] using hh

/-- The actual coordinate opens satisfy the augmented H0 gluing property. -/
theorem existsUnique_gluing (side : Side) (r ι : R) (q : Sections R side r ι)
    (hq : Compatible R side r ι q) :
    ∃! p : CurveRing side r ι, ∀ i,
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι {i}) p=q i := by
  let c := localizedCoordinates R side r ι {0} (q 0)
  have hpoles (ab : (ShiftIndex side)) : HasPoles ∅ (c ab) := by
    intro e i _ hi
    by_cases hi0 : i=0
    · subst i
      change (localizedCoordinates R side r ι {0} (q 0) ab).coeff e=0
      rw [compatible_coordinates R side r ι q hq 0 1]
      exact localizedCoordinates_hasPoles R side r ι {1} (q 1) ab e 0 (by decide) hi
    · exact localizedCoordinates_hasPoles R side r ι {0} (q 0) ab e i (by simpa using hi0) hi
  obtain ⟨p,hp⟩ := (mem_range_globalCoordinates R side r ι c).mpr hpoles
  have hm (i : Fin 2) : algebraMap (CurveRing side r ι) (CurveLocal R side r ι {i}) p=q i := by
    apply localizedCoordinates_injective R side r ι {i}
    funext ab
    rw [localizedCoordinates_algebraMap]
    change globalCoordinates R side r ι p ab=_
    rw [hp]
    exact congrFun (compatible_coordinates R side r ι q hq 0 i) ab
  refine ⟨p,hm,?_⟩
  intro p' hp'
  exact localization_injective R side r ι {0} ((hp' 0).trans (hm 0).symm)

/-- Grading is inherited by the glued quotient class from any chart. -/
theorem gluing_preserves_grade (side : Side) (r ι : R) (q : Sections R side r ι) (p : CurveRing side r ι)
    (hp : ∀ i, algebraMap (CurveRing side r ι) (CurveLocal R side r ι {i}) p=q i)
    (g : ℤ) (hg : ∀ ab, HasDegree ab g (localizedCoordinates R side r ι {0} (q 0) ab)) :
    ∀ ab, HasDegree ab g (globalCoordinates R side r ι p ab) := by
  intro ab
  have hh := congrArg (fun z => localizedCoordinates R side r ι {0} z ab) (hp 0)
  rw [localizedCoordinates_algebraMap] at hh
  change HasDegree ab g (baseToLaurent R ((curveBasis R side r ι).repr p ab))
  rw [hh]
  exact hg ab

/-- Compatible graded local sections have an actual globally homogeneous
polynomial representative in the original four variables. -/
theorem exists_homogeneous_polynomial_gluing (side : Side) (r ι : R) (q : Sections R side r ι)
    (hq : Compatible R side r ι q) (g : ℤ)
    (hg : ∀ ab, HasDegree ab g (localizedCoordinates R side r ι {0} (q 0) ab)) :
    ∃ p : CurvePoly R, Standard side p ∧ SignedHomogeneous R p g ∧ ∀ i,
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι {i})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=q i := by
  obtain ⟨p,hp,_⟩ := existsUnique_gluing R side r ι q hq
  obtain ⟨P,hP,hPg,hPp⟩ := exists_signed_homogeneous_representative R side r ι p g
    (gluing_preserves_grade R side r ι q p hp g hg)
  exact ⟨P,hP,hPg,by simpa only [hPp] using hp⟩

end CycleQ2CurveCechGlobalGluing

#print axioms CycleQ2CurveCechGlobalGluing.existsUnique_gluing
#print axioms CycleQ2CurveCechGlobalGluing.exists_homogeneous_polynomial_gluing
end
end


/- Component: continuation_3/SeedCyclicLocalization.lean -/
section
/-! The actual diagonal action on each coordinate localization.  Homogeneous
fractions retain ideal membership when their image under the action belongs
to that ideal, by clearing a homogeneous numerator and a unit denominator. -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCyclicLocalization

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions
  CycleQ2SeedQuotientGrading CycleQ2SeedCyclicAction

variable {R : Type*} [CommRing R]

def baseScalars (ζ : R) : Fin 3 → R := ![ζ^2,ζ,1]
def baseFactor (ζ : R) (s : Finset (Fin 3)) : R := ∏ i∈s, baseScalars ζ i
def baseProductPoly (s : Finset (Fin 3)) : Poly R := remainingInclusion R (baseProduct R s)

theorem cube_root_isUnit (ζ : R) (hζ : ζ^3=1) : IsUnit ζ := by
  apply IsUnit.of_mul_eq_one (ζ^2)
  calc
    ζ*ζ^2=ζ^3 := by ring
    _=1 := hζ

theorem baseFactor_isUnit (ζ : R) (hζ : ζ^3=1) (s : Finset (Fin 3)) : IsUnit (baseFactor ζ s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseFactor]
  | @insert i s hi ih =>
    rw [baseFactor,Finset.prod_insert hi]
    apply IsUnit.mul _ ih
    fin_cases i
    · exact (cube_root_isUnit ζ hζ).pow 2
    · exact cube_root_isUnit ζ hζ
    · exact isUnit_one

theorem actionValues_remaining (ζ : R) (i : Fin 3) :
    actionValues ζ (remainingIndex i)=C (baseScalars ζ i)*X (remainingIndex i) := by
  fin_cases i <;> simp [actionValues,remainingIndex,baseScalars]

theorem polynomialAction_baseProduct (ζ : R) (s : Finset (Fin 3)) :
    polynomialAction ζ (baseProductPoly (R:=R) s)=C (baseFactor ζ s)*baseProductPoly s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseProductPoly,baseProduct,baseFactor]
  | @insert i s hi ih =>
    have hp : baseProductPoly (R:=R) (insert i s)=X (remainingIndex i)*baseProductPoly s := by
      simp [baseProductPoly,baseProduct,hi,remainingInclusion]
    have hf : baseFactor ζ (insert i s)=baseScalars ζ i*baseFactor ζ s := by
      simp [baseFactor,hi]
    rw [hp,map_mul,polynomialAction_X,actionValues_remaining,ih,hf,map_mul]
    ring

theorem seedAction_baseProduct (ζ : R) (hζ : ζ^3=1) (r ι : R) (s : Finset (Fin 3)) :
    seedAction ζ hζ r ι (algebraMap (Base R) (SeedRing r ι) (baseProduct R s))=
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (C (baseFactor ζ s))*
        algebraMap (Base R) (SeedRing r ι) (baseProduct R s) := by
  change seedAction ζ hζ r ι
    (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (baseProductPoly s))=_
  rw [seedAction_mk,polynomialAction_baseProduct,map_mul]
  rfl

theorem acted_baseProduct_isUnit (ζ : R) (hζ : ζ^3=1) (r ι : R) (s : Finset (Fin 3)) :
    IsUnit (algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (seedAction ζ hζ r ι (algebraMap (Base R) (SeedRing r ι) (baseProduct R s)))) := by
  rw [seedAction_baseProduct,map_mul]
  apply IsUnit.mul
  · exact (baseFactor_isUnit ζ hζ s).map
      (((algebraMap (SeedRing r ι) (SeedLocal R r ι s)).comp
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))).comp C)
  · exact seedProduct_isUnit R r ι (Finset.Subset.refl s)

def localAction (ζ : R) (hζ : ζ^3=1) (r ι : R) (s : Finset (Fin 3)) :
    SeedLocal R r ι s →+* SeedLocal R r ι s :=
  IsLocalization.Away.lift
    (S:=SeedLocal R r ι s) (P:=SeedLocal R r ι s)
    (g:=(algebraMap (SeedRing r ι) (SeedLocal R r ι s)).comp (seedAction ζ hζ r ι).toRingHom)
    (algebraMap (Base R) (SeedRing r ι) (baseProduct R s))
    (acted_baseProduct_isUnit ζ hζ r ι s)

@[simp] theorem localAction_algebraMap (ζ : R) (hζ : ζ^3=1) (r ι : R)
    (s : Finset (Fin 3)) (q : SeedRing r ι) :
    localAction ζ hζ r ι s (algebraMap (SeedRing r ι) (SeedLocal R r ι s) q)=
      algebraMap (SeedRing r ι) (SeedLocal R r ι s) (seedAction ζ hζ r ι q) :=
  IsLocalization.Away.lift_eq _ (acted_baseProduct_isUnit ζ hζ r ι s) q

@[simp] theorem localAction_mk (ζ : R) (hζ : ζ^3=1) (r ι : R)
    (s : Finset (Fin 3)) (p : Poly R) :
    localAction ζ hζ r ι s
      (algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p))=
      algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (polynomialAction ζ p)) := by
  rw [localAction_algebraMap,seedAction_mk]

theorem homogeneous_mem_of_action_mem [Nontrivial R] (ζ : R) (hζ : ζ^3=1)
    (r ι : R) (s : Finset (Fin 3)) (q : SeedLocal R r ι s) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g (localizedCoordinates R r ι s q ab))
    (J : Ideal (SeedLocal R r ι s)) (hTq : localAction ζ hζ r ι s q∈J) : q∈J := by
  obtain ⟨n,p,hp,hfrac⟩ := (localized_homogeneous_iff_fraction R r ι s q g).mp hq
  let φ := algebraMap (SeedRing r ι) (SeedLocal R r ι s)
  let π := Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
  let den := φ (algebraMap (Base R) (SeedRing r ι) (baseProduct R s^n))
  let u := φ (π (C (ζ^(g+baseGrade (n • openExponent s)).2.val)))
  have hden : IsUnit den := by
    dsimp [den,φ]
    simpa only [map_pow] using (seedProduct_isUnit R r ι (Finset.Subset.refl s)).pow n
  have hu : IsUnit u := (cube_root_isUnit ζ hζ).pow _ |>.map ((φ.comp π).comp C)
  have ht : localAction ζ hζ r ι s q*localAction ζ hζ r ι s den∈J := by
    rw [mul_comm (localAction ζ hζ r ι s q) (localAction ζ hζ r ι s den)]
    exact J.mul_mem_left _ hTq
  have he := congrArg (localAction ζ hζ r ι s) hfrac
  rw [map_mul,localAction_mk,polynomialAction_signedHomogeneous ζ hζ p _ hp,map_mul,map_mul] at he
  change localAction ζ hζ r ι s q*localAction ζ hζ r ι s den=u*(φ (π p)) at he
  change q*den=φ (π p) at hfrac
  rw [←hfrac] at he
  rw [he] at ht
  have hqd : q*den∈J := (J.unit_mul_mem_iff_mem hu).mp ht
  apply (J.unit_mul_mem_iff_mem hden).mp
  rw [mul_comm den q]
  exact hqd

end CycleQ2SeedCyclicLocalization

#print axioms CycleQ2SeedCyclicLocalization.localAction
#print axioms CycleQ2SeedCyclicLocalization.homogeneous_mem_of_action_mem
end
end


/- Component: continuation_3/SeedLinkageComponents.lean -/
section
/-! The literal three-component intersection for each actual linkage ideal
on every nonempty coordinate localization of the complex seed. -/

noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageComponents

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals
  CycleQ2SeedLinkagePrincipal CycleQ2SeedLinkageOrbitCover
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2SeedCechLocalizedBasis

variable {K : Type*} [Field K]

def orbitB (s : Side) (r ι : K) : SeedRing r ι :=
  match s with | .left => linkageB r ι | .right => -linkageD r ι

def orbitD (s : Side) (r ι : K) : SeedRing r ι :=
  match s with | .left => linkageD r ι | .right => -linkageB r ι

theorem linkageIdeal_eq_generic (s : Side) (r ι : K) :
    linkageIdeal s r ι=leftIdeal (linkageA r ι) (orbitB s r ι) (linkageC r ι) (orbitD s r ι) := by
  cases s
  · change Ideal.span (Set.range (fun j => quotientMap r ι
        (CycleQ2SegreSeed.linkageE (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) j)))=_
    have hfun : (fun j => quotientMap r ι
        (CycleQ2SegreSeed.linkageE (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) j))=
        CycleQ2SegreSeed.linkageE (linkageA r ι) (linkageB r ι) (linkageC r ι) (linkageD r ι) := by
      funext j
      exact map_linkageE (quotientMap r ι) _ _ _ _ j
    rw [hfun]
    rfl
  · change Ideal.span (Set.range (fun j => quotientMap r ι
        (CycleQ2SegreSeed.linkageEprime (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) j)))=_
    have hfun : (fun j => quotientMap r ι
        (CycleQ2SegreSeed.linkageEprime (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) j))=
        CycleQ2SegreSeed.linkageEprime (linkageA r ι) (linkageB r ι) (linkageC r ι) (linkageD r ι) := by
      funext j
      exact map_linkageEprime (quotientMap r ι) _ _ _ _ j
    rw [hfun,rightIdeal_eq_leftIdeal]
    rfl

theorem span_pair_neg_swap {A : Type*} [CommRing A] (b d : A) :
    Ideal.span ({-d,-b} : Set A)=Ideal.span {b,d} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      exact (Ideal.span ({b,d}:Set A)).neg_mem (Ideal.subset_span (by simp))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (Ideal.span ({b,d}:Set A)).neg_mem (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      have h : -b∈Ideal.span ({-d,-b}:Set A) := Ideal.subset_span (by simp)
      exact (Ideal.span ({-d,-b}:Set A)).neg_mem_iff.mp h
    · rw [Set.mem_singleton_iff.mp hx]
      have h : -d∈Ideal.span ({-d,-b}:Set A) := Ideal.subset_span (by simp)
      exact (Ideal.span ({-d,-b}:Set A)).neg_mem_iff.mp h

def localScalar (r ι : K) (t : Finset (Fin 3)) : K →+* SeedLocal K r ι t :=
  ((algebraMap (SeedRing r ι) (SeedLocal K r ι t)).comp (quotientMap r ι)).comp C

def localLinkageIdeal (s : Side) (r ι : K) (t : Finset (Fin 3)) : Ideal (SeedLocal K r ι t) :=
  (linkageIdeal s r ι).map (algebraMap (SeedRing r ι) (SeedLocal K r ι t))

def localComponent (s : Side) (r ι : K) (t : Finset (Fin 3)) (z : K) : Ideal (SeedLocal K r ι t) :=
  componentIdeal (localScalar r ι t z)
    (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageA r ι))
    (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitB s r ι))
    (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageC r ι))
    (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitD s r ι))

theorem localLinkageIdeal_eq_generic (s : Side) (r ι : K) (t : Finset (Fin 3)) :
    localLinkageIdeal s r ι t=
      leftIdeal (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageA r ι))
        (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitB s r ι))
        (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageC r ι))
        (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitD s r ι)) := by
  rw [localLinkageIdeal,linkageIdeal_eq_generic]
  exact @map_leftIdeal (SeedRing r ι) (SeedLocal K r ι t)
    (inferInstance : CommRing (SeedRing r ι)) (inferInstance : CommRing (SeedLocal K r ι t))
    (algebraMap (SeedRing r ι) (SeedLocal K r ι t))
    (linkageA r ι) (orbitB s r ι) (linkageC r ι) (orbitD s r ι)

theorem local_orbit_vertex_cover (s : Side) (r ι : K)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1) (t : Finset (Fin 3)) (ht : t.Nonempty) :
    localLinkageIdeal s r ι t ⊔
      Ideal.span {algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitB s r ι),
        algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitD s r ι)}=⊤ := by
  cases s
  · exact localized_vertex_cover .left r ι hr hι hι1 t ht
  · simp only [orbitB,orbitD,map_neg]
    rw [span_pair_neg_swap
      (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageB r ι))
      (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageD r ι))]
    exact localized_vertex_cover .right r ι hr hι hι1 t ht

theorem localized_linkageIdeal_eq_components (s : Side) (r ι : ℂ)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1) (t : Finset (Fin 3)) (ht : t.Nonempty) :
    @localLinkageIdeal ℂ (inferInstance : Field ℂ) s r ι t=
      (@localComponent ℂ (inferInstance : Field ℂ) s r ι t 1 ⊓
        @localComponent ℂ (inferInstance : Field ℂ) s r ι t complexRoot) ⊓
        @localComponent ℂ (inferInstance : Field ℂ) s r ι t (complexRoot^2) := by
  let φ := algebraMap (SeedRing r ι) (SeedLocal ℂ r ι t)
  let z := localScalar r ι t complexRoot
  have hz : z^2+z+1=0 := by
    simpa only [map_add (localScalar r ι t),map_pow (localScalar r ι t),
      map_one (localScalar r ι t),map_zero (localScalar r ι t)] using
      congrArg (localScalar r ι t) complexRoot_quadratic
  have hcover := @local_orbit_vertex_cover ℂ (inferInstance : Field ℂ) s r ι hr hι hι1 t ht
  rw [localLinkageIdeal_eq_generic s r ι t] at hcover ⊢
  have h := @leftIdeal_eq_components (SeedLocal ℂ r ι t)
    (inferInstance : CommRing (SeedLocal ℂ r ι t)) z (φ (linkageA r ι)) (φ (orbitB s r ι))
    (φ (linkageC r ι)) (φ (orbitD s r ι)) hz
    (@mapped_root_units (SeedLocal ℂ r ι t) (inferInstance : CommRing (SeedLocal ℂ r ι t))
      (localScalar r ι t)) hcover
  simpa only [localComponent,map_one (localScalar r ι t),map_pow (localScalar r ι t)] using h

end CycleQ2SeedLinkageComponents

#print axioms CycleQ2SeedLinkageComponents.localized_linkageIdeal_eq_components
end
end


/- Component: continuation_3/SeedLinkageModularSeed.lean -/
section
set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option Elab.async false

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSimpArgs false

namespace CycleQ2SeedLinkageModularChecks

open MvPolynomial CycleQ2IncidenceEquations CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection

open CycleQ2SparseModularPolynomial CycleQ2SeedLinkageIdeals CycleQ2SeedLinkageSections

open CycleQ2SeedLinkageReflection CycleQ2CurveRestrictionMatrixCheck CycleQ2SeedLinkageModularData

noncomputable section

variable {R : Type*} [CommRing R] [CharP R 109]

theorem seedH_value : fullValue (R:=R) CycleQ2SeedLinkageModularData.seedH = smoothH (33:R) := by

  have hc : CharP (Poly R) 109 := inferInstance

  simp only [CycleQ2SeedLinkageModularData.seedH, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg, smoothH, smoothB, smoothA]

  apply sub_eq_zero.mp

  ring_nf <;> reduce_mod_char!

theorem seedG_value : fullValue (R:=R) CycleQ2SeedLinkageModularData.seedG = CycleQ2IncidenceEquations.seedG (57:R) := by

  have hc : CharP (Poly R) 109 := inferInstance

  simp only [CycleQ2SeedLinkageModularData.seedG, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg, CycleQ2IncidenceEquations.seedG, CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG]

  apply sub_eq_zero.mp

  ring_nf <;> reduce_mod_char!

end

end CycleQ2SeedLinkageModularChecks
end


/- Component: continuation_3/cylinder_bridge/SeedLocalizedClearing.lean -/
section
/-! # Common polynomial denominators in the actual seed coordinate charts -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SeedLocalizedClearing

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis CycleQ2SeedQuotientGrading

variable (R : Type*) [CommRing R]

def openPolynomial (s : Finset (Fin 3)) : Poly R :=
  remainingInclusion R (baseProduct R s)

def openGrade (s : Finset (Fin 3)) : Grade :=
  ∑ i ∈ s, fullGrading (remainingIndex i)

def polynomialMap (r ι : R) (s : Finset (Fin 3)) : Poly R →+* SeedLocal R r ι s :=
  (algebraMap (SeedRing r ι) (SeedLocal R r ι s)).comp
    (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))

@[simp] theorem quotient_openPolynomial (r ι : R) (s : Finset (Fin 3)) :
    Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (openPolynomial R s)=
      algebraMap (Base R) (SeedRing r ι) (baseProduct R s) := rfl

/-- The actual chart denominator is homogeneous for the original grading. -/
theorem openPolynomial_homogeneous (s : Finset (Fin 3)) :
    HG (openPolynomial R s) (openGrade s) := by
  unfold openPolynomial baseProduct
  rw [map_prod]
  apply IsWeightedHomogeneous.prod
  intro i hi
  simpa [remainingInclusion] using isWeightedHomogeneous_X R fullGrading (remainingIndex i)

def signedGradeHom : Grade →+ LaurentGrade where
  toFun := signedGrade
  map_zero' := rfl
  map_add' a b := by
    apply Prod.ext
    · exact Nat.cast_add _ _
    · rfl

theorem signed_openGrade : ∀ s : Finset (Fin 3),
    signedGrade (openGrade s)=baseGrade (openExponent s) := by decide

theorem signed_openGrade_nsmul (s : Finset (Fin 3)) (n : ℕ) :
    signedGrade (n • openGrade s)=baseGrade (n • openExponent s) := by
  change signedGradeHom (n • openGrade s)=_
  rw [map_nsmul]
  change n • signedGrade (openGrade s)=_
  rw [signed_openGrade,map_nsmul]

/-- Nine arbitrary actual local entries can be cleared with one power of
the chart denominator and lifted to the original polynomial ring. -/
theorem exists_common_polynomial_denominator (r ι : R) (s : Finset (Fin 3))
    (N : Matrix (Fin 3) (Fin 3) (SeedLocal R r ι s)) :
    ∃ (n : ℕ) (P : Matrix (Fin 3) (Fin 3) (Poly R)),
      ∀ i j, polynomialMap R r ι s (P i j)=
        polynomialMap R r ι s (openPolynomial R s ^ n)*N i j := by
  let d : SeedRing r ι := algebraMap (Base R) (SeedRing r ι) (baseProduct R s)
  obtain ⟨den,hden⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers d) (fun q : Fin 3 × Fin 3 => N q.1 q.2)
  choose a ha using hden
  obtain ⟨n,hn⟩ := den.property
  choose P hP using fun q : Fin 3 × Fin 3 =>
    Ideal.Quotient.mk_surjective (a q)
  refine ⟨n,fun i j => P (i,j),?_⟩
  intro i j
  have hh := ha (i,j)
  change algebraMap (SeedRing r ι) (SeedLocal R r ι s) (a (i,j))=
    (den : SeedRing r ι) • N i j at hh
  rw [← hP (i,j),← hn] at hh
  change algebraMap (SeedRing r ι) (SeedLocal R r ι s)
    (Ideal.Quotient.mk _ (P (i,j)))=(d^n) • N i j at hh
  rw [Algebra.smul_def (R := SeedRing r ι) (A := SeedLocal R r ι s)] at hh
  change polynomialMap R r ι s (P (i,j))=
    algebraMap (SeedRing r ι) (SeedLocal R r ι s) (d^n)*N i j at hh
  simpa only [polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial,d] using hh

end CycleQ2SeedLocalizedClearing

#print axioms CycleQ2SeedLocalizedClearing.exists_common_polynomial_denominator
#print axioms CycleQ2SeedLocalizedClearing.openPolynomial_homogeneous
end
end


/- Component: continuation_3/cylinder_bridge/SegreCechConnecting.lean -/
section
/-! # The actual Čech connecting obstruction for the Segre cofactor map

Local preimages of a global cofactor variation differ by sections of the
actual cofactor-differential kernel. Their overlap differences form a Čech
cocycle. It is a kernel-valued boundary exactly when the variation admits a
global matrix preimage. The crucial gluing step uses the proved augmented
complex of the literal seed localizations, not an assumed sheaf exactness.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SegreCechConnecting

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechGlobalGluing

variable (R : Type*) [CommRing R] [Nontrivial R]

abbrev GlobalMatrix (r ι : R) := Matrix (Fin 3) (Fin 3) (SeedRing r ι)
abbrev LocalMatrices (r ι : R) := (i : Fin 3) → Matrix (Fin 3) (Fin 3) (SeedLocal R r ι {i})

def localizeMatrix (r ι : R) (s : Finset (Fin 3)) (M : GlobalMatrix R r ι) :
    Matrix (Fin 3) (Fin 3) (SeedLocal R r ι s) :=
  (algebraMap (SeedRing r ι) (SeedLocal R r ι s)).mapMatrix M

theorem restrict_localizeMatrix (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (M : GlobalMatrix R r ι) :
    (restriction R r ι hst).mapMatrix (localizeMatrix R r ι s M)=
      localizeMatrix R r ι t M := by
  ext k l
  exact restriction_algebraMap R r ι hst (M k l)

theorem restriction_comp (r ι : R) {s t u : Finset (Fin 3)}
    (hst : s ⊆ t) (htu : t ⊆ u) (p : SeedLocal R r ι s) :
    restriction R r ι htu (restriction R r ι hst p)=
      restriction R r ι (hst.trans htu) p := by
  apply localizedCoordinates_injective R r ι u
  funext ab
  simp only [coordinates_restriction]

theorem cofactorDifferential_sub {A : Type*} [CommRing A]
    (M N K : Matrix (Fin 3) (Fin 3) A) :
    cofactorDifferential M (N-K)=cofactorDifferential M N-cofactorDifferential M K :=
  map_sub (cofactorDifferentialLinear M) N K

def overlapDifference (r ι : R) (N : LocalMatrices R r ι) (i j : Fin 3) :
    Matrix (Fin 3) (Fin 3) (SeedLocal R r ι {i,j}) :=
  (secondPairRestriction R r ι i j).mapMatrix (N j)-
    (pairRestriction R r ι i j).mapMatrix (N i)

def HasLocalLift (r ι : R) (M C : GlobalMatrix R r ι) (N : LocalMatrices R r ι) : Prop :=
  ∀ i, cofactorDifferential (localizeMatrix R r ι {i} M) (N i)=
    localizeMatrix R r ι {i} C

/-- The overlap differences lie in the kernel of the literal cofactor map. -/
theorem overlapDifference_kernel (r ι : R) (M C : GlobalMatrix R r ι)
    (N : LocalMatrices R r ι) (hN : HasLocalLift R r ι M C N) (i j : Fin 3) :
    cofactorDifferential (localizeMatrix R r ι {i,j} M)
      (overlapDifference R r ι N i j)=0 := by
  have hi := map_cofactorDifferential (B := SeedLocal R r ι {i,j}) (pairRestriction R r ι i j)
    (localizeMatrix R r ι {i} M) (N i)
  have hj := map_cofactorDifferential (B := SeedLocal R r ι {i,j}) (secondPairRestriction R r ι i j)
    (localizeMatrix R r ι {j} M) (N j)
  rw [hN i] at hi
  rw [hN j] at hj
  simp only [pairRestriction,secondPairRestriction,restrict_localizeMatrix] at hi hj
  simp only [overlapDifference,cofactorDifferential_sub,pairRestriction,secondPairRestriction]
  rw [← hj,← hi,sub_self]

/-- The actual three-open cocycle identity, after canonical restriction to
the triple overlap. -/
theorem overlapDifference_cocycle (r ι : R) (N : LocalMatrices R r ι) :
    (restriction R r ι (show ({0,1} : Finset (Fin 3)) ⊆ Finset.univ by decide)).mapMatrix
        (overlapDifference R r ι N 0 1) -
      (restriction R r ι (show ({0,2} : Finset (Fin 3)) ⊆ Finset.univ by decide)).mapMatrix
        (overlapDifference R r ι N 0 2) +
      (restriction R r ι (show ({1,2} : Finset (Fin 3)) ⊆ Finset.univ by decide)).mapMatrix
        (overlapDifference R r ι N 1 2)=0 := by
  ext k l
  change restriction R r ι (show ({0,1} : Finset (Fin 3)) ⊆ Finset.univ by decide)
      (secondPairRestriction R r ι 0 1 (N 1 k l)-pairRestriction R r ι 0 1 (N 0 k l)) - restriction R r ι (show ({0,2} : Finset (Fin 3)) ⊆ Finset.univ by decide)
      (secondPairRestriction R r ι 0 2 (N 2 k l)-pairRestriction R r ι 0 2 (N 0 k l)) + restriction R r ι (show ({1,2} : Finset (Fin 3)) ⊆ Finset.univ by decide)
      (secondPairRestriction R r ι 1 2 (N 2 k l)-pairRestriction R r ι 1 2 (N 1 k l))=0
  simp only [map_sub,pairRestriction,secondPairRestriction,restriction_comp]
  abel

def KernelBoundary (r ι : R) (M : GlobalMatrix R r ι) (N : LocalMatrices R r ι) : Prop :=
  ∃ K : LocalMatrices R r ι,
    (∀ i, cofactorDifferential (localizeMatrix R r ι {i} M) (K i)=0) ∧
    ∀ i j, overlapDifference R r ι N i j=overlapDifference R r ι K i j

/-- Entrywise augmented gluing for the actual nine matrix coefficients. -/
theorem exists_matrix_gluing (r ι : R) (Q : LocalMatrices R r ι)
    (hQ : ∀ i j, (pairRestriction R r ι i j).mapMatrix (Q i)=
      (secondPairRestriction R r ι i j).mapMatrix (Q j)) :
    ∃ P : GlobalMatrix R r ι, ∀ i, localizeMatrix R r ι {i} P=Q i := by
  have hc (k l : Fin 3) : Compatible R r ι (fun i => Q i k l) := by
    intro i j
    exact congrArg (fun T => T k l) (hQ i j)
  choose P hP using fun k l => (existsUnique_gluing R r ι (fun i => Q i k l) (hc k l)).exists
  refine ⟨P,?_⟩
  intro i
  ext k l
  exact hP k l i

theorem global_differential_of_local (r ι : R) (M C P : GlobalMatrix R r ι)
    (hP : cofactorDifferential (localizeMatrix R r ι {0} M)
      (localizeMatrix R r ι {0} P)=localizeMatrix R r ι {0} C) :
    cofactorDifferential M P=C := by
  have hh := map_cofactorDifferential (B := SeedLocal R r ι {0})
    (algebraMap (SeedRing r ι) (SeedLocal R r ι {0})) M P
  change localizeMatrix R r ι {0} (cofactorDifferential M P)=
    cofactorDifferential (localizeMatrix R r ι {0} M) (localizeMatrix R r ι {0} P) at hh
  rw [hP] at hh
  ext k l
  apply localization_injective R r ι {0}
  exact congrArg (fun T => T k l) hh

/-- The zero-class criterion for the actual connecting obstruction. No rank
bound, global preimage, or cohomology vanishing is assumed. -/
theorem kernelBoundary_iff_global_lift (r ι : R) (M C : GlobalMatrix R r ι)
    (N : LocalMatrices R r ι) (hN : HasLocalLift R r ι M C N) :
    KernelBoundary R r ι M N ↔ ∃ P : GlobalMatrix R r ι, cofactorDifferential M P=C := by
  constructor
  · rintro ⟨K,hK,hNK⟩
    let Q : LocalMatrices R r ι := fun i => N i-K i
    have hQ (i j : Fin 3) : (pairRestriction R r ι i j).mapMatrix (Q i)=
        (secondPairRestriction R r ι i j).mapMatrix (Q j) := by
      ext k l
      have hh := congrArg (fun T => T k l) (hNK i j)
      change secondPairRestriction R r ι i j (N j k l)-pairRestriction R r ι i j (N i k l)=
        secondPairRestriction R r ι i j (K j k l)-pairRestriction R r ι i j (K i k l) at hh
      change pairRestriction R r ι i j (N i k l-K i k l)=
        secondPairRestriction R r ι i j (N j k l-K j k l)
      rw [map_sub,map_sub]
      linear_combination -hh
    obtain ⟨P,hP⟩ := exists_matrix_gluing R r ι Q hQ
    refine ⟨P,global_differential_of_local R r ι M C P ?_⟩
    rw [hP 0]
    change cofactorDifferential _ (N 0-K 0)=_
    rw [cofactorDifferential_sub,hN 0,hK 0,sub_zero]
  · rintro ⟨P,hP⟩
    let K : LocalMatrices R r ι := fun i => N i-localizeMatrix R r ι {i} P
    refine ⟨K,?_,?_⟩
    · intro i
      change cofactorDifferential _ (N i-localizeMatrix R r ι {i} P)=0
      rw [cofactorDifferential_sub,hN i]
      have hh := map_cofactorDifferential (B := SeedLocal R r ι {i})
        (algebraMap (SeedRing r ι) (SeedLocal R r ι {i})) M P
      rw [hP] at hh
      change localizeMatrix R r ι {i} C=cofactorDifferential
        (localizeMatrix R r ι {i} M) (localizeMatrix R r ι {i} P) at hh
      rw [← hh,sub_self]
    · intro i j
      ext k l
      have hi := restriction_algebraMap R r ι
        (show ({i} : Finset (Fin 3)) ⊆ {i,j} by simp) (P k l)
      have hj := restriction_algebraMap R r ι
        (show ({j} : Finset (Fin 3)) ⊆ {i,j} by simp) (P k l)
      change secondPairRestriction R r ι i j (N j k l)-pairRestriction R r ι i j (N i k l) = secondPairRestriction R r ι i j
        (N j k l-algebraMap (SeedRing r ι) (SeedLocal R r ι {j}) (P k l))-
        pairRestriction R r ι i j
          (N i k l-algebraMap (SeedRing r ι) (SeedLocal R r ι {i}) (P k l))
      simp only [map_sub,pairRestriction,secondPairRestriction,hi,hj]
      abel

end CycleQ2SegreCechConnecting

#print axioms CycleQ2SegreCechConnecting.overlapDifference_kernel
#print axioms CycleQ2SegreCechConnecting.overlapDifference_cocycle
#print axioms CycleQ2SegreCechConnecting.kernelBoundary_iff_global_lift
end
end


/- Component: continuation_3/SegreModularCorrelationChecks.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SparseModularFunctional CycleQ2SegreModularDetectorData
  CycleQ2SegreModularDetectorExpressions

theorem checkEntry_first_row (W : WeightData) (j : Fin 3) :
    checkEntry W 0 j=true := by
  have hz (a b u v : ℕ) : entryDot 0 j W a b u v=0 := by
    fin_cases j <;> rfl
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  apply List.all_eq_true.mpr
  intro u hu
  apply List.all_eq_true.mpr
  intro v hv
  simp [hz]

theorem all_entry_checks (k : Fin 7) (i j : Fin 3) :
    checkEntry (weights k) i j=true := by
  fin_cases k <;> fin_cases i <;> fin_cases j
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry0_10
  · exact entry0_11
  · exact entry0_12
  · exact entry0_20
  · exact entry0_21
  · exact entry0_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry1_10
  · exact entry1_11
  · exact entry1_12
  · exact entry1_20
  · exact entry1_21
  · exact entry1_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry2_10
  · exact entry2_11
  · exact entry2_12
  · exact entry2_20
  · exact entry2_21
  · exact entry2_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry3_10
  · exact entry3_11
  · exact entry3_12
  · exact entry3_20
  · exact entry3_21
  · exact entry3_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry4_10
  · exact entry4_11
  · exact entry4_12
  · exact entry4_20
  · exact entry4_21
  · exact entry4_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry5_10
  · exact entry5_11
  · exact entry5_12
  · exact entry5_20
  · exact entry5_21
  · exact entry5_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry6_10
  · exact entry6_11
  · exact entry6_12
  · exact entry6_20
  · exact entry6_21
  · exact entry6_22

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.all_entry_checks
end


/- Component: continuation_3/CurveCoordinateCover.lean -/
section
/-! # The two base-coordinate opens cover each actual projective curve -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveCoordinateCover

open MvPolynomial CycleQ2CurveRestriction

variable {R : Type*} [CommRing R]

theorem zero_coordinates {S : Type*} [CommRing S] [IsDomain S]
    (side : Side) (r ι : R) (ψ : CurvePoly R →+* S)
    (hQ : ψ (quadric side r)=0) (hH : ψ (cubic side r ι)=0)
    (h1 : ψ (X 1)=0) (h3 : ψ (X 3)=0) : ∀ j : Fin 4,ψ (X j)=0 := by
  cases side
  · have h0 : ψ (X 0)=0 := by
      apply eq_zero_of_pow_eq_zero (n:=2)
      simpa only [quadric,map_sub,map_mul,map_pow,h1,h3,mul_zero,sub_zero] using hQ
    have h2 : ψ (X 2)=0 := by
      apply eq_zero_of_pow_eq_zero (n:=3)
      simpa only [cubic,map_add,map_sub,map_mul,map_pow,h0,h1,h3,zero_mul,mul_zero,
        zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),add_zero,sub_zero] using hH
    intro j
    fin_cases j <;> assumption
  · have h0 : ψ (X 0)=0 := by
      apply eq_zero_of_pow_eq_zero (n:=3)
      simpa only [cubic,map_add,map_sub,map_mul,map_pow,h1,h3,zero_mul,mul_zero,
        zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),add_zero,sub_zero] using hH
    have h2 : ψ (X 2)=0 := by
      apply eq_zero_of_pow_eq_zero (n:=2)
      simpa only [quadric,map_add,map_pow,h0,zero_pow (by decide : 2≠0),add_zero] using hQ
    intro j
    fin_cases j <;> assumption

def coordinate (side : Side) (r ι : R) (j : Fin 4) : CurveRing side r ι :=
  Ideal.Quotient.mk _ (X j)

/-- The statement holds at every relevant prime, not just closed points. -/
theorem prime_cover (side : Side) (r ι : R) (P : Ideal (CurveRing side r ι))
    (hP : P.IsPrime) (hrelevant : ∃ j,coordinate side r ι j∉P) :
    coordinate side r ι 1∉P ∨ coordinate side r ι 3∉P := by
  letI : P.IsPrime := hP
  by_contra hn
  have h1 : coordinate side r ι 1∈P := by tauto
  have h3 : coordinate side r ι 3∈P := by tauto
  let ψ : CurvePoly R →+* (CurveRing side r ι ⧸ P) :=
    (Ideal.Quotient.mk P).comp (Ideal.Quotient.mk (curveIdeal side r ι))
  have hQ : ψ (quadric side r)=0 := by
    have hz : Ideal.Quotient.mk (curveIdeal side r ι) (quadric side r)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [curveIdeal]))
    change Ideal.Quotient.mk P (Ideal.Quotient.mk _ (quadric side r))=0
    rw [hz,map_zero]
  have hH : ψ (cubic side r ι)=0 := by
    have hz : Ideal.Quotient.mk (curveIdeal side r ι) (cubic side r ι)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [curveIdeal]))
    change Ideal.Quotient.mk P (Ideal.Quotient.mk _ (cubic side r ι))=0
    rw [hz,map_zero]
  have hz1 : ψ (X 1)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr h1
  have hz3 : ψ (X 3)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr h3
  have hz : ∀ j : Fin 4, ψ (X j)=0 :=
    zero_coordinates (R:=R) (S:=CurveRing side r ι ⧸ P) side r ι ψ hQ hH hz1 hz3
  obtain ⟨j,hj⟩ := hrelevant
  exact hj (Ideal.Quotient.eq_zero_iff_mem.mp (hz j))

end CycleQ2CurveCoordinateCover

#print axioms CycleQ2CurveCoordinateCover.prime_cover
end
end


/- Component: continuation_3/CurvePairGluing.lean -/
section
/-! # Two-chart gluing with one explicit overlap equality -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurvePairGluing

open CycleQ2CurveRestriction CycleQ2CurveQuotientFiniteFree
  CycleQ2CurveCechTwoOpen CycleQ2CurveCechLocalizedBasis
  CycleQ2CurveCechRestrictions CycleQ2CurveQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]

def sections (side : Side) (r ι : R)
    (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1}) :
    CycleQ2CurveCechGlobalGluing.Sections R side r ι :=
  Fin.cons q0 (Fin.cons q1 (fun i => Fin.elim0 i))

@[simp] theorem sections_zero (side : Side) (r ι : R)
    (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1}) :
    sections R side r ι q0 q1 0=q0 := rfl

@[simp] theorem sections_one (side : Side) (r ι : R)
    (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1}) :
    sections R side r ι q0 q1 1=q1 := rfl

theorem compatible (side : Side) (r ι : R)
    (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1})
    (h : restriction R side r ι (show ({0}:Finset (Fin 2))⊆{0,1} by decide) q0=
      restriction R side r ι (show ({1}:Finset (Fin 2))⊆{0,1} by decide) q1) :
    CycleQ2CurveCechGlobalGluing.Compatible R side r ι (sections R side r ι q0 q1) := by
  have hc : localizedCoordinates R side r ι {0} q0=localizedCoordinates R side r ι {1} q1 := by
    funext ab
    have hh := congrArg (fun z => localizedCoordinates R side r ι {0,1} z ab) h
    simpa only [coordinates_restriction] using hh
  intro i j
  apply localizedCoordinates_injective R side r ι {i,j}
  funext ab
  simp only [CycleQ2CurveCechGlobalGluing.pairRestriction,
    CycleQ2CurveCechGlobalGluing.secondPairRestriction,coordinates_restriction]
  fin_cases i <;> fin_cases j
  · rfl
  · change localizedCoordinates R side r ι {0} q0 ab=
      localizedCoordinates R side r ι {1} q1 ab
    exact congrFun hc ab
  · change localizedCoordinates R side r ι {1} q1 ab=
      localizedCoordinates R side r ι {0} q0 ab
    exact (congrFun hc ab).symm
  · rfl

theorem exists_homogeneous_gluing (side : Side) (r ι : R)
    (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1})
    (h : restriction R side r ι (show ({0}:Finset (Fin 2))⊆{0,1} by decide) q0=
      restriction R side r ι (show ({1}:Finset (Fin 2))⊆{0,1} by decide) q1)
    (g : ℤ) (hg : ∀ ab,HasDegree ab g (localizedCoordinates R side r ι {0} q0 ab)) :
    ∃ p : CurvePoly R, Standard side p ∧ SignedHomogeneous R p g ∧
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι {0})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=q0 ∧
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι {1})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=q1 := by
  have hg0 : ∀ ab,HasDegree ab g (localizedCoordinates R side r ι {0}
      (sections R side r ι q0 q1 0) ab) := by
    simpa only [sections_zero] using hg
  obtain ⟨p,hp,hg',he⟩ := CycleQ2CurveCechGlobalGluing.exists_homogeneous_polynomial_gluing
    R side r ι (sections R side r ι q0 q1) (compatible R side r ι q0 q1 h) g hg0
  refine ⟨p,hp,hg',?_,?_⟩
  · simpa only [sections_zero] using he 0
  · simpa only [sections_one] using he 1

end CycleQ2CurvePairGluing

#print axioms CycleQ2CurvePairGluing.exists_homogeneous_gluing
end
end


/- Component: continuation_3/cylinder_bridge/SeedHomogeneousDenominator.lean -/
section
/-! # Common homogeneous numerators on the actual coordinate charts

A finite family of actual homogeneous localized sections admits one common
coordinate-product denominator, with the expected shifted numerator grades.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedHomogeneousDenominator

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedQuotientGrading CycleQ2SeedLocalizedClearing

variable (R : Type*) [CommRing R] [Nontrivial R]

/-- Common denominators preserve the original weighted degree and character,
not merely an abstract grading of a chosen quotient basis. -/
theorem exists_common_homogeneous_denominator {I : Type*} [Fintype I]
    (r ι : R) (s : Finset (Fin 3)) (g : I → Grade)
    (z : I → SeedLocal R r ι s)
    (hz : ∀ i ab, HasGrade ab (signedGrade (g i)) (localizedCoordinates R r ι s (z i) ab)) :
    ∃ (n : ℕ) (P : I → Poly R),
      (∀ i, HG (P i) (n • openGrade s+g i)) ∧
      ∀ i, polynomialMap R r ι s (P i)=
        polynomialMap R r ι s (openPolynomial R s^n)*z i := by
  classical
  choose n P hP he using fun i =>
    (localized_homogeneous_iff_fraction R r ι s (z i) (signedGrade (g i))).mp (hz i)
  let N := ∑ i, n i
  have hn (i : I) : n i≤N :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hg (i : I) : HG (P i) (n i • openGrade s+g i) := by
    apply (signedHomogeneous_iff R (P i) _).mp
    have hgrade : signedGrade (n i • openGrade s+g i)=
        signedGrade (g i)+baseGrade (n i • openExponent s) := by
      change signedGradeHom (n i • openGrade s+g i)=_
      rw [map_add]
      change signedGrade (n i • openGrade s)+signedGrade (g i)=_
      rw [signed_openGrade_nsmul,add_comm]
    rw [hgrade]
    exact hP i
  let Q : I → Poly R := fun i => openPolynomial R s^(N-n i)*P i
  refine ⟨N,Q,?_,?_⟩
  · intro i
    have hh := ((openPolynomial_homogeneous R s).pow (N-n i)).mul (hg i)
    have hgrade : (N-n i) • openGrade s+(n i • openGrade s+g i)=N • openGrade s+g i := by
      rw [← add_assoc,← add_nsmul,Nat.sub_add_cancel (hn i)]
    exact hgrade ▸ hh
  · intro i
    let f := polynomialMap R r ι s
    have hden : algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (algebraMap (Base R) (SeedRing r ι) (baseProduct R s^n i))=
        f (openPolynomial R s^n i) := by
      simp only [f,polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial]
    have hei := he i
    rw [hden] at hei
    change z i*f (openPolynomial R s^n i)=f (P i) at hei
    change f (openPolynomial R s^(N-n i)*P i)=f (openPolynomial R s^N)*z i
    calc
      _ = f (openPolynomial R s)^(N-n i)*(z i*f (openPolynomial R s)^n i) := by
        rw [map_mul,← hei,map_pow,map_pow]
      _ = f (openPolynomial R s)^((N-n i)+n i)*z i := by rw [pow_add]; ring
      _ = f (openPolynomial R s^N)*z i := by rw [Nat.sub_add_cancel (hn i),map_pow]

end CycleQ2SeedHomogeneousDenominator

#print axioms CycleQ2SeedHomogeneousDenominator.exists_common_homogeneous_denominator
end
end


/- Component: continuation_3/cylinder_bridge/SeedLinkageGrading.lean -/
section
/-! # Homogeneous projection in the actual linkage ideals

The actual polynomial preimage of each linkage ideal is homogeneous for
the original weighted degree and cubic character. The same projection
property holds after localization at any coordinate product: clearing a
power of the homogeneous denominator reduces it to polynomial projection.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageGrading

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2CurveRestriction
  CycleQ2SeedLinkageIdeals CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedLocalizedClearing CycleQ2WeightedComponent

variable {R : Type*} [CommRing R]

local instance : GradedAlgebra (weightedHomogeneousSubmodule R fullGrading) :=
  MvPolynomial.weightedGradedAlgebra R fullGrading

def polynomialIdeal (side : Side) (r : R) : Ideal (Poly R) :=
  Ideal.span (Set.range (linkageGenerator side r))

theorem polynomialIdeal_homogeneous (side : Side) (r : R) :
    (polynomialIdeal side r).IsHomogeneous (weightedHomogeneousSubmodule R fullGrading) := by
  apply Ideal.homogeneous_span
  rintro p ⟨j,rfl⟩
  exact ⟨(generatorDegree j,(generatorCharacter j:ZMod 3)),linkageGenerator_homogeneous side r j⟩

theorem polynomialIdeal_map (side : Side) (r ι : R) :
    (polynomialIdeal side r).map
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))=linkageIdeal side r ι := by
  unfold polynomialIdeal linkageIdeal
  rw [Ideal.map_span,← Set.range_comp]
  rfl

theorem polynomial_preimage_homogeneous (side : Side) (r ι : R) :
    ((linkageIdeal side r ι).comap
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))).IsHomogeneous
      (weightedHomogeneousSubmodule R fullGrading) := by
  rw [← polynomialIdeal_map side r ι,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot,Ideal.mk_ker]
  exact (polynomialIdeal_homogeneous side r).sup
    (CycleQ2SegreWeightedProjection.equationsIdeal_homogeneous r ι)

/-- Projection preserves membership in the actual quotient ideal. -/
theorem quotient_component_mem (side : Side) (r ι : R) (p : Poly R) (d : Grade)
    (hp : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p ∈
      linkageIdeal side r ι) :
    Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (weightedHomogeneousComponent fullGrading d p) ∈ linkageIdeal side r ι :=
  weightedHomogeneousComponent_mem_of_mem R fullGrading
    (polynomial_preimage_homogeneous side r ι) hp d

/-- Localized ideal membership survives selection of any weighted-degree
and character component of a polynomial numerator. -/
theorem localized_component_mem (side : Side) (r ι : R) (s : Finset (Fin 3))
    (p : Poly R) (d : Grade)
    (hp : polynomialMap R r ι s p ∈ (linkageIdeal side r ι).map
      (algebraMap (SeedRing r ι) (SeedLocal R r ι s))) :
    polynomialMap R r ι s (weightedHomogeneousComponent fullGrading d p) ∈
      (linkageIdeal side r ι).map
        (algebraMap (SeedRing r ι) (SeedLocal R r ι s)) := by
  let den : SeedRing r ι := algebraMap (Base R) (SeedRing r ι) (baseProduct R s)
  obtain ⟨z,hz,hzp⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers den)
      (SeedLocal R r ι s) (linkageIdeal side r ι)
      (Ideal.Quotient.mk _ p)).mp hp
  obtain ⟨n,hn⟩ := hz
  have hpre : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (openPolynomial R s^n*p) ∈ linkageIdeal side r ι := by
    rw [map_mul,map_pow,quotient_openPolynomial]
    rw [← hn] at hzp
    exact hzp
  have hc := quotient_component_mem side r ι (openPolynomial R s^n*p)
    (n • openGrade s+d) hpre
  rw [component_mul_left fullGrading (openPolynomial R s^n) p
    (n • openGrade s) d ((openPolynomial_homogeneous R s).pow n)] at hc
  have hl := Ideal.mem_map_of_mem (algebraMap (SeedRing r ι) (SeedLocal R r ι s)) hc
  change polynomialMap R r ι s
    (openPolynomial R s^n*weightedHomogeneousComponent fullGrading d p) ∈ _ at hl
  rw [map_mul] at hl
  have hu : IsUnit (polynomialMap R r ι s (openPolynomial R s^n)) := by
    have hh := IsLocalization.map_units (SeedLocal R r ι s)
      (⟨den^n,⟨n,rfl⟩⟩ : Submonoid.powers den)
    simpa only [polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial,den] using hh
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hl

end CycleQ2SeedLinkageGrading

#print axioms CycleQ2SeedLinkageGrading.polynomial_preimage_homogeneous
#print axioms CycleQ2SeedLinkageGrading.localized_component_mem
end
end


