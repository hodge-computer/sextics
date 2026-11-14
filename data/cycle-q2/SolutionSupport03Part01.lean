import Proposal.GeometricCartierOrbit
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

/-! Components extracted from SolutionSupport03.lean, in their original order.
See solution.md for the mathematical and verification status. -/

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

end CycleQ2SeedCyclicAction

#print axioms CycleQ2SeedCyclicAction.polynomialAction_homogeneous
#print axioms CycleQ2SeedCyclicAction.seedAction
end
end


