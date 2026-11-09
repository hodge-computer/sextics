import Proposal.SymmetricTraceEndpoint
import Proposal.CubicSelectorSource
import HodgeComputer.Constructions.ResidueTransport.CoordinateIndependence

/-!
# The ratio-chart current and the actual protected primitive

All coordinates and derivations in this file belong to the existing
function field of the protected reflection chart.  In the ratio chart
`b=r, c=t, d=s*t`, the volume is `-t dt wedge dr wedge ds`.  The source
therefore acquires the factor `-t`.  The three current coefficients are
transported with that Jacobian before the primitive is assembled.

The last constructor accepts a selector current and two literal finite
trace matches, retaining the moving normal origin `w=u-beta`. It does
not construct the moving-point extension or prove either source trace.
-/

noncomputable section

namespace SymmetricRatioCurrent

open MvPolynomial WeightedPrimitiveTransport SymmetricAffineField
open SymmetricPrimitiveEndpoint SymmetricTraceEndpoint CubicTraceDescent
open HoldoutConstruction
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def t : FunctionField := weightedMap (X 2)
def d : FunctionField := weightedMap (X 3)

theorem tangent_weighted (i : Fin 4) (p : Poly) :
    tangent i (weightedMap p) = weightedMap (pderiv i.castSucc p)-
      weightedMap (pderiv i.castSucc rawWeighted)/normal*weightedMap (pderiv 4 p) :=
  chartTangent_squareLift quotient quotient_surjective quotient_kernel
    SymmetricAffineField.normal_nonzero i p

theorem tangent_coordinate (i j : Fin 4) :
    tangent i (weightedMap (X j.castSucc)) = if j = i then 1 else 0 := by
  rw [tangent_weighted]
  have hj : j.castSucc ≠ (4 : Fin 5) := Fin.castSucc_ne_last j
  simp [pderiv_X, Pi.single_apply, hj, eq_comm]

theorem tangent_t (i : Fin 4) : tangent i t = if i = 2 then 1 else 0 := by
  simpa only [t, show (2 : Fin 4).castSucc = (2 : Fin 5) from by decide,
    eq_comm] using tangent_coordinate i 2

theorem tangent_d (i : Fin 4) : tangent i d = if i = 3 then 1 else 0 := by
  simpa only [d, show (3 : Fin 4).castSucc = (3 : Fin 5) from by decide,
    eq_comm] using tangent_coordinate i 3

theorem t_nonzero : t ≠ 0 := by
  intro h
  have ht := tangent_t 2
  rw [h, map_zero] at ht
  norm_num at ht

/-- The tangent order is `(t,r,s)`, with `s=d/t`. -/
def ratioTangent : Fin 3 → Derivation ℤ FunctionField FunctionField :=
  ![tangent 2+(d/t) • tangent 3, tangent 1, t • tangent 3]

theorem tangent_commute (i j : Fin 4) : Function.Commute (tangent i) (tangent j) :=
  residueTangent_commute quotient quotient_surjective normalPartial
    (tangentPartial i) (tangentPartial j) chartEquation quotient_kernel
    SymmetricAffineField.normal_nonzero
    (integerPartial_commute i.castSucc 4) (integerPartial_commute j.castSucc 4)
    (integerPartial_commute i.castSucc j.castSucc)

theorem ratio_t (i : Fin 3) : ratioTangent i t = if i = 0 then 1 else 0 := by
  fin_cases i <;> simp [ratioTangent, tangent_t]

theorem ratio_time_r_commute : Function.Commute (ratioTangent 0) (ratioTangent 1) := by
  intro x
  have hdt : tangent 1 (d/t) = 0 := by
    simp [Derivation.leibniz_div, tangent_t, tangent_d]
  change tangent 2 (tangent 1 x)+(d/t)*tangent 3 (tangent 1 x) =
    tangent 1 (tangent 2 x+(d/t)*tangent 3 x)
  simp only [map_add, Derivation.leibniz, smul_eq_mul, hdt, mul_zero, add_zero]
  rw [tangent_commute 2 1 x, tangent_commute 3 1 x]

theorem ratio_time_s_commute : Function.Commute (ratioTangent 0) (ratioTangent 2) := by
  intro x
  have h2 : tangent 2 t = 1 := by simpa using tangent_t 2
  have h3 : tangent 3 t = 0 := by simpa using tangent_t 3
  have hdt : tangent 3 (d/t) = 1/t := by
    simp [Derivation.leibniz_div, tangent_t, tangent_d]
    field_simp [t_nonzero]
  change tangent 2 (t*tangent 3 x)+(d/t)*tangent 3 (t*tangent 3 x) =
    t*tangent 3 (tangent 2 x+(d/t)*tangent 3 x)
  simp only [map_add, Derivation.leibniz, smul_eq_mul, h2, h3, hdt]
  norm_num
  rw [tangent_commute 2 3 x]
  field_simp [t_nonzero]
  ring

def parameterCoordinates : Fin 3 → FunctionField :=
  ![weightedMap (X (0 : Fin 4).castSucc), weightedMap (X (1 : Fin 4).castSucc), d/t]

def parameterDerivations : Fin 3 → Derivation ℤ FunctionField FunctionField :=
  ![tangent 0, tangent 1, t • tangent 3]

theorem parameter_coordinate_derivative (i j : Fin 3) :
    parameterDerivations i (parameterCoordinates j) = if j = i then 1 else 0 := by
  have hx0 (k : Fin 4) : tangent k (weightedMap (X 0)) = if k = 0 then 1 else 0 := by
    simpa only [show (0 : Fin 4).castSucc = (0 : Fin 5) from by decide,
      eq_comm] using tangent_coordinate k 0
  have hx1 (k : Fin 4) : tangent k (weightedMap (X 1)) = if k = 1 then 1 else 0 := by
    simpa only [show (1 : Fin 4).castSucc = (1 : Fin 5) from by decide,
      eq_comm] using tangent_coordinate k 1
  have hs0 : tangent 0 (d/t) = 0 := by
    simp [Derivation.leibniz_div, tangent_t, tangent_d]
  have hs1 : tangent 1 (d/t) = 0 := by
    simp [Derivation.leibniz_div, tangent_t, tangent_d]
  have hs3 : tangent 3 (d/t) = 1/t := by
    simp [Derivation.leibniz_div, tangent_t, tangent_d]
    field_simp [t_nonzero]
  fin_cases i <;> fin_cases j <;>
    simp [parameterDerivations, parameterCoordinates, hx0, hx1,
      Derivation.smul_apply, smul_eq_mul, hs0, hs1, hs3, t_nonzero]

def constantMap : ℂ →+* FunctionField := weightedMap.comp C

theorem parameter_constant_derivative (i : Fin 3) (z : ℂ) :
    parameterDerivations i (constantMap z) = 0 := by
  have hc (j : Fin 4) : tangent j (constantMap z) = 0 := by
    change tangent j (weightedMap (C z)) = 0
    rw [tangent_weighted]
    simp
  fin_cases i <;> simp [parameterDerivations, Derivation.smul_apply, smul_eq_mul, hc]

def complexParameterMap : MvPolynomial (Fin 3) ℂ →+* FunctionField :=
  eval₂Hom constantMap parameterCoordinates

theorem complexParameterMap_injective : Function.Injective complexParameterMap :=
  ResidueCoordinateIndependence.injective_of_coordinate_derivations constantMap
    parameterCoordinates parameterDerivations parameter_constant_derivative
    parameter_coordinate_derivative

abbrev ParameterRing := MvPolynomial (Fin 3) ℤ

/-- The exact integral coefficient ring embeds in the actual chart field.
This is the generic-base hypothesis needed for arithmetic incidence lifting. -/
def parameterMap : ParameterRing →+* FunctionField :=
  complexParameterMap.comp (MvPolynomial.map (Int.castRingHom ℂ))

theorem parameterMap_injective : Function.Injective parameterMap :=
  complexParameterMap_injective.comp (MvPolynomial.map_injective _ Int.cast_injective)

@[simp] theorem parameterMap_X (i : Fin 3) : parameterMap (X i) = parameterCoordinates i := by
  simp [parameterMap, complexParameterMap]

@[simp] theorem parameterMap_C (z : ℤ) : parameterMap (C z) = z := by
  simp [parameterMap, complexParameterMap, constantMap]

theorem time_parameter_coordinate (i : Fin 3) : ratioTangent 0 (parameterCoordinates i) = 0 := by
  have hx (j : Fin 4) (k : Fin 4) : tangent j (weightedMap (X k.castSucc)) =
      if k = j then 1 else 0 := tangent_coordinate j k
  have htd : ratioTangent 0 d = d/t := by
    simp [ratioTangent, tangent_d]
  have htt : ratioTangent 0 t = 1 := by simpa using ratio_t 0
  have hts : ratioTangent 0 (d/t) = 0 := by
    rw [Derivation.leibniz_div, htd, htt]
    simp only [smul_eq_mul]
    field_simp [t_nonzero]
    ring
  fin_cases i
  · change tangent 2 (weightedMap (X (0 : Fin 4).castSucc))+
      (d/t)*tangent 3 (weightedMap (X (0 : Fin 4).castSucc)) = 0
    rw [hx, hx]
    norm_num [Fin.ext_iff]
  · change tangent 2 (weightedMap (X (1 : Fin 4).castSucc))+
      (d/t)*tangent 3 (weightedMap (X (1 : Fin 4).castSucc)) = 0
    rw [hx, hx]
    norm_num [Fin.ext_iff]
  · exact hts

theorem time_parameterMap (p : ParameterRing) : ratioTangent 0 (parameterMap p) = 0 := by
  induction p using MvPolynomial.induction_on with
  | C z => simp [Derivation.map_intCast]
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | mul_X p j hp =>
    rw [map_mul, Derivation.leibniz, parameterMap_X, time_parameter_coordinate, hp]
    simp

/-- The cofactor formula includes the negative volume Jacobian. -/
def toChart (w : Fin 3 → FunctionField) : Fin 3 → FunctionField :=
  ![-w 1/t, -w 0/t, -d*w 0/t^2-w 2]

theorem toChart_divergence (w : Fin 3 → FunctionField) :
    (∑ i : Fin 3, tangent i.succ (toChart w i)) =
      -(∑ i : Fin 3, ratioTangent i (w i))/t := by
  have h1 : tangent 1 t = 0 := by simpa using tangent_t 1
  have h2 : tangent 2 t = 1 := by simpa using tangent_t 2
  have h3 : tangent 3 t = 0 := by simpa using tangent_t 3
  have h4 : tangent 3 d = 1 := by simpa using tangent_d 3
  simp only [Fin.sum_univ_three]
  change tangent 1 (-w 1/t)+tangent 2 (-w 0/t)+
    tangent 3 (-d*w 0/t^2-w 2) =
      -(tangent 2 (w 0)+(d/t)*tangent 3 (w 0)+
        tangent 1 (w 1)+t*tangent 3 (w 2))/t
  simp only [map_sub, map_neg, Derivation.leibniz_div, Derivation.leibniz,
    Derivation.leibniz_pow, h1, h2, h3, h4, smul_eq_mul]
  field_simp [t_nonzero]
  ring

theorem target_ratio_density :
    linearDensity normal secondNormal normalCoordinate
      (-t*targetSource0) (-t*targetSource1) = -t*residueDensity := by
  rw [residueDensity_eq_linearDensity]
  unfold linearDensity
  ring

variable {L : Type*} [Field L] [Algebra FunctionField L]
variable [FiniteDimensional FunctionField L]

def extended (i : Fin 3) : Derivation ℤ L L :=
  extendFiniteDerivation (L := L) (ratioTangent i)

theorem extended_t (i : Fin 3) :
    extended (L := L) i (algebraMap FunctionField L t) = if i = 0 then 1 else 0 := by
  rw [extended, extendFiniteDerivation_apply, ratio_t]
  split_ifs <;> simp

theorem extended_time_r_commute :
    Function.Commute (extended (L := L) 0) (extended (L := L) 1) :=
  extendFiniteDerivation_commute (ratioTangent 0) (ratioTangent 1) ratio_time_r_commute

theorem extended_time_s_commute :
    Function.Commute (extended (L := L) 0) (extended (L := L) 2) :=
  extendFiniteDerivation_commute (ratioTangent 0) (ratioTangent 2) ratio_time_s_commute

/-- Finite normalized trace followed by the literal ratio-chart cofactor
map supplies the original three-coefficient primitive. -/
def relativePrimitiveOfRatioTrace
    (s0 s1 : L) (w : Fin 3 → L)
    (hcurrent : (∑ i, extendFiniteDerivation (L := L) (ratioTangent i) (w i)) =
      linearDensity (algebraMap FunctionField L normal)
        (algebraMap FunctionField L secondNormal)
        (algebraMap FunctionField L normalCoordinate) s0 s1)
    (hsource0 : Algebra.normalizedTrace FunctionField L s0 = -t*targetSource0)
    (hsource1 : Algebra.normalizedTrace FunctionField L s1 = -t*targetSource1) :
    RelativePrimitive where
  coefficient := toChart (fun i => Algebra.normalizedTrace FunctionField L (w i))
  differential_eq := by
    rw [toChart_divergence]
    have h := finiteTrace_primitive_of_source_match
      (K := FunctionField) (L := L) ratioTangent
      (fun i => extendFiniteDerivation (L := L) (ratioTangent i))
      (fun i x => extendFiniteDerivation_apply (ratioTangent i) x)
      normal secondNormal normalCoordinate (-t*targetSource0) (-t*targetSource1)
      s0 s1 w hcurrent hsource0 hsource1
    rw [h, target_ratio_density]
    field_simp [t_nonzero]

/-- A selector source in `u-beta` has constant coefficient
`sourceZero-beta*sourceOne` in the protected normal coordinate `u`.
The trace is of this product, rather than a product of separate traces. -/
def relativePrimitiveOfShiftedSelector
    [CharZero L] (j : CubicSelectorSource.Jet L) (beta : L) (w : Fin 3 → L)
    (hl : j.l ≠ 0) (hd : j.delta ≠ 0)
    (hg : CubicSelectorSource.normal j
      (algebraMap FunctionField L normalCoordinate-beta) = algebraMap FunctionField L normal)
    (hgu : CubicSelectorSource.secondNormal j
      (algebraMap FunctionField L normalCoordinate-beta) =
        algebraMap FunctionField L secondNormal)
    (hf : CubicSelectorSource.equation j
      (algebraMap FunctionField L normalCoordinate-beta) = 0)
    (hcurrent : (∑ i, extendFiniteDerivation (L := L) (ratioTangent i) (w i)) =
      2*CubicSelectorSource.numeratorThree j
        (algebraMap FunctionField L normalCoordinate-beta)/
        (3*j.delta*(algebraMap FunctionField L normal)^3))
    (hsource0 : Algebra.normalizedTrace FunctionField L
      (CubicSelectorSource.sourceZero j-beta*CubicSelectorSource.sourceOne j) =
        -t*targetSource0)
    (hsource1 : Algebra.normalizedTrace FunctionField L
      (CubicSelectorSource.sourceOne j) = -t*targetSource1) : RelativePrimitive := by
  apply relativePrimitiveOfRatioTrace
    (CubicSelectorSource.sourceZero j-beta*CubicSelectorSource.sourceOne j)
    (CubicSelectorSource.sourceOne j) w ?_ hsource0 hsource1
  rw [hcurrent]
  have hnormal : CubicSelectorSource.normal j
      (algebraMap FunctionField L normalCoordinate-beta) ≠ 0 := by
    rw [hg]
    exact (map_ne_zero (algebraMap FunctionField L)).mpr
      SymmetricTraceEndpoint.normal_nonzero
  have h := CubicSelectorSource.selector_density j
    (algebraMap FunctionField L normalCoordinate-beta) hl hd hnormal hf
  rw [hg, hgu, CubicSelectorSource.linearDensity_shift] at h
  exact h

/-- The current is now the explicit paired selector of a supplied closed
one-form, rather than a tuple supplied with its divergence equation. -/
def closedSelectorCurrent [CharZero L] (j : CubicSelectorSource.Jet L)
    (beta U V : L) : Fin 3 → L :=
  let tL := algebraMap FunctionField L t
  let z := algebraMap FunctionField L normalCoordinate-beta
  let k := CubicSelectorSource.selector j z/CubicSelectorSource.normal j z
  ![CubicSelectorCurrent.currentT (extended 1) (extended 2) tL j.alpha U V k,
    CubicSelectorCurrent.currentR tL j.alpha V k,
    CubicSelectorCurrent.currentS tL j.alpha U k]

def relativePrimitiveOfClosedSelector
    [CharZero L] (j : CubicSelectorSource.Jet L) (beta U V : L)
    (hTa : extended 0 j.alpha = 0) (hTU : extended 0 U = 0) (hTV : extended 0 V = 0)
    (hclosed : extended 1 V = extended 2 U)
    (hl : j.l ≠ 0) (hd : j.delta ≠ 0)
    (hdelta : j.delta = CubicSelectorCurrent.movingDenominator
      (algebraMap FunctionField L t) j.alpha)
    (hg : CubicSelectorSource.normal j
      (algebraMap FunctionField L normalCoordinate-beta) = algebraMap FunctionField L normal)
    (hgu : CubicSelectorSource.secondNormal j
      (algebraMap FunctionField L normalCoordinate-beta) =
        algebraMap FunctionField L secondNormal)
    (hf : CubicSelectorSource.equation j
      (algebraMap FunctionField L normalCoordinate-beta) = 0)
    (hselector : CubicSelectorSource.movingOperator (extended 0) (extended 1) (extended 2)
      (algebraMap FunctionField L t) j.alpha U V
        (CubicSelectorSource.selector j (algebraMap FunctionField L normalCoordinate-beta)) =
      j.alpha*(j.aDot*(algebraMap FunctionField L normalCoordinate-beta)+
        2*j.gDot-j.a*j.betaDot)/3-j.a*CubicSelectorSource.motion j
          (algebraMap FunctionField L normalCoordinate-beta)/
          (3*CubicSelectorSource.normal j (algebraMap FunctionField L normalCoordinate-beta)))
    (hnormal : CubicSelectorSource.movingOperator (extended 0) (extended 1) (extended 2)
      (algebraMap FunctionField L t) j.alpha U V
        (CubicSelectorSource.normal j (algebraMap FunctionField L normalCoordinate-beta)) =
      CubicSelectorSource.normalMotion j (algebraMap FunctionField L normalCoordinate-beta)-
        CubicSelectorSource.secondNormal j (algebraMap FunctionField L normalCoordinate-beta)*
          CubicSelectorSource.motion j (algebraMap FunctionField L normalCoordinate-beta)/
            CubicSelectorSource.normal j (algebraMap FunctionField L normalCoordinate-beta))
    (hsource0 : Algebra.normalizedTrace FunctionField L
      (CubicSelectorSource.sourceZero j-beta*CubicSelectorSource.sourceOne j) =
        -t*targetSource0)
    (hsource1 : Algebra.normalizedTrace FunctionField L
      (CubicSelectorSource.sourceOne j) = -t*targetSource1) : RelativePrimitive := by
  have hnormal_ne : CubicSelectorSource.normal j
      (algebraMap FunctionField L normalCoordinate-beta) ≠ 0 := by
    rw [hg]
    exact (map_ne_zero (algebraMap FunctionField L)).mpr
      SymmetricTraceEndpoint.normal_nonzero
  have h := CubicSelectorSource.current_density (extended 0) (extended 1) (extended 2)
    (algebraMap FunctionField L t) (algebraMap FunctionField L normalCoordinate-beta) U V j
    extended_time_r_commute extended_time_s_commute
    (by simpa using extended_t (L := L) 0)
    (by simpa using extended_t (L := L) 1)
    (by simpa using extended_t (L := L) 2)
    hTa hTU hTV hclosed hdelta hl hd hnormal_ne hf hselector hnormal
  rw [hg, hgu, CubicSelectorSource.linearDensity_shift] at h
  apply relativePrimitiveOfRatioTrace
    (CubicSelectorSource.sourceZero j-beta*CubicSelectorSource.sourceOne j)
    (CubicSelectorSource.sourceOne j) (closedSelectorCurrent j beta U V) ?_ hsource0 hsource1
  simpa [closedSelectorCurrent, Fin.sum_univ_three, extended, hg] using h

end SymmetricRatioCurrent

#print axioms SymmetricRatioCurrent.t_nonzero
#print axioms SymmetricRatioCurrent.toChart_divergence
#print axioms SymmetricRatioCurrent.relativePrimitiveOfShiftedSelector
#print axioms SymmetricRatioCurrent.relativePrimitiveOfClosedSelector
#print axioms SymmetricRatioCurrent.parameterMap_injective
#print axioms SymmetricRatioCurrent.time_parameterMap

noncomputable section
namespace ChartGeneration
open MvPolynomial WeightedPrimitiveTransport SymmetricAffineField

/-- Every chart function is generated by the five polynomial coordinates and constants. -/
theorem subfield_eq_top (S : Subfield FunctionField)
    (hc : ∀ z : ℂ, residueMap (C z) ∈ S)
    (hx : ∀ i : Fin 5, residueMap (X i) ∈ S) : S = ⊤ := by
  have hp (p : Poly) : residueMap p ∈ S := by
    induction p using MvPolynomial.induction_on with
    | C z => exact hc z
    | add p q hp hq => simpa only [map_add] using S.add_mem hp hq
    | mul_X p i hp => simpa only [map_mul] using S.mul_mem hp (hx i)
  apply top_unique
  intro z hz
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective CoordinateRing z
  obtain ⟨p,rfl⟩ := quotient_surjective a
  obtain ⟨q,rfl⟩ := quotient_surjective b
  exact S.div_mem (hp p) (hp q)

#print axioms subfield_eq_top
end ChartGeneration

noncomputable section
namespace SymmetryTraceDescent

variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

theorem normalizedTrace_mul_base (a : K) (z : L) :
    Algebra.normalizedTrace K L (algebraMap K L a * z) =
      a * Algebra.normalizedTrace K L z := by
  simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply] using
    (map_smul (Algebra.normalizedTrace K L) a z)

/-- Finite trace descends this relative first-order equation without a Galois assumption. -/
theorem descend
    (Dr Ds Dx : Derivation ℤ K K) (Er Es Ex : Derivation ℤ L L)
    (hr : ∀ x, Er (algebraMap K L x) = algebraMap K L (Dr x))
    (hs : ∀ x, Es (algebraMap K L x) = algebraMap K L (Ds x))
    (hx : ∀ x, Ex (algebraMap K L x) = algebraMap K L (Dx x))
    (x target : K) (a b c : L)
    (h : Er a + Es b + c + algebraMap K L (2*x)*Ex c = algebraMap K L target) :
    ∃ A B C : K, Dr A + Ds B + C + (2*x)*Dx C = target := by
  refine ⟨Algebra.normalizedTrace K L a, Algebra.normalizedTrace K L b,
    Algebra.normalizedTrace K L c, ?_⟩
  have h' := congrArg (Algebra.normalizedTrace K L) h
  simp only [map_add, normalizedTrace_mul_base,
    HoldoutConstruction.finiteNormalizedTrace_derivation Dr Er hr,
    HoldoutConstruction.finiteNormalizedTrace_derivation Ds Es hs,
    HoldoutConstruction.finiteNormalizedTrace_derivation Dx Ex hx,
    Algebra.normalizedTrace_algebraMap_apply_eq_self] at h'
  exact h'

theorem ascend
    (Dr Ds Dx : Derivation ℤ K K) (Er Es Ex : Derivation ℤ L L)
    (hr : ∀ x, Er (algebraMap K L x) = algebraMap K L (Dr x))
    (hs : ∀ x, Es (algebraMap K L x) = algebraMap K L (Ds x))
    (hx : ∀ x, Ex (algebraMap K L x) = algebraMap K L (Dx x))
    (x target : K) (A B C : K)
    (h : Dr A + Ds B + C + (2*x)*Dx C = target) :
    ∃ a b c : L, Er a + Es b + c + algebraMap K L (2*x)*Ex c = algebraMap K L target := by
  refine ⟨algebraMap K L A, algebraMap K L B, algebraMap K L C, ?_⟩
  rw [hr, hs, hx, ← map_mul, ← map_add, ← map_add, ← map_add, h]


omit [FiniteDimensional K L] in
/-- Three square roots generate only a finite extension. -/
theorem finite_of_three_squares
    (a b c : L) (ha : IsIntegral K (a^2)) (hb : IsIntegral K (b^2))
    (hc : IsIntegral K (c^2))
    (hgen : IntermediateField.adjoin K ({a,b,c} : Set L) = ⊤) :
    FiniteDimensional K L := by
  have hfin : FiniteDimensional K (IntermediateField.adjoin K ({a,b,c} : Set L)) := by
    apply IntermediateField.finiteDimensional_adjoin
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact IsIntegral.of_pow (by decide : 0 < 2) ha
    · exact IsIntegral.of_pow (by decide : 0 < 2) hb
    · exact IsIntegral.of_pow (by decide : 0 < 2) hc
  letI := hfin
  apply Module.Finite.of_surjective (IntermediateField.val (IntermediateField.adjoin K ({a,b,c} : Set L))).toLinearMap
  intro x
  have hx : x ∈ IntermediateField.adjoin K ({a,b,c} : Set L) := by rw [hgen]; trivial
  exact ⟨⟨x,hx⟩,rfl⟩

#print axioms finite_of_three_squares

#print axioms descend
#print axioms ascend
end SymmetryTraceDescent

noncomputable section
namespace ChartSquareBase
open MvPolynomial WeightedPrimitiveTransport SymmetricAffineField SymmetricRatioCurrent

def lambda : FunctionField := residueMap (X 0)
def b : FunctionField := residueMap (X 1)
def d : FunctionField := residueMap (X 3)
def v : FunctionField := residueMap (X 4)
def constants : ℂ →+* FunctionField := residueMap.comp C

def generators : Fin 5 → FunctionField := ![lambda^2,b,d/t,t^2,v^2]
def SquareField : Subfield FunctionField :=
  Subfield.closure (Set.range constants ∪ Set.range generators)

theorem constant_mem (z : ℂ) : constants z ∈ SquareField :=
  Subfield.subset_closure (Or.inl (Set.mem_range_self z))

theorem generator_mem (i : Fin 5) : generators i ∈ SquareField :=
  Subfield.subset_closure (Or.inr (Set.mem_range_self i))

def rootField : IntermediateField SquareField FunctionField :=
  IntermediateField.adjoin SquareField ({lambda,t,v} : Set FunctionField)

theorem rootField_gen (z : FunctionField) (hz : z ∈ SquareField) : z ∈ rootField := by
  exact rootField.algebraMap_mem ⟨z,hz⟩

theorem rootField_lambda : lambda ∈ rootField := by
  apply IntermediateField.subset_adjoin SquareField
  simp

theorem rootField_t : t ∈ rootField := by
  apply IntermediateField.subset_adjoin SquareField
  simp

theorem rootField_v : v ∈ rootField := by
  apply IntermediateField.subset_adjoin SquareField
  simp

theorem rootField_b : b ∈ rootField := by
  apply rootField_gen
  simpa [generators] using generator_mem 1

theorem rootField_d : d ∈ rootField := by
  have hs : d/t ∈ rootField := rootField_gen _ (by simpa [generators] using generator_mem 2)
  have ht := rootField_t
  have hh := rootField.mul_mem hs ht
  rwa [div_mul_cancel₀ _ t_nonzero] at hh

theorem t_eq_residue : t = residueMap (X 2) := by
  simp [t, SymmetricTraceEndpoint.weightedMap]

theorem rootField_eq_top : rootField = ⊤ := by
  have htop : rootField.toSubfield = ⊤ := by
    apply ChartGeneration.subfield_eq_top
    · intro z
      exact rootField_gen _ (constant_mem z)
    · intro i
      fin_cases i
      · exact rootField_lambda
      · exact rootField_b
      · change residueMap (X 2) ∈ rootField
        rw [← t_eq_residue]; exact rootField_t
      · exact rootField_d
      · exact rootField_v
  apply top_unique
  intro z hz
  change z ∈ rootField.toSubfield
  rw [htop]
  trivial

theorem finite_extension : FiniteDimensional SquareField FunctionField := by
  apply SymmetryTraceDescent.finite_of_three_squares lambda t v
  · have h : lambda^2 ∈ SquareField := by simpa [generators] using generator_mem 0
    exact isIntegral_algebraMap (x := (⟨lambda^2,h⟩ : SquareField))
  · have h : t^2 ∈ SquareField := by simpa [generators] using generator_mem 3
    exact isIntegral_algebraMap (x := (⟨t^2,h⟩ : SquareField))
  · have h : v^2 ∈ SquareField := by simpa [generators] using generator_mem 4
    exact isIntegral_algebraMap (x := (⟨v^2,h⟩ : SquareField))
  · exact rootField_eq_top

#print axioms rootField_eq_top
#print axioms finite_extension
end ChartSquareBase

noncomputable section
namespace SquareDifferentials
open MvPolynomial WeightedPrimitiveTransport SymmetricAffineField SymmetricRatioCurrent ChartSquareBase
open SymmetricTraceEndpoint SymmetricPrimitiveEndpoint
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev GP := MvPolynomial (Fin 5) ℂ
/-- Coordinates ordered as λ²,r,s,x,u. -/
def G : GP :=
  let z := X 0
  let r := X 1
  let s := X 2
  let x := X 3
  let u := X 4
  let l := 1+2*r-u
  let w := x*(1+2*s)-z*u
  2+r^6+2*x^3+s^6*x^3+30*u+30*u^2+2*u^3+
  30*z*x^2*u+30*z^2*x*u^2+2*z^3*u^3+
  C (5/7:ℂ)*l^2*w+C (10/7:ℂ)*l*w^2

def evalG : GP →+* FunctionField := eval₂Hom constants generators

theorem evalG_mem (p : GP) : evalG p ∈ SquareField := by
  induction p using MvPolynomial.induction_on with
  | C z => simpa [evalG] using constant_mem z
  | add p q hp hq => simpa only [map_add] using SquareField.add_mem hp hq
  | mul_X p i hp =>
    have hi : evalG (X i) ∈ SquareField := by simpa [evalG] using generator_mem i
    simpa only [map_mul] using SquareField.mul_mem hp hi

theorem normal_eq_Gu : normal = evalG (pderiv 4 G) := by
  have hc5 : residueMap (C (5/7 : ℂ)) = (5/7 : FunctionField) := by
    change constants (5/7) = _
    simp only [map_div₀, map_ofNat]
  have hc10 : residueMap (C (10/7 : ℂ)) = (10/7 : FunctionField) := by
    change constants (10/7) = _
    simp only [map_div₀, map_ofNat]
  have htwo : (pderiv 4 : Derivation ℂ GP GP) 2 = 0 := (pderiv 4 : Derivation ℂ GP GP).map_natCast 2
  have hthirty : (pderiv 4 : Derivation ℂ GP GP) 30 = 0 := (pderiv 4 : Derivation ℂ GP GP).map_natCast 30
  simp [htwo, hthirty, normal, weightedMap, evalG, G, generators, lambda, b, ChartSquareBase.d, v, t,
    constants, rawWeighted, leftQuadric, rightQuadric, map_ofNat, pderiv_mul,
    pderiv_pow, pderiv_X, Pi.single_apply, Fin.ext_iff]
  simp only [hc5, hc10]
  have ht : residueMap (X 2) ≠ 0 := t_eq_residue ▸ t_nonzero
  field_simp [ht]
  all_goals ring

theorem secondNormal_eq_Guu : secondNormal = evalG (pderiv 4 (pderiv 4 G)) := by
  have hc5 : residueMap (C (5/7 : ℂ)) = (5/7 : FunctionField) := by
    change constants (5/7) = _
    simp only [map_div₀, map_ofNat]
  have hc10 : residueMap (C (10/7 : ℂ)) = (10/7 : FunctionField) := by
    change constants (10/7) = _
    simp only [map_div₀, map_ofNat]
  have htwo : (pderiv 4 : Derivation ℂ GP GP) 2 = 0 := (pderiv 4 : Derivation ℂ GP GP).map_natCast 2
  have hthirty : (pderiv 4 : Derivation ℂ GP GP) 30 = 0 := (pderiv 4 : Derivation ℂ GP GP).map_natCast 30
  have hthree : (pderiv 4 : Derivation ℂ GP GP) 3 = 0 := (pderiv 4 : Derivation ℂ GP GP).map_natCast 3
  simp [hthree, htwo, hthirty, secondNormal, weightedMap, evalG, G, generators, lambda, b, ChartSquareBase.d, v, t,
    constants, rawWeighted, leftQuadric, rightQuadric, map_ofNat, pderiv_mul,
    pderiv_pow, pderiv_X, Pi.single_apply, Fin.ext_iff]
  simp only [hc5, hc10]
  have ht : residueMap (X 2) ≠ 0 := t_eq_residue ▸ t_nonzero
  field_simp [ht]
  all_goals ring

theorem raw_derivative_r : weightedMap (pderiv 1 rawWeighted) = evalG (pderiv 1 G) := by
  have hc5 : residueMap (C (5/7 : ℂ)) = (5/7 : FunctionField) := by
    change constants (5/7) = _
    simp only [map_div₀, map_ofNat]
  have hc10 : residueMap (C (10/7 : ℂ)) = (10/7 : FunctionField) := by
    change constants (10/7) = _
    simp only [map_div₀, map_ofNat]
  have htwo : (pderiv 1 : Derivation ℂ GP GP) 2 = 0 := (pderiv 1 : Derivation ℂ GP GP).map_natCast 2
  have hthirty : (pderiv 1 : Derivation ℂ GP GP) 30 = 0 := (pderiv 1 : Derivation ℂ GP GP).map_natCast 30
  simp [htwo, hthirty, normal, weightedMap, evalG, G, generators, lambda, b, ChartSquareBase.d, v, t,
    constants, rawWeighted, leftQuadric, rightQuadric, map_ofNat, pderiv_mul,
    pderiv_pow, pderiv_X, Pi.single_apply, Fin.ext_iff]
  simp only [hc5, hc10]
  have ht : residueMap (X 2) ≠ 0 := t_eq_residue ▸ t_nonzero
  field_simp [ht]
  all_goals ring

theorem raw_derivative_s : t * weightedMap (pderiv 3 rawWeighted) = evalG (pderiv 2 G) := by
  have hc5 : residueMap (C (5/7 : ℂ)) = (5/7 : FunctionField) := by
    change constants (5/7) = _
    simp only [map_div₀, map_ofNat]
  have hc10 : residueMap (C (10/7 : ℂ)) = (10/7 : FunctionField) := by
    change constants (10/7) = _
    simp only [map_div₀, map_ofNat]
  have htwo : (pderiv 2 : Derivation ℂ GP GP) 2 = 0 := (pderiv 2 : Derivation ℂ GP GP).map_natCast 2
  have hthirty : (pderiv 2 : Derivation ℂ GP GP) 30 = 0 := (pderiv 2 : Derivation ℂ GP GP).map_natCast 30
  have htwo3 : (pderiv 3 : Derivation ℂ GP GP) 2 = 0 := (pderiv 3 : Derivation ℂ GP GP).map_natCast 2
  have hthirty3 : (pderiv 3 : Derivation ℂ GP GP) 30 = 0 := (pderiv 3 : Derivation ℂ GP GP).map_natCast 30
  simp [htwo3, hthirty3, htwo, hthirty, normal, weightedMap, evalG, G, generators, lambda, b, ChartSquareBase.d, v, t,
    constants, rawWeighted, leftQuadric, rightQuadric, map_ofNat, pderiv_mul,
    pderiv_pow, pderiv_X, Pi.single_apply, Fin.ext_iff]
  simp only [hc5, hc10]
  have ht : residueMap (X 2) ≠ 0 := t_eq_residue ▸ t_nonzero
  field_simp [ht]
  all_goals ring

theorem raw_derivative_x : 2*t*evalG (pderiv 3 G) = weightedMap (pderiv 2 rawWeighted) + (ChartSquareBase.d/t)*weightedMap (pderiv 3 rawWeighted) := by
  have hc5 : residueMap (C (5/7 : ℂ)) = (5/7 : FunctionField) := by
    change constants (5/7) = _
    simp only [map_div₀, map_ofNat]
  have hc10 : residueMap (C (10/7 : ℂ)) = (10/7 : FunctionField) := by
    change constants (10/7) = _
    simp only [map_div₀, map_ofNat]
  have htwo : (pderiv 2 : Derivation ℂ GP GP) 2 = 0 := (pderiv 2 : Derivation ℂ GP GP).map_natCast 2
  have hthirty : (pderiv 2 : Derivation ℂ GP GP) 30 = 0 := (pderiv 2 : Derivation ℂ GP GP).map_natCast 30
  have htwo3 : (pderiv 3 : Derivation ℂ GP GP) 2 = 0 := (pderiv 3 : Derivation ℂ GP GP).map_natCast 2
  have hthirty3 : (pderiv 3 : Derivation ℂ GP GP) 30 = 0 := (pderiv 3 : Derivation ℂ GP GP).map_natCast 30
  simp [htwo3, hthirty3, htwo, hthirty, normal, weightedMap, evalG, G, generators, lambda, b, ChartSquareBase.d, v, t,
    constants, rawWeighted, leftQuadric, rightQuadric, map_ofNat, pderiv_mul,
    pderiv_pow, pderiv_X, Pi.single_apply, Fin.ext_iff]
  simp only [hc5, hc10]
  have ht : residueMap (X 2) ≠ 0 := t_eq_residue ▸ t_nonzero
  field_simp [ht]
  all_goals ring


def Dr : Derivation ℤ FunctionField FunctionField := ratioTangent 1
def Ds : Derivation ℤ FunctionField FunctionField := ratioTangent 2
def Dx : Derivation ℤ FunctionField FunctionField := (1/(2*t)) • ratioTangent 0

theorem u_as_weighted : v^2 = weightedMap (X 4) := by
  simp [v, weightedMap, map_pow]

theorem Dr_u : Dr (v^2) = -evalG (pderiv 1 G)/normal := by
  rw [u_as_weighted]
  change tangent 1 (weightedMap (X 4)) = _
  rw [tangent_weighted]
  simp only [show (1 : Fin 4).castSucc = (1 : Fin 5) from rfl, show (3 : Fin 4).castSucc = (3 : Fin 5) from rfl]
  simp only [pderiv_X, Pi.single_apply, Fin.reduceEq, ite_false, ite_true, map_zero,
    map_one, zero_sub, mul_one]
  rw [raw_derivative_r]
  ring

theorem Ds_u : Ds (v^2) = -evalG (pderiv 2 G)/normal := by
  rw [u_as_weighted]
  change t * tangent 3 (weightedMap (X 4)) = _
  rw [tangent_weighted]
  simp only [show (1 : Fin 4).castSucc = (1 : Fin 5) from rfl, show (3 : Fin 4).castSucc = (3 : Fin 5) from rfl]
  simp only [pderiv_X, Pi.single_apply, Fin.reduceEq, ite_false, ite_true, map_zero,
    map_one, zero_sub, mul_one]
  rw [← raw_derivative_s]
  ring

theorem Dx_u : Dx (v^2) = -evalG (pderiv 3 G)/normal := by
  rw [u_as_weighted]
  change (1/(2*t))*(tangent 2 (weightedMap (X 4))+(SymmetricRatioCurrent.d/t)*tangent 3 (weightedMap (X 4))) = _
  rw [tangent_weighted, tangent_weighted]
  simp only [show (2 : Fin 4).castSucc = (2 : Fin 5) from rfl, show (3 : Fin 4).castSucc = (3 : Fin 5) from rfl]
  simp only [pderiv_X, Pi.single_apply, Fin.reduceEq, ite_false, ite_true, map_zero,
    map_one, zero_sub, mul_one]
  have hd : SymmetricRatioCurrent.d = ChartSquareBase.d := by simp [SymmetricRatioCurrent.d, ChartSquareBase.d, weightedMap]
  rw [hd]
  have hh := raw_derivative_x
  field_simp [t_nonzero, SymmetricTraceEndpoint.normal_nonzero] at *
  linear_combination hh


def P : GP := X 1*X 2*X 3*(1-X 4)*(X 3-X 0*X 4)

theorem source_eq_P : t*source = evalG P := by
  simp [source, t, weightedMap, evalG, P, generators, lambda, b, ChartSquareBase.d, v,
    constants, rawSource, pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply, Fin.ext_iff]
  have ht : residueMap (X 2) ≠ 0 := t_eq_residue ▸ t_nonzero
  field_simp [ht]
  all_goals ring

theorem sourceDerivative_eq_Pu : t*sourceDerivative = evalG (pderiv 4 P) := by
  simp [sourceDerivative, t, weightedMap, evalG, P, generators, lambda, b, ChartSquareBase.d, v,
    constants, rawSource, pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply, Fin.ext_iff]
  have ht : residueMap (X 2) ≠ 0 := t_eq_residue ▸ t_nonzero
  field_simp [ht]
  all_goals ring

#print axioms evalG_mem
#print axioms normal_eq_Gu
#print axioms secondNormal_eq_Guu
#print axioms raw_derivative_r
#print axioms raw_derivative_s
#print axioms raw_derivative_x
#print axioms Dr_u
#print axioms Ds_u
#print axioms Dx_u
#print axioms source_eq_P
#print axioms sourceDerivative_eq_Pu
end SquareDifferentials

noncomputable section
namespace SquareStable
open MvPolynomial SymmetricAffineField SymmetricRatioCurrent ChartSquareBase SquareDifferentials
open SymmetricPrimitiveEndpoint SymmetricTraceEndpoint

theorem normal_mem : normal ∈ SquareField := by
  rw [normal_eq_Gu]
  exact evalG_mem _

theorem Dr_u_mem : Dr (v^2) ∈ SquareField := by
  rw [Dr_u]
  exact SquareField.div_mem (SquareField.neg_mem (evalG_mem _)) normal_mem

theorem Ds_u_mem : Ds (v^2) ∈ SquareField := by
  rw [Ds_u]
  exact SquareField.div_mem (SquareField.neg_mem (evalG_mem _)) normal_mem

theorem Dx_u_mem : Dx (v^2) ∈ SquareField := by
  rw [Dx_u]
  exact SquareField.div_mem (SquareField.neg_mem (evalG_mem _)) normal_mem

/-- A derivation preserving the chosen generators preserves their full subfield. -/
theorem closure_stable (D : Derivation ℤ FunctionField FunctionField)
    (hc : ∀ z : ℂ, D (constants z) = 0)
    (hg : ∀ i : Fin 5, D (generators i) ∈ SquareField)
    {z : FunctionField} (hz : z ∈ SquareField) : D z ∈ SquareField := by
  induction hz using Subfield.closure_induction with
  | mem y hy =>
    rcases hy with ⟨w,rfl⟩ | ⟨i,rfl⟩
    · rw [hc]; exact SquareField.zero_mem
    · exact hg i
  | one => simpa using SquareField.zero_mem
  | add y z hy hz ihy ihz => simpa only [map_add] using SquareField.add_mem ihy ihz
  | neg y hy ih => simpa only [map_neg] using SquareField.neg_mem ih
  | inv y hy ih =>
    rw [Derivation.leibniz_inv]
    exact SquareField.mul_mem (SquareField.neg_mem (SquareField.pow_mem (SquareField.inv_mem hy) 2)) ih
  | mul y z hy hz ihy ihz =>
    rw [Derivation.leibniz]
    exact SquareField.add_mem (SquareField.mul_mem hy ihz) (SquareField.mul_mem hz ihy)


theorem coordinate_lambda : parameterCoordinates 0 = lambda := by
  simp [parameterCoordinates, lambda, weightedMap]

theorem coordinate_b : parameterCoordinates 1 = b := by
  simp [parameterCoordinates, b, weightedMap]

theorem coordinate_s : parameterCoordinates 2 = ChartSquareBase.d/t := by
  simp [parameterCoordinates, SymmetricRatioCurrent.d, ChartSquareBase.d, weightedMap]

theorem constants_eq (z : ℂ) : constants z = constantMap z := by
  simp [constants, constantMap, weightedMap]

theorem tangent_constant (i : Fin 4) (z : ℂ) : tangent i (constants z) = 0 := by
  rw [constants_eq]
  change tangent i (weightedMap (C z)) = 0
  rw [tangent_weighted]
  simp

theorem Dr_const (z : ℂ) : Dr (constants z) = 0 := by
  change tangent 1 (constants z) = 0
  exact tangent_constant 1 z

theorem Ds_const (z : ℂ) : Ds (constants z) = 0 := by
  change t * tangent 3 (constants z) = 0
  rw [tangent_constant, mul_zero]

theorem Dx_const (z : ℂ) : Dx (constants z) = 0 := by
  change (1/(2*t)) * (tangent 2 (constants z)+(SymmetricRatioCurrent.d/t)*tangent 3 (constants z)) = 0
  rw [tangent_constant, tangent_constant]
  ring


theorem Dr_param (i : Fin 3) : Dr (parameterCoordinates i) = if i = 1 then 1 else 0 := by
  simpa [Dr, ratioTangent, parameterDerivations] using parameter_coordinate_derivative 1 i

theorem Ds_param (i : Fin 3) : Ds (parameterCoordinates i) = if i = 2 then 1 else 0 := by
  simpa [Ds, ratioTangent, parameterDerivations] using parameter_coordinate_derivative 2 i

theorem Dx_param (i : Fin 3) : Dx (parameterCoordinates i) = 0 := by
  change (1/(2*t)) * ratioTangent 0 (parameterCoordinates i) = 0
  rw [time_parameter_coordinate, mul_zero]

theorem Dr_t : Dr t = 0 := by simpa [Dr] using ratio_t 1
theorem Ds_t : Ds t = 0 := by simpa [Ds] using ratio_t 2
theorem Dx_tsq : Dx (t^2) = 1 := by
  change (1/(2*t)) * ratioTangent 0 (t^2) = 1
  rw [pow_two, Derivation.leibniz]
  simp only [ratio_t, ite_true, smul_eq_mul, mul_one]
  field_simp [t_nonzero]
  norm_num



theorem Dr_generators (i : Fin 5) : Dr (generators i) ∈ SquareField := by
  fin_cases i
  · change Dr (lambda^2) ∈ SquareField
    rw [← coordinate_lambda, pow_two, Derivation.leibniz]
    simp [Dr_param]
  · change Dr b ∈ SquareField
    rw [← coordinate_b, Dr_param]
    simp
  · change Dr (ChartSquareBase.d/t) ∈ SquareField
    rw [← coordinate_s, Dr_param]
    simp
  · change Dr (t^2) ∈ SquareField
    rw [pow_two, Derivation.leibniz, Dr_t]
    simp
  · exact Dr_u_mem

theorem Ds_generators (i : Fin 5) : Ds (generators i) ∈ SquareField := by
  fin_cases i
  · change Ds (lambda^2) ∈ SquareField
    rw [← coordinate_lambda, pow_two, Derivation.leibniz]
    simp [Ds_param]
  · change Ds b ∈ SquareField
    rw [← coordinate_b, Ds_param]
    simp
  · change Ds (ChartSquareBase.d/t) ∈ SquareField
    rw [← coordinate_s, Ds_param]
    simp
  · change Ds (t^2) ∈ SquareField
    rw [pow_two, Derivation.leibniz, Ds_t]
    simp
  · exact Ds_u_mem

theorem Dx_generators (i : Fin 5) : Dx (generators i) ∈ SquareField := by
  fin_cases i
  · change Dx (lambda^2) ∈ SquareField
    rw [← coordinate_lambda, pow_two, Derivation.leibniz]
    simp [Dx_param]
  · change Dx b ∈ SquareField
    rw [← coordinate_b, Dx_param]
    exact SquareField.zero_mem
  · change Dx (ChartSquareBase.d/t) ∈ SquareField
    rw [← coordinate_s, Dx_param]
    exact SquareField.zero_mem
  · change Dx (t^2) ∈ SquareField
    rw [Dx_tsq]
    exact SquareField.one_mem
  · exact Dx_u_mem

theorem Dr_stable {x : FunctionField} (h : x ∈ SquareField) : Dr x ∈ SquareField :=
  closure_stable Dr Dr_const Dr_generators h

theorem Ds_stable {x : FunctionField} (h : x ∈ SquareField) : Ds x ∈ SquareField :=
  closure_stable Ds Ds_const Ds_generators h

theorem Dx_stable {x : FunctionField} (h : x ∈ SquareField) : Dx x ∈ SquareField :=
  closure_stable Dx Dx_const Dx_generators h


theorem scaled_residue_mem : t*residueDensity ∈ SquareField := by
  have hN : normal ∈ SquareField := normal_mem
  have hNN : secondNormal ∈ SquareField := by
    rw [secondNormal_eq_Guu]
    exact evalG_mem _
  have hP : t*source ∈ SquareField := by
    rw [source_eq_P]
    exact evalG_mem _
  have hPu : t*sourceDerivative ∈ SquareField := by
    rw [sourceDerivative_eq_Pu]
    exact evalG_mem _
  have heq : t*residueDensity =
      2*(normal*(t*sourceDerivative)-secondNormal*(t*source))/normal^3 := by
    change t*(2*(normal*sourceDerivative-secondNormal*source)/normal^3) = _
    ring
  rw [heq]
  have htwo : (2 : FunctionField) ∈ SquareField := by
    simpa only [one_add_one_eq_two] using SquareField.add_mem SquareField.one_mem SquareField.one_mem
  exact SquareField.div_mem
    (SquareField.mul_mem htwo
      (SquareField.sub_mem (SquareField.mul_mem hN hPu) (SquareField.mul_mem hNN hP)))
    (SquareField.pow_mem hN 3)

/-- Restrict an ambient derivation known to preserve the square-coordinate field. -/
def restrict (D : Derivation ℤ FunctionField FunctionField)
    (hD : ∀ x ∈ SquareField, D x ∈ SquareField) : Derivation ℤ SquareField SquareField := by
  refine Derivation.mk' ?_ ?_
  · exact { toFun := fun x => ⟨D x, hD x x.property⟩
            map_add' := by intro x y; apply Subtype.ext; exact map_add D (x : FunctionField) (y : FunctionField)
            map_smul' := by intro n x; apply Subtype.ext; exact D.toLinearMap.map_smul n (x : FunctionField) }
  · intro x y
    apply Subtype.ext
    exact Derivation.leibniz D x y

def Dr0 : Derivation ℤ SquareField SquareField := restrict Dr (fun _ h => Dr_stable h)
def Ds0 : Derivation ℤ SquareField SquareField := restrict Ds (fun _ h => Ds_stable h)
def Dx0 : Derivation ℤ SquareField SquareField := restrict Dx (fun _ h => Dx_stable h)

#print axioms scaled_residue_mem
#print axioms Dr0
#print axioms Ds0
#print axioms Dx0

#print axioms Dr_stable
#print axioms Ds_stable
#print axioms Dx_stable

#print axioms Dr_u_mem
#print axioms closure_stable
end SquareStable

noncomputable section
namespace SquarePrimitive
open MvPolynomial SymmetricAffineField SymmetricRatioCurrent SymmetricPrimitiveEndpoint
open SymmetryTraceDescent ChartSquareBase SquareDifferentials SquareStable
open scoped BigOperators

def chartCurrent (a b c : FunctionField) : Fin 3 → FunctionField := ![-t*c,-a,-b]

theorem chartCurrent_divergence (a b c : FunctionField) :
    (∑ i : Fin 3, tangent i.succ (toChart (chartCurrent a b c) i)) =
      (Dr a + Ds b + c + 2*t^2*Dx c)/t := by
  rw [toChart_divergence]
  simp only [Fin.sum_univ_three]
  change -(ratioTangent 0 (-t*c)+ratioTangent 1 (-a)+ratioTangent 2 (-b))/t = _
  simp only [map_neg, Derivation.leibniz, ratio_t, ite_true, smul_eq_mul, mul_one]
  simp only [Dr, Ds, Dx, Derivation.smul_apply, smul_eq_mul]
  field_simp [t_nonzero]
  ring

def BaseEquation (a b c : SquareField) : Prop :=
  Dr0 a + Ds0 b + c + (2*⟨t^2, by simpa [generators] using generator_mem 3⟩)*Dx0 c =
    ⟨t*residueDensity,scaled_residue_mem⟩

theorem lift_equation (a b c : SquareField) (h : BaseEquation a b c) :
    Nonempty RelativePrimitive := by
  let A : FunctionField := a
  let B : FunctionField := b
  let C : FunctionField := c
  refine ⟨⟨toChart (chartCurrent A B C), ?_⟩⟩
  rw [chartCurrent_divergence]
  have h' : Dr A + Ds B + C + 2*t^2*Dx C = t*residueDensity := by
    exact congrArg Subtype.val h
  rw [h']
  exact mul_div_cancel_left₀ residueDensity t_nonzero


theorem descend_primitive (beta : RelativePrimitive) :
    ∃ a b c : SquareField, BaseEquation a b c := by
  let A : FunctionField := t*beta.coefficient 0
  let B : FunctionField := beta.coefficient 2-(SymmetricRatioCurrent.d/t)*beta.coefficient 1
  let C : FunctionField := beta.coefficient 1
  have hchart : toChart (chartCurrent A B C) = beta.coefficient := by
    funext i
    fin_cases i <;> simp [toChart, chartCurrent, A, B, C] <;> field_simp [t_nonzero] <;> ring
  have hdiv := chartCurrent_divergence A B C
  rw [hchart, beta.differential_eq] at hdiv
  have hbase : Dr A+Ds B+C+2*t^2*Dx C = t*residueDensity := by
    field_simp [t_nonzero] at hdiv
    linear_combination -hdiv
  letI : FiniteDimensional SquareField FunctionField := finite_extension
  let x : SquareField := ⟨t^2, by simpa [generators] using generator_mem 3⟩
  let target : SquareField := ⟨t*residueDensity, scaled_residue_mem⟩
  have heq : Dr A+Ds B+C+algebraMap SquareField FunctionField (2*x)*Dx C =
      algebraMap SquareField FunctionField target := by
    exact hbase
  obtain ⟨a,b,c,h⟩ := SymmetryTraceDescent.descend Dr0 Ds0 Dx0 Dr Ds Dx
    (by intro y; rfl) (by intro y; rfl) (by intro y; rfl) x target A B C heq
  exact ⟨a,b,c,h⟩

theorem primitive_iff_square_equation :
    Nonempty RelativePrimitive ↔ ∃ a b c : SquareField, BaseEquation a b c := by
  constructor
  · intro ⟨beta⟩
    exact descend_primitive beta
  · rintro ⟨a,b,c,h⟩
    exact lift_equation a b c h

#print axioms descend_primitive
#print axioms primitive_iff_square_equation

#print axioms chartCurrent_divergence
#print axioms lift_equation
end SquarePrimitive
