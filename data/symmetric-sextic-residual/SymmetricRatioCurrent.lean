import Proposal.SymmetricTraceEndpoint
import Proposal.CubicSelectorSource

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
