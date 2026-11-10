import Proposal.SymmetricChartField
import Proposal.SymmetricChartClearing
import Proposal.SymmetricPrimitiveEndpoint
import Proposal.SymmetricSmoothness

/-!
# Finite polynomial transport of a relative primitive

The actual chart, its inverse-Jacobian current, and one common polynomial
substitution give all six original-coordinate numerators and a legal
denominator. The final theorem is conditional only on an actual relative
primitive; it makes no geometric existence assertion.
-/

noncomputable section

namespace SymmetricCertificateTransport

open MvPolynomial HoldoutConstruction SymmetricPiolaTransport
open SymmetricChartField SymmetricChartClearing
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev ChartPoly := WeightedPrimitiveTransport.Poly
abbrev PhysicalPoly := HodgeComputer.AmbientPoly 5

@[simp] theorem physicalMap_U : physicalMap U = 2*x 0 := by
  simp [U, chartCoordinates]
  ring

@[simp] theorem physicalMap_S : physicalMap S = 2*x 0*x 5 := by
  simp [S, chartCoordinates]
  ring

@[simp] theorem physicalMap_T : physicalMap T = 2*x 0*x 1*x 5 := by
  simp [T, chartCoordinates]
  ring

@[simp] theorem physicalMap_B : physicalMap B = 4*(x 0)^2*x 5 := by
  simp [B]
  ring

@[simp] theorem physicalMap_G (i : Fin 5) :
    physicalMap (G i) = (4*(x 0)^2*x 5)*x i.succ := by
  fin_cases i <;> simp [G, chartCoordinates, map_ofNat] <;> ring

theorem physicalMap_liftPolynomial (p : ChartPoly) (L : ℕ)
    (hp : p.totalDegree ≤ L) :
    physicalMap (liftPolynomial p L) =
      (4*(x 0)^2*x 5)^L * affineMap p := by
  have hc : physicalMap.comp (C : ℂ →+* PhysicalPoly) = coefficientMap := by
    ext c
    simp
  have h := CommonDenominatorSubstitution.map_cleared p B G L hp
    physicalMap (4*(x 0)^2*x 5) (fun i : Fin 5 => x i.succ)
    physicalMap_B physicalMap_G
  simpa only [liftPolynomial, hc, affineMap_as_eval, coe_eval₂Hom] using h

def certificateNumerator (N : Fin 5 → ChartPoly) (L : ℕ) : Fin 6 → PhysicalPoly :=
  ![U^2*S*liftPolynomial (N 4) L,
    -(U^2*S*liftPolynomial (N 4) L),
    U^2*S*liftPolynomial (N 1) L,
    U*S^2*liftPolynomial (N 0) L+U^2*S*liftPolynomial (N 2) L+
      U^2*T*liftPolynomial (N 4) L,
    -(U*S^2*liftPolynomial (N 0) L)+U^2*S*liftPolynomial (N 2) L-
      U^2*T*liftPolynomial (N 4) L,
    U^2*S*liftPolynomial (N 3) L]

def certificateQuotient (Q : ChartPoly) (L : ℕ) : PhysicalPoly :=
  1024*U^(L-5)*S^(L+3)*liftPolynomial Q L

theorem certificateNumerator_homogeneous (N : Fin 5 → ChartPoly) (L : ℕ)
    (hLN : ∀ i, (N i).totalDegree ≤ L) (i : Fin 6) :
    (certificateNumerator N L i).IsHomogeneous (2*L+3) := by
  have hstandard (j : Fin 5) : (U^2*S*liftPolynomial (N j) L).IsHomogeneous (2*L+3) := by
    simpa [Nat.add_comm] using
      (((U_homogeneous.pow 2).mul S_homogeneous).mul
        (liftPolynomial_homogeneous (N j) L (hLN j)))
  have hlam : (U*S^2*liftPolynomial (N 0) L).IsHomogeneous (2*L+3) := by
    simpa [Nat.add_comm] using
      ((U_homogeneous.mul (S_homogeneous.pow 2)).mul
        (liftPolynomial_homogeneous (N 0) L (hLN 0)))
  have hlast : (U^2*T*liftPolynomial (N 4) L).IsHomogeneous (2*L+3) := by
    simpa [Nat.add_comm] using
      (((U_homogeneous.pow 2).mul T_homogeneous).mul
        (liftPolynomial_homogeneous (N 4) L (hLN 4)))
  fin_cases i
  · exact hstandard 4
  · exact (hstandard 4).neg
  · exact hstandard 1
  · exact (hlam.add (hstandard 2)).add hlast
  · exact (hlam.neg.add (hstandard 2)).sub hlast
  · exact hstandard 3

theorem certificateQuotient_clear (Q : ChartPoly) (L : ℕ) (hL : 5 ≤ L) :
    U^5*certificateQuotient Q L = 1024*B^L*S^3*liftPolynomial Q L := by
  have hp : U^5*U^(L-5) = U^L := by
    rw [← pow_add, Nat.add_sub_of_le hL]
  simp only [certificateQuotient, B, mul_pow, pow_add]
  calc
    _ = 1024*(U^5*U^(L-5))*S^L*S^3*liftPolynomial Q L := by ring
    _ = _ := by rw [hp]; ring

theorem certificateCurrent_map (D : ChartPoly) (N : Fin 5 → ChartPoly) (L : ℕ)
    (hD : D ≠ 0) (hLD : D.totalDegree ≤ L)
    (hLN : ∀ i, (N i).totalDegree ≤ L) :
    (fun i => physicalMap (certificateNumerator N L i)/
      physicalMap (certificateDenominator D L)) =
      physicalCurrent (x 0) (x 1) (x 5)
        (fun i => affineMap (N i)/affineMap D) := by
  have ha := coordinate_ne_zero 0
  have hv := coordinate_ne_zero 5
  have hd : affineMap D ≠ 0 := fun h => hD (affineMap_injective (by simpa using h))
  have hb : 4*(x 0)^2*x 5 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha)) hv
  funext i
  fin_cases i <;>
    simp [certificateNumerator, certificateDenominator, physicalCurrent, map_ofNat,
      physicalMap_liftPolynomial D L hLD,
      physicalMap_liftPolynomial (N 0) L (hLN 0),
      physicalMap_liftPolynomial (N 1) L (hLN 1),
      physicalMap_liftPolynomial (N 2) L (hLN 2),
      physicalMap_liftPolynomial (N 3) L (hLN 3),
      physicalMap_liftPolynomial (N 4) L (hLN 4)] <;>
    field_simp <;> ring

theorem certificateQuotient_map (D Q : ChartPoly) (L : ℕ)
    (hL : 5 ≤ L) (hD : D ≠ 0) (hLD : D.totalDegree ≤ L)
    (hLQ : Q.totalDegree ≤ L) :
    physicalMap (certificateQuotient Q L) =
      (physicalMap (certificateDenominator D L))^2 *
        (affineMap Q/(4*(x 0)^6*x 5*(affineMap D)^2)) := by
  have ha := coordinate_ne_zero 0
  have hv := coordinate_ne_zero 5
  have hd : affineMap D ≠ 0 := fun h => hD (affineMap_injective (by simpa using h))
  have hu : physicalMap U ≠ 0 := by rw [physicalMap_U]; exact mul_ne_zero (by norm_num) ha
  apply mul_left_cancel₀ (pow_ne_zero 5 hu)
  have h := congrArg physicalMap (certificateQuotient_clear Q L hL)
  simp only [map_mul, map_pow, map_ofNat] at h
  rw [h]
  simp only [certificateDenominator, map_mul, map_pow, map_ofNat,
    physicalMap_U, physicalMap_S, physicalMap_B,
    physicalMap_liftPolynomial D L hLD, physicalMap_liftPolynomial Q L hLQ]
  field_simp
  <;> ring

/-- Exact affine normalized data produce exact normalized polynomial data
for the original protected sextic. -/
theorem transported_normalized_equations
    (D Q : ChartPoly) (N : Fin 5 → ChartPoly) (L : ℕ)
    (hL : 5 ≤ L) (hD : D ≠ 0) (hLD : D.totalDegree ≤ L)
    (hLN : ∀ i, (N i).totalDegree ≤ L) (hLQ : Q.totalDegree ≤ L)
    (hlegal : IsRelPrime WeightedPrimitiveTransport.chartEquation D)
    (hnormal : HodgeTestbed.directional WeightedPrimitiveTransport.chartEquation N =
      WeightedPrimitiveTransport.chartSource*D)
    (hdiv : HodgeTestbed.divergenceNumerator D N =
      WeightedPrimitiveTransport.chartEquation*Q) :
    HodgeTestbed.directional HodgeSubmission.F (certificateNumerator N L) =
        HodgeSubmission.A*certificateDenominator D L ∧
      HodgeTestbed.divergenceNumerator (certificateDenominator D L)
        (certificateNumerator N L) = HodgeSubmission.F*certificateQuotient Q L := by
  obtain ⟨hn, hd⟩ := affine_current_equations D WeightedPrimitiveTransport.chartEquation
    WeightedPrimitiveTransport.chartSource Q N hD hnormal hdiv
  have hp := normalized_current_transport delta x delta_coordinate
    (coordinate_ne_zero 0) (coordinate_ne_zero 5)
    (affineMap WeightedPrimitiveTransport.chartEquation)
    (affineMap WeightedPrimitiveTransport.chartSource)
    (affineMap Q/(affineMap D)^2)
    (fun i => affineMap (N i)/affineMap D) hn hd
  change
    (∑ j, physicalCurrent (x 0) (x 1) (x 5)
      (fun i => affineMap (N i)/affineMap D) j * theta j
      ((x 0)^6*affineMap WeightedPrimitiveTransport.chartEquation)) = _ ∧
      fieldDivergence theta (physicalCurrent (x 0) (x 1) (x 5)
        (fun i => affineMap (N i)/affineMap D)) = _ at hp
  rw [← physicalMap_F, ← certificateCurrent_map D N L hD hLD hLN] at hp
  have hden : physicalMap (certificateDenominator D L) ≠ 0 := fun h =>
    certificateDenominator_ne_zero D L hLD hlegal
      (physicalMap_injective (by simpa using h))
  have hs : (x 0)^6*affineMap WeightedPrimitiveTransport.chartSource/(4*x 5) =
      physicalMap HodgeSubmission.A := by
    rw [← physicalMap_A]
    field_simp [coordinate_ne_zero 5]
  have hr := certificateQuotient_map D Q L hL hD hLD hLQ
  constructor
  · apply physicalMap_injective
    rw [map_mul]
    have h := hp.1
    rw [hs, quotient_contraction physicalMap theta theta_physicalMap] at h
    exact (div_eq_iff hden).mp h
  · apply physicalMap_injective
    rw [map_mul]
    have h := hp.2
    rw [quotient_divergence physicalMap theta theta_physicalMap] at h
    have h' := (div_eq_iff (pow_ne_zero 2 hden)).mp h
    rw [hr]
    calc
      _ = (physicalMap HodgeSubmission.F *
        ((affineMap Q/(affineMap D)^2)/(4*(x 0)^6*x 5))) *
          (physicalMap (certificateDenominator D L))^2 := h'
      _ = _ := by ring

/-- The displayed denominator and six displayed numerators themselves pass
the unchanged verifier. No subsequent homogeneous replacement is used. -/
theorem explicit_verify
    (D Q : ChartPoly) (N : Fin 5 → ChartPoly) (L : ℕ)
    (hL : 5 ≤ L) (hD : D ≠ 0) (hLD : D.totalDegree ≤ L)
    (hLN : ∀ i, (N i).totalDegree ≤ L) (hLQ : Q.totalDegree ≤ L)
    (hlegal : IsRelPrime WeightedPrimitiveTransport.chartEquation D)
    (hnormal : HodgeTestbed.directional WeightedPrimitiveTransport.chartEquation N =
      WeightedPrimitiveTransport.chartSource*D)
    (hdiv : HodgeTestbed.divergenceNumerator D N =
      WeightedPrimitiveTransport.chartEquation*Q) :
    HodgeComputer.Verify HodgeSubmission.F HodgeSubmission.A 6 1
      (certificateDenominator D L) (certificateNumerator N L) (certificateQuotient Q L) := by
  obtain ⟨hn, hd⟩ := transported_normalized_equations D Q N L hL hD hLD hLN hLQ
    hlegal hnormal hdiv
  have hden := certificateDenominator_ne_zero D L hLD hlegal
  have hhom := certificateDenominator_homogeneous D L hLD
  refine ⟨SymmetricSmoothness.target_ne_zero, SymmetricSmoothness.target_homogeneous,
    ?_, hden, ?_, ?_, certificateDenominator_legal D L hLD hlegal, ?_⟩
  · simpa using HodgeComputer.Homogeneous.of_isHomogeneous SymmetricSmoothness.source_homogeneous
  · rw [hhom.totalDegree hden]
    exact hhom
  · intro i
    rw [hhom.totalDegree hden]
    convert HodgeComputer.Homogeneous.of_isHomogeneous
      (certificateNumerator_homogeneous N L hLN i) using 1 <;> push_cast <;> omega
  · apply HodgeComputer.normalized_identity
    · simpa only [Nat.cast_one, one_mul] using hn
    · simpa only [pow_one] using hd

theorem certificate_of_affine_normalized
    (D Q : ChartPoly) (N : Fin 5 → ChartPoly) (hD : D ≠ 0)
    (hlegal : IsRelPrime WeightedPrimitiveTransport.chartEquation D)
    (hnormal : HodgeTestbed.directional WeightedPrimitiveTransport.chartEquation N =
      WeightedPrimitiveTransport.chartSource*D)
    (hdiv : HodgeTestbed.divergenceNumerator D N =
      WeightedPrimitiveTransport.chartEquation*Q) :
    HodgeComputer.HasCertificate HodgeSubmission.F 1 HodgeSubmission.A := by
  let L := max 5 (max D.totalDegree (max Q.totalDegree
    (Finset.univ.sup (fun i => (N i).totalDegree))))
  have hL : 5 ≤ L := Nat.le_max_left _ _
  have hLD : D.totalDegree ≤ L :=
    (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)
  have hLQ : Q.totalDegree ≤ L :=
    (Nat.le_max_left _ _).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  have hLN : ∀ i, (N i).totalDegree ≤ L := by
    intro i
    have hi : (N i).totalDegree ≤ Finset.univ.sup (fun j => (N j).totalDegree) :=
      Finset.le_sup (f := fun j => (N j).totalDegree) (Finset.mem_univ i)
    dsimp [L]
    omega
  exact (explicit_verify D Q N L hL hD hLD hLN hLQ hlegal hnormal hdiv).hasCertificate

def mergeNumerators (Nv : ChartPoly) (N : Fin 4 → ChartPoly) : Fin 5 → ChartPoly :=
  ![N 0, N 1, N 2, N 3, Nv]

theorem mergeNumerators_directional (P Nv : ChartPoly) (N : Fin 4 → ChartPoly) :
    HodgeTestbed.directional P (mergeNumerators Nv N) =
      Nv*pderiv 4 P + ∑ i : Fin 4, N i*pderiv i.castSucc P := by
  simp [HodgeTestbed.directional, mergeNumerators, Fin.sum_univ_succ]
  ring

theorem mergeNumerators_divergence (D Nv : ChartPoly) (N : Fin 4 → ChartPoly) :
    HodgeTestbed.divergenceNumerator D (mergeNumerators Nv N) =
      residueDivNum WeightedPrimitiveTransport.normalPartial
        WeightedPrimitiveTransport.tangentPartial D Nv N := by
  simp [HodgeTestbed.divergenceNumerator, HodgeTestbed.divergence,
    HodgeTestbed.directional, mergeNumerators, residueDivNum, Fin.sum_univ_succ,
    WeightedPrimitiveTransport.normalPartial, WeightedPrimitiveTransport.tangentPartial]
  ring

/-- The transport admission is discharged once the actual relative primitive
is supplied. The existence of that primitive remains the geometric problem. -/
theorem certificate_of_relative_primitive (beta : SymmetricPrimitiveEndpoint.RelativePrimitive) :
    HodgeComputer.HasCertificate HodgeSubmission.F 1 HodgeSubmission.A := by
  obtain ⟨D, Nv, N, Q, hD, hlegal, hn, hd, _⟩ :=
    SymmetricPrimitiveEndpoint.clear_relative_primitive beta
  apply certificate_of_affine_normalized D Q (mergeNumerators Nv N) hD hlegal
  · rw [mergeNumerators_directional]
    exact hn
  · rw [mergeNumerators_divergence]
    exact hd

#print axioms transported_normalized_equations
#print axioms explicit_verify
#print axioms certificate_of_relative_primitive

end SymmetricCertificateTransport
