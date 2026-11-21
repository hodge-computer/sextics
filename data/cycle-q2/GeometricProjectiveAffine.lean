import Proposal.GeometricProjectiveCharts
import Proposal.GeometricAffineCurveCharts

/-!
# The actual affine coordinate presentations of the projective curve

Degree-zero localization at a homogeneous coordinate is compared with the
literal dehomogenized polynomial quotient. The maps retain both parameters.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

namespace CycleQ2GeometricProjectiveAffine

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
open CycleQ2GeometricProjectiveCurve CycleQ2GeometricAffineCurveCharts
open CategoryTheory AlgebraicGeometry

/-- The homogeneous element defining an actual coordinate open. -/
abbrev coordinateDen (r θ : ℂ) (j : Fin 4) : CurveRing r θ := curveMap r θ (X j)

abbrev ProjectiveCoordinateRing (r θ : ℂ) (j : Fin 4) :=
  HomogeneousLocalization.Away (curveGrade r θ) (coordinateDen r θ j)

abbrev OrdinaryCoordinateLocalization (r θ : ℂ) (j : Fin 4) :=
  Localization.Away (coordinateDen r θ j)

def coordinateConstants (r θ : ℂ) (j : Fin 4) :
    ℂ →+* ProjectiveCoordinateRing r θ j :=
  (HomogeneousLocalization.fromZeroRingHom (curveGrade r θ)
    (Submonoid.powers (coordinateDen r θ j))).comp
      (algebraMap ℂ (curveGrade r θ 0))

instance coordinateAlgebra (r θ : ℂ) (j : Fin 4) :
    Algebra ℂ (ProjectiveCoordinateRing r θ j) :=
  (coordinateConstants r θ j).toAlgebra

@[simp] theorem val_algebraMap (r θ : ℂ) (j : Fin 4) (c : ℂ) :
    (algebraMap ℂ (ProjectiveCoordinateRing r θ j) c).val =
      algebraMap ℂ (OrdinaryCoordinateLocalization r θ j) c := by
  change Localization.mk (algebraMap ℂ (CurveRing r θ) c) 1 = _
  rw [Localization.mk_one_eq_algebraMap]
  exact IsScalarTower.algebraMap_apply ℂ (CurveRing r θ)
    (OrdinaryCoordinateLocalization r θ j) c

def toLocalization (r θ : ℂ) (j : Fin 4) :
    ProjectiveCoordinateRing r θ j →ₐ[ℂ] OrdinaryCoordinateLocalization r θ j where
  toRingHom := algebraMap _ _
  commutes' := val_algebraMap r θ j

@[simp] theorem toLocalization_apply (r θ : ℂ) (j : Fin 4)
    (a : ProjectiveCoordinateRing r θ j) : toLocalization r θ j a = a.val := rfl

/-- Homogeneity is used at the level of actual evaluation maps. -/
theorem aeval_mul_coordinates {S : Type*} [CommRing S] [Algebra ℂ S]
    (p : Poly) {n : ℕ} (hp : p.IsHomogeneous n) (u : S) (x : Fin 4 → S) :
    aeval (fun k => u * x k) p = u ^ n * aeval x p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  simp only [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [aeval_def, eval₂_monomial, Finsupp.prod, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hp.degree_eq_sum_deg_support hd]
  ring

def coordinateInverse (r θ : ℂ) (j : Fin 4) :
    OrdinaryCoordinateLocalization r θ j :=
  IsLocalization.Away.invSelf (coordinateDen r θ j)

@[simp] theorem coordinateDen_mul_inverse (r θ : ℂ) (j : Fin 4) :
    algebraMap (CurveRing r θ) (OrdinaryCoordinateLocalization r θ j)
        (coordinateDen r θ j) * coordinateInverse r θ j = 1 :=
  IsLocalization.Away.mul_invSelf _

/-- The fraction x_k/x_j has degree zero in the actual localization. -/
def coordinateRatio (r θ : ℂ) (j k : Fin 4) : ProjectiveCoordinateRing r θ j :=
  HomogeneousLocalization.mk
    ⟨1, ⟨curveMap r θ (X k), coordinate_mem_grade r θ k⟩,
      ⟨coordinateDen r θ j, coordinate_mem_grade r θ j⟩,
      Submonoid.mem_powers _⟩

@[simp] theorem coordinateRatio_self (r θ : ℂ) (j : Fin 4) :
    coordinateRatio r θ j j = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_one]
  change Localization.mk (coordinateDen r θ j)
    ⟨coordinateDen r θ j, Submonoid.mem_powers _⟩ = 1
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_self _ _

theorem coordinateRatio_val (r θ : ℂ) (j k : Fin 4) :
    (coordinateRatio r θ j k).val = coordinateInverse r θ j *
      algebraMap (CurveRing r θ) (OrdinaryCoordinateLocalization r θ j)
        (curveMap r θ (X k)) := by
  change Localization.mk (curveMap r θ (X k))
      ⟨coordinateDen r θ j, Submonoid.mem_powers _⟩ = _
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  exact mul_comm
    (algebraMap (CurveRing r θ) (OrdinaryCoordinateLocalization r θ j)
      (curveMap r θ (X k))) (coordinateInverse r θ j)

theorem homogeneousFraction_val (r θ : ℂ) (j : Fin 4) (n : ℕ)
    (a : CurveRing r θ) (ha : a ∈ curveGrade r θ (n • 1)) :
    (HomogeneousLocalization.Away.mk (curveGrade r θ)
      (show coordinateDen r θ j ∈ curveGrade r θ 1 from
        coordinate_mem_grade r θ j) n a ha).val =
      coordinateInverse r θ j ^ n *
        algebraMap (CurveRing r θ) (OrdinaryCoordinateLocalization r θ j) a := by
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  symm
  calc
    _ = (algebraMap (CurveRing r θ) (OrdinaryCoordinateLocalization r θ j)
        (coordinateDen r θ j) * coordinateInverse r θ j) ^ n *
      algebraMap (CurveRing r θ) (OrdinaryCoordinateLocalization r θ j) a := by
      ring
    _ = _ := by rw [coordinateDen_mul_inverse, one_pow, one_mul]

/-- Set the selected homogeneous coordinate to one, retaining the other three. -/
def dehomogenize (j : Fin 4) : Poly →ₐ[ℂ] AffinePoly :=
  aeval (Fin.insertNth j 1 (fun i : Fin 3 => X i))

@[simp] theorem dehomogenize_self (j : Fin 4) : dehomogenize j (X j) = 1 := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_succAbove (j : Fin 4) (i : Fin 3) :
    dehomogenize j (X (j.succAbove i)) = X i := by
  simp [dehomogenize]

def coordinateEquations (r θ : ℂ) (j : Fin 4) : Fin 2 → AffinePoly :=
  ![dehomogenize j (relation r 0), dehomogenize j (curveH θ)]

abbrev AffineCoordinateRing (r θ : ℂ) (j : Fin 4) :=
  ChartRing (coordinateEquations r θ j)

def chartMap (r θ : ℂ) (j : Fin 4) : AffinePoly →ₐ[ℂ] AffineCoordinateRing r θ j :=
  Ideal.Quotient.mkₐ ℂ (chartIdeal (coordinateEquations r θ j))

@[simp] theorem chartMap_equation (r θ : ℂ) (j : Fin 4) (i : Fin 2) :
    chartMap r θ j (coordinateEquations r θ j i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)

def dehomToChart (r θ : ℂ) (j : Fin 4) : Poly →ₐ[ℂ] AffineCoordinateRing r θ j :=
  (chartMap r θ j).comp (dehomogenize j)

private theorem curveIdeal_le_dehom_kernel (r θ : ℂ) (j : Fin 4) :
    curveIdeal r θ ≤ RingHom.ker (dehomToChart r θ j).toRingHom := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases (show p = relation r 0 ∨ p = curveH θ from hp) with rfl | rfl
  · exact chartMap_equation r θ j 0
  · exact chartMap_equation r θ j 1

def curveToChart (r θ : ℂ) (j : Fin 4) :
    CurveRing r θ →ₐ[ℂ] AffineCoordinateRing r θ j :=
  Ideal.Quotient.liftₐ (curveIdeal r θ) (dehomToChart r θ j)
    (fun _ hp => curveIdeal_le_dehom_kernel r θ j hp)

@[simp] theorem curveToChart_curveMap (r θ : ℂ) (j : Fin 4) (p : Poly) :
    curveToChart r θ j (curveMap r θ p) = chartMap r θ j (dehomogenize j p) := rfl

@[simp] theorem curveToChart_den (r θ : ℂ) (j : Fin 4) :
    curveToChart r θ j (coordinateDen r θ j) = 1 := by
  change chartMap r θ j (dehomogenize j (X j)) = 1
  rw [dehomogenize_self, map_one]

def localizedToChart (r θ : ℂ) (j : Fin 4) :
    OrdinaryCoordinateLocalization r θ j →ₐ[ℂ] AffineCoordinateRing r θ j :=
  IsLocalization.Away.liftAlgHom (coordinateDen r θ j)
    (f := curveToChart r θ j) (by rw [curveToChart_den]; exact isUnit_one)

theorem localizedToChart_fraction (r θ : ℂ) (j : Fin 4) (n : ℕ)
    (a : CurveRing r θ) :
    localizedToChart r θ j
        (Localization.mk a ⟨coordinateDen r θ j ^ n, n, rfl⟩) =
      curveToChart r θ j a := by
  simp only [localizedToChart, IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift, Localization.mk_eq_mk', IsLocalization.lift_mk'_spec]
  change curveToChart r θ j a =
    curveToChart r θ j (coordinateDen r θ j ^ n) * curveToChart r θ j a
  rw [map_pow, curveToChart_den, one_pow, one_mul]

def toChart (r θ : ℂ) (j : Fin 4) :
    ProjectiveCoordinateRing r θ j →ₐ[ℂ] AffineCoordinateRing r θ j :=
  (localizedToChart r θ j).comp (toLocalization r θ j)

theorem toChart_fraction (r θ : ℂ) (j : Fin 4) (n : ℕ)
    (a : CurveRing r θ) (ha : a ∈ curveGrade r θ (n • 1)) :
    toChart r θ j (HomogeneousLocalization.Away.mk (curveGrade r θ)
        (show coordinateDen r θ j ∈ curveGrade r θ 1 from
          coordinate_mem_grade r θ j) n a ha) =
      curveToChart r θ j a :=
  localizedToChart_fraction r θ j n a

@[simp] theorem toChart_coordinateRatio (r θ : ℂ) (j k : Fin 4) :
    toChart r θ j (coordinateRatio r θ j k) =
      chartMap r θ j (dehomogenize j (X k)) := by
  change localizedToChart r θ j
    (Localization.mk (curveMap r θ (X k))
      ⟨coordinateDen r θ j, Submonoid.mem_powers _⟩) =
    curveToChart r θ j (curveMap r θ (X k))
  simpa only [pow_one] using
    localizedToChart_fraction r θ j 1 (curveMap r θ (X k))

def localizedPolynomial (r θ : ℂ) (j : Fin 4) :
    Poly →ₐ[ℂ] OrdinaryCoordinateLocalization r θ j :=
  (IsScalarTower.toAlgHom ℂ (CurveRing r θ) (OrdinaryCoordinateLocalization r θ j)).comp
    (Ideal.Quotient.mkₐ ℂ (curveIdeal r θ))

def ratioEvaluation (r θ : ℂ) (j : Fin 4) : Poly →ₐ[ℂ] ProjectiveCoordinateRing r θ j :=
  aeval (coordinateRatio r θ j)

theorem ratioEvaluation_val (r θ : ℂ) (j : Fin 4) (p : Poly) {n : ℕ}
    (hp : p.IsHomogeneous n) :
    (ratioEvaluation r θ j p).val =
      coordinateInverse r θ j ^ n * localizedPolynomial r θ j p := by
  have he : (toLocalization r θ j).comp (ratioEvaluation r θ j) =
      aeval (fun k => coordinateInverse r θ j * localizedPolynomial r θ j (X k)) := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [AlgHom.comp_apply, ratioEvaluation, aeval_X, toLocalization_apply]
    exact coordinateRatio_val r θ j k
  have hx : aeval (fun k => localizedPolynomial r θ j (X k)) =
      localizedPolynomial r θ j := by
    apply MvPolynomial.algHom_ext
    intro k
    exact aeval_X _ _
  calc
    _ = aeval (fun k => coordinateInverse r θ j *
        localizedPolynomial r θ j (X k)) p :=
      congrArg (fun f : Poly →ₐ[ℂ] OrdinaryCoordinateLocalization r θ j => f p) he
    _ = coordinateInverse r θ j ^ n *
        aeval (fun k => localizedPolynomial r θ j (X k)) p :=
      aeval_mul_coordinates p hp _ _
    _ = _ := congrArg (fun z => coordinateInverse r θ j ^ n * z)
      (congrArg (fun f : Poly →ₐ[ℂ] OrdinaryCoordinateLocalization r θ j => f p) hx)

theorem ratioEvaluation_quadric (r θ : ℂ) (j : Fin 4) :
    ratioEvaluation r θ j (relation r 0) = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [ratioEvaluation_val r θ j _ (relation_zero_homogeneous r),
    HomogeneousLocalization.val_zero]
  change coordinateInverse r θ j ^ 2 *
    algebraMap (CurveRing r θ) (OrdinaryCoordinateLocalization r θ j)
      (curveMap r θ (relation r 0)) = 0
  rw [curveMap_f1, map_zero, mul_zero]

theorem ratioEvaluation_cubic (r θ : ℂ) (j : Fin 4) :
    ratioEvaluation r θ j (curveH θ) = 0 := by
  apply HomogeneousLocalization.val_injective
  rw [ratioEvaluation_val r θ j _ (sparse_curveH_homogeneous θ),
    HomogeneousLocalization.val_zero]
  change coordinateInverse r θ j ^ 3 *
    algebraMap (CurveRing r θ) (OrdinaryCoordinateLocalization r θ j)
      (curveMap r θ (curveH θ)) = 0
  rw [curveMap_h, map_zero, mul_zero]

def chartEvaluation (r θ : ℂ) (j : Fin 4) :
    AffinePoly →ₐ[ℂ] ProjectiveCoordinateRing r θ j :=
  aeval (fun i => coordinateRatio r θ j (j.succAbove i))

theorem chartEvaluation_dehomogenize (r θ : ℂ) (j : Fin 4) :
    (chartEvaluation r θ j).comp (dehomogenize j) = ratioEvaluation r θ j := by
  apply MvPolynomial.algHom_ext
  intro k
  refine Fin.succAboveCases j ?_ (fun i => ?_) k
  · simp [chartEvaluation, dehomogenize, ratioEvaluation]
  · simp [chartEvaluation, dehomogenize, ratioEvaluation]

private theorem chartIdeal_le_ratio_kernel (r θ : ℂ) (j : Fin 4) :
    chartIdeal (coordinateEquations r θ j) ≤ RingHom.ker (chartEvaluation r θ j).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · change ((chartEvaluation r θ j).comp (dehomogenize j)) (relation r 0) = 0
    rw [chartEvaluation_dehomogenize]
    exact ratioEvaluation_quadric r θ j
  · change ((chartEvaluation r θ j).comp (dehomogenize j)) (curveH θ) = 0
    rw [chartEvaluation_dehomogenize]
    exact ratioEvaluation_cubic r θ j

def fromChart (r θ : ℂ) (j : Fin 4) :
    AffineCoordinateRing r θ j →ₐ[ℂ] ProjectiveCoordinateRing r θ j :=
  Ideal.Quotient.liftₐ (chartIdeal (coordinateEquations r θ j)) (chartEvaluation r θ j)
    (fun _ hp => chartIdeal_le_ratio_kernel r θ j hp)

@[simp] theorem fromChart_chartMap (r θ : ℂ) (j : Fin 4) (p : AffinePoly) :
    fromChart r θ j (chartMap r θ j p) = chartEvaluation r θ j p := rfl

theorem fromChart_dehomogenize (r θ : ℂ) (j : Fin 4) (p : Poly) :
    fromChart r θ j (chartMap r θ j (dehomogenize j p)) = ratioEvaluation r θ j p :=
  congrArg (fun f : Poly →ₐ[ℂ] ProjectiveCoordinateRing r θ j => f p)
    (chartEvaluation_dehomogenize r θ j)

theorem toChart_fromChart (r θ : ℂ) (j : Fin 4) :
    (toChart r θ j).comp (fromChart r θ j) = AlgHom.id ℂ (AffineCoordinateRing r θ j) := by
  apply Ideal.Quotient.algHom_ext ℂ
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  change toChart r θ j (fromChart r θ j (chartMap r θ j (X i))) = chartMap r θ j (X i)
  rw [fromChart_chartMap]
  simp only [chartEvaluation, aeval_X, toChart_coordinateRatio, dehomogenize_succAbove]

theorem fromChart_toChart (r θ : ℂ) (j : Fin 4) :
    (fromChart r θ j).comp (toChart r θ j) = AlgHom.id ℂ (ProjectiveCoordinateRing r θ j) := by
  apply AlgHom.ext
  intro z
  change fromChart r θ j (toChart r θ j z) = z
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (curveGrade r θ)
    (show coordinateDen r θ j ∈ curveGrade r θ 1 from coordinate_mem_grade r θ j) z
  obtain ⟨p, hp, rfl⟩ := ha
  rw [toChart_fraction]
  change fromChart r θ j (curveToChart r θ j (curveMap r θ p)) = _
  rw [curveToChart_curveMap, fromChart_dehomogenize]
  apply HomogeneousLocalization.val_injective
  have hp' : p.IsHomogeneous n := by simpa using hp
  rw [ratioEvaluation_val r θ j p hp']
  exact (homogeneousFraction_val r θ j n (curveMap r θ p)
    (curveMap_mem_grade r θ hp)).symm

/-- The actual homogeneous coordinate open has its actual dehomogenized
polynomial presentation, with mutually inverse maps constructed above. -/
def coordinateEquiv (r θ : ℂ) (j : Fin 4) :
    ProjectiveCoordinateRing r θ j ≃ₐ[ℂ] AffineCoordinateRing r θ j :=
  AlgEquiv.ofAlgHom (toChart r θ j) (fromChart r θ j)
    (toChart_fromChart r θ j) (fromChart_toChart r θ j)

/-! ## The literal two affine equations used by the differential calculation -/

theorem dehomogenize_one : dehomogenize (1 : Fin 4) = firstDehomogenize := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [dehomogenize, firstDehomogenize, aeval_X]
  fin_cases i <;> rfl

theorem dehomogenize_two : dehomogenize (2 : Fin 4) = secondDehomogenize := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [dehomogenize, secondDehomogenize, aeval_X]
  fin_cases i <;> rfl

theorem coordinateEquations_one (r θ : ℂ) :
    coordinateEquations r θ 1 = ![firstQuadric r, firstCubic θ] := by
  simp only [coordinateEquations, dehomogenize_one,
    firstDehomogenize_quadric, firstDehomogenize_cubic]

theorem coordinateEquations_two (r θ : ℂ) :
    coordinateEquations r θ 2 = ![secondQuadric r, secondCubic θ] := by
  simp only [coordinateEquations, dehomogenize_two,
    secondDehomogenize_quadric, secondDehomogenize_cubic]

abbrev FirstChartRing (r θ : ℂ) := ChartRing ![firstQuadric r, firstCubic θ]
abbrev SecondChartRing (r θ : ℂ) := ChartRing ![secondQuadric r, secondCubic θ]

def firstChartMap (r θ : ℂ) : AffinePoly →ₐ[ℂ] FirstChartRing r θ :=
  Ideal.Quotient.mkₐ ℂ (chartIdeal ![firstQuadric r, firstCubic θ])

def secondChartMap (r θ : ℂ) : AffinePoly →ₐ[ℂ] SecondChartRing r θ :=
  Ideal.Quotient.mkₐ ℂ (chartIdeal ![secondQuadric r, secondCubic θ])

/-- The first homogeneous coordinate localization is the literal first
affine quotient, with its existing complex algebra structure. -/
def firstCoordinateEquiv (r θ : ℂ) :
    ProjectiveCoordinateRing r θ 1 ≃ₐ[ℂ] FirstChartRing r θ :=
  (coordinateEquiv r θ 1).trans
    (Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (coordinateEquations_one r θ)))

/-- The second homogeneous coordinate localization is the literal second
affine quotient, with its existing complex algebra structure. -/
def secondCoordinateEquiv (r θ : ℂ) :
    ProjectiveCoordinateRing r θ 2 ≃ₐ[ℂ] SecondChartRing r θ :=
  (coordinateEquiv r θ 2).trans
    (Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (coordinateEquations_two r θ)))

theorem firstCoordinateEquiv_fraction (r θ : ℂ) (n : ℕ) (p : Poly)
    (hp : p.IsHomogeneous n) :
    firstCoordinateEquiv r θ
        (HomogeneousLocalization.Away.mk (curveGrade r θ)
          (show coordinateDen r θ 1 ∈ curveGrade r θ 1 from
            coordinate_mem_grade r θ 1) n (curveMap r θ p)
          (by simpa using curveMap_mem_grade r θ hp)) =
      firstChartMap r θ (firstDehomogenize p) := by
  change Ideal.quotientEquivAlgOfEq ℂ
    (congrArg chartIdeal (coordinateEquations_one r θ)) (toChart r θ 1 _) = _
  rw [toChart_fraction, curveToChart_curveMap]
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (coordinateEquations_one r θ))
    (Ideal.Quotient.mk _ (dehomogenize 1 p)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, dehomogenize_one]
  rfl

theorem secondCoordinateEquiv_fraction (r θ : ℂ) (n : ℕ) (p : Poly)
    (hp : p.IsHomogeneous n) :
    secondCoordinateEquiv r θ
        (HomogeneousLocalization.Away.mk (curveGrade r θ)
          (show coordinateDen r θ 2 ∈ curveGrade r θ 1 from
            coordinate_mem_grade r θ 2) n (curveMap r θ p)
          (by simpa using curveMap_mem_grade r θ hp)) =
      secondChartMap r θ (secondDehomogenize p) := by
  change Ideal.quotientEquivAlgOfEq ℂ
    (congrArg chartIdeal (coordinateEquations_two r θ)) (toChart r θ 2 _) = _
  rw [toChart_fraction, curveToChart_curveMap]
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (coordinateEquations_two r θ))
    (Ideal.Quotient.mk _ (dehomogenize 2 p)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, dehomogenize_two]
  rfl

/-- The first quartic divided by x1^4 is exactly 3r²(x3/x1)². -/
theorem firstCoordinateEquiv_denominator (r θ : ℂ) :
    firstCoordinateEquiv r θ
        (HomogeneousLocalization.Away.mk (curveGrade r θ)
          (show coordinateDen r θ 1 ∈ curveGrade r θ 1 from
            coordinate_mem_grade r θ 1) 4 (curveG1 r θ)
          (by simpa using curveG1_mem_grade r θ)) =
      firstChartMap r θ (C (3 * r ^ 2) * X 2 ^ 2) := by
  change Ideal.quotientEquivAlgOfEq ℂ
    (congrArg chartIdeal (coordinateEquations_one r θ)) (toChart r θ 1 _) = _
  rw [toChart_fraction]
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (coordinateEquations_one r θ))
    (curveToChart r θ 1 (ambientCurveMap r θ (originalG1 r))) = _
  rw [ambientCurveMap_g1, curveToChart_curveMap]
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (coordinateEquations_one r θ))
    (Ideal.Quotient.mk _ (dehomogenize 1 _)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, dehomogenize_one]
  change firstChartMap r θ (firstDehomogenize _) = _
  simp [firstDehomogenize, CycleQ2SeedCech.curveA]

/-- The second quartic divided by x2^4 is the nonzero constant 3. -/
theorem secondCoordinateEquiv_denominator (r θ : ℂ) :
    secondCoordinateEquiv r θ
        (HomogeneousLocalization.Away.mk (curveGrade r θ)
          (show coordinateDen r θ 2 ∈ curveGrade r θ 1 from
            coordinate_mem_grade r θ 2) 4 (curveG2 r θ)
          (by simpa using curveG2_mem_grade r θ)) =
      algebraMap ℂ (SecondChartRing r θ) 3 := by
  change Ideal.quotientEquivAlgOfEq ℂ
    (congrArg chartIdeal (coordinateEquations_two r θ)) (toChart r θ 2 _) = _
  rw [toChart_fraction]
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (coordinateEquations_two r θ))
    (curveToChart r θ 2 (ambientCurveMap r θ originalG2)) = _
  rw [ambientCurveMap_g2, curveToChart_curveMap]
  change Ideal.quotientEquivAlgOfEq ℂ (congrArg chartIdeal (coordinateEquations_two r θ))
    (Ideal.Quotient.mk _ (dehomogenize 2 _)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk, dehomogenize_two]
  change secondChartMap r θ (secondDehomogenize _) = _
  simp [secondDehomogenize, CycleQ2SeedCech.curveB]

/-! ## Actual isomorphisms of schemes on the coordinate opens -/

/-- The canonical Proj affine chart, followed by the proved polynomial
presentation. This is an isomorphism of actual schemes and structure sheaves. -/
def coordinateChartIso (r θ : ℂ) (j : Fin 4) :
    (coordinateProjectivePatch r θ j).toScheme ≅
      Spec (CommRingCat.of (AffineCoordinateRing r θ j)) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (coordinateDen r θ j)
      (coordinate_mem_grade r θ j) (by decide) ≪≫
    Scheme.Spec.mapIso (coordinateEquiv r θ j).toRingEquiv.toCommRingCatIso.symm.op

def firstCoordinateChartIso (r θ : ℂ) :
    (coordinateProjectivePatch r θ 1).toScheme ≅
      Spec (CommRingCat.of (FirstChartRing r θ)) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (coordinateDen r θ 1)
      (coordinate_mem_grade r θ 1) (by decide) ≪≫
    Scheme.Spec.mapIso (firstCoordinateEquiv r θ).toRingEquiv.toCommRingCatIso.symm.op

def secondCoordinateChartIso (r θ : ℂ) :
    (coordinateProjectivePatch r θ 2).toScheme ≅
      Spec (CommRingCat.of (SecondChartRing r θ)) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (coordinateDen r θ 2)
      (coordinate_mem_grade r θ 2) (by decide) ≪≫
    Scheme.Spec.mapIso (secondCoordinateEquiv r θ).toRingEquiv.toCommRingCatIso.symm.op

/-- The first denominator open lies in the coordinate chart on which the
first affine differential frame is defined. -/
theorem firstProjectivePatch_le_firstCoordinate (r θ : ℂ) :
    firstProjectivePatch r θ ≤ coordinateProjectivePatch r θ 1 := by
  apply Proj.basicOpen_mono
  refine ⟨curveMap r θ (C (3 * r ^ 2) * X 1 * X 3 ^ 2), ?_⟩
  change ambientCurveMap r θ (originalG1 r) = _
  rw [ambientCurveMap_g1, ← map_mul]
  apply congrArg (curveMap r θ)
  simp only [CycleQ2SeedCech.curveA]
  ring

private theorem constant_basicOpen_eq_top (r θ c : ℂ) (hc : c ≠ 0) :
    Proj.basicOpen (curveGrade r θ) (curveMap r θ (C c)) = ⊤ := by
  apply top_unique
  intro q _
  change curveMap r θ (C c) ∉ q.asHomogeneousIdeal.toIdeal
  exact Ideal.notMem_of_isUnit q.asHomogeneousIdeal.toIdeal
    ((isUnit_iff_ne_zero.mpr hc).map C |>.map (curveMap r θ))

/-- The second denominator open is the entire second coordinate chart. -/
theorem secondProjectivePatch_eq_secondCoordinate (r θ : ℂ) :
    secondProjectivePatch r θ = coordinateProjectivePatch r θ 2 := by
  change Proj.basicOpen (curveGrade r θ) (ambientCurveMap r θ originalG2) = _
  rw [ambientCurveMap_g2, map_mul, map_pow, Proj.basicOpen_mul]
  rw [constant_basicOpen_eq_top r θ 3 (by norm_num), top_inf_eq]
  exact Proj.basicOpen_pow (curveGrade r θ) (curveMap r θ (X 2)) 4 (by decide)

theorem secondProjectivePatch_le_secondCoordinate (r θ : ℂ) :
    secondProjectivePatch r θ ≤ coordinateProjectivePatch r θ 2 :=
  le_of_eq (secondProjectivePatch_eq_secondCoordinate r θ)

/-- The two affine coordinate charts already cover when the original
quartic denominator charts cover. -/
theorem first_second_coordinate_cover (r θ : ℂ) (hr : r ≠ 0) :
    coordinateProjectivePatch r θ 1 ⊔ coordinateProjectivePatch r θ 2 = ⊤ := by
  apply top_unique
  rw [← projective_twoOpen_cover r θ hr]
  exact sup_le_sup (firstProjectivePatch_le_firstCoordinate r θ)
    (secondProjectivePatch_le_secondCoordinate r θ)

end CycleQ2GeometricProjectiveAffine

end
