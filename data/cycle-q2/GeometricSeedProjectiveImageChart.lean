import Proposal.SegreFactorCechComplex
import Proposal.GeometricSurfaceCoordinateSections
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The actual Segre image and orbit-ideal dual on projective charts

The coordinate rings below are the actual affine charts of the surface at
`(r, theta) = (57, 1)`. The comparison with the incidence seed at `(57, I)`
uses `seedRingEquiv`, which is the identity on the five polynomial
coordinates and identifies their two defining ideals.

On each of the three weight-one coordinate charts, the original linkage
pairing identifies the image of the dehomogenized degree-fourteen matrix
with the dual of the actual three-component orbit ideal. Regularity is
proved by embedding the dehomogenized ring into the original homogeneous
localization; it is not assumed after a quotient operation.

The resulting associated-sheaf isomorphism is a chart of the comparison
`image(14) = I_E^dual(4)`. The degree-four transition is kept separate from
this local trivialization. This file does not assert a global Chern-class
or cycle-class comparison.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveImageChart

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift CycleQ2CartierSurfaceGrading
  CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2SegreTangentLocal
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
  CycleQ2SegreFactorSequence CycleQ2SegreLinkageDuality CycleQ2SegreLinkageImage

local instance imageSeedCommRing : CommRing (SeedRing (57 : ℂ) Complex.I) :=
  Ideal.Quotient.commRing
    (CycleQ2IncidenceNormalForm.equationsIdeal
      (CycleQ2IncidenceEquations.smoothH Complex.I)
      (CycleQ2IncidenceEquations.smoothF (57 : ℂ) Complex.I))

local instance imageSurfaceCommRing : CommRing (SurfaceRing 57 1) :=
  Ideal.Quotient.commRing (surfaceIdeal 57 1)

section BaseChange

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Transport the literal linkage data. Its sole nonformal condition,
regularity of the transported linkage element, is proved below for the
actual projective chart map. -/
def mapFactorData (F : FactorData A) (f : A →+* B)
    (hf : Function.Injective (fun z : B => f F.linkage * z)) : FactorData B where
  leftIdeal := F.leftIdeal.map f
  rightIdeal := F.rightIdeal.map f
  linkage := f F.linkage
  matrix := f.mapMatrix F.matrix
  left i := f (F.left i)
  right j := f (F.right j)
  left_mem i := Ideal.mem_map_of_mem f (F.left_mem i)
  right_mem j := Ideal.mem_map_of_mem f (F.right_mem j)
  product i j := by
    simpa only [map_mul, RingHom.mapMatrix_apply, Matrix.map_apply] using
      congrArg f (F.product i j)
  ideals_product := by
    rw [← Ideal.map_mul]
    simpa only [Ideal.map_span, Set.image_singleton] using
      Ideal.map_mono (f := f) F.ideals_product
  regular := hf
  cofactors_zero := CycleQ2SegreCech.cofactors_map_zero f F.matrix F.cofactors_zero
  entries_generate := by
    have h := congrArg (Ideal.map f) F.entries_generate
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def,
      Ideal.map_top, RingHom.mapMatrix_apply, Matrix.map_apply] using h

def mappedLeft (F : FactorData A) (f : A →+* B)
    (hf : Function.Injective (fun z : B => f F.linkage * z))
    (x : F.leftIdeal) : (mapFactorData F f hf).leftIdeal :=
  ⟨f x.val, Ideal.mem_map_of_mem f x.property⟩

def mappedRight (F : FactorData A) (f : A →+* B)
    (hf : Function.Injective (fun z : B => f F.linkage * z))
    (y : F.rightIdeal) : (mapFactorData F f hf).rightIdeal :=
  ⟨f y.val, Ideal.mem_map_of_mem f y.property⟩

/-- The new pairing is the base change of the old pairing on every pair
of original ideal elements, not merely on the selected generators. -/
theorem mapFactorData_pairing (F : FactorData A) (f : A →+* B)
    (hf : Function.Injective (fun z : B => f F.linkage * z))
    (x : F.leftIdeal) (y : F.rightIdeal) :
    pairing (mapFactorData F f hf) (mappedRight F f hf y) (mappedLeft F f hf x) =
      f (pairing F y x) := by
  apply hf
  calc
    _ = f (x : A) * f (y : A) :=
      linkage_pair (mapFactorData F f hf) (mappedLeft F f hf x) (mappedRight F f hf y)
    _ = f ((x : A) * (y : A)) := (map_mul f _ _).symm
    _ = f (F.linkage * pairing F y x) := congrArg f (linkage_pair F x y).symm
    _ = _ := map_mul f _ _

end BaseChange

abbrev AffineRing (i : Fin 3) := DehomogenizedRing 57 1 i.succ

abbrev ConeRing (i : Fin 3) := CycleQ2SegreFactorChartExact.Chart {i}

def localizingCoordinate (i : Fin 3) : SeedRing (57 : ℂ) Complex.I :=
  algebraMap (Base ℂ) (SeedRing (57 : ℂ) Complex.I) (baseProduct ℂ {i})

local instance cone_isLocalization (i : Fin 3) :
    IsLocalization.Away (localizingCoordinate i) (ConeRing i) := by
  change IsLocalization (Submonoid.powers (localizingCoordinate i)) (ConeRing i)
  dsimp only [localizingCoordinate]
  rw [← Submonoid.map_powers]
  infer_instance

theorem remainingIndex_eq (i : Fin 3) : remainingIndex i = i.succ.castSucc := by
  fin_cases i <;> rfl

theorem localizingCoordinate_eq (i : Fin 3) :
    localizingCoordinate i =
      seedRingEquiv 57 (surfaceQuotient 57 1 (X i.succ.castSucc)) := by
  rw [localizingCoordinate, ← seedRingEquiv_coordinateProduct]
  congr 1
  simp only [coordinateProduct, Finset.prod_singleton, coordinateElement,
    remainingIndex_eq]
  rfl

def seedToChart (i : Fin 3) : SeedRing (57 : ℂ) Complex.I →+* AffineRing i :=
  (surfaceToDehomogenized 57 1 i.succ).comp (seedRingEquiv 57).symm.toRingHom

theorem seedToChart_localizingCoordinate (i : Fin 3) :
    seedToChart i (localizingCoordinate i) = 1 := by
  rw [localizingCoordinate_eq]
  change surfaceToDehomogenized 57 1 i.succ
    ((seedRingEquiv 57).symm (seedRingEquiv 57
      (surfaceQuotient 57 1 (X i.succ.castSucc)))) = 1
  rw [AlgEquiv.symm_apply_apply, surfaceToDehomogenized_self]

def coneToChart (i : Fin 3) : ConeRing i →+* AffineRing i :=
  IsLocalization.Away.lift (S := ConeRing i) (g := seedToChart i)
    (localizingCoordinate i) (by rw [seedToChart_localizingCoordinate]; exact isUnit_one)

@[simp] theorem coneToChart_base (i : Fin 3) (x : SeedRing (57 : ℂ) Complex.I) :
    coneToChart i (CycleQ2SegreFactorChartExact.chartMap {i} x) = seedToChart i x :=
  IsLocalization.Away.lift_eq _ _ x

def conePolynomial (i : Fin 3) : WeightedPoly →+* ConeRing i :=
  (CycleQ2SegreFactorChartExact.chartMap {i}).comp
    (CycleQ2SeedLinkagePrincipal.quotientMap (57 : ℂ) Complex.I)

def affinePolynomial (i : Fin 3) : WeightedPoly →+* AffineRing i :=
  (dehomogenizedMap 57 1 i.succ).comp (dehomogenize i.succ).toRingHom

@[simp] theorem coneToChart_polynomial (i : Fin 3) (p : WeightedPoly) :
    coneToChart i (conePolynomial i p) = affinePolynomial i p := by
  change coneToChart i (CycleQ2SegreFactorChartExact.chartMap {i}
    (Ideal.Quotient.mk _ p)) = _
  rw [coneToChart_base, ← seedRingEquiv_quotient 57 p]
  change surfaceToDehomogenized 57 1 i.succ
    ((seedRingEquiv 57).symm (seedRingEquiv 57 (quotientMap 57 1 p))) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

private theorem coordinateSubmonoid_map (i : Fin 3) :
    (Submonoid.powers (surfaceQuotient 57 1 (X i.succ.castSucc))).map
        (seedRingEquiv 57).toRingEquiv.toMonoidHom =
      Submonoid.powers (localizingCoordinate i) := by
  rw [Submonoid.map_powers]
  exact congrArg Submonoid.powers (localizingCoordinate_eq i).symm

/-- The full coordinate localization agrees with the original seed
localization, before taking its homogeneous degree-zero subring. -/
def coneCoordinateEquiv (i : Fin 3) :
    CoordinateLocalization 57 1 i.succ ≃+* ConeRing i :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (surfaceQuotient 57 1 (X i.succ.castSucc)))
    (T := Submonoid.powers (localizingCoordinate i))
    (CoordinateLocalization 57 1 i.succ) (ConeRing i)
    (seedRingEquiv 57).toRingEquiv
    (coordinateSubmonoid_map i)

@[simp] theorem coneCoordinateEquiv_base (i : Fin 3) (x : SurfaceRing 57 1) :
    coneCoordinateEquiv i
      (algebraMap (SurfaceRing 57 1) (CoordinateLocalization 57 1 i.succ) x) =
      CycleQ2SegreFactorChartExact.chartMap {i} (seedRingEquiv 57 x) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ x

@[simp] theorem coneCoordinateEquiv_polynomial (i : Fin 3) (p : WeightedPoly) :
    coneCoordinateEquiv i
      (algebraMap (SurfaceRing 57 1) (CoordinateLocalization 57 1 i.succ)
        (surfaceQuotient 57 1 p)) = conePolynomial i p := by
  rw [coneCoordinateEquiv_base]
  change CycleQ2SegreFactorChartExact.chartMap {i}
    (seedRingEquiv 57 (quotientMap 57 1 p)) = _
  rw [seedRingEquiv_quotient]
  rfl

/-- The faithful map from the actual affine chart into its cone chart
sends a homogeneous polynomial to its normalized homogeneous fraction. -/
def affineCoefficient (i : Fin 3) : AffineRing i →+* ConeRing i :=
  (coneCoordinateEquiv i).toRingHom.comp
    ((algebraMap (CoordinateRing 57 1 i.succ) (CoordinateLocalization 57 1 i.succ)).comp
      (coordinateChartEquiv 57 1 i.succ).symm.toRingHom)

theorem affineCoefficient_injective (i : Fin 3) : Function.Injective (affineCoefficient i) := by
  intro x y h
  apply (coordinateChartEquiv 57 1 i.succ).symm.injective
  apply HomogeneousLocalization.val_injective
  exact (coneCoordinateEquiv i).injective h

theorem affineCoefficient_homogeneous (i : Fin 3) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) :
    affineCoefficient i (affinePolynomial i p) *
        conePolynomial i (X i.succ.castSucc) ^ n = conePolynomial i p := by
  let a := algebraMap (SurfaceRing 57 1) (CoordinateLocalization 57 1 i.succ)
    (surfaceQuotient 57 1 p)
  let x := algebraMap (SurfaceRing 57 1) (CoordinateLocalization 57 1 i.succ)
    (surfaceQuotient 57 1 (X i.succ.castSucc))
  let t : CoordinateLocalization 57 1 i.succ :=
    IsLocalization.Away.invSelf (surfaceQuotient 57 1 (X i.succ.castSucc))
  have ht : t * x = 1 := by
    rw [mul_comm]
    exact IsLocalization.Away.mul_invSelf _
  have hn : affineCoefficient i (affinePolynomial i p) =
      coneCoordinateEquiv i (a * t ^ n) := by
    change coneCoordinateEquiv i
      ((coordinateChartEquiv 57 1 i.succ).symm
        (dehomogenizedMap 57 1 i.succ (dehomogenize i.succ p))).val = _
    rw [← coordinateChartEquiv_homogeneousFraction 57 1 i.succ n p hp,
      RingEquiv.symm_apply_apply, homogeneousFraction_val]
  rw [hn, ← coneCoordinateEquiv_polynomial i (X i.succ.castSucc),
    ← coneCoordinateEquiv_polynomial i p]
  change coneCoordinateEquiv i (a * t ^ n) * coneCoordinateEquiv i x ^ n =
    coneCoordinateEquiv i a
  rw [← map_pow, ← map_mul]
  congr 1
  rw [mul_assoc, ← mul_pow, ht, one_pow, mul_one]

/-- Regularity of an actual homogeneous cone equation descends to its
dehomogenization. The proof uses the faithful coefficient embedding. -/
theorem affinePolynomial_regular (i : Fin 3) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n)
    (hreg : Function.Injective (fun z : ConeRing i => conePolynomial i p * z)) :
    Function.Injective (fun z : AffineRing i => affinePolynomial i p * z) := by
  intro x y h
  apply affineCoefficient_injective i
  apply hreg
  have h' := congrArg (affineCoefficient i) h
  simp only [map_mul] at h'
  have hn := affineCoefficient_homogeneous i n p hp
  calc
    conePolynomial i p * affineCoefficient i x =
        (affineCoefficient i (affinePolynomial i p) *
          conePolynomial i (X i.succ.castSucc) ^ n) * affineCoefficient i x := by rw [hn]
    _ = conePolynomial i (X i.succ.castSucc) ^ n *
        (affineCoefficient i (affinePolynomial i p) * affineCoefficient i x) := by ring
    _ = conePolynomial i (X i.succ.castSucc) ^ n *
        (affineCoefficient i (affinePolynomial i p) * affineCoefficient i y) := by rw [h']
    _ = (affineCoefficient i (affinePolynomial i p) *
          conePolynomial i (X i.succ.castSucc) ^ n) * affineCoefficient i y := by ring
    _ = conePolynomial i p * affineCoefficient i y := by rw [hn]

theorem linkage_weighted_homogeneous :
    (CycleQ2SeedFactorHomogeneous.polynomialLinkage (57 : ℂ)).IsWeightedHomogeneous weight 4 :=
  CycleQ2GeometricIncidenceProj.homogeneous_of_character
    (CycleQ2SeedFactorHomogeneous.polynomialLinkage_homogeneous (57 : ℂ))

theorem chart_linkage_regular (i : Fin 3) :
    Function.Injective (fun z : AffineRing i =>
      coneToChart i (CycleQ2SegreFactorChartExact.linkage {i}) * z) := by
  change Function.Injective (fun z : AffineRing i =>
    coneToChart i (conePolynomial i
      (CycleQ2SeedFactorHomogeneous.polynomialLinkage (57 : ℂ))) * z)
  rw [coneToChart_polynomial]
  exact affinePolynomial_regular i 4 _ linkage_weighted_homogeneous
    (CycleQ2SegreFactorChartExact.linkage_regular {i})

def chartFactorData (i : Fin 3) : FactorData (AffineRing i) :=
  mapFactorData (CycleQ2SegreFactorChartExact.factorData {i} (Finset.singleton_nonempty i))
    (coneToChart i) (chart_linkage_regular i)

abbrev OrbitIdeal (i : Fin 3) := (chartFactorData i).leftIdeal

abbrev ImageModule (i : Fin 3) := LinearMap.range (chartFactorData i).matrix.mulVecLin

abbrev OrbitDual (i : Fin 3) := OrbitIdeal i →ₗ[AffineRing i] AffineRing i

theorem chartMatrix_polynomial (i a b : Fin 3) :
    (chartFactorData i).matrix a b =
      affinePolynomial i (CycleQ2IncidenceEquations.rawSeedMatrix (57 : ℂ) a b) := by
  change coneToChart i (conePolynomial i
    (CycleQ2IncidenceEquations.rawSeedMatrix (57 : ℂ) a b)) = _
  exact coneToChart_polynomial i _

def imageDualEquiv (i : Fin 3) : ImageModule i ≃ₗ[AffineRing i] OrbitDual i :=
  (rightEquivImage (chartFactorData i)).symm.trans (rightEquivLeftDual (chartFactorData i))

/-- Evaluation at the actual degree-ten left generators recovers the
literal vector entries. This characterizes the chart comparison. -/
theorem imageDualEquiv_selected (i : Fin 3) (z : ImageModule i) (a : Fin 3) :
    imageDualEquiv i z (leftElement (chartFactorData i) a) = z.val a := by
  obtain ⟨y, rfl⟩ := (rightEquivImage (chartFactorData i)).surjective z
  change pairing (chartFactorData i)
    ((rightEquivImage (chartFactorData i)).symm
      (rightEquivImage (chartFactorData i) y)) (leftElement (chartFactorData i) a) = _
  rw [LinearEquiv.symm_apply_apply]
  exact (rightEquivImage_apply (chartFactorData i) y a).symm

/-- The affine comparison is the original `actualDuality` after the
actual dehomogenization map, for arbitrary original ideal elements. -/
theorem chartDuality_original (i : Fin 3)
    (x : CycleQ2SegreFactorChartExact.leftIdeal {i})
    (y : CycleQ2SegreFactorChartExact.rightIdeal {i}) :
    pairing (chartFactorData i)
      (mappedRight (CycleQ2SegreFactorChartExact.factorData {i} (Finset.singleton_nonempty i))
        (coneToChart i) (chart_linkage_regular i) y)
      (mappedLeft (CycleQ2SegreFactorChartExact.factorData {i} (Finset.singleton_nonempty i))
        (coneToChart i) (chart_linkage_regular i) x) =
      coneToChart i (CycleQ2SegreSeedLinkageDuality.actualDuality {i}
        (Finset.singleton_nonempty i) y x) :=
  mapFactorData_pairing
    (CycleQ2SegreFactorChartExact.factorData {i} (Finset.singleton_nonempty i))
    (coneToChart i) (chart_linkage_regular i) x y

def affineComponentIdeal (i : Fin 3) (z : ℂ) : Ideal (AffineRing i) :=
  (CycleQ2SeedLinkageComponents.localComponent .left (57 : ℂ) Complex.I {i} z).map
    (coneToChart i)

/-- The ideal in the target of the duality is the product of the three
literal orbit-component ideals, on the actual projective chart. -/
theorem orbitIdeal_eq_component_product (i : Fin 3) :
    OrbitIdeal i = affineComponentIdeal i 1 *
      affineComponentIdeal i CycleQ2LinkageComponentAlgebra.complexRoot *
      affineComponentIdeal i (CycleQ2LinkageComponentAlgebra.complexRoot ^ 2) := by
  have hI : Complex.I ≠ (1 : ℂ) := by
    intro h
    have h' := congrArg Complex.im h
    norm_num at h'
  have h := CycleQ2SeedLinkageOrbitProduct.localized_linkageIdeal_eq_product
    .left (57 : ℂ) Complex.I (by norm_num) Complex.I_ne_zero hI
    {i} (Finset.singleton_nonempty i)
  have hm := congrArg (Ideal.map (coneToChart i)) h
  rw [Ideal.map_mul, Ideal.map_mul] at hm
  change ((CycleQ2SeedLinkageComponents.localLinkageIdeal
      .left (57 : ℂ) Complex.I {i}).map (coneToChart i)) = _
  exact hm

section LiteralCurve

open CycleQ2SeedLinkageComponents CycleQ2SeedLinkageOrbitCover
  CycleQ2LinkageComponentDecomposition

def originalAffineCurveIdeal (i : Fin 3) : Ideal (AffineRing i) :=
  (curveIdealOnSurface 57 1).map (surfaceToDehomogenized 57 1 i.succ)

private theorem originalAffineCurveIdeal_generators (i : Fin 3) :
    originalAffineCurveIdeal i = Ideal.span (Set.range (fun j : Fin 2 =>
      affinePolynomial i (![originalF1 57, originalF2] j))) := by
  change ((ambientCurveIdeal 57 1).map (Ideal.Quotient.mk (surfaceIdeal 57 1))).map
      (surfaceToDehomogenized 57 1 i.succ) = _
  rw [Ideal.map_map, ambientCurveIdeal, Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact Ideal.subset_span ⟨0, rfl⟩
    · exact Ideal.subset_span ⟨1, rfl⟩
    · change affinePolynomial i (thetaH 1) ∈ _
      have hz : affinePolynomial i (thetaH 1) = 0 :=
        dehomogenizedMap_equation 57 1 i.succ 1
      rw [hz]
      exact Ideal.zero_mem _
  · apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    fin_cases j
    · exact Ideal.subset_span ⟨0, rfl⟩
    · exact Ideal.subset_span ⟨1, rfl⟩

private theorem affineComponentIdeal_one_generators (i : Fin 3) :
    affineComponentIdeal i 1 = Ideal.span (Set.range (fun j : Fin 2 =>
      affinePolynomial i (![originalF1 57, originalF2] j))) := by
  let g : Fin 2 → ConeRing i := componentGenerator
    (localScalar (57 : ℂ) Complex.I {i} 1)
    (algebraMap (SeedRing (57 : ℂ) Complex.I) (ConeRing i) (linkageA 57 Complex.I))
    (algebraMap (SeedRing (57 : ℂ) Complex.I) (ConeRing i) (linkageB 57 Complex.I))
    (algebraMap (SeedRing (57 : ℂ) Complex.I) (ConeRing i) (linkageC 57 Complex.I))
    (algebraMap (SeedRing (57 : ℂ) Complex.I) (ConeRing i) (linkageD 57 Complex.I))
  have hg (j : Fin 2) : g j = conePolynomial i (![originalF1 57, originalF2] j) := by
    fin_cases j
    · change conePolynomial i (X 0 ^ 2) -
        localScalar (57 : ℂ) Complex.I {i} 1 *
          conePolynomial i (C 57 * X 1 * X 3) =
        conePolynomial i (X 0 ^ 2 - C 57 * X 1 * X 3)
      rw [map_one, one_mul, map_sub]
    · change conePolynomial i (X 4) +
        (localScalar (57 : ℂ) Complex.I {i} 1) ^ 2 *
          conePolynomial i (X 2 ^ 2) = conePolynomial i (X 4 + X 2 ^ 2)
      rw [map_one, one_pow, one_mul, map_add]
  change (Ideal.span (Set.range g)).map (coneToChart i) = _
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  change coneToChart i (g j) = _
  rw [hg]
  exact coneToChart_polynomial i _

/-- The orbit component at 1 is the original canonical curve on the
actual surface chart. The parameter comparison is the fixed
`surfaceIdeal 57 1 = equationsIdeal (smoothH I) (smoothF 57 I)`. -/
theorem affineComponentIdeal_one_eq_original (i : Fin 3) :
    affineComponentIdeal i 1 = originalAffineCurveIdeal i := by
  rw [affineComponentIdeal_one_generators, originalAffineCurveIdeal_generators]

end LiteralCurve

def affineImageSheaf (i : Fin 3) : (Spec (CommRingCat.of (AffineRing i))).Modules :=
  tilde (ModuleCat.of (AffineRing i) (ImageModule i))

def affineOrbitDualSheaf (i : Fin 3) : (Spec (CommRingCat.of (AffineRing i))).Modules :=
  tilde (ModuleCat.of (AffineRing i) (OrbitDual i))

def affineImageDualIso (i : Fin 3) : affineImageSheaf i ≅ affineOrbitDualSheaf i :=
  (tilde.functor (CommRingCat.of (AffineRing i))).mapIso (imageDualEquiv i).toModuleIso

def projectiveImageSheaf (i : Fin 3) : (coordinatePatch 57 1 i.succ.castSucc).toScheme.Modules :=
  (Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).obj
    (affineImageSheaf i)

def projectiveOrbitDualSheaf (i : Fin 3) :
    (coordinatePatch 57 1 i.succ.castSucc).toScheme.Modules :=
  (Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).obj
    (affineOrbitDualSheaf i)

/-- An actual isomorphism of structure-module sheaves on each of the
three projective coordinate charts, induced from the original pairing. -/
def projectiveImageDualIso (i : Fin 3) :
    projectiveImageSheaf i ≅ projectiveOrbitDualSheaf i :=
  (Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).mapIso
    (affineImageDualIso i)

#print axioms chart_linkage_regular
#print axioms imageDualEquiv_selected
#print axioms chartDuality_original
#print axioms orbitIdeal_eq_component_product
#print axioms affineComponentIdeal_one_eq_original
#print axioms projectiveImageDualIso

end CycleQ2SeedProjectiveImageChart
end
