import Proposal.GeometricSeedNormalIdeals
import Proposal.GeometricAffineCurveCharts
import Proposal.GeometricChartKaehler
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Algebra

/-!
# Actual surface cotangent determinants and adjunction along the seed curve

The fourth affine variable is the actual curve equation f₂. Thus the change
from the weighted coordinate y is z = y + b² on the first projective chart
and z = y + 1 on the second. Both are polynomial coordinate changes.

The surface equations, their maps to the existing curve chart rings, and
the Jacobian localizations below are constructed from the literal equations.
The determinant modules are exterior powers of actual Kähler differentials.
Projective transition and gluing statements are separate from local frames.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricSurfaceAdjunction

open MvPolynomial Module
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricAffineCurveCharts
open scoped TensorProduct

/-- The distinguished variable `none` is z = f₂; `some j` is a curve-chart
coordinate. This is the polynomial ring in the actual four affine variables. -/
abbrev SurfacePoly := MvPolynomial (Option (Fin 3)) ℂ

def includeCurve : AffinePoly →ₐ[ℂ] SurfacePoly := rename Option.some

def setNormalZero : SurfacePoly →ₐ[ℂ] AffinePoly :=
  aeval (fun j => match j with | none => 0 | some i => X i)

@[simp] theorem setNormalZero_include (p : AffinePoly) :
    setNormalZero (includeCurve p) = p := by
  have h : setNormalZero.comp includeCurve = AlgHom.id ℂ AffinePoly := by
    ext i
    simp [setNormalZero, includeCurve]
  exact congrArg (fun f : AffinePoly →ₐ[ℂ] AffinePoly => f p) h

@[simp] theorem setNormalZero_X : setNormalZero (X none) = 0 := by
  simp [setNormalZero]

def firstSurfaceDehomogenize : WeightedPoly →ₐ[ℂ] SurfacePoly :=
  aeval ![X (some 0), 1, X (some 1), X (some 2), X none - X (some 1) ^ 2]

def secondSurfaceDehomogenize : WeightedPoly →ₐ[ℂ] SurfacePoly :=
  aeval ![X (some 0), X (some 1), 1, X (some 2), X none - 1]

theorem firstSurfaceDehomogenize_f1 (r : ℂ) :
    firstSurfaceDehomogenize (originalF1 r) = includeCurve (firstQuadric r) := by
  simp [firstSurfaceDehomogenize, originalF1, includeCurve, firstQuadric, quadricOne]

theorem secondSurfaceDehomogenize_f1 (r : ℂ) :
    secondSurfaceDehomogenize (originalF1 r) = includeCurve (secondQuadric r) := by
  simp [secondSurfaceDehomogenize, originalF1, includeCurve, secondQuadric, quadricTwo]

@[simp] theorem firstSurfaceDehomogenize_f2 :
    firstSurfaceDehomogenize originalF2 = X none := by
  simp [firstSurfaceDehomogenize, originalF2]

@[simp] theorem secondSurfaceDehomogenize_f2 :
    secondSurfaceDehomogenize originalF2 = X none := by
  simp [secondSurfaceDehomogenize, originalF2]

theorem firstSurfaceDehomogenize_h (θ : ℂ) :
    firstSurfaceDehomogenize (thetaH θ) = includeCurve (firstCubic θ) := by
  simp [firstSurfaceDehomogenize, thetaH, originalH, originalB,
    includeCurve, firstCubic, cubicOne]

theorem secondSurfaceDehomogenize_h (θ : ℂ) :
    secondSurfaceDehomogenize (thetaH θ) = includeCurve (secondCubic θ) := by
  simp [secondSurfaceDehomogenize, thetaH, originalH, originalB,
    includeCurve, secondCubic, cubicTwo]

/-- The actual factorized surface equation in the coordinates (a,b,c,z). -/
def surfaceEquation (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) : SurfacePoly :=
  includeCurve q * g₁ + X none * g₂ + includeCurve h * k

theorem firstSurfaceDehomogenize_equation (r θ : ℂ) :
    firstSurfaceDehomogenize (actualSeedEquation r θ) =
      surfaceEquation (firstQuadric r) (firstCubic θ)
        (firstSurfaceDehomogenize (originalG1 r))
        (firstSurfaceDehomogenize originalG2) (firstSurfaceDehomogenize (thetaK θ)) := by
  simp only [actualSeedEquation, map_add, map_mul, firstSurfaceDehomogenize_f1,
    firstSurfaceDehomogenize_f2, firstSurfaceDehomogenize_h, surfaceEquation]

theorem secondSurfaceDehomogenize_equation (r θ : ℂ) :
    secondSurfaceDehomogenize (actualSeedEquation r θ) =
      surfaceEquation (secondQuadric r) (secondCubic θ)
        (secondSurfaceDehomogenize (originalG1 r))
        (secondSurfaceDehomogenize originalG2) (secondSurfaceDehomogenize (thetaK θ)) := by
  simp only [actualSeedEquation, map_add, map_mul, secondSurfaceDehomogenize_f1,
    secondSurfaceDehomogenize_f2, secondSurfaceDehomogenize_h, surfaceEquation]

def surfaceChartIdeal (v : Fin 2 → SurfacePoly) : Ideal SurfacePoly :=
  Ideal.span (Set.range v)

abbrev SurfaceChartRing (v : Fin 2 → SurfacePoly) := SurfacePoly ⧸ surfaceChartIdeal v

def polynomialToCurve (q h : AffinePoly) : SurfacePoly →ₐ[ℂ] ChartRing ![q,h] :=
  (Ideal.Quotient.mkₐ ℂ (chartIdeal ![q,h])).comp setNormalZero

@[simp] theorem polynomialToCurve_include (q h p : AffinePoly) :
    polynomialToCurve q h (includeCurve p) = Ideal.Quotient.mk (chartIdeal ![q,h]) p := by
  simp [polynomialToCurve]

@[simp] theorem polynomialToCurve_normal (q h : AffinePoly) :
    polynomialToCurve q h (X none) = 0 := by
  simp [polynomialToCurve]

@[simp] theorem polynomialToCurve_quadric (q h : AffinePoly) :
    polynomialToCurve q h (includeCurve q) = 0 := by
  rw [polynomialToCurve_include]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨0, rfl⟩

@[simp] theorem polynomialToCurve_cubic (q h : AffinePoly) :
    polynomialToCurve q h (includeCurve h) = 0 := by
  rw [polynomialToCurve_include]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span ⟨1, rfl⟩

@[simp] theorem polynomialToCurve_surfaceEquation (q h : AffinePoly)
    (g₁ g₂ k : SurfacePoly) :
    polynomialToCurve q h (surfaceEquation q h g₁ g₂ k) = 0 := by
  simp only [surfaceEquation, map_add, map_mul, polynomialToCurve_quadric,
    polynomialToCurve_normal, polynomialToCurve_cubic, zero_mul, add_zero]

/-- This map is induced by setting the actual equation z=f₂ to zero and
imposing the existing quadric and cubic. No surface-to-curve map is assumed. -/
def surfaceToCurve (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) :
    SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h] →ₐ[ℂ]
      ChartRing ![q,h] :=
  Ideal.Quotient.liftₐ (surfaceChartIdeal ![surfaceEquation q h g₁ g₂ k, includeCurve h])
    (polynomialToCurve q h) (by
      change surfaceChartIdeal ![surfaceEquation q h g₁ g₂ k, includeCurve h] ≤
        RingHom.ker (polynomialToCurve q h).toRingHom
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact polynomialToCurve_surfaceEquation q h g₁ g₂ k
      · exact polynomialToCurve_cubic q h)

@[simp] theorem surfaceToCurve_polynomial (q h : AffinePoly) (g₁ g₂ k p : SurfacePoly) :
    surfaceToCurve q h g₁ g₂ k
      (Ideal.Quotient.mk (surfaceChartIdeal ![surfaceEquation q h g₁ g₂ k, includeCurve h]) p) =
        polynomialToCurve q h p := rfl

/-! ## The exact cotangent presentation of the actual surface quotient -/

/-- The quotient presentation before any Jacobian is inverted. -/
def presentation (v : Fin 2 → SurfacePoly) :
    Algebra.Presentation ℂ (SurfaceChartRing v) (Option (Fin 3)) (Fin 2) :=
  Algebra.Presentation.naive (v := v)

/-- The actual ambient cotangent space of this presentation. -/
abbrev AmbientDifferentials (v : Fin 2 → SurfacePoly) :=
  (presentation v).toExtension.CotangentSpace

/-- The ambient differential of a literal polynomial, restricted to the surface. -/
def ambientDifferential (v : Fin 2 → SurfacePoly) (p : SurfacePoly) :
    AmbientDifferentials v :=
  (1 : SurfaceChartRing v) ⊗ₜ[(presentation v).toExtension.Ring]
    KaehlerDifferential.D ℂ (presentation v).toExtension.Ring p

private theorem extension_toKaehler_polynomial {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    (P : Algebra.Extension R S) (p : P.Ring) :
    P.toKaehler ((1 : S) ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p) =
      KaehlerDifferential.D R S (algebraMap P.Ring S p) := by
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

@[simp] theorem ambientToKaehler_polynomial (v : Fin 2 → SurfacePoly) (p : SurfacePoly) :
    (presentation v).toExtension.toKaehler (ambientDifferential v p) =
      KaehlerDifferential.D ℂ (SurfaceChartRing v)
        (Ideal.Quotient.mk (surfaceChartIdeal v) p) :=
  extension_toKaehler_polynomial (presentation v).toExtension p

/-- The actual conormal class of a defining surface equation. -/
def surfaceRelationClass (v : Fin 2 → SurfacePoly) (j : Fin 2) :
    (presentation v).toExtension.Cotangent :=
  Algebra.Extension.Cotangent.mk
    ⟨(presentation v).relation j, (presentation v).relation_mem_ker j⟩

theorem surfaceRelationClass_span (v : Fin 2 → SurfacePoly) :
    Submodule.span (SurfaceChartRing v) (Set.range (surfaceRelationClass v)) = ⊤ :=
  Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker
    (P := (presentation v).toExtension)
    (presentation v).relation (presentation v).span_range_relation_eq_ker

@[simp] theorem surfaceRelationClass_differential (v : Fin 2 → SurfacePoly) (j : Fin 2) :
    (presentation v).toExtension.cotangentComplex (surfaceRelationClass v j) =
      ambientDifferential v (v j) := rfl

/-- The kernel is generated by the actual differentials of the actual equations. -/
theorem surfaceDifferential_kernel (v : Fin 2 → SurfacePoly) :
    LinearMap.ker (presentation v).toExtension.toKaehler =
      Submodule.span (SurfaceChartRing v) (Set.range (fun j => ambientDifferential v (v j))) := by
  rw [(presentation v).toExtension.exact_cotangentComplex_toKaehler.linearMap_ker_eq,
    ← Submodule.map_top, ← surfaceRelationClass_span v, Submodule.map_span,
    ← Set.range_comp]
  simp only [Function.comp_def, surfaceRelationClass_differential]

/-- The ambient-coordinate cokernel is identified with the genuine surface
Kähler module through the actual universal differential. -/
def surfaceCotangentQuotientEquiv (v : Fin 2 → SurfacePoly) :
    (AmbientDifferentials v ⧸ Submodule.span (SurfaceChartRing v)
      (Set.range (fun j => ambientDifferential v (v j)))) ≃ₗ[SurfaceChartRing v]
        KaehlerDifferential ℂ (SurfaceChartRing v) :=
  (Submodule.quotEquivOfEq _ _ (surfaceDifferential_kernel v).symm).trans
    ((presentation v).toExtension.toKaehler.quotKerEquivOfSurjective
      (presentation v).toExtension.toKaehler_surjective)

@[simp] theorem surfaceCotangentQuotientEquiv_polynomial
    (v : Fin 2 → SurfacePoly) (p : SurfacePoly) :
    surfaceCotangentQuotientEquiv v (Submodule.Quotient.mk (ambientDifferential v p)) =
      KaehlerDifferential.D ℂ (SurfaceChartRing v)
        (Ideal.Quotient.mk (surfaceChartIdeal v) p) := by
  simp only [surfaceCotangentQuotientEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk,
    ambientToKaehler_polynomial]

/-! ## Determinants of genuine rank-two modules -/

section Determinant

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private def topIndex : Set.powersetCard (Fin 2) 2 := ⟨Finset.univ, by simp⟩

private theorem topIndex_unique (s : Set.powersetCard (Fin 2) 2) : s = topIndex := by
  apply Subtype.ext
  exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp [s.property])

private instance : Subsingleton (Set.powersetCard (Fin 2) 2) :=
  ⟨fun s t => (topIndex_unique s).trans (topIndex_unique t).symm⟩

/-- The determinant coordinate of an ordered basis of an actual rank-two module. -/
def determinantEquiv (b : Basis (Fin 2) R M) : (⋀[R]^2 M) ≃ₗ[R] R :=
  (b.exteriorPower 2).repr.trans (Finsupp.uniqueLinearEquiv R R topIndex)

theorem topBasis_wedge (b : Basis (Fin 2) R M) :
    b.exteriorPower 2 topIndex = exteriorPower.ιMulti R 2 b := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  have ho : (fun i : Fin 2 => i) =
      (Finset.univ : Finset (Fin 2)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique _ (fun _ => Finset.mem_univ _) strictMono_id
  exact congrArg b (congrFun ho j).symm

@[simp] theorem determinantEquiv_wedge (b : Basis (Fin 2) R M) :
    determinantEquiv b (exteriorPower.ιMulti R 2 b) = 1 := by
  rw [← topBasis_wedge]
  simp [determinantEquiv]

theorem determinantEquiv_symm_one (b : Basis (Fin 2) R M) :
    (determinantEquiv b).symm 1 = exteriorPower.ιMulti R 2 b := by
  apply (determinantEquiv b).injective
  rw [LinearEquiv.apply_symm_apply, determinantEquiv_wedge]

end Determinant

/-! ## A quotient basis obtained from the exact kernel -/

section QuotientBasis

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
variable (b : Basis (Fin 2 ⊕ Fin 2) R M)

private def relationInclusion : (Fin 2 → R) →ₗ[R] M :=
  (Pi.basisFun R (Fin 2)).constr R (fun j => b (Sum.inl j))

private def relationRetraction : M →ₗ[R] (Fin 2 → R) :=
  LinearMap.pi (fun j => b.coord (Sum.inl j))

private theorem relationRetraction_inclusion :
    (relationRetraction b).comp (relationInclusion b) = LinearMap.id := by
  apply (Pi.basisFun R (Fin 2)).ext
  intro j
  ext k
  simp [relationRetraction, relationInclusion, Basis.coord_apply,
    Pi.basisFun_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]

/-- When the first two vectors of an actual basis are the exact kernel,
the last two vectors give a constructed basis of the quotient target. -/
def quotientBasis (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (hker : LinearMap.ker g = Submodule.span R (Set.range (fun j => b (Sum.inl j)))) :
    Basis (Fin 2) R N := by
  have hexact : Function.Exact (relationInclusion b) g := by
    rw [LinearMap.exact_iff, hker, relationInclusion, Basis.constr_range]
  apply b.ofSplitExact (relationRetraction_inclusion b) hexact hg
    (a := Sum.inr) (b := Sum.inl) Sum.inr_injective
  · intro j
    ext k
    simp [relationRetraction, Basis.coord_apply]
  · have hh : relationRetraction b ∘ b ∘ Sum.inl = Pi.basisFun R (Fin 2) := by
      ext j k
      simp [relationRetraction, Basis.coord_apply, Pi.basisFun_apply,
        Pi.single_apply, Finsupp.single_apply, eq_comm]
    rw [hh]
    exact (Pi.basisFun R (Fin 2)).linearIndependent
  · exact Set.isCompl_range_inl_range_inr.symm.codisjoint

@[simp] theorem quotientBasis_apply (g : M →ₗ[R] N) (hg : Function.Surjective g)
    (hker : LinearMap.ker g = Submodule.span R (Set.range (fun j => b (Sum.inl j))))
    (j : Fin 2) : quotientBasis b g hg hker j = g (b (Sum.inr j)) := by
  simp [quotientBasis]

end QuotientBasis

/-! ## Actual augmented-Jacobian surface patches -/

abbrev AmbientIndex := Fin 2 ⊕ Fin 2

/-- This ordering of the ambient coordinates is (z,a,b,c). -/
def ambientIndexEquiv : AmbientIndex ≃ Option (Fin 3) :=
  (finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).trans (finSuccEquiv 3)

def ambientBasis (v : Fin 2 → SurfacePoly) :
    Basis AmbientIndex (SurfaceChartRing v) (AmbientDifferentials v) :=
  (presentation v).cotangentSpaceBasis.reindex ambientIndexEquiv.symm

/-- The two defining differentials followed by the actual conormal
polynomial and the chosen free coordinate differential. -/
def augmentedFamily (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    AmbientIndex → AmbientDifferentials v :=
  Sum.elim (fun j => ambientDifferential v (v j))
    (fun j => ambientDifferential v (![n,t] j))

def augmentedJacobian (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) : SurfaceChartRing v :=
  ((ambientBasis v).toMatrix (augmentedFamily v n t)).det

/-- The inverted element is the literal determinant of the four specified
actual differentials. This construction treats f₂ and f₁ symmetrically. -/
abbrev AdjunctionPatch (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :=
  Localization.Away (augmentedJacobian v n t)

abbrev LocalAmbientDifferentials (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :=
  AdjunctionPatch v n t ⊗[SurfaceChartRing v] AmbientDifferentials v

def localAmbientBasis (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    Basis AmbientIndex (AdjunctionPatch v n t) (LocalAmbientDifferentials v n t) :=
  (ambientBasis v).baseChange (AdjunctionPatch v n t)

def localAugmentedFamily (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    AmbientIndex → LocalAmbientDifferentials v n t :=
  fun j => (1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v] augmentedFamily v n t j

theorem localAugmentedMatrix (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    (localAmbientBasis v n t).toMatrix (localAugmentedFamily v n t) =
      ((ambientBasis v).toMatrix (augmentedFamily v n t)).map
        (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)) := by
  ext i j
  simp [Basis.toMatrix, localAmbientBasis, localAugmentedFamily,
    Basis.baseChange_repr_tmul, Algebra.smul_def]

theorem localAugmentedDet_isUnit (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    IsUnit ((localAmbientBasis v n t).toMatrix (localAugmentedFamily v n t)).det := by
  rw [localAugmentedMatrix]
  change IsUnit ((algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)).mapMatrix
    ((ambientBasis v).toMatrix (augmentedFamily v n t))).det
  rw [← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (augmentedJacobian v n t)

/-- The unit determinant constructs the actual ambient cotangent basis;
no linear independence or rank comparison is supplied as an input. -/
def augmentedBasis (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    Basis AmbientIndex (AdjunctionPatch v n t) (LocalAmbientDifferentials v n t) :=
  (localAmbientBasis v n t).map
    (Matrix.toLinearEquiv (localAmbientBasis v n t)
      ((localAmbientBasis v n t).toMatrix (localAugmentedFamily v n t))
      (localAugmentedDet_isUnit v n t))

@[simp] theorem augmentedBasis_apply (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
    (j : AmbientIndex) : augmentedBasis v n t j = localAugmentedFamily v n t j := by
  rw [augmentedBasis, Basis.map_apply, Matrix.toLinearEquiv_apply,
    Basis.toMatrix_eq_toMatrix_constr, Matrix.toLin_toMatrix, Basis.constr_basis]

/-- The actual localized ambient-to-surface cotangent map. -/
def localToKaehler (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    LocalAmbientDifferentials v n t →ₗ[AdjunctionPatch v n t]
      KaehlerDifferential ℂ (AdjunctionPatch v n t) :=
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      ℂ (SurfaceChartRing v) (AdjunctionPatch v n t)).toLinearMap.comp
    ((presentation v).toExtension.toKaehler.baseChange (AdjunctionPatch v n t))

theorem localToKaehler_surjective (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    Function.Surjective (localToKaehler v n t) :=
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      ℂ (SurfaceChartRing v) (AdjunctionPatch v n t)).surjective.comp
    (LinearMap.baseChange_surjective (AdjunctionPatch v n t)
      (presentation v).toExtension.toKaehler_surjective)

theorem localRelationClass_span (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    Submodule.span (AdjunctionPatch v n t)
      (Set.range (fun j => (1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v]
        surfaceRelationClass v j)) = ⊤ := by
  rw [Set.range_comp']
  change Submodule.span (AdjunctionPatch v n t)
    ((TensorProduct.mk (SurfaceChartRing v) (AdjunctionPatch v n t)
      (presentation v).toExtension.Cotangent 1) '' Set.range (surfaceRelationClass v)) = ⊤
  rw [← Submodule.baseChange_span,
    surfaceRelationClass_span, Submodule.baseChange_top]

theorem localToKaehler_kernel (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    LinearMap.ker (localToKaehler v n t) =
      Submodule.span (AdjunctionPatch v n t)
        (Set.range (fun j => augmentedBasis v n t (Sum.inl j))) := by
  let f := (presentation v).toExtension.cotangentComplex.baseChange (AdjunctionPatch v n t)
  let g := (presentation v).toExtension.toKaehler.baseChange (AdjunctionPatch v n t)
  have hexact : Function.Exact f g :=
    lTensor_exact (AdjunctionPatch v n t)
      (presentation v).toExtension.exact_cotangentComplex_toKaehler
      (presentation v).toExtension.toKaehler_surjective
  have hker : LinearMap.ker (localToKaehler v n t) = LinearMap.range f := by
    ext x
    change (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      ℂ (SurfaceChartRing v) (AdjunctionPatch v n t)) (g x) = 0 ↔ _
    rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
      ℂ (SurfaceChartRing v) (AdjunctionPatch v n t)).map_zero,
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
        ℂ (SurfaceChartRing v) (AdjunctionPatch v n t)).injective.eq_iff]
    exact hexact x
  rw [hker, ← Submodule.map_top, ← localRelationClass_span v n t,
    Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, f, LinearMap.baseChange_tmul,
    surfaceRelationClass_differential, augmentedBasis_apply, localAugmentedFamily,
    augmentedFamily, Sum.elim_inl]

theorem localAugmentedFamily_linearIndependent (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    LinearIndependent (AdjunctionPatch v n t) (localAugmentedFamily v n t) := by
  have hb : (augmentedBasis v n t : AmbientIndex → LocalAmbientDifferentials v n t) =
      localAugmentedFamily v n t := funext (augmentedBasis_apply v n t)
  rw [← hb]
  exact (augmentedBasis v n t).linearIndependent

theorem localAugmentedFamily_span (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    Submodule.span (AdjunctionPatch v n t) (Set.range (localAugmentedFamily v n t)) = ⊤ := by
  have hb : (augmentedBasis v n t : AmbientIndex → LocalAmbientDifferentials v n t) =
      localAugmentedFamily v n t := funext (augmentedBasis_apply v n t)
  rw [← hb]
  exact (augmentedBasis v n t).span_eq

/-- The identical actual basis vectors, with an abstract coordinate
equivalence constructed from their proved independence and spanning. -/
def compactAugmentedBasis (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    Basis AmbientIndex (AdjunctionPatch v n t) (LocalAmbientDifferentials v n t) :=
  Basis.mk (localAugmentedFamily_linearIndependent v n t) (localAugmentedFamily_span v n t).ge

@[simp] theorem compactAugmentedBasis_apply (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
    (j : AmbientIndex) : compactAugmentedBasis v n t j = localAugmentedFamily v n t j :=
  Basis.mk_apply _ _ _

theorem localToKaehler_kernel_compact (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    LinearMap.ker (localToKaehler v n t) =
      Submodule.span (AdjunctionPatch v n t)
        (Set.range (fun j => compactAugmentedBasis v n t (Sum.inl j))) := by
  simpa only [compactAugmentedBasis_apply, augmentedBasis_apply] using
    localToKaehler_kernel v n t

/-- The actual surface Kähler basis on the actual augmented-Jacobian
localization consists of Dn and Dt, including when n=f₁ is not a polynomial
coordinate. The cotangent exact sequence proves this construction. -/
def localSurfaceKaehlerBasis (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    Basis (Fin 2) (AdjunctionPatch v n t) (KaehlerDifferential ℂ (AdjunctionPatch v n t)) :=
  quotientBasis (compactAugmentedBasis v n t) (localToKaehler v n t)
    (localToKaehler_surjective v n t) (localToKaehler_kernel_compact v n t)


@[simp] theorem localToKaehler_polynomial (v : Fin 2 → SurfacePoly)
    (n t p : SurfacePoly) :
    localToKaehler v n t ((1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v]
        ambientDifferential v p) =
      KaehlerDifferential.D ℂ (AdjunctionPatch v n t)
        (algebraMap SurfacePoly (AdjunctionPatch v n t) p) := by
  simp only [localToKaehler, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul, ambientToKaehler_polynomial,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

@[simp] theorem localSurfaceKaehlerBasis_apply (v : Fin 2 → SurfacePoly)
    (n t : SurfacePoly) (j : Fin 2) :
    localSurfaceKaehlerBasis v n t j =
      KaehlerDifferential.D ℂ (AdjunctionPatch v n t)
        (algebraMap SurfacePoly (AdjunctionPatch v n t) (![n,t] j)) := by
  rw [localSurfaceKaehlerBasis, quotientBasis_apply, compactAugmentedBasis_apply]
  exact localToKaehler_polynomial v n t _

/-- This is the determinant of the actual surface Kähler module, with
the normalization fixed by the actual four-column differential determinant. -/
def localSurfaceDeterminantEquiv (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    (⋀[AdjunctionPatch v n t]^2 (KaehlerDifferential ℂ (AdjunctionPatch v n t))) ≃ₗ[
      AdjunctionPatch v n t] AdjunctionPatch v n t :=
  (determinantEquiv (localSurfaceKaehlerBasis v n t)).trans
    (LinearEquiv.smulOfUnit
      (IsLocalization.Away.algebraMap_isUnit (S := AdjunctionPatch v n t)
        (augmentedJacobian v n t)).unit)

def localSurfaceResidueForm (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    ⋀[AdjunctionPatch v n t]^2 (KaehlerDifferential ℂ (AdjunctionPatch v n t)) :=
  (localSurfaceDeterminantEquiv v n t).symm 1

@[simp] theorem localSurfaceResidueForm_normalization (v : Fin 2 → SurfacePoly)
    (n t : SurfacePoly) :
    localSurfaceDeterminantEquiv v n t (localSurfaceResidueForm v n t) = 1 :=
  (localSurfaceDeterminantEquiv v n t).apply_symm_apply 1


/-! ## Restriction of the actual augmented determinant to the curve -/

open CycleQ2GeometricSparseJacobianCover CycleQ2GeometricResidueFrames
  CycleQ2GeometricAffineOverlap

@[simp] theorem pderiv_include_some (p : AffinePoly) (j : Fin 3) :
    pderiv (some j) (includeCurve p) = includeCurve (pderiv j p) :=
  MvPolynomial.pderiv_rename (Option.some_injective (Fin 3)) j p

@[simp] theorem pderiv_include_none (p : AffinePoly) :
    pderiv none (includeCurve p) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨j, _, hj⟩ := MvPolynomial.mem_vars_rename Option.some p h
  cases hj

theorem surface_aeval_presentation (v : Fin 2 → SurfacePoly) :
    aeval (presentation v).val = Ideal.Quotient.mkₐ ℂ (surfaceChartIdeal v) := by
  ext i
  simp only [aeval_X]
  rfl

theorem ambientBasis_repr_differential (v : Fin 2 → SurfacePoly)
    (p : SurfacePoly) (j : AmbientIndex) :
    (ambientBasis v).repr (ambientDifferential v p) j =
      Ideal.Quotient.mk (surfaceChartIdeal v) (pderiv (ambientIndexEquiv j) p) := by
  rw [ambientBasis, Basis.repr_reindex_apply]
  have hh := (presentation v).toGenerators.cotangentSpaceBasis_repr_one_tmul p
    (ambientIndexEquiv j)
  rw [surface_aeval_presentation] at hh
  exact hh

def augmentedPolynomialRows (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    Fin 4 → SurfacePoly := ![v 0, v 1, n, t]

private theorem augmentedFamily_reindex (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
    (i : Fin 4) :
    augmentedFamily v n t ((finSumFinEquiv : AmbientIndex ≃ Fin 4).symm i) =
      ambientDifferential v (augmentedPolynomialRows v n t i) := by
  fin_cases i <;> rfl

private theorem surfaceCoordinateIndex (i : Fin 4) :
    _root_.finSuccEquiv 3 i = (![none, some 0, some 1, some 2] : Fin 4 → Option (Fin 3)) i := by
  fin_cases i <;> rfl

theorem augmentedJacobian_polynomial (v : Fin 2 → SurfacePoly) (n t : SurfacePoly) :
    augmentedJacobian v n t =
      Matrix.det (fun i j : Fin 4 => Ideal.Quotient.mk (surfaceChartIdeal v)
        (pderiv ((_root_.finSuccEquiv 3) j) (augmentedPolynomialRows v n t i))) := by
  rw [augmentedJacobian, ← Matrix.det_reindex_self
    (finSumFinEquiv : AmbientIndex ≃ Fin 4), ← Matrix.det_transpose]
  congr 1
  ext i j
  simp only [Matrix.transpose_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    Basis.toMatrix_apply]
  rw [augmentedFamily_reindex, ambientBasis_repr_differential]
  simp only [ambientIndexEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]

theorem augmentedJacobian_restriction (q h : AffinePoly) (g₁ g₂ k n t : SurfacePoly) :
    surfaceToCurve q h g₁ g₂ k
      (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h] n t) =
      Matrix.det (fun i j : Fin 4 => polynomialToCurve q h
        (pderiv ((_root_.finSuccEquiv 3) j)
          (augmentedPolynomialRows ![surfaceEquation q h g₁ g₂ k, includeCurve h]
            n t i))) := by
  rw [augmentedJacobian_polynomial, AlgHom.map_det]
  rfl

section FourByFour

variable {R : Type*} [CommRing R]

private theorem succAbove_four (i : Fin 4) (j : Fin 3) :
    i.succAbove j = (!![(1 : Fin 4), 2, 3; 0, 2, 3; 0, 1, 3; 0, 1, 2] i j) := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem det_normal_coordinate (u v : Fin 3 → R) (a b c : R) (j : Fin 3) :
    Matrix.det !![
      b, a * u 0 + c * v 0, a * u 1 + c * v 1, a * u 2 + c * v 2;
      0, v 0, v 1, v 2;
      1, 0, 0, 0;
      0, (if j = 0 then 1 else 0), (if j = 1 then 1 else 0),
        (if j = 2 then 1 else 0)] = a * jacobianMinors u v j := by
  fin_cases j <;>
    simp [Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
      Matrix.submatrix_apply, Fin.sum_univ_succ, succAbove_four,
      jacobianMinors] <;> ring

private theorem det_normal_quadric (u v : Fin 3 → R) (a b c : R) (j : Fin 3) :
    Matrix.det !![
      b, a * u 0 + c * v 0, a * u 1 + c * v 1, a * u 2 + c * v 2;
      0, v 0, v 1, v 2;
      0, u 0, u 1, u 2;
      0, (if j = 0 then 1 else 0), (if j = 1 then 1 else 0),
        (if j = 2 then 1 else 0)] = -b * jacobianMinors u v j := by
  fin_cases j <;>
    simp [Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
      Matrix.submatrix_apply, Fin.sum_univ_succ, succAbove_four,
      jacobianMinors] <;> ring

end FourByFour

@[simp] theorem curveChart_quadric_zero (q h : AffinePoly) :
    Ideal.Quotient.mk (chartIdeal ![q,h]) q = 0 := by
  simpa only [polynomialToCurve_include] using polynomialToCurve_quadric q h

@[simp] theorem curveChart_cubic_zero (q h : AffinePoly) :
    Ideal.Quotient.mk (chartIdeal ![q,h]) h = 0 := by
  simpa only [polynomialToCurve_include] using polynomialToCurve_cubic q h

@[simp] theorem polynomialToCurve_surfaceDerivative_none (q h : AffinePoly)
    (g₁ g₂ k : SurfacePoly) :
    polynomialToCurve q h (pderiv none (surfaceEquation q h g₁ g₂ k)) =
      polynomialToCurve q h g₂ := by
  simp [surfaceEquation, Derivation.leibniz, smul_eq_mul]

@[simp] theorem polynomialToCurve_surfaceDerivative_some (q h : AffinePoly)
    (g₁ g₂ k : SurfacePoly) (j : Fin 3) :
    polynomialToCurve q h (pderiv (some j) (surfaceEquation q h g₁ g₂ k)) =
      polynomialToCurve q h g₁ * chartMap ![q,h] (pderiv j q) +
        polynomialToCurve q h k * chartMap ![q,h] (pderiv j h) := by
  simp [surfaceEquation, Derivation.leibniz, smul_eq_mul, chartMap, mul_comm]

/-- On the f₂ chart, the actual surface determinant restricts to +g₁J.
Here J is the existing signed curve minor in the fixed (a,b,c) order. -/
theorem augmentedJacobian_normal_restriction (q h : AffinePoly)
    (g₁ g₂ k : SurfacePoly) (j : Fin 3) :
    surfaceToCurve q h g₁ g₂ k
      (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (X none) (includeCurve (X j))) =
      polynomialToCurve q h g₁ * chartMinor ![q,h] j := by
  rw [augmentedJacobian_restriction]
  have hm : (fun i l : Fin 4 => polynomialToCurve q h
      (pderiv ((_root_.finSuccEquiv 3) l)
        (augmentedPolynomialRows ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (X none) (includeCurve (X j)) i))) =
      !![polynomialToCurve q h g₂,
        polynomialToCurve q h g₁ * chartMap ![q,h] (pderiv 0 q) +
          polynomialToCurve q h k * chartMap ![q,h] (pderiv 0 h),
        polynomialToCurve q h g₁ * chartMap ![q,h] (pderiv 1 q) +
          polynomialToCurve q h k * chartMap ![q,h] (pderiv 1 h),
        polynomialToCurve q h g₁ * chartMap ![q,h] (pderiv 2 q) +
          polynomialToCurve q h k * chartMap ![q,h] (pderiv 2 h);
        0, chartMap ![q,h] (pderiv 0 h), chartMap ![q,h] (pderiv 1 h),
          chartMap ![q,h] (pderiv 2 h);
        1, 0, 0, 0;
        0, (if j = 0 then 1 else 0), (if j = 1 then 1 else 0),
          (if j = 2 then 1 else 0)] := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [augmentedPolynomialRows, surfaceCoordinateIndex, chartMap, Pi.single_apply]
  rw [hm, det_normal_coordinate
    (fun l => chartMap ![q,h] (pderiv l q)) (fun l => chartMap ![q,h] (pderiv l h))
    (polynomialToCurve q h g₁) (polynomialToCurve q h g₂) (polynomialToCurve q h k) j]
  congr 1
  fin_cases j <;>
    simp [chartMinor, minorPolynomial, jacobianMinors, chartMap, map_sub, map_mul]


/-- On the f₁ chart, the actual surface determinant restricts to −g₂J.
Here J is the existing signed curve minor in the fixed (a,b,c) order. -/
theorem augmentedJacobian_quadric_restriction (q h : AffinePoly)
    (g₁ g₂ k : SurfacePoly) (j : Fin 3) :
    surfaceToCurve q h g₁ g₂ k
      (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (includeCurve q) (includeCurve (X j))) =
      -polynomialToCurve q h g₂ * chartMinor ![q,h] j := by
  rw [augmentedJacobian_restriction]
  have hm : (fun i l : Fin 4 => polynomialToCurve q h
      (pderiv ((_root_.finSuccEquiv 3) l)
        (augmentedPolynomialRows ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (includeCurve q) (includeCurve (X j)) i))) =
      !![polynomialToCurve q h g₂,
        polynomialToCurve q h g₁ * chartMap ![q,h] (pderiv 0 q) +
          polynomialToCurve q h k * chartMap ![q,h] (pderiv 0 h),
        polynomialToCurve q h g₁ * chartMap ![q,h] (pderiv 1 q) +
          polynomialToCurve q h k * chartMap ![q,h] (pderiv 1 h),
        polynomialToCurve q h g₁ * chartMap ![q,h] (pderiv 2 q) +
          polynomialToCurve q h k * chartMap ![q,h] (pderiv 2 h);
        0, chartMap ![q,h] (pderiv 0 h), chartMap ![q,h] (pderiv 1 h),
          chartMap ![q,h] (pderiv 2 h);
        0, chartMap ![q,h] (pderiv 0 q), chartMap ![q,h] (pderiv 1 q),
          chartMap ![q,h] (pderiv 2 q);
        0, (if j = 0 then 1 else 0), (if j = 1 then 1 else 0),
          (if j = 2 then 1 else 0)] := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [augmentedPolynomialRows, surfaceCoordinateIndex, chartMap, Pi.single_apply]
  rw [hm, det_normal_quadric
    (fun l => chartMap ![q,h] (pderiv l q)) (fun l => chartMap ![q,h] (pderiv l h))
    (polynomialToCurve q h g₁) (polynomialToCurve q h g₂) (polynomialToCurve q h k) j]
  congr 1
  fin_cases j <;>
    simp [chartMinor, minorPolynomial, jacobianMinors, chartMap, map_sub, map_mul]


/-! ## The actual closed immersion and its kernel -/

def surfaceMap (v : Fin 2 → SurfacePoly) : SurfacePoly →ₐ[ℂ] SurfaceChartRing v :=
  Ideal.Quotient.mkₐ ℂ (surfaceChartIdeal v)

@[simp] theorem surfaceMap_relation (v : Fin 2 → SurfacePoly) (j : Fin 2) :
    surfaceMap v (v j) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)

/-- Polynomial division by the distinguished variable is the literal
evaluation z=0, with no smoothness or geometric hypothesis. -/
theorem normalDifference_mem (p : SurfacePoly) :
    p - includeCurve (setNormalZero p) ∈ Ideal.span ({X none} : Set SurfacePoly) := by
  let I : Ideal SurfacePoly := Ideal.span {X none}
  let f := Ideal.Quotient.mkₐ ℂ I
  have he : f.comp (includeCurve.comp setNormalZero) = f := by
    ext i
    cases i with
    | none =>
      simp only [AlgHom.comp_apply, setNormalZero_X, map_zero]
      exact (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))).symm
    | some i => simp [includeCurve, setNormalZero]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f (p - includeCurve (setNormalZero p)) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (congrArg (fun g : SurfacePoly →ₐ[ℂ] SurfacePoly ⧸ I => g p) he).symm

private theorem chartIdeal_pair (q h : AffinePoly) : chartIdeal ![q,h] = Ideal.span {q,h} := by
  unfold chartIdeal
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (hx | hx)
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩

theorem surfaceToCurve_surjective (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) :
    Function.Surjective (surfaceToCurve q h g₁ g₂ k) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨surfaceMap ![surfaceEquation q h g₁ g₂ k, includeCurve h] (includeCurve p),
    polynomialToCurve_include q h p⟩

/-- The actual kernel of the actual closed-immersion map is generated by
the two curve equations q=f₁ and z=f₂ on the surface. -/
theorem surfaceToCurve_kernel (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) :
    RingHom.ker (surfaceToCurve q h g₁ g₂ k).toRingHom =
      Ideal.span {surfaceMap ![surfaceEquation q h g₁ g₂ k, includeCurve h] (includeCurve q),
        surfaceMap ![surfaceEquation q h g₁ g₂ k, includeCurve h] (X none)} := by
  let v := ![surfaceEquation q h g₁ g₂ k, includeCurve h]
  apply le_antisymm
  · intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change polynomialToCurve q h p = 0 at hx
    have hp : setNormalZero p ∈ Ideal.span ({q,h} : Set AffinePoly) := by
      rw [← chartIdeal_pair]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hp
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (normalDifference_mem p)
    have heval : includeCurve (setNormalZero p) =
        includeCurve a * includeCurve q + includeCurve b * includeCurve h := by
      rw [← hab, map_add, map_mul, map_mul]
    have hdecomp : p = includeCurve a * includeCurve q + c * X none +
        includeCurve b * includeCurve h := by
      calc
        p = (p - includeCurve (setNormalZero p)) + includeCurve (setNormalZero p) :=
          (sub_add_cancel _ _).symm
        _ = c * X none + (includeCurve a * includeCurve q + includeCurve b * includeCurve h) := by
          rw [← hc, heval]
        _ = _ := by ring
    apply Ideal.mem_span_pair.mpr
    refine ⟨surfaceMap v (includeCurve a), surfaceMap v c, ?_⟩
    have hz : surfaceMap v (includeCurve h) = 0 := surfaceMap_relation v 1
    change surfaceMap v (includeCurve a) * surfaceMap v (includeCurve q) +
      surfaceMap v c * surfaceMap v (X none) = surfaceMap v p
    rw [hdecomp, map_add, map_add, map_mul, map_mul, map_mul, hz, mul_zero, add_zero]
  · apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · exact polynomialToCurve_quadric q h
    · exact polynomialToCurve_normal q h

/-- The induced curve patch in exactly the image of the surface determinant. -/
abbrev CurveAdjunctionPatch (q h : AffinePoly) (g₁ g₂ k n t : SurfacePoly) :=
  Localization.Away (surfaceToCurve q h g₁ g₂ k
    (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h] n t))

/-- The actual localized closed-immersion map, induced by the previously
constructed quotient map and the literal augmented determinant. -/
def adjunctionToCurve (q h : AffinePoly) (g₁ g₂ k n t : SurfacePoly) :
    AdjunctionPatch ![surfaceEquation q h g₁ g₂ k, includeCurve h] n t →ₐ[ℂ]
      CurveAdjunctionPatch q h g₁ g₂ k n t :=
  IsLocalization.Away.mapₐ _ _ (surfaceToCurve q h g₁ g₂ k)
    (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h] n t)

@[simp] theorem adjunctionToCurve_base (q h : AffinePoly) (g₁ g₂ k n t : SurfacePoly)
    (a : SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h]) :
    adjunctionToCurve q h g₁ g₂ k n t
      (algebraMap _ (AdjunctionPatch ![surfaceEquation q h g₁ g₂ k, includeCurve h] n t) a) =
      algebraMap (ChartRing ![q,h]) (CurveAdjunctionPatch q h g₁ g₂ k n t)
        (surfaceToCurve q h g₁ g₂ k a) := by
  simp only [adjunctionToCurve, IsLocalization.Away.mapₐ_apply,
    IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

theorem adjunctionToCurve_surjective (q h : AffinePoly) (g₁ g₂ k n t : SurfacePoly) :
    Function.Surjective (adjunctionToCurve q h g₁ g₂ k n t) := by
  change Function.Surjective (IsLocalization.Away.map _ _
    (surfaceToCurve q h g₁ g₂ k).toRingHom _)
  apply (IsLocalization.Away.map_surjective_iff _ _ _ _).mpr
  intro a
  obtain ⟨b, hb⟩ := surfaceToCurve_surjective q h g₁ g₂ k a
  refine ⟨b, 0, ?_⟩
  rw [pow_zero, one_mul]
  change surfaceToCurve q h g₁ g₂ k b = a
  exact hb

/-- Localizing the actual closed immersion preserves its literal
two-generator kernel; this identifies the ideal used in the conormal module. -/
theorem adjunctionToCurve_kernel (q h : AffinePoly) (g₁ g₂ k n t : SurfacePoly) :
    RingHom.ker (adjunctionToCurve q h g₁ g₂ k n t).toRingHom =
      Ideal.span {
        algebraMap SurfacePoly
          (AdjunctionPatch ![surfaceEquation q h g₁ g₂ k, includeCurve h] n t) (includeCurve q),
        algebraMap SurfacePoly
          (AdjunctionPatch ![surfaceEquation q h g₁ g₂ k, includeCurve h] n t) (X none)} := by
  let v := ![surfaceEquation q h g₁ g₂ k, includeCurve h]
  let d := augmentedJacobian v n t
  have hk := IsLocalization.ker_map
    (M := Submonoid.powers d) (S := AdjunctionPatch v n t)
    (T := Submonoid.powers (surfaceToCurve q h g₁ g₂ k d))
    (CurveAdjunctionPatch q h g₁ g₂ k n t)
    (surfaceToCurve q h g₁ g₂ k).toRingHom (Submonoid.map_powers _ _)
  change RingHom.ker (adjunctionToCurve q h g₁ g₂ k n t).toRingHom =
    (RingHom.ker (surfaceToCurve q h g₁ g₂ k).toRingHom).map
      (algebraMap (SurfaceChartRing v) (AdjunctionPatch v n t)) at hk
  rw [hk, surfaceToCurve_kernel, Ideal.map_span]
  simp only [Set.image_pair]
  rfl



/-! ## Generation of the actual base-changed conormal module -/

section ConormalGeneration

variable {S R : Type*} [CommRing S] [CommRing R] [Algebra S R]

def tensorCotangentClass (I : Ideal S) (x : S) (hx : x ∈ I) : R ⊗[S] I.Cotangent :=
  (1 : R) ⊗ₜ[S] I.toCotangent ⟨x, hx⟩

theorem tensorCotangent_generators_span {ι : Type*} (I : Ideal S) (s : ι → S)
    (hs : ∀ i, s i ∈ I) (hspan : Submodule.span S (Set.range s) = I) :
    Submodule.span R (Set.range (fun i => tensorCotangentClass (R := R) I (s i) (hs i))) = ⊤ := by
  have hgen : Submodule.span S (Set.range (fun i => (⟨s i, hs i⟩ : I))) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff I hs).mpr hspan
  have hcot : Submodule.span S
      (Set.range (fun i => I.toCotangent ⟨s i, hs i⟩)) = ⊤ := by
    rw [Set.range_comp', ← Submodule.map_span, hgen, Submodule.map_top,
      Ideal.toCotangent_range]
  change Submodule.span R
    (Set.range (fun i => (1 : R) ⊗ₜ[S] I.toCotangent ⟨s i, hs i⟩)) = ⊤
  rw [Set.range_comp']
  change Submodule.span R ((TensorProduct.mk S R I.Cotangent 1) ''
    Set.range (fun i => I.toCotangent ⟨s i, hs i⟩)) = ⊤
  rw [← Submodule.baseChange_span, hcot, Submodule.baseChange_top]

theorem tensorCotangent_pair_relation (I : Ideal S) (x y u v : S)
    (hx : x ∈ I) (hy : y ∈ I) (hrel : u * x + v * y = 0) :
    algebraMap S R u • tensorCotangentClass (R := R) I x hx +
      algebraMap S R v • tensorCotangentClass (R := R) I y hy = 0 := by
  have hc : u • I.toCotangent ⟨x, hx⟩ + v • I.toCotangent ⟨y, hy⟩ = 0 := by
    rw [← map_smul, ← map_smul, ← map_add]
    have he : u • (⟨x, hx⟩ : I) + v • (⟨y, hy⟩ : I) = 0 :=
      Subtype.ext hrel
    rw [he, map_zero]
  have ht := congrArg (TensorProduct.mk S R I.Cotangent 1) hc
  simpa only [map_add, map_smul, map_zero, tensorCotangentClass,
    TensorProduct.mk_apply, algebraMap_smul] using ht

end ConormalGeneration

section CoordinateEquivalence

variable {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]

/-- A constructed scalar coordinate on a spanning generator gives an
actual inverse; the application below obtains this coordinate from the
universal conormal differential and the actual surface Kähler basis. -/
def generatorCoordinateEquiv (n : Q) (c : Q →ₗ[R] R)
    (hc : c n = 1) (hn : Submodule.span R {n} = ⊤) : Q ≃ₗ[R] R :=
  LinearEquiv.ofBijective c (by
    have hrec (x : Q) : c x • n = x := by
      have hx : x ∈ Submodule.span R {n} := hn.symm ▸ Submodule.mem_top
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul, hc, smul_eq_mul, mul_one]
    constructor
    · intro x y hxy
      rw [← hrec x, ← hrec y, hxy]
    · intro a
      exact ⟨a • n, by rw [map_smul, hc, smul_eq_mul, mul_one]⟩)

@[simp] theorem generatorCoordinateEquiv_generator (n : Q) (c : Q →ₗ[R] R)
    (hc : c n = 1) (hn : Submodule.span R {n} = ⊤) :
    generatorCoordinateEquiv n c hc hn n = 1 := hc

theorem generatorCoordinateEquiv_symm_one (n : Q) (c : Q →ₗ[R] R)
    (hc : c n = 1) (hn : Submodule.span R {n} = ⊤) :
    (generatorCoordinateEquiv n c hc hn).symm 1 = n := by
  apply (generatorCoordinateEquiv n c hc hn).injective
  rw [LinearEquiv.apply_symm_apply, generatorCoordinateEquiv_generator]

end CoordinateEquivalence


/-! ## The universal rank-two adjunction map -/

section TwoDimensionalLinearAlgebra

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The determinant coordinate is computed on arbitrary genuine wedges,
not merely on the selected frame. -/
theorem determinantEquiv_pair (b : Basis (Fin 2) R M) (x y : M) :
    determinantEquiv b (exteriorPower.ιMulti R 2 ![x,y]) =
      b.repr x 0 * b.repr y 1 - b.repr x 1 * b.repr y 0 := by
  let s : Set.powersetCard (Fin 2) 2 := ⟨Finset.univ, by simp⟩
  change (b.exteriorPower 2).repr (exteriorPower.ιMulti R 2 ![x,y]) s = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  have hs (j : Fin 2) : Set.powersetCard.ofFinEmbEquiv.symm s j = j := by
    change (Finset.univ : Finset (Fin 2)).orderEmbOfFin (by simp) j = j
    have ho : (fun i : Fin 2 => i) =
        (Finset.univ : Finset (Fin 2)).orderEmbOfFin (by simp) :=
      Finset.orderEmbOfFin_unique _ (fun _ => Finset.mem_univ _) strictMono_id
    exact (congrFun ho j).symm
  simp only [Matrix.det_fin_two, Matrix.of_apply, hs, Basis.coord_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem basis_two_decomposition (b : Basis (Fin 2) R M) (m : M) :
    b.repr m 0 • b 0 + b.repr m 1 • b 1 = m := by
  simpa only [Fin.sum_univ_succ, Fin.val_zero, Fin.succ_zero_eq_one,
    Finset.univ_eq_empty, Finset.sum_empty, add_zero] using b.sum_repr m

/-- A genuine surjective linear map whose proved kernel is the first
basis line has the displayed inverse on its second basis vector. -/
def quotientLineEquiv (b : Basis (Fin 2) R M) (g : M →ₗ[R] N)
    (hg : Function.Surjective g) (hk : LinearMap.ker g = Submodule.span R {b 0}) : R ≃ₗ[R] N :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton R N (g (b 1))) (by
    have hzero : g (b 0) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [hk]
      exact Submodule.subset_span (by simp)
    constructor
    · intro a c hac
      have hz : (a-c) • g (b 1) = 0 := by
        change a • g (b 1) = c • g (b 1) at hac
        rw [sub_smul, hac, sub_self]
      have hm : (a-c) • b 1 ∈ LinearMap.ker g := by
        simpa only [LinearMap.mem_ker, map_smul] using hz
      rw [hk] at hm
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hm
      have hc := congrArg (b.coord 1) hd
      have : a-c = 0 := by
        simpa only [map_smul, Basis.coord_apply, Basis.repr_self,
          Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
          Finsupp.single_eq_same, smul_eq_mul, mul_zero, mul_one] using hc.symm
      exact sub_eq_zero.mp this
    · intro n
      obtain ⟨m,rfl⟩ := hg n
      refine ⟨b.repr m 1, ?_⟩
      change b.repr m 1 • g (b 1) = g m
      conv_rhs => rw [← basis_two_decomposition b m]
      rw [map_add, map_smul, map_smul, hzero, smul_zero, zero_add])

@[simp] theorem quotientLineEquiv_apply (b : Basis (Fin 2) R M) (g : M →ₗ[R] N)
    (hg : Function.Surjective g) (hk : LinearMap.ker g = Submodule.span R {b 0}) (a : R) :
    quotientLineEquiv b g hg hk a = a • g (b 1) := rfl

@[simp] theorem quotientLineEquiv_one (b : Basis (Fin 2) R M) (g : M →ₗ[R] N)
    (hg : Function.Surjective g) (hk : LinearMap.ker g = Submodule.span R {b 0}) :
    quotientLineEquiv b g hg hk 1 = g (b 1) := by
  rw [quotientLineEquiv_apply, one_smul]

theorem quotientLineEquiv_symm_image (b : Basis (Fin 2) R M) (g : M →ₗ[R] N)
    (hg : Function.Surjective g) (hk : LinearMap.ker g = Submodule.span R {b 0}) (m : M) :
    (quotientLineEquiv b g hg hk).symm (g m) = b.repr m 1 := by
  apply (quotientLineEquiv b g hg hk).injective
  rw [LinearEquiv.apply_symm_apply, quotientLineEquiv_apply]
  have hzero : g (b 0) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [hk]
    exact Submodule.subset_span (by simp)
  conv_lhs => rw [← basis_two_decomposition b m]
  rw [map_add, map_smul, map_smul, hzero, smul_zero, zero_add]

end TwoDimensionalLinearAlgebra

section DeterminantBaseChange

variable {S R M : Type*} [CommRing S] [CommRing R] [Algebra S R]
  [AddCommGroup M] [Module S M]

/-- The actual scalar-extension map on top exterior powers. Its formula
on every wedge below fixes the canonical map independently of coordinates. -/
def determinantBaseChange (b : Basis (Fin 2) S M) :
    (⋀[S]^2 M) →ₛₗ[algebraMap S R] (⋀[R]^2 (R ⊗[S] M)) where
  toFun w := algebraMap S R (determinantEquiv b w) •
    exteriorPower.ιMulti R 2 (b.baseChange R)
  map_add' x y := by simp only [map_add, add_smul]
  map_smul' a x := by
    simp only [map_smul, smul_eq_mul, map_mul, mul_smul]

@[simp] theorem determinantBaseChange_wedge (b : Basis (Fin 2) S M) (x y : M) :
    determinantBaseChange (R := R) b (exteriorPower.ιMulti S 2 ![x,y]) =
      exteriorPower.ιMulti R 2 ![(1 : R) ⊗ₜ[S] x, (1 : R) ⊗ₜ[S] y] := by
  apply (determinantEquiv (b.baseChange R)).injective
  simp only [determinantBaseChange, LinearMap.coe_mk, AddHom.coe_mk,
    map_smul, determinantEquiv_wedge, smul_eq_mul, mul_one, determinantEquiv_pair,
    Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one, map_sub, map_mul]

theorem determinantBaseChange_basis (b : Basis (Fin 2) S M) :
    determinantBaseChange (R := R) b (exteriorPower.ιMulti S 2 b) =
      exteriorPower.ιMulti R 2 (b.baseChange R) := by
  change algebraMap S R (determinantEquiv b (exteriorPower.ιMulti S 2 b)) •
    exteriorPower.ιMulti R 2 (b.baseChange R) = exteriorPower.ιMulti R 2 (b.baseChange R)
  rw [determinantEquiv_wedge, map_one, one_smul]

@[simp] theorem determinantBaseChange_coordinate (b : Basis (Fin 2) S M) (w : ⋀[S]^2 M) :
    determinantEquiv (b.baseChange R) (determinantBaseChange (R := R) b w) =
      algebraMap S R (determinantEquiv b w) := by
  change determinantEquiv (b.baseChange R)
    (algebraMap S R (determinantEquiv b w) • exteriorPower.ιMulti R 2 (b.baseChange R)) = _
  rw [map_smul, determinantEquiv_wedge, smul_eq_mul, mul_one]

end DeterminantBaseChange

/-! ## The actual conormal differential on the two normal charts -/

private theorem normalIndex_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

def normalPolynomial (q : AffinePoly) (i : Fin 2) : SurfacePoly := ![includeCurve q, X none] i

def normalMultiplier (g₁ g₂ : SurfacePoly) (i : Fin 2) : SurfacePoly := ![-g₂, g₁] i

abbrev NormalSurfacePatch (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3) :=
  AdjunctionPatch ![surfaceEquation q h g₁ g₂ k, includeCurve h]
    (normalPolynomial q i) (includeCurve (X j))

abbrev NormalCurvePatch (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3) :=
  CurveAdjunctionPatch q h g₁ g₂ k (normalPolynomial q i) (includeCurve (X j))

def normalChartMap (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3) :
    NormalSurfacePatch q h g₁ g₂ k i j →ₐ[ℂ] NormalCurvePatch q h g₁ g₂ k i j :=
  adjunctionToCurve q h g₁ g₂ k (normalPolynomial q i) (includeCurve (X j))

instance normalChartAlgebra (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3) :
    Algebra (NormalSurfacePatch q h g₁ g₂ k i j) (NormalCurvePatch q h g₁ g₂ k i j) :=
  (normalChartMap q h g₁ g₂ k i j).toRingHom.toAlgebra

instance normalChartScalarTower (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    IsScalarTower ℂ (NormalSurfacePatch q h g₁ g₂ k i j) (NormalCurvePatch q h g₁ g₂ k i j) :=
  IsScalarTower.of_algHom (normalChartMap q h g₁ g₂ k i j)

def normalCoefficientMap (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) : SurfacePoly →ₐ[ℂ] NormalCurvePatch q h g₁ g₂ k i j :=
  (IsScalarTower.toAlgHom ℂ (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j)).comp
    (polynomialToCurve q h)

@[simp] theorem normalAlgebraMap_polynomial (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (p : SurfacePoly) :
    algebraMap (NormalSurfacePatch q h g₁ g₂ k i j) (NormalCurvePatch q h g₁ g₂ k i j)
      (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) p) =
      normalCoefficientMap q h g₁ g₂ k i j p := by
  change adjunctionToCurve q h g₁ g₂ k (normalPolynomial q i) (includeCurve (X j))
    (algebraMap (SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h])
      (NormalSurfacePatch q h g₁ g₂ k i j)
        (surfaceMap ![surfaceEquation q h g₁ g₂ k, includeCurve h] p)) = _
  rw [adjunctionToCurve_base]
  rfl

abbrev NormalCurveIdeal (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3) :=
  RingHom.ker (algebraMap (NormalSurfacePatch q h g₁ g₂ k i j)
    (NormalCurvePatch q h g₁ g₂ k i j))

theorem normalEquation_mem (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (normalPolynomial q a) ∈
      NormalCurveIdeal q h g₁ g₂ k i j := by
  change adjunctionToCurve q h g₁ g₂ k (normalPolynomial q i) (includeCurve (X j))
    (algebraMap (SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h])
      (NormalSurfacePatch q h g₁ g₂ k i j)
        (surfaceMap ![surfaceEquation q h g₁ g₂ k, includeCurve h] (normalPolynomial q a))) = 0
  rw [adjunctionToCurve_base]
  change algebraMap (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j)
    (polynomialToCurve q h (normalPolynomial q a)) = 0
  rcases normalIndex_cases a with rfl | rfl <;>
    simp only [normalPolynomial, Matrix.cons_val_zero, Matrix.cons_val_one,
      polynomialToCurve_quadric, polynomialToCurve_normal, map_zero]

theorem normalEquations_span (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    Submodule.span (NormalSurfacePatch q h g₁ g₂ k i j)
      (Set.range (fun a => algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j)
        (normalPolynomial q a))) = NormalCurveIdeal q h g₁ g₂ k i j := by
  change _ = RingHom.ker
    (adjunctionToCurve q h g₁ g₂ k (normalPolynomial q i) (includeCurve (X j))).toRingHom
  rw [adjunctionToCurve_kernel]
  congr 1
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    rcases normalIndex_cases a with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (hx | hx)
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩

/-- The conormal module is that of the actual kernel of the actual
localized surface-to-curve map, followed by its actual scalar extension. -/
abbrev NormalConormal (q h : AffinePoly) (g₁ g₂ k : SurfacePoly) (i : Fin 2) (j : Fin 3) :=
  NormalCurvePatch q h g₁ g₂ k i j ⊗[NormalSurfacePatch q h g₁ g₂ k i j]
    (NormalCurveIdeal q h g₁ g₂ k i j).Cotangent

def normalEquationClass (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (a : Fin 2) : NormalConormal q h g₁ g₂ k i j :=
  tensorCotangentClass (R := NormalCurvePatch q h g₁ g₂ k i j)
    (NormalCurveIdeal q h g₁ g₂ k i j)
    (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (normalPolynomial q a))
    (normalEquation_mem q h g₁ g₂ k i j a)

theorem normalEquationClasses_span (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    Submodule.span (NormalCurvePatch q h g₁ g₂ k i j)
      (Set.range (normalEquationClass q h g₁ g₂ k i j)) = ⊤ :=
  tensorCotangent_generators_span (R := NormalCurvePatch q h g₁ g₂ k i j)
    (NormalCurveIdeal q h g₁ g₂ k i j)
    (fun a => algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j)
      (normalPolynomial q a)) (normalEquation_mem q h g₁ g₂ k i j)
        (normalEquations_span q h g₁ g₂ k i j)

abbrev RestrictedSurfaceDifferentials (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :=
  NormalCurvePatch q h g₁ g₂ k i j ⊗[NormalSurfacePatch q h g₁ g₂ k i j]
    KaehlerDifferential ℂ (NormalSurfacePatch q h g₁ g₂ k i j)

/-- The canonical conormal differential, not an arbitrarily selected
map between free modules. -/
def normalConormalDifferential (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      RestrictedSurfaceDifferentials q h g₁ g₂ k i j :=
  (KaehlerDifferential.kerCotangentToTensor ℂ (NormalSurfacePatch q h g₁ g₂ k i j)
    (NormalCurvePatch q h g₁ g₂ k i j)).liftBaseChange (NormalCurvePatch q h g₁ g₂ k i j)

def restrictedSurfaceBasis (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    Basis (Fin 2) (NormalCurvePatch q h g₁ g₂ k i j)
      (RestrictedSurfaceDifferentials q h g₁ g₂ k i j) :=
  (localSurfaceKaehlerBasis ![surfaceEquation q h g₁ g₂ k, includeCurve h]
    (normalPolynomial q i) (includeCurve (X j))).baseChange (NormalCurvePatch q h g₁ g₂ k i j)

@[simp] theorem normalConormalDifferential_equation (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    normalConormalDifferential q h g₁ g₂ k i j (normalEquationClass q h g₁ g₂ k i j a) =
      (1 : NormalCurvePatch q h g₁ g₂ k i j) ⊗ₜ[NormalSurfacePatch q h g₁ g₂ k i j]
        KaehlerDifferential.D ℂ (NormalSurfacePatch q h g₁ g₂ k i j)
          (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (normalPolynomial q a)) := by
  simp only [normalConormalDifferential, normalEquationClass, tensorCotangentClass,
    LinearMap.liftBaseChange_tmul, one_smul, KaehlerDifferential.kerCotangentToTensor_toCotangent]

@[simp] theorem normalConormalDifferential_selected (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    normalConormalDifferential q h g₁ g₂ k i j (normalEquationClass q h g₁ g₂ k i j i) =
      restrictedSurfaceBasis q h g₁ g₂ k i j 0 := by
  rw [normalConormalDifferential_equation, restrictedSurfaceBasis, Basis.baseChange_apply,
    localSurfaceKaehlerBasis_apply]
  rfl

theorem normalAugmentedJacobian_restriction (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    surfaceToCurve q h g₁ g₂ k
      (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (normalPolynomial q i) (includeCurve (X j))) =
      polynomialToCurve q h (normalMultiplier g₁ g₂ i) * chartMinor ![q,h] j := by
  rcases normalIndex_cases i with rfl | rfl
  · simpa only [normalPolynomial, normalMultiplier, Matrix.cons_val_zero, map_neg] using
      augmentedJacobian_quadric_restriction q h g₁ g₂ k j
  · simpa only [normalPolynomial, normalMultiplier, Matrix.cons_val_one, Matrix.cons_val_zero] using
      augmentedJacobian_normal_restriction q h g₁ g₂ k j

/-- The determinant restriction in a fixed actual curve localization.
Mapping the equality first keeps the localization carrier fixed. -/
theorem normalAugmentedJacobian_map (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    algebraMap (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j)
      (surfaceToCurve q h g₁ g₂ k
        (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (normalPolynomial q i) (includeCurve (X j)))) =
      normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i) *
        algebraMap (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j)
          (chartMinor ![q,h] j) := by
  have he := congrArg (algebraMap (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j))
    (normalAugmentedJacobian_restriction q h g₁ g₂ k i j)
  rw [map_mul] at he
  exact he

/-- The coefficient required to eliminate the other conormal generator
is a unit on the actual curve patch because it is a factor of the inverted
actual augmented determinant. It is not assumed a unit on the whole surface. -/
theorem normalMultiplier_isUnit (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    IsUnit (normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := NormalCurvePatch q h g₁ g₂ k i j)
    (surfaceToCurve q h g₁ g₂ k
      (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (normalPolynomial q i) (includeCurve (X j))))
  have hv := (normalAugmentedJacobian_map q h g₁ g₂ k i j) ▸ hu
  exact (IsUnit.mul_iff.mp hv).1

theorem normalCurveMinor_isUnit (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    IsUnit (algebraMap (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j)
      (chartMinor ![q,h] j)) := by
  have hu := IsLocalization.Away.algebraMap_isUnit
    (S := NormalCurvePatch q h g₁ g₂ k i j)
    (surfaceToCurve q h g₁ g₂ k
      (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (normalPolynomial q i) (includeCurve (X j))))
  have hv := (normalAugmentedJacobian_map q h g₁ g₂ k i j) ▸ hu
  exact (IsUnit.mul_iff.mp hv).2

theorem normalSurface_equation_relation (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) g₁ *
        algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (includeCurve q) +
      algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) g₂ *
        algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (X none) = 0 := by
  have hf : algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j)
      (surfaceEquation q h g₁ g₂ k) = 0 := by
    change algebraMap (SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h])
      (NormalSurfacePatch q h g₁ g₂ k i j)
        (surfaceMap ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (![surfaceEquation q h g₁ g₂ k, includeCurve h] 0)) = 0
    rw [surfaceMap_relation, map_zero]
  have hh : algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (includeCurve h) = 0 := by
    change algebraMap (SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h])
      (NormalSurfacePatch q h g₁ g₂ k i j)
        (surfaceMap ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (![surfaceEquation q h g₁ g₂ k, includeCurve h] 1)) = 0
    rw [surfaceMap_relation, map_zero]
  simpa only [surfaceEquation, map_add, map_mul, hh, zero_mul, add_zero, mul_comm] using hf

theorem normalEquationClasses_relation (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    normalCoefficientMap q h g₁ g₂ k i j g₁ • normalEquationClass q h g₁ g₂ k i j 0 +
      normalCoefficientMap q h g₁ g₂ k i j g₂ • normalEquationClass q h g₁ g₂ k i j 1 = 0 := by
  have hr := tensorCotangent_pair_relation (R := NormalCurvePatch q h g₁ g₂ k i j)
    (NormalCurveIdeal q h g₁ g₂ k i j)
    (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (includeCurve q))
    (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (X none))
    (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) g₁)
    (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) g₂)
    (normalEquation_mem q h g₁ g₂ k i j 0) (normalEquation_mem q h g₁ g₂ k i j 1)
    (normalSurface_equation_relation q h g₁ g₂ k i j)
  simpa only [normalAlgebraMap_polynomial, normalEquationClass, normalPolynomial,
    Matrix.cons_val_zero, Matrix.cons_val_one] using hr

theorem selectedNormalEquationClass_span (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    Submodule.span (NormalCurvePatch q h g₁ g₂ k i j)
      {normalEquationClass q h g₁ g₂ k i j i} = ⊤ := by
  apply top_unique
  rw [← normalEquationClasses_span q h g₁ g₂ k i j]
  apply Submodule.span_le.mpr
  rintro x ⟨a, rfl⟩
  have hr := normalEquationClasses_relation q h g₁ g₂ k i j
  have hu := normalMultiplier_isUnit q h g₁ g₂ k i j
  rcases normalIndex_cases i with rfl | rfl <;>
    rcases normalIndex_cases a with rfl | rfl
  · exact Submodule.subset_span (by simp)
  · have hu₂ : IsUnit (normalCoefficientMap q h g₁ g₂ k 0 j g₂) := by
      simpa only [normalMultiplier, Matrix.cons_val_zero, map_neg, IsUnit.neg_iff] using hu
    apply (Submodule.smul_mem_iff_of_isUnit _ hu₂).mp
    rw [eq_neg_of_add_eq_zero_right hr]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · have hu₁ : IsUnit (normalCoefficientMap q h g₁ g₂ k 1 j g₁) := by
      simpa only [normalMultiplier, Matrix.cons_val_one, Matrix.cons_val_zero] using hu
    apply (Submodule.smul_mem_iff_of_isUnit _ hu₁).mp
    rw [eq_neg_of_add_eq_zero_left hr]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · exact Submodule.subset_span (by simp)

def normalConormalCoordinate (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j :=
  ((restrictedSurfaceBasis q h g₁ g₂ k i j).coord 0).comp
    (normalConormalDifferential q h g₁ g₂ k i j)

@[simp] theorem normalConormalCoordinate_selected (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    normalConormalCoordinate q h g₁ g₂ k i j (normalEquationClass q h g₁ g₂ k i j i) = 1 := by
  simp only [normalConormalCoordinate, LinearMap.comp_apply,
    normalConormalDifferential_selected, Basis.coord_apply, Basis.repr_self,
    Finsupp.single_eq_same]

/-- A genuine trivialization of the actual conormal module is constructed
from its proved generating equation and its universal conormal differential. -/
def normalConormalEquiv (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    NormalConormal q h g₁ g₂ k i j ≃ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j :=
  generatorCoordinateEquiv (normalEquationClass q h g₁ g₂ k i j i)
    (normalConormalCoordinate q h g₁ g₂ k i j)
    (normalConormalCoordinate_selected q h g₁ g₂ k i j)
    (selectedNormalEquationClass_span q h g₁ g₂ k i j)

/-! ## The second fundamental sequence for the constructed closed immersion -/

theorem normalChartAlgebra_surjective (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    Function.Surjective (algebraMap (NormalSurfacePatch q h g₁ g₂ k i j)
      (NormalCurvePatch q h g₁ g₂ k i j)) := by
  change Function.Surjective (normalChartMap q h g₁ g₂ k i j)
  exact adjunctionToCurve_surjective q h g₁ g₂ k (normalPolynomial q i) (includeCurve (X j))

@[simp] theorem normalConormalEquiv_selected (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    normalConormalEquiv q h g₁ g₂ k i j (normalEquationClass q h g₁ g₂ k i j i) = 1 :=
  normalConormalCoordinate_selected q h g₁ g₂ k i j

theorem normalConormal_reconstruct (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (x : NormalConormal q h g₁ g₂ k i j) :
    normalConormalEquiv q h g₁ g₂ k i j x • normalEquationClass q h g₁ g₂ k i j i = x := by
  apply (normalConormalEquiv q h g₁ g₂ k i j).injective
  rw [map_smul, normalConormalEquiv_selected, smul_eq_mul, mul_one]

theorem normalConormalDifferential_eq (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (x : NormalConormal q h g₁ g₂ k i j) :
    normalConormalDifferential q h g₁ g₂ k i j x =
      normalConormalEquiv q h g₁ g₂ k i j x • restrictedSurfaceBasis q h g₁ g₂ k i j 0 := by
  conv_lhs => rw [← normalConormal_reconstruct q h g₁ g₂ k i j x]
  rw [map_smul, normalConormalDifferential_selected]

/-- The canonical map in the second fundamental sequence of the actual
localized surface-to-curve quotient. -/
def normalToCurveKaehler (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    RestrictedSurfaceDifferentials q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      KaehlerDifferential ℂ (NormalCurvePatch q h g₁ g₂ k i j) :=
  KaehlerDifferential.mapBaseChange ℂ (NormalSurfacePatch q h g₁ g₂ k i j)
    (NormalCurvePatch q h g₁ g₂ k i j)

@[simp] theorem normalToCurveKaehler_selected (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    normalToCurveKaehler q h g₁ g₂ k i j (restrictedSurfaceBasis q h g₁ g₂ k i j 0) = 0 := by
  rw [← normalConormalDifferential_selected, normalConormalDifferential_equation]
  change KaehlerDifferential.mapBaseChange ℂ (NormalSurfacePatch q h g₁ g₂ k i j)
    (NormalCurvePatch q h g₁ g₂ k i j) (1 ⊗ₜ KaehlerDifferential.D ℂ
      (NormalSurfacePatch q h g₁ g₂ k i j)
        (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j)
          (normalPolynomial q i))) = 0
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
    RingHom.mem_ker.mp (normalEquation_mem q h g₁ g₂ k i j i), map_zero]

@[simp] theorem normalToCurveKaehler_last (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    normalToCurveKaehler q h g₁ g₂ k i j (restrictedSurfaceBasis q h g₁ g₂ k i j 1) =
      KaehlerDifferential.D ℂ (NormalCurvePatch q h g₁ g₂ k i j)
        (normalCoefficientMap q h g₁ g₂ k i j (includeCurve (X j))) := by
  rw [restrictedSurfaceBasis, Basis.baseChange_apply, localSurfaceKaehlerBasis_apply]
  simp only [normalToCurveKaehler, Matrix.cons_val_one, Matrix.cons_val_zero,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D,
    normalAlgebraMap_polynomial]

theorem normalToCurveKaehler_surjective (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    Function.Surjective (normalToCurveKaehler q h g₁ g₂ k i j) :=
  KaehlerDifferential.mapBaseChange_surjective ℂ (NormalSurfacePatch q h g₁ g₂ k i j)
    (NormalCurvePatch q h g₁ g₂ k i j)
      (normalChartAlgebra_surjective q h g₁ g₂ k i j)

/-- Exactness is obtained from Mathlib's second fundamental sequence
for the constructed surjective quotient map, not assumed as a comparison. -/
theorem normalToCurveKaehler_kernel (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    LinearMap.ker (normalToCurveKaehler q h g₁ g₂ k i j) =
      Submodule.span (NormalCurvePatch q h g₁ g₂ k i j)
        {restrictedSurfaceBasis q h g₁ g₂ k i j 0} := by
  apply le_antisymm
  · intro x hx
    have he := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange ℂ
      (NormalSurfacePatch q h g₁ g₂ k i j) (NormalCurvePatch q h g₁ g₂ k i j)
      (normalChartAlgebra_surjective q h g₁ g₂ k i j)
    obtain ⟨a, ha⟩ := (he x).mp hx
    let y : NormalConormal q h g₁ g₂ k i j := (1 : NormalCurvePatch q h g₁ g₂ k i j) ⊗ₜ a
    have hy : normalConormalDifferential q h g₁ g₂ k i j y = x := by
      simpa only [normalConormalDifferential, y, LinearMap.liftBaseChange_tmul, one_smul] using ha
    rw [← hy, normalConormalDifferential_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    rintro x rfl
    exact normalToCurveKaehler_selected q h g₁ g₂ k i j

/-- The actual curve Kähler coordinate is dual to the actual surviving
coordinate differential in the second fundamental sequence. -/
def normalCurveKaehlerEquiv (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    KaehlerDifferential ℂ (NormalCurvePatch q h g₁ g₂ k i j) ≃ₗ[
      NormalCurvePatch q h g₁ g₂ k i j] NormalCurvePatch q h g₁ g₂ k i j :=
  (quotientLineEquiv (restrictedSurfaceBasis q h g₁ g₂ k i j)
    (normalToCurveKaehler q h g₁ g₂ k i j) (normalToCurveKaehler_surjective q h g₁ g₂ k i j)
    (normalToCurveKaehler_kernel q h g₁ g₂ k i j)).symm

@[simp] theorem normalCurveKaehlerEquiv_image (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (m : RestrictedSurfaceDifferentials q h g₁ g₂ k i j) :
    normalCurveKaehlerEquiv q h g₁ g₂ k i j (normalToCurveKaehler q h g₁ g₂ k i j m) =
      (restrictedSurfaceBasis q h g₁ g₂ k i j).repr m 1 :=
  quotientLineEquiv_symm_image _ _ _ _ m

@[simp] theorem normalCurveKaehlerEquiv_coordinate (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    normalCurveKaehlerEquiv q h g₁ g₂ k i j
      (KaehlerDifferential.D ℂ (NormalCurvePatch q h g₁ g₂ k i j)
        (normalCoefficientMap q h g₁ g₂ k i j (includeCurve (X j)))) = 1 := by
  rw [← normalToCurveKaehler_last, normalCurveKaehlerEquiv_image,
    Basis.repr_self, Finsupp.single_eq_same]

/-- The canonical local adjunction contraction of an actual conormal dual
with an actual surface determinant. The intrinsic formula below fixes its
normal-first orientation on every conormal class and every differential. -/
def normalAdjunction (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3)
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j) :
    (⋀[NormalCurvePatch q h g₁ g₂ k i j]^2
      (RestrictedSurfaceDifferentials q h g₁ g₂ k i j)) →ₗ[
        NormalCurvePatch q h g₁ g₂ k i j]
          KaehlerDifferential ℂ (NormalCurvePatch q h g₁ g₂ k i j) :=
  (determinantEquiv (restrictedSurfaceBasis q h g₁ g₂ k i j)).toLinearMap.smulRight
    (φ (normalEquationClass q h g₁ g₂ k i j i) •
      normalToCurveKaehler q h g₁ g₂ k i j (restrictedSurfaceBasis q h g₁ g₂ k i j 1))

theorem normalAdjunction_intrinsic (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3)
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j)
    (x : NormalConormal q h g₁ g₂ k i j)
    (m : RestrictedSurfaceDifferentials q h g₁ g₂ k i j) :
    normalAdjunction q h g₁ g₂ k i j φ
      (exteriorPower.ιMulti (NormalCurvePatch q h g₁ g₂ k i j) 2
        ![normalConormalDifferential q h g₁ g₂ k i j x, m]) =
      φ x • normalToCurveKaehler q h g₁ g₂ k i j m := by
  apply (normalCurveKaehlerEquiv q h g₁ g₂ k i j).injective
  simp only [normalAdjunction, LinearMap.smulRight_apply, LinearEquiv.coe_coe,
    map_smul, normalCurveKaehlerEquiv_image, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, determinantEquiv_pair, normalConormalDifferential_eq,
    Finsupp.smul_apply, Basis.repr_self,
    Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0), zero_mul, sub_zero]
  have hφ : φ x = normalConormalEquiv q h g₁ g₂ k i j x *
      φ (normalEquationClass q h g₁ g₂ k i j i) := by
    conv_lhs => rw [← normalConormal_reconstruct q h g₁ g₂ k i j x]
    rw [map_smul, smul_eq_mul]
  rw [hφ]
  ring

private theorem determinant_normal_hom_ext {R Q M N : Type*}
    [CommRing R] [AddCommGroup Q] [Module R Q]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (b : Basis (Fin 2) R M) (j : Q →ₗ[R] M) (n : Q) (hn : j n = b 0)
    (g : M →ₗ[R] N) (φ : Q →ₗ[R] R) (f F : (⋀[R]^2 M) →ₗ[R] N)
    (hf : ∀ x m, f (exteriorPower.ιMulti R 2 ![j x,m]) = φ x • g m)
    (hF : ∀ x m, F (exteriorPower.ιMulti R 2 ![j x,m]) = φ x • g m) : f = F := by
  have hframe : f (exteriorPower.ιMulti R 2 b) = F (exteriorPower.ιMulti R 2 b) := by
    have he : (![b 0,b 1] : Fin 2 → M) = b := by ext a; fin_cases a <;> rfl
    simpa only [hn, he] using (hf n (b 1)).trans (hF n (b 1)).symm
  apply LinearMap.ext
  intro w
  have hw : determinantEquiv b w • exteriorPower.ιMulti _ 2 b = w := by
    apply (determinantEquiv b).injective
    rw [map_smul, determinantEquiv_wedge, smul_eq_mul, mul_one]
  rw [← hw, map_smul, map_smul, hframe]

/-- The intrinsic characterization is unique: setting the conormal class
to its actual generating equation and the differential to the second basis
vector determines the map on the whole top exterior power. -/
theorem normalAdjunction_unique (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3)
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j)
    (f : (⋀[NormalCurvePatch q h g₁ g₂ k i j]^2
      (RestrictedSurfaceDifferentials q h g₁ g₂ k i j)) →ₗ[
        NormalCurvePatch q h g₁ g₂ k i j]
          KaehlerDifferential ℂ (NormalCurvePatch q h g₁ g₂ k i j))
    (hf : ∀ x m, f (exteriorPower.ιMulti (NormalCurvePatch q h g₁ g₂ k i j) 2
        ![normalConormalDifferential q h g₁ g₂ k i j x, m]) =
      φ x • normalToCurveKaehler q h g₁ g₂ k i j m) :
    f = normalAdjunction q h g₁ g₂ k i j φ :=
  determinant_normal_hom_ext (restrictedSurfaceBasis q h g₁ g₂ k i j)
    (normalConormalDifferential q h g₁ g₂ k i j)
    (normalEquationClass q h g₁ g₂ k i j i)
    (normalConormalDifferential_selected q h g₁ g₂ k i j)
    (normalToCurveKaehler q h g₁ g₂ k i j) φ f (normalAdjunction q h g₁ g₂ k i j φ) hf
    (normalAdjunction_intrinsic q h g₁ g₂ k i j φ)

/-- Evaluation on the actual conormal generator identifies its actual
linear dual; the inverse is the already constructed conormal coordinate. -/
def normalDualEquiv (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    (NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j) ≃ₗ[NormalCurvePatch q h g₁ g₂ k i j]
        NormalCurvePatch q h g₁ g₂ k i j where
  toFun φ := φ (normalEquationClass q h g₁ g₂ k i j i)
  invFun a := a • (normalConormalEquiv q h g₁ g₂ k i j).toLinearMap
  left_inv φ := by
    apply LinearMap.ext
    intro x
    change φ (normalEquationClass q h g₁ g₂ k i j i) *
      normalConormalEquiv q h g₁ g₂ k i j x = φ x
    conv_rhs => rw [← normalConormal_reconstruct q h g₁ g₂ k i j x]
    rw [map_smul, smul_eq_mul]
    exact mul_comm _ _
  right_inv a := by
    simp only [LinearMap.smul_apply, LinearEquiv.coe_coe,
      normalConormalEquiv_selected, smul_eq_mul, mul_one]
  map_add' φ ψ := rfl
  map_smul' a φ := rfl

@[simp] theorem normalDualEquiv_apply (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3)
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j) :
    normalDualEquiv q h g₁ g₂ k i j φ = φ (normalEquationClass q h g₁ g₂ k i j i) := rfl

@[simp] theorem normalCurveKaehlerEquiv_symm_apply (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (a : NormalCurvePatch q h g₁ g₂ k i j) :
    (normalCurveKaehlerEquiv q h g₁ g₂ k i j).symm a =
      a • normalToCurveKaehler q h g₁ g₂ k i j (restrictedSurfaceBasis q h g₁ g₂ k i j 1) :=
  quotientLineEquiv_apply (restrictedSurfaceBasis q h g₁ g₂ k i j)
    (normalToCurveKaehler q h g₁ g₂ k i j)
    (normalToCurveKaehler_surjective q h g₁ g₂ k i j)
    (normalToCurveKaehler_kernel q h g₁ g₂ k i j) a

/-- The actual adjunction isomorphism on the constructed surface/curve
Jacobian patch. Both its exact sequence and its conormal basis have been
proved for these rings; no adjunction or freeness premise is supplied. -/
def normalAdjunctionEquiv (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    ((NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
        NormalCurvePatch q h g₁ g₂ k i j) ⊗[NormalCurvePatch q h g₁ g₂ k i j]
      (⋀[NormalCurvePatch q h g₁ g₂ k i j]^2
        (RestrictedSurfaceDifferentials q h g₁ g₂ k i j))) ≃ₗ[
          NormalCurvePatch q h g₁ g₂ k i j]
            KaehlerDifferential ℂ (NormalCurvePatch q h g₁ g₂ k i j) :=
  (TensorProduct.congr (normalDualEquiv q h g₁ g₂ k i j)
    (determinantEquiv (restrictedSurfaceBasis q h g₁ g₂ k i j))).trans
      ((TensorProduct.lid (NormalCurvePatch q h g₁ g₂ k i j)
        (NormalCurvePatch q h g₁ g₂ k i j)).trans
          (normalCurveKaehlerEquiv q h g₁ g₂ k i j).symm)

@[simp] theorem normalAdjunctionEquiv_tmul (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3)
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j)
    (w : ⋀[NormalCurvePatch q h g₁ g₂ k i j]^2
      (RestrictedSurfaceDifferentials q h g₁ g₂ k i j)) :
    normalAdjunctionEquiv q h g₁ g₂ k i j (φ ⊗ₜ w) =
      normalAdjunction q h g₁ g₂ k i j φ w := by
  simp only [normalAdjunctionEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    TensorProduct.lid_tmul, smul_eq_mul, normalDualEquiv_apply,
    normalCurveKaehlerEquiv_symm_apply, normalAdjunction, LinearMap.smulRight_apply,
    LinearEquiv.coe_coe, smul_smul]
  congr 1
  exact mul_comm _ _
/-! ## The fixed normal vector and the actual residue contraction -/

/-- The normal dual is characterized below on the literal equations
q=f₁ and z=f₂. Its values are exactly (G₂,−G₁), with no free rescaling. -/
def normalVector (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j :=
  (-normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i)) •
    (normalConormalEquiv q h g₁ g₂ k i j).toLinearMap

@[simp] theorem normalVector_selected (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    normalVector q h g₁ g₂ k i j (normalEquationClass q h g₁ g₂ k i j i) =
      -normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i) := by
  simp only [normalVector, LinearMap.smul_apply, LinearEquiv.coe_coe,
    normalConormalEquiv_selected, smul_eq_mul, mul_one]

theorem normalVector_equation (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (a : Fin 2) :
    normalVector q h g₁ g₂ k i j (normalEquationClass q h g₁ g₂ k i j a) =
      ![normalCoefficientMap q h g₁ g₂ k i j g₂,
        -normalCoefficientMap q h g₁ g₂ k i j g₁] a := by
  have hrel := congrArg (normalVector q h g₁ g₂ k i j)
    (normalEquationClasses_relation q h g₁ g₂ k i j)
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at hrel
  have hu := normalMultiplier_isUnit q h g₁ g₂ k i j
  rcases normalIndex_cases i with rfl | rfl <;>
    rcases normalIndex_cases a with rfl | rfl
  · simpa only [normalMultiplier, Matrix.cons_val_zero, map_neg, neg_neg] using
      normalVector_selected q h g₁ g₂ k 0 j
  · have hu₂ : IsUnit (normalCoefficientMap q h g₁ g₂ k 0 j g₂) := by
      simpa only [normalMultiplier, Matrix.cons_val_zero, map_neg, IsUnit.neg_iff] using hu
    apply hu₂.mul_left_cancel
    have hs : normalVector q h g₁ g₂ k 0 j (normalEquationClass q h g₁ g₂ k 0 j 0) =
        normalCoefficientMap q h g₁ g₂ k 0 j g₂ := by
      simpa only [normalMultiplier, Matrix.cons_val_zero, map_neg, neg_neg] using
        normalVector_selected q h g₁ g₂ k 0 j
    rw [hs] at hrel
    calc
      _ = -(normalCoefficientMap q h g₁ g₂ k 0 j g₁ *
          normalCoefficientMap q h g₁ g₂ k 0 j g₂) := eq_neg_of_add_eq_zero_right hrel
      _ = _ := by simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; ring
  · have hu₁ : IsUnit (normalCoefficientMap q h g₁ g₂ k 1 j g₁) := by
      simpa only [normalMultiplier, Matrix.cons_val_one, Matrix.cons_val_zero] using hu
    apply hu₁.mul_left_cancel
    have hs := normalVector_selected q h g₁ g₂ k 1 j
    simp only [normalMultiplier, Matrix.cons_val_one, Matrix.cons_val_zero] at hs
    rw [hs] at hrel
    calc
      _ = -(normalCoefficientMap q h g₁ g₂ k 1 j g₂ *
          -normalCoefficientMap q h g₁ g₂ k 1 j g₁) := eq_neg_of_add_eq_zero_left hrel
      _ = _ := by simp only [Matrix.cons_val_zero]; ring
  · simpa only [normalMultiplier, Matrix.cons_val_one, Matrix.cons_val_zero] using
      normalVector_selected q h g₁ g₂ k 1 j

theorem normalVector_unique (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3)
    (φ : NormalConormal q h g₁ g₂ k i j →ₗ[NormalCurvePatch q h g₁ g₂ k i j]
      NormalCurvePatch q h g₁ g₂ k i j)
    (hφ : ∀ a, φ (normalEquationClass q h g₁ g₂ k i j a) =
      ![normalCoefficientMap q h g₁ g₂ k i j g₂,
        -normalCoefficientMap q h g₁ g₂ k i j g₁] a) :
    φ = normalVector q h g₁ g₂ k i j := by
  apply LinearMap.ext_on (normalEquationClasses_span q h g₁ g₂ k i j)
  rintro x ⟨a,rfl⟩
  exact (hφ a).trans (normalVector_equation q h g₁ g₂ k i j a).symm

/-- Restriction of the actual surface top form by the canonical exterior
scalar-extension map, characterized above on every genuine wedge. -/
def restrictedSurfaceResidueForm (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    ⋀[NormalCurvePatch q h g₁ g₂ k i j]^2
      (RestrictedSurfaceDifferentials q h g₁ g₂ k i j) :=
  determinantBaseChange (R := NormalCurvePatch q h g₁ g₂ k i j)
    (localSurfaceKaehlerBasis ![surfaceEquation q h g₁ g₂ k, includeCurve h]
      (normalPolynomial q i) (includeCurve (X j)))
    (localSurfaceResidueForm ![surfaceEquation q h g₁ g₂ k, includeCurve h]
      (normalPolynomial q i) (includeCurve (X j)))

/-- The actual surface determinant has the precise restriction ±GJ. -/
theorem restrictedSurfaceResidue_normalization (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    (normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i) *
      algebraMap (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j) (chartMinor ![q,h] j)) *
      determinantEquiv (restrictedSurfaceBasis q h g₁ g₂ k i j)
        (restrictedSurfaceResidueForm q h g₁ g₂ k i j) = 1 := by
  have hs := localSurfaceResidueForm_normalization
    ![surfaceEquation q h g₁ g₂ k, includeCurve h]
      (normalPolynomial q i) (includeCurve (X j))
  change (↑((IsLocalization.Away.algebraMap_isUnit
    (S := NormalSurfacePatch q h g₁ g₂ k i j)
    (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h]
      (normalPolynomial q i) (includeCurve (X j)))).unit) :
        NormalSurfacePatch q h g₁ g₂ k i j) *
      determinantEquiv (localSurfaceKaehlerBasis
        ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (normalPolynomial q i) (includeCurve (X j)))
        (localSurfaceResidueForm ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (normalPolynomial q i) (includeCurve (X j))) = 1 at hs
  rw [IsUnit.unit_spec] at hs
  let f : NormalSurfacePatch q h g₁ g₂ k i j →+* NormalCurvePatch q h g₁ g₂ k i j :=
    algebraMap (NormalSurfacePatch q h g₁ g₂ k i j) (NormalCurvePatch q h g₁ g₂ k i j)
  let d : NormalSurfacePatch q h g₁ g₂ k i j :=
    algebraMap (SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h])
      (NormalSurfacePatch q h g₁ g₂ k i j)
      (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (normalPolynomial q i) (includeCurve (X j)))
  let a : NormalSurfacePatch q h g₁ g₂ k i j :=
    determinantEquiv (localSurfaceKaehlerBasis
      ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (normalPolynomial q i) (includeCurve (X j)))
      (localSurfaceResidueForm ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (normalPolynomial q i) (includeCurve (X j)))
  have hd : f d = normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i) *
      algebraMap (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j) (chartMinor ![q,h] j) := by
    change adjunctionToCurve q h g₁ g₂ k (normalPolynomial q i) (includeCurve (X j))
      (algebraMap (SurfaceChartRing ![surfaceEquation q h g₁ g₂ k, includeCurve h])
        (NormalSurfacePatch q h g₁ g₂ k i j)
        (augmentedJacobian ![surfaceEquation q h g₁ g₂ k, includeCurve h]
          (normalPolynomial q i) (includeCurve (X j)))) = _
    rw [adjunctionToCurve_base]
    exact normalAugmentedJacobian_map q h g₁ g₂ k i j
  have ha : determinantEquiv (restrictedSurfaceBasis q h g₁ g₂ k i j)
      (restrictedSurfaceResidueForm q h g₁ g₂ k i j) = f a :=
    determinantBaseChange_coordinate (R := NormalCurvePatch q h g₁ g₂ k i j)
      (localSurfaceKaehlerBasis ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (normalPolynomial q i) (includeCurve (X j)))
      (localSurfaceResidueForm ![surfaceEquation q h g₁ g₂ k, includeCurve h]
        (normalPolynomial q i) (includeCurve (X j)))
  calc
    _ = f d * f a := congrArg₂ (fun x y : NormalCurvePatch q h g₁ g₂ k i j => x * y)
      hd.symm ha
    _ = f (d * a) := (map_mul f d a).symm
    _ = f 1 := congrArg f hs
    _ = 1 := map_one f

/-- The contraction of the actual surface residue by the fixed actual
normal vector is the negatively oriented curve residue on both normal
charts: the f₂ determinant is +G₁J and the f₁ determinant is −G₂J. -/
theorem normalAdjunction_residue_balance (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    algebraMap (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j) (chartMinor ![q,h] j) •
      normalAdjunction q h g₁ g₂ k i j (normalVector q h g₁ g₂ k i j)
        (restrictedSurfaceResidueForm q h g₁ g₂ k i j) =
      -KaehlerDifferential.D ℂ (NormalCurvePatch q h g₁ g₂ k i j)
        (normalCoefficientMap q h g₁ g₂ k i j (includeCurve (X j))) := by
  apply (normalCurveKaehlerEquiv q h g₁ g₂ k i j).injective
  simp only [map_smul, map_neg, normalAdjunction, LinearMap.smulRight_apply,
    LinearEquiv.coe_coe, normalVector_selected, normalCurveKaehlerEquiv_image,
    Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one,
    normalCurveKaehlerEquiv_coordinate]
  have hn := restrictedSurfaceResidue_normalization q h g₁ g₂ k i j
  calc
    _ = -((normalCoefficientMap q h g₁ g₂ k i j (normalMultiplier g₁ g₂ i) *
        algebraMap (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j) (chartMinor ![q,h] j)) *
        determinantEquiv (restrictedSurfaceBasis q h g₁ g₂ k i j)
          (restrictedSurfaceResidueForm q h g₁ g₂ k i j)) := by ring
    _ = -1 := congrArg Neg.neg hn

/-- Where a whole-chart cofactor form is available, the contraction is
literally its negative after the actual Kähler restriction. The hypothesis
only selects that already constructed chart form; it does not assert an
adjunction or comparison. -/
theorem normalAdjunction_eq_chartForm (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (hJ : jacobianIdeal ![q,h] = ⊤) :
    normalAdjunction q h g₁ g₂ k i j (normalVector q h g₁ g₂ k i j)
        (restrictedSurfaceResidueForm q h g₁ g₂ k i j) =
      -KaehlerDifferential.map ℂ ℂ (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j)
        (CycleQ2GeometricChartKaehler.globalForm ![q,h] hJ) := by
  apply (IsUnit.smul_left_cancel (normalCurveMinor_isUnit q h g₁ g₂ k i j)).mp
  rw [normalAdjunction_residue_balance, smul_neg]
  congr 1
  have hd := congrArg (KaehlerDifferential.map ℂ ℂ (ChartRing ![q,h])
    (NormalCurvePatch q h g₁ g₂ k i j))
      (CycleQ2GeometricChartKaehler.differential_coordinate_eq_smul ![q,h] hJ j)
  simpa only [KaehlerDifferential.map_D, map_smul, algebraMap_smul,
    CycleQ2GeometricChartKaehler.coordinate, normalCoefficientMap,
    AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', polynomialToCurve_include,
    CycleQ2GeometricAffineOverlap.chartMap, Ideal.Quotient.mkₐ_eq_mk] using hd

/-- The literal cubic X₀³ multiplies the actual local surface determinant
section. This definition is on the displayed surface chart; global descent
requires the separate projective transition and covering argument. -/
def localCubicSurfaceForm (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    ⋀[NormalSurfacePatch q h g₁ g₂ k i j]^2
      (KaehlerDifferential ℂ (NormalSurfacePatch q h g₁ g₂ k i j)) :=
  algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j)
      (includeCurve (X 0 ^ 3)) •
    localSurfaceResidueForm ![surfaceEquation q h g₁ g₂ k, includeCurve h]
      (normalPolynomial q i) (includeCurve (X j))

def restrictedCubicSurfaceForm (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    ⋀[NormalCurvePatch q h g₁ g₂ k i j]^2
      (RestrictedSurfaceDifferentials q h g₁ g₂ k i j) :=
  determinantBaseChange (R := NormalCurvePatch q h g₁ g₂ k i j)
    (localSurfaceKaehlerBasis ![surfaceEquation q h g₁ g₂ k, includeCurve h]
      (normalPolynomial q i) (includeCurve (X j)))
    (localCubicSurfaceForm q h g₁ g₂ k i j)

theorem restrictedCubicSurfaceForm_eq (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) :
    restrictedCubicSurfaceForm q h g₁ g₂ k i j =
      (normalCoefficientMap q h g₁ g₂ k i j (includeCurve (X 0))) ^ 3 •
        restrictedSurfaceResidueForm q h g₁ g₂ k i j := by
  let f := determinantBaseChange (R := NormalCurvePatch q h g₁ g₂ k i j)
    (localSurfaceKaehlerBasis ![surfaceEquation q h g₁ g₂ k, includeCurve h]
      (normalPolynomial q i) (includeCurve (X j)))
  let s : NormalSurfacePatch q h g₁ g₂ k i j :=
    algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j) (includeCurve (X 0 ^ 3))
  let ω := localSurfaceResidueForm ![surfaceEquation q h g₁ g₂ k, includeCurve h]
    (normalPolynomial q i) (includeCurve (X j))
  have hc : algebraMap (NormalSurfacePatch q h g₁ g₂ k i j)
      (NormalCurvePatch q h g₁ g₂ k i j) s =
      (normalCoefficientMap q h g₁ g₂ k i j (includeCurve (X 0))) ^ 3 := by
    change algebraMap (NormalSurfacePatch q h g₁ g₂ k i j)
      (NormalCurvePatch q h g₁ g₂ k i j)
      (algebraMap SurfacePoly (NormalSurfacePatch q h g₁ g₂ k i j)
        (includeCurve (X 0 ^ 3))) = _
    rw [normalAlgebraMap_polynomial, map_pow, map_pow]
  change f (s • ω) = _ • f ω
  exact (f.map_smulₛₗ s ω).trans
    (congrArg (fun a : NormalCurvePatch q h g₁ g₂ k i j => a • f ω) hc)

private theorem linearMap_scaled_neg {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (x y : M) (a : R) (z : N)
    (hx : x = a • y) (hy : f y = -z) : f x = (-a) • z := by
  rw [hx, map_smul, hy, smul_neg, neg_smul]

/-- Contraction of the actual local cubic surface form has exactly the
cubic coefficient and negative curve orientation used by the canonical
Čech boundary construction. No scalar is chosen by nonvanishing. -/
theorem normalAdjunction_cubic_eq_chartForm (q h : AffinePoly) (g₁ g₂ k : SurfacePoly)
    (i : Fin 2) (j : Fin 3) (hJ : jacobianIdeal ![q,h] = ⊤) :
    normalAdjunction q h g₁ g₂ k i j (normalVector q h g₁ g₂ k i j)
        (restrictedCubicSurfaceForm q h g₁ g₂ k i j) =
      -((normalCoefficientMap q h g₁ g₂ k i j (includeCurve (X 0))) ^ 3) •
        KaehlerDifferential.map ℂ ℂ (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j)
          (CycleQ2GeometricChartKaehler.globalForm ![q,h] hJ) :=
  linearMap_scaled_neg
    (normalAdjunction q h g₁ g₂ k i j (normalVector q h g₁ g₂ k i j))
    (restrictedCubicSurfaceForm q h g₁ g₂ k i j)
    (restrictedSurfaceResidueForm q h g₁ g₂ k i j)
    ((normalCoefficientMap q h g₁ g₂ k i j (includeCurve (X 0))) ^ 3)
    (KaehlerDifferential.map ℂ ℂ (ChartRing ![q,h]) (NormalCurvePatch q h g₁ g₂ k i j)
      (CycleQ2GeometricChartKaehler.globalForm ![q,h] hJ))
    (restrictedCubicSurfaceForm_eq q h g₁ g₂ k i j)
    (normalAdjunction_eq_chartForm q h g₁ g₂ k i j hJ)

end CycleQ2GeometricSurfaceAdjunction

end
