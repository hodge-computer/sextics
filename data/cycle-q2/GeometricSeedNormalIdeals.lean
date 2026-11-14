import Proposal.GeometricCurveCoordinates
import Proposal.GeometricRelativeConormal
import Mathlib.Tactic.FinCases

/-!
# The literal curve ideal on its actual containing surface

The initial declarations are extracted from the existing seed and normal
sequence modules. Their names, polynomial definitions, quotient rings,
conormal classes, and localization algebra structures are preserved.
The final comparison identifies the actual surface-relative conormal dual
with the already defined ambient normal-map kernel.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped TensorProduct

namespace CycleQ2SeedTrace
open MvPolynomial

def originalB : WeightedPoly :=
  X 3 ^ 3 + X 2 ^ 3 + X 1 * X 2 * X 3 + X 0 * X 2 * X 3 + X 0 * X 1 ^ 2
def originalH : WeightedPoly := originalB - C Complex.I * (X 1 ^ 3 + X 3 ^ 3)
def originalK : WeightedPoly := originalB + C Complex.I * (X 1 ^ 3 + X 3 ^ 3)
def originalF1 (r : ℂ) : WeightedPoly := X 0 ^ 2 - C r * X 1 * X 3

def originalF2 : WeightedPoly := X 4 + X 2 ^ 2

end CycleQ2SeedTrace

namespace CycleQ2NormalConnecting
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta

def thetaH (θ : ℂ) : WeightedPoly := originalH+C θ*X 0^3
def thetaK (θ : ℂ) : WeightedPoly := originalK+C θ*X 0^3

theorem substitute_thetaH (θ : ℂ) : substitute (thetaH θ) = curveH θ := by
  simp [thetaH, curveH, originalH, originalB, h, b, substitute]


@[simp] theorem ambientCurveMap_f1 (r θ : ℂ) : ambientCurveMap r θ (originalF1 r)=0 := by
  change curveMap r θ (substitute (originalF1 r))=0
  have hh : substitute (originalF1 r)=relation r 0 := by
    simp [originalF1, substitute, relation]
  rw [hh, curveMap_f1]

@[simp] theorem ambientCurveMap_f2 (r θ : ℂ) : ambientCurveMap r θ originalF2=0 := by
  simp [ambientCurveMap, originalF2, substitute]

@[simp] theorem ambientCurveMap_h (r θ : ℂ) : ambientCurveMap r θ (thetaH θ)=0 := by
  change curveMap r θ (substitute (thetaH θ))=0
  rw [substitute_thetaH, curveMap_h]

def derivativeA : WeightedPoly := X 2*X 3^3*X 4

def curveEquations (r θ : ℂ) : Fin 3 → WeightedPoly :=
  ![originalF1 r, originalF2, thetaH θ]

def ambientCurveIdeal (r θ : ℂ) : Ideal WeightedPoly :=
  Ideal.span (Set.range (curveEquations r θ))

theorem curveEquation_mem (r θ : ℂ) (i : Fin 3) :
    curveEquations r θ i ∈ ambientCurveIdeal r θ := Ideal.subset_span ⟨i,rfl⟩

def conormalGenerator (r θ : ℂ) (i : Fin 3) : (ambientCurveIdeal r θ).Cotangent :=
  (ambientCurveIdeal r θ).toCotangent ⟨curveEquations r θ i,curveEquation_mem r θ i⟩

def overlapAmbient (r θ : ℂ) : WeightedPoly →+* Overlap r θ :=
  (algebraMap (CurveRing r θ) (Overlap r θ)).comp (ambientCurveMap r θ)

def firstOpenAmbient (r θ : ℂ) : WeightedPoly →+* FirstOpen r θ :=
  (algebraMap (CurveRing r θ) (FirstOpen r θ)).comp (ambientCurveMap r θ)
def secondOpenAmbient (r θ : ℂ) : WeightedPoly →+* SecondOpen r θ :=
  (algebraMap (CurveRing r θ) (SecondOpen r θ)).comp (ambientCurveMap r θ)

/-- The parameter-dependent hypersurface equation actually used by the
Segre incidence presentation. -/
def actualSeedEquation (r θ : ℂ) : WeightedPoly :=
  originalF1 r*originalG1 r+originalF2*originalG2+thetaH θ*thetaK θ

/-- Literal ideal membership for the parameter-dependent equation. -/
theorem actualSeedEquation_mem (r θ : ℂ) :
    actualSeedEquation r θ ∈ ambientCurveIdeal r θ := by
  exact Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 0))
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 1)))
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 2))

/-- The actual normal equation is the class of the actual incidence
hypersurface in the curve ideal modulo its square. -/
theorem actual_conormal_relation (r θ : ℂ) :
    (ambientCurveIdeal r θ).toCotangent
        ⟨actualSeedEquation r θ,actualSeedEquation_mem r θ⟩ =
      originalG1 r • conormalGenerator r θ 0+
      originalG2 • conormalGenerator r θ 1+thetaK θ • conormalGenerator r θ 2 := by
  have hh :
      (⟨actualSeedEquation r θ,actualSeedEquation_mem r θ⟩ : ambientCurveIdeal r θ) =
      originalG1 r • ⟨curveEquations r θ 0,curveEquation_mem r θ 0⟩+
      originalG2 • ⟨curveEquations r θ 1,curveEquation_mem r θ 1⟩+
      thetaK θ • ⟨curveEquations r θ 2,curveEquation_mem r θ 2⟩ := by
    apply Subtype.ext
    change actualSeedEquation r θ = originalG1 r*originalF1 r+originalG2*originalF2+
      thetaK θ*thetaH θ
    unfold actualSeedEquation
    ring
  rw [hh,map_add,map_add,map_smul,map_smul,map_smul]
  rfl

end CycleQ2NormalConnecting

namespace CycleQ2ConormalJacobian
open CycleQ2SeedTrace CycleQ2NormalConnecting

abbrev P := WeightedPoly

def surfaceEquations (r θ : ℂ) : Fin 2 → P := ![actualSeedEquation r θ,thetaH θ]
def surfaceIdeal (r θ : ℂ) : Ideal P := Ideal.span (Set.range (surfaceEquations r θ))

theorem surfaceIdeal_le_curveIdeal (r θ : ℂ) : surfaceIdeal r θ≤ambientCurveIdeal r θ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨j,rfl⟩
  fin_cases j
  · exact actualSeedEquation_mem r θ
  · exact curveEquation_mem r θ 2

end CycleQ2ConormalJacobian

namespace CycleQ2NaturalNormalMap
open CycleQ2ConormalJacobian CycleQ2NormalConnecting CycleQ2SeedTrace

/-- The literal natural map J/J^2 -> I/I^2, with J=(F,h), I=(f1,f2,h).
The algebra homomorphism is the identity of the actual polynomial ring. -/
def naturalCotangentMap (r θ : ℂ) :
    (surfaceIdeal r θ).Cotangent →ₗ[P] (ambientCurveIdeal r θ).Cotangent :=
  Ideal.mapCotangent (surfaceIdeal r θ) (ambientCurveIdeal r θ)
    (AlgHom.id P P) (by
      intro x hx
      change x ∈ ambientCurveIdeal r θ
      exact surfaceIdeal_le_curveIdeal r θ hx)

/-- This is the identity-homomorphism instance of
Ideal.mapCotangent_toCotangent, whose proof in mathlib is also rfl. -/
@[simp] theorem naturalCotangentMap_toCotangent (r θ : ℂ)
    (x : surfaceIdeal r θ) :
    naturalCotangentMap r θ ((surfaceIdeal r θ).toCotangent x) =
      (ambientCurveIdeal r θ).toCotangent
        ⟨(x : P), surfaceIdeal_le_curveIdeal r θ x.property⟩ := by
  rfl

section ScalarExtension

variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

/-- Scalar extension of the actual natural cotangent map. -/
def baseChangedNaturalCotangentMap (r θ : ℂ) :
    S ⊗[P] (surfaceIdeal r θ).Cotangent →ₗ[S]
      S ⊗[P] (ambientCurveIdeal r θ).Cotangent :=
  (naturalCotangentMap r θ).baseChange S

@[simp] theorem baseChangedNaturalCotangentMap_toCotangent (r θ : ℂ)
    (s : S) (x : surfaceIdeal r θ) :
    baseChangedNaturalCotangentMap (S := S) r θ
        (s ⊗ₜ[P] (surfaceIdeal r θ).toCotangent x) =
      s ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent
        ⟨(x : P), surfaceIdeal_le_curveIdeal r θ x.property⟩ := by
  simp only [baseChangedNaturalCotangentMap, LinearMap.baseChange_tmul,
    naturalCotangentMap_toCotangent]

/-- The normal map is dualization of the genuine, base-changed natural
cotangent map. No choice of equation coordinates enters this definition. -/
def naturalNormalMap (r θ : ℂ) :
    (S ⊗[P] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S) →ₗ[S]
      (S ⊗[P] (surfaceIdeal r θ).Cotangent →ₗ[S] S) :=
  (baseChangedNaturalCotangentMap (S := S) r θ).dualMap

@[simp] theorem naturalNormalMap_toCotangent (r θ : ℂ)
    (φ : S ⊗[P] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S)
    (s : S) (x : surfaceIdeal r θ) :
    naturalNormalMap r θ φ (s ⊗ₜ[P] (surfaceIdeal r θ).toCotangent x) =
      φ (s ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent
        ⟨(x : P), surfaceIdeal_le_curveIdeal r θ x.property⟩) := by
  simp only [naturalNormalMap, LinearMap.dualMap_apply,
    baseChangedNaturalCotangentMap_toCotangent]

end ScalarExtension
end CycleQ2NaturalNormalMap

namespace CycleQ2ActualNormalCech
open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap CycleQ2NormalConnecting
  CycleQ2SeedTrace CycleQ2SeedCechTheta

/-- The literal five-variable curve map, as a complex algebra homomorphism. -/
def ambientCurveAlg (r θ : ℂ) : P →ₐ[ℂ] CurveRing r θ :=
  (Ideal.Quotient.mkₐ ℂ (CycleQ2SeedCechTheta.curveIdeal r θ)).comp substitute

@[simp] theorem ambientCurveAlg_apply (r θ : ℂ) (p : P) :
    ambientCurveAlg r θ p = ambientCurveMap r θ p := rfl

/-- Cache the standard complex actions before introducing the polynomial
algebra structures on the reducible localization aliases. -/
instance (priority := 2000) firstComplexAlgebra (r θ : ℂ) : Algebra ℂ (FirstOpen r θ) :=
  inferInstance
instance (priority := 2000) firstComplexSMul (r θ : ℂ) : SMul ℂ (FirstOpen r θ) :=
  (firstComplexAlgebra r θ).toSMul
instance (priority := 2000) firstComplexModule (r θ : ℂ) : Module ℂ (FirstOpen r θ) :=
  @Algebra.toModule ℂ (FirstOpen r θ) _ _ (firstComplexAlgebra r θ)

instance (priority := 2000) secondComplexAlgebra (r θ : ℂ) : Algebra ℂ (SecondOpen r θ) :=
  inferInstance
instance (priority := 2000) secondComplexSMul (r θ : ℂ) : SMul ℂ (SecondOpen r θ) :=
  (secondComplexAlgebra r θ).toSMul
instance (priority := 2000) secondComplexModule (r θ : ℂ) : Module ℂ (SecondOpen r θ) :=
  @Algebra.toModule ℂ (SecondOpen r θ) _ _ (secondComplexAlgebra r θ)

instance (priority := 2000) overlapComplexAlgebra (r θ : ℂ) : Algebra ℂ (Overlap r θ) :=
  inferInstance
instance (priority := 2000) overlapComplexSMul (r θ : ℂ) : SMul ℂ (Overlap r θ) :=
  (overlapComplexAlgebra r θ).toSMul
instance (priority := 2000) overlapComplexModule (r θ : ℂ) : Module ℂ (Overlap r θ) :=
  @Algebra.toModule ℂ (Overlap r θ) _ _ (overlapComplexAlgebra r θ)

def firstAmbientAlg (r θ : ℂ) : P →ₐ[ℂ] FirstOpen r θ :=
  (IsScalarTower.toAlgHom ℂ (CurveRing r θ) (FirstOpen r θ)).comp (ambientCurveAlg r θ)

def secondAmbientAlg (r θ : ℂ) : P →ₐ[ℂ] SecondOpen r θ :=
  (IsScalarTower.toAlgHom ℂ (CurveRing r θ) (SecondOpen r θ)).comp (ambientCurveAlg r θ)

def overlapAmbientAlg (r θ : ℂ) : P →ₐ[ℂ] Overlap r θ :=
  (IsScalarTower.toAlgHom ℂ (CurveRing r θ) (Overlap r θ)).comp (ambientCurveAlg r θ)

instance (priority := 2000) firstAlgebra (r θ : ℂ) : Algebra P (FirstOpen r θ) :=
  (firstAmbientAlg r θ).toRingHom.toAlgebra
instance (priority := 2000) secondAlgebra (r θ : ℂ) : Algebra P (SecondOpen r θ) :=
  (secondAmbientAlg r θ).toRingHom.toAlgebra
instance (priority := 2000) overlapAlgebra (r θ : ℂ) : Algebra P (Overlap r θ) :=
  (overlapAmbientAlg r θ).toRingHom.toAlgebra

/-- These instances use exactly the actions of the preceding algebras;
they prevent expensive rediscovery through localization and quotient types. -/
instance (priority := 2000) firstPolynomialSMul (r θ : ℂ) : SMul P (FirstOpen r θ) :=
  (firstAlgebra r θ).toSMul
instance (priority := 2000) firstPolynomialModule (r θ : ℂ) : Module P (FirstOpen r θ) :=
  @Algebra.toModule P (FirstOpen r θ) _ _ (firstAlgebra r θ)

instance (priority := 2000) secondPolynomialSMul (r θ : ℂ) : SMul P (SecondOpen r θ) :=
  (secondAlgebra r θ).toSMul
instance (priority := 2000) secondPolynomialModule (r θ : ℂ) : Module P (SecondOpen r θ) :=
  @Algebra.toModule P (SecondOpen r θ) _ _ (secondAlgebra r θ)

instance (priority := 2000) overlapPolynomialSMul (r θ : ℂ) : SMul P (Overlap r θ) :=
  (overlapAlgebra r θ).toSMul
instance (priority := 2000) overlapPolynomialModule (r θ : ℂ) : Module P (Overlap r θ) :=
  @Algebra.toModule P (Overlap r θ) _ _ (overlapAlgebra r θ)

instance firstTower (r θ : ℂ) : IsScalarTower ℂ P (FirstOpen r θ) :=
  IsScalarTower.of_algHom (firstAmbientAlg r θ)
instance secondTower (r θ : ℂ) : IsScalarTower ℂ P (SecondOpen r θ) :=
  IsScalarTower.of_algHom (secondAmbientAlg r θ)
instance overlapTower (r θ : ℂ) : IsScalarTower ℂ P (Overlap r θ) :=
  IsScalarTower.of_algHom (overlapAmbientAlg r θ)

@[simp] theorem first_algebraMap (r θ : ℂ) (p : P) :
    algebraMap P (FirstOpen r θ) p = firstOpenAmbient r θ p := rfl
@[simp] theorem second_algebraMap (r θ : ℂ) (p : P) :
    algebraMap P (SecondOpen r θ) p = secondOpenAmbient r θ p := rfl
@[simp] theorem overlap_algebraMap (r θ : ℂ) (p : P) :
    algebraMap P (Overlap r θ) p = overlapAmbient r θ p := rfl

/-- No new annihilation hypothesis is needed: the actual substitution map
kills the three literal curve equations. -/
theorem ambientCurveMap_kills (r θ : ℂ) (p : P)
    (hp : p ∈ ambientCurveIdeal r θ) : ambientCurveMap r θ p = 0 := by
  have hi : ambientCurveIdeal r θ ≤ RingHom.ker (ambientCurveMap r θ) := by
    rw [ambientCurveIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i <;>
      simp [curveEquations, RingHom.mem_ker]
  exact hi hp

theorem first_annihilates (r θ : ℂ) :
    ∀ p ∈ ambientCurveIdeal r θ, algebraMap P (FirstOpen r θ) p = 0 := by
  intro p hp
  change algebraMap (CurveRing r θ) (FirstOpen r θ) (ambientCurveMap r θ p) = 0
  rw [ambientCurveMap_kills r θ p hp, map_zero]

theorem second_annihilates (r θ : ℂ) :
    ∀ p ∈ ambientCurveIdeal r θ, algebraMap P (SecondOpen r θ) p = 0 := by
  intro p hp
  change algebraMap (CurveRing r θ) (SecondOpen r θ) (ambientCurveMap r θ p) = 0
  rw [ambientCurveMap_kills r θ p hp, map_zero]

theorem overlap_annihilates (r θ : ℂ) :
    ∀ p ∈ ambientCurveIdeal r θ, algebraMap P (Overlap r θ) p = 0 := by
  intro p hp
  change algebraMap (CurveRing r θ) (Overlap r θ) (ambientCurveMap r θ p) = 0
  rw [ambientCurveMap_kills r θ p hp, map_zero]

/-- The existing restriction ring maps respect the literal polynomial action. -/
def firstRestrictionAlg (r θ : ℂ) : FirstOpen r θ →ₐ[P] Overlap r θ where
  __ := firstRestriction r θ
  commutes' p := by
    change firstRestriction r θ (firstOpenAmbient r θ p) = overlapAmbient r θ p
    exact IsLocalization.Away.awayToAwayRight_eq _ _ _

def secondRestrictionAlg (r θ : ℂ) : SecondOpen r θ →ₐ[P] Overlap r θ where
  __ := secondRestriction r θ
  commutes' p := by
    change secondRestriction r θ (secondOpenAmbient r θ p) = overlapAmbient r θ p
    exact IsLocalization.Away.awayToAwayLeft_eq _ _ _

@[simp] theorem firstRestrictionAlg_apply (r θ : ℂ) (x : FirstOpen r θ) :
    firstRestrictionAlg r θ x = firstRestriction r θ x := rfl
@[simp] theorem secondRestrictionAlg_apply (r θ : ℂ) (x : SecondOpen r θ) :
    secondRestrictionAlg r θ x = secondRestriction r θ x := rfl

end CycleQ2ActualNormalCech

namespace CycleQ2GeometricSeedNormalIdeals

open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap CycleQ2NormalConnecting
  CycleQ2SeedTrace CycleQ2ActualNormalCech

/-- The actual containing surface cone, with both literal equations imposed. -/
abbrev SurfaceRing (r θ : ℂ) := P ⧸ surfaceIdeal r θ

/-- The actual ideal of the curve in that surface. -/
def curveIdealOnSurface (r θ : ℂ) : Ideal (SurfaceRing r θ) :=
  CycleQ2GeometricRelativeConormal.relativeIdeal (surfaceIdeal r θ) (ambientCurveIdeal r θ)

section SurfaceScalars

variable {S : Type*} [CommRing S] [Algebra P S]

/-- An actual curve-chart coefficient map factors through the actual surface quotient. -/
def surfaceMap (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap P S p = 0) :
    SurfaceRing r θ →+* S :=
  Ideal.Quotient.lift (surfaceIdeal r θ) (algebraMap P S)
    (fun p hp => hI p (surfaceIdeal_le_curveIdeal r θ hp))

@[simp] theorem surfaceMap_mk (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap P S p = 0) (p : P) :
    surfaceMap r θ hI (Ideal.Quotient.mk (surfaceIdeal r θ) p) = algebraMap P S p := rfl

end SurfaceScalars

instance firstSurfaceAlgebra (r θ : ℂ) : Algebra (SurfaceRing r θ) (FirstOpen r θ) :=
  (surfaceMap r θ (first_annihilates r θ)).toAlgebra

instance secondSurfaceAlgebra (r θ : ℂ) : Algebra (SurfaceRing r θ) (SecondOpen r θ) :=
  (surfaceMap r θ (second_annihilates r θ)).toAlgebra

instance overlapSurfaceAlgebra (r θ : ℂ) : Algebra (SurfaceRing r θ) (Overlap r θ) :=
  (surfaceMap r θ (overlap_annihilates r θ)).toAlgebra

instance firstSurfaceTower (r θ : ℂ) : IsScalarTower P (SurfaceRing r θ) (FirstOpen r θ) where
  smul_assoc p a s := by
    change surfaceMap r θ (first_annihilates r θ)
        ((Ideal.Quotient.mk (surfaceIdeal r θ) p) * a) * s =
      algebraMap P (FirstOpen r θ) p * (surfaceMap r θ (first_annihilates r θ) a * s)
    rw [map_mul, surfaceMap_mk, mul_assoc]

instance secondSurfaceTower (r θ : ℂ) : IsScalarTower P (SurfaceRing r θ) (SecondOpen r θ) where
  smul_assoc p a s := by
    change surfaceMap r θ (second_annihilates r θ)
        ((Ideal.Quotient.mk (surfaceIdeal r θ) p) * a) * s =
      algebraMap P (SecondOpen r θ) p * (surfaceMap r θ (second_annihilates r θ) a * s)
    rw [map_mul, surfaceMap_mk, mul_assoc]

instance overlapSurfaceTower (r θ : ℂ) : IsScalarTower P (SurfaceRing r θ) (Overlap r θ) where
  smul_assoc p a s := by
    change surfaceMap r θ (overlap_annihilates r θ)
        ((Ideal.Quotient.mk (surfaceIdeal r θ) p) * a) * s =
      algebraMap P (Overlap r θ) p * (surfaceMap r θ (overlap_annihilates r θ) a * s)
    rw [map_mul, surfaceMap_mk, mul_assoc]

section NormalComparison

variable (r θ : ℂ) (S : Type*) [CommRing S] [Algebra P S]
  [Algebra (SurfaceRing r θ) S] [IsScalarTower P (SurfaceRing r θ) S]

/-- The normal module of the curve inside its actual surface, restricted to `S`. -/
abbrev RelativeNormal := S ⊗[SurfaceRing r θ] (curveIdealOnSurface r θ).Cotangent →ₗ[S] S

/-- The actual equation class in the relative curve ideal, after restriction to `S`. -/
def relativeEquationClass (i : Fin 3) :
    S ⊗[SurfaceRing r θ] (curveIdealOnSurface r θ).Cotangent :=
  (1 : S) ⊗ₜ[SurfaceRing r θ] (curveIdealOnSurface r θ).toCotangent
    ⟨Ideal.Quotient.mk (surfaceIdeal r θ) (curveEquations r θ i),
      Ideal.mem_map_of_mem _ (curveEquation_mem r θ i)⟩

/-- The existing ambient normal-map kernel is the actual surface-relative normal module.
The curve inclusion is proved for the literal equations at all parameter values. -/
def normalModuleEquiv : RelativeNormal r θ S ≃ₗ[S]
    LinearMap.ker (naturalNormalMap (S := S) r θ) :=
  CycleQ2GeometricRelativeConormal.relativeNormalEquiv
    (surfaceIdeal r θ) (ambientCurveIdeal r θ) S (surfaceIdeal_le_curveIdeal r θ)

/-- This comparison preserves each literal equation value; it does not choose a normal vector. -/
theorem normalModuleEquiv_symm_equation
    (φ : LinearMap.ker (naturalNormalMap (S := S) r θ)) (i : Fin 3) :
    (normalModuleEquiv r θ S).symm φ (relativeEquationClass r θ S i) =
      φ.val ((1 : S) ⊗ₜ[P] conormalGenerator r θ i) :=
  CycleQ2GeometricRelativeConormal.relativeNormalEquiv_symm_toCotangent
    (surfaceIdeal r θ) (ambientCurveIdeal r θ) S (surfaceIdeal_le_curveIdeal r θ)
    φ 1 ⟨curveEquations r θ i, curveEquation_mem r θ i⟩

end NormalComparison

/-- On the actual first localization there are no scalar-factorization hypotheses left. -/
def firstNormalModuleEquiv (r θ : ℂ) : RelativeNormal r θ (FirstOpen r θ) ≃ₗ[FirstOpen r θ]
    LinearMap.ker (naturalNormalMap (S := FirstOpen r θ) r θ) :=
  normalModuleEquiv r θ (FirstOpen r θ)

/-- The analogous comparison on the actual second localization. -/
def secondNormalModuleEquiv (r θ : ℂ) : RelativeNormal r θ (SecondOpen r θ) ≃ₗ[SecondOpen r θ]
    LinearMap.ker (naturalNormalMap (S := SecondOpen r θ) r θ) :=
  normalModuleEquiv r θ (SecondOpen r θ)

/-- The actual overlap comparison used for the normal connecting cochain. -/
def overlapNormalModuleEquiv (r θ : ℂ) : RelativeNormal r θ (Overlap r θ) ≃ₗ[Overlap r θ]
    LinearMap.ker (naturalNormalMap (S := Overlap r θ) r θ) :=
  normalModuleEquiv r θ (Overlap r θ)

/-- In particular the comparison applies at the same literal `(57,1)` seed as the
proved incidence-rank and ambient-test nonvanishing statements. -/
theorem literal_overlap_equation
    (φ : LinearMap.ker (naturalNormalMap (S := Overlap 57 1) 57 1)) (i : Fin 3) :
    (overlapNormalModuleEquiv 57 1).symm φ (relativeEquationClass 57 1 (Overlap 57 1) i) =
      φ.val ((1 : Overlap 57 1) ⊗ₜ[P] conormalGenerator 57 1 i) :=
  normalModuleEquiv_symm_equation 57 1 (Overlap 57 1) φ i

end CycleQ2GeometricSeedNormalIdeals
