import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Proposal.GeometricAffineScheme
import Proposal.GeometricDeRham

/-!
# Regular algebraic forms on the actual normal-Jacobian open

Source-only continuation. No elaboration or compilation has been run.

The regular coefficient ring is the actual localization of the protected
affine coordinate ring at its normal partial derivative, followed by any
further principal localization needed to remove a support divisor. Its
embedding in the protected function field, the four tangent derivations,
and the regularity of the protected residue are constructed below. The
regular forms are genuine exterior powers of its Kaehler module, using the
basis obtained from the explicit smooth presentation in
`GeometricAffineScheme`. Their exterior differentials form an actual
bounded cochain complex, with a canonical cochain restriction to the
existing generic-point complex and a canonical degree-four homology
identification. The associated sheaves recover these actual modules as
their global sections.

The map to the generic-point de Rham quotient is an actual algebraic map.
No injectivity of an analytic comparison and no vanishing of the residue
class is asserted by these constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

namespace CycleQ2GeometricRegularDeRham

open MvPolynomial HodgeComputer CycleQ2AffineClearing
open CycleQ2AffineHypersurface
open scoped BigOperators

abbrev BaseRing := CycleQ2GeometricAffineScheme.BaseRing
abbrev normalClass := CycleQ2GeometricAffineScheme.normalClass
abbrev OpenRing := CycleQ2GeometricAffineScheme.OpenRing
abbrev K := CycleQ2AffineDifferentials.K

local instance affineFunctionFieldIntAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

def normalJacobian : K := affineMap (pderiv 0 affineF)

theorem normalJacobian_ne_zero : normalJacobian ≠ 0 := normal_ne_zero

/-- The actual map from the normal-Jacobian localization into the original
function field. -/
def functionFieldMap : OpenRing →ₐ[ℂ] K :=
  IsLocalization.Away.liftAlgHom normalClass
    (f := IsScalarTower.toAlgHom ℂ BaseRing K)
    (isUnit_iff_ne_zero.mpr normalJacobian_ne_zero)

@[simp] theorem functionFieldMap_algebraMap (a : BaseRing) :
    functionFieldMap (algebraMap BaseRing OpenRing a) =
      algebraMap BaseRing K a :=
  IsLocalization.lift_eq _ a

theorem functionFieldMap_injective : Function.Injective functionFieldMap := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers normalClass) OpenRing functionFieldMap.toRingHom
  intro a ha
  change functionFieldMap (algebraMap BaseRing OpenRing a) = 0 at ha
  rw [functionFieldMap_algebraMap] at ha
  have hz : a = 0 :=
    IsFractionRing.injective BaseRing K (by simpa only [map_zero] using ha)
  rw [hz, map_zero]

/-- Polynomial classes regarded as regular functions on the open. -/
def polynomialValue (P : AmbientPoly 4) : OpenRing :=
  algebraMap BaseRing OpenRing (affineProjection P)

@[simp] theorem functionFieldMap_polynomialValue (P : AmbientPoly 4) :
    functionFieldMap (polynomialValue P) = affineMap P :=
  functionFieldMap_algebraMap _

def normalInverse : OpenRing :=
  IsLocalization.Away.invSelf (S := OpenRing) normalClass

theorem normal_mul_inverse :
    algebraMap BaseRing OpenRing normalClass * normalInverse = 1 :=
  IsLocalization.Away.mul_invSelf normalClass

@[simp] theorem functionFieldMap_normalInverse :
    functionFieldMap normalInverse = normalJacobian⁻¹ := by
  apply mul_left_cancel₀ normalJacobian_ne_zero
  rw [mul_inv_cancel₀ normalJacobian_ne_zero]
  have h := congrArg functionFieldMap normal_mul_inverse
  simp only [map_mul, functionFieldMap_algebraMap, map_one] at h
  change normalJacobian * functionFieldMap normalInverse = 1 at h
  exact h

/-- A concrete algebraic description of the image of the principal-open
coordinate ring in the function field. -/
def regularFunctions : Subalgebra ℂ K :=
  Algebra.adjoin ℂ (Set.range affineMap ∪ {normalJacobian⁻¹})

theorem polynomial_mem_regular (P : AmbientPoly 4) :
    affineMap P ∈ regularFunctions :=
  Algebra.subset_adjoin (Or.inl ⟨P, rfl⟩)

theorem inverse_mem_regular : normalJacobian⁻¹ ∈ regularFunctions :=
  Algebra.subset_adjoin (Or.inr rfl)

theorem functionFieldMap_mem_regular (a : OpenRing) :
    functionFieldMap a ∈ regularFunctions := by
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj normalClass a
  obtain ⟨P, rfl⟩ := affineProjection_surjective b
  have h := congrArg functionFieldMap hb
  simp only [map_mul, map_pow, functionFieldMap_algebraMap] at h
  change functionFieldMap a * normalJacobian ^ n = affineMap P at h
  have hrepr : functionFieldMap a = affineMap P * (normalJacobian⁻¹) ^ n := by
    apply mul_right_cancel₀ (pow_ne_zero n normalJacobian_ne_zero)
    rw [h]
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ normalJacobian_ne_zero, one_pow, mul_one]
  rw [hrepr]
  exact regularFunctions.mul_mem (polynomial_mem_regular P)
    (regularFunctions.pow_mem inverse_mem_regular n)

theorem functionFieldMap_range : functionFieldMap.range = regularFunctions := by
  apply le_antisymm
  · rintro z ⟨a, rfl⟩
    exact functionFieldMap_mem_regular a
  · apply Algebra.adjoin_le
    intro z hz
    rcases hz with ⟨P, rfl⟩ | hz
    · exact ⟨polynomialValue P, functionFieldMap_polynomialValue P⟩
    · have heq : z = normalJacobian⁻¹ := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨normalInverse, functionFieldMap_normalInverse⟩

theorem tangent_polynomial_mem_regular (j : Fin 4) (P : AmbientPoly 4) :
    affineTangent j (affineMap P) ∈ regularFunctions := by
  rw [affineTangent_apply, div_eq_mul_inv]
  exact regularFunctions.sub_mem (polynomial_mem_regular _)
    (regularFunctions.mul_mem
      (regularFunctions.mul_mem (polynomial_mem_regular _) inverse_mem_regular)
      (polynomial_mem_regular _))

/-- The actual four tangent derivations preserve regular functions on
this open; denominators are powers of the inverted normal Jacobian. -/
theorem tangent_mem_regular (j : Fin 4) {z : K}
    (hz : z ∈ regularFunctions) : affineTangent j z ∈ regularFunctions := by
  change z ∈ Algebra.adjoin ℂ (Set.range affineMap ∪ {normalJacobian⁻¹}) at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
      rcases hz with ⟨P, rfl⟩ | hz
      · exact tangent_polynomial_mem_regular j P
      · have heq : z = normalJacobian⁻¹ := Set.mem_singleton_iff.mp hz
        subst z
        rw [Derivation.leibniz_inv, smul_eq_mul]
        exact regularFunctions.mul_mem
          (regularFunctions.neg_mem (regularFunctions.pow_mem inverse_mem_regular 2))
          (tangent_polynomial_mem_regular j (pderiv 0 affineF))
  | algebraMap c =>
      rw [CycleQ2AffineDifferentials.tangent_complex_constant]
      exact regularFunctions.zero_mem
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact regularFunctions.add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact regularFunctions.add_mem (regularFunctions.mul_mem hx ihy)
        (regularFunctions.mul_mem hy ihx)

private theorem derivative_exists (j : Fin 4) (a : OpenRing) :
    ∃ b : OpenRing,
      functionFieldMap b = affineTangent j (functionFieldMap a) := by
  apply (AlgHom.mem_range functionFieldMap).mp
  rw [functionFieldMap_range]
  exact tangent_mem_regular j (functionFieldMap_mem_regular a)

private def derivativeValue (j : Fin 4) (a : OpenRing) : OpenRing :=
  Classical.choose (derivative_exists j a)

private theorem derivativeValue_spec (j : Fin 4) (a : OpenRing) :
    functionFieldMap (derivativeValue j a) =
      affineTangent j (functionFieldMap a) :=
  Classical.choose_spec (derivative_exists j a)

/-- A genuine derivation of the localized coordinate ring, obtained by
the proved preservation result and the injective function-field map. -/
def tangent (j : Fin 4) : Derivation ℂ OpenRing OpenRing where
  toFun := derivativeValue j
  map_add' a b := by
    apply functionFieldMap_injective
    simp only [derivativeValue_spec, map_add]
  map_smul' c a := by
    apply functionFieldMap_injective
    simp only [derivativeValue_spec, map_smul,
      CycleQ2AffineDifferentials.tangent_complex_smul, RingHom.id_apply]
  map_one_eq_zero' := by
    apply functionFieldMap_injective
    change functionFieldMap (derivativeValue j 1) = functionFieldMap 0
    simp only [derivativeValue_spec, map_one, Derivation.map_one_eq_zero, map_zero]
  leibniz' a b := by
    apply functionFieldMap_injective
    change functionFieldMap (derivativeValue j (a * b)) =
      functionFieldMap (a * derivativeValue j b + b * derivativeValue j a)
    simp only [derivativeValue_spec, smul_eq_mul, map_add, map_mul,
      Derivation.leibniz]

@[simp] theorem functionFieldMap_tangent (j : Fin 4) (a : OpenRing) :
    functionFieldMap (tangent j a) = affineTangent j (functionFieldMap a) :=
  derivativeValue_spec j a

theorem tangents_commute (i j : Fin 4) : Function.Commute (tangent i) (tangent j) := by
  intro a
  apply functionFieldMap_injective
  simp only [functionFieldMap_tangent]
  exact affineTangents_commute i j (functionFieldMap a)

/-! ## Every further principal open

The support argument may remove an additional divisor. Consequently the
construction is made for every further principal open, not only `D(g)`.
The regular modules and their differentials are defined without a
nonemptiness assumption. A nonzero further denominator is needed only
for the injective restriction into the function field.
-/

abbrev LocalRing (s : OpenRing) := Localization.Away s

theorem functionFieldMap_ne_zero {s : OpenRing} (hs : s ≠ 0) :
    functionFieldMap s ≠ 0 := by
  intro h
  apply hs
  apply functionFieldMap_injective
  simpa only [map_zero] using h

/-- Restriction of genuine regular functions on a further principal open
to the original function field. -/
def localFunctionFieldMap (s : OpenRing) (hs : s ≠ 0) :
    LocalRing s →ₐ[ℂ] K :=
  IsLocalization.Away.liftAlgHom s (f := functionFieldMap)
    (isUnit_iff_ne_zero.mpr (functionFieldMap_ne_zero hs))

@[simp] theorem localFunctionFieldMap_algebraMap (s : OpenRing) (hs : s ≠ 0)
    (a : OpenRing) :
    localFunctionFieldMap s hs (algebraMap OpenRing (LocalRing s) a) =
      functionFieldMap a :=
  IsLocalization.lift_eq _ a

theorem localFunctionFieldMap_injective (s : OpenRing) (hs : s ≠ 0) :
    Function.Injective (localFunctionFieldMap s hs) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers s) (LocalRing s) (localFunctionFieldMap s hs).toRingHom
  intro a ha
  change localFunctionFieldMap s hs
    (algebraMap OpenRing (LocalRing s) a) = 0 at ha
  rw [localFunctionFieldMap_algebraMap] at ha
  have hz : a = 0 := functionFieldMap_injective (by simpa only [map_zero] using ha)
  rw [hz, map_zero]

def localPolynomial (s : OpenRing) (P : AmbientPoly 4) : LocalRing s :=
  algebraMap OpenRing (LocalRing s) (polynomialValue P)

def localNormalInverse (s : OpenRing) : LocalRing s :=
  algebraMap OpenRing (LocalRing s) normalInverse

@[simp] theorem localFunctionFieldMap_polynomial (s : OpenRing) (hs : s ≠ 0)
    (P : AmbientPoly 4) :
    localFunctionFieldMap s hs (localPolynomial s P) = affineMap P := by
  rw [localPolynomial, localFunctionFieldMap_algebraMap,
    functionFieldMap_polynomialValue]

@[simp] theorem localFunctionFieldMap_normalInverse (s : OpenRing) (hs : s ≠ 0) :
    localFunctionFieldMap s hs (localNormalInverse s) = normalJacobian⁻¹ := by
  rw [localNormalInverse, localFunctionFieldMap_algebraMap,
    functionFieldMap_normalInverse]

abbrev Omega (s : OpenRing) := Ω[LocalRing s⁄ℂ]
abbrev d (s : OpenRing) : Derivation ℂ (LocalRing s) (Omega s) :=
  KaehlerDifferential.D ℂ (LocalRing s)
abbrev Form (s : OpenRing) (p : ℕ) := ⋀[LocalRing s]^p (Omega s)

/-- This is a basis of the actual Kähler module of the actual localized
coordinate ring, supplied by the proved submersive presentation. -/
def coordinateBasis (s : OpenRing) : Module.Basis (Fin 4) (LocalRing s) (Omega s) :=
  CycleQ2GeometricAffineScheme.furtherCoordinateBasis s

@[simp] theorem coordinateBasis_apply (s : OpenRing) (i : Fin 4) :
    coordinateBasis s i = d s (localPolynomial s (X i.succ)) :=
  CycleQ2GeometricAffineScheme.furtherCoordinateBasis_apply s i

/-- Coordinate derivations are obtained from the universal differential.
No derivative-closure property is postulated. -/
def tangentOn (s : OpenRing) (i : Fin 4) : Derivation ℂ (LocalRing s) (LocalRing s) :=
  ((coordinateBasis s).coord i).compDer (d s)

@[simp] theorem coordinateBasis_repr_d (s : OpenRing) (a : LocalRing s) (i : Fin 4) :
    (coordinateBasis s).repr (d s a) i = tangentOn s i a := rfl

/-- The field-algebra structure is kept local to pullback constructions,
so it does not replace any ambient scalar structure. -/
private def localFieldAlgebra (s : OpenRing) (hs : s ≠ 0) :
    Algebra (LocalRing s) K := (localFunctionFieldMap s hs).toRingHom.toAlgebra

private theorem localFieldTower (s : OpenRing) (hs : s ≠ 0) :
    letI := localFieldAlgebra s hs
    IsScalarTower ℂ (LocalRing s) K := by
  letI := localFieldAlgebra s hs
  constructor
  intro c a z
  simp only [Algebra.smul_def, map_mul]
  change localFunctionFieldMap s hs (c • a) * z =
    algebraMap ℂ K c * (localFunctionFieldMap s hs a * z)
  have hsmul : localFunctionFieldMap s hs (c • a) =
      c • localFunctionFieldMap s hs a :=
    (localFunctionFieldMap s hs).toLinearMap.map_smul c a
  rw [hsmul]
  simp only [Algebra.smul_def, mul_assoc]

/-- Canonical restriction on universal one-forms. -/
def oneFormPullback (s : OpenRing) (hs : s ≠ 0) :
    Omega s →ₗ[ℂ] CycleQ2AffineDifferentials.Omega := by
  letI := localFieldAlgebra s hs
  letI := localFieldTower s hs
  exact (KaehlerDifferential.map ℂ ℂ (LocalRing s) K).restrictScalars ℂ

@[simp] theorem oneFormPullback_d (s : OpenRing) (hs : s ≠ 0) (a : LocalRing s) :
    oneFormPullback s hs (d s a) =
      CycleQ2AffineDifferentials.d (localFunctionFieldMap s hs a) := by
  letI := localFieldAlgebra s hs
  letI := localFieldTower s hs
  exact KaehlerDifferential.map_D ℂ ℂ (LocalRing s) K a

@[simp] theorem oneFormPullback_smul (s : OpenRing) (hs : s ≠ 0)
    (a : LocalRing s) (ω : Omega s) :
    oneFormPullback s hs (a • ω) =
      localFunctionFieldMap s hs a • oneFormPullback s hs ω := by
  letI := localFieldAlgebra s hs
  letI := localFieldTower s hs
  change KaehlerDifferential.map ℂ ℂ (LocalRing s) K (a • ω) =
    algebraMap (LocalRing s) K a • KaehlerDifferential.map ℂ ℂ (LocalRing s) K ω
  rw [map_smul, IsScalarTower.algebraMap_smul]

@[simp] theorem oneFormPullback_coordinateBasis (s : OpenRing) (hs : s ≠ 0)
    (i : Fin 4) :
    oneFormPullback s hs (coordinateBasis s i) =
      CycleQ2AffineDifferentials.coordinateBasis i := by
  rw [coordinateBasis_apply, oneFormPullback_d, localFunctionFieldMap_polynomial,
    CycleQ2AffineDifferentials.coordinateBasis_apply] <;> rfl

theorem oneFormPullback_coordinates (s : OpenRing) (hs : s ≠ 0) (ω : Omega s) :
    oneFormPullback s hs ω = ∑ i : Fin 4,
      localFunctionFieldMap s hs ((coordinateBasis s).repr ω i) •
        CycleQ2AffineDifferentials.coordinateBasis i := by
  calc
    oneFormPullback s hs ω = oneFormPullback s hs
        (∑ i : Fin 4, (coordinateBasis s).repr ω i • coordinateBasis s i) :=
      congrArg (oneFormPullback s hs) ((coordinateBasis s).sum_repr ω).symm
    _ = _ := by
      simp only [map_sum, oneFormPullback_smul, oneFormPullback_coordinateBasis]

theorem oneFormPullback_repr (s : OpenRing) (hs : s ≠ 0) (ω : Omega s) (i : Fin 4) :
    CycleQ2AffineDifferentials.coordinateBasis.repr (oneFormPullback s hs ω) i =
      localFunctionFieldMap s hs ((coordinateBasis s).repr ω i) := by
  have hcoord (j l : Fin 4) :
      CycleQ2AffineDifferentials.coordinateBasis.repr
          (CycleQ2AffineDifferentials.coordinateDifferential j) l =
        if j = l then 1 else 0 := by
    simpa only [CycleQ2AffineDifferentials.coordinateBasis_apply] using
      CycleQ2AffineDifferentials.coordinateBasis.repr_self_apply j l
  rw [oneFormPullback_coordinates]
  simp only [map_sum, map_smul, Finsupp.sum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self_apply]
  simp [hcoord]

theorem oneFormPullback_injective (s : OpenRing) (hs : s ≠ 0) :
    Function.Injective (oneFormPullback s hs) := by
  intro ω η h
  apply (coordinateBasis s).repr.injective
  ext i
  apply localFunctionFieldMap_injective s hs
  simpa only [oneFormPullback_repr] using
    congrArg (fun z => CycleQ2AffineDifferentials.coordinateBasis.repr z i) h

/-- The canonical coordinate derivations restrict to the already fixed
function-field tangent derivations. -/
@[simp] theorem localFunctionFieldMap_tangent (s : OpenRing) (hs : s ≠ 0)
    (i : Fin 4) (a : LocalRing s) :
    localFunctionFieldMap s hs (tangentOn s i a) =
      affineTangent i (localFunctionFieldMap s hs a) := by
  have h := oneFormPullback_repr s hs (d s a) i
  rw [oneFormPullback_d, CycleQ2AffineDifferentials.coordinateBasis_repr_d,
    coordinateBasis_repr_d] at h
  exact h.symm

theorem tangentsOn_commute (s : OpenRing) (hs : s ≠ 0) (i j : Fin 4) :
    Function.Commute (tangentOn s i) (tangentOn s j) := by
  intro a
  apply localFunctionFieldMap_injective s hs
  simp only [localFunctionFieldMap_tangent]
  exact affineTangents_commute i j (localFunctionFieldMap s hs a)

/-- Restriction on genuine exterior powers, induced by the universal
alternating property of the canonical Kähler restriction. -/
def exteriorPullback (s : OpenRing) (hs : s ≠ 0) (p : ℕ) :
    Form s p →ₗ[ℂ] CycleQ2AffineExterior.Form p := by
  letI := localFieldAlgebra s hs
  letI := localFieldTower s hs
  let wedge : CycleQ2AffineDifferentials.Omega [⋀^Fin p]→ₗ[LocalRing s]
      (CycleQ2AffineExterior.Form p) :=
    { toMultilinearMap :=
        (exteriorPower.ιMulti K p).toMultilinearMap.restrictScalars (LocalRing s)
      map_eq_zero_of_eq' := (exteriorPower.ιMulti K p).map_eq_zero_of_eq' }
  exact (exteriorPower.alternatingMapLinearEquiv
    (wedge.compLinearMap (KaehlerDifferential.map ℂ ℂ (LocalRing s) K))).restrictScalars ℂ

@[simp] theorem exteriorPullback_ιMulti (s : OpenRing) (hs : s ≠ 0) (p : ℕ)
    (v : Fin p → Omega s) :
    exteriorPullback s hs p (exteriorPower.ιMulti (LocalRing s) p v) =
      exteriorPower.ιMulti K p (fun i => oneFormPullback s hs (v i)) := by
  letI := localFieldAlgebra s hs
  letI := localFieldTower s hs
  simp only [exteriorPullback, LinearMap.coe_restrictScalars,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply] <;> rfl

@[simp] theorem exteriorPullback_smul (s : OpenRing) (hs : s ≠ 0) (p : ℕ)
    (a : LocalRing s) (ω : Form s p) :
    exteriorPullback s hs p (a • ω) =
      localFunctionFieldMap s hs a • exteriorPullback s hs p ω := by
  letI := localFieldAlgebra s hs
  letI := localFieldTower s hs
  unfold exteriorPullback
  simp only [LinearMap.coe_restrictScalars, map_smul] <;>
    exact (IsScalarTower.algebraMap_smul (R := LocalRing s) (A := K) a _).symm

theorem exteriorPullback_basis (s : OpenRing) (hs : s ≠ 0) (p : ℕ)
    (i : Set.powersetCard (Fin 4) p) :
    exteriorPullback s hs p ((coordinateBasis s).exteriorPower p i) =
      CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p i := by
  simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorPullback_ιMulti]
  congr 1
  funext j
  exact oneFormPullback_coordinateBasis s hs _

theorem exteriorPullback_repr (s : OpenRing) (hs : s ≠ 0) (p : ℕ)
    (ω : Form s p) (i : Set.powersetCard (Fin 4) p) :
    (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p).repr
      (exteriorPullback s hs p ω) i =
      localFunctionFieldMap s hs (((coordinateBasis s).exteriorPower p).repr ω i) := by
  have h : exteriorPullback s hs p ω =
      ∑ j : Set.powersetCard (Fin 4) p,
        localFunctionFieldMap s hs (((coordinateBasis s).exteriorPower p).repr ω j) •
          CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p j := by
    calc
      exteriorPullback s hs p ω = exteriorPullback s hs p
          (∑ j, ((coordinateBasis s).exteriorPower p).repr ω j •
            (coordinateBasis s).exteriorPower p j) :=
        congrArg (exteriorPullback s hs p)
          (((coordinateBasis s).exteriorPower p).sum_repr ω).symm
      _ = _ := by
        simp only [map_sum, exteriorPullback_smul, exteriorPullback_basis]
  have hcoord (j l : Set.powersetCard (Fin 4) p) :
      (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p).repr
        (exteriorPower.ιMulti_family K p CycleQ2AffineDifferentials.coordinateBasis j) l =
          if j = l then 1 else 0 := by
    simpa only [exteriorPower.basis_apply] using
      (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p).repr_self_apply j l
  rw [h]
  simp only [map_sum, map_smul, Finsupp.sum_apply, Finsupp.smul_apply,
    Module.Basis.repr_self_apply]
  simp [hcoord]

theorem exteriorPullback_injective (s : OpenRing) (hs : s ≠ 0) (p : ℕ) :
    Function.Injective (exteriorPullback s hs p) := by
  intro ω η h
  apply ((coordinateBasis s).exteriorPower p).repr.injective
  ext i
  apply localFunctionFieldMap_injective s hs
  simpa only [exteriorPullback_repr] using congrArg
    (fun z => (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p).repr z i) h

/-! ## The regular exterior differentials -/

def secondBasis (s : OpenRing) : Module.Basis (Fin 6) (LocalRing s) (Form s 2) :=
  ((coordinateBasis s).exteriorPower 2).reindex
    CycleQ2AffineDeRhamComplex.pairEquiv.symm

def thirdBasis (s : OpenRing) : Module.Basis (Fin 4) (LocalRing s) (Form s 3) :=
  ((coordinateBasis s).exteriorPower 3).reindex CycleQ2AffineExterior.omitEquiv.symm

def volume (s : OpenRing) : Form s 4 :=
  (coordinateBasis s).exteriorPower 4 CycleQ2AffineExterior.topIndex

@[simp] theorem exteriorPullback_secondBasis (s : OpenRing) (hs : s ≠ 0)
    (i : Fin 6) :
    exteriorPullback s hs 2 (secondBasis s i) =
      CycleQ2AffineDeRhamComplex.secondBasis i := by
  simpa only [secondBasis, CycleQ2AffineDeRhamComplex.secondBasis,
    Module.Basis.reindex_apply, Equiv.symm_symm] using
    exteriorPullback_basis s hs 2 (CycleQ2AffineDeRhamComplex.pairEquiv i)

@[simp] theorem exteriorPullback_thirdBasis (s : OpenRing) (hs : s ≠ 0)
    (i : Fin 4) :
    exteriorPullback s hs 3 (thirdBasis s i) = CycleQ2AffineExterior.thirdBasis i := by
  simpa only [thirdBasis, CycleQ2AffineExterior.thirdBasis,
    Module.Basis.reindex_apply, Equiv.symm_symm] using
    exteriorPullback_basis s hs 3 (CycleQ2AffineExterior.omitEquiv i)

@[simp] theorem exteriorPullback_volume (s : OpenRing) (hs : s ≠ 0) :
    exteriorPullback s hs 4 (volume s) = CycleQ2AffineExterior.volume := by
  rw [volume, exteriorPullback_basis, CycleQ2AffineExterior.topBasis_apply]

theorem exteriorPullback_second_repr (s : OpenRing) (hs : s ≠ 0)
    (ω : Form s 2) (i : Fin 6) :
    CycleQ2AffineDeRhamComplex.secondBasis.repr (exteriorPullback s hs 2 ω) i =
      localFunctionFieldMap s hs ((secondBasis s).repr ω i) := by
  simpa only [secondBasis, CycleQ2AffineDeRhamComplex.secondBasis,
    Module.Basis.repr_reindex_apply, Equiv.symm_symm] using
    exteriorPullback_repr s hs 2 ω (CycleQ2AffineDeRhamComplex.pairEquiv i)

theorem exteriorPullback_third_repr (s : OpenRing) (hs : s ≠ 0)
    (ω : Form s 3) (i : Fin 4) :
    CycleQ2AffineExterior.thirdBasis.repr (exteriorPullback s hs 3 ω) i =
      localFunctionFieldMap s hs ((thirdBasis s).repr ω i) := by
  simpa only [thirdBasis, CycleQ2AffineExterior.thirdBasis,
    Module.Basis.repr_reindex_apply, Equiv.symm_symm] using
    exteriorPullback_repr s hs 3 ω (CycleQ2AffineExterior.omitEquiv i)

private def firstCoordinateDerivative (s : OpenRing) (i j : Fin 4) :
    Omega s →ₗ[ℂ] LocalRing s :=
  (tangentOn s i).toLinearMap.comp (((coordinateBasis s).coord j).restrictScalars ℂ)

private def firstCoefficients (s : OpenRing) (k : Fin 6) :
    Omega s →ₗ[ℂ] LocalRing s :=
  firstCoordinateDerivative s (CycleQ2AffineDeRhamComplex.pairLeft k)
      (CycleQ2AffineDeRhamComplex.pairRight k) -
    firstCoordinateDerivative s (CycleQ2AffineDeRhamComplex.pairRight k)
      (CycleQ2AffineDeRhamComplex.pairLeft k)

/-- Exterior differentiation of regular one-forms, in the basis of exact
coordinate one-forms of the actual smooth open. -/
def exteriorD1 (s : OpenRing) : Omega s →ₗ[ℂ] Form s 2 :=
  ((secondBasis s).equivFun.symm.toLinearMap.restrictScalars ℂ).comp
    (LinearMap.pi (firstCoefficients s))

@[simp] theorem exteriorD1_repr (s : OpenRing) (ω : Omega s) (k : Fin 6) :
    (secondBasis s).repr (exteriorD1 s ω) k =
      tangentOn s (CycleQ2AffineDeRhamComplex.pairLeft k)
          ((coordinateBasis s).repr ω (CycleQ2AffineDeRhamComplex.pairRight k)) -
        tangentOn s (CycleQ2AffineDeRhamComplex.pairRight k)
          ((coordinateBasis s).repr ω (CycleQ2AffineDeRhamComplex.pairLeft k)) := by
  change (secondBasis s).coord k ((secondBasis s).equivFun.symm _) = _
  rw [Module.Basis.coord_equivFun_symm] <;> rfl

private def secondCoordinateDerivative (s : OpenRing) (i : Fin 4) (k : Fin 6) :
    Form s 2 →ₗ[ℂ] LocalRing s :=
  (tangentOn s i).toLinearMap.comp (((secondBasis s).coord k).restrictScalars ℂ)

private def secondCoefficients (s : OpenRing) : Fin 4 → (Form s 2 →ₗ[ℂ] LocalRing s) :=
  ![secondCoordinateDerivative s 1 5 - secondCoordinateDerivative s 2 4 +
      secondCoordinateDerivative s 3 3,
    secondCoordinateDerivative s 0 5 - secondCoordinateDerivative s 2 2 +
      secondCoordinateDerivative s 3 1,
    secondCoordinateDerivative s 0 4 - secondCoordinateDerivative s 1 2 +
      secondCoordinateDerivative s 3 0,
    secondCoordinateDerivative s 0 3 - secondCoordinateDerivative s 1 1 +
      secondCoordinateDerivative s 2 0]

def exteriorD2 (s : OpenRing) : Form s 2 →ₗ[ℂ] Form s 3 :=
  ((thirdBasis s).equivFun.symm.toLinearMap.restrictScalars ℂ).comp
    (LinearMap.pi (secondCoefficients s))

@[simp] theorem exteriorD2_repr (s : OpenRing) (η : Form s 2) (i : Fin 4) :
    (thirdBasis s).repr (exteriorD2 s η) i =
      ![tangentOn s 1 ((secondBasis s).repr η 5) -
          tangentOn s 2 ((secondBasis s).repr η 4) +
          tangentOn s 3 ((secondBasis s).repr η 3),
        tangentOn s 0 ((secondBasis s).repr η 5) -
          tangentOn s 2 ((secondBasis s).repr η 2) +
          tangentOn s 3 ((secondBasis s).repr η 1),
        tangentOn s 0 ((secondBasis s).repr η 4) -
          tangentOn s 1 ((secondBasis s).repr η 2) +
          tangentOn s 3 ((secondBasis s).repr η 0),
        tangentOn s 0 ((secondBasis s).repr η 3) -
          tangentOn s 1 ((secondBasis s).repr η 1) +
          tangentOn s 2 ((secondBasis s).repr η 0)] i := by
  calc
    (thirdBasis s).repr (exteriorD2 s η) i = secondCoefficients s i η :=
      (thirdBasis s).coord_equivFun_symm i (fun j => secondCoefficients s j η)
    _ = _ := by fin_cases i <;> rfl

/-- Exterior differentiation of genuine regular three-forms. -/
def exteriorD3 (s : OpenRing) : Form s 3 →ₗ[ℂ] Form s 4 :=
  ∑ i : Fin 4,
    ((LinearMap.toSpanSingleton (LocalRing s) (Form s 4)
      ((-1 : LocalRing s) ^ i.val • volume s)).restrictScalars ℂ).comp
      ((tangentOn s i).toLinearMap.comp
        (((thirdBasis s).coord i).restrictScalars ℂ))

theorem exteriorD3_apply (s : OpenRing) (η : Form s 3) :
    exteriorD3 s η =
      (∑ i : Fin 4, (-1 : LocalRing s) ^ i.val *
        tangentOn s i ((thirdBasis s).repr η i)) • volume s := by
  simp only [exteriorD3, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, LinearMap.toSpanSingleton_apply,
    Module.Basis.coord_apply, Derivation.coeFn_coe]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    _ = (tangentOn s i ((thirdBasis s).repr η i) *
        (-1 : LocalRing s) ^ i.val) • volume s :=
      (mul_smul (tangentOn s i ((thirdBasis s).repr η i))
        ((-1 : LocalRing s) ^ i.val) (volume s)).symm
    _ = _ := by rw [mul_comm]

theorem exteriorD1_pullback (s : OpenRing) (hs : s ≠ 0) (ω : Omega s) :
    exteriorPullback s hs 2 (exteriorD1 s ω) =
      CycleQ2AffineDeRhamComplex.exteriorD1 (oneFormPullback s hs ω) := by
  apply CycleQ2AffineDeRhamComplex.secondBasis.repr.injective
  ext k
  simp only [exteriorPullback_second_repr, exteriorD1_repr, map_sub,
    localFunctionFieldMap_tangent, CycleQ2AffineDeRhamComplex.exteriorD1_repr,
    oneFormPullback_repr]

theorem exteriorD2_pullback (s : OpenRing) (hs : s ≠ 0) (η : Form s 2) :
    exteriorPullback s hs 3 (exteriorD2 s η) =
      CycleQ2AffineDeRhamComplex.exteriorD2 (exteriorPullback s hs 2 η) := by
  apply CycleQ2AffineExterior.thirdBasis.repr.injective
  ext i
  rw [exteriorPullback_third_repr, exteriorD2_repr]
  conv_rhs => rw [CycleQ2AffineDeRhamComplex.exteriorD2_repr]
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_zero', Matrix.cons_val_succ',
    map_add, map_sub, localFunctionFieldMap_tangent, exteriorPullback_second_repr]

theorem exteriorD3_pullback (s : OpenRing) (hs : s ≠ 0) (η : Form s 3) :
    exteriorPullback s hs 4 (exteriorD3 s η) =
      CycleQ2AffineExterior.exteriorD3 (exteriorPullback s hs 3 η) := by
  rw [exteriorD3_apply, exteriorPullback_smul, exteriorPullback_volume,
    CycleQ2AffineExterior.exteriorD3_apply]
  congr 1
  simp only [map_sum, map_mul, map_pow, map_neg, map_one,
    localFunctionFieldMap_tangent, exteriorPullback_third_repr]

theorem exteriorD1_d (s : OpenRing) (hs : s ≠ 0) (a : LocalRing s) :
    exteriorD1 s (d s a) = 0 := by
  apply exteriorPullback_injective s hs 2
  rw [exteriorD1_pullback, oneFormPullback_d, map_zero,
    CycleQ2AffineDeRhamComplex.exteriorD1_d]

theorem exteriorD2_exteriorD1 (s : OpenRing) (hs : s ≠ 0) (ω : Omega s) :
    exteriorD2 s (exteriorD1 s ω) = 0 := by
  apply exteriorPullback_injective s hs 3
  rw [exteriorD2_pullback, exteriorD1_pullback, map_zero,
    CycleQ2AffineDeRhamComplex.exteriorD2_exteriorD1]

theorem exteriorD3_exteriorD2 (s : OpenRing) (hs : s ≠ 0) (η : Form s 2) :
    exteriorD3 s (exteriorD2 s η) = 0 := by
  apply exteriorPullback_injective s hs 4
  rw [exteriorD3_pullback, exteriorD2_pullback, map_zero,
    CycleQ2AffineDeRhamComplex.exteriorD3_exteriorD2]

/-! ## The fixed protected residue is a regular form -/

/-- The explicit normal residue coefficient uses only polynomial classes,
the already inverted normal Jacobian, and a complex scalar. It is regular
on every further principal open. -/
def residueCoefficient (s : OpenRing) (A : AmbientPoly 4) : LocalRing s :=
  algebraMap ℂ (LocalRing s) (1 / 2 : ℂ) *
    (localPolynomial s (pderiv 0 (pderiv 0 A)) * (localNormalInverse s) ^ 3 -
      (3 * localPolynomial s (pderiv 0 A) *
          localPolynomial s (pderiv 0 (pderiv 0 affineF)) +
        localPolynomial s A *
          localPolynomial s (pderiv 0 (pderiv 0 (pderiv 0 affineF)))) *
        (localNormalInverse s) ^ 4 +
      3 * localPolynomial s A *
        (localPolynomial s (pderiv 0 (pderiv 0 affineF))) ^ 2 *
          (localNormalInverse s) ^ 5)

theorem localFunctionFieldMap_residueCoefficient (s : OpenRing) (hs : s ≠ 0)
    (A : AmbientPoly 4) :
    localFunctionFieldMap s hs (residueCoefficient s A) =
      CycleQ2AffineResidueClosure.affineNormalSource A /
        CycleQ2AffineExactness.normalDensity := by
  simp only [residueCoefficient, map_mul, map_sub, map_add, map_pow, map_ofNat,
    AlgHom.commutes, map_div₀, map_one, localFunctionFieldMap_polynomial,
    localFunctionFieldMap_normalInverse]
  unfold CycleQ2AffineResidueClosure.affineNormalSource
    SplitHigherResidue.normalSourceTwo CycleQ2AffineExactness.normalDensity normalJacobian
  field_simp [normal_ne_zero]
  <;> ring

def residueSourceForm (s : OpenRing) (A : AmbientPoly 4) : Form s 4 :=
  residueCoefficient s A • volume s

/-- The source form is tied to the actual protected rational residue by
the canonical restriction map, rather than an assumed source-binding map. -/
@[simp] theorem exteriorPullback_residueSourceForm (s : OpenRing) (hs : s ≠ 0)
    (A : AmbientPoly 4) :
    exteriorPullback s hs 4 (residueSourceForm s A) =
      CycleQ2AffineExactness.residueSourceForm A := by
  rw [residueSourceForm, exteriorPullback_smul, exteriorPullback_volume,
    localFunctionFieldMap_residueCoefficient] <;> rfl

def exactTopForms (s : OpenRing) : Submodule ℂ (Form s 4) :=
  LinearMap.range (exteriorD3 s)

/-- Degree-four cohomology of the complex of regular algebraic forms on
this affine open, presented as actual four-forms modulo actual exterior
derivatives. -/
abbrev TopDeRham (s : OpenRing) := Form s 4 ⧸ exactTopForms s

def classOf (s : OpenRing) : Form s 4 →ₗ[ℂ] TopDeRham s := (exactTopForms s).mkQ

theorem classOf_eq_zero_iff (s : OpenRing) (ω : Form s 4) :
    classOf s ω = 0 ↔ ∃ η : Form s 3, exteriorD3 s η = ω := by
  change (Submodule.Quotient.mk ω : TopDeRham s) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change ω ∈ LinearMap.range (exteriorD3 s) ↔ _
  exact LinearMap.mem_range

@[simp] theorem classOf_exteriorD3 (s : OpenRing) (η : Form s 3) :
    classOf s (exteriorD3 s η) = 0 :=
  (classOf_eq_zero_iff s _).mpr ⟨η, rfl⟩

/-- The induced map to the existing generic-point quotient. Exactness is
preserved by the proved commutation with the actual exterior derivative. -/
def toGeneric (s : OpenRing) (hs : s ≠ 0) :
    TopDeRham s →ₗ[ℂ] CycleQ2AffineTopCohomology.TopDeRham :=
  (exactTopForms s).liftQ
    (CycleQ2AffineTopCohomology.classOf.comp (exteriorPullback s hs 4)) (by
      rintro ω ⟨η, rfl⟩
      change CycleQ2AffineTopCohomology.classOf
        (exteriorPullback s hs 4 (exteriorD3 s η)) = 0
      rw [exteriorD3_pullback, CycleQ2AffineTopCohomology.classOf_exteriorD3])

@[simp] theorem toGeneric_classOf (s : OpenRing) (hs : s ≠ 0) (ω : Form s 4) :
    toGeneric s hs (classOf s ω) =
      CycleQ2AffineTopCohomology.classOf (exteriorPullback s hs 4 ω) := rfl

/-- The fixed numerator is the original `affineA`, with the original
normal residue density. -/
def residueClass (s : OpenRing) : TopDeRham s :=
  classOf s (residueSourceForm s affineA)

@[simp] theorem toGeneric_residueClass (s : OpenRing) (hs : s ≠ 0) :
    toGeneric s hs (residueClass s) =
      CycleQ2AffineTopCohomology.residueClass affineA := by
  rw [residueClass, toGeneric_classOf, exteriorPullback_residueSourceForm] <;> rfl

/-- Vanishing on any such nonempty open gives the unchanged certificate.
The geometric argument still has to produce the open and this vanishing. -/
theorem protected_certificate_of_residueClass_eq_zero (s : OpenRing) (hs : s ≠ 0)
    (h : residueClass s = 0) :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  apply CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
  apply (CycleQ2AffineTopCohomology.classOf_eq_zero_iff _).mp
  have h' := congrArg (toGeneric s hs) h
  simpa only [toGeneric_residueClass, map_zero,
    CycleQ2AffineTopCohomology.residueClass] using h'

/-! ## The actual bounded cochain complex

The maps above assemble into a Mathlib cochain complex, with the quotient
already constructed as its fourth homology. The canonical restrictions
assemble into a cochain map to the protected generic-point complex.
-/

instance formFiveSubsingleton (s : OpenRing) : Subsingleton (Form s 5) := by
  refine ⟨?_⟩
  intro η ξ
  apply ((coordinateBasis s).exteriorPower 5).repr.injective
  apply Finsupp.ext
  intro t
  have hcard : (t : Finset (Fin 4)).card ≤ 4 := by
    simpa using Finset.card_le_univ (t : Finset (Fin 4))
  have ht : (t : Finset (Fin 4)).card = 5 := t.property
  exact False.elim (by omega)

open CategoryTheory

def object (s : OpenRing) : ℕ → ModuleCat ℂ
  | 0 => ModuleCat.of ℂ (LocalRing s)
  | 1 => ModuleCat.of ℂ (Omega s)
  | 2 => ModuleCat.of ℂ (Form s 2)
  | 3 => ModuleCat.of ℂ (Form s 3)
  | 4 => ModuleCat.of ℂ (Form s 4)
  | _ + 5 => ModuleCat.of ℂ (Fin 0 → ℂ)

def differential (s : OpenRing) : (n : ℕ) → (object s n ⟶ object s (n + 1))
  | 0 => ModuleCat.ofHom (d s).toLinearMap
  | 1 => ModuleCat.ofHom (exteriorD1 s)
  | 2 => ModuleCat.ofHom (exteriorD2 s)
  | 3 => ModuleCat.ofHom (exteriorD3 s)
  | _ + 4 => 0

theorem differential_comp (s : OpenRing) (hs : s ≠ 0) (n : ℕ) :
    differential s n ≫ differential s (n + 1) = 0 := by
  cases n with
  | zero =>
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact exteriorD1_d s hs a
  | succ n =>
      cases n with
      | zero =>
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro ω
          exact exteriorD2_exteriorD1 s hs ω
      | succ n =>
          cases n with
          | zero =>
              apply ModuleCat.hom_ext
              apply LinearMap.ext
              intro η
              exact exteriorD3_exteriorD2 s hs η
          | succ n =>
              cases n with
              | zero =>
                  change ModuleCat.ofHom (exteriorD3 s) ≫ 0 = 0
                  exact CategoryTheory.Limits.comp_zero
              | succ n =>
                  change (0 : object s (n + 4) ⟶ object s (n + 5)) ≫ 0 = 0
                  exact CategoryTheory.Limits.zero_comp

def complex (s : OpenRing) (hs : s ≠ 0) : CochainComplex (ModuleCat ℂ) ℕ :=
  CochainComplex.of (object s) (differential s) (differential_comp s hs)

@[simp] theorem complex_d_succ (s : OpenRing) (hs : s ≠ 0) (n : ℕ) :
    (complex s hs).d n (n + 1) = differential s n :=
  CochainComplex.of_d (object s) (differential s) n

@[simp] theorem complex_d_three (s : OpenRing) (hs : s ≠ 0) :
    (complex s hs).d 3 4 = ModuleCat.ofHom (exteriorD3 s) := by
  simpa only [differential] using complex_d_succ s hs 3

@[simp] theorem complex_d_four (s : OpenRing) (hs : s ≠ 0) :
    (complex s hs).d 4 5 = 0 := by
  simpa only [differential] using complex_d_succ s hs 4

private def restrictionComponent (s : OpenRing) (hs : s ≠ 0) :
    (n : ℕ) → (object s n ⟶ CycleQ2GeometricDeRham.object n)
  | 0 => ModuleCat.ofHom (localFunctionFieldMap s hs).toLinearMap
  | 1 => ModuleCat.ofHom (oneFormPullback s hs)
  | 2 => ModuleCat.ofHom (exteriorPullback s hs 2)
  | 3 => ModuleCat.ofHom (exteriorPullback s hs 3)
  | 4 => ModuleCat.ofHom (exteriorPullback s hs 4)
  | _ + 5 => 0

/-- The actual algebraic restriction is a cochain map, not just a map
between unrelated top-degree vector spaces. -/
def restriction (s : OpenRing) (hs : s ≠ 0) :
    complex s hs ⟶ CycleQ2GeometricDeRham.complex :=
  CochainComplex.ofHom (restrictionComponent s hs) (by
    intro n
    rw [complex_d_succ, CycleQ2GeometricDeRham.complex_d_succ]
    cases n with
    | zero =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact (oneFormPullback_d s hs a).symm
    | succ n =>
        cases n with
        | zero =>
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro ω
            exact (exteriorD1_pullback s hs ω).symm
        | succ n =>
            cases n with
            | zero =>
                apply ModuleCat.hom_ext
                apply LinearMap.ext
                intro η
                exact (exteriorD2_pullback s hs η).symm
            | succ n =>
                cases n with
                | zero =>
                    apply ModuleCat.hom_ext
                    apply LinearMap.ext
                    intro η
                    exact (exteriorD3_pullback s hs η).symm
                | succ n =>
                    change restrictionComponent s hs (n + 4) ≫ 0 = 0 ≫ _
                    simp only [CategoryTheory.Limits.comp_zero,
                      CategoryTheory.Limits.zero_comp])

abbrev topShortComplex (s : OpenRing) (hs : s ≠ 0) : ShortComplex (ModuleCat ℂ) :=
  (complex s hs).sc' 3 4 5

def topOpcyclesIso (s : OpenRing) (hs : s ≠ 0) :
    (topShortComplex s hs).opcycles ≅ ModuleCat.of ℂ (TopDeRham s) := by
  have hf : (topShortComplex s hs).f.hom = exteriorD3 s :=
    congrArg ModuleCat.Hom.hom (complex_d_three s hs)
  have h := (topShortComplex s hs).moduleCatOpcyclesIso
  change (topShortComplex s hs).opcycles ≅
    ModuleCat.of ℂ ((Form s 4) ⧸ LinearMap.range (topShortComplex s hs).f.hom) at h
  rw [hf] at h
  exact h

def topShortHomologyIso (s : OpenRing) (hs : s ≠ 0) :
    (topShortComplex s hs).homology ≅ ModuleCat.of ℂ (TopDeRham s) :=
  (topShortComplex s hs).asIsoHomologyι (complex_d_four s hs) ≪≫ topOpcyclesIso s hs

/-- Canonical identification of the genuine regular complex's fourth
homology with the regular top-form quotient used above. -/
def homologyIso (s : OpenRing) (hs : s ≠ 0) :
    (complex s hs).homology 4 ≅ ModuleCat.of ℂ (TopDeRham s) :=
  (complex s hs).homologyIsoSc' 3 4 5
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 3 4 from rfl))
    ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 4 5 from rfl)) ≪≫
      topShortHomologyIso s hs

def homologyClassOf (s : OpenRing) (hs : s ≠ 0) :
    Form s 4 →ₗ[ℂ] (complex s hs).homology 4 :=
  (homologyIso s hs).inv.hom.comp (classOf s)

@[simp] theorem homologyIso_homologyClassOf (s : OpenRing) (hs : s ≠ 0)
    (ω : Form s 4) :
    (homologyIso s hs).hom (homologyClassOf s hs ω) = classOf s ω := by
  change (homologyIso s hs).hom ((homologyIso s hs).inv (classOf s ω)) = _
  have h := congrArg
    (fun f : ModuleCat.of ℂ (TopDeRham s) ⟶ ModuleCat.of ℂ (TopDeRham s) =>
      f (classOf s ω)) (homologyIso s hs).inv_hom_id
  change (homologyIso s hs).hom ((homologyIso s hs).inv (classOf s ω)) =
    classOf s ω at h
  exact h

/-! ## The corresponding algebraic sheaves

These are actual sheaves on the actual affine scheme. Their global
sections are canonically the regular modules used above. Exterior
differentiation is only complex-linear; no morphism of structure-sheaf
modules is incorrectly obtained by applying the tilde functor to it.
-/

def formSheaf (s : OpenRing) (p : ℕ) :
    (CycleQ2GeometricAffineScheme.furtherOpen s).Modules :=
  AlgebraicGeometry.tilde (R := CommRingCat.of (LocalRing s))
    (ModuleCat.of (LocalRing s) (Form s p))

def formGlobalSectionsIso (s : OpenRing) (p : ℕ) :
    ModuleCat.of (LocalRing s) (Form s p) ≅
      (AlgebraicGeometry.modulesSpecToSheaf.obj (formSheaf s p)).presheaf.obj (.op ⊤) :=
  AlgebraicGeometry.tilde.isoTop (R := CommRingCat.of (LocalRing s))
    (ModuleCat.of (LocalRing s) (Form s p))

end CycleQ2GeometricRegularDeRham

end
