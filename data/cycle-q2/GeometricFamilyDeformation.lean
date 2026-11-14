import Proposal.GeometricSquareZeroProjectors
import Proposal.GeometricNormalizedCartierClass
import Proposal.GeometricSeedConormalBases
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.Module

section SourceUniversalSurfaceFirstOrder

/-! The actual normalized complete-intersection family has a faithful
first-order deformation by F - εA with h fixed.  Regularity is proved
from the original monic leading equations, rather than assumed. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricUniversalSurfaceFirstOrder

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2SeedQuotientFiniteFree
  CycleQ2UniversalSurface CycleQ2GeometricSurfaceFirstOrder

variable (R : Type*) [CommRing R]

def cubicIdeal (hcoeff : FullCubicTailIndex → R) : Ideal (MvPolynomial (Fin 5) R) :=
  Ideal.span {normalizedFullCubic hcoeff}

abbrev CubicQuotient (hcoeff : FullCubicTailIndex → R) :=
  MvPolynomial (Fin 5) R ⧸ cubicIdeal R hcoeff

-- Fix the regular left and right actions before constructing the dual
-- numbers; the quotient also carries several inherited scalar actions.
local instance cubicSelfModule (hcoeff : FullCubicTailIndex → R) :
    Module (CubicQuotient R hcoeff) (CubicQuotient R hcoeff) :=
  Semiring.toModule

local instance cubicOppositeModule (hcoeff : FullCubicTailIndex → R) :
    Module (CubicQuotient R hcoeff)ᵐᵒᵖ (CubicQuotient R hcoeff) :=
  Semiring.toOppositeModule

local instance cubicCentralScalar (hcoeff : FullCubicTailIndex → R) :
    IsCentralScalar (CubicQuotient R hcoeff) (CubicQuotient R hcoeff) where
  op_smul_eq_smul x y := by
    change y * x = x * y
    exact mul_comm y x

local instance cubicSmulCommClass (hcoeff : FullCubicTailIndex → R) :
    SMulCommClass (CubicQuotient R hcoeff) (CubicQuotient R hcoeff)ᵐᵒᵖ
      (CubicQuotient R hcoeff) where
  smul_comm x y z := by
    change x * (z * MulOpposite.unop y) = (x * z) * MulOpposite.unop y
    exact (mul_assoc x z (MulOpposite.unop y)).symm

def sexticClass (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) : CubicQuotient R hcoeff :=
  Ideal.Quotient.mk (cubicIdeal R hcoeff) (normalizedFullSextic Fcoeff)

def testClass (hcoeff : FullCubicTailIndex → R) (A : MvPolynomial (Fin 5) R) :
    CubicQuotient R hcoeff := Ideal.Quotient.mk (cubicIdeal R hcoeff) A

/-- The actual sextic can be cancelled modulo the actual cubic over any
nontrivial coefficient ring, including rings with zero divisors. -/
theorem normalized_sextic_regular_mod_cubic [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : MvPolynomial (Fin 5) R)
    (hp : normalizedFullSextic Fcoeff * p ∈ cubicIdeal R hcoeff) :
    p ∈ cubicIdeal R hcoeff := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hp
  have hn : nestedSextic R Fcoeff * regroup R p ∈
      Ideal.span ({nestedCubic R hcoeff} : Set (Nested R)) := by
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨regroup R b, ?_⟩
    have hm := congrArg (regroup R) hb
    simpa only [map_mul, regroup_cubic, regroup_sextic] using hm
  have hc := CycleQ2MonicRegular.pair_regular_mod_first nestedOrder
    (nestedCubic_leading R hcoeff).2 (nestedSextic_leading R Fcoeff).2
    (nested_coprime R hcoeff Fcoeff) (regroup R p) hn
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hc
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨(regroup R).symm b, ?_⟩
  apply (regroup R).injective
  simpa only [map_mul, AlgEquiv.apply_symm_apply, regroup_cubic] using hb

theorem sexticClass_regular [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ∀ x : CubicQuotient R hcoeff, sexticClass R hcoeff Fcoeff * x = 0 → x = 0 := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  intro hp
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply normalized_sextic_regular_mod_cubic R hcoeff Fcoeff p
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk (cubicIdeal R hcoeff) (normalizedFullSextic Fcoeff) *
    Ideal.Quotient.mk (cubicIdeal R hcoeff) p = 0 at hp
  simpa only [map_mul] using hp

private theorem mapped_sextic_ideal
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    (Ideal.span ({normalizedFullSextic Fcoeff} : Set (MvPolynomial (Fin 5) R))).map
        (Ideal.Quotient.mkₐ R (cubicIdeal R hcoeff)) =
      Ideal.span ({sexticClass R hcoeff Fcoeff} : Set (CubicQuotient R hcoeff)) := by
  simp only [Ideal.map_span, Set.image_singleton]
  rfl

private theorem two_ideals_eq
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    cubicIdeal R hcoeff ⊔ Ideal.span ({normalizedFullSextic Fcoeff} : Set (MvPolynomial (Fin 5) R)) =
      surfaceIdeal R hcoeff Fcoeff := by
  exact (Ideal.span_insert _ _).symm

/-- The closed fibre is the original universal surface, with all five
polynomial coordinates fixed by the comparison. -/
def closedSurfaceEquiv
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Closed (sexticClass R hcoeff Fcoeff) ≃ₐ[R] SurfaceRing R hcoeff Fcoeff :=
  ((Ideal.quotientEquivAlgOfEq R (mapped_sextic_ideal R hcoeff Fcoeff).symm).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ R (cubicIdeal R hcoeff)
      (Ideal.span ({normalizedFullSextic Fcoeff} : Set (MvPolynomial (Fin 5) R))))).trans
    (Ideal.quotientEquivAlgOfEq R (two_ideals_eq R hcoeff Fcoeff))

@[simp] theorem closedSurfaceEquiv_mk
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : MvPolynomial (Fin 5) R) :
    closedSurfaceEquiv R hcoeff Fcoeff
      (Ideal.Quotient.mk (Ideal.span ({sexticClass R hcoeff Fcoeff} :
        Set (CubicQuotient R hcoeff)))
        (Ideal.Quotient.mk (cubicIdeal R hcoeff) p)) =
      Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff) p := rfl

@[simp] theorem closedSurfaceEquiv_symm_mk
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : MvPolynomial (Fin 5) R) :
    (closedSurfaceEquiv R hcoeff Fcoeff).symm
      (Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff) p) =
      Ideal.Quotient.mk (Ideal.span ({sexticClass R hcoeff Fcoeff} :
        Set (CubicQuotient R hcoeff)))
        (Ideal.Quotient.mk (cubicIdeal R hcoeff) p) := rfl

/-- This is the quotient by h and then F - εA, not a chosen extension of
the surface as an abstract module. -/
abbrev SurfaceDeformation
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) :=
  Deformation (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)

local instance surfaceDeformationModule
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) :
    Module R (SurfaceDeformation R hcoeff Fcoeff A) :=
  @Algebra.toModule R (SurfaceDeformation R hcoeff Fcoeff A)
    (inferInstance : CommSemiring R)
    (inferInstance : Semiring (SurfaceDeformation R hcoeff Fcoeff A)) inferInstance

local instance surfaceDeformationCubicModule
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) :
    Module (CubicQuotient R hcoeff) (SurfaceDeformation R hcoeff Fcoeff A) :=
  @Algebra.toModule (CubicQuotient R hcoeff) (SurfaceDeformation R hcoeff Fcoeff A)
    (inferInstance : CommSemiring (CubicQuotient R hcoeff))
    (inferInstance : Semiring (SurfaceDeformation R hcoeff Fcoeff A)) inferInstance

def surfaceReduction
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) :
    SurfaceDeformation R hcoeff Fcoeff A →ₐ[R] SurfaceRing R hcoeff Fcoeff :=
  (closedSurfaceEquiv R hcoeff Fcoeff).toAlgHom.comp
    ((reduction (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)).restrictScalars R)

def surfaceEpsilon
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) :
    SurfaceRing R hcoeff Fcoeff →ₗ[R] SurfaceDeformation R hcoeff Fcoeff A :=
  ((epsilon (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)).restrictScalars R).comp
    (closedSurfaceEquiv R hcoeff Fcoeff).symm.toLinearEquiv.toLinearMap

@[simp] theorem surfaceReduction_mk
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A p q : MvPolynomial (Fin 5) R) :
    surfaceReduction R hcoeff Fcoeff A
      (Ideal.Quotient.mk (deformationIdeal (sexticClass R hcoeff Fcoeff)
        (testClass R hcoeff A))
        (Ideal.Quotient.mk (cubicIdeal R hcoeff) p,
          Ideal.Quotient.mk (cubicIdeal R hcoeff) q)) =
      Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff) p := rfl

@[simp] theorem surfaceEpsilon_mk
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A p : MvPolynomial (Fin 5) R) :
    surfaceEpsilon R hcoeff Fcoeff A
      (Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff) p) =
      Ideal.Quotient.mk (deformationIdeal (sexticClass R hcoeff Fcoeff)
        (testClass R hcoeff A))
        (TrivSqZeroExt.inr (Ideal.Quotient.mk (cubicIdeal R hcoeff) p)) := rfl

theorem surfaceEpsilon_injective [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) : Function.Injective (surfaceEpsilon R hcoeff Fcoeff A) :=
  (epsilon_injective _ _ (sexticClass_regular R hcoeff Fcoeff)).comp
    (closedSurfaceEquiv R hcoeff Fcoeff).symm.injective

theorem surfaceReduction_eq_zero_iff
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) (z : SurfaceDeformation R hcoeff Fcoeff A) :
    surfaceReduction R hcoeff Fcoeff A z = 0 ↔
      ∃ x : SurfaceRing R hcoeff Fcoeff, surfaceEpsilon R hcoeff Fcoeff A x = z := by
  have hr : surfaceReduction R hcoeff Fcoeff A z = 0 ↔
      reduction (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A) z = 0 :=
    (closedSurfaceEquiv R hcoeff Fcoeff).map_eq_zero_iff
  rw [hr, reduction_eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨closedSurfaceEquiv R hcoeff Fcoeff x, ?_⟩
    simpa only [surfaceEpsilon, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_coe, AlgEquiv.toLinearEquiv_apply, AlgEquiv.symm_apply_apply] using hx
  · rintro ⟨x, hx⟩
    exact ⟨(closedSurfaceEquiv R hcoeff Fcoeff).symm x, hx⟩

/-- The actual kernel of the actual deformed-family reduction is
canonically the original surface ring; no flatness premise is supplied. -/
def surfaceKernelEquiv [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) :
    SurfaceRing R hcoeff Fcoeff ≃ₗ[R]
      LinearMap.ker (surfaceReduction R hcoeff Fcoeff A).toLinearMap :=
  LinearEquiv.ofBijective
    ((surfaceEpsilon R hcoeff Fcoeff A).codRestrict _ (fun x =>
      (surfaceReduction_eq_zero_iff R hcoeff Fcoeff A _).mpr ⟨x, rfl⟩)) (by
        constructor
        · intro x y hxy
          exact surfaceEpsilon_injective R hcoeff Fcoeff A (congrArg Subtype.val hxy)
        · rintro ⟨z, hz⟩
          obtain ⟨x, hx⟩ := (surfaceReduction_eq_zero_iff R hcoeff Fcoeff A z).mp hz
          exact ⟨x, Subtype.ext hx⟩)

@[simp] theorem surfaceKernelEquiv_val [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) (x : SurfaceRing R hcoeff Fcoeff) :
    (surfaceKernelEquiv R hcoeff Fcoeff A x).val =
      surfaceEpsilon R hcoeff Fcoeff A x := rfl

theorem surface_kernel_mul_zero
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) (x y : SurfaceDeformation R hcoeff Fcoeff A)
    (hx : surfaceReduction R hcoeff Fcoeff A x = 0)
    (hy : surfaceReduction R hcoeff Fcoeff A y = 0) : x * y = 0 := by
  apply kernel_mul_zero (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A) x y
  · exact (closedSurfaceEquiv R hcoeff Fcoeff).injective (hx.trans (map_zero _).symm)
  · exact (closedSurfaceEquiv R hcoeff Fcoeff).injective (hy.trans (map_zero _).symm)

end CycleQ2GeometricUniversalSurfaceFirstOrder

#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.sexticClass_regular
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.closedSurfaceEquiv_mk
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.surfaceKernelEquiv
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.surface_kernel_mul_zero

end
end SourceUniversalSurfaceFirstOrder

section SourceUniversalSurfaceFirstOrderMaps

/-! Actual coefficient maps on F - epsilon A and its normalized universal
surface specialization.  The epsilon character and the division of A by
an invertible leading coefficient are explicit maps of the defining
quotients.  No endomorphism base-change or desired obstruction class is
assumed. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricSurfaceFirstOrder

private theorem firstOrderMaps_snd_mul {R : Type*} [CommRing R] (x y : Dual R) :
    (x * y).snd = x.fst * y.snd + x.snd * y.fst := rfl

end CycleQ2GeometricSurfaceFirstOrder


namespace CycleQ2GeometricSurfaceFirstOrder

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Coefficient specialization on the actual dual-number rings. -/
def dualMap (φ : R →+* S) : Dual R →+* Dual S where
  toFun z := (φ z.fst, φ z.snd)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · change φ (x.fst + y.fst) = φ x.fst + φ y.fst
      exact map_add φ _ _
    · change φ (x.snd + y.snd) = φ x.snd + φ y.snd
      exact map_add φ _ _
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · change φ (x.fst * y.fst) = φ x.fst * φ y.fst
      exact map_mul φ _ _
    · change φ (x.fst * y.snd + x.snd * y.fst) =
        φ x.fst * φ y.snd + φ x.snd * φ y.fst
      rw [map_add, map_mul, map_mul]

@[simp] theorem dualMap_fst (φ : R →+* S) (z : Dual R) :
    (dualMap φ z).fst = φ z.fst := rfl

@[simp] theorem dualMap_snd (φ : R →+* S) (z : Dual R) :
    (dualMap φ z).snd = φ z.snd := rfl

@[simp] theorem dualMap_relation (φ : R →+* S) (f a : R) :
    dualMap φ (relation f a) = relation (φ f) (φ a) := by
  apply TrivSqZeroExt.ext
  · rfl
  · exact map_neg φ a

def closedMap (φ : R →+* S) (f : R) : Closed f →+* Closed (φ f) :=
  Ideal.Quotient.lift (Ideal.span ({f} : Set R))
    ((Ideal.Quotient.mk (Ideal.span ({φ f} : Set S))).comp φ) (by
      intro x hx
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hx
      change Ideal.Quotient.mk (Ideal.span ({φ f} : Set S)) (φ x) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply Ideal.mem_span_singleton'.mpr
      exact ⟨φ u, by rw [← map_mul, hu]⟩)

@[simp] theorem closedMap_mk (φ : R →+* S) (f x : R) :
    closedMap φ f (Ideal.Quotient.mk (Ideal.span ({f} : Set R)) x) =
      Ideal.Quotient.mk (Ideal.span ({φ f} : Set S)) (φ x) := rfl

/-- The deformed quotient itself specializes, before any coefficient
extraction or cohomology class is chosen. -/
def deformationMap (φ : R →+* S) (f a : R) :
    Deformation f a →+* Deformation (φ f) (φ a) :=
  Ideal.Quotient.lift (deformationIdeal f a)
    ((Ideal.Quotient.mk (deformationIdeal (φ f) (φ a))).comp (dualMap φ)) (by
      intro x hx
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hx
      change Ideal.Quotient.mk (deformationIdeal (φ f) (φ a)) (dualMap φ x) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨dualMap φ u, ?_⟩
      rw [← dualMap_relation, ← map_mul, hu])

@[simp] theorem deformationMap_mk (φ : R →+* S) (f a : R) (z : Dual R) :
    deformationMap φ f a (Ideal.Quotient.mk (deformationIdeal f a) z) =
      Ideal.Quotient.mk (deformationIdeal (φ f) (φ a)) (dualMap φ z) := rfl

theorem reduction_natural (φ : R →+* S) (f a : R) (z : Deformation f a) :
    reduction (φ f) (φ a) (deformationMap φ f a z) =
      closedMap φ f (reduction f a z) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem epsilon_natural (φ : R →+* S) (f a : R) (x : Closed f) :
    deformationMap φ f a (epsilon f a x) =
      epsilon (φ f) (φ a) (closedMap φ f x) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [epsilon_mk, deformationMap_mk, closedMap_mk, epsilon_mk]
  congr 1
  apply TrivSqZeroExt.ext
  · exact map_zero φ
  · rfl

/-- Canonical ε-coefficients commute with specialization whenever the
regularity hypothesis holds on both actual hypersurfaces. -/
theorem kernelEquiv_natural (φ : R →+* S) (f a : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hφf : ∀ x : S, φ f * x = 0 → x = 0)
    (z : Deformation f a) (hz : reduction f a z = 0) :
    (kernelEquiv (φ f) (φ a) hφf).symm
        ⟨deformationMap φ f a z, by
          change reduction (φ f) (φ a) (deformationMap φ f a z) = 0
          rw [reduction_natural, hz, map_zero]⟩ =
      closedMap φ f ((kernelEquiv f a hf).symm ⟨z, hz⟩) := by
  apply epsilon_injective (φ f) (φ a) hφf
  have hleft := congrArg Subtype.val
    ((kernelEquiv (φ f) (φ a) hφf).apply_symm_apply
      ⟨deformationMap φ f a z, by
        change reduction (φ f) (φ a) (deformationMap φ f a z) = 0
        rw [reduction_natural, hz, map_zero]⟩)
  have hright := congrArg Subtype.val
    ((kernelEquiv f a hf).apply_symm_apply ⟨z, hz⟩)
  change epsilon (φ f) (φ a) _ = deformationMap φ f a z at hleft
  change epsilon f a _ = z at hright
  rw [hleft, ← epsilon_natural, hright]

end CycleQ2GeometricSurfaceFirstOrder

namespace CycleQ2GeometricSurfaceFirstOrder

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The actual map of dual-number rings allowing ε to have a nontrivial
character.  In the cyclic application c = ζ² and the ambient test has
character ζ, so f - εa is fixed. -/
def dualMapScaled (φ : R →+* S) (c : S) : Dual R →+* Dual S where
  toFun z := (φ z.fst, c * φ z.snd)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · change φ (x.fst + y.fst) = φ x.fst + φ y.fst
      exact map_add φ _ _
    · change c * φ (x.snd + y.snd) = c * φ x.snd + c * φ y.snd
      rw [map_add, mul_add]
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · change φ (x.fst * y.fst) = φ x.fst * φ y.fst
      exact map_mul φ _ _
    · change c * φ (x.fst * y.snd + x.snd * y.fst) =
        φ x.fst * (c * φ y.snd) + (c * φ x.snd) * φ y.fst
      rw [map_add, map_mul, map_mul]
      ring

@[simp] theorem dualMapScaled_relation (φ : R →+* S) (c : S) (f a : R) :
    dualMapScaled φ c (relation f a) = relation (φ f) (c * φ a) := by
  apply TrivSqZeroExt.ext
  · rfl
  · exact (congrArg (c * ·) (map_neg φ a)).trans (mul_neg c (φ a))

/-- This is a map of the actual deformed quotients, with the ambient
test transformed along with the ε character. -/
def deformationMapScaled (φ : R →+* S) (c : S) (f a : R) :
    Deformation f a →+* Deformation (φ f) (c * φ a) :=
  Ideal.Quotient.lift (deformationIdeal f a)
    ((Ideal.Quotient.mk (deformationIdeal (φ f) (c * φ a))).comp
      (dualMapScaled φ c)) (by
      intro x hx
      obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hx
      change Ideal.Quotient.mk (deformationIdeal (φ f) (c * φ a))
        (dualMapScaled φ c x) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨dualMapScaled φ c u, ?_⟩
      rw [← dualMapScaled_relation, ← map_mul, hu])

@[simp] theorem deformationMapScaled_mk (φ : R →+* S) (c : S)
    (f a : R) (z : Dual R) :
    deformationMapScaled φ c f a (Ideal.Quotient.mk (deformationIdeal f a) z) =
      Ideal.Quotient.mk (deformationIdeal (φ f) (c * φ a)) (dualMapScaled φ c z) := rfl

theorem reduction_scaled_natural (φ : R →+* S) (c : S)
    (f a : R) (z : Deformation f a) :
    reduction (φ f) (c * φ a) (deformationMapScaled φ c f a z) =
      closedMap φ f (reduction f a z) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

theorem epsilon_scaled_natural (φ : R →+* S) (c : S)
    (f a : R) (x : Closed f) :
    deformationMapScaled φ c f a (epsilon f a x) =
      epsilon (φ f) (c * φ a)
        (Ideal.Quotient.mk (Ideal.span ({φ f} : Set S)) c * closedMap φ f x) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [epsilon_mk, deformationMapScaled_mk, closedMap_mk,
    ← map_mul (Ideal.Quotient.mk (Ideal.span ({φ f} : Set S))), epsilon_mk]
  congr 1
  apply TrivSqZeroExt.ext
  · exact map_zero φ
  · rfl

/-- The character on the actual infinitesimal parameter is visible in
canonical coefficient extraction.  With c = ζ² this is the inverse
character factor required by the ambient-test obstruction. -/
theorem kernelEquiv_scaled_natural (φ : R →+* S) (c : S) (f a : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (hφf : ∀ x : S, φ f * x = 0 → x = 0)
    (z : Deformation f a) (hz : reduction f a z = 0) :
    (kernelEquiv (φ f) (c * φ a) hφf).symm
        ⟨deformationMapScaled φ c f a z,
          by
            change reduction (φ f) (c * φ a) (deformationMapScaled φ c f a z) = 0
            rw [reduction_scaled_natural, hz, map_zero]⟩ =
      Ideal.Quotient.mk (Ideal.span ({φ f} : Set S)) c *
        closedMap φ f ((kernelEquiv f a hf).symm ⟨z, hz⟩) := by
  apply epsilon_injective (φ f) (c * φ a) hφf
  have hleft := congrArg Subtype.val
    ((kernelEquiv (φ f) (c * φ a) hφf).apply_symm_apply
      ⟨deformationMapScaled φ c f a z,
        by
          change reduction (φ f) (c * φ a) (deformationMapScaled φ c f a z) = 0
          rw [reduction_scaled_natural, hz, map_zero]⟩)
  have hright := congrArg Subtype.val
    ((kernelEquiv f a hf).apply_symm_apply ⟨z, hz⟩)
  change epsilon (φ f) (c * φ a) _ = deformationMapScaled φ c f a z at hleft
  change epsilon f a _ = z at hright
  rw [hleft, ← epsilon_scaled_natural, hright]

end CycleQ2GeometricSurfaceFirstOrder

namespace CycleQ2GeometricSurfaceFirstOrder

variable {R : Type*} [CommRing R]

/-- Dividing the defining equation by a unit also divides the ambient
test by that unit. The epsilon coordinate itself is unchanged. -/
theorem relation_unit_mul (u : Rˣ) (f a : R) :
    relation ((u : R) * f) a =
      TrivSqZeroExt.inl (u : R) * relation f ((↑(u⁻¹) : R) * a) := by
  apply TrivSqZeroExt.ext
  · change (u : R) * f = (u : R) * f
    rfl
  · change -a = (u : R) * (-((↑(u⁻¹) : R) * a)) + 0 * f
    rw [zero_mul, add_zero, mul_neg, ← mul_assoc, Units.mul_inv, one_mul]

theorem deformationIdeal_unit_mul (u : Rˣ) (f a : R) :
    deformationIdeal ((u : R) * f) a = deformationIdeal f ((↑(u⁻¹) : R) * a) := by
  unfold deformationIdeal
  rw [relation_unit_mul]
  exact Ideal.span_singleton_mul_left_unit
    (u.isUnit.map (TrivSqZeroExt.inlHom R R)) _

theorem closedIdeal_unit_mul (u : Rˣ) (f : R) :
    Ideal.span ({(u : R) * f} : Set R) = Ideal.span ({f} : Set R) :=
  Ideal.span_singleton_mul_left_unit u.isUnit f

/-- The actual quotient-ring identity from raw to normalized equation.
In the incidence family u is the leading sextic coefficient. -/
def unitNormalization (u : Rˣ) (f a : R) :
    Deformation ((u : R) * f) a ≃ₐ[R] Deformation f ((↑(u⁻¹) : R) * a) :=
  Ideal.quotientEquivAlgOfEq R (deformationIdeal_unit_mul u f a)

def unitClosedNormalization (u : Rˣ) (f : R) :
    Closed ((u : R) * f) ≃ₐ[R] Closed f :=
  Ideal.quotientEquivAlgOfEq R (closedIdeal_unit_mul u f)

@[simp] theorem unitNormalization_mk (u : Rˣ) (f a : R) (z : Dual R) :
    unitNormalization u f a
      (Ideal.Quotient.mk (deformationIdeal ((u : R) * f) a) z) =
      Ideal.Quotient.mk (deformationIdeal f ((↑(u⁻¹) : R) * a)) z := rfl

@[simp] theorem unitClosedNormalization_mk (u : Rˣ) (f x : R) :
    unitClosedNormalization u f
      (Ideal.Quotient.mk (Ideal.span ({(u : R) * f} : Set R)) x) =
      Ideal.Quotient.mk (Ideal.span ({f} : Set R)) x := rfl

theorem unitNormalization_reduction (u : Rˣ) (f a : R)
    (z : Deformation ((u : R) * f) a) :
    reduction f ((↑(u⁻¹) : R) * a) (unitNormalization u f a z) =
      unitClosedNormalization u f (reduction ((u : R) * f) a z) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

/-- Normalization preserves the actual epsilon coefficient under the
identity on polynomial representatives. -/
theorem unitNormalization_epsilon (u : Rˣ) (f a : R)
    (x : Closed ((u : R) * f)) :
    unitNormalization u f a (epsilon ((u : R) * f) a x) =
      epsilon f ((↑(u⁻¹) : R) * a) (unitClosedNormalization u f x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end CycleQ2GeometricSurfaceFirstOrder

namespace CycleQ2GeometricUniversalSurfaceFirstOrder

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2UniversalSurfaceCoefficientMap CycleQ2GeometricSurfaceFirstOrder

variable {R S : Type*} [CommRing R] [CommRing S]

attribute [local instance] cubicSelfModule cubicOppositeModule
  cubicCentralScalar cubicSmulCommClass surfaceDeformationModule surfaceDeformationCubicModule

/-- The coefficient map acts on the actual quotient by the cubic, with
all five polynomial coordinates mapped by the original coefficient map. -/
def cubicMap (φ : R →+* S) (hcoeff : FullCubicTailIndex → R) :
    CubicQuotient R hcoeff →+* CubicQuotient S (fun i => φ (hcoeff i)) :=
  Ideal.quotientMap (cubicIdeal S (fun i => φ (hcoeff i))) (MvPolynomial.map φ) (by
    apply Ideal.span_le.mpr
    rintro p (rfl : p = normalizedFullCubic hcoeff)
    change MvPolynomial.map φ (normalizedFullCubic hcoeff) ∈
      cubicIdeal S (fun i => φ (hcoeff i))
    rw [map_cubic]
    exact Ideal.mem_span_singleton_self _)

@[simp] theorem cubicMap_mk (φ : R →+* S) (hcoeff : FullCubicTailIndex → R)
    (p : MvPolynomial (Fin 5) R) :
    cubicMap φ hcoeff (Ideal.Quotient.mk (cubicIdeal R hcoeff) p) =
      Ideal.Quotient.mk (cubicIdeal S (fun i => φ (hcoeff i)))
        (MvPolynomial.map φ p) := rfl

@[simp] theorem cubicMap_sexticClass (φ : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    cubicMap φ hcoeff (sexticClass R hcoeff Fcoeff) =
      sexticClass S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i)) := by
  change Ideal.Quotient.mk _ (MvPolynomial.map φ (normalizedFullSextic Fcoeff)) = _
  rw [map_sextic]
  rfl

@[simp] theorem cubicMap_testClass (φ : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (A : MvPolynomial (Fin 5) R) :
    cubicMap φ hcoeff (testClass R hcoeff A) =
      testClass S (fun i => φ (hcoeff i)) (MvPolynomial.map φ A) := rfl

/-- Specialization of the actual normalized F - epsilon A quotient.
This map is defined on representatives before extracting any class. -/
def surfaceDeformationMap (φ : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) :
    SurfaceDeformation R hcoeff Fcoeff A →+*
      SurfaceDeformation S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i))
        (MvPolynomial.map φ A) :=
  Ideal.quotientMap
    (deformationIdeal (sexticClass S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i)))
      (testClass S (fun i => φ (hcoeff i)) (MvPolynomial.map φ A)))
    (dualMap (cubicMap φ hcoeff)) (by
      apply Ideal.span_le.mpr
      rintro z (rfl : z = relation (sexticClass R hcoeff Fcoeff)
        (testClass R hcoeff A))
      change dualMap (cubicMap φ hcoeff)
          (relation (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)) ∈
        deformationIdeal
          (sexticClass S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i)))
          (testClass S (fun i => φ (hcoeff i)) (MvPolynomial.map φ A))
      rw [dualMap_relation, cubicMap_sexticClass, cubicMap_testClass]
      exact Ideal.mem_span_singleton_self _)

@[simp] theorem surfaceDeformationMap_mk (φ : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) (z : Dual (CubicQuotient R hcoeff)) :
    surfaceDeformationMap φ hcoeff Fcoeff A
      (Ideal.Quotient.mk (deformationIdeal (sexticClass R hcoeff Fcoeff)
        (testClass R hcoeff A)) z) =
      Ideal.Quotient.mk
        (deformationIdeal
          (sexticClass S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i)))
          (testClass S (fun i => φ (hcoeff i)) (MvPolynomial.map φ A)))
        (dualMap (cubicMap φ hcoeff) z) := rfl

/-- Its reduction is precisely the already fixed universal surface
coefficient map, preserving the original nine monomial coordinates. -/
theorem surfaceDeformationMap_reduction (φ : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) (z : SurfaceDeformation R hcoeff Fcoeff A) :
    surfaceReduction S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i))
        (MvPolynomial.map φ A) (surfaceDeformationMap φ hcoeff Fcoeff A z) =
      surfaceMap φ hcoeff Fcoeff (surfaceReduction R hcoeff Fcoeff A z) := by
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective z.fst
  change closedSurfaceEquiv S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i))
      (Ideal.Quotient.mk _ (cubicMap φ hcoeff z.fst)) =
    surfaceMap φ hcoeff Fcoeff
      (closedSurfaceEquiv R hcoeff Fcoeff (Ideal.Quotient.mk _ z.fst))
  rw [← hp, cubicMap_mk, closedSurfaceEquiv_mk, closedSurfaceEquiv_mk,
    surfaceMap_mk]

theorem surfaceDeformationMap_epsilon (φ : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) (x : SurfaceRing R hcoeff Fcoeff) :
    surfaceDeformationMap φ hcoeff Fcoeff A (surfaceEpsilon R hcoeff Fcoeff A x) =
      surfaceEpsilon S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i))
        (MvPolynomial.map φ A) (surfaceMap φ hcoeff Fcoeff x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [surfaceEpsilon_mk, surfaceDeformationMap_mk, surfaceMap_mk, surfaceEpsilon_mk]
  congr 1
  apply TrivSqZeroExt.ext
  · exact map_zero (cubicMap φ hcoeff)
  · rfl

/-- The coefficient of epsilon in the actual deformed surface kernel
specializes to the coefficient of the same element on the actual target
surface.  Both regularity facts are proved by the monic family equations. -/
theorem surfaceKernelCoefficient_natural [Nontrivial R] [Nontrivial S]
    (φ : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (A : MvPolynomial (Fin 5) R) (z : SurfaceDeformation R hcoeff Fcoeff A)
    (hz : surfaceReduction R hcoeff Fcoeff A z = 0) :
    (surfaceKernelEquiv S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i))
        (MvPolynomial.map φ A)).symm
      ⟨surfaceDeformationMap φ hcoeff Fcoeff A z,
        by
          change surfaceReduction S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i))
            (MvPolynomial.map φ A) (surfaceDeformationMap φ hcoeff Fcoeff A z) = 0
          rw [surfaceDeformationMap_reduction, hz, map_zero]⟩ =
      surfaceMap φ hcoeff Fcoeff ((surfaceKernelEquiv R hcoeff Fcoeff A).symm ⟨z, hz⟩) := by
  apply surfaceEpsilon_injective S (fun i => φ (hcoeff i))
    (fun i => φ (Fcoeff i)) (MvPolynomial.map φ A)
  have hs := congrArg Subtype.val
    ((surfaceKernelEquiv R hcoeff Fcoeff A).apply_symm_apply ⟨z, hz⟩)
  have ht := congrArg Subtype.val
    ((surfaceKernelEquiv S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i))
      (MvPolynomial.map φ A)).apply_symm_apply
        ⟨surfaceDeformationMap φ hcoeff Fcoeff A z,
          by
            change surfaceReduction S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i))
              (MvPolynomial.map φ A) (surfaceDeformationMap φ hcoeff Fcoeff A z) = 0
            rw [surfaceDeformationMap_reduction, hz, map_zero]⟩)
  change surfaceEpsilon R hcoeff Fcoeff A _ = z at hs
  change surfaceEpsilon S (fun i => φ (hcoeff i)) (fun i => φ (Fcoeff i))
    (MvPolynomial.map φ A) _ = surfaceDeformationMap φ hcoeff Fcoeff A z at ht
  rw [ht, ← surfaceDeformationMap_epsilon, hs]

end CycleQ2GeometricUniversalSurfaceFirstOrder

#print axioms CycleQ2GeometricSurfaceFirstOrder.kernelEquiv_scaled_natural
#print axioms CycleQ2GeometricSurfaceFirstOrder.unitNormalization_epsilon
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.cubicMap_sexticClass
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.surfaceDeformationMap_reduction
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.surfaceDeformationMap_epsilon
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.surfaceKernelCoefficient_natural

end
end SourceUniversalSurfaceFirstOrderMaps

section SourceUniversalCoefficientTangent

/-! Actual first-order evaluation of the original coefficient parameter
ring.  These are invariant coefficient tangents, not the character-one
ambient test used in the separate F - epsilon A deformation.  The cubic,
sextic, and matrix coefficients are all evaluated by the original
specialization map, and normalization obeys the actual quotient rule. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricUniversalCoefficientTangent

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2UniversalSurfaceNormalization
  CycleQ2GeometricSurfaceFirstOrder

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]

section Evaluation

variable (hcoeff : FullInvariantIndex 3 → S)
  (Fcoeff : FullInvariantIndex 6 → S)
  (matrixCoeff : Fin 3 → Fin 3 → StandardIndex 14 → S)
  (dh : FullInvariantIndex 3 → S) (dF : FullInvariantIndex 6 → S)
  (dM : Fin 3 → Fin 3 → StandardIndex 14 → S)
  (hu : IsUnit (hcoeff fullCubicLeadingIndex))
  (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))

/-- The original localized parameter ring is evaluated at its literal
dual-number coefficient point.  No incidence equation is assumed here. -/
def firstOrderEvaluation : ParameterRing R →ₐ[R] Dual S :=
  specialization (S := Dual S)
    (fun e => ((hcoeff e, dh e) : Dual S)) (fun e => ((Fcoeff e, dF e) : Dual S))
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr hu)
    (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr Fu)
    (fun i j e => ((matrixCoeff i j e, dM i j e) : Dual S))

@[simp] theorem firstOrderEvaluation_polynomial (p : ParameterPolynomial R) :
    firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu
        (algebraMap (ParameterPolynomial R) (ParameterRing R) p) =
      polynomialSpecialization (S := Dual S)
        (fun e => ((hcoeff e, dh e) : Dual S))
        (fun e => ((Fcoeff e, dF e) : Dual S))
        (fun i j e => ((matrixCoeff i j e, dM i j e) : Dual S)) p :=
  specialization_polynomial _ _ _ _ _ p

@[simp] theorem firstOrderEvaluation_cubic (e : FullInvariantIndex 3) :
    firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu
      (cubicCoefficient R e) = (hcoeff e, dh e) :=
  specialization_cubicCoefficient _ _ _ _ _ e

@[simp] theorem firstOrderEvaluation_sextic (e : FullInvariantIndex 6) :
    firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu
      (sexticCoefficient R e) = (Fcoeff e, dF e) :=
  specialization_sexticCoefficient _ _ _ _ _ e

@[simp] theorem firstOrderEvaluation_matrix (i j : Fin 3) (e : StandardIndex 14) :
    firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu
      (matrixCoefficient R i j e) = (matrixCoeff i j e, dM i j e) :=
  specialization_matrixCoefficient _ _ _ _ _ i j e

/-- Reduction is the original coefficient specialization on the entire
localized parameter ring, not only on its polynomial generators. -/
theorem firstOrderEvaluation_reduction :
    (TrivSqZeroExt.fstHom R S S).comp
        (firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu) =
      specialization hcoeff Fcoeff hu Fu matrixCoeff := by
  apply IsLocalization.algHom_ext (Submonoid.powers (leadingProduct R))
  apply AlgHom.ext
  intro p
  change (firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu
      (algebraMap (ParameterPolynomial R) (ParameterRing R) p)).fst =
    specialization hcoeff Fcoeff hu Fu matrixCoeff
      (algebraMap (ParameterPolynomial R) (ParameterRing R) p)
  rw [firstOrderEvaluation_polynomial, specialization_polynomial]
  have he : (TrivSqZeroExt.fstHom R S S).comp
      (polynomialSpecialization (S := Dual S)
        (fun e => ((hcoeff e, dh e) : Dual S))
        (fun e => ((Fcoeff e, dF e) : Dual S))
        (fun i j e => ((matrixCoeff i j e, dM i j e) : Dual S))) =
      polynomialSpecialization hcoeff Fcoeff matrixCoeff := by
    apply MvPolynomial.algHom_ext
    intro i
    rcases i with e | (e | q) <;>
      simp only [AlgHom.comp_apply, polynomialSpecialization, aeval_X] <;> rfl
  exact AlgHom.congr_fun he p

end Evaluation

private def coefficientDual (a da : S) : Dual S := (a, da)

private theorem dual_ratio (u : Sˣ) (du a da : S) (z : Dual S)
    (hz : coefficientDual (u : S) du * z = coefficientDual a da) :
    z.fst = (↑(u⁻¹) : S) * a ∧
      z.snd = (↑(u⁻¹) : S) * (da - du * ((↑(u⁻¹) : S) * a)) := by
  have h0 := congrArg TrivSqZeroExt.fst hz
  have h1 := congrArg TrivSqZeroExt.snd hz
  change (u : S) * z.fst = a at h0
  change (u : S) * z.snd + du * z.fst = da at h1
  have hz0 : z.fst = (↑(u⁻¹) : S) * a := by
    rw [← h0, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨hz0, ?_⟩
  rw [hz0] at h1
  have hz1 := eq_sub_of_add_eq h1
  calc
    z.snd = (↑(u⁻¹) : S) * ((u : S) * z.snd) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := congrArg ((↑(u⁻¹) : S) * ·) hz1

section Normalization

variable (hcoeff : FullInvariantIndex 3 → S)
  (Fcoeff : FullInvariantIndex 6 → S)
  (matrixCoeff : Fin 3 → Fin 3 → StandardIndex 14 → S)
  (dh : FullInvariantIndex 3 → S) (dF : FullInvariantIndex 6 → S)
  (dM : Fin 3 → Fin 3 → StandardIndex 14 → S)
  (hu : IsUnit (hcoeff fullCubicLeadingIndex))
  (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))

/-- The normalized cubic has the actual differentiated inverse leading
coefficient.  In particular a moving leading coefficient is not ignored. -/
theorem firstOrderEvaluation_normalizedCubic (e : FullCubicTailIndex) :
    firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu
        (universalCubicTail R e) =
      ((↑(hu.unit⁻¹) : S) * hcoeff e.val,
        (↑(hu.unit⁻¹) : S) *
          (dh e.val - dh fullCubicLeadingIndex *
            ((↑(hu.unit⁻¹) : S) * hcoeff e.val))) := by
  have hp : cubicCoefficient R fullCubicLeadingIndex * universalCubicTail R e =
      cubicCoefficient R e.val := by
    dsimp only [universalCubicTail, normalizedCubicTail]
    simpa only [(leading_coefficients_units R).1.unit_spec] using
      Units.mul_inv_cancel_left (leading_coefficients_units R).1.unit
        (cubicCoefficient R e.val)
  have hm := congrArg
    (firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu) hp
  rw [map_mul, firstOrderEvaluation_cubic, firstOrderEvaluation_cubic] at hm
  have h := dual_ratio hu.unit (dh fullCubicLeadingIndex) (hcoeff e.val)
    (dh e.val)
    (firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu (universalCubicTail R e))
    (by simpa only [coefficientDual, hu.unit_spec] using hm)
  exact TrivSqZeroExt.ext h.1 h.2

/-- The same original map gives the normalized sextic quotient rule. -/
theorem firstOrderEvaluation_normalizedSextic (e : FullSexticTailIndex) :
    firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu
        (universalSexticTail R e) =
      ((↑(Fu.unit⁻¹) : S) * Fcoeff e.val,
        (↑(Fu.unit⁻¹) : S) *
          (dF e.val - dF fullSexticLeadingIndex *
            ((↑(Fu.unit⁻¹) : S) * Fcoeff e.val))) := by
  have hp : sexticCoefficient R fullSexticLeadingIndex * universalSexticTail R e =
      sexticCoefficient R e.val := by
    dsimp only [universalSexticTail, normalizedSexticTail]
    simpa only [(leading_coefficients_units R).2.unit_spec] using
      Units.mul_inv_cancel_left (leading_coefficients_units R).2.unit
        (sexticCoefficient R e.val)
  have hm := congrArg
    (firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu) hp
  rw [map_mul, firstOrderEvaluation_sextic, firstOrderEvaluation_sextic] at hm
  have h := dual_ratio Fu.unit (dF fullSexticLeadingIndex) (Fcoeff e.val)
    (dF e.val)
    (firstOrderEvaluation hcoeff Fcoeff matrixCoeff dh dF dM hu Fu (universalSexticTail R e))
    (by simpa only [coefficientDual, Fu.unit_spec] using hm)
  exact TrivSqZeroExt.ext h.1 h.2

end Normalization
end CycleQ2GeometricUniversalCoefficientTangent

#print axioms CycleQ2GeometricUniversalCoefficientTangent.firstOrderEvaluation_reduction
#print axioms CycleQ2GeometricUniversalCoefficientTangent.firstOrderEvaluation_matrix
#print axioms CycleQ2GeometricUniversalCoefficientTangent.firstOrderEvaluation_normalizedCubic
#print axioms CycleQ2GeometricUniversalCoefficientTangent.firstOrderEvaluation_normalizedSextic

end
end SourceUniversalCoefficientTangent

section SourceSeedFirstOrderEquations

/-! Individual original seed equations, not just equality of the pair
ideal. The original leading coefficients are exactly one, so the actual
normalized first-order regularity applies to theta=1 with no rescaling. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricSeedNormalizedCoordinates

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2UniversalSurfaceNormalization
  CycleQ2UniversalSurfaceCoefficientMap CycleQ2GeometricUniversalSurfaceFirstOrder
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricSeedNormalIdeals CycleQ2NormalConnecting

variable (R : Type*) [CommRing R] [IsDomain R]

theorem seed_cubicLeadingUnit (r ι : R) :
    seedSpecialization R r ι ((leading_coefficients_units R).1.unit : ParameterRing R) = 1 := by
  calc
    _ = seedSpecialization R r ι (cubicCoefficient R fullCubicLeadingIndex) :=
      congrArg (seedSpecialization R r ι) (leading_coefficients_units R).1.unit_spec
    _ = 1 := by
      rw [seedSpecialization, specialization_cubicCoefficient]
      simpa only [seedCubicCoefficients, fullCubicLeadingIndex_exponent] using
        smoothH_leading_coefficient ι

theorem seed_sexticLeadingUnit (r ι : R) :
    seedSpecialization R r ι ((leading_coefficients_units R).2.unit : ParameterRing R) = 1 := by
  calc
    _ = seedSpecialization R r ι (sexticCoefficient R fullSexticLeadingIndex) :=
      congrArg (seedSpecialization R r ι) (leading_coefficients_units R).2.unit_spec
    _ = 1 := by
      rw [seedSpecialization, specialization_sexticCoefficient]
      simpa only [seedSexticCoefficients, fullSexticLeadingIndex_exponent] using
        smoothF_leading_coefficient r ι

theorem seed_normalized_cubic (r ι : R) :
    normalizedFullCubic (fun i => seedSpecialization R r ι (universalCubicTail R i)) =
      smoothH ι := by
  have hm := congrArg (MvPolynomial.map (seedSpecialization R r ι).toRingHom)
    (fullCubic_eq_unit_mul (cubicCoefficient R) (leading_coefficients_units R).1)
  simp only [map_fullInvariantPolynomial, map_mul, MvPolynomial.map_C, map_cubic,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hm
  rw [seed_cubicLeadingUnit R r ι, map_one, one_mul] at hm
  have hc : (fun e => seedSpecialization R r ι (cubicCoefficient R e)) =
      seedCubicCoefficients ι := by
    funext e
    exact specialization_cubicCoefficient _ _ _ _ _ e
  simp only [Function.comp_def] at hm
  rw [hc, seedCubicCoefficients_polynomial] at hm
  exact hm.symm

theorem seed_normalized_sextic (r ι : R) :
    normalizedFullSextic (fun i => seedSpecialization R r ι (universalSexticTail R i)) =
      smoothF r ι := by
  have hm := congrArg (MvPolynomial.map (seedSpecialization R r ι).toRingHom)
    (fullSextic_eq_unit_mul (sexticCoefficient R) (leading_coefficients_units R).2)
  simp only [map_fullInvariantPolynomial, map_mul, MvPolynomial.map_C, map_sextic,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hm
  rw [seed_sexticLeadingUnit R r ι, map_one, one_mul] at hm
  have hc : (fun e => seedSpecialization R r ι (sexticCoefficient R e)) =
      seedSexticCoefficients r ι := by
    funext e
    exact specialization_sexticCoefficient _ _ _ _ _ e
  simp only [Function.comp_def] at hm
  rw [hc, seedSexticCoefficients_polynomial] at hm
  exact hm.symm

theorem normalizedCubic_eq_thetaH_one (r : ℂ) :
    normalizedFullCubic (cubicCoefficients r) = thetaH 1 :=
  (seed_normalized_cubic ℂ r Complex.I).trans smoothH_eq_thetaH

theorem normalizedSextic_eq_actualSeedEquation (r : ℂ) :
    normalizedFullSextic (sexticCoefficients r) = actualSeedEquation r 1 :=
  (seed_normalized_sextic ℂ r Complex.I).trans (actualSeedEquation_eq_smoothF r).symm

/-- The literal theta=1 seed equation is regular modulo its actual cubic,
for every r; this uses the checked normalized monic pair. -/
theorem actualSeedEquation_regular_mod_thetaH (r : ℂ)
    (p : CycleQ2SeedTrace.WeightedPoly)
    (hp : actualSeedEquation r 1 * p ∈ Ideal.span ({thetaH 1} : Set CycleQ2SeedTrace.WeightedPoly)) :
    p ∈ Ideal.span ({thetaH 1} : Set CycleQ2SeedTrace.WeightedPoly) := by
  have hp' : normalizedFullSextic (sexticCoefficients r) * p ∈
      cubicIdeal ℂ (cubicCoefficients r) := by
    simpa only [cubicIdeal, normalizedCubic_eq_thetaH_one,
      normalizedSextic_eq_actualSeedEquation] using hp
  have h := normalized_sextic_regular_mod_cubic ℂ
    (cubicCoefficients r) (sexticCoefficients r) p hp'
  simpa only [cubicIdeal, normalizedCubic_eq_thetaH_one] using h

end CycleQ2GeometricSeedNormalizedCoordinates

#print axioms CycleQ2GeometricSeedNormalizedCoordinates.seed_normalized_cubic
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.seed_normalized_sextic
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.normalizedCubic_eq_thetaH_one
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.normalizedSextic_eq_actualSeedEquation
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.actualSeedEquation_regular_mod_thetaH

end
end SourceSeedFirstOrderEquations

section SourceFirstOrderLocalization

/-! Localization of the actual square-zero reduction and its canonical
kernel.  The comparison uses the actual algebra maps and is characterized
on original surface functions. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricSurfaceFirstOrder

variable {R : Type*} [CommRing R]

@[instance_reducible] def reducedAlgebra (f a : R) :
    Algebra (Deformation f a) (Closed f) := (reduction f a).toRingHom.toAlgebra

attribute [local instance] reducedAlgebra

instance reducedModule (f a : R) : Module (Deformation f a) (Closed f) :=
  @Algebra.toModule (Deformation f a) (Closed f) _ _ (reducedAlgebra f a)

/-- The ε map is linear over the actual deformed ring, where its action
on the closed fibre is reduction. -/
def epsilonDeformationLinear (f a : R) :
    Closed f →ₗ[Deformation f a] Deformation f a where
  toFun := epsilon f a
  map_add' := (epsilon f a).map_add
  map_smul' z x := by
    change epsilon f a (reduction f a z * x) = z * epsilon f a x
    exact (mul_epsilon f a z x).symm

/-- Canonical ε coefficients, with the scalar action needed to localize
the actual kernel rather than merely its underlying additive group. -/
def kernelEquivOverDeformation (f a : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) :
    Closed f ≃ₗ[Deformation f a] RingHom.ker (reduction f a).toRingHom :=
  LinearEquiv.ofBijective
    ((epsilonDeformationLinear f a).codRestrict _ (fun x => reduction_epsilon f a x)) (by
      constructor
      · intro x y hxy
        exact epsilon_injective f a hf (congrArg Subtype.val hxy)
      · rintro ⟨z, hz⟩
        obtain ⟨x, hx⟩ := (reduction_eq_zero_iff f a z).mp hz
        exact ⟨x, Subtype.ext hx⟩)

@[simp] theorem kernelEquivOverDeformation_val (f a : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) (x : Closed f) :
    (kernelEquivOverDeformation f a hf x).val = epsilon f a x := rfl

end CycleQ2GeometricSurfaceFirstOrder

namespace CycleQ2GeometricKernelLocalization

variable (E C : Type*) [CommRing E] [CommRing C] [Algebra E C]

abbrev ThickAt (t : E) := Localization.Away t
abbrev ClosedAt (t : E) := Localization.Away (algebraMap E C t)

/-- The genuine localization of the given reduction homomorphism. -/
def localReduction (t : E) : ThickAt E t →+* ClosedAt E C t :=
  IsLocalization.Away.map (ThickAt E t) (ClosedAt E C t) (algebraMap E C) t

@[simp] theorem localReduction_base (t x : E) :
    localReduction E C t (algebraMap E (ThickAt E t) x) =
      algebraMap C (ClosedAt E C t) (algebraMap E C x) :=
  IsLocalization.map_eq (M := Submonoid.powers t)
    (T := Submonoid.powers (algebraMap E C t))
    (S := ThickAt E t) (Q := ClosedAt E C t) (g := algebraMap E C)
    (by rintro y ⟨n, rfl⟩; exact ⟨n, by simp⟩) x

@[instance_reducible] def localReductionAlgebra (t : E) :
    Algebra (ThickAt E t) (ClosedAt E C t) := (localReduction E C t).toAlgebra

attribute [local instance] localReductionAlgebra

instance localReductionModule (t : E) :
    Module (ThickAt E t) (ClosedAt E C t) :=
  @Algebra.toModule (ThickAt E t) (ClosedAt E C t) _ _ (localReductionAlgebra E C t)

instance localReductionTower (t : E) :
    IsScalarTower E (ThickAt E t) (ClosedAt E C t) :=
  IsScalarTower.of_algebraMap_eq (fun x => (localReduction_base E C t x).symm)

abbrev LocalKernel (t : E) := RingHom.ker (localReduction E C t)

/-- The actual kernel element is sent by the original localization map. -/
def kernelMap (t : E) :
    RingHom.ker (algebraMap E C) →ₗ[E] LocalKernel E C t :=
  RingHom.toKerIsLocalization (M := Submonoid.powers t)
    (T := Submonoid.powers (algebraMap E C t))
    (ThickAt E t) (ClosedAt E C t) (algebraMap E C)
    (by rintro x ⟨n, rfl⟩; exact ⟨n, by simp⟩)

@[simp] theorem kernelMap_val (t : E) (x : RingHom.ker (algebraMap E C)) :
    (kernelMap E C t x).val = algebraMap E (ThickAt E t) x.val := rfl

instance kernelMap_localizes (t : E) :
    IsLocalizedModule (Submonoid.powers t) (kernelMap E C t) := by
  exact RingHom.toKerIsLocalization_isLocalizedModule
    (M := Submonoid.powers t) (T := Submonoid.powers (algebraMap E C t))
    (S := ThickAt E t) (ClosedAt E C t) (algebraMap E C)
    (by rw [Submonoid.map_powers])

def closedMap (t : E) : C →ₗ[E] ClosedAt E C t :=
  (IsScalarTower.toAlgHom E C (ClosedAt E C t)).toLinearMap

instance closedMap_localizes (t : E) :
    IsLocalizedModule (Submonoid.powers t) (closedMap E C t) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers t))
      (ClosedAt E C t) := by
    rw [Algebra.algebraMapSubmonoid_powers]
    infer_instance
  exact inferInstanceAs (IsLocalizedModule (Submonoid.powers t)
    (IsScalarTower.toAlgHom E C (ClosedAt E C t)).toLinearMap)

/-- Localizing a proved actual kernel identification gives the actual
kernel on every principal open.  The resulting map is linear over the
localized deformed ring. -/
def localizedKernelEquiv (e : C ≃ₗ[E] RingHom.ker (algebraMap E C)) (t : E) :
    ClosedAt E C t ≃ₗ[ThickAt E t] LocalKernel E C t :=
  (IsLocalizedModule.linearEquiv (Submonoid.powers t) (closedMap E C t)
    ((kernelMap E C t).comp e.toLinearMap)).extendScalarsOfIsLocalization
      (Submonoid.powers t) (ThickAt E t)

@[simp] theorem localizedKernelEquiv_base
    (e : C ≃ₗ[E] RingHom.ker (algebraMap E C)) (t : E) (x : C) :
    (localizedKernelEquiv E C e t (algebraMap C (ClosedAt E C t) x)).val =
      algebraMap E (ThickAt E t) (e x).val := by
  change (IsLocalizedModule.linearEquiv (Submonoid.powers t) (closedMap E C t)
    ((kernelMap E C t).comp e.toLinearMap) (closedMap E C t x)).val = _
  rw [IsLocalizedModule.linearEquiv_apply]
  rfl

/-- Multiplication on the localized actual kernel uses exactly the
localized reduction. This is the coefficient rule for overlap matrices. -/
theorem localizedKernelEquiv_mul
    (e : C ≃ₗ[E] RingHom.ker (algebraMap E C)) (t : E)
    (z : ThickAt E t) (x : ClosedAt E C t) :
    (localizedKernelEquiv E C e t (localReduction E C t z * x)).val =
      z * (localizedKernelEquiv E C e t x).val := by
  exact congrArg Subtype.val ((localizedKernelEquiv E C e t).map_smul z x)

theorem localReduction_surjective
    (hρ : Function.Surjective (algebraMap E C)) (t : E) :
    Function.Surjective (localReduction E C t) := by
  apply (IsLocalization.Away.map_surjective_iff
    (ThickAt E t) (ClosedAt E C t) (algebraMap E C) t).mpr
  intro x
  obtain ⟨y, hy⟩ := hρ x
  exact ⟨y, 0, by simpa using hy⟩

end CycleQ2GeometricKernelLocalization

namespace CycleQ2GeometricSurfaceFirstOrder

open CycleQ2GeometricKernelLocalization

variable {R : Type*} [CommRing R]

attribute [local instance] reducedAlgebra

/-- The original coordinate in the actual deformation ring.  Naming the
map fixes its canonical quotient-ring structure before localizing. -/
def deformationCoordinate (f a t : R) : Deformation f a :=
  Ideal.Quotient.mk (deformationIdeal f a) (TrivSqZeroExt.inl t)

@[simp] theorem deformationCoordinate_eq_algebraMap (f a t : R) :
    deformationCoordinate f a t =
      @algebraMap R (Deformation f a) (inferInstance : CommSemiring R)
        (inferInstance : Semiring (Deformation f a)) inferInstance t := rfl

/-- Actual coordinate-local deformation of f - εa. -/
abbrev LocalDeformation (f a t : R) :=
  ThickAt (Deformation f a) (deformationCoordinate f a t)

abbrev LocalClosed (f a t : R) :=
  ClosedAt (Deformation f a) (Closed f) (deformationCoordinate f a t)

/-- The kernel identification on the actual principal localization of
the actual deformation. The input regularity is discharged by the
normalized-family leading-term theorem. -/
def localKernelEquiv (f a t : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) :=
  localizedKernelEquiv (Deformation f a) (Closed f)
    (kernelEquivOverDeformation f a hf) (deformationCoordinate f a t)

@[simp] theorem localKernelEquiv_base (f a t : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) (x : Closed f) :
    (localKernelEquiv f a t hf
      (algebraMap (Closed f) (LocalClosed f a t) x)).val =
      @algebraMap (Deformation f a) (LocalDeformation f a t)
        (inferInstance : CommSemiring (Deformation f a))
        (inferInstance : Semiring (LocalDeformation f a t)) inferInstance (epsilon f a x) := by
  have h := localizedKernelEquiv_base (Deformation f a) (Closed f)
    (kernelEquivOverDeformation f a hf) (deformationCoordinate f a t) x
  rw [kernelEquivOverDeformation_val] at h
  exact h

end CycleQ2GeometricSurfaceFirstOrder

#print axioms CycleQ2GeometricSurfaceFirstOrder.kernelEquivOverDeformation
#print axioms CycleQ2GeometricKernelLocalization.localizedKernelEquiv
#print axioms CycleQ2GeometricKernelLocalization.localizedKernelEquiv_base
#print axioms CycleQ2GeometricKernelLocalization.localizedKernelEquiv_mul
#print axioms CycleQ2GeometricKernelLocalization.localReduction_surjective
#print axioms CycleQ2GeometricSurfaceFirstOrder.localKernelEquiv_base

end
end SourceFirstOrderLocalization

section SourceLocalizedProjectorCoefficients

/-! The coefficient interface for projector defects is supplied by the
actual localized kernel, with its original epsilon normalization.  The
actual hypersurface specialization discharges kernel exactness and
faithfulness using the regularity of the defining equation. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricKernelLocalization

open CycleQ2GeometricProjectorDefect

variable (E C : Type*) [CommRing E] [CommRing C] [Algebra E C]

attribute [local instance] localReductionAlgebra

/-- No new extension is introduced: epsilon is the inclusion of the
canonical actual kernel equivalence on the principal localization. -/
def localizedCoefficients
    (e : C ≃ₗ[E] RingHom.ker (algebraMap E C)) (t : E) :
    Coefficients (localReduction E C t) where
  epsilon := (LocalKernel E C t).subtype.toAddMonoidHom.comp
    (localizedKernelEquiv E C e t).toAddMonoidHom
  injective := by
    intro x y hxy
    apply (localizedKernelEquiv E C e t).injective
    exact Subtype.ext hxy
  reduction_epsilon x := (localizedKernelEquiv E C e t x).property
  exact_kernel z hz := by
    refine ⟨(localizedKernelEquiv E C e t).symm ⟨z, hz⟩, ?_⟩
    exact congrArg Subtype.val
      ((localizedKernelEquiv E C e t).apply_symm_apply ⟨z, hz⟩)
  mul_epsilon z x := (localizedKernelEquiv_mul E C e t z x).symm
  epsilon_mul x z := by
    change (localizedKernelEquiv E C e t x).val * z =
      (localizedKernelEquiv E C e t (x * localReduction E C t z)).val
    rw [mul_comm (localizedKernelEquiv E C e t x).val z,
      mul_comm x (localReduction E C t z)]
    exact (localizedKernelEquiv_mul E C e t z x).symm

@[simp] theorem localizedCoefficients_epsilon
    (e : C ≃ₗ[E] RingHom.ker (algebraMap E C)) (t : E)
    (x : ClosedAt E C t) :
    (localizedCoefficients E C e t).epsilon x =
      (localizedKernelEquiv E C e t x).val := rfl

/-- Coefficient extraction is the inverse of the same canonical kernel
map, not a choice of an unrelated scalar on the closed surface. -/
theorem localizedCoefficients_coefficient
    (e : C ≃ₗ[E] RingHom.ker (algebraMap E C)) (t : E)
    (z : ThickAt E t) (hz : localReduction E C t z = 0) :
    (localizedCoefficients E C e t).coefficient z hz =
      (localizedKernelEquiv E C e t).symm ⟨z, hz⟩ := by
  apply (localizedCoefficients E C e t).injective
  rw [Coefficients.epsilon_coefficient, localizedCoefficients_epsilon]
  exact (congrArg Subtype.val
    ((localizedKernelEquiv E C e t).apply_symm_apply ⟨z, hz⟩)).symm

/-- Original surface functions have exactly the original epsilon
coefficient after localization. -/
@[simp] theorem localizedCoefficients_epsilon_base
    (e : C ≃ₗ[E] RingHom.ker (algebraMap E C)) (t : E) (x : C) :
    (localizedCoefficients E C e t).epsilon
      (algebraMap C (ClosedAt E C t) x) =
      algebraMap E (ThickAt E t) (e x).val :=
  localizedKernelEquiv_base E C e t x

end CycleQ2GeometricKernelLocalization

namespace CycleQ2GeometricSurfaceFirstOrder

open CycleQ2GeometricKernelLocalization
  CycleQ2GeometricProjectorDefect

variable {R : Type*} [CommRing R]

attribute [local instance] reducedAlgebra

/-- Actual coefficients for the principal localization of the quotient
by f - epsilon a.  The normalized family proves the displayed regularity
condition by its two monic leading equations. -/
def localCoefficients (f a t : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) :=
  localizedCoefficients (Deformation f a) (Closed f)
    (kernelEquivOverDeformation f a hf) (deformationCoordinate f a t)

@[simp] theorem localCoefficients_epsilon_base (f a t : R)
    (hf : ∀ x : R, f * x = 0 → x = 0) (x : Closed f) :
    (localCoefficients f a t hf).epsilon
      (algebraMap (Closed f) (LocalClosed f a t) x) =
      @algebraMap (Deformation f a) (LocalDeformation f a t)
        (inferInstance : CommSemiring (Deformation f a))
        (inferInstance : Semiring (LocalDeformation f a t)) inferInstance (epsilon f a x) := by
  change (localKernelEquiv f a t hf
    (algebraMap (Closed f) (LocalClosed f a t) x)).val = _
  exact localKernelEquiv_base f a t hf x

/-- The matrix coefficient structure is entrywise the same faithful
actual localized epsilon map. -/
def localMatrixCoefficients (f a t : R)
    (hf : ∀ x : R, f * x = 0 → x = 0)
    (n : Type*) [Fintype n] [DecidableEq n] :=
  (localCoefficients f a t hf).matrixCoefficients n

end CycleQ2GeometricSurfaceFirstOrder

#print axioms CycleQ2GeometricKernelLocalization.localizedCoefficients
#print axioms CycleQ2GeometricKernelLocalization.localizedCoefficients_coefficient
#print axioms CycleQ2GeometricSurfaceFirstOrder.localCoefficients_epsilon_base
#print axioms CycleQ2GeometricSurfaceFirstOrder.localMatrixCoefficients

end
end SourceLocalizedProjectorCoefficients

section SourceImageProjectorCochain

/-! Projector defects act on the actual rank-one matrix image.  Their
scalar coefficients are obtained from the proved endomorphism equivalence,
and the explicit finite formula commutes with coefficient ring maps. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricRankOneImage

open Matrix CycleQ2GeometricProjectorDefect
open scoped BigOperators

variable {R m n : Type*} [CommRing R]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

@[simp] theorem projectorMatrix_mulVec_image (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1) (x : Image M) :
    (projectorMatrix M w).mulVec x.val = x.val := by
  rw [projectorMatrix, LinearMap.toMatrix'_mulVec]
  exact congrArg Subtype.val (projection_retract M hM w hw x)

/-- The output of C lies in the original image because P C = C and P
is the explicit retraction onto that image. -/
def imageEnd (M : Matrix m n R) (w : m × n → R)
    (C : Matrix m m R) (hC : projectorMatrix M w * C = C) :
    Module.End R (Image M) :=
  ((C.mulVecLin).comp (Image M).subtype).codRestrict (Image M) (by
    intro x
    have hx : (projectorMatrix M w).mulVec (C.mulVec x.val) = C.mulVec x.val := by
      rw [Matrix.mulVec_mulVec, hC]
    have hm : (projectorMatrix M w).mulVec (C.mulVec x.val) ∈ Image M := by
      rw [projectorMatrix, LinearMap.toMatrix'_mulVec]
      exact (projection M w (C.mulVec x.val)).property
    change C.mulVec x.val ∈ Image M
    exact hx ▸ hm)

@[simp] theorem imageEnd_val (M : Matrix m n R) (w : m × n → R)
    (C : Matrix m m R) (hC : projectorMatrix M w * C = C) (x : Image M) :
    (imageEnd M w C hC x).val = C.mulVec x.val := rfl

/-- The same finite formula used by End(image) = R, written on matrices
so that coefficient restriction and specialization are literal finite sums. -/
def matrixScalar (M : Matrix m n R) (w : m × n → R) :
    Matrix m m R →ₗ[R] R where
  toFun C := ∑ q, w q * (C.mulVec (M.col q.2)) q.1
  map_add' C D := by
    simp only [Matrix.add_mulVec, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c C := by
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring

theorem matrixScalar_eq_endEquiv (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → R) (hw : ∑ q, w q * M q.1 q.2 = 1)
    (C : Matrix m m R) (hC : projectorMatrix M w * C = C) :
    matrixScalar M w C = endEquiv M hM w hw (imageEnd M w C hC) := rfl

theorem scalar_certificate_independent (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w v : m × n → R)
    (hw : ∑ q, w q * M q.1 q.2 = 1) (hv : ∑ q, v q * M q.1 q.2 = 1)
    (φ : Module.End R (Image M)) : scalar M w φ = scalar M v φ := by
  have hφ : scalarMap M (scalar M v φ) = φ :=
    LinearMap.ext (scalar_reconstruction M hM v hv φ)
  calc
    scalar M w φ = scalar M w (scalarMap M (scalar M v φ)) :=
      congrArg (scalar M w) hφ.symm
    _ = scalar M v φ := scalar_scalarMap M w hw (scalar M v φ)

/-- Changing the certificate for the same image cannot change the scalar. -/
theorem matrixScalar_certificate_independent (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w v : m × n → R)
    (hw : ∑ q, w q * M q.1 q.2 = 1) (hv : ∑ q, v q * M q.1 q.2 = 1)
    (C : Matrix m m R) (hC : projectorMatrix M w * C = C) :
    matrixScalar M w C = matrixScalar M v C :=
  scalar_certificate_independent M hM w v hw hv (imageEnd M w C hC)

/-- This is direct coefficient specialization of the actual finite
formula, with no assumption about base change of endomorphism modules. -/
theorem matrixScalar_map {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix m n R) (w : m × n → R) (C : Matrix m m R) :
    f (matrixScalar M w C) =
      matrixScalar (M.map f) (fun q => f (w q)) (C.map f) := by
  change f (∑ q, w q * (C.mulVec (M.col q.2)) q.1) =
    ∑ q, f (w q) * ((C.map f).mulVec ((M.map f).col q.2)) q.1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_mul, RingHom.map_mulVec]
  rfl

/-- A matrix that vanishes on a genuine image projector has zero scalar
on the same image. -/
theorem matrixScalar_zero_of_right_zero (M : Matrix m n R)
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w v : m × n → R) (hv : ∑ q, v q * M q.1 q.2 = 1)
    (C : Matrix m m R) (hC : C * projectorMatrix M v = 0) :
    matrixScalar M w C = 0 := by
  change (∑ q, w q * (C.mulVec (M.col q.2)) q.1) = 0
  apply Finset.sum_eq_zero
  intro q _
  have h := congrArg (fun T : Matrix m m R => T.mulVec (column M q.2).val) hC
  rw [← Matrix.mulVec_mulVec, projectorMatrix_mulVec_image M hM v hv,
    Matrix.zero_mulVec] at h
  have hq := congrFun h q.1
  change (C.mulVec (M.col q.2)) q.1 = 0 at hq
  rw [hq, mul_zero]

section Family

variable {E I : Type*} [CommRing E] (ρ : E →+* R)
  (K : Coefficients (ρ.mapMatrix : Matrix m m E →+* Matrix m m R))
  (M : Matrix m n R)
  (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
  (w : I → m × n → R) (hw : ∀ i, ∑ q, w i q * M q.1 q.2 = 1)
  (e : I → Matrix m m E) (he : ∀ i, e i * e i = e i)
  (hred : ∀ i, ρ.mapMatrix (e i) = projectorMatrix M (w i))

include hM hw hred in
theorem reduced_common_image (i j : I) :
    ρ.mapMatrix (e i) * ρ.mapMatrix (e j) = ρ.mapMatrix (e j) := by
  rw [hred, hred]
  exact projectorMatrix_mul M hM (w i) (hw i) (w j)

def imageCoefficient (i j k : I) : Matrix m m R :=
  K.cochain e (reduced_common_image ρ M hM w hw e hred) i j k

include he in
theorem imageCoefficient_left (i j k : I) :
    projectorMatrix M (w i) * imageCoefficient ρ K M hM w hw e hred i j k =
      imageCoefficient ρ K M hM w hw e hred i j k := by
  rw [← hred]
  exact K.cochain_left e (reduced_common_image ρ M hM w hw e hred) he i j k

/-- The actual epsilon coefficient acts on the literal matrix image. -/
def imageCoefficientEnd (i j k : I) : Module.End R (Image M) :=
  imageEnd M (w i) (imageCoefficient ρ K M hM w hw e hred i j k)
    (imageCoefficient_left ρ K M hM w hw e he hred i j k)

/-- Any fixed certificate may extract scalars on a common overlap; the
previous independence theorem identifies the result with every local one. -/
def scalarCochain (v : m × n → R) (i j k : I) : R :=
  matrixScalar M v (imageCoefficient ρ K M hM w hw e hred i j k)

theorem scalarCochain_eq_endEquiv (i j k : I) :
    scalarCochain ρ K M hM w hw e hred (w i) i j k =
      endEquiv M hM (w i) (hw i)
        (imageCoefficientEnd ρ K M hM w hw e he hred i j k) := rfl

include he in
/-- The actual epsilon-extracted scalar is a two-cocycle on each common
overlap. No quotient class or desired nonzero vector has been selected. -/
theorem scalarCochain_cocycle (v : m × n → R) (i j k l : I) :
    scalarCochain ρ K M hM w hw e hred v j k l -
      scalarCochain ρ K M hM w hw e hred v i k l +
      scalarCochain ρ K M hM w hw e hred v i j l -
      scalarCochain ρ K M hM w hw e hred v i j k = 0 := by
  have h := K.cochain_cocycle_on_image e
    (reduced_common_image ρ M hM w hw e hred) he i j k l
    (ρ.mapMatrix (e l)) (fun a => reduced_common_image ρ M hM w hw e hred a l)
  rw [hred] at h
  have hs := matrixScalar_zero_of_right_zero M hM v (w l) (hw l) _ h
  simpa only [scalarCochain, imageCoefficient, map_sub, map_add] using hs

include he in
/-- The mixed-projector prism becomes a literal scalar Cech boundary
after restricting to the same actual image. -/
theorem scalarCochain_prism {J : Type*} (v : m × n → R)
    (f g : J → I) (i j k : J) :
    scalarCochain ρ K M hM w hw e hred v (g i) (g j) (g k) -
      scalarCochain ρ K M hM w hw e hred v (f i) (f j) (f k) =
      prismCorrection (scalarCochain ρ K M hM w hw e hred v) f g j k -
        prismCorrection (scalarCochain ρ K M hM w hw e hred v) f g i k +
        prismCorrection (scalarCochain ρ K M hM w hw e hred v) f g i j :=
  prism_boundary _ (scalarCochain_cocycle ρ K M hM w hw e he hred v) f g i j k

end Family
end CycleQ2GeometricRankOneImage

#print axioms CycleQ2GeometricRankOneImage.imageEnd
#print axioms CycleQ2GeometricRankOneImage.matrixScalar_eq_endEquiv
#print axioms CycleQ2GeometricRankOneImage.matrixScalar_certificate_independent
#print axioms CycleQ2GeometricRankOneImage.matrixScalar_map
#print axioms CycleQ2GeometricRankOneImage.scalarCochain_cocycle
#print axioms CycleQ2GeometricRankOneImage.scalarCochain_prism

end
end SourceImageProjectorCochain

section SourceProjectorMatrixNaturality

/-! The actual finite matrix formula commutes with ring maps.  An explicit
idempotent correction stays in a specified subring, so a later degree-zero
lift does not lose its grading through an arbitrary idempotent choice. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricRankOneImage

open Matrix
open scoped BigOperators

variable {R S m n : Type*} [CommRing R] [CommRing S]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

theorem projectorMatrix_apply (M : Matrix m n R) (w : m × n → R) (i k : m) :
    projectorMatrix M w i k = ∑ j, w (k,j) * M i j := by
  classical
  rw [projectorMatrix, LinearMap.toMatrix'_apply]
  change (∑ q : m × n, (w q * (Pi.single k (1 : R) : m → R) q.1) • column M q.2).val i = _
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, column_val, Fintype.sum_prod_type]
  simp [Pi.single_apply, mul_ite, eq_comm]

/-- Restriction and coefficient specialization act on the original finite
formula, without choosing an equivalence of base-changed endomorphisms. -/
theorem projectorMatrix_map (f : R →+* S) (M : Matrix m n R) (w : m × n → R) :
    (projectorMatrix M w).map f = projectorMatrix (M.map f) (fun q => f (w q)) := by
  ext i k
  simp only [Matrix.map_apply, projectorMatrix_apply, map_sum, map_mul]

end CycleQ2GeometricRankOneImage

namespace CycleQ2GeometricProjectorDefect

variable {E R : Type*} [Ring E] [Ring R]

/-- The polynomial 3x²−2x³, written so that its reduction is immediate. -/
def idempotentCorrection (x : E) : E :=
  x + (1 - x - x) * (x * x - x)

theorem idempotentCorrection_defect (x : E) :
    idempotentCorrection x * idempotentCorrection x - idempotentCorrection x =
      (x * x - x) * (x * x - x) * (4 * x * x - 4 * x - 3) := by
  unfold idempotentCorrection
  noncomm_ring

theorem idempotentCorrection_idempotent (x : E)
    (hx : (x * x - x) * (x * x - x) = 0) :
    IsIdempotentElem (idempotentCorrection x) := by
  apply sub_eq_zero.mp
  rw [idempotentCorrection_defect, hx, zero_mul]

theorem idempotentCorrection_reduction (ρ : E →+* R) (x : E)
    (h : ρ x * ρ x = ρ x) : ρ (idempotentCorrection x) = ρ x := by
  simp only [idempotentCorrection, map_add, map_mul, map_sub, map_one,
    h, sub_self, mul_zero, add_zero]

/-- A chosen degree-zero subring is preserved by the explicit correction. -/
theorem idempotentCorrection_mem (A : Subring E) (x : E) (hx : x ∈ A) :
    idempotentCorrection x ∈ A :=
  A.add_mem hx (A.mul_mem (A.sub_mem (A.sub_mem A.one_mem hx) hx)
    (A.sub_mem (A.mul_mem hx hx) hx))

/-- The square-zero reduction hypothesis supplies the correction identity;
the initial lift and its subring membership stay in the conclusion. -/
theorem explicit_idempotent_lift_in_subring (ρ : E →+* R)
    (hker : ∀ x y, ρ x = 0 → ρ y = 0 → x * y = 0)
    (A : Subring E) (p : R) (hp : p * p = p)
    (x : E) (hx : x ∈ A) (hred : ρ x = p) :
    IsIdempotentElem (idempotentCorrection x) ∧
      idempotentCorrection x ∈ A ∧ ρ (idempotentCorrection x) = p := by
  have hz : ρ (x * x - x) = 0 := by
    rw [map_sub, map_mul, hred, hp, sub_self]
  refine ⟨idempotentCorrection_idempotent x (hker _ _ hz hz),
    idempotentCorrection_mem A x hx, ?_⟩
  rw [idempotentCorrection_reduction ρ x (by simpa only [hred] using hp), hred]

end CycleQ2GeometricProjectorDefect
end

#print axioms CycleQ2GeometricRankOneImage.projectorMatrix_apply
#print axioms CycleQ2GeometricRankOneImage.projectorMatrix_map
#print axioms CycleQ2GeometricProjectorDefect.explicit_idempotent_lift_in_subring

end SourceProjectorMatrixNaturality

section SourceUniversalSurfaceLocalDeformation

/-! The genuine normalized-family square-zero extension on the original
coordinate localizations.  The closed-local ring is identified by the
original polynomial quotient and the actual coordinate denominator,
and its coefficient interface retains the same epsilon normalization. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricUniversalSurfaceFirstOrder

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions
  CycleQ2GeometricSurfaceFirstOrder CycleQ2GeometricKernelLocalization
  CycleQ2GeometricProjectorDefect

open scoped BigOperators

attribute [local instance] cubicSelfModule cubicOppositeModule
  cubicCentralScalar cubicSmulCommClass surfaceDeformationModule
  surfaceDeformationCubicModule reducedAlgebra

variable (R : Type*) [CommRing R]
  (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
  (A : MvPolynomial (Fin 5) R)

/-- The original product of base coordinates, in the actual quotient by h. -/
def coordinateClass (s : Finset (Fin 3)) : CubicQuotient R hcoeff :=
  testClass R hcoeff (remainingInclusion R (baseProduct R s))

abbrev LocalSurfaceDeformation (s : Finset (Fin 3)) :=
  LocalDeformation (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
    (coordinateClass R hcoeff s)

abbrev LocalSurfaceClosed (s : Finset (Fin 3)) :=
  LocalClosed (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
    (coordinateClass R hcoeff s)

@[simp] theorem closedSurfaceEquiv_coordinate (s : Finset (Fin 3)) :
    closedSurfaceEquiv R hcoeff Fcoeff
      (@algebraMap (SurfaceDeformation R hcoeff Fcoeff A)
        (Closed (sexticClass R hcoeff Fcoeff))
        (inferInstance : CommSemiring (SurfaceDeformation R hcoeff Fcoeff A))
        (inferInstance : Semiring (Closed (sexticClass R hcoeff Fcoeff)))
        (reducedAlgebra (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A))
        (deformationCoordinate (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
          (coordinateClass R hcoeff s))) =
      algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s) := rfl

/-- The closed-fibre coordinate localization is the original universal
surface localization, with no independent choice of basis or quotient map. -/
def localClosedSurfaceEquiv (s : Finset (Fin 3)) :
    LocalSurfaceClosed R hcoeff Fcoeff A s ≃+* SurfaceLocal R hcoeff Fcoeff s :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers
      (@algebraMap (SurfaceDeformation R hcoeff Fcoeff A)
        (Closed (sexticClass R hcoeff Fcoeff))
        (inferInstance : CommSemiring (SurfaceDeformation R hcoeff Fcoeff A))
        (inferInstance : Semiring (Closed (sexticClass R hcoeff Fcoeff)))
        (reducedAlgebra (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A))
        (deformationCoordinate (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
          (coordinateClass R hcoeff s))))
    (T := Submonoid.powers
      (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s)))
    (LocalSurfaceClosed R hcoeff Fcoeff A s) (SurfaceLocal R hcoeff Fcoeff s)
    (closedSurfaceEquiv R hcoeff Fcoeff).toRingEquiv
    (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers (closedSurfaceEquiv_coordinate R hcoeff Fcoeff A s))

@[simp] theorem localClosedSurfaceEquiv_base (s : Finset (Fin 3))
    (z : Closed (sexticClass R hcoeff Fcoeff)) :
    localClosedSurfaceEquiv R hcoeff Fcoeff A s
      (algebraMap (Closed (sexticClass R hcoeff Fcoeff))
        (LocalSurfaceClosed R hcoeff Fcoeff A s) z) =
      algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s)
        (closedSurfaceEquiv R hcoeff Fcoeff z) := by
  unfold localClosedSurfaceEquiv
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (S := LocalSurfaceClosed R hcoeff Fcoeff A s)
    (Q := SurfaceLocal R hcoeff Fcoeff s)
    (j := (closedSurfaceEquiv R hcoeff Fcoeff).toRingEquiv) _ z

/-- Reduction into the actual original coordinate-local surface ring. -/
def localSurfaceReduction (s : Finset (Fin 3)) :
    LocalSurfaceDeformation R hcoeff Fcoeff A s →+* SurfaceLocal R hcoeff Fcoeff s :=
  (localClosedSurfaceEquiv R hcoeff Fcoeff A s).toRingHom.comp
    (localReduction (SurfaceDeformation R hcoeff Fcoeff A)
      (Closed (sexticClass R hcoeff Fcoeff))
      (deformationCoordinate (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
        (coordinateClass R hcoeff s)))

theorem localSurfaceReduction_surjective (s : Finset (Fin 3)) :
    Function.Surjective (localSurfaceReduction R hcoeff Fcoeff A s) :=
  (localClosedSurfaceEquiv R hcoeff Fcoeff A s).surjective.comp
    (localReduction_surjective (SurfaceDeformation R hcoeff Fcoeff A)
      (Closed (sexticClass R hcoeff Fcoeff))
      (reduction_surjective (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A))
      (deformationCoordinate (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
        (coordinateClass R hcoeff s)))

/-- The coefficient map is transported along the actual closed-fibre
quotient/localization identity.  Regularity is a proved family theorem. -/
def localSurfaceCoefficients [Nontrivial R] (s : Finset (Fin 3)) :
    Coefficients (localSurfaceReduction R hcoeff Fcoeff A s) := by
  let e := localClosedSurfaceEquiv R hcoeff Fcoeff A s
  let ρ : LocalSurfaceDeformation R hcoeff Fcoeff A s →+*
      LocalSurfaceClosed R hcoeff Fcoeff A s :=
    localReduction (SurfaceDeformation R hcoeff Fcoeff A)
      (Closed (sexticClass R hcoeff Fcoeff))
      (deformationCoordinate (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
        (coordinateClass R hcoeff s))
  let K := localCoefficients (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
    (coordinateClass R hcoeff s) (sexticClass_regular R hcoeff Fcoeff)
  refine
    { epsilon := K.epsilon.comp e.symm.toAddMonoidHom
      injective := K.injective.comp e.symm.injective
      reduction_epsilon := ?_
      exact_kernel := ?_
      mul_epsilon := ?_
      epsilon_mul := ?_ }
  · intro x
    change e (ρ (K.epsilon (e.symm x))) = 0
    rw [K.reduction_epsilon, map_zero]
  · intro z hz
    change e (ρ z) = 0 at hz
    have hz' : ρ z = 0 := e.injective (hz.trans (map_zero e).symm)
    obtain ⟨x, hx⟩ := K.exact_kernel z hz'
    refine ⟨e x, ?_⟩
    change K.epsilon (e.symm (e x)) = z
    rw [e.symm_apply_apply, hx]
  · intro z x
    change z * K.epsilon (e.symm x) = K.epsilon (e.symm (e (ρ z) * x))
    rw [K.mul_epsilon, e.symm.map_mul, e.symm_apply_apply]
  · intro x z
    change K.epsilon (e.symm x) * z = K.epsilon (e.symm (x * e (ρ z)))
    rw [K.epsilon_mul, e.symm.map_mul, e.symm_apply_apply]

/-- The exact localized epsilon map on original polynomial classes. -/
@[simp] theorem localSurfaceCoefficients_epsilon_base [Nontrivial R]
    (s : Finset (Fin 3)) (x : SurfaceRing R hcoeff Fcoeff) :
    (localSurfaceCoefficients R hcoeff Fcoeff A s).epsilon
      (algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) x) =
      @algebraMap (SurfaceDeformation R hcoeff Fcoeff A)
        (LocalSurfaceDeformation R hcoeff Fcoeff A s)
        (inferInstance : CommSemiring (SurfaceDeformation R hcoeff Fcoeff A))
        (inferInstance : Semiring (LocalSurfaceDeformation R hcoeff Fcoeff A s))
        inferInstance (surfaceEpsilon R hcoeff Fcoeff A x) := by
  have he := localClosedSurfaceEquiv_base R hcoeff Fcoeff A s
    ((closedSurfaceEquiv R hcoeff Fcoeff).symm x)
  rw [AlgEquiv.apply_symm_apply] at he
  rw [← he]
  change (localCoefficients (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
    (coordinateClass R hcoeff s) (sexticClass_regular R hcoeff Fcoeff)).epsilon
      ((localClosedSurfaceEquiv R hcoeff Fcoeff A s).symm
        (localClosedSurfaceEquiv R hcoeff Fcoeff A s _)) = _
  rw [RingEquiv.symm_apply_apply, localCoefficients_epsilon_base]
  rfl

theorem localSurface_kernel_mul_zero [Nontrivial R] (s : Finset (Fin 3))
    (x y : LocalSurfaceDeformation R hcoeff Fcoeff A s)
    (hx : localSurfaceReduction R hcoeff Fcoeff A s x = 0)
    (hy : localSurfaceReduction R hcoeff Fcoeff A s y = 0) : x * y = 0 := by
  let K := localSurfaceCoefficients R hcoeff Fcoeff A s
  obtain ⟨a, rfl⟩ := K.exact_kernel x hx
  obtain ⟨b, rfl⟩ := K.exact_kernel y hy
  exact K.epsilon_mul_epsilon a b

/-- The actual normalized-family image projector lifts on every
coordinate open where its actual entries generate the unit ideal. -/
theorem exists_localSurface_image_projector [Nontrivial R]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (s : Finset (Fin 3)) (M : Matrix m n (SurfaceLocal R hcoeff Fcoeff s))
    (hM : ∀ i j k l, M i j * M k l = M k j * M i l)
    (w : m × n → SurfaceLocal R hcoeff Fcoeff s)
    (hw : ∑ q, w q * M q.1 q.2 = 1) :
    ∃ Q : Matrix m m (LocalSurfaceDeformation R hcoeff Fcoeff A s),
      IsIdempotentElem Q ∧
        (localSurfaceReduction R hcoeff Fcoeff A s).mapMatrix Q =
          CycleQ2GeometricRankOneImage.projectorMatrix M w :=
  CycleQ2GeometricRankOneImage.exists_image_projector_lift
    (localSurfaceReduction R hcoeff Fcoeff A s)
    (localSurfaceReduction_surjective R hcoeff Fcoeff A s)
    (localSurface_kernel_mul_zero R hcoeff Fcoeff A s) M hM w hw

end CycleQ2GeometricUniversalSurfaceFirstOrder

#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.localClosedSurfaceEquiv_base
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.localSurfaceCoefficients
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.localSurfaceCoefficients_epsilon_base
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.exists_localSurface_image_projector


namespace CycleQ2GeometricKernelLocalization

variable (E C : Type*) [CommRing E] [CommRing C] [Algebra E C]

attribute [local instance] localReductionAlgebra

theorem restriction_isUnit {t u : E} (htu : t ∣ u) :
    IsUnit (algebraMap E (ThickAt E u) t) :=
  IsLocalization.Away.isUnit_of_dvd (S := ThickAt E u) u htu

def thickRestriction {t u : E} (htu : t ∣ u) :
    ThickAt E t →ₐ[E] ThickAt E u :=
  IsLocalization.Away.liftAlgHom t (f := Algebra.ofId E (ThickAt E u))
    (restriction_isUnit E htu)

@[simp] theorem thickRestriction_base {t u : E} (htu : t ∣ u) (x : E) :
    thickRestriction E htu (algebraMap E (ThickAt E t) x) =
      algebraMap E (ThickAt E u) x :=
  IsLocalization.Away.lift_eq t (restriction_isUnit E htu) x

def closedRestriction {t u : E} (htu : t ∣ u) :
    ClosedAt E C t →ₐ[C] ClosedAt E C u :=
  IsLocalization.Away.liftAlgHom (algebraMap E C t)
    (f := Algebra.ofId C (ClosedAt E C u))
    (IsLocalization.Away.isUnit_of_dvd (S := ClosedAt E C u)
      (algebraMap E C u) (map_dvd (algebraMap E C) htu))

@[simp] theorem closedRestriction_base {t u : E} (htu : t ∣ u) (x : C) :
    closedRestriction E C htu (algebraMap C (ClosedAt E C t) x) =
      algebraMap C (ClosedAt E C u) x :=
  IsLocalization.Away.lift_eq (algebraMap E C t)
    (IsLocalization.Away.isUnit_of_dvd (S := ClosedAt E C u)
      (algebraMap E C u) (map_dvd (algebraMap E C) htu)) x

/-- The two actual ring restrictions form a commuting square with
the actual localized reduction. -/
theorem localReduction_restriction {t u : E} (htu : t ∣ u)
    (x : ThickAt E t) :
    localReduction E C u (thickRestriction E htu x) =
      closedRestriction E C htu (localReduction E C t x) := by
  have h : (localReduction E C u).comp (thickRestriction E htu).toRingHom =
      (closedRestriction E C htu).toRingHom.comp (localReduction E C t) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    apply RingHom.ext
    intro b
    change localReduction E C u
        (thickRestriction E htu (algebraMap E (ThickAt E t) b)) =
      closedRestriction E C htu
        (localReduction E C t (algebraMap E (ThickAt E t) b))
    rw [thickRestriction_base, localReduction_base, localReduction_base,
      closedRestriction_base]
  exact congrArg (fun f : ThickAt E t →+* ClosedAt E C u => f x) h

/-- Canonical ε coefficients commute with restriction to every smaller
principal open. The equality uses the original kernel identification e
on both opens, and follows from localization uniqueness. -/
theorem localizedKernelEquiv_restriction
    (e : C ≃ₗ[E] RingHom.ker (algebraMap E C))
    {t u : E} (htu : t ∣ u) (x : ClosedAt E C t) :
    thickRestriction E htu (localizedKernelEquiv E C e t x).val =
      (localizedKernelEquiv E C e u (closedRestriction E C htu x)).val := by
  let ηt : ClosedAt E C t →ₗ[E] ThickAt E t :=
    ((LocalKernel E C t).subtype.restrictScalars E).comp
      ((localizedKernelEquiv E C e t).toLinearMap.restrictScalars E)
  let ηu : ClosedAt E C u →ₗ[E] ThickAt E u :=
    ((LocalKernel E C u).subtype.restrictScalars E).comp
      ((localizedKernelEquiv E C e u).toLinearMap.restrictScalars E)
  let L : ClosedAt E C t →ₗ[E] ThickAt E u :=
    (thickRestriction E htu).toLinearMap.comp ηt
  let Q : ClosedAt E C t →ₗ[E] ThickAt E u :=
    ηu.comp ((closedRestriction E C htu).toLinearMap.restrictScalars E)
  have hu : ∀ s : Submonoid.powers t,
      IsUnit (algebraMap E (Module.End E (ThickAt E u)) s) := by
    rintro ⟨s, n, rfl⟩
    have hs : IsUnit (algebraMap E (ThickAt E u) (t ^ n)) := by
      rw [map_pow]
      exact (restriction_isUnit E htu).pow n
    simpa only [AlgHom.commutes] using hs.map (Algebra.lmul E (ThickAt E u))
  have heq : L = Q := by
    apply IsLocalizedModule.ext (Submonoid.powers t) (closedMap E C t) hu
    ext b
    change thickRestriction E htu
      (localizedKernelEquiv E C e t (algebraMap C (ClosedAt E C t) b)).val =
      (localizedKernelEquiv E C e u
        (closedRestriction E C htu (algebraMap C (ClosedAt E C t) b))).val
    rw [localizedKernelEquiv_base, thickRestriction_base, closedRestriction_base,
      localizedKernelEquiv_base]
  exact congrArg (fun f : ClosedAt E C t →ₗ[E] ThickAt E u => f x) heq

end CycleQ2GeometricKernelLocalization

namespace CycleQ2GeometricUniversalSurfaceFirstOrder

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions
  CycleQ2GeometricSurfaceFirstOrder CycleQ2GeometricKernelLocalization
  CycleQ2GeometricProjectorDefect

attribute [local instance] cubicSelfModule cubicOppositeModule
  cubicCentralScalar cubicSmulCommClass surfaceDeformationModule
  surfaceDeformationCubicModule reducedAlgebra

variable (R : Type*) [CommRing R]
  (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
  (A : MvPolynomial (Fin 5) R)

theorem coordinateClass_dvd {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    coordinateClass R hcoeff s ∣ coordinateClass R hcoeff t :=
  map_dvd ((Ideal.Quotient.mk (cubicIdeal R hcoeff)).comp
    (remainingInclusion R).toRingHom) (baseProduct_dvd R hst)

theorem deformationCoordinate_dvd {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    deformationCoordinate (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
        (coordinateClass R hcoeff s) ∣
      deformationCoordinate (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
        (coordinateClass R hcoeff t) :=
  map_dvd
    ((Ideal.Quotient.mk
      (deformationIdeal (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A))).comp
        (TrivSqZeroExt.inlHom (CubicQuotient R hcoeff) (CubicQuotient R hcoeff)))
    (coordinateClass_dvd R hcoeff hst)

/-- Restriction on the actual deformed coordinate opens. -/
def localSurfaceRestriction {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    LocalSurfaceDeformation R hcoeff Fcoeff A s →+*
      LocalSurfaceDeformation R hcoeff Fcoeff A t :=
  (thickRestriction (SurfaceDeformation R hcoeff Fcoeff A)
    (deformationCoordinate_dvd R hcoeff Fcoeff A hst)).toRingHom

/-- The actual closed-localization identity commutes with the original
universal surface restriction maps. -/
theorem localClosedSurfaceEquiv_restriction {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (x : LocalSurfaceClosed R hcoeff Fcoeff A s) :
    localClosedSurfaceEquiv R hcoeff Fcoeff A t
      (closedRestriction (SurfaceDeformation R hcoeff Fcoeff A)
        (Closed (sexticClass R hcoeff Fcoeff))
        (deformationCoordinate_dvd R hcoeff Fcoeff A hst) x) =
      restriction R hcoeff Fcoeff hst (localClosedSurfaceEquiv R hcoeff Fcoeff A s x) := by
  have heq : (localClosedSurfaceEquiv R hcoeff Fcoeff A t).toRingHom.comp
      (closedRestriction (SurfaceDeformation R hcoeff Fcoeff A)
        (Closed (sexticClass R hcoeff Fcoeff))
        (deformationCoordinate_dvd R hcoeff Fcoeff A hst)).toRingHom =
      (restriction R hcoeff Fcoeff hst).comp
        (localClosedSurfaceEquiv R hcoeff Fcoeff A s).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers
      (reduction (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
        (deformationCoordinate (sexticClass R hcoeff Fcoeff) (testClass R hcoeff A)
          (coordinateClass R hcoeff s))))
    apply RingHom.ext
    intro b
    change localClosedSurfaceEquiv R hcoeff Fcoeff A t
        (closedRestriction (SurfaceDeformation R hcoeff Fcoeff A)
          (Closed (sexticClass R hcoeff Fcoeff))
          (deformationCoordinate_dvd R hcoeff Fcoeff A hst)
          (algebraMap (Closed (sexticClass R hcoeff Fcoeff))
            (LocalSurfaceClosed R hcoeff Fcoeff A s) b)) =
      restriction R hcoeff Fcoeff hst
        (localClosedSurfaceEquiv R hcoeff Fcoeff A s
          (algebraMap (Closed (sexticClass R hcoeff Fcoeff))
            (LocalSurfaceClosed R hcoeff Fcoeff A s) b))
    rw [closedRestriction_base, localClosedSurfaceEquiv_base,
      localClosedSurfaceEquiv_base, restriction_algebraMap]
  exact RingHom.congr_fun heq x

theorem localSurfaceReduction_restriction {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (z : LocalSurfaceDeformation R hcoeff Fcoeff A s) :
    localSurfaceReduction R hcoeff Fcoeff A t (localSurfaceRestriction R hcoeff Fcoeff A hst z) =
      restriction R hcoeff Fcoeff hst (localSurfaceReduction R hcoeff Fcoeff A s z) := by
  unfold localSurfaceReduction localSurfaceRestriction
  change localClosedSurfaceEquiv R hcoeff Fcoeff A t
      (localReduction (SurfaceDeformation R hcoeff Fcoeff A)
        (Closed (sexticClass R hcoeff Fcoeff)) _
        (thickRestriction (SurfaceDeformation R hcoeff Fcoeff A)
          (deformationCoordinate_dvd R hcoeff Fcoeff A hst) z)) =
    restriction R hcoeff Fcoeff hst
      (localClosedSurfaceEquiv R hcoeff Fcoeff A s
        (localReduction (SurfaceDeformation R hcoeff Fcoeff A)
          (Closed (sexticClass R hcoeff Fcoeff)) _ z))
  rw [localReduction_restriction]
  exact localClosedSurfaceEquiv_restriction R hcoeff Fcoeff A hst _

/-- The same actual epsilon coefficient is used on every coordinate
intersection. This is a square of actual ring restriction maps. -/
theorem localSurfaceEpsilon_restriction [Nontrivial R]
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (x : SurfaceLocal R hcoeff Fcoeff s) :
    localSurfaceRestriction R hcoeff Fcoeff A hst
      ((localSurfaceCoefficients R hcoeff Fcoeff A s).epsilon x) =
      (localSurfaceCoefficients R hcoeff Fcoeff A t).epsilon
        (restriction R hcoeff Fcoeff hst x) := by
  let es := localClosedSurfaceEquiv R hcoeff Fcoeff A s
  let et := localClosedSurfaceEquiv R hcoeff Fcoeff A t
  have hc : closedRestriction (SurfaceDeformation R hcoeff Fcoeff A)
      (Closed (sexticClass R hcoeff Fcoeff))
      (deformationCoordinate_dvd R hcoeff Fcoeff A hst) (es.symm x) =
      et.symm (restriction R hcoeff Fcoeff hst x) := by
    apply et.injective
    rw [RingEquiv.apply_symm_apply]
    change localClosedSurfaceEquiv R hcoeff Fcoeff A t _ = _
    rw [localClosedSurfaceEquiv_restriction]
    exact congrArg (restriction R hcoeff Fcoeff hst) (es.apply_symm_apply x)
  change thickRestriction (SurfaceDeformation R hcoeff Fcoeff A)
      (deformationCoordinate_dvd R hcoeff Fcoeff A hst)
      (localizedKernelEquiv (SurfaceDeformation R hcoeff Fcoeff A)
        (Closed (sexticClass R hcoeff Fcoeff))
        (kernelEquivOverDeformation (sexticClass R hcoeff Fcoeff)
          (testClass R hcoeff A) (sexticClass_regular R hcoeff Fcoeff))
        _ (es.symm x)).val =
    (localizedKernelEquiv (SurfaceDeformation R hcoeff Fcoeff A)
      (Closed (sexticClass R hcoeff Fcoeff))
      (kernelEquivOverDeformation (sexticClass R hcoeff Fcoeff)
        (testClass R hcoeff A) (sexticClass_regular R hcoeff Fcoeff))
      _ (et.symm (restriction R hcoeff Fcoeff hst x))).val
  rw [localizedKernelEquiv_restriction, hc]

/-- Canonical extraction of the coefficient of the same kernel element
commutes with restriction to any smaller original coordinate open. -/
theorem localSurfaceCoefficient_restriction [Nontrivial R]
    {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (z : LocalSurfaceDeformation R hcoeff Fcoeff A s)
    (hz : localSurfaceReduction R hcoeff Fcoeff A s z = 0) :
    (localSurfaceCoefficients R hcoeff Fcoeff A t).coefficient
        (localSurfaceRestriction R hcoeff Fcoeff A hst z)
        (by rw [localSurfaceReduction_restriction, hz, map_zero]) =
      restriction R hcoeff Fcoeff hst
        ((localSurfaceCoefficients R hcoeff Fcoeff A s).coefficient z hz) := by
  apply (localSurfaceCoefficients R hcoeff Fcoeff A t).injective
  rw [Coefficients.epsilon_coefficient, ← localSurfaceEpsilon_restriction,
    Coefficients.epsilon_coefficient]

end CycleQ2GeometricUniversalSurfaceFirstOrder

#print axioms CycleQ2GeometricKernelLocalization.localizedKernelEquiv_restriction
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.localClosedSurfaceEquiv_restriction
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.localSurfaceReduction_restriction
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.localSurfaceEpsilon_restriction
#print axioms CycleQ2GeometricUniversalSurfaceFirstOrder.localSurfaceCoefficient_restriction

end
end SourceUniversalSurfaceLocalDeformation
