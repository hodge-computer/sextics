import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Proposal.GeometricRegularDeRham

/-!
# Regular de Rham restriction on the actual principal-open basis

This source-only continuation constructs restriction maps for inclusions
`D(t) ≤ D(s)` in the spectrum of the actual normal-Jacobian coordinate
ring. The maps on functions are the universal localization maps. The maps
on one-forms are the canonical maps of Kähler modules, and those on higher
forms are induced by the universal alternating property of exterior powers.

All four differentials commute with these restrictions. On nonempty
principal opens the actual complexes therefore form a contravariant
functor, with the protected residue classes compatible under restriction.
This is a diagram on the principal-open basis. It does not assert the
sheaf gluing theorem, a sheaf-hypercohomology comparison, or the algebraic
de Rham comparison with Betti cohomology.

The `CycleQ2GeometricRationalSpread` namespace then clears the finite
coefficients of rational forms. It identifies the filtered colimit of
these regular top-cohomology groups with the original function-field
quotient, and identifies the protected exactness assertion with regular
vanishing on some smaller nonempty principal open. It does not establish
that vanishing.

No Lean elaboration, compilation, or kernel replay was run for this file.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

noncomputable section

namespace CycleQ2GeometricPrincipalRestriction

open CategoryTheory
open scoped BigOperators
open MvPolynomial HodgeComputer CycleQ2AffineClearing
open CycleQ2GeometricRegularDeRham

/-- The inclusion of the actual principal opens, in its geometric direction. -/
abbrev Inclusion (s t : OpenRing) : Prop :=
  PrimeSpectrum.basicOpen t ≤ PrimeSpectrum.basicOpen s

/-- The localization universal property applies because the source
denominator is a unit on the smaller principal open. -/
def functionRestriction (s t : OpenRing) (h : Inclusion s t) :
    LocalRing s →ₐ[ℂ] LocalRing t :=
  IsLocalization.Away.liftAlgHom s
    (f := IsScalarTower.toAlgHom ℂ OpenRing (LocalRing t))
    ((PrimeSpectrum.basicOpen_le_basicOpen_iff_algebraMap_isUnit
      (S := LocalRing t)).mp h)

@[simp] theorem functionRestriction_algebraMap (s t : OpenRing)
    (h : Inclusion s t) (a : OpenRing) :
    functionRestriction s t h (algebraMap OpenRing (LocalRing s) a) =
      algebraMap OpenRing (LocalRing t) a :=
  IsLocalization.lift_eq _ a

@[simp] theorem functionRestriction_polynomial (s t : OpenRing)
    (h : Inclusion s t) (P : AmbientPoly 4) :
    functionRestriction s t h (localPolynomial s P) = localPolynomial t P :=
  functionRestriction_algebraMap s t h _

@[simp] theorem functionRestriction_normalInverse (s t : OpenRing)
    (h : Inclusion s t) :
    functionRestriction s t h (localNormalInverse s) = localNormalInverse t :=
  functionRestriction_algebraMap s t h _

theorem functionRestriction_id (s : OpenRing) :
    functionRestriction s s le_rfl = AlgHom.id ℂ (LocalRing s) := by
  apply IsLocalization.algHom_ext (Submonoid.powers s)
  apply AlgHom.ext
  intro a
  exact functionRestriction_algebraMap s s le_rfl a

theorem functionRestriction_comp (s t u : OpenRing)
    (hst : Inclusion s t) (htu : Inclusion t u) :
    (functionRestriction t u htu).comp (functionRestriction s t hst) =
      functionRestriction s u (htu.trans hst) := by
  apply IsLocalization.algHom_ext (Submonoid.powers s)
  apply AlgHom.ext
  intro a
  change functionRestriction t u htu
      (functionRestriction s t hst (algebraMap OpenRing (LocalRing s) a)) =
    functionRestriction s u (htu.trans hst)
      (algebraMap OpenRing (LocalRing s) a)
  simp only [functionRestriction_algebraMap]

/-- Restriction through any smaller nonempty principal open agrees with
restriction to the already fixed function field. -/
@[simp] theorem functionRestriction_toGeneric (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (a : LocalRing s) :
    localFunctionFieldMap t ht (functionRestriction s t h a) =
      localFunctionFieldMap s hs a := by
  have hm : (localFunctionFieldMap t ht).comp (functionRestriction s t h) =
      localFunctionFieldMap s hs := by
    apply IsLocalization.algHom_ext (Submonoid.powers s)
    apply AlgHom.ext
    intro b
    change localFunctionFieldMap t ht
        (functionRestriction s t h (algebraMap OpenRing (LocalRing s) b)) =
      localFunctionFieldMap s hs (algebraMap OpenRing (LocalRing s) b)
    simp only [functionRestriction_algebraMap, localFunctionFieldMap_algebraMap]
  exact congrArg (fun f : LocalRing s →ₐ[ℂ] K => f a) hm

theorem functionRestriction_injective (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) :
    Function.Injective (functionRestriction s t h) := by
  intro a b hab
  apply localFunctionFieldMap_injective s hs
  simpa only [functionRestriction_toGeneric s t hs ht h] using
    congrArg (localFunctionFieldMap t ht) hab

private def restrictionAlgebra (s t : OpenRing) (h : Inclusion s t) :
    Algebra (LocalRing s) (LocalRing t) :=
  (functionRestriction s t h).toRingHom.toAlgebra

private theorem restrictionTower (s t : OpenRing) (h : Inclusion s t) :
    letI := restrictionAlgebra s t h
    IsScalarTower ℂ (LocalRing s) (LocalRing t) := by
  letI := restrictionAlgebra s t h
  constructor
  intro c a z
  change functionRestriction s t h (c • a) * z =
    c • (functionRestriction s t h a * z)
  have hsmul : functionRestriction s t h (c • a) =
      c • functionRestriction s t h a :=
    (functionRestriction s t h).toLinearMap.map_smul c a
  rw [hsmul]
  exact smul_mul_assoc c (functionRestriction s t h a) z

/-- Canonical restriction of the actual universal Kähler one-forms. -/
def oneFormRestriction (s t : OpenRing) (h : Inclusion s t) :
    Omega s →ₗ[ℂ] Omega t := by
  letI := restrictionAlgebra s t h
  letI := restrictionTower s t h
  exact (KaehlerDifferential.map ℂ ℂ (LocalRing s) (LocalRing t)).restrictScalars ℂ

@[simp] theorem oneFormRestriction_d (s t : OpenRing)
    (h : Inclusion s t) (a : LocalRing s) :
    oneFormRestriction s t h (d s a) =
      d t (functionRestriction s t h a) := by
  letI := restrictionAlgebra s t h
  letI := restrictionTower s t h
  exact KaehlerDifferential.map_D ℂ ℂ (LocalRing s) (LocalRing t) a

@[simp] theorem oneFormRestriction_smul (s t : OpenRing)
    (h : Inclusion s t) (a : LocalRing s) (ω : Omega s) :
    oneFormRestriction s t h (a • ω) =
      functionRestriction s t h a • oneFormRestriction s t h ω := by
  letI := restrictionAlgebra s t h
  letI := restrictionTower s t h
  change KaehlerDifferential.map ℂ ℂ (LocalRing s) (LocalRing t) (a • ω) =
    algebraMap (LocalRing s) (LocalRing t) a •
      KaehlerDifferential.map ℂ ℂ (LocalRing s) (LocalRing t) ω
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul (R := LocalRing s) (A := LocalRing t) a
    (KaehlerDifferential.map ℂ ℂ (LocalRing s) (LocalRing t) ω)).symm

@[simp] theorem oneFormRestriction_basis (s t : OpenRing)
    (h : Inclusion s t) (i : Fin 4) :
    oneFormRestriction s t h (coordinateBasis s i) = coordinateBasis t i := by
  rw [coordinateBasis_apply, oneFormRestriction_d,
    functionRestriction_polynomial, coordinateBasis_apply]

theorem oneFormRestriction_coordinates (s t : OpenRing)
    (h : Inclusion s t) (ω : Omega s) :
    oneFormRestriction s t h ω = ∑ i : Fin 4,
      functionRestriction s t h ((coordinateBasis s).repr ω i) • coordinateBasis t i := by
  calc
    oneFormRestriction s t h ω = oneFormRestriction s t h
        (∑ i : Fin 4, (coordinateBasis s).repr ω i • coordinateBasis s i) :=
      congrArg (oneFormRestriction s t h) ((coordinateBasis s).sum_repr ω).symm
    _ = _ := by simp only [map_sum, oneFormRestriction_smul, oneFormRestriction_basis]

@[simp] theorem oneFormRestriction_toGeneric (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (ω : Omega s) :
    oneFormPullback t ht (oneFormRestriction s t h ω) = oneFormPullback s hs ω := by
  rw [oneFormRestriction_coordinates, oneFormPullback_coordinates s hs]
  simp only [map_sum, oneFormPullback_smul, oneFormPullback_coordinateBasis,
    functionRestriction_toGeneric s t hs ht h]

theorem oneFormRestriction_injective (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) :
    Function.Injective (oneFormRestriction s t h) := by
  intro ω η heq
  apply oneFormPullback_injective s hs
  simpa only [oneFormRestriction_toGeneric s t hs ht h] using congrArg (oneFormPullback t ht) heq

theorem oneFormRestriction_id (s : OpenRing) (hs : s ≠ 0) (ω : Omega s) :
    oneFormRestriction s s le_rfl ω = ω := by
  apply oneFormPullback_injective s hs
  exact oneFormRestriction_toGeneric s s hs hs le_rfl ω

theorem oneFormRestriction_comp (s t u : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0)
    (hst : Inclusion s t) (htu : Inclusion t u) (ω : Omega s) :
    oneFormRestriction t u htu (oneFormRestriction s t hst ω) =
      oneFormRestriction s u (htu.trans hst) ω := by
  apply oneFormPullback_injective u hu
  rw [oneFormRestriction_toGeneric t u ht hu htu,
    oneFormRestriction_toGeneric s t hs ht hst,
    oneFormRestriction_toGeneric s u hs hu (htu.trans hst)]

/-- Restriction on genuine exterior powers, induced by the canonical
Kähler restriction and the universal alternating map. -/
def exteriorRestriction (s t : OpenRing) (h : Inclusion s t) (p : ℕ) :
    Form s p →ₗ[ℂ] Form t p := by
  letI := restrictionAlgebra s t h
  letI := restrictionTower s t h
  let wedge : Omega t [⋀^Fin p]→ₗ[LocalRing s] (Form t p) :=
    { toMultilinearMap :=
        (exteriorPower.ιMulti (LocalRing t) p).toMultilinearMap.restrictScalars (LocalRing s)
      map_eq_zero_of_eq' := (exteriorPower.ιMulti (LocalRing t) p).map_eq_zero_of_eq' }
  exact (exteriorPower.alternatingMapLinearEquiv
    (wedge.compLinearMap (KaehlerDifferential.map ℂ ℂ (LocalRing s) (LocalRing t))))
      |>.restrictScalars ℂ

@[simp] theorem exteriorRestriction_ιMulti (s t : OpenRing)
    (h : Inclusion s t) (p : ℕ) (v : Fin p → Omega s) :
    exteriorRestriction s t h p (exteriorPower.ιMulti (LocalRing s) p v) =
      exteriorPower.ιMulti (LocalRing t) p (fun i => oneFormRestriction s t h (v i)) := by
  letI := restrictionAlgebra s t h
  letI := restrictionTower s t h
  simp only [exteriorRestriction, LinearMap.coe_restrictScalars,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply] <;> rfl

@[simp] theorem exteriorRestriction_smul (s t : OpenRing)
    (h : Inclusion s t) (p : ℕ) (a : LocalRing s) (ω : Form s p) :
    exteriorRestriction s t h p (a • ω) =
      functionRestriction s t h a • exteriorRestriction s t h p ω := by
  letI := restrictionAlgebra s t h
  letI := restrictionTower s t h
  unfold exteriorRestriction
  simp only [LinearMap.coe_restrictScalars, map_smul] <;>
    exact (IsScalarTower.algebraMap_smul (R := LocalRing s) (A := LocalRing t) a _).symm

@[simp] theorem exteriorRestriction_basis (s t : OpenRing)
    (h : Inclusion s t) (p : ℕ) (i : Set.powersetCard (Fin 4) p) :
    exteriorRestriction s t h p ((coordinateBasis s).exteriorPower p i) =
      (coordinateBasis t).exteriorPower p i := by
  simp only [exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    exteriorRestriction_ιMulti]
  congr 1
  funext j
  exact oneFormRestriction_basis s t h _

theorem exteriorRestriction_coordinates (s t : OpenRing)
    (h : Inclusion s t) (p : ℕ) (ω : Form s p) :
    exteriorRestriction s t h p ω = ∑ i : Set.powersetCard (Fin 4) p,
      functionRestriction s t h (((coordinateBasis s).exteriorPower p).repr ω i) •
        (coordinateBasis t).exteriorPower p i := by
  calc
    exteriorRestriction s t h p ω = exteriorRestriction s t h p
        (∑ i, ((coordinateBasis s).exteriorPower p).repr ω i •
          (coordinateBasis s).exteriorPower p i) :=
      congrArg (exteriorRestriction s t h p)
        (((coordinateBasis s).exteriorPower p).sum_repr ω).symm
    _ = _ := by simp only [map_sum, exteriorRestriction_smul, exteriorRestriction_basis]

@[simp] theorem exteriorRestriction_toGeneric (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (p : ℕ) (ω : Form s p) :
    exteriorPullback t ht p (exteriorRestriction s t h p ω) =
      exteriorPullback s hs p ω := by
  apply (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p).repr.injective
  ext i
  have hcoord (j l : Set.powersetCard (Fin 4) p) :
      (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p).repr
        (exteriorPower.ιMulti_family CycleQ2AffineDifferentials.K p
          CycleQ2AffineDifferentials.coordinateBasis j) l = if j = l then 1 else 0 := by
    simpa only [exteriorPower.basis_apply] using
      (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p).repr_self_apply j l
  rw [exteriorRestriction_coordinates]
  simp only [map_sum, exteriorPullback_smul, exteriorPullback_basis,
    functionRestriction_toGeneric s t hs ht h]
  simp [exteriorPullback_repr, hcoord]

theorem exteriorRestriction_injective (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (p : ℕ) :
    Function.Injective (exteriorRestriction s t h p) := by
  intro ω η heq
  apply exteriorPullback_injective s hs p
  simpa only [exteriorRestriction_toGeneric s t hs ht h] using
    congrArg (exteriorPullback t ht p) heq

theorem exteriorRestriction_id (s : OpenRing) (hs : s ≠ 0) (p : ℕ) (ω : Form s p) :
    exteriorRestriction s s le_rfl p ω = ω := by
  apply exteriorPullback_injective s hs p
  exact exteriorRestriction_toGeneric s s hs hs le_rfl p ω

theorem exteriorRestriction_comp (s t u : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0)
    (hst : Inclusion s t) (htu : Inclusion t u) (p : ℕ) (ω : Form s p) :
    exteriorRestriction t u htu p (exteriorRestriction s t hst p ω) =
      exteriorRestriction s u (htu.trans hst) p ω := by
  apply exteriorPullback_injective u hu p
  rw [exteriorRestriction_toGeneric t u ht hu htu,
    exteriorRestriction_toGeneric s t hs ht hst,
    exteriorRestriction_toGeneric s u hs hu (htu.trans hst)]

/-! ## Every exterior derivative is natural on the actual opens -/

theorem exteriorD1_restrict (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (ω : Omega s) :
    exteriorRestriction s t h 2 (exteriorD1 s ω) =
      exteriorD1 t (oneFormRestriction s t h ω) := by
  apply exteriorPullback_injective t ht 2
  rw [exteriorRestriction_toGeneric s t hs ht h, exteriorD1_pullback,
    exteriorD1_pullback, oneFormRestriction_toGeneric s t hs ht h]

theorem exteriorD2_restrict (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (ω : Form s 2) :
    exteriorRestriction s t h 3 (exteriorD2 s ω) =
      exteriorD2 t (exteriorRestriction s t h 2 ω) := by
  apply exteriorPullback_injective t ht 3
  rw [exteriorRestriction_toGeneric s t hs ht h, exteriorD2_pullback,
    exteriorD2_pullback, exteriorRestriction_toGeneric s t hs ht h]

theorem exteriorD3_restrict (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (ω : Form s 3) :
    exteriorRestriction s t h 4 (exteriorD3 s ω) =
      exteriorD3 t (exteriorRestriction s t h 3 ω) := by
  apply exteriorPullback_injective t ht 4
  rw [exteriorRestriction_toGeneric s t hs ht h, exteriorD3_pullback,
    exteriorD3_pullback, exteriorRestriction_toGeneric s t hs ht h]

def restrictionComponent (s t : OpenRing) (h : Inclusion s t) :
    (n : ℕ) → (object s n ⟶ object t n)
  | 0 => ModuleCat.ofHom (functionRestriction s t h).toLinearMap
  | 1 => ModuleCat.ofHom (oneFormRestriction s t h)
  | 2 => ModuleCat.ofHom (exteriorRestriction s t h 2)
  | 3 => ModuleCat.ofHom (exteriorRestriction s t h 3)
  | 4 => ModuleCat.ofHom (exteriorRestriction s t h 4)
  | _ + 5 => 0

/-- Actual restriction is a map of the previously constructed regular
de Rham complexes in every degree. -/
def complexRestriction (s t : OpenRing) (hs : s ≠ 0) (ht : t ≠ 0)
    (h : Inclusion s t) : complex s hs ⟶ complex t ht :=
  CochainComplex.ofHom (restrictionComponent s t h) (by
    intro n
    rw [complex_d_succ, complex_d_succ]
    cases n with
    | zero =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        exact (oneFormRestriction_d s t h a).symm
    | succ n =>
        cases n with
        | zero =>
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro ω
            exact (exteriorD1_restrict s t hs ht h ω).symm
        | succ n =>
            cases n with
            | zero =>
                apply ModuleCat.hom_ext
                apply LinearMap.ext
                intro ω
                exact (exteriorD2_restrict s t hs ht h ω).symm
            | succ n =>
                cases n with
                | zero =>
                    apply ModuleCat.hom_ext
                    apply LinearMap.ext
                    intro ω
                    exact (exteriorD3_restrict s t hs ht h ω).symm
                | succ n =>
                    change restrictionComponent s t h (n + 4) ≫ 0 = 0 ≫ _
                    simp only [CategoryTheory.Limits.comp_zero,
                      CategoryTheory.Limits.zero_comp])

theorem complexRestriction_id (s : OpenRing) (hs : s ≠ 0) :
    complexRestriction s s hs hs le_rfl = 𝟙 (complex s hs) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact congrArg (fun f : LocalRing s →ₐ[ℂ] LocalRing s => f a)
        (functionRestriction_id s)
  | succ n =>
      cases n with
      | zero =>
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          exact oneFormRestriction_id s hs
      | succ n =>
          cases n with
          | zero =>
              apply ModuleCat.hom_ext
              apply LinearMap.ext
              exact exteriorRestriction_id s hs 2
          | succ n =>
              cases n with
              | zero =>
                  apply ModuleCat.hom_ext
                  apply LinearMap.ext
                  exact exteriorRestriction_id s hs 3
              | succ n =>
                  cases n with
                  | zero =>
                      apply ModuleCat.hom_ext
                      apply LinearMap.ext
                      exact exteriorRestriction_id s hs 4
                  | succ n =>
                      apply ModuleCat.hom_ext
                      apply LinearMap.ext
                      intro a
                      haveI : Subsingleton ((complex s hs).X (n + 1 + 1 + 1 + 1 + 1)) := by
                        change Subsingleton (Fin 0 → ℂ)
                        infer_instance
                      exact Subsingleton.elim _ _

theorem complexRestriction_comp (s t u : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0)
    (hst : Inclusion s t) (htu : Inclusion t u) :
    complexRestriction s t hs ht hst ≫ complexRestriction t u ht hu htu =
      complexRestriction s u hs hu (htu.trans hst) := by
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact congrArg (fun f : LocalRing s →ₐ[ℂ] LocalRing u => f a)
        (functionRestriction_comp s t u hst htu)
  | succ n =>
      cases n with
      | zero =>
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          exact oneFormRestriction_comp s t u hs ht hu hst htu
      | succ n =>
          cases n with
          | zero =>
              apply ModuleCat.hom_ext
              apply LinearMap.ext
              exact exteriorRestriction_comp s t u hs ht hu hst htu 2
          | succ n =>
              cases n with
              | zero =>
                  apply ModuleCat.hom_ext
                  apply LinearMap.ext
                  exact exteriorRestriction_comp s t u hs ht hu hst htu 3
              | succ n =>
                  cases n with
                  | zero =>
                      apply ModuleCat.hom_ext
                      apply LinearMap.ext
                      exact exteriorRestriction_comp s t u hs ht hu hst htu 4
                  | succ n =>
                      apply ModuleCat.hom_ext
                      apply LinearMap.ext
                      intro a
                      haveI : Subsingleton ((complex u hu).X (n + 1 + 1 + 1 + 1 + 1)) := by
                        change Subsingleton (Fin 0 → ℂ)
                        infer_instance
                      exact Subsingleton.elim _ _

/-! ## The diagram on nonempty principal opens -/

/-- A presentation of a nonempty principal open of the actual coordinate
ring. Different denominators presenting the same open are isomorphic in
the inclusion preorder; no syntactic choice of generator is fixed. -/
structure PrincipalOpen where
  denominator : OpenRing
  nonzero : denominator ≠ 0

instance : Preorder PrincipalOpen where
  le U V := PrimeSpectrum.basicOpen U.denominator ≤ PrimeSpectrum.basicOpen V.denominator
  le_refl _ := le_rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂

/-- A concrete common refinement, still nonempty because the actual
normal-Jacobian coordinate ring is a domain. -/
def PrincipalOpen.intersection (U V : PrincipalOpen) : PrincipalOpen :=
  ⟨U.denominator * V.denominator, mul_ne_zero U.nonzero V.nonzero⟩

theorem PrincipalOpen.intersection_le_left (U V : PrincipalOpen) :
    U.intersection V ≤ U :=
  PrimeSpectrum.basicOpen_mul_le_left U.denominator V.denominator

theorem PrincipalOpen.intersection_le_right (U V : PrincipalOpen) :
    U.intersection V ≤ V :=
  PrimeSpectrum.basicOpen_mul_le_right U.denominator V.denominator

instance : Nonempty PrincipalOpen := ⟨⟨1, one_ne_zero⟩⟩

/-- Every two nonempty principal opens have the displayed nonempty
intersection, and the inclusion category has at most one morphism between
any fixed pair. Its opposite is therefore a filtered indexing category. -/
instance : IsCofiltered PrincipalOpen where
  cone_objs U V := ⟨U.intersection V,
    homOfLE (U.intersection_le_left V), homOfLE (U.intersection_le_right V), trivial⟩
  cone_maps {U V} f g := ⟨U, 𝟙 U, Subsingleton.elim _ _⟩

/-- Contravariant regular de Rham complexes, with the actual principal-open
inclusions as morphisms and proved identity/composition laws. -/
def principalComplex : PrincipalOpenᵒᵖ ⥤ CochainComplex (ModuleCat ℂ) ℕ where
  obj U := complex U.unop.denominator U.unop.nonzero
  map {U V} f := complexRestriction U.unop.denominator V.unop.denominator
    U.unop.nonzero V.unop.nonzero (leOfHom f.unop)
  map_id U := complexRestriction_id U.unop.denominator U.unop.nonzero
  map_comp {U V W} f g :=
    (complexRestriction_comp U.unop.denominator V.unop.denominator W.unop.denominator
      U.unop.nonzero V.unop.nonzero W.unop.nonzero
      (leOfHom f.unop) (leOfHom g.unop)).symm

/-! ## The protected residue and top cohomology restrict compatibly -/

@[simp] theorem exteriorRestriction_residueSourceForm (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (A : AmbientPoly 4) :
    exteriorRestriction s t h 4 (residueSourceForm s A) = residueSourceForm t A := by
  apply exteriorPullback_injective t ht 4
  rw [exteriorRestriction_toGeneric s t hs ht h, exteriorPullback_residueSourceForm,
    exteriorPullback_residueSourceForm]

def topRestriction (s t : OpenRing) (hs : s ≠ 0) (ht : t ≠ 0)
    (h : Inclusion s t) : TopDeRham s →ₗ[ℂ] TopDeRham t :=
  (exactTopForms s).liftQ ((classOf t).comp (exteriorRestriction s t h 4)) (by
    rintro ω ⟨η, rfl⟩
    change classOf t (exteriorRestriction s t h 4 (exteriorD3 s η)) = 0
    rw [exteriorD3_restrict s t hs ht, classOf_exteriorD3])

@[simp] theorem topRestriction_classOf (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (ω : Form s 4) :
    topRestriction s t hs ht h (classOf s ω) =
      classOf t (exteriorRestriction s t h 4 ω) := rfl

@[simp] theorem topRestriction_residueClass (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) :
    topRestriction s t hs ht h (residueClass s) = residueClass t := by
  rw [residueClass, topRestriction_classOf,
    exteriorRestriction_residueSourceForm s t hs ht] <;> rfl

@[simp] theorem topRestriction_toGeneric (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (ξ : TopDeRham s) :
    toGeneric t ht (topRestriction s t hs ht h ξ) = toGeneric s hs ξ := by
  refine Submodule.Quotient.induction_on (exactTopForms s) ξ ?_
  intro ω
  change toGeneric t ht (topRestriction s t hs ht h (classOf s ω)) =
    toGeneric s hs (classOf s ω)
  rw [topRestriction_classOf, toGeneric_classOf, toGeneric_classOf,
    exteriorRestriction_toGeneric s t hs ht h]

theorem topRestriction_id (s : OpenRing) (hs : s ≠ 0) (ξ : TopDeRham s) :
    topRestriction s s hs hs le_rfl ξ = ξ := by
  refine Submodule.Quotient.induction_on (exactTopForms s) ξ ?_
  intro ω
  change topRestriction s s hs hs le_rfl (classOf s ω) = classOf s ω
  rw [topRestriction_classOf, exteriorRestriction_id s hs]

theorem topRestriction_comp (s t u : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0)
    (hst : Inclusion s t) (htu : Inclusion t u) (ξ : TopDeRham s) :
    topRestriction t u ht hu htu (topRestriction s t hs ht hst ξ) =
      topRestriction s u hs hu (htu.trans hst) ξ := by
  refine Submodule.Quotient.induction_on (exactTopForms s) ξ ?_
  intro ω
  change topRestriction t u ht hu htu
      (topRestriction s t hs ht hst (classOf s ω)) =
    topRestriction s u hs hu (htu.trans hst) (classOf s ω)
  rw [topRestriction_classOf, topRestriction_classOf, topRestriction_classOf]
  exact congrArg (classOf u) (exteriorRestriction_comp s t u hs ht hu hst htu 4 ω)

/-- The top cohomology quotients with their actual induced restrictions.
No sheaf property of this cohomology presheaf is asserted. -/
def principalTopCohomology : PrincipalOpenᵒᵖ ⥤ ModuleCat ℂ where
  obj U := ModuleCat.of ℂ (TopDeRham U.unop.denominator)
  map {U V} f := ModuleCat.ofHom
    (topRestriction U.unop.denominator V.unop.denominator
      U.unop.nonzero V.unop.nonzero (leOfHom f.unop))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact topRestriction_id U.unop.denominator U.unop.nonzero
  map_comp {U V W} f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro ξ
    exact (topRestriction_comp U.unop.denominator V.unop.denominator W.unop.denominator
      U.unop.nonzero V.unop.nonzero W.unop.nonzero
      (leOfHom f.unop) (leOfHom g.unop) ξ).symm

/-- Vanishing on one actual open persists after shrinking. This proves
only persistence: the missing geometric support argument must first
produce an open on which the protected residue class vanishes. -/
theorem residueClass_zero_on_smaller (s t : OpenRing)
    (hs : s ≠ 0) (ht : t ≠ 0) (h : Inclusion s t) (hz : residueClass s = 0) :
    residueClass t = 0 := by
  have heq := congrArg (topRestriction s t hs ht h) hz
  simpa only [topRestriction_residueClass, map_zero] using heq

end CycleQ2GeometricPrincipalRestriction

end


/-! ## Rational spreading and the generic top-cohomology colimit -/

/-!
# Spreading actual rational forms to nonempty principal opens

The generic-point complex in the protected target is not an abstract
replacement for regular algebraic forms. Every one of its forms has
finitely many coefficients in the actual function field. Clearing those
coefficients gives a regular form on a further principal open of the
constructed smooth Jacobian open.

This file constructs that lift, even inside any prescribed nonempty
principal open. Injectivity of the actual exterior restriction then shows
that rational exactness is equivalent to regular exactness after a further
restriction. In particular, the protected residue is rationally exact if
and only if its regular class vanishes on some such open.

No vanishing of that class, geometric support construction, or analytic
comparison is assumed or asserted here. This is source-only work; Lean
elaboration, compilation, and kernel checking remain deferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2GeometricRationalSpread

open CycleQ2GeometricRegularDeRham
open CycleQ2GeometricPrincipalRestriction
open scoped BigOperators

/-- The inverse of the further denominator has its expected value at the
generic point. The denominator is nonzero, rather than an arbitrary unit
postulated in the function field. -/
theorem localFunctionFieldMap_invSelf (s : OpenRing) (hs : s ≠ 0) :
    localFunctionFieldMap s hs
        (IsLocalization.Away.invSelf (S := LocalRing s) s) =
      (functionFieldMap s)⁻¹ := by
  apply mul_left_cancel₀ (functionFieldMap_ne_zero hs)
  rw [mul_inv_cancel₀ (functionFieldMap_ne_zero hs)]
  have h := congrArg (localFunctionFieldMap s hs)
    (IsLocalization.Away.mul_invSelf (S := LocalRing s) s)
  simpa only [map_mul, localFunctionFieldMap_algebraMap, map_one] using h

/-- Divisibility of denominators gives the actual inclusion of basic
opens in the spectrum of the constructed Jacobian coordinate ring. -/
theorem basicOpen_le_of_dvd {t s : OpenRing} (h : t ∣ s) :
    PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen t := by
  obtain ⟨u, rfl⟩ := h
  exact PrimeSpectrum.basicOpen_mul_le_left t u

/-- A finite family of actual rational functions becomes regular on one
nonempty principal open contained in any prescribed `D(t)`.

The common denominator is chosen in the original affine coordinate ring.
It is then multiplied by `t`, so the result is inside the required open.
This does not impose a bound on the denominator or on its pole order. -/
theorem exists_regular_coefficients_within
    {ι : Type*} [Finite ι] (t : OpenRing) (ht : t ≠ 0) (c : ι → K) :
    ∃ (s : OpenRing) (hs : s ≠ 0), t ∣ s ∧
      ∃ a : ι → LocalRing s, ∀ i, localFunctionFieldMap s hs (a i) = c i := by
  classical
  obtain ⟨b, hb⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors BaseRing) c
  have hnum : ∀ i, ∃ a : BaseRing,
      algebraMap BaseRing K a = algebraMap BaseRing K (b : BaseRing) * c i := by
    intro i
    obtain ⟨a, ha⟩ := hb i
    exact ⟨a, by simpa only [Algebra.smul_def] using ha⟩
  choose a ha using hnum
  let b' : OpenRing := algebraMap BaseRing OpenRing (b : BaseRing)
  have hbK : algebraMap BaseRing K (b : BaseRing) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
  have hb' : b' ≠ 0 := by
    intro h
    apply hbK
    have h' := congrArg functionFieldMap h
    simpa only [b', functionFieldMap_algebraMap, map_zero] using h'
  let s : OpenRing := b' * t
  have hs : s ≠ 0 := mul_ne_zero hb' ht
  refine ⟨s, hs, ⟨b', mul_comm b' t⟩, ?_⟩
  refine ⟨fun i =>
    algebraMap OpenRing (LocalRing s)
      (algebraMap BaseRing OpenRing (a i) * t) *
        IsLocalization.Away.invSelf (S := LocalRing s) s, ?_⟩
  intro i
  have hnum' :
      functionFieldMap (algebraMap BaseRing OpenRing (a i) * t) =
        functionFieldMap s * c i := by
    simp only [s, b', map_mul, functionFieldMap_algebraMap, ha]
    ring
  rw [map_mul, localFunctionFieldMap_algebraMap,
    localFunctionFieldMap_invSelf, hnum']
  calc
    (functionFieldMap s * c i) * (functionFieldMap s)⁻¹ =
        c i * (functionFieldMap s * (functionFieldMap s)⁻¹) := by ring
    _ = c i := by rw [mul_inv_cancel₀ (functionFieldMap_ne_zero hs), mul_one]

/-- Every actual exterior form at the generic point spreads to a regular
form on a nonempty principal open, with a prescribed initial open.
The construction uses the genuine exterior-power bases on both sides. -/
theorem exists_regular_form_within (t : OpenRing) (ht : t ≠ 0)
    (p : ℕ) (ω : CycleQ2AffineExterior.Form p) :
    ∃ (s : OpenRing) (hs : s ≠ 0), t ∣ s ∧
      ∃ η : Form s p, exteriorPullback s hs p η = ω := by
  classical
  obtain ⟨s, hs, hts, a, ha⟩ := exists_regular_coefficients_within t ht
    (fun i : Set.powersetCard (Fin 4) p =>
      (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p).repr ω i)
  refine ⟨s, hs, hts,
    ∑ i : Set.powersetCard (Fin 4) p,
      a i • (coordinateBasis s).exteriorPower p i, ?_⟩
  simp only [map_sum, exteriorPullback_smul, exteriorPullback_basis, ha]
  exact (CycleQ2AffineDifferentials.coordinateBasis.exteriorPower p).sum_repr ω

theorem exists_regular_form (p : ℕ) (ω : CycleQ2AffineExterior.Form p) :
    ∃ (s : OpenRing) (hs : s ≠ 0),
      ∃ η : Form s p, exteriorPullback s hs p η = ω := by
  obtain ⟨s, hs, _, η, hη⟩ := exists_regular_form_within 1 one_ne_zero p ω
  exact ⟨s, hs, η, hη⟩

/-! ## Generic cohomology and eventual regular vanishing -/

/-- Every actual generic top-cohomology class is represented on a
nonempty principal open inside any prescribed one. This is surjectivity
from the family of regular cohomologies, not from one fixed member. -/
theorem exists_regular_top_class_within (t : OpenRing) (ht : t ≠ 0)
    (ξ : CycleQ2AffineTopCohomology.TopDeRham) :
    ∃ (s : OpenRing) (hs : s ≠ 0), t ∣ s ∧
      ∃ ζ : TopDeRham s, toGeneric s hs ζ = ξ := by
  refine Submodule.Quotient.induction_on
    CycleQ2AffineTopCohomology.exactTopForms ξ ?_
  intro ω
  obtain ⟨s, hs, hts, η, hη⟩ := exists_regular_form_within t ht 4 ω
  refine ⟨s, hs, hts, classOf s η, ?_⟩
  rw [toGeneric_classOf, hη] <;> rfl

/-- A regular top-cohomology class becomes zero at the generic point
exactly when it becomes zero after restricting to a smaller nonempty
principal open. In the forward direction the smaller denominator is
constructed by spreading the actual rational primitive.

This is the eventual-equality property needed for a directed-limit
description; it does not falsely assert that `toGeneric` is injective on
one fixed open. -/
theorem toGeneric_eq_zero_iff_eventually_zero
    (t : OpenRing) (ht : t ≠ 0) (ξ : TopDeRham t) :
    toGeneric t ht ξ = 0 ↔
      ∃ (s : OpenRing) (hs : s ≠ 0) (hts : t ∣ s),
        topRestriction t s ht hs (basicOpen_le_of_dvd hts) ξ = 0 := by
  refine Submodule.Quotient.induction_on (exactTopForms t) ξ ?_
  intro ω
  change toGeneric t ht (classOf t ω) = 0 ↔
    ∃ (s : OpenRing) (hs : s ≠ 0) (hts : t ∣ s),
      topRestriction t s ht hs (basicOpen_le_of_dvd hts) (classOf t ω) = 0
  constructor
  · intro hzero
    rw [toGeneric_classOf] at hzero
    obtain ⟨η, hη⟩ :=
      (CycleQ2AffineTopCohomology.classOf_eq_zero_iff _).mp hzero
    obtain ⟨s, hs, hts, η', hη'⟩ := exists_regular_form_within t ht 3 η
    refine ⟨s, hs, hts, ?_⟩
    rw [topRestriction_classOf]
    apply (classOf_eq_zero_iff s _).mpr
    refine ⟨η', ?_⟩
    apply exteriorPullback_injective s hs 4
    rw [exteriorD3_pullback, hη', hη]
    exact (exteriorRestriction_toGeneric t s ht hs (basicOpen_le_of_dvd hts) 4 ω).symm
  · rintro ⟨s, hs, hts, hzero⟩
    have h := congrArg (toGeneric s hs) hzero
    simpa only [topRestriction_toGeneric, map_zero] using h

/-- Equality of two classes on the same regular open is detected after
shrinking whenever their generic classes agree. -/
theorem toGeneric_eq_iff_eventually_eq
    (t : OpenRing) (ht : t ≠ 0) (ξ ζ : TopDeRham t) :
    toGeneric t ht ξ = toGeneric t ht ζ ↔
      ∃ (s : OpenRing) (hs : s ≠ 0) (hts : t ∣ s),
        topRestriction t s ht hs (basicOpen_le_of_dvd hts) ξ =
          topRestriction t s ht hs (basicOpen_le_of_dvd hts) ζ := by
  rw [← sub_eq_zero, ← map_sub, toGeneric_eq_zero_iff_eventually_zero]
  simp only [map_sub, sub_eq_zero]

/-! ## The actual filtered colimit of regular top cohomology -/

open CategoryTheory CategoryTheory.Limits

/-- The generic quotient receives the canonical, compatible restrictions
from the actual regular cohomology diagram. -/
def genericTopCocone : Cocone principalTopCohomology where
  pt := ModuleCat.of ℂ CycleQ2AffineTopCohomology.TopDeRham
  ι :=
    { app U := ModuleCat.ofHom (toGeneric U.unop.denominator U.unop.nonzero)
      naturality U V f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro ξ
        change toGeneric V.unop.denominator V.unop.nonzero
            (topRestriction U.unop.denominator V.unop.denominator
              U.unop.nonzero V.unop.nonzero (leOfHom f.unop) ξ) =
          toGeneric U.unop.denominator U.unop.nonzero ξ
        exact topRestriction_toGeneric _ _ _ _ _ ξ }

/-- The generic top de Rham quotient has the universal property of the
filtered colimit of the regular quotients on nonempty principal opens.

Surjectivity is supplied by spreading coefficients of an actual form.
Equality is supplied by spreading an actual rational primitive. Thus the
colimit statement is established from algebraic constructions, without a
geometric or analytic comparison hypothesis. -/
def genericTopIsColimit : IsColimit genericTopCocone := by
  apply isColimitOfReflects (forget (ModuleCat ℂ))
  refine Types.FilteredColimit.isColimitOf'
    (principalTopCohomology ⋙ forget (ModuleCat ℂ))
    ((forget (ModuleCat ℂ)).mapCocone genericTopCocone) ?_ ?_
  · intro ξ
    obtain ⟨s, hs, _, ζ, hζ⟩ := exists_regular_top_class_within 1 one_ne_zero ξ
    refine ⟨Opposite.op (⟨s, hs⟩ : PrincipalOpen), ζ, ?_⟩
    exact hζ.symm
  · intro U ξ ζ h
    change toGeneric U.unop.denominator U.unop.nonzero ξ =
      toGeneric U.unop.denominator U.unop.nonzero ζ at h
    obtain ⟨s, hs, hts, heq⟩ :=
      (toGeneric_eq_iff_eventually_eq U.unop.denominator U.unop.nonzero ξ ζ).mp h
    let V : PrincipalOpen := ⟨s, hs⟩
    let f : U ⟶ Opposite.op V :=
      (homOfLE (show V ≤ U.unop from basicOpen_le_of_dvd hts)).op
    refine ⟨Opposite.op V, f, ?_⟩
    exact heq

/-- A genuine isomorphism in the category of complex vector spaces,
not a definition of the regular colimit as the generic quotient. -/
def genericTopColimitIso :
    colimit principalTopCohomology ≅
      ModuleCat.of ℂ CycleQ2AffineTopCohomology.TopDeRham :=
  (colimit.isColimit principalTopCohomology).coconePointUniqueUpToIso
    genericTopIsColimit

/-- The colimit comparison is tied to the already constructed restriction
maps, so it carries the protected regular residue to the protected generic
residue by `toGeneric_residueClass`. -/
@[reassoc (attr := simp)]
theorem colimit_ι_genericTopColimitIso_hom (U : PrincipalOpenᵒᵖ) :
    colimit.ι principalTopCohomology U ≫ genericTopColimitIso.hom =
      ModuleCat.ofHom (toGeneric U.unop.denominator U.unop.nonzero) :=
  (colimit.isColimit principalTopCohomology).comp_coconePointUniqueUpToIso_hom
    genericTopIsColimit U

/-- An exact rational residue admits an actual regular primitive after
shrinking inside any prescribed nonempty principal open. Conversely,
restriction of a regular primitive gives the original rational equation.

This theorem is an equivalence, not a proof of either existence statement. -/
theorem residue_exact_iff_regular_exact_within
    (t : OpenRing) (ht : t ≠ 0) (A : HodgeComputer.AmbientPoly 4) :
    (∃ η : CycleQ2AffineExterior.Form 3,
      CycleQ2AffineExterior.exteriorD3 η =
        CycleQ2AffineExactness.residueSourceForm A) ↔
    ∃ (s : OpenRing) (hs : s ≠ 0), t ∣ s ∧
      ∃ η : Form s 3, exteriorD3 s η = residueSourceForm s A := by
  constructor
  · rintro ⟨η, hη⟩
    obtain ⟨s, hs, hts, ξ, hξ⟩ := exists_regular_form_within t ht 3 η
    refine ⟨s, hs, hts, ξ, ?_⟩
    apply exteriorPullback_injective s hs 4
    rw [exteriorD3_pullback, hξ, hη, exteriorPullback_residueSourceForm]
  · rintro ⟨s, hs, _, η, hη⟩
    refine ⟨exteriorPullback s hs 3 η, ?_⟩
    rw [← exteriorD3_pullback, hη, exteriorPullback_residueSourceForm]

/-- The same statement on the actual fourth-cohomology quotients.
No injection from one fixed open's cohomology to the generic point is
claimed; a further restriction is allowed and is constructed above. -/
theorem residue_class_zero_iff_regular_zero_within
    (t : OpenRing) (ht : t ≠ 0) (A : HodgeComputer.AmbientPoly 4) :
    CycleQ2AffineTopCohomology.residueClass A = 0 ↔
      ∃ s : OpenRing, s ≠ 0 ∧ t ∣ s ∧
        classOf s (residueSourceForm s A) = 0 := by
  rw [CycleQ2AffineTopCohomology.residueClass_eq_zero_iff,
    residue_exact_iff_regular_exact_within t ht A]
  constructor
  · rintro ⟨s, hs, hts, η, hη⟩
    exact ⟨s, hs, hts, (classOf_eq_zero_iff s _).mpr ⟨η, hη⟩⟩
  · rintro ⟨s, hs, hts, hzero⟩
    obtain ⟨η, hη⟩ := (classOf_eq_zero_iff s _).mp hzero
    exact ⟨s, hs, hts, η, hη⟩

/-- The protected rational existence statement is precisely regular
vanishing on some nonempty smooth principal open of the constructed
Jacobian open. Producing that vanishing remains the geometric obligation. -/
theorem protected_exact_iff_exists_regular_zero :
    (∃ η : CycleQ2AffineExterior.Form 3,
      CycleQ2AffineExterior.exteriorD3 η =
        CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA) ↔
      ∃ s : OpenRing, s ≠ 0 ∧ residueClass s = 0 := by
  rw [← CycleQ2AffineTopCohomology.residueClass_eq_zero_iff
      CycleQ2AffineClearing.affineA,
    residue_class_zero_iff_regular_zero_within 1 one_ne_zero
      CycleQ2AffineClearing.affineA]
  simp only [one_dvd, true_and, residueClass]

end CycleQ2GeometricRationalSpread

end
