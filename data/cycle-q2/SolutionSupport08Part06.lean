import Proposal.SolutionSupport08Part05

/-! Components extracted from SolutionSupport08.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_20261112/UniversalSurfaceCoefficientMap.lean -/
section
/-!
# Canonical coefficient specialization on the universal surface and its charts

All maps below are induced by the coefficient homomorphism on the actual
polynomial quotient and its actual coordinate localizations.  The Laurent
coordinate compatibility is a theorem about those maps, not their definition.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceCoefficientMap

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree CycleQ2UniversalSurface
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_cubic (f : R →+* S) (hcoeff : FullCubicTailIndex → R) :
    MvPolynomial.map f (normalizedFullCubic hcoeff) =
      normalizedFullCubic (fun i => f (hcoeff i)) := by
  simp [normalizedFullCubic]

theorem map_sextic (f : R →+* S) (Fcoeff : FullSexticTailIndex → R) :
    MvPolynomial.map f (normalizedFullSextic Fcoeff) =
      normalizedFullSextic (fun i => f (Fcoeff i)) := by
  simp [normalizedFullSextic]

theorem map_mem_surfaceIdeal (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {p : Poly R} (hp : p ∈ surfaceIdeal R hcoeff Fcoeff) :
    MvPolynomial.map f p ∈ surfaceIdeal S (fun i => f (hcoeff i))
      (fun i => f (Fcoeff i)) := by
  obtain ⟨a,b,hp⟩ := Ideal.mem_span_pair.mp hp
  apply Ideal.mem_span_pair.mpr
  refine ⟨MvPolynomial.map f a, MvPolynomial.map f b, ?_⟩
  rw [← hp]
  simp only [map_add, map_mul, map_cubic, map_sextic]

def surfaceMap (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    SurfaceRing R hcoeff Fcoeff →+*
      SurfaceRing S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) :=
  Ideal.quotientMap _ (MvPolynomial.map f) (by
    intro p hp
    exact map_mem_surfaceIdeal f hcoeff Fcoeff hp)

@[simp] theorem surfaceMap_mk (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : Poly R) :
    surfaceMap f hcoeff Fcoeff (Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff) p) =
      Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

@[simp] theorem surfaceMap_base (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : Base R) :
    surfaceMap f hcoeff Fcoeff (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) p) =
      algebraMap (Base S) (SurfaceRing S (fun i => f (hcoeff i))
        (fun i => f (Fcoeff i))) (MvPolynomial.map f p) := by
  change Ideal.Quotient.mk _ (MvPolynomial.map f (remainingInclusion R p)) =
    Ideal.Quotient.mk _ (remainingInclusion S (MvPolynomial.map f p))
  rw [remainingInclusion, remainingInclusion, MvPolynomial.map_rename]

@[simp] theorem surfaceMap_basis [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (ab : ShiftIndex) :
    surfaceMap f hcoeff Fcoeff (surfaceBasis R hcoeff Fcoeff ab) =
      surfaceBasis S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) ab := by
  simp only [surfaceBasis_apply, surfaceMap_mk, map_mul, map_pow,
    MvPolynomial.map_X]

theorem coordinates_surfaceMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (z : SurfaceRing R hcoeff Fcoeff) (ab : ShiftIndex) :
    (surfaceBasis S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i))).repr
        (surfaceMap f hcoeff Fcoeff z) ab =
      MvPolynomial.map f ((surfaceBasis R hcoeff Fcoeff).repr z ab) := by
  classical
  have hz := (surfaceBasis R hcoeff Fcoeff).sum_repr z
  have hm := congrArg (surfaceMap f hcoeff Fcoeff) hz
  simp only [map_sum, Algebra.smul_def, map_mul, surfaceMap_base,
    surfaceMap_basis] at hm
  rw [← hm]
  change (surfaceBasis S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i))).repr
      (∑ i, MvPolynomial.map f ((surfaceBasis R hcoeff Fcoeff).repr z i) •
        surfaceBasis S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) i) ab = _
  simp [Finsupp.single_apply]

def laurentMap (f : R →+* S) : Laurent (R := R) →+* Laurent (R := S) :=
  AddMonoidAlgebra.mapRingHom LaurentExponent f

@[simp] theorem laurentMap_coeff (f : R →+* S) (z : Laurent (R := R))
    (e : LaurentExponent) : (laurentMap f z).coeff e = f (z.coeff e) := by
  exact AddMonoidAlgebra.coeff_mapRingHom f z e

@[simp] theorem laurentMap_T (f : R →+* S) (e : LaurentExponent) :
    laurentMap f (T R e) = T S e := by
  simp [laurentMap, T]

@[simp] theorem map_baseProduct (f : R →+* S) (s : Finset (Fin 3)) :
    MvPolynomial.map f (baseProduct R s) = baseProduct S s := by
  simp [baseProduct]

@[simp] theorem laurentMap_baseToLaurent (f : R →+* S) (p : Base R) :
    laurentMap f (baseToLaurent R p) = baseToLaurent S (MvPolynomial.map f p) := by
  have he : (laurentMap f).comp (baseToLaurent R).toRingHom =
      (baseToLaurent S).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.map_C]
      change laurentMap f (baseToLaurent R (monomial 0 c)) =
        baseToLaurent S (monomial 0 (f c))
      rw [baseToLaurent_monomial, baseToLaurent_monomial]
      simp [laurentMap]
    · intro i
      simp
  exact congrArg (fun g : Base R →+* Laurent (R := S) => g p) he

def localMap (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) :
    SurfaceLocal R hcoeff Fcoeff s →+*
      SurfaceLocal S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s :=
  IsLocalization.Away.lift
    (S := SurfaceLocal R hcoeff Fcoeff s)
    (P := SurfaceLocal S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s)
    (g := (algebraMap _ _).comp (surfaceMap f hcoeff Fcoeff))
    (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s))
    (by
      simp only [RingHom.comp_apply, surfaceMap_base, map_baseProduct]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp] theorem localMap_algebraMap (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (z : SurfaceRing R hcoeff Fcoeff) :
    localMap f hcoeff Fcoeff s
        (algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) z) =
      algebraMap _ _ (surfaceMap f hcoeff Fcoeff z) := by
  exact IsLocalization.Away.lift_eq _ _ z

theorem coordinates_localMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (z : SurfaceLocal R hcoeff Fcoeff s) (ab : ShiftIndex) :
    localizedCoordinates S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s
        (localMap f hcoeff Fcoeff s z) ab =
      laurentMap f (localizedCoordinates R hcoeff Fcoeff s z ab) := by
  obtain ⟨n,p,hp⟩ := IsLocalization.Away.surj
    (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s)) z
  have hp' : z * algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s)
      (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s ^ n)) =
      algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) p := by
    simpa only [map_pow] using hp
  have hs := congrArg (fun z => localizedCoordinates R hcoeff Fcoeff s z ab) hp'
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at hs
  have hs' := congrArg (laurentMap f) hs
  simp only [map_mul, laurentMap_baseToLaurent, map_pow, map_baseProduct] at hs'
  have ht := congrArg (localMap f hcoeff Fcoeff s) hp'
  simp only [map_mul, localMap_algebraMap, surfaceMap_base] at ht
  simp only [map_pow, map_baseProduct] at ht
  have ht0 : localMap f hcoeff Fcoeff s z *
      algebraMap _ _ (algebraMap (Base S)
        (SurfaceRing S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)))
        (baseProduct S s ^ n)) =
      algebraMap _ _ (surfaceMap f hcoeff Fcoeff p) := by
    simpa only [map_pow] using ht
  have ht' := congrArg (fun z => localizedCoordinates S (fun i => f (hcoeff i))
    (fun i => f (Fcoeff i)) s z ab) ht0
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap,
    coordinates_surfaceMap] at ht'
  have hu : IsUnit (baseToLaurent S (baseProduct S s ^ n)) := by
    rw [map_pow, baseToLaurent_baseProduct]
    exact (T_isUnit S _).pow n
  apply hu.mul_right_injective
  simpa only [map_pow] using ht'.trans hs'.symm

theorem localMap_restriction [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (z : SurfaceLocal R hcoeff Fcoeff s) :
    localMap f hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst z) =
      restriction S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) hst
        (localMap f hcoeff Fcoeff s z) := by
  apply localizedCoordinates_injective S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) t
  funext ab
  simp only [coordinates_localMap, coordinates_restriction]

end CycleQ2UniversalSurfaceCoefficientMap

#print axioms CycleQ2UniversalSurfaceCoefficientMap.coordinates_surfaceMap
#print axioms CycleQ2UniversalSurfaceCoefficientMap.coordinates_localMap
#print axioms CycleQ2UniversalSurfaceCoefficientMap.localMap_restriction
end
end


/- Component: continuation_20261112/UniversalSurfaceCechPersistence.lean -/
section
/-!
# Base change and pointed persistence for actual top Cech classes

The cohomology is the quotient of the triple coordinate localization by
the images of the three actual pair-coordinate restriction maps, in degree
zero and invariant character.  Coefficient specialization is induced on
those actual localizations.  Thus the final nonvanishing implication is
about genuine classes in this complex, not a replacement scalar functional.

An application to a moving connecting class must still prove that its
specialization is the previously computed seed class.  No such comparison
is assumed or asserted here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceCechPersistence

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree CycleQ2UniversalSurface
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2SeedCechTopCohomology CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates
  CycleQ2UniversalSurfaceTopCech CycleQ2UniversalSurfaceCoefficientMap
open scoped TensorProduct

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

theorem localMap_smul (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (c : R) (z : SurfaceLocal R hcoeff Fcoeff s) :
    localMap f hcoeff Fcoeff s (c • z) = f c • localMap f hcoeff Fcoeff s z := by
  simp only [Algebra.smul_def, map_mul]
  congr 1
  rw [IsScalarTower.algebraMap_apply R (SurfaceRing R hcoeff Fcoeff)
    (SurfaceLocal R hcoeff Fcoeff s), localMap_algebraMap]
  change algebraMap _ _ (Ideal.Quotient.mk _ (MvPolynomial.map f (C c))) = _
  rw [MvPolynomial.map_C]
  rfl

def gradedLocalMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) :
    gradedLocal R hcoeff Fcoeff s →ₛₗ[f]
      gradedLocal S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s where
  toFun p := ⟨localMap f hcoeff Fcoeff s p.val, by
    intro ab e he
    change (localizedCoordinates S _ _ s (localMap f hcoeff Fcoeff s p.val) ab).coeff e = 0
    rw [coordinates_localMap, laurentMap_coeff]
    exact (congrArg f (p.property ab e he)).trans (map_zero f)⟩
  map_add' p q := by apply Subtype.ext; exact map_add (localMap f hcoeff Fcoeff s) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact localMap_smul f hcoeff Fcoeff s c p.val

def actualCoordinates [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ActualTopCechQuotient R hcoeff Fcoeff ≃ₗ[R] (TopIndex →₀ R) :=
  (actualTopEquiv R hcoeff Fcoeff).trans (topCechEquiv R)

@[simp] theorem actualCoordinates_mk [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R hcoeff Fcoeff Finset.univ) :
    actualCoordinates hcoeff Fcoeff (Submodule.Quotient.mk p) =
      topProjection R (gradedCoordinates R hcoeff Fcoeff Finset.univ p) := by
  change topCechEquiv R (Submodule.Quotient.mk
    (gradedCoordinates R hcoeff Fcoeff Finset.univ p)) = _
  exact topCechEquiv_mk R _

theorem mem_actualBoundary_iff [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R hcoeff Fcoeff Finset.univ) :
    p ∈ actualBoundary R hcoeff Fcoeff ↔
      topProjection R (gradedCoordinates R hcoeff Fcoeff Finset.univ p) = 0 := by
  rw [← actualCoordinates_mk]
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

theorem gradedLocalMap_mem_boundary [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R hcoeff Fcoeff Finset.univ)
    (hp : p ∈ actualBoundary R hcoeff Fcoeff) :
    gradedLocalMap f hcoeff Fcoeff Finset.univ p ∈
      actualBoundary S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) := by
  apply (mem_actualBoundary_iff _ _ _).mpr
  ext q
  change (localizedCoordinates S _ _ Finset.univ
      (localMap f hcoeff Fcoeff Finset.univ p.val) q.val.1).coeff
      (topExponent q.val.2) = 0
  rw [coordinates_localMap, laurentMap_coeff]
  have hz := congrArg (fun z : TopIndex →₀ R => z q)
    ((mem_actualBoundary_iff hcoeff Fcoeff p).mp hp)
  change (localizedCoordinates R hcoeff Fcoeff Finset.univ p.val q.val.1).coeff
    (topExponent q.val.2) = 0 at hz
  rw [hz, map_zero]

/-- The map on actual cohomology induced by coefficient specialization. -/
def actualTopMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ActualTopCechQuotient R hcoeff Fcoeff →ₛₗ[f]
      ActualTopCechQuotient S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) :=
  (actualBoundary R hcoeff Fcoeff).mapQ
    (actualBoundary S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)))
    (gradedLocalMap f hcoeff Fcoeff Finset.univ)
    (by intro p hp; exact gradedLocalMap_mem_boundary f hcoeff Fcoeff p hp)

@[simp] theorem actualTopMap_mk [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R hcoeff Fcoeff Finset.univ) :
    actualTopMap f hcoeff Fcoeff (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (gradedLocalMap f hcoeff Fcoeff Finset.univ p) := rfl

theorem coordinates_actualTopMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R hcoeff Fcoeff) (q : TopIndex) :
    actualCoordinates (fun i => f (hcoeff i)) (fun i => f (Fcoeff i))
        (actualTopMap f hcoeff Fcoeff z) q =
      f (actualCoordinates hcoeff Fcoeff z q) := by
  refine Submodule.Quotient.induction_on _ z ?_
  intro p
  rw [actualTopMap_mk, actualCoordinates_mk, actualCoordinates_mk]
  change (localizedCoordinates S _ _ Finset.univ
      (localMap f hcoeff Fcoeff Finset.univ p.val) q.val.1).coeff
      (topExponent q.val.2) = _
  rw [coordinates_localMap, laurentMap_coeff]
  rfl

/-- In particular, faithful coefficient extension is faithful on these actual
cohomology classes.  No generic flatness theorem is a hypothesis. -/
theorem actualTopMap_injective [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hf : Function.Injective f)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Function.Injective (actualTopMap f hcoeff Fcoeff) := by
  intro z w hzw
  apply (actualCoordinates hcoeff Fcoeff).injective
  ext q
  apply hf
  simpa only [coordinates_actualTopMap] using
    congrArg (fun u => actualCoordinates (fun i => f (hcoeff i))
      (fun i => f (Fcoeff i)) u q) hzw

/-- The pointed generic-component condition, applied to actual cohomology.
Only the scalar kernel containment is supplied; freeness and coefficient
compatibility of this concrete Cech quotient were proved above. -/
theorem nonzero_generic_of_nonzero_specialization
    [Nontrivial R] [Nontrivial S] [Nontrivial T]
    (generic : R →+* S) (specialization : R →+* T)
    (hpointed : ∀ c : R, generic c = 0 → specialization c = 0)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R hcoeff Fcoeff)
    (hz : actualTopMap specialization hcoeff Fcoeff z ≠ 0) :
    actualTopMap generic hcoeff Fcoeff z ≠ 0 := by
  intro hzero
  apply hz
  apply (actualCoordinates (fun i => specialization (hcoeff i))
    (fun i => specialization (Fcoeff i))).injective
  ext q
  rw [coordinates_actualTopMap, map_zero, Finsupp.zero_apply]
  apply hpointed
  have hq := congrArg (fun u => actualCoordinates (fun i => generic (hcoeff i))
    (fun i => generic (Fcoeff i)) u q) hzero
  simpa only [coordinates_actualTopMap, map_zero, Finsupp.zero_apply] using hq

/-- Every coordinate functional of the actual top cohomology is natural
under coefficient specialization; these are the seven relative trace coordinates. -/
def traceCoordinate [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (q : TopIndex) : ActualTopCechQuotient R hcoeff Fcoeff →ₗ[R] R :=
  (Finsupp.lapply q).comp (actualCoordinates hcoeff Fcoeff).toLinearMap

@[simp] theorem traceCoordinate_specialization [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R hcoeff Fcoeff) (q : TopIndex) :
    traceCoordinate (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) q
      (actualTopMap f hcoeff Fcoeff z) = f (traceCoordinate hcoeff Fcoeff q z) :=
  coordinates_actualTopMap f hcoeff Fcoeff z q

end CycleQ2UniversalSurfaceCechPersistence

#print axioms CycleQ2UniversalSurfaceCechPersistence.actualTopMap_injective
#print axioms CycleQ2UniversalSurfaceCechPersistence.nonzero_generic_of_nonzero_specialization
#print axioms CycleQ2UniversalSurfaceCechPersistence.traceCoordinate_specialization
end
end


/- Component: continuation_20261112/UniversalSurfaceBaseChange.lean -/
section
/-!
# Tensor base change for the actual seven-dimensional Cech quotient

The equivalence below is proved to send s tensor z to s times the class
induced by the actual coefficient-specialization maps on the localized
surface.  Thus it is the canonical base-change map of this explicit complex,
not merely an unrelated equivalence between free modules of the same rank.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceBaseChange

open CycleQ2IncidenceNormalForm CycleQ2UniversalSurfaceTopCech
  CycleQ2SeedCechTopCohomology CycleQ2UniversalSurfaceCechPersistence
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Nontrivial R] [Nontrivial S]

def coordinateBasis (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Basis TopIndex R (ActualTopCechQuotient R hcoeff Fcoeff) :=
  Module.Basis.ofRepr (actualCoordinates hcoeff Fcoeff)

def actualBaseChange (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    (S ⊗[R] ActualTopCechQuotient R hcoeff Fcoeff) ≃ₗ[S]
      ActualTopCechQuotient S (fun i => algebraMap R S (hcoeff i))
        (fun i => algebraMap R S (Fcoeff i)) :=
  ((coordinateBasis hcoeff Fcoeff).baseChange S).repr.trans
    (actualCoordinates (fun i => algebraMap R S (hcoeff i))
      (fun i => algebraMap R S (Fcoeff i))).symm

@[simp] theorem actualBaseChange_tmul (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) (s : S)
    (z : ActualTopCechQuotient R hcoeff Fcoeff) :
    actualBaseChange hcoeff Fcoeff (s ⊗ₜ[R] z) =
      s • actualTopMap (algebraMap R S) hcoeff Fcoeff z := by
  apply (actualCoordinates (fun i => algebraMap R S (hcoeff i))
    (fun i => algebraMap R S (Fcoeff i))).injective
  ext q
  simp only [actualBaseChange, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.baseChange_repr_tmul, map_smul, Finsupp.smul_apply,
    coordinates_actualTopMap]
  change actualCoordinates hcoeff Fcoeff z q • s =
    s * algebraMap R S (actualCoordinates hcoeff Fcoeff z q)
  rw [Algebra.smul_def, mul_comm]

end CycleQ2UniversalSurfaceBaseChange

#print axioms CycleQ2UniversalSurfaceBaseChange.actualBaseChange_tmul
end
end


/- Component: continuation_20261112/UniversalSurfaceNormalization.lean -/
section
/-!
# The literal universal incidence surface and its normalized Cech model

The original cubic and sextic leading coefficients are inverted in the
existing universal parameter ring.  Dividing the equations by these units
does not change their ideal.  The same equality holds after every coefficient
specialization, so the finite free surface and its Cech complex above concern
the literal incidence surface, with no change of its coordinate functions.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceNormalization

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2SeedQuotientFiniteFree
  CycleQ2UniversalSurface CycleQ2UniversalSurfaceCoefficientMap

variable {R : Type*} [CommRing R]

theorem equationsIdeal_unit_mul (u v : Rˣ) (h F : Poly R) :
    equationsIdeal (C (u : R) * h) (C (v : R) * F) = equationsIdeal h F := by
  ext p
  constructor
  · intro hp
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    have hp' : ∃ a b, p = a * (C (u : R) * h) + b * (C (v : R) * F) + 0 :=
      ⟨a,b,by simpa using hab.symm⟩
    obtain ⟨a,b,hab⟩ := (unit_scaled_representation_iff u v h F p 0).mpr hp'
    exact Ideal.mem_span_pair.mpr ⟨a,b,by simpa using hab.symm⟩
  · intro hp
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    have hp' : ∃ a b, p = a * h + b * F + 0 := ⟨a,b,by simpa using hab.symm⟩
    obtain ⟨a,b,hab⟩ := (unit_scaled_representation_iff u v h F p 0).mp hp'
    exact Ideal.mem_span_pair.mpr ⟨a,b,by simpa using hab.symm⟩

def normalizedCubicTail (hcoeff : FullInvariantIndex 3 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex)) : FullCubicTailIndex → R :=
  fun e => (↑hu.unit⁻¹ : R) * hcoeff e.val

def normalizedSexticTail (Fcoeff : FullInvariantIndex 6 → R)
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) : FullSexticTailIndex → R :=
  fun e => (↑Fu.unit⁻¹ : R) * Fcoeff e.val

theorem fullCubic_eq_unit_mul (hcoeff : FullInvariantIndex 3 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex)) :
    fullInvariantPolynomial 3 hcoeff =
      C (hu.unit : R) * normalizedFullCubic (normalizedCubicTail hcoeff hu) := by
  rw [fullInvariantPolynomial_cubic]
  exact (congrArg (fun z => rawFullCubic z (fun e => hcoeff e.val))
    hu.unit_spec.symm).trans (rawFullCubic_eq_unit_mul hu.unit _)

theorem fullSextic_eq_unit_mul (Fcoeff : FullInvariantIndex 6 → R)
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) :
    fullInvariantPolynomial 6 Fcoeff =
      C (Fu.unit : R) * normalizedFullSextic (normalizedSexticTail Fcoeff Fu) := by
  rw [fullInvariantPolynomial_sextic]
  exact (congrArg (fun z => rawFullSextic z (fun e => Fcoeff e.val))
    Fu.unit_spec.symm).trans (rawFullSextic_eq_unit_mul Fu.unit _)

theorem fullIdeal_normalized (hcoeff : FullInvariantIndex 3 → R)
    (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) :
    equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) =
      surfaceIdeal R (normalizedCubicTail hcoeff hu) (normalizedSexticTail Fcoeff Fu) := by
  rw [fullCubic_eq_unit_mul hcoeff hu, fullSextic_eq_unit_mul Fcoeff Fu]
  exact equationsIdeal_unit_mul hu.unit Fu.unit _ _

/-- This equivalence is induced by the identity on the original five coordinates. -/
def fullSurfaceEquiv (hcoeff : FullInvariantIndex 3 → R)
    (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) :
    (Poly R ⧸ equationsIdeal (fullInvariantPolynomial 3 hcoeff)
      (fullInvariantPolynomial 6 Fcoeff)) ≃ₐ[Base R]
      SurfaceRing R (normalizedCubicTail hcoeff hu) (normalizedSexticTail Fcoeff Fu) :=
  Ideal.quotientEquivAlgOfEq (Base R) (fullIdeal_normalized hcoeff Fcoeff hu Fu)

@[simp] theorem fullSurfaceEquiv_mk (hcoeff : FullInvariantIndex 3 → R)
    (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : Poly R) :
    fullSurfaceEquiv hcoeff Fcoeff hu Fu (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ p := rfl

variable (R) [IsDomain R]

def universalCubicTail : FullCubicTailIndex → ParameterRing R :=
  normalizedCubicTail (cubicCoefficient R) (leading_coefficients_units R).1

def universalSexticTail : FullSexticTailIndex → ParameterRing R :=
  normalizedSexticTail (sexticCoefficient R) (leading_coefficients_units R).2

theorem universalIdeal_normalized :
    equationsIdeal (fullInvariantPolynomial 3 (cubicCoefficient R))
      (fullInvariantPolynomial 6 (sexticCoefficient R)) =
      surfaceIdeal (ParameterRing R) (universalCubicTail R) (universalSexticTail R) :=
  fullIdeal_normalized _ _ (leading_coefficients_units R).1
    (leading_coefficients_units R).2

/-- The equality of the actual surface ideals is compatible with every
coefficient-ring map, including maps to a pointed generic trace field. -/
theorem mapped_universalIdeal_normalized {S : Type*} [CommRing S]
    (f : ParameterRing R →+* S) :
    equationsIdeal (fullInvariantPolynomial 3 (fun i => f (cubicCoefficient R i)))
      (fullInvariantPolynomial 6 (fun i => f (sexticCoefficient R i))) =
      surfaceIdeal S (fun i => f (universalCubicTail R i))
        (fun i => f (universalSexticTail R i)) := by
  have h := congrArg (fun I : Ideal (Poly (ParameterRing R)) =>
    I.map (MvPolynomial.map f)) (universalIdeal_normalized R)
  simpa only [equationsIdeal, surfaceIdeal, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton, map_fullInvariantPolynomial, map_cubic, map_sextic,
    Function.comp_def] using h

theorem seed_normalized_ideal (r ι : R) :
    equationsIdeal (smoothH ι) (smoothF r ι) =
      surfaceIdeal R
        (fun i => seedSpecialization R r ι (universalCubicTail R i))
        (fun i => seedSpecialization R r ι (universalSexticTail R i)) := by
  have h := mapped_universalIdeal_normalized R (seedSpecialization R r ι).toRingHom
  simpa only [seedSpecialization, specialization_cubicCoefficient,
    specialization_sexticCoefficient, seedCubicCoefficients_polynomial,
    seedSexticCoefficients_polynomial, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h

end CycleQ2UniversalSurfaceNormalization

#print axioms CycleQ2UniversalSurfaceNormalization.fullSurfaceEquiv_mk
#print axioms CycleQ2UniversalSurfaceNormalization.mapped_universalIdeal_normalized
#print axioms CycleQ2UniversalSurfaceNormalization.seed_normalized_ideal
end
end


/- Component: continuation_20261112/UniversalSurfaceCharacterPersistence.lean -/
section
/-!
# Actual coefficient maps, persistence, and tensor base change in every character

All maps are induced by the original quotient/localization coefficient maps.
The character-one specialization is the rank-eight piece required by the
ambient test; the already checked character-zero modules remain unchanged.
The construction and seed identification of the geometric ambient-test
class are still separate tasks.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceCharacterPersistence

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree CycleQ2UniversalSurface
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2CharacterTopCech CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates
  CycleQ2UniversalSurfaceCharacterCech CycleQ2UniversalSurfaceCoefficientMap
open CycleQ2SeedCechTopCohomology (topExponent)
open CycleQ2UniversalSurfaceCechPersistence (localMap_smul)
open scoped TensorProduct

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (χ : ZMod 3)

def gradedLocalMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) :
    gradedLocal R χ hcoeff Fcoeff s →ₛₗ[f]
      gradedLocal S χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s where
  toFun p := ⟨localMap f hcoeff Fcoeff s p.val, by
    intro ab e he
    change (localizedCoordinates S _ _ s (localMap f hcoeff Fcoeff s p.val) ab).coeff e = 0
    rw [coordinates_localMap, laurentMap_coeff]
    exact (congrArg f (p.property ab e he)).trans (map_zero f)⟩
  map_add' p q := by apply Subtype.ext; exact map_add (localMap f hcoeff Fcoeff s) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact localMap_smul f hcoeff Fcoeff s c p.val

def actualCoordinates [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ActualTopCechQuotient R χ hcoeff Fcoeff ≃ₗ[R] ((TopIndex χ) →₀ R) :=
  (actualTopEquiv R χ hcoeff Fcoeff).trans (topCechEquiv R χ)

@[simp] theorem actualCoordinates_mk [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R χ hcoeff Fcoeff Finset.univ) :
    actualCoordinates χ hcoeff Fcoeff (Submodule.Quotient.mk p) =
      topProjection R χ (gradedCoordinates R χ hcoeff Fcoeff Finset.univ p) := by
  change topCechEquiv R χ (Submodule.Quotient.mk
    (gradedCoordinates R χ hcoeff Fcoeff Finset.univ p)) = _
  exact topCechEquiv_mk R χ _

theorem mem_actualBoundary_iff [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R χ hcoeff Fcoeff Finset.univ) :
    p ∈ actualBoundary R χ hcoeff Fcoeff ↔
      topProjection R χ (gradedCoordinates R χ hcoeff Fcoeff Finset.univ p) = 0 := by
  rw [← actualCoordinates_mk]
  rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]

theorem gradedLocalMap_mem_boundary [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R χ hcoeff Fcoeff Finset.univ)
    (hp : p ∈ actualBoundary R χ hcoeff Fcoeff) :
    gradedLocalMap χ f hcoeff Fcoeff Finset.univ p ∈
      actualBoundary S χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) := by
  apply (mem_actualBoundary_iff χ _ _ _).mpr
  ext q
  change (localizedCoordinates S _ _ Finset.univ
      (localMap f hcoeff Fcoeff Finset.univ p.val) q.val.1).coeff
      (topExponent q.val.2) = 0
  rw [coordinates_localMap, laurentMap_coeff]
  have hz := congrArg (fun z : (TopIndex χ) →₀ R => z q)
    ((mem_actualBoundary_iff χ hcoeff Fcoeff p).mp hp)
  change (localizedCoordinates R hcoeff Fcoeff Finset.univ p.val q.val.1).coeff
    (topExponent q.val.2) = 0 at hz
  rw [hz, map_zero]

/-- The map on actual cohomology induced by coefficient specialization. -/
def actualTopMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ActualTopCechQuotient R χ hcoeff Fcoeff →ₛₗ[f]
      ActualTopCechQuotient S χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) :=
  (actualBoundary R χ hcoeff Fcoeff).mapQ
    (actualBoundary S χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)))
    (gradedLocalMap χ f hcoeff Fcoeff Finset.univ)
    (by intro p hp; exact gradedLocalMap_mem_boundary χ f hcoeff Fcoeff p hp)

@[simp] theorem actualTopMap_mk [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R χ hcoeff Fcoeff Finset.univ) :
    actualTopMap χ f hcoeff Fcoeff (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (gradedLocalMap χ f hcoeff Fcoeff Finset.univ p) := rfl

theorem coordinates_actualTopMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R χ hcoeff Fcoeff) (q : (TopIndex χ)) :
    actualCoordinates χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i))
        (actualTopMap χ f hcoeff Fcoeff z) q =
      f (actualCoordinates χ hcoeff Fcoeff z q) := by
  refine Submodule.Quotient.induction_on _ z ?_
  intro p
  rw [actualTopMap_mk, actualCoordinates_mk, actualCoordinates_mk]
  change (localizedCoordinates S _ _ Finset.univ
      (localMap f hcoeff Fcoeff Finset.univ p.val) q.val.1).coeff
      (topExponent q.val.2) = _
  rw [coordinates_localMap, laurentMap_coeff]
  rfl

/-- In particular, faithful coefficient extension is faithful on these actual
cohomology classes.  No generic flatness theorem is a hypothesis. -/
theorem actualTopMap_injective [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hf : Function.Injective f)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    Function.Injective (actualTopMap χ f hcoeff Fcoeff) := by
  intro z w hzw
  apply (actualCoordinates χ hcoeff Fcoeff).injective
  ext q
  apply hf
  simpa only [coordinates_actualTopMap] using
    congrArg (fun u => actualCoordinates χ (fun i => f (hcoeff i))
      (fun i => f (Fcoeff i)) u q) hzw

/-- The pointed generic-component condition, applied to actual cohomology.
Only the scalar kernel containment is supplied; freeness and coefficient
compatibility of this concrete Cech quotient were proved above. -/
theorem nonzero_generic_of_nonzero_specialization
    [Nontrivial R] [Nontrivial S] [Nontrivial T]
    (generic : R →+* S) (specialization : R →+* T)
    (hpointed : ∀ c : R, generic c = 0 → specialization c = 0)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R χ hcoeff Fcoeff)
    (hz : actualTopMap χ specialization hcoeff Fcoeff z ≠ 0) :
    actualTopMap χ generic hcoeff Fcoeff z ≠ 0 := by
  intro hzero
  apply hz
  apply (actualCoordinates χ (fun i => specialization (hcoeff i))
    (fun i => specialization (Fcoeff i))).injective
  ext q
  rw [coordinates_actualTopMap, map_zero, Finsupp.zero_apply]
  apply hpointed
  have hq := congrArg (fun u => actualCoordinates χ (fun i => generic (hcoeff i))
    (fun i => generic (Fcoeff i)) u q) hzero
  simpa only [coordinates_actualTopMap, map_zero, Finsupp.zero_apply] using hq

/-- Every coordinate functional of the actual top cohomology is natural
under coefficient specialization, in the specified character. -/
def traceCoordinate [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (q : (TopIndex χ)) : ActualTopCechQuotient R χ hcoeff Fcoeff →ₗ[R] R :=
  (Finsupp.lapply q).comp (actualCoordinates χ hcoeff Fcoeff).toLinearMap

@[simp] theorem traceCoordinate_specialization [Nontrivial R] [Nontrivial S]
    (f : R →+* S) (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R)
    (z : ActualTopCechQuotient R χ hcoeff Fcoeff) (q : (TopIndex χ)) :
    traceCoordinate χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) q
      (actualTopMap χ f hcoeff Fcoeff z) = f (traceCoordinate χ hcoeff Fcoeff q z) :=
  coordinates_actualTopMap χ f hcoeff Fcoeff z q


section TensorBaseChange
variable [Algebra R S] [Nontrivial R] [Nontrivial S]

def coordinateBasis (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Basis (TopIndex χ) R (ActualTopCechQuotient R χ hcoeff Fcoeff) :=
  Module.Basis.ofRepr (actualCoordinates χ hcoeff Fcoeff)

def actualBaseChange (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    (S ⊗[R] ActualTopCechQuotient R χ hcoeff Fcoeff) ≃ₗ[S]
      ActualTopCechQuotient S χ (fun i => algebraMap R S (hcoeff i))
        (fun i => algebraMap R S (Fcoeff i)) :=
  ((coordinateBasis χ hcoeff Fcoeff).baseChange S).repr.trans
    (actualCoordinates χ (fun i => algebraMap R S (hcoeff i))
      (fun i => algebraMap R S (Fcoeff i))).symm

@[simp] theorem actualBaseChange_tmul (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) (s : S)
    (z : ActualTopCechQuotient R χ hcoeff Fcoeff) :
    actualBaseChange χ hcoeff Fcoeff (s ⊗ₜ[R] z) =
      s • actualTopMap χ (algebraMap R S) hcoeff Fcoeff z := by
  apply (actualCoordinates χ (fun i => algebraMap R S (hcoeff i))
    (fun i => algebraMap R S (Fcoeff i))).injective
  ext q
  simp only [actualBaseChange, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    Module.Basis.baseChange_repr_tmul, map_smul, Finsupp.smul_apply,
    coordinates_actualTopMap]
  change actualCoordinates χ hcoeff Fcoeff z q • s =
    s * algebraMap R S (actualCoordinates χ hcoeff Fcoeff z q)
  rw [Algebra.smul_def, mul_comm]

end TensorBaseChange

end CycleQ2UniversalSurfaceCharacterPersistence

#print axioms CycleQ2UniversalSurfaceCharacterPersistence.actualTopMap_injective
#print axioms CycleQ2UniversalSurfaceCharacterPersistence.nonzero_generic_of_nonzero_specialization
#print axioms CycleQ2UniversalSurfaceCharacterPersistence.actualBaseChange_tmul
end
end


/- Component: continuation_20261112/IncidenceTraceCechPersistence.lean -/
section
/-!
# Actual top-Cech persistence on the finite pointed incidence trace family

The pointedness already proved for the literal trace point is a kernel
containment on the polynomial parameter ring.  We extend it across the two
inverted leading coefficients and then apply the proved seven-coordinate
description of actual top Cech cohomology.

This theorem transports a supplied universal class with its identified seed
specialization.  It does not identify an Abel--Jacobi map, and it does not
assert that the fixed-sextic family's normal obstruction is nonzero.  The
relevant prospective input is an ambient-test class, which must be constructed
and compared with the seed normal/residue calculation separately.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceTraceCechPersistence

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SegreFullJacobianBounds
  CycleQ2PolynomialAffineSlice CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceDirection CycleQ2IncidenceTraceDerivative
  CycleQ2IncidenceTraceGenericPoint CycleQ2IncidenceTraceGeometry
  CycleQ2IncidenceGenericPointSemantics CycleQ2IncidenceImageLine
  CycleQ2SeedQuotientFiniteFree CycleQ2UniversalSurface
  CycleQ2UniversalSurfaceNormalization CycleQ2UniversalSurfaceTopCech
  CycleQ2UniversalSurfaceCechPersistence
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

/-- Kernel containment of the two coefficient maps survives localization.
No specialization of the generic field itself is asserted or needed. -/
theorem kernel_containment_away
    {R A S T : Type*} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] (r : R) [IsLocalization.Away r A]
    (generic : A →+* S) (specialization : A →+* T)
    (hpointed : ∀ p : R, generic (algebraMap R A p) = 0 →
      specialization (algebraMap R A p) = 0) :
    ∀ a : A, generic a = 0 → specialization a = 0 := by
  intro a ha
  obtain ⟨n,p,hp⟩ := IsLocalization.Away.surj r a
  have hpg : generic (algebraMap R A p) = 0 := by
    rw [← hp, map_mul, ha, zero_mul]
  have hps := hpointed p hpg
  have hmul : specialization a * specialization (algebraMap R A r) ^ n = 0 := by
    simpa only [map_mul, map_pow] using (congrArg specialization hp).trans hps
  have hu : IsUnit (specialization (algebraMap R A r) ^ n) :=
    ((IsLocalization.Away.algebraMap_isUnit (S := A) r).map specialization).pow n
  exact hu.mul_left_eq_zero.mp hmul

variable {S : Type} [CommRing S] [Algebra ℂ S]

def pointSpecialization (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) : ParameterRing ℂ →ₐ[ℂ] S :=
  specialization (pointCubic y) (pointSextic y)
    (point_leading_units y hy).1 (point_leading_units y hy).2 (pointMatrix y)

@[simp] theorem pointSpecialization_polynomial (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) (p : ParameterPolynomial ℂ) :
    pointSpecialization y hy (algebraMap (ParameterPolynomial ℂ) (ParameterRing ℂ) p) =
      aeval y p := by
  rw [pointSpecialization, specialization_polynomial, polynomialSpecialization,
    coefficientPoint_components]

@[simp] theorem pointSpecialization_cubic (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) (e : FullInvariantIndex 3) :
    pointSpecialization y hy (cubicCoefficient ℂ e) = pointCubic y e := by
  exact specialization_cubicCoefficient _ _ _ _ _ e

@[simp] theorem pointSpecialization_sextic (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) (e : FullInvariantIndex 6) :
    pointSpecialization y hy (sexticCoefficient ℂ e) = pointSextic y e := by
  exact specialization_sexticCoefficient _ _ _ _ _ e

@[simp] theorem seedSpecialization_polynomial (p : ParameterPolynomial ℂ) :
    seedSpecialization ℂ (57 : ℂ) Complex.I
      (algebraMap (ParameterPolynomial ℂ) (ParameterRing ℂ) p) =
      eval (seedPoint (57 : ℂ) Complex.I) p := by
  rw [seedSpecialization, specialization_polynomial]
  rfl

theorem pointSurface_ideal_normalized (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) :
    equationsIdeal
      (MvPolynomial.map (pointMap y) CycleQ2IncidenceBasepointOpen.familyH)
      (MvPolynomial.map (pointMap y) CycleQ2IncidenceBasepointOpen.familyF) =
      surfaceIdeal S
        (fun i => pointSpecialization y hy (universalCubicTail ℂ i))
        (fun i => pointSpecialization y hy (universalSexticTail ℂ i)) := by
  rw [pointMap_familyH, pointMap_familyF]
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    pointSpecialization_cubic, pointSpecialization_sextic] using
    mapped_universalIdeal_normalized ℂ (pointSpecialization y hy).toRingHom

/-- The literal surface supporting the already-constructed image line is
the normalized surface used in the actual Cech calculation. -/
def pointSurfaceEquiv (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) :
    PointSurface y ≃ₐ[Base S]
      SurfaceRing S
        (fun i => pointSpecialization y hy (universalCubicTail ℂ i))
        (fun i => pointSpecialization y hy (universalSexticTail ℂ i)) :=
  Ideal.quotientEquivAlgOfEq (Base S) (pointSurface_ideal_normalized y hy)

@[simp] theorem pointSurfaceEquiv_mk (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) (p : Poly S) :
    pointSurfaceEquiv y hy (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

variable [Algebra TraceRing S] [IsScalarTower ℂ TraceRing S]

theorem pointedTrace_polynomial_kernel
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsPointedTracePoint P B c z)
    (p : ParameterPolynomial ℂ) (hp : aeval (tracePointValue B z) p = 0) :
    eval (seedPoint (57 : ℂ) Complex.I) p = 0 := by
  have hp' : aeval (tracePointValue B z)
      (MvPolynomial.map (C : ℂ →+* TraceRing) p) = 0 := by
    rwa [eval_coefficient_map]
  have hs := hz.2 (MvPolynomial.map (C : ℂ →+* TraceRing) p) hp'
  simpa only [eval_coefficientMap] using hs

theorem pointedTrace_localized_kernel
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsPointedTracePoint P B c z) :
    ∀ a : ParameterRing ℂ,
      pointSpecialization (tracePointValue B z) (tracePoint_leading_unit P B c z hz.1) a = 0 →
        seedSpecialization ℂ (57 : ℂ) Complex.I a = 0 := by
  apply kernel_containment_away (leadingProduct ℂ)
    (pointSpecialization (tracePointValue B z) (tracePoint_leading_unit P B c z hz.1)).toRingHom
    (seedSpecialization ℂ (57 : ℂ) Complex.I).toRingHom
  intro p hp
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pointSpecialization_polynomial] at hp
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, seedSpecialization_polynomial]
  exact pointedTrace_polynomial_kernel P B c z hz p hp

abbrev UniversalTopCech :=
  ActualTopCechQuotient (ParameterRing ℂ) (universalCubicTail ℂ) (universalSexticTail ℂ)

/-- Actual cohomology persistence for the proved finite pointed trace family.
The class must be one universal class with a nonzero identified seed image;
coefficient motion alone is not used as a substitute for that identification. -/
theorem tracePoint_top_nonzero [Nontrivial S]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsPointedTracePoint P B c z)
    (ξ : UniversalTopCech)
    (hξ : actualTopMap (seedSpecialization ℂ (57 : ℂ) Complex.I).toRingHom
      (universalCubicTail ℂ) (universalSexticTail ℂ) ξ ≠ 0) :
    actualTopMap
      (pointSpecialization (tracePointValue B z)
        (tracePoint_leading_unit P B c z hz.1)).toRingHom
      (universalCubicTail ℂ) (universalSexticTail ℂ) ξ ≠ 0 := by
  apply nonzero_generic_of_nonzero_specialization
    (pointSpecialization (tracePointValue B z)
      (tracePoint_leading_unit P B c z hz.1)).toRingHom
    (seedSpecialization ℂ (57 : ℂ) Complex.I).toRingHom
    (pointedTrace_localized_kernel P B c z hz)
    (universalCubicTail ℂ) (universalSexticTail ℂ) ξ hξ

end CycleQ2IncidenceTraceCechPersistence

#print axioms CycleQ2IncidenceTraceCechPersistence.pointSurfaceEquiv_mk
#print axioms CycleQ2IncidenceTraceCechPersistence.pointedTrace_localized_kernel
#print axioms CycleQ2IncidenceTraceCechPersistence.tracePoint_top_nonzero
end
end


/- Component: continuation_20261112/IncidenceSurfaceGradientOpen.lean -/
section
/-! The actual pointed trace surface is covered by its genuine Jacobian
minor opens. The seed cover is propagated by a proved coefficient open,
using pointedness rather than assuming smoothness of a moving surface. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceSurfaceGradientOpen
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2HomogeneousIdealArithmetic CycleQ2HomogeneousPrimeCoverOpen
open CycleQ2IncidenceBasepointOpen (Coeff familyF familyH seedEvaluation)

theorem seed_prime_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hP : generatorIdeal (fun i => map seedEvaluation (generators i)) ≤ P) :
    ∀ j : Fin 5, X j ∈ P := by
  have hmem (i : Index) : map seedEvaluation (generators i) ∈ P :=
    hP (Ideal.subset_span ⟨i,rfl⟩)
  have hF : smoothF (57:ℂ) Complex.I ∈ P := by
    simpa only [generators,Matrix.cons_val_zero,familyF_seed] using hmem (Sum.inl 0)
  have hh : smoothH Complex.I ∈ P := by
    simpa only [generators,Matrix.cons_val_one,Matrix.cons_val_zero,familyH_seed]
      using hmem (Sum.inl 1)
  intro j
  by_contra hj
  obtain ⟨a,b,hab⟩ := CycleQ2SeedSurfaceGradient.prime_minor_cover P hF hh ⟨j,hj⟩
  apply hab
  have hm := hmem (Sum.inr (a,b))
  rw [generators,map_pow,minor_map,familyF_seed,familyH_seed] at hm
  exact (inferInstance : P.IsPrime).mem_of_pow_mem 3 hm

/-- This open is proved nonempty by the literal r=57,theta=1 seed. -/
theorem exists_surface_minor_open : ∃ s : Coeff, seedEvaluation s=1 ∧
    ∀ (S : Type*) [CommRing S] (φ : Coeff →+* S), IsUnit (φ s) →
      ∀ (P : Ideal (Poly S)) [P.IsPrime],
        map φ familyF ∈ P → map φ familyH ∈ P →
        (∃ j : Fin 5, X j ∉ P) →
        ∃ j k : Fin 5, minor (map φ familyF) (map φ familyH) j k ∉ P := by
  obtain ⟨s,hs,hopen⟩ := exists_prime_cover_open seedEvaluation C
    CycleQ2IncidenceBasepointOpen.seedEvaluation_constant generators degree
    generators_homogeneous seed_prime_cover
  refine ⟨s,hs,?_⟩
  intro S _ φ hφ P _ hF hh hx
  by_contra hn
  push_neg at hn
  have hP : generatorIdeal (fun i => map φ (generators i)) ≤ P := by
    rw [generatorIdeal,Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl j =>
      fin_cases j
      · simpa [generators] using hF
      · simpa [generators] using hh
    | inr jk =>
      rcases jk with ⟨j,k⟩
      change map φ (minor familyF familyH j k ^ 3) ∈ P
      rw [map_pow,minor_map]
      exact Ideal.pow_mem_of_mem P (hn j k) 3 (by decide)
  obtain ⟨j,hj⟩ := hx
  exact hj (hopen S φ hφ P hP j)

theorem pointed_surface_prime_cover {L : Type*} [Field L]
    (φ : Coeff →+* L) (hpointed : ∀ a, φ a=0 → seedEvaluation a=0)
    (P : Ideal (Poly L)) [P.IsPrime]
    (hF : map φ familyF ∈ P) (hh : map φ familyH ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j k : Fin 5, minor (map φ familyF) (map φ familyH) j k ∉ P := by
  obtain ⟨s,hs,hopen⟩ := exists_surface_minor_open
  have hu : IsUnit (φ s) := isUnit_iff_ne_zero.mpr (fun hz =>
    one_ne_zero (hs.symm.trans (hpointed s hz)))
  exact hopen L φ hu P hF hh hx

section Trace
open CycleQ2IncidenceTraceCechPersistence CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceGeometry CycleQ2IncidenceTraceGenericPoint
  CycleQ2IncidenceLocalDerivations CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2SegreFullJacobianBounds CycleQ2PolynomialAffineSlice
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidenceTraceFieldDerivation
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

variable {L : Type} [Field L] [Algebra TraceField L]
  [Algebra TraceRing L] [IsScalarTower TraceRing TraceField L]
  [Algebra ℂ L] [IsScalarTower ℂ TraceRing L] [FiniteDimensional TraceField L]

/-- The actual Jacobian localizations used by actualLocalTime cover every
relevant prime of the actual finite pointed trace surface. -/
theorem actual_trace_prime_minor_cover
    (Q : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → L) (hz : IsPointedTracePoint Q B c z)
    (P : Ideal (Poly L)) [P.IsPrime]
    (hF : actualF B z ∈ P) (hh : actualH B z ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j k : Fin 5, minor (actualF B z) (actualH B z) j k ∉ P := by
  rw [actualF_eq_specialized] at hF ⊢
  rw [actualH_eq_specialized] at hh ⊢
  apply pointed_surface_prime_cover (CycleQ2IncidenceImageLine.pointMap (tracePointValue B z))
    (fun a ha => ?_) P hF hh hx
  exact pointedTrace_polynomial_kernel Q B c z hz a ha

end Trace
end CycleQ2IncidenceSurfaceGradientOpen

#print axioms CycleQ2IncidenceSurfaceGradientOpen.exists_surface_minor_open
#print axioms CycleQ2IncidenceSurfaceGradientOpen.actual_trace_prime_minor_cover
end
end


/- Component: continuation_20261112/IncidenceTraceComponent.lean -/
section
/-!
# Cohomology on the actual pointed component of the incidence trace family

We first retain the chosen extra open (in particular the actual basepoint
open), then quotient by the kernel of the constructed trace-point map.
This coefficient ring maps injectively to the generic coefficient field
and has the literal r=57,i seed specialization.  Its incidence equations
vanish, and the retained open is a unit.  An ambient test class can therefore
be defined on this component itself; no lift to the unconstrained parameter
space is required by the persistence theorem.

The geometric class and the equality of its seed image with the computed
normal/residue class remain separate construction and comparison tasks.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceTraceComponent

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialRelations
  CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SegreFullJacobianBounds
  CycleQ2IncidenceTraceFamily CycleQ2IncidenceTraceDirection
  CycleQ2IncidenceTraceGenericPoint CycleQ2IncidenceTraceGeometry
  CycleQ2UniversalSurfaceNormalization CycleQ2UniversalSurfaceTopCech
  CycleQ2UniversalSurfaceCechPersistence CycleQ2IncidenceTraceCechPersistence
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

def extraOpenElement (c : ParameterPolynomial ℂ) : ParameterRing ℂ :=
  algebraMap (ParameterPolynomial ℂ) (ParameterRing ℂ) c

abbrev TraceOpen (c : ParameterPolynomial ℂ) := Localization.Away (extraOpenElement c)

def openSeed (c : ParameterPolynomial ℂ)
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1) : TraceOpen c →+* ℂ :=
  IsLocalization.Away.lift (extraOpenElement c)
    (g := (seedSpecialization ℂ (57 : ℂ) Complex.I).toRingHom) (by
      change IsUnit (seedSpecialization ℂ (57 : ℂ) Complex.I (extraOpenElement c))
      rw [extraOpenElement, seedSpecialization_polynomial, hc]
      exact isUnit_one)

@[simp] theorem openSeed_algebraMap (c : ParameterPolynomial ℂ)
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1) (a : ParameterRing ℂ) :
    openSeed c hc (algebraMap (ParameterRing ℂ) (TraceOpen c) a) =
      seedSpecialization ℂ (57 : ℂ) Complex.I a := by
  exact IsLocalization.Away.lift_eq _ _ _

variable {S : Type} [CommRing S] [Algebra ℂ S] [Algebra TraceRing S]
  [IsScalarTower ℂ TraceRing S]

variable (P : Matrix SquareIndex ColumnIndex ℂ)
  (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
  (z : SquareIndex → S) (hz : IsPointedTracePoint P B c z)

def openGeneric : TraceOpen c →+* S :=
  IsLocalization.Away.lift (extraOpenElement c)
    (g := (pointSpecialization (tracePointValue B z)
      (tracePoint_leading_unit P B c z hz.1)).toRingHom) (by
      change IsUnit (pointSpecialization (tracePointValue B z)
        (tracePoint_leading_unit P B c z hz.1) (extraOpenElement c))
      rw [extraOpenElement, pointSpecialization_polynomial]
      exact tracePoint_extra_unit P B c z hz.1)

@[simp] theorem openGeneric_algebraMap (a : ParameterRing ℂ) :
    openGeneric P B c z hz (algebraMap (ParameterRing ℂ) (TraceOpen c) a) =
      pointSpecialization (tracePointValue B z)
        (tracePoint_leading_unit P B c z hz.1) a := by
  exact IsLocalization.Away.lift_eq _ _ _

theorem pointed_open_kernel
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1) :
    ∀ a : TraceOpen c, openGeneric P B c z hz a = 0 → openSeed c hc a = 0 := by
  apply kernel_containment_away (extraOpenElement c)
    (openGeneric P B c z hz) (openSeed c hc)
  intro a ha
  rw [openGeneric_algebraMap] at ha
  rw [openSeed_algebraMap]
  exact pointedTrace_localized_kernel P B c z hz a ha

abbrev ComponentRing := TraceOpen c ⧸ RingHom.ker (openGeneric P B c z hz)

def componentGeneric : ComponentRing P B c z hz →+* S :=
  (openGeneric P B c z hz).kerLift

theorem componentGeneric_injective : Function.Injective (componentGeneric P B c z hz) :=
  RingHom.kerLift_injective _

instance componentNontrivial [Nontrivial S] : Nontrivial (ComponentRing P B c z hz) :=
  (componentGeneric P B c z hz).domain_nontrivial

def componentSeed (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1) :
    ComponentRing P B c z hz →+* ℂ :=
  Ideal.Quotient.lift _ (openSeed c hc) (by
    intro a ha
    exact pointed_open_kernel P B c z hz hc a (RingHom.mem_ker.mp ha))

def componentCoefficients : ParameterRing ℂ →+* ComponentRing P B c z hz :=
  (Ideal.Quotient.mk _).comp (algebraMap (ParameterRing ℂ) (TraceOpen c))

@[simp] theorem componentGeneric_coefficients (a : ParameterRing ℂ) :
    componentGeneric P B c z hz (componentCoefficients P B c z hz a) =
      pointSpecialization (tracePointValue B z)
        (tracePoint_leading_unit P B c z hz.1) a := by
  simp only [componentGeneric, componentCoefficients, RingHom.comp_apply,
    RingHom.kerLift_mk, openGeneric_algebraMap]

@[simp] theorem componentSeed_coefficients
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1) (a : ParameterRing ℂ) :
    componentSeed P B c z hz hc (componentCoefficients P B c z hz a) =
      seedSpecialization ℂ (57 : ℂ) Complex.I a := by
  simp only [componentSeed, componentCoefficients, RingHom.comp_apply,
    Ideal.Quotient.lift_mk, openSeed_algebraMap]

/-- The retained geometric open is a unit on the whole component ring,
not just at its generic coefficient-field point. -/
theorem component_extraOpen_isUnit :
    IsUnit (componentCoefficients P B c z hz (extraOpenElement c)) :=
  (IsLocalization.Away.algebraMap_isUnit (S := TraceOpen c) (extraOpenElement c)).map
    (Ideal.Quotient.mk (RingHom.ker (openGeneric P B c z hz)))

/-- The actual cleared incidence equations vanish on this component. -/
theorem component_incidence_equations (q : ColumnIndex) :
    componentCoefficients P B c z hz
      (algebraMap (ParameterPolynomial ℂ) (ParameterRing ℂ)
        ((presentation ℂ 57).equation q)) = 0 := by
  apply componentGeneric_injective P B c z hz
  rw [componentGeneric_coefficients, map_zero, pointSpecialization_polynomial]
  exact tracePoint_original_equations P B c z hz.1 q

def componentCubic : FullCubicTailIndex → ComponentRing P B c z hz :=
  fun i => componentCoefficients P B c z hz (universalCubicTail ℂ i)

def componentSextic : FullSexticTailIndex → ComponentRing P B c z hz :=
  fun i => componentCoefficients P B c z hz (universalSexticTail ℂ i)

abbrev ComponentTopCech [Nontrivial S] :=
  ActualTopCechQuotient (ComponentRing P B c z hz)
    (componentCubic P B c z hz) (componentSextic P B c z hz)

/-- The actual top-Cech coefficient map to the generic point is injective. -/
theorem componentTop_generic_injective [Nontrivial S] :
    Function.Injective (actualTopMap (componentGeneric P B c z hz)
      (componentCubic P B c z hz) (componentSextic P B c z hz)) :=
  actualTopMap_injective _ (componentGeneric_injective P B c z hz) _ _

/-- Persistence for a class constructed on the actual pointed component.
This requires no lift of that class to the unconstrained parameter space. -/
theorem componentTop_nonzero [Nontrivial S]
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1)
    (ξ : ComponentTopCech P B c z hz)
    (hξ : actualTopMap (componentSeed P B c z hz hc)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0) :
    actualTopMap (componentGeneric P B c z hz)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0 := by
  intro hzero
  have hξzero : ξ = 0 := (componentTop_generic_injective P B c z hz)
    (hzero.trans (map_zero _).symm)
  exact hξ (by rw [hξzero, map_zero])

end CycleQ2IncidenceTraceComponent

#print axioms CycleQ2IncidenceTraceComponent.component_extraOpen_isUnit
#print axioms CycleQ2IncidenceTraceComponent.component_incidence_equations
#print axioms CycleQ2IncidenceTraceComponent.componentTop_generic_injective
#print axioms CycleQ2IncidenceTraceComponent.componentTop_nonzero
end
end


