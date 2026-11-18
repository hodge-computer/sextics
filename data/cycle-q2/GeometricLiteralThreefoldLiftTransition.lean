import Proposal.GeometricLiteralThreefoldChartLift
import Proposal.GeometricLiteralThreefoldResidueChartMaps
import Proposal.GeometricFamilyDeformation

/-!
# The actual first-order transition over every pair of weight-one charts

The inverse of a lifted coordinate uses its first-order coefficient and
the inverse of its reduction. Changing the canonical source lift by this
unit yields a point of the target deformation above the original target
chart map. The construction commutes with further coefficient maps and
two successive changes of chart give the direct change.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldLiftTransition

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2GeometricSurfaceFirstOrder

attribute [local instance] fixedAmbientAlgebra fixedAmbientTower sourceFixedAlgebra sourceFixedTower

private theorem map_linearValues {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (i : Fin 4) (x : Index → R) (l : Fin 4) :
    f (linearValues i x l) = linearValues i (fun a => f (x a)) l := by
  refine Fin.succAboveCases i ?_ (fun a => ?_) l <;> simp [linearValues]

theorem map_changedCoordinate {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (i j : Fin 4) (x : Index → R) (u : R) (a : Index) :
    f (changedCoordinate i j x u a) = changedCoordinate i j (fun a => f (x a)) (f u) a := by
  cases a with
  | none => simp [changedCoordinate]
  | some a =>
    change f (linearValues i x (j.succAbove a) * u) = _
    rw [map_mul, map_linearValues]
    rfl

private theorem linearValues_changed {R : Type*} [CommRing R] [Algebra ℂ R]
    (i j : Fin 4) (x : Index → R) (t : R) (ht : t * linearValues i x j = 1) (l : Fin 4) :
    linearValues j (changedCoordinate i j x t) l = t * linearValues i x l := by
  simpa only [eval_linearCoordinate, linearValues] using changed_linear i j x t ht l

variable {S U : Type*} [CommRing S] [Algebra ℂ S] [CommRing U] [Algebra ℂ U]


/-- Apply the same coefficient homomorphism to both terms of a first-order value. -/
def jetMap (h : S →ₐ[ℂ] U) : Jet S →ₐ[ℂ] Jet U where
  __ := dualMap h.toRingHom
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact h.commutes c
    · exact map_zero h

private theorem jetMap_aeval (h : S →ₐ[ℂ] U) (x : Index → Jet S)
    (p : MvPolynomial Index ℂ) :
    jetMap h (aeval x p) = aeval (fun a => jetMap h (x a)) p := by
  have he : (jetMap h).comp (aeval x) = aeval (fun a => jetMap h (x a)) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp
  exact AlgHom.congr_fun he p

/-- Restriction of a point of the original deformation to another coefficient ring. -/
def mapLift (h : S →ₐ[ℂ] U) {i : Fin 4} (x : Lift i S) : Lift i U where
  x a := jetMap h (x.x a)
  equation := by
    rw [← jetMap_aeval, ← jetMap_aeval, x.equation, map_mul]
    have he : jetMap h (TrivSqZeroExt.inr 1 : Jet S) = (TrivSqZeroExt.inr 1 : Jet U) := by
      apply TrivSqZeroExt.ext
      · exact map_zero h
      · exact map_one h
    rw [he]

@[ext] theorem lift_ext {i : Fin 4} {x y : Lift i S} (h : x.x = y.x) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem mapLift_canonical (h : S →ₐ[ℂ] U) (i : Fin 4) (f : T i →ₐ[ℂ] S) :
    mapLift h (canonical i f) = canonical i (h.comp f) := by
  apply lift_ext
  rfl

theorem mapLift_change_inverse (h : S →ₐ[ℂ] U) {i : Fin 4} (x : Lift i S) (j : Fin 4)
    (u : Jet S) (hu : u * linearValues i x.x j = 1) :
    jetMap h u * linearValues i (mapLift h x).x j = 1 := by
  have he := congrArg (jetMap h) hu
  rw [map_mul, map_one] at he
  change jetMap h u * linearValues i (fun a => jetMap h (x.x a)) j = 1
  exact (congrArg (fun z : Jet U => jetMap h u * z)
    (map_linearValues (jetMap h).toRingHom i x.x j).symm).trans he

theorem mapLift_change (h : S →ₐ[ℂ] U) {i : Fin 4} (x : Lift i S) (j : Fin 4)
    (u : Jet S) (hu : u * linearValues i x.x j = 1) :
    mapLift h (change x j u hu) =
      change (mapLift h x) j (jetMap h u) (mapLift_change_inverse h x j u hu) := by
  exact lift_ext (funext fun a => map_changedCoordinate (jetMap h).toRingHom i j x.x u a)

/-- Inverse of a first-order unit, computed from the inverse of its reduction. -/
def inverseJet (z : Jet S) (t : S) : Jet S := (t, -(t^2 * z.snd))

omit [Algebra ℂ S] in
theorem inverseJet_mul (z : Jet S) (t : S) (ht : t * z.fst = 1) :
    inverseJet z t * z = 1 := by
  apply TrivSqZeroExt.ext
  · exact ht
  · change t * z.snd + -(t^2 * z.snd) * z.fst = 0
    linear_combination -(t*z.snd)*ht

abbrev sourceMap (i : Fin 4) (k : Fin 3) : T i →ₐ[ℂ] FixedOverlap i k :=
  IsScalarTower.toAlgHom ℂ (T i) (FixedOverlap i k)

/-- Specialize ambient coordinates to the actual fixed intersection and
then restrict them along the specified map. -/
def coefficients (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) : AmbientOverlap k →+* S :=
  g.toRingHom.comp (algebraMap (AmbientOverlap k) (FixedOverlap i k))

def sourceLift (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) : Lift i S :=
  canonical i (g.comp (sourceMap i k))

theorem sourceLift_fst (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) (a : Index) :
    ((sourceLift i k g).x a).fst = coefficients i k g (overlapCoordinates k a) := by
  change g (sourceMap i k (q i (X a))) = _
  rw [sourceMap, ← fixedSourceMap_eq]
  exact congrArg g (chartMap_coordinate _ i (overlapCoordinates k) (equation_zero i k) a)

private theorem source_inverse (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) :
    coefficients i k g (overlapInverse k) * ((sourceLift i k g).x (some k)).fst = 1 := by
  rw [sourceLift_fst, ← map_mul, overlapInverse_mul, map_one]

/-- The specific invertible coordinate of the actual lifted point on the pairwise overlap. -/
def sourceUnit (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) : (Jet S)ˣ where
  val := (sourceLift i k g).x (some k)
  inv := inverseJet ((sourceLift i k g).x (some k)) (coefficients i k g (overlapInverse k))
  inv_val := inverseJet_mul _ _ (source_inverse i k g)
  val_inv := (mul_comm _ _).trans (inverseJet_mul _ _ (source_inverse i k g))

theorem sourceUnit_normalizes (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) :
    (↑(sourceUnit i k g)⁻¹ : Jet S) * linearValues i (sourceLift i k g).x (i.succAbove k) = 1 := by
  rw [linearValues, Fin.insertNth_apply_succAbove]
  exact (sourceUnit i k g).inv_mul

/-- The canonical source deformation written in target chart coordinates. -/
def normalizedLift (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) :
    Lift (i.succAbove k) S :=
  change (sourceLift i k g) (i.succAbove k) (↑(sourceUnit i k g)⁻¹) (sourceUnit_normalizes i k g)

/-- The target and the normalized source lift the same literal point. -/
theorem normalizedLift_fst (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) (a : Index) :
    ((normalizedLift i k g).x a).fst = g (fixedTargetMap i k (q (i.succAbove k) (X a))) := by
  let π := (TrivSqZeroExt.fstHom ℂ S S).toRingHom
  change π (changedCoordinate i (i.succAbove k) (sourceLift i k g).x
    (↑(sourceUnit i k g)⁻¹ : Jet S) a) = _
  rw [map_changedCoordinate]
  change changedCoordinate i (i.succAbove k) (fun a => ((sourceLift i k g).x a).fst)
    (coefficients i k g (overlapInverse k)) a = _
  simp_rw [sourceLift_fst]
  rw [← map_changedCoordinate]
  exact congrArg g (chartMap_coordinate _ _ _ (targetEquation_zero i k _ (equation_zero i k)) a).symm

/-- Further restrictions carry the full first-order normalization, including
the varying inverse coordinate, to its own normalization on that subopen. -/
theorem normalizedLift_map (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S)
    (h : S →ₐ[ℂ] U) (a : Index) :
    dualMap h.toRingHom ((normalizedLift i k g).x a) = (normalizedLift i k (h.comp g)).x a := by
  change dualMap h.toRingHom (changedCoordinate i (i.succAbove k) (sourceLift i k g).x
    (↑(sourceUnit i k g)⁻¹ : Jet S) a) = _
  rw [map_changedCoordinate]
  have hInv : dualMap h.toRingHom (↑(sourceUnit i k g)⁻¹ : Jet S) =
      (↑(sourceUnit i k (h.comp g))⁻¹ : Jet U) := by
    apply TrivSqZeroExt.ext
    · rfl
    · change h (-(_^2 * _)) = -(_^2 * _)
      rw [map_neg, map_mul, map_pow]
      rfl
  rw [hInv]
  rfl


theorem mapLift_normalized (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S)
    (h : S →ₐ[ℂ] U) : mapLift h (normalizedLift i k g) = normalizedLift i k (h.comp g) :=
  lift_ext (funext (normalizedLift_map i k g h))

local instance sourceFixedLocalization (i : Fin 4) (k : Fin 3) :
    IsLocalization.Away (q i (X (some k))) (FixedOverlap i k) :=
  inferInstanceAs (IsLocalization.Away (Ideal.Quotient.mk (Ideal.span {literalEquation i}) (X (some k)))
    (Localization.Away (Ideal.Quotient.mk (Ideal.span {literalEquation i}) (X (some k)))))

/-- Extend a point of the fixed source chart to the intersection where its
target coordinate is a unit. -/
def overlapLift (i : Fin 4) (k : Fin 3) (f : T i →ₐ[ℂ] S)
    (hf : IsUnit (f (q i (X (some k))))) : FixedOverlap i k →ₐ[ℂ] S :=
  IsLocalization.Away.liftAlgHom (q i (X (some k))) (f := f) hf

theorem overlapLift_source (i : Fin 4) (k : Fin 3) (f : T i →ₐ[ℂ] S)
    (hf : IsUnit (f (q i (X (some k))))) (a : T i) :
    overlapLift i k f hf (sourceMap i k a) = f a :=
  IsLocalization.Away.lift_eq (S := FixedOverlap i k) (g := f.toRingHom) _ hf a

theorem overlapLift_coordinate (i : Fin 4) (k : Fin 3) (f : T i →ₐ[ℂ] S)
    (hf : IsUnit (f (q i (X (some k))))) (a : Index) :
    coefficients i k (overlapLift i k f hf) (overlapCoordinates k a) = f (q i (X a)) := by
  rw [← sourceLift_fst]
  exact overlapLift_source i k f hf _

/-- This formula holds for arbitrary inverses, including genuine units in
square-zero coefficient algebras. -/
theorem overlapLift_target_of_inverse (i : Fin 4) (k : Fin 3) (f : T i →ₐ[ℂ] S)
    (hf : IsUnit (f (q i (X (some k))))) (t : S) (ht : t * f (q i (X (some k))) = 1)
    (a : Index) :
    overlapLift i k f hf (fixedTargetMap i k (q (i.succAbove k) (X a))) =
      changedCoordinate i (i.succAbove k) (fun b => f (q i (X b))) t a := by
  let g := overlapLift i k f hf
  let c := coefficients i k g
  have hi : c (overlapInverse k) = t := by
    have h' : c (overlapInverse k) * f (q i (X (some k))) = 1 := by
      rw [← overlapLift_coordinate i k f hf (some k)]
      change c _ * c _ = 1
      rw [← map_mul, overlapInverse_mul, map_one]
    exact hf.mul_right_cancel (h'.trans ht.symm)
  have hc : (fun b => c (overlapCoordinates k b)) = (fun b => f (q i (X b))) :=
    funext (overlapLift_coordinate i k f hf)
  calc
    _ = c (changedCoordinate i (i.succAbove k) (overlapCoordinates k) (overlapInverse k) a) :=
      congrArg g (chartMap_coordinate _ _ _ (targetEquation_zero i k _ (equation_zero i k)) a)
    _ = _ := by rw [map_changedCoordinate, hc, hi]

theorem overlapLift_target_coordinate (i : Fin 4) (k : Fin 3) (f : T i →ₐ[ℂ] S)
    (hf : IsUnit (f (q i (X (some k))))) (a : Index) :
    overlapLift i k f hf (fixedTargetMap i k (q (i.succAbove k) (X a))) =
      changedCoordinate i (i.succAbove k) (fun b => f (q i (X b))) (↑hf.unit⁻¹) a :=
  overlapLift_target_of_inverse i k f hf _
    ((congrArg (fun b : S => (↑hf.unit⁻¹ : S) * b) hf.unit_spec.symm).trans hf.unit.inv_mul) a

/-- Two successive chart normalizations multiply their inverse coordinates,
including the square-zero part, and give exactly the direct normalization. -/
theorem change_comp (i j l : Fin 4) (x : Lift i S) (u v : Jet S)
    (hu : u * linearValues i x.x j = 1)
    (hv : v * linearValues j (change x j u hu).x l = 1) :
    ∃ h : (v*u) * linearValues i x.x l = 1,
      (change (change x j u hu) l v hv).x = (change x l (v*u) h).x := by
  have h : (v*u) * linearValues i x.x l = 1 := by
    rw [mul_assoc, ← linearValues_changed i j x.x u hu l]
    exact hv
  refine ⟨h, funext fun a => ?_⟩
  cases a with
  | none =>
    change x.x none * u^2 * v^2 = x.x none * (v*u)^2
    ring
  | some a =>
    change linearValues j (changedCoordinate i j x.x u) (l.succAbove a) * v =
      linearValues i x.x (l.succAbove a) * (v*u)
    rw [linearValues_changed i j x.x u hu]
    ring

end CycleQ2LiteralThreefoldLiftTransition
end

#print axioms CycleQ2LiteralThreefoldLiftTransition.normalizedLift_fst
#print axioms CycleQ2LiteralThreefoldLiftTransition.normalizedLift_map
#print axioms CycleQ2LiteralThreefoldLiftTransition.change_comp

#print axioms CycleQ2LiteralThreefoldLiftTransition.overlapLift_target_coordinate
