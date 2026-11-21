import Proposal.GeometricLiteralThreefoldChartEvaluation
import Proposal.GeometricLiteralThreefoldTangentOverlap

/-!
# The actual two-forms of the ambient test on native overlap rings

The section for an ordered pair is the oriented threefold volume evaluated
at the difference between the first chart lift, written in the second chart,
and the second chart lift. The construction commutes with restriction and
with choosing a different reference chart for both lifts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldTestEdges

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldTangentCoordinates CycleQ2LiteralThreefoldLiftDifference
  CycleQ2LiteralThreefoldTangentOverlap CycleQ2LiteralThreefoldChartEvaluation
  CycleQ2ThreefoldContractionAlongMap CycleQ2ExteriorSectionNaturality

variable {S S' : Type} [CommRing S] [Algebra ℂ S] [CommRing S'] [Algebra ℂ S']

/-- Evaluate the oriented volume at the infinitesimal component of a point. -/
def jetValue (i : Fin 4) (v : T i →ₐ[ℂ] Jet S) : Forms S 2 :=
  evaluate i ((TrivSqZeroExt.fstHom ℂ S S).comp v) v (fun _ => rfl)

private theorem jetValue_eq {i : Fin 4} (v : T i →ₐ[ℂ] Jet S) (f : T i →ₐ[ℂ] S)
    (h : ∀ a, (v a).fst = f a) : jetValue i v = evaluate i f v h := by
  have hf : (TrivSqZeroExt.fstHom ℂ S S).comp v = f := AlgHom.ext h
  subst f
  rfl

private theorem jetValue_map (i : Fin 4) (v : T i →ₐ[ℂ] Jet S) (b : S →ₐ[ℂ] S') :
    exteriorDifferentialMap b 2 (jetValue i v) = jetValue i ((jetMap b).comp v) := by
  rw [jetValue, evaluate_map]
  exact (jetValue_eq _ _ (fun _ => rfl)).symm

def value {i : Fin 4} (x y : Lift i S) (h : ∀ a, (x.x a).fst = (y.x a).fst) : Forms S 2 :=
  jetValue i (tangentPoint x y h)

theorem value_cocycle {i : Fin 4} (x y z : Lift i S)
    (hxy : ∀ a, (x.x a).fst = (y.x a).fst) (hyz : ∀ a, (y.x a).fst = (z.x a).fst) :
    value x z (fun a => (hxy a).trans (hyz a)) = value x y hxy + value y z hyz := by
  let π := (TrivSqZeroExt.fstHom ℂ S S)
  let v := tangentPoint x y hxy
  let w := tangentPoint y z hyz
  let t := tangentPoint x z (fun a => (hxy a).trans (hyz a))
  let f := π.comp v
  have hw (a : T i) : (w a).fst = f a := by
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
    change (tangentPoint y z hyz (q i p)).fst = (tangentPoint x y hxy (q i p)).fst
    rw [tangentPoint_mk, tangentPoint_mk]
    exact (aeval_fst_eq _ _ hxy p).symm
  have ht (a : T i) : (t a).fst = f a := by
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
    change (tangentPoint x z (fun a => (hxy a).trans (hyz a)) (q i p)).fst =
      (tangentPoint x y hxy (q i p)).fst
    rw [tangentPoint_mk, tangentPoint_mk]
    rfl
  change jetValue i t = jetValue i v + jetValue i w
  rw [jetValue_eq t f ht, jetValue_eq v f (fun _ => rfl), jetValue_eq w f hw]
  apply evaluate_add
  intro a
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  change (tangentPoint x z (fun a => (hxy a).trans (hyz a)) (q i p)).snd =
    (tangentPoint x y hxy (q i p)).snd + (tangentPoint y z hyz (q i p)).snd
  simp only [tangentPoint_mk, difference, TrivSqZeroExt.snd_mk]
  abel

theorem value_map {i : Fin 4} (x y : Lift i S) (h : ∀ a, (x.x a).fst = (y.x a).fst)
    (b : S →ₐ[ℂ] S') : exteriorDifferentialMap b 2 (value x y h) =
      value (mapLift b x) (mapLift b y) (fun a => congrArg b (h a)) := by
  rw [value, jetValue_map]
  apply congrArg (jetValue i)
  apply chart_ext
  intro a
  change jetMap b (tangentPoint x y h (q i (X a))) = _
  simp only [tangentPoint_mk, aeval_X]
  apply TrivSqZeroExt.ext
  · rfl
  · exact map_sub b _ _

/-- Choosing the other weight-one chart gives the same two-form on the
coefficient algebra, even for two independently normalized lifted points. -/
theorem value_change (i : Fin 4) (k : Fin 3) (x y : Lift i S)
    (h : ∀ a, (x.x a).fst = (y.x a).fst) (u v : Jet S)
    (hu : u * linearValues i x.x (i.succAbove k) = 1)
    (hv : v * linearValues i y.x (i.succAbove k) = 1)
    (h' : ∀ a, ((change x (i.succAbove k) u hu).x a).fst =
      ((change y (i.succAbove k) v hv).x a).fst) :
    value (change x _ u hu) (change y _ v hv) h' = value x y h := by
  obtain ⟨jet, hh, hs, ht⟩ := exists_overlap_jet i k x y h u v hu hv
  let f := (TrivSqZeroExt.fstHom ℂ S S).comp jet
  have H := evaluate_overlap i k f jet (fun _ => rfl)
  change jetValue _ (jet.comp (fixedTargetMap i k)) = jetValue i (jet.comp (sourceMap i k)) at H
  rw [hs, ht] at H
  exact H

/-- A native overlap edge after arbitrary further restriction. -/
def edgeAt (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) : Forms S 2 :=
  value (normalizedLift i k g) (canonical (i.succAbove k) (g.comp (fixedTargetMap i k)))
    (normalizedLift_fst i k g)

def nativeEdge (i : Fin 4) (k : Fin 3) : Forms (FixedOverlap i k) 2 :=
  edgeAt i k (AlgHom.id ℂ (FixedOverlap i k))

theorem edgeAt_map (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) (b : S →ₐ[ℂ] S') :
    exteriorDifferentialMap b 2 (edgeAt i k g) = edgeAt i k (b.comp g) := by
  unfold edgeAt
  rw [value_map]
  simp only [mapLift_normalized, mapLift_canonical]
  rfl

theorem nativeEdge_restrict (i : Fin 4) (k : Fin 3) (g : FixedOverlap i k →ₐ[ℂ] S) :
    exteriorDifferentialMap g 2 (nativeEdge i k) = edgeAt i k g :=
  edgeAt_map i k (AlgHom.id ℂ _) g

end CycleQ2LiteralThreefoldTestEdges
end

#print axioms CycleQ2LiteralThreefoldTestEdges.value_cocycle
#print axioms CycleQ2LiteralThreefoldTestEdges.value_change
#print axioms CycleQ2LiteralThreefoldTestEdges.nativeEdge_restrict
