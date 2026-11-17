import Proposal.GeometricLiteralOrbitCoordinateClass
import Proposal.GeometricLiteralOrbitCoordinateClassRepresentative
import Proposal.GeometricLiteralOrbitCoordinate
import Proposal.GeometricLiteralOrbitBoundary
import Proposal.GeometricAutomorphismCechTwo

/-!
# The genuine normal action on the coordinate degree-two class

The projective automorphism fixes the three coordinate opens. Its map on
the normal term of the cotangent extension multiplies the scheme pullback
by the square of the cube root of unity. The finite Čech realization
identifies this operation with the induced map on derived cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralOrbitCoordinateClass

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
  CycleQ2FiniteCechOrbitPullback CycleQ2FiniteCechDescent CycleQ2CoordinateMVBinding
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ThreeOpenH2Naturality
  CycleQ2CanonicalCoordinateH2 CycleQ2ProjectiveCoordinateH2 CycleQ2GeometricHomogeneousWeight
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSurfaceCoefficients
  CycleQ2GeometricProjectiveHOne CycleQ2LiteralOrbitAction CycleQ2LiteralOrbitBoundary
  CycleQ2AutomorphismCohomology CycleQ2AutomorphismCechTwo
  CycleQ2LiteralOrbitCoordinate CycleQ2LiteralOrbitCoordinateClassRepresentative

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

variable (z : ℂ) (hz : z ^ 3 = 1)

private abbrev e := closedProjectiveAction z hz
private abbrev g := (e z hz).hom
private abbrev topAction := Scheme.forgetToTop.mapIso (e z hz)
private abbrev F := structureAdditiveSheaf Surface
private abbrev U := coordinateFamily 57

/-- A coordinate section is mapped to the top-open class by both Mayer–Vietoris boundaries. -/
abbrev coordinateClass := coordinateStructureClass 57

private theorem stable (i : Fin 4) : U i ≤ pre (topAction z hz).hom (U i) := by
  fin_cases i
  · exact (coordinateOpen_preimage z hz 0).ge
  · exact (coordinateOpen_preimage z hz 1).ge
  · exact (coordinateOpen_preimage z hz 2).ge
  · have he : U 3 = ⊥ := Proj.basicOpen_zero _
    exact he.le.trans bot_le

/-- The map on derived H² induced by the actual sheaf map on the normal term. -/
abbrev normalPullH2 := coordinateActionH2 57 (topAction z hz) (additiveNormal z hz)

private theorem scalarAdjoint_section {S : Scheme.{0}} (f : S ⟶ S) (cs : ℂ →+* Γ(S, ⊤))
    (a : ℂ) (V : S.Opens) (h : V ≤ f ⁻¹ᵁ V) (x : Γ(S, V)) :
    S.presheaf.map (homOfLE h).op ((scalarAdjoint f cs a).val.app (op V) x) =
      (show Γ(S, V) from coefficientOn S.sheaf cs V a) * f.appLE V V h x := by
  let r := S.presheaf.map (homOfLE h).op
  have hc : r (coefficientOn S.sheaf cs (f ⁻¹ᵁ V) a) = coefficientOn S.sheaf cs V a :=
    CycleQ2GeometricTwistedDifferential.coefficientOn_restrict S.sheaf cs h a
  have hm := map_mul r.hom (f.app V x) (show Γ(S, f ⁻¹ᵁ V) from coefficientOn S.sheaf cs _ a)
  rw [scalarAdjoint_apply]
  change r _ = _ * r (f.app V x)
  exact hm.trans ((congrArg (fun y : Γ(S, V) => r (f.app V x) * y) hc).trans (mul_comm _ _))

theorem normalPull_triple (q : HomogeneousCoordinateTop 57) :
    pullTo (F := F) (G := F) (topAction z hz).hom (additiveNormal z hz) (triple_stable (topAction z hz).hom U (stable z hz) 0 1 2)
      (tripleSections 57 1 q) = tripleSections 57 1 (CycleQ2LiteralOrbitCoordinate.normalPull z hz q) := by
  let T := TripleOpen
  let h := (sectionAt_preimage z hz T (coordinateIntersection_univ 57 1).symm).ge
  change Surface.presheaf.map (homOfLE h).op
    ((scalarAdjoint (g z hz) (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1)
      (z^2)).val.app (op T) (tripleSections 57 1 q)) = _
  have hs := scalarAdjoint_section (g z hz) (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1)
    (z^2) T h (tripleSections 57 1 q)
  exact hs.trans (normalPull_section z hz q).symm

private def normalPullCoordinateProof (q : HomogeneousCoordinateTop 57) :=
  pullH_coordinateSection_of_eq 57 (topAction z hz)
    (additiveNormal z hz) (stable z hz) q (CycleQ2LiteralOrbitCoordinate.normalPull z hz q)
    (normalPull_triple z hz q)

theorem normalPull_coordinate (q : HomogeneousCoordinateTop 57) : type_of% (normalPullCoordinateProof z hz q) :=
  normalPullCoordinateProof z hz q

private theorem sum_normalTriples (q : HomogeneousCoordinateTop 57) :
    q + CycleQ2LiteralOrbitCoordinate.normalPull z hz q +
      CycleQ2LiteralOrbitCoordinate.normalPull z hz (CycleQ2LiteralOrbitCoordinate.normalPull z hz q) =
    weightedTriple z hz q := by
  have hz₂ : (z^2)^3 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]
  rw [weightedTriple_eq_normalPull z hz hz₂ q, normalPull_comp]
  simp only [pow_two]

private def normalOrbitCoordinateProof (q : HomogeneousCoordinateTop 57) :=
  let t := CycleQ2LiteralOrbitCoordinate.normalPull z hz q
  pullH_coordinateOrbit_of_eq 57 (topAction z hz) (additiveNormal z hz) (stable z hz)
    q t (CycleQ2LiteralOrbitCoordinate.normalPull z hz t) (weightedTriple z hz q)
    (normalPull_triple z hz q) (normalPull_triple z hz t) (sum_normalTriples z hz q)

theorem normalPull_coordinate_orbit (q : HomogeneousCoordinateTop 57) : type_of% (normalOrbitCoordinateProof z hz q) :=
  normalOrbitCoordinateProof z hz q

end CycleQ2LiteralOrbitCoordinateClass
end

#print axioms CycleQ2LiteralOrbitCoordinateClass.normalPull_coordinate_orbit
