import Proposal.GeometricSeedProjectiveImageTwist

/-!
# The seed image-line transition in actual projective sections

This component constructs the coordinate-ratio units on common opens of
the original projective surface at `(r, theta) = (57, 1)`. Their restriction
and cocycle laws hold in the actual structure-sheaf section rings.
The original matrix and left generators have transitions of degrees
fourteen and ten, respectively, so their comparison retains degree four.

Source-only proof draft: no Lean elaboration or kernel replay has been run
for this module. Its imported draft dependencies are not newly verified.
The section identities do not yet prove naturality of the local image-dual
isomorphisms, the global internal-Hom comparison, or residue exactness.

The geometric route is due to Ben Diamond and the sources credited in
solution.md. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveImageCocycle

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceOverlap
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
  CycleQ2SurfaceCoordinateSections CycleQ2SeedProjectiveImageChart

abbrev Surface := projectiveSurface (57 : ℂ) (1 : ℂ)
abbrev Patch (i : Fin 3) := coordinatePatch (57 : ℂ) 1 i.succ.castSucc

/-- The original affine-chart map followed by the actual sheaf restriction. -/
def chartSectionMap (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    AffineRing i →+* Γ(Surface, V) :=
  chartSection (coordinateAffineChart 57 1 i.succ) (Over.mk (homOfLE hi))

def polynomialSection (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    WeightedPoly →+* Γ(Surface, V) :=
  (chartSectionMap i V hi).comp (affinePolynomial i)

theorem polynomialSection_restrict (i : Fin 3) (V W : Surface.Opens)
    (hWV : W ≤ V) (hi : V ≤ Patch i) (p : WeightedPoly) :
    Surface.presheaf.map (homOfLE hWV).op (polynomialSection i V hi p) =
      polynomialSection i W (hWV.trans hi) p := by
  change Surface.presheaf.map (homOfLE hWV).op
      (chartSection (coordinateAffineChart 57 1 i.succ)
        (Over.mk (homOfLE hi)) (affinePolynomial i p)) =
    chartSection (coordinateAffineChart 57 1 i.succ)
      (Over.mk (homOfLE (hWV.trans hi))) (affinePolynomial i p)
  rw [coordinate_chartSection_subopen, coordinate_chartSection_subopen]
  change (Surface.presheaf.map (homOfLE hi).op ≫
    Surface.presheaf.map (homOfLE hWV).op) _ = _
  rw [← Functor.map_comp]
  rfl

theorem polynomialSection_change (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    polynomialSection j V hj p =
      polynomialSection j V hj (X i.succ.castSucc) ^ n *
        polynomialSection i V hi p :=
  coordinatePolynomialSection_change 57 1 i.succ j.succ V hi hj n p hp

/-- `Xi / Xj`, with its inverse supplied by the opposite chart section. -/
def transitionUnit (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) : Γ(Surface, V)ˣ where
  val := polynomialSection j V hj (X i.succ.castSucc)
  inv := polynomialSection i V hi (X j.succ.castSucc)
  val_inv := coordinateRatio_inverse 57 1 j.succ i.succ V hj hi
  inv_val := coordinateRatio_inverse 57 1 i.succ j.succ V hi hj

theorem transitionUnit_self (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    transitionUnit i i V hi hi = 1 := by
  apply Units.ext
  exact coordinatePolynomialSection_self 57 1 i.succ V hi

theorem transitionUnit_symm (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) :
    transitionUnit j i V hj hi = (transitionUnit i j V hi hj)⁻¹ := by
  apply Units.ext
  rfl

/-- The transition is natural under actual structure-sheaf restriction. -/
theorem transitionUnit_restrict (i j : Fin 3) (V W : Surface.Opens)
    (hWV : W ≤ V) (hi : V ≤ Patch i) (hj : V ≤ Patch j) :
    Units.map (Surface.presheaf.map (homOfLE hWV).op).hom.toMonoidHom
        (transitionUnit i j V hi hj) =
      transitionUnit i j W (hWV.trans hi) (hWV.trans hj) := by
  apply Units.ext
  exact polynomialSection_restrict j V W hWV hj (X i.succ.castSucc)

/-- The ordered chart changes compose on every actual triple overlap. -/
theorem transitionUnit_cocycle (i j k : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (hk : V ≤ Patch k) :
    transitionUnit j k V hj hk * transitionUnit i j V hi hj =
      transitionUnit i k V hi hk := by
  apply Units.ext
  change polynomialSection k V hk (X j.succ.castSucc) *
      polynomialSection j V hj (X i.succ.castSucc) =
    polynomialSection k V hk (X i.succ.castSucc)
  have hp : (X i.succ.castSucc : WeightedPoly).IsWeightedHomogeneous weight 1 := by
    simpa only [weight_castSucc] using isWeightedHomogeneous_X ℂ weight i.succ.castSucc
  simpa only [pow_one] using
    (polynomialSection_change j k V hj hk 1 (X i.succ.castSucc) hp).symm

theorem transitionUnit_power_cocycle (n : ℕ) (i j k : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (hk : V ≤ Patch k) :
    transitionUnit j k V hj hk ^ n * transitionUnit i j V hi hj ^ n =
      transitionUnit i k V hi hk ^ n := by
  rw [← mul_pow, transitionUnit_cocycle]

/-- The actual restricted matrix, before any choice of image-line frame. -/
def sectionMatrix (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    Matrix (Fin 3) (Fin 3) Γ(Surface, V) :=
  (chartSectionMap i V hi).mapMatrix (chartFactorData i).matrix

theorem sectionMatrix_entry (i a b : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    sectionMatrix i V hi a b =
      polynomialSection i V hi (CycleQ2IncidenceEquations.rawSeedMatrix (57 : ℂ) a b) := by
  exact congrArg (chartSectionMap i V hi) (chartMatrix_polynomial i a b)

/-- These are the original orbit-ideal generators under the same restriction. -/
def sectionLeft (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    Fin 3 → Γ(Surface, V) :=
  fun a => chartSectionMap i V hi ((chartFactorData i).left a)

theorem sectionLeft_entry (i a : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    sectionLeft i V hi a =
      polynomialSection i V hi (CycleQ2SeedFactorHomogeneous.polynomialLeft (57 : ℂ) a) := by
  change chartSectionMap i V hi (coneToChart i (conePolynomial i
      (CycleQ2SeedFactorHomogeneous.polynomialLeft (57 : ℂ) a))) =
    chartSectionMap i V hi (affinePolynomial i
      (CycleQ2SeedFactorHomogeneous.polynomialLeft (57 : ℂ) a))
  exact congrArg (chartSectionMap i V hi) (coneToChart_polynomial i _)

theorem sectionMatrix_change (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) :
    sectionMatrix j V hj =
      (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 14 • sectionMatrix i V hi := by
  ext a b
  change sectionMatrix j V hj a b =
    (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 14 * sectionMatrix i V hi a b
  rw [sectionMatrix_entry, sectionMatrix_entry]
  exact polynomialSection_change i j V hi hj 14 _
    (CycleQ2GeometricIncidenceProj.homogeneous_of_character
      (CycleQ2IncidenceEquations.rawSeedMatrix_homogeneous (57 : ℂ) a b))

theorem sectionLeft_change (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) :
    sectionLeft j V hj =
      (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 10 • sectionLeft i V hi := by
  funext a
  change sectionLeft j V hj a =
    (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 10 * sectionLeft i V hi a
  rw [sectionLeft_entry, sectionLeft_entry]
  exact polynomialSection_change i j V hi hj 10 _
    (CycleQ2GeometricIncidenceProj.homogeneous_of_character
      (CycleQ2SeedFactorHomogeneous.polynomialLeft_homogeneous (57 : ℂ) a))

/-- The degree-four multiplier is itself a unit of the projective section ring. -/
def twistTransition (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) : Γ(Surface, V)ˣ :=
  transitionUnit i j V hi hj ^ 4

theorem twistTransition_restrict (i j : Fin 3) (V W : Surface.Opens)
    (hWV : W ≤ V) (hi : V ≤ Patch i) (hj : V ≤ Patch j) :
    Units.map (Surface.presheaf.map (homOfLE hWV).op).hom.toMonoidHom
        (twistTransition i j V hi hj) =
      twistTransition i j W (hWV.trans hi) (hWV.trans hj) := by
  simp only [twistTransition, map_pow, transitionUnit_restrict]

theorem twistTransition_cocycle (i j k : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (hk : V ≤ Patch k) :
    twistTransition j k V hj hk * twistTransition i j V hi hj =
      twistTransition i k V hi hk :=
  transitionUnit_power_cocycle 4 i j k V hi hj hk

/-- This degree balance is in the actual section ring, with the positive twist. -/
theorem twistTransition_degree_balance (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) :
    (twistTransition i j V hi hj : Γ(Surface, V)) *
        (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 10 =
      (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 14 := by
  change (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 4 *
      (transitionUnit i j V hi hj : Γ(Surface, V)) ^ 10 = _
  rw [← pow_add]

#print axioms transitionUnit_restrict
#print axioms transitionUnit_cocycle
#print axioms sectionMatrix_change
#print axioms sectionLeft_change
#print axioms twistTransition_cocycle
#print axioms twistTransition_degree_balance

end CycleQ2SeedProjectiveImageCocycle
end
