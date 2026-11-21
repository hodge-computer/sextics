import Proposal.GeometricLiteralThreefoldOverlapAtlas
import Proposal.GeometricSurfaceResidueOverlap
import Proposal.GeometricFiniteCechHOne

/-!
# Algebraic two-forms on the four affine charts of the fixed threefold

The six oriented overlap forms map to the exterior-square differential sheaf of
the smooth proper incidence fibre. The four triangle identities can be checked
in the ordinary Kähler exterior squares of the triple intersection rings.
They then give a class in the derived degree-one group of that sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldHodgeCech

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts CycleQ2LiteralThreefoldOverlapAtlas
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSectionDifferentials
  CycleQ2GeometricExteriorSheaf CycleQ2ChartExteriorBinding CycleQ2ExteriorSectionNaturality
  CycleQ2GeometricSheafLocalIso CycleQ2FiniteCechHOne

attribute [local instance] sourceFixedAlgebra sourceFixedTower

abbrev Threefold := IncidenceFiber 57
abbrev structureMap := incidenceFiberToComplex 57
abbrev coefficients := schemeCoefficient structureMap
abbrev Cotangent := differentialSheaf Threefold.sheaf coefficients
abbrev TwoForms := exteriorSheaf Threefold.sheaf Cotangent.val 2
abbrev HodgeSheaf := CycleQ2GeometricModuleLocalIso.addSheaf TwoForms

abbrev Hodge21 : AddCommGrpCat.{1} :=
  @Sheaf.H' Threefold.Opens _ (Opens.grothendieckTopology (show TopCat from Threefold))
    _ (HasExt.standard _) HodgeSheaf 1 ⊤

private theorem overlap_overComplex (i : Fin 4) (k : Fin 3) :
    (overlapIso i k).hom ≫ (fixedOpen i ⊓ fixedOpen (i.succAbove k)).ι ≫ structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FixedOverlap i k))) := by
  rw [← Category.assoc, overlapIso_hom_ι, Category.assoc, chartInclusion_overComplex, ← Spec.map_comp]
  rfl_cat

abbrev NativeForms (i : Fin 4) (k : Fin 3) :=
  ⋀[FixedOverlap i k]^2 (KaehlerDifferential ℂ (FixedOverlap i k))

/-- The native overlap two-form, as a section on any common subopen. -/
def overlapSection (i : Fin 4) (k : Fin 3) (W : Threefold.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) :
    NativeForms i k →+ HodgeSheaf.obj.obj (op W) :=
  (chartExteriorSheafSection (overlapIso i k).symm structureMap (overlap_overComplex i k)
    2 (Over.mk (homOfLE h))).toAddMonoidHom

theorem overlapSection_restrict (i : Fin 4) (k : Fin 3) {U W : Threefold.Opens}
    (hU : U ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) (hW : W ≤ U)
    (ω : NativeForms i k) :
    res HodgeSheaf hW (overlapSection i k U hU ω) =
      overlapSection i k W (hW.trans hU) ω := by
  let f : Over.mk (homOfLE (hW.trans hU)) ⟶ Over.mk (homOfLE hU) :=
    Over.homMk (homOfLE hW)
  exact chartExteriorSheafSection_restrict (overlapIso i k).symm structureMap
    (overlap_overComplex i k) f 2 ω

abbrev RingOn (W : Threefold.Opens) := SectionRing Threefold.sheaf W
local instance complexOn (W : Threefold.Opens) : Algebra ℂ (RingOn W) :=
  sectionAlgebra Threefold.sheaf coefficients W

abbrev FormsOn (W : Threefold.Opens) := ⋀[RingOn W]^2 (KaehlerDifferential ℂ (RingOn W))

/-- The native algebra map into the ring of functions on a common subopen. -/
def overlapAlgebraMap (i : Fin 4) (k : Fin 3) (W : Threefold.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) : FixedOverlap i k →ₐ[ℂ] RingOn W where
  toRingHom := chartSection (overlapIso i k).symm (Over.mk (homOfLE h))
  commutes' := chartSection_complex (overlapIso i k).symm structureMap
    (overlap_overComplex i k) (Over.mk (homOfLE h))

/-- The actual polynomial chart evaluated on any contained open. -/
def chartAlgebraMap (i : Fin 4) (W : Threefold.Opens) (h : W ≤ fixedOpen i) :
    CycleQ2LiteralAbelJacobiContraction.T i →ₐ[ℂ] RingOn W where
  toRingHom := chartSection (fixedChart i).symm (Over.mk (homOfLE h))
  commutes' := chartSection_complex (fixedChart i).symm structureMap
    (by simpa only [Iso.symm_inv, ← Category.assoc, chartInclusion] using chartInclusion_overComplex i)
    (Over.mk (homOfLE h))

theorem overlapAlgebraMap_source (i : Fin 4) (k : Fin 3) (W : Threefold.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) :
    (overlapAlgebraMap i k W h).comp
      (IsScalarTower.toAlgHom ℂ (CycleQ2LiteralAbelJacobiContraction.T i) (FixedOverlap i k)) =
      chartAlgebraMap i W (h.trans inf_le_left) := by
  ext a
  exact CycleQ2GeometricPrincipalChartSections.chartSection_compatible
    (fixedChart i).symm (overlapIso i k).symm inf_le_left _ (overlapIso_hom_ι i k)
    (Over.mk (homOfLE h)) a

theorem overlapAlgebraMap_target (i : Fin 4) (k : Fin 3) (W : Threefold.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) :
    (overlapAlgebraMap i k W h).comp (fixedTargetMap i k) =
      chartAlgebraMap (i.succAbove k) W (h.trans inf_le_right) := by
  ext a
  exact CycleQ2GeometricPrincipalChartSections.chartSection_compatible
    (fixedChart (i.succAbove k)).symm (overlapIso i k).symm inf_le_right _
    (overlapIso_hom_ι_target i k) (Over.mk (homOfLE h)) a

def restrictNative (i : Fin 4) (k : Fin 3) (W : Threefold.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) : NativeForms i k →+ FormsOn W :=
  (exteriorDifferentialMap (overlapAlgebraMap i k W h) 2).toAddMonoidHom

def realize (W : Threefold.Opens) : FormsOn W →+ HodgeSheaf.obj.obj (op W) :=
  (exteriorSectionLift Threefold.sheaf coefficients Cotangent
    (universalDifferential Threefold.sheaf coefficients) W (RingHom.id _)
    (fun _ => rfl) 2).toAddMonoidHom

theorem realize_restrictNative (i : Fin 4) (k : Fin 3) (W : Threefold.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k)) (ω : NativeForms i k) :
    realize W (restrictNative i k W h ω) = overlapSection i k W h ω := by
  exact exteriorSectionLift_differentialMap Threefold.sheaf coefficients Cotangent
    (universalDifferential Threefold.sheaf coefficients) W
    ((overlapAlgebraMap i k W h).toRingHom) (overlapAlgebraMap i k W h).commutes
    (RingHom.id _) (fun _ => rfl) (overlapAlgebraMap i k W h) (fun _ => rfl) 2 ω

/-- Index of the second chart in the three labels different from the first. -/
def slot (i j : Fin 4) (h : i < j) : Fin 3 :=
  (Fin.exists_succAbove_eq (ne_of_gt h)).choose

@[simp] theorem succAbove_slot (i j : Fin 4) (h : i < j) : i.succAbove (slot i j h) = j :=
  (Fin.exists_succAbove_eq (ne_of_gt h)).choose_spec

private theorem overlap_le {W : Threefold.Opens} {i j : Fin 4} (hij : i < j)
    (h : W ≤ fixedOpen i ⊓ fixedOpen j) : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove (slot i j hij)) := by
  simpa only [succAbove_slot] using h

abbrev NativeEdges := ∀ (i : Fin 4) (k : Fin 3), NativeForms i k

def edge (ω : NativeEdges) (i j : Fin 4) (hij : i < j)
    (W : Threefold.Opens) (h : W ≤ fixedOpen i ⊓ fixedOpen j) :=
  overlapSection i (slot i j hij) W (overlap_le hij h) (ω i (slot i j hij))

def edgeForm (ω : NativeEdges) (i j : Fin 4) (hij : i < j)
    (W : Threefold.Opens) (h : W ≤ fixedOpen i ⊓ fixedOpen j) : FormsOn W :=
  restrictNative i (slot i j hij) W (overlap_le hij h) (ω i (slot i j hij))

theorem edge_restrict (ω : NativeEdges) (i j : Fin 4) (hij : i < j)
    {U W : Threefold.Opens} (hU : U ≤ fixedOpen i ⊓ fixedOpen j) (hW : W ≤ U) :
    res HodgeSheaf hW (edge ω i j hij U hU) = edge ω i j hij W (hW.trans hU) :=
  overlapSection_restrict i _ _ hW _

theorem realize_edge (ω : NativeEdges) (i j : Fin 4) (hij : i < j)
    (W : Threefold.Opens) (h : W ≤ fixedOpen i ⊓ fixedOpen j) :
    realize W (edgeForm ω i j hij W h) = edge ω i j hij W h :=
  realize_restrictNative i _ W _ _

abbrev Triple (i j k : Fin 4) := (fixedOpen i ⊓ fixedOpen j) ⊓ fixedOpen k

/-- This equality lives in ordinary Kähler exterior powers over the triple-open ring. -/
def Face (ω : NativeEdges) (i j k : Fin 4) (hij : i < j) (hjk : j < k) : Prop :=
  edgeForm ω i j hij (Triple i j k) inf_le_left +
      edgeForm ω j k hjk (Triple i j k) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) =
    edgeForm ω i k (hij.trans hjk) (Triple i j k) (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

private theorem face_restrict (ω : NativeEdges) (i j k : Fin 4) (hij : i < j) (hjk : j < k)
    (hf : Face ω i j k hij hjk) (W : Threefold.Opens)
    (hi : W ≤ fixedOpen i) (hj : W ≤ fixedOpen j) (hk : W ≤ fixedOpen k) :
    res HodgeSheaf (le_inf hi hj) (edge ω i j hij _ le_rfl) +
      res HodgeSheaf (le_inf hj hk) (edge ω j k hjk _ le_rfl) =
    res HodgeSheaf (le_inf hi hk) (edge ω i k (hij.trans hjk) _ le_rfl) := by
  have H := congrArg (realize (Triple i j k)) hf
  unfold Face at hf
  change realize _ (_ + _) = realize _ _ at H
  rw [map_add, realize_edge, realize_edge, realize_edge] at H
  have H' := congrArg (res HodgeSheaf (le_inf (le_inf hi hj) hk)) H
  rw [map_add, edge_restrict, edge_restrict, edge_restrict] at H'
  simpa only [edge_restrict] using H'

/-- Four algebraic triangle identities suffice for the six oriented forms to
define an additive cocycle on the actual four-open cover. -/
def hodgeCocycle (ω : NativeEdges)
    (h : ∀ (i j k : Fin 4) (hij : i < j) (hjk : j < k), Face ω i j k hij hjk) :
    CartierCechCoverTransfer.OneCocycle HodgeSheaf fixedOpen :=
  CartierCechFour.fourEdgeCocycle HodgeSheaf fixedOpen
    (edge ω 0 1 (by decide) _ le_rfl) (edge ω 0 2 (by decide) _ le_rfl)
    (edge ω 0 3 (by decide) _ le_rfl) (edge ω 1 2 (by decide) _ le_rfl)
    (edge ω 1 3 (by decide) _ le_rfl) (edge ω 2 3 (by decide) _ le_rfl)
    (face_restrict ω 0 1 2 _ _ (h 0 1 2 (by decide) (by decide)))
    (face_restrict ω 0 1 3 _ _ (h 0 1 3 (by decide) (by decide)))
    (face_restrict ω 0 2 3 _ _ (h 0 2 3 (by decide) (by decide)))
    (face_restrict ω 1 2 3 _ _ (h 1 2 3 (by decide) (by decide)))

/-- Derived degree-one cohomology of the actual algebraic exterior-square sheaf. -/
def hodgeClass (ω : NativeEdges)
    (h : ∀ (i j k : Fin 4) (hij : i < j) (hjk : j < k), Face ω i j k hij hjk) :
    Hodge21 :=
  cechOneClass fixedOpen fixedOpen_cover (hodgeCocycle ω h).val
    (fun i j k W hi hj hk => ((hodgeCocycle ω h).condition i j k W hi hj hk).symm)

end CycleQ2LiteralThreefoldHodgeCech
end

#print axioms CycleQ2LiteralThreefoldHodgeCech.overlapSection_restrict
#print axioms CycleQ2LiteralThreefoldHodgeCech.overlapAlgebraMap_target
#print axioms CycleQ2LiteralThreefoldHodgeCech.realize_restrictNative
#print axioms CycleQ2LiteralThreefoldHodgeCech.hodgeClass
