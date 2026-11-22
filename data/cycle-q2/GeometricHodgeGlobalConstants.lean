import Proposal.GeometricHodgeTwistConstantSections
import Proposal.GeometricAffineChartSections
import Proposal.GeometricHodgeThreefoldLiteral
import Proposal.GeometricLiteralThreefoldResidueGluing

/-!
# Canonical constants on the original monic weighted threefold

The degree-zero Laurent coefficient gives the actual constant coming from
the structure morphism, rather than an unspecified additive coordinate.
Thus the canonical scalar map onto global functions is surjective.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeGlobalConstants

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeTwistAnchor (torus torus_le commonCoefficient)
open CycleQ2HodgeTwistMonomials (evaluate monomial)
open CycleQ2HodgeTwistTorusChart (structureChart structureLaurentSections)
open CycleQ2HodgeTwistGlobal (globalMap globalMap_injective)
open CycleQ2HodgeTwistConstantSections (constant coefficient constant_coefficient structureSections)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricDifferentialSheaf (coefficientOn)
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)

private theorem restrict_top (X : Scheme.{0}) (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

private theorem chartScalar_map (φ : CoeffRing →+* ℂ) (i : Fin 4) :
    CommRingCat.ofHom (schemeCoefficient (toBase φ)) ≫ (threefold φ).presheaf.map
        (homOfLE (show coordinateOpen φ i ≤ ⊤ from le_top)).op =
      CommRingCat.ofHom (chartCoefficient φ i) ≫ Proj.awayToSection (grade φ) (coord φ i.castSucc) := by
  let U := coordinateOpen φ i
  let e := coordinateChart φ i
  have hb : e.inv ≫ U.ι ≫ toBase φ = Spec.map (CommRingCat.ofHom (chartCoefficient φ i)) :=
    coordinateChart_overBase φ i
  have h : U.ι ≫ toBase φ = e.hom ≫ Spec.map (CommRingCat.ofHom (chartCoefficient φ i)) :=
    (Iso.hom_inv_id_assoc e _).symm.trans (congrArg (fun k => e.hom ≫ k) hb)
  have he := congrArg (fun k : U.toScheme ⟶ Spec (CommRingCat.of ℂ) =>
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ k.appTop ≫ U.topIso.hom) h
  simp only [Scheme.Hom.comp_appTop, U, e, coordinateChart, Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_app_top, Category.assoc, Scheme.ΓSpecIso_naturality_assoc,
    Iso.inv_hom_id_assoc, restrict_top] at he
  simpa only [schemeCoefficient, CommRingCat.ofHom_hom, Category.assoc,
    Proj.basicOpenIsoAway_hom, Iso.inv_hom_id, Category.comp_id, threefold, coordinateOpen] using he

theorem chartScalar (φ : CoeffRing →+* ℂ) (i : Fin 4) (c : ℂ) :
    coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) (coordinateOpen φ i) c =
      (Proj.awayToSection (grade φ) (coord φ i.castSucc)) (chartCoefficient φ i c) :=
  congrArg (fun k : CommRingCat.of ℂ ⟶ Γ(threefold φ, coordinateOpen φ i) => k.hom c)
    (chartScalar_map φ i)

theorem torusScalar (φ : CoeffRing →+* ℂ) (c : ℂ) :
    coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) (torus φ) c =
      commonCoefficient φ c := by
  have e := congrArg (res (threefold φ).sheaf (torus_le φ 0)) (chartScalar φ 0 c)
  change res _ _ (res _ _ (schemeCoefficient (toBase φ) c)) = commonCoefficient φ c at e
  rw [res_comp] at e
  exact e

variable (φ : CoeffRing →+* ℂ) (h : IsUnit (φ vertexCoefficient))

private theorem torus_evaluate (s : Γ(threefold φ, torus φ)) :
    evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
      ((structureChart φ h).coordinates s) = s := by
  let W := torus φ
  let e := CycleQ2HodgeThreefoldTwist.chartFrame φ 0 0 W (torus_le φ 0)
  let p := e.symm s
  have hn := CycleQ2HodgeTwistAnchor.face_frame_evaluation φ 0 h Finset.univ (Finset.mem_univ _) 0 p
  change e (CycleQ2GeometricSheafLocalIso.res
    (CycleQ2GeometricModuleLocalIso.addSheaf (CycleQ2HodgeThreefoldTwist.twist φ 0))
      (show W ≤ W from le_rfl) p) = _ at hn
  rw [CycleQ2GeometricSheafLocalIso.res_self] at hn
  exact hn.symm.trans (e.apply_symm_apply s)

private theorem evaluate_constant (c : ℂ) :
    evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0 (constant c).val =
      commonCoefficient φ c := by
  classical
  simp [evaluate, constant, Fin.sum_univ_three, monomial, CycleQ2HodgeTwistMonomials.units]

include h in
theorem restrict_torus_injective : Function.Injective
    (res (threefold φ).sheaf (show torus φ ≤ ⊤ from le_top)) := by
  intro a b hab
  apply globalMap_injective (structureLaurentSections φ h) (coordinateOpens_cover φ h)
  apply Subtype.ext
  change (structureChart φ h).coordinates (res (threefold φ).sheaf le_top a) =
    (structureChart φ h).coordinates (res (threefold φ).sheaf le_top b)
  exact congrArg (structureChart φ h).coordinates hab

/-- The previously computed Laurent coefficient is the canonical scalar itself. -/
theorem section_eq_scalar (s : Γ(threefold φ, ⊤)) :
    s = schemeCoefficient (toBase φ) (structureSections φ h s) := by
  apply restrict_torus_injective φ h
  let p := globalMap (structureLaurentSections φ h) s
  have hp : (constant (structureSections φ h s)).val = p.val :=
    congrArg Subtype.val (constant_coefficient p)
  calc
    res (threefold φ).sheaf le_top s =
        evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0 p.val :=
      (torus_evaluate φ h _).symm
    _ = commonCoefficient φ (structureSections φ h s) := by rw [← hp, evaluate_constant]
    _ = _ := (torusScalar φ _).symm

include h in
/-- Every actual global function comes from the original structure morphism. -/
theorem scalar_surjective : Function.Surjective (schemeCoefficient (toBase φ)) :=
  fun s => ⟨structureSections φ h s, (section_eq_scalar φ h s).symm⟩

/-- The isomorphism is the canonical ring map, with its multiplication intact. -/
def scalarEquiv : ℂ ≃+* Γ(threefold φ, ⊤) := by
  letI : Nontrivial Γ(threefold φ, ⊤) := (structureSections φ h).symm.injective.nontrivial
  exact RingEquiv.ofBijective (schemeCoefficient (toBase φ))
    ⟨RingHom.injective _, scalar_surjective φ h⟩

open CycleQ2GeometricHodgeThreefoldIncidence
open CycleQ2LiteralAmbientSmooth (incidenceFiberToComplex)

/-- Transport uses the actual isomorphism over the original complex point. -/
theorem original_scalar_surjective : Function.Surjective (schemeCoefficient (incidenceFiberToComplex 57)) := by
  intro s
  obtain ⟨c,hc⟩ := scalar_surjective literalEval literal_vertex_unit (literalIso.hom.appTop s)
  refine ⟨c, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso literalIso.hom.appTop).injective
  have hf := CycleQ2GeometricAffineChartSections.schemeCoefficient_comp
    literalIso.hom (incidenceFiberToComplex 57) c
  rw [literalIso_overComplex] at hf
  exact hf.symm.trans hc

end CycleQ2HodgeGlobalConstants
end

#print axioms CycleQ2HodgeGlobalConstants.chartScalar
#print axioms CycleQ2HodgeGlobalConstants.section_eq_scalar
#print axioms CycleQ2HodgeGlobalConstants.scalar_surjective
#print axioms CycleQ2HodgeGlobalConstants.scalarEquiv
#print axioms CycleQ2HodgeGlobalConstants.original_scalar_surjective

/-!
## The top trace on the original fixed threefold and its canonical sheaf

The Laurent comparison is transported by the actual section maps of
`literalIso`. The canonical comparison then uses the glued native residue
frame. Both derived traces use the same three Mayer--Vietoris boundaries
on the original four weight-one opens.
-/

noncomputable section
namespace CycleQ2LiteralThreefoldTopTrace

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf overIsoOfPatchIso)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen)
open CycleQ2GeometricHodgeThreefoldIncidence
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)
open CycleQ2LiteralThreefoldHodgeCech (Threefold)
open CycleQ2HodgeTwistCech (Vertex NormalForm sections)
open CycleQ2HodgeTwistCoordinates (Chart HasLaurentSections read nativeTopSectionTrace)
open CycleQ2HodgeTwistTopDerived
open CycleQ2GeometricSheafLocalIso (res res_self)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2GeometricCanonicalGluing (LocalFrame)

local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _

abbrev Structure := structureAdditiveSheaf Threefold
abbrev Face (S : Finset Vertex) : Threefold.Opens := S.inf fixedOpen
abbrev Torus : Threefold.Opens := Face Finset.univ

private theorem torus_le_face (S : Finset Vertex) : Torus ≤ Face S :=
  Finset.le_inf (fun i _ => Finset.inf_le (Finset.mem_univ i))

/-- The original scheme isomorphism identifies every standard intersection. -/
theorem literalIso_preimage_face (S : Finset Vertex) :
    literalIso.hom ⁻¹ᵁ Face S = S.inf (coordinateOpen literalEval) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Face]
  | insert i S hi ih =>
    simp only [Face, Finset.inf_insert, Scheme.Hom.preimage_inf,
      literalIso_preimage] at ih ⊢
    exact congrArg (coordinateOpen literalEval i ⊓ ·) ih

private theorem iso_appLE_bijective {X Y : Scheme.{0}} (e : X ≅ Y)
    (U : Y.Opens) (V : X.Opens) (h : e.hom ⁻¹ᵁ U = V) :
    Function.Bijective (e.hom.appLE U V h.ge) := by
  subst V
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (e.hom.app U)

/-- This equivalence is the original scheme's section pullback. -/
def faceSectionEquiv (S : Finset Vertex) :
    Γ(Threefold, Face S) ≃+* Γ(threefold literalEval, S.inf (coordinateOpen literalEval)) :=
  RingEquiv.ofBijective
    (literalIso.hom.appLE (Face S) (S.inf (coordinateOpen literalEval))
      (literalIso_preimage_face S).ge).hom
    (iso_appLE_bijective literalIso (Face S) _ (literalIso_preimage_face S))

theorem faceSectionEquiv_restrict (S : Finset Vertex) (s : Γ(Threefold, Face S)) :
    faceSectionEquiv Finset.univ (res Structure (torus_le_face S) s) =
      res (structureAdditiveSheaf (threefold literalEval))
        (CycleQ2HodgeTwistAnchor.torus_le_face literalEval S) (faceSectionEquiv S s) :=
  CycleQ2ChartSectionPullback.restriction_square literalIso.hom (torus_le_face S)
    (literalIso_preimage_face S).ge
    (CycleQ2HodgeTwistAnchor.torus_le_face literalEval S)
    (literalIso_preimage_face Finset.univ).ge s

/-- Laurent coordinates of the actual fixed-fiber structure sections. -/
def structureChart : Chart Structure fixedOpen ℂ where
  common := Torus
  le i := Finset.inf_le (Finset.mem_univ i)
  coordinates :=
    (CycleQ2HodgeTwistTorusChart.structureChart literalEval literal_vertex_unit).coordinates.comp
      (faceSectionEquiv Finset.univ).toAddEquiv.toAddMonoidHom

theorem read_structure_face (S : Finset Vertex) (s : Γ(Threefold, Face S)) :
    read structureChart (torus_le_face S) s =
      read (CycleQ2HodgeTwistTorusChart.structureChart literalEval literal_vertex_unit)
        (CycleQ2HodgeTwistAnchor.torus_le_face literalEval S) (faceSectionEquiv S s) := by
  change (CycleQ2HodgeTwistTorusChart.structureChart literalEval literal_vertex_unit).coordinates
    (faceSectionEquiv Finset.univ (res Structure (torus_le_face S) s)) = _
  rw [faceSectionEquiv_restrict]
  rfl

theorem structureLaurentSections : HasLaurentSections structureChart 0 where
  injective S hS := by
    intro x y hxy
    apply (faceSectionEquiv S).injective
    apply (CycleQ2HodgeTwistTorusChart.structureLaurentSections
      literalEval literal_vertex_unit).injective S hS
    exact (read_structure_face S x).symm.trans (hxy.trans (read_structure_face S y))
  range_eq S hS := by
    let H := CycleQ2HodgeTwistTorusChart.structureLaurentSections literalEval literal_vertex_unit
    ext p
    rw [← H.range_eq S hS]
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨faceSectionEquiv S s, (read_structure_face S s).symm⟩
    · rintro ⟨s,rfl⟩
      refine ⟨(faceSectionEquiv S).symm s, ?_⟩
      rw [read_structure_face, RingEquiv.apply_symm_apply]

theorem face_affine (S : Finset Vertex) (hS : S.Nonempty) : IsAffineOpen (Face S) := by
  obtain ⟨i,hi⟩ := hS
  have h : IsAffineOpen (S.inf (coordinateOpen literalEval)) := by
    rw [← CycleQ2HodgeTwistFaces.face_inf literalEval i S hi]
    exact CycleQ2HodgeTwistFaces.face_affine literalEval i _
  have e : literalIso.inv ⁻¹ᵁ (S.inf (coordinateOpen literalEval)) = Face S := by
    rw [← literalIso_preimage_face, ← Scheme.Hom.comp_preimage, literalIso.inv_hom_id]
    rfl
  exact e ▸ h.preimage literalIso.inv

theorem structure_face_acyclic : FaceAcyclic Structure fixedOpen := by
  intro S hS n
  exact CycleQ2GeometricAffineHThree.frame_subsingleton (face_affine S hS).isoSpec
    Structure (Iso.refl _) (n+1)
    (CycleQ2GeometricAffineHThree.affine_H_positive_subsingleton n Γ(Threefold,Face S))

def structureSectionTrace : Γ(Threefold,Torus) →+ ℂ :=
  nativeTopSectionTrace structureLaurentSections

theorem structureSectionTrace_pullback (s : Γ(Threefold,Torus)) :
    structureSectionTrace s = CycleQ2HodgeTwistTorusChart.structureTopSectionTrace
      literalEval literal_vertex_unit (faceSectionEquiv Finset.univ s) := by
  change ((CycleQ2HodgeTwistTorusChart.structureChart literalEval literal_vertex_unit).coordinates
      (faceSectionEquiv Finset.univ (res Structure le_rfl s))) 2
        CycleQ2HodgeTwistCech.negativeExponent =
    ((CycleQ2HodgeTwistTorusChart.structureChart literalEval literal_vertex_unit).coordinates
      (res (structureAdditiveSheaf (threefold literalEval)) le_rfl
        (faceSectionEquiv Finset.univ s))) 2 CycleQ2HodgeTwistCech.negativeExponent
  rw [res_self, res_self]

def structureTrace : Structure.H' 3 ⊤ ≃+ ℂ :=
  derivedTopTraceEquiv Structure fixedOpen structureLaurentSections fixedOpen_cover
    structure_face_acyclic

theorem structureTrace_connecting (s : Γ(Threefold,Torus)) :
    structureTrace (nativeTopConnecting Structure fixedOpen fixedOpen_cover s) =
      structureSectionTrace s :=
  derivedTopTrace_connecting Structure fixedOpen structureLaurentSections fixedOpen_cover
    structure_face_acyclic s

section Framed

variable (M : SheafOfModules.{0}
    (CycleQ2GeometricProjectiveCurve.TwistedModule.ringSheaf Threefold.sheaf))
  (e : LocalFrame Threefold.sheaf M ⊤)

/-- A global native frame transports the same actual Laurent coordinates. -/
def framedChart : Chart (addSheaf M) fixedOpen ℂ where
  common := Torus
  le i := Finset.inf_le (Finset.mem_univ i)
  coordinates := structureChart.coordinates.comp
    (e.app Torus le_top).toAddEquiv.toAddMonoidHom

theorem read_framed_face (S : Finset Vertex) (s : M.val.obj (op (Face S))) :
    read (framedChart M e) (torus_le_face S) s =
      read structureChart (torus_le_face S) (e.app (Face S) le_top s) := by
  change structureChart.coordinates
    (e.app Torus le_top (res (addSheaf M) (torus_le_face S) s)) = _
  rw [← e.naturality (torus_le_face S) le_top]
  rfl

theorem framedLaurentSections : HasLaurentSections (framedChart M e) 0 where
  injective S hS := by
    intro x y hxy
    apply (e.app (Face S) le_top).injective
    apply structureLaurentSections.injective S hS
    exact (read_framed_face M e S x).symm.trans
      (hxy.trans (read_framed_face M e S y))
  range_eq S hS := by
    ext p
    rw [← structureLaurentSections.range_eq S hS]
    constructor
    · rintro ⟨s,rfl⟩
      exact ⟨e.app (Face S) le_top s, (read_framed_face M e S s).symm⟩
    · rintro ⟨s,rfl⟩
      refine ⟨(e.app (Face S) le_top).symm s, ?_⟩
      rw [read_framed_face, LinearEquiv.apply_symm_apply]

theorem framed_face_acyclic : FaceAcyclic (addSheaf M) fixedOpen := by
  intro S hS n
  let fr : CycleQ2GeometricSheafLocalIso.PatchIso (addSheaf M) Structure (Face S) :=
    { app O hO := (e.app O le_top).toAddEquiv
      naturality hPO hO s := e.naturality hPO le_top s }
  exact CycleQ2GeometricAffineHThree.frame_subsingleton (face_affine S hS).isoSpec
    (addSheaf M) (overIsoOfPatchIso fr) (n+1)
    (CycleQ2GeometricAffineHThree.affine_H_positive_subsingleton n Γ(Threefold,Face S))

def framedSectionTrace : M.val.obj (op Torus) →+ ℂ :=
  nativeTopSectionTrace (framedLaurentSections M e)

theorem framedSectionTrace_frame (s : M.val.obj (op Torus)) :
    framedSectionTrace M e s = structureSectionTrace (e.app Torus le_top s) := by
  change (structureChart.coordinates
    (e.app Torus le_top (res (addSheaf M) le_rfl s))) 2
      CycleQ2HodgeTwistCech.negativeExponent =
    (structureChart.coordinates (res Structure le_rfl (e.app Torus le_top s))) 2
      CycleQ2HodgeTwistCech.negativeExponent
  rw [res_self, res_self]

def framedTrace : (addSheaf M).H' 3 ⊤ ≃+ ℂ :=
  derivedTopTraceEquiv (addSheaf M) fixedOpen (framedLaurentSections M e)
    fixedOpen_cover (framed_face_acyclic M e)

theorem framedTrace_connecting (s : M.val.obj (op Torus)) :
    framedTrace M e (nativeTopConnecting (addSheaf M) fixedOpen fixedOpen_cover s) =
      framedSectionTrace M e s :=
  derivedTopTrace_connecting (addSheaf M) fixedOpen (framedLaurentSections M e)
    fixedOpen_cover (framed_face_acyclic M e) s

/-- The generator is pulled back through the original scheme isomorphism
and multiplied by the specified actual global frame. -/
def framedGenerator (a : ℂ) : M.val.obj (op Torus) :=
  (e.app Torus le_top).symm ((faceSectionEquiv Finset.univ).symm
    (CycleQ2HodgeTwistTorusChart.structureTopGenerator literalEval literal_vertex_unit a))

theorem framedSectionTrace_generator (a : ℂ) :
    framedSectionTrace M e (framedGenerator M e a) = a := by
  rw [framedSectionTrace_frame, framedGenerator, LinearEquiv.apply_symm_apply,
    structureSectionTrace_pullback, RingEquiv.apply_symm_apply,
    CycleQ2HodgeTwistTorusChart.structureTopSectionTrace_generator]

def framedClass (a : ℂ) : (addSheaf M).H' 3 ⊤ :=
  nativeTopConnecting (addSheaf M) fixedOpen fixedOpen_cover (framedGenerator M e a)

theorem framedTrace_class (a : ℂ) : framedTrace M e (framedClass M e a) = a := by
  rw [framedClass, framedTrace_connecting, framedSectionTrace_generator]

theorem framedClass_ne_zero {a : ℂ} (ha : a ≠ 0) : framedClass M e a ≠ 0 := by
  intro hz
  apply ha
  have he := congrArg (framedTrace M e) hz
  rwa [framedTrace_class, map_zero] at he

end Framed

open CycleQ2LiteralThreefoldCanonicalFrame

/-- Trace on the actual canonical three-form sheaf of `IncidenceFiber 57`. -/
def canonicalTrace : CanonicalAdditiveSheaf.H' 3 ⊤ ≃+ ℂ :=
  framedTrace CanonicalForms globalFrame

def canonicalSectionTrace : CanonicalForms.val.obj (op Torus) →+ ℂ :=
  framedSectionTrace CanonicalForms globalFrame

theorem canonicalSectionTrace_coefficient (s : CanonicalForms.val.obj (op Torus)) :
    canonicalSectionTrace s = CycleQ2HodgeTwistTorusChart.structureTopSectionTrace
      literalEval literal_vertex_unit
      (faceSectionEquiv Finset.univ (canonicalIso.hom.val.app (op Torus) s)) := by
  rw [canonicalIso_hom]
  exact (framedSectionTrace_frame CanonicalForms globalFrame s).trans
    (structureSectionTrace_pullback _)

theorem canonicalTrace_connecting (s : CanonicalForms.val.obj (op Torus)) :
    canonicalTrace (nativeTopConnecting CanonicalAdditiveSheaf fixedOpen fixedOpen_cover s) =
      canonicalSectionTrace s :=
  framedTrace_connecting CanonicalForms globalFrame s

def canonicalClass (a : ℂ) : CanonicalAdditiveSheaf.H' 3 ⊤ :=
  framedClass CanonicalForms globalFrame a

theorem canonicalTrace_class (a : ℂ) : canonicalTrace (canonicalClass a) = a :=
  framedTrace_class CanonicalForms globalFrame a

theorem canonicalClass_one_ne_zero : canonicalClass 1 ≠ 0 :=
  framedClass_ne_zero CanonicalForms globalFrame one_ne_zero

end CycleQ2LiteralThreefoldTopTrace
end

#print axioms CycleQ2LiteralThreefoldTopTrace.structureLaurentSections
#print axioms CycleQ2LiteralThreefoldTopTrace.canonicalSectionTrace_coefficient
#print axioms CycleQ2LiteralThreefoldTopTrace.canonicalTrace_connecting
#print axioms CycleQ2LiteralThreefoldTopTrace.canonicalClass_one_ne_zero
