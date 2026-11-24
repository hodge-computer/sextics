import Proposal.GeometricLiteralAbelJacobiQPullbackSections

/-!
# Restricting two-forms to the spectrum of a pair ring

If an affine map into a chart is induced by a coordinate homomorphism,
the pullback of every native exterior form to every smaller open is the
ordinary Kähler form obtained from that homomorphism.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiQAffineForms

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricAffineChartSections CycleQ2GeometricAffineDifferentialSheaf
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricExteriorSheaf
  CycleQ2ExteriorSectionNaturality CycleQ2ChartExteriorBinding
  CycleQ2GeometricSchemeDifferentialMap CycleQ2LiteralAbelJacobiQPullback
  CycleQ2LiteralAbelJacobiQPullbackSections

section Chart
variable {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]
  {U : X.Opens} (e : U.toScheme ≅ Spec (CommRingCat.of R))
  (φ : R →+* S) (g : Spec (CommRingCat.of S) ⟶ X)
  (hg : g = Spec.map (CommRingCat.ofHom φ) ≫ e.inv ≫ U.ι)
  (W : X.Opens) (hW : W ≤ U)

include hg in
/-- Regular functions from the chart pull back to the literal images
of their coordinates on the affine source, on every inverse-image open. -/
theorem chart_app (x : R) :
    g.app W (chartSection e (Over.mk (homOfLE hW)) x) =
      algebraMap S (AffineSections S (g ⁻¹ᵁ W)) (φ x) := by
  subst g
  let V : Over U := Over.mk (homOfLE hW)
  let a := algebraMap R (AffineSections R ((chartOpensEquiv e).functor.obj V)) x
  change (Spec.map (CommRingCat.ofHom φ)).app _ ((chartSectionIso e V).hom
    ((chartSectionIso e V).inv a)) = _
  rw [Iso.inv_hom_id_apply]
  exact ConcreteCategory.congr_hom (StructureSheaf.toOpen_comp_comap φ
    ((chartOpensEquiv e).functor.obj V)) x

include hg in
theorem chart_appLE (O : (Spec (CommRingCat.of S)).Opens) (hO : O ≤ g ⁻¹ᵁ W) (x : R) :
    g.appLE W O hO (chartSection e (Over.mk (homOfLE hW)) x) =
      algebraMap S (AffineSections S O) (φ x) := by
  change (Spec (CommRingCat.of S)).presheaf.map (homOfLE hO).op
    (g.app W (chartSection e (Over.mk (homOfLE hW)) x)) = _
  rw [chart_app e φ g hg W hW]
  rfl

end Chart

section Realization
variable (S : Type) [CommRing S] [Algebra ℂ S]

abbrev affineScheme := Spec (CommRingCat.of S)

abbrev nativeRealize (U : (affineScheme S).Opens) (n : ℕ) :=
  exteriorSectionLift (affineScheme S).sheaf (affineCoefficient S)
    (differentialSheaf (affineScheme S).sheaf (affineCoefficient S))
    (universalDifferential (affineScheme S).sheaf (affineCoefficient S)) U
    (algebraMap S (AffineSections S U)) (fun _ => rfl) n

end Realization

section Family
open CycleQ2IncidenceEtaleParameter CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
  CycleQ2LiteralAbelJacobiTimeFamily CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldOverlapAtlas CycleQ2LiteralThreefoldResidueChartMaps

attribute [local instance] CycleQ2LiteralThreefoldHodgeCech.complexOn sourceFixedAlgebra sourceFixedTower

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3)
  {S : Type} [CommRing S] [Algebra ℂ S] (a : affineScheme S ⟶ family V t)
  (φ : FixedOverlap i k →ₐ[ℂ] S)
  (ha : a ≫ toThreefold V t = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (overlapIso i k).hom ≫ (fixedOpen i ⊓ fixedOpen (i.succAbove k)).ι)

include ha
theorem chart_overComplex :
    a ≫ projection V t ≫ (timeOpen V).ι ≫ CycleQ2LiteralIncidenceTimeCurve.toComplex =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ S)) := by
  rw [← toThreefold_overComplex, ← Category.assoc, ha]
  simp only [Category.assoc]
  rw [← Category.assoc (overlapIso i k).hom, overlapIso_hom_ι, Category.assoc,
    chartInclusion_overComplex, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (RingHom.ext φ.commutes)

theorem chart_compatible (U : (family V t).Opens) (z : ℂ) :
    a.app U (coefficientOn (family V t).sheaf (familyCoefficient V t) U z) =
      coefficientOn (affineScheme S).sheaf (affineCoefficient S) (a ⁻¹ᵁ U) z := by
  rw [coefficientOn_app, chart_overComplex V t i k a φ ha]
  exact congrArg (fun c => coefficientOn (affineScheme S).sheaf c (a ⁻¹ᵁ U) z)
    (congrArg CommRingCat.Hom.hom (affineCoefficient_structureMorphism S).symm)

abbrev chartForms := exteriorPull a
  (schemeDifferentialMap a (affineCoefficient S) (familyCoefficient V t)
    (chart_compatible V t i k a φ ha)) 2

variable (W : Threefold.Opens) (hW : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k))

theorem chart_q_app (x : FixedOverlap i k) :
    a.app ((toThreefold V t) ⁻¹ᵁ W) (overlapRingMap V t i k W hW x) =
      algebraMap S (AffineSections S ((a ≫ toThreefold V t) ⁻¹ᵁ W)) (φ x) :=
  chart_app (overlapIso i k).symm φ.toRingHom (a ≫ toThreefold V t) ha W hW x

/-- Pulling the true cylinder two-form onto the affine source takes
the ordinary Kähler exterior pullback along its native coordinate map. -/
theorem chart_q_forms (ω : NativeForms i k) :
    (chartForms V t i k a φ ha).val.app (op ((toThreefold V t) ⁻¹ᵁ W))
        ((qForms V t).val.app (op W) (overlapSection i k W hW ω)) =
      nativeRealize S ((a ≫ toThreefold V t) ⁻¹ᵁ W) 2 (exteriorDifferentialMap φ 2 ω) := by
  rw [qForms_overlapSection]
  let hc := chart_compatible V t i k a φ ha
  let f := overlapRingMap V t i k W hW
  let hf := overlapRingMap_complex V t i k W hW
  refine (exteriorPull_sectionLift a (affineCoefficient S) (familyCoefficient V t) hc
    ((toThreefold V t) ⁻¹ᵁ W) f hf 2 ω).trans ?_
  symm
  apply exteriorSectionLift_differentialMap
  intro x
  exact (chart_q_app V t i k a φ ha W hW x).symm

end Family
end CycleQ2LiteralAbelJacobiQAffineForms
end

#print axioms CycleQ2LiteralAbelJacobiQAffineForms.chart_q_forms
