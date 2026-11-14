import Proposal.GeometricDifferentialSheaf

/-!
# The actual complex coefficients in projective affine charts

The coefficient map defined by the projective structure morphism agrees,
on every positive-degree homogeneous basic open, with the canonical
degree-zero coefficient map into its homogeneous localization. This binds
the complex structure used for differentials to the literal affine rings.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricProjectiveCoefficients

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2NormalConnecting CycleQ2GeometricProjectiveCurve
  CycleQ2GeometricDifferentialSheaf

private theorem restriction_from_top (X : Scheme.{0}) (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

def basicOpenCoefficient (r θ : ℂ) (f : CurveRing r θ) :
    ℂ →+* HomogeneousLocalization.Away (curveGrade r θ) f :=
  (HomogeneousLocalization.fromZeroRingHom (curveGrade r θ) (Submonoid.powers f)).comp
    (projectiveCoefficient r θ)

theorem awayι_projectiveToComplex (r θ : ℂ) (f : CurveRing r θ) {n : ℕ}
    (hf : f ∈ curveGrade r θ n) (hn : 0 < n) :
    Proj.awayι (curveGrade r θ) f hf hn ≫ projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (basicOpenCoefficient r θ f)) := by
  rw [projectiveToComplex, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  rfl

/-- The actual global scalars restrict to the canonical homogeneous
localization coefficients, under the actual chart-section isomorphism. -/
theorem globalCoefficient_restriction (r θ : ℂ) (f : CurveRing r θ) {n : ℕ}
    (hf : f ∈ curveGrade r θ n) (hn : 0 < n) :
    CommRingCat.ofHom (projectiveGlobalCoefficient r θ) ≫
        (projectiveCurve r θ).presheaf.map
          (homOfLE (show Proj.basicOpen (curveGrade r θ) f ≤ ⊤ from le_top)).op =
      CommRingCat.ofHom (basicOpenCoefficient r θ f) ≫
        (Proj.basicOpenIsoAway (curveGrade r θ) f hf hn).hom := by
  have hg := congrArg
    (fun k => (Proj.basicOpenIsoSpec (curveGrade r θ) f hf hn).hom ≫ k)
    (awayι_projectiveToComplex r θ f hf hn)
  have hg' : (Proj.basicOpen (curveGrade r θ) f).ι ≫ projectiveToComplex r θ =
      (Proj.basicOpenIsoSpec (curveGrade r θ) f hf hn).hom ≫
        Spec.map (CommRingCat.ofHom (basicOpenCoefficient r θ f)) := by
    simpa only [Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc] using hg
  have hs := congrArg
    (fun k : (Proj.basicOpen (curveGrade r θ) f).toScheme ⟶ Spec (CommRingCat.of ℂ) =>
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ k.appTop ≫
        (Proj.basicOpen (curveGrade r θ) f).topIso.hom) hg'
  simp only [Scheme.Hom.comp_appTop, Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_app_top, Category.assoc, Scheme.ΓSpecIso_naturality_assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, restriction_from_top] at hs
  simpa only [projectiveGlobalCoefficient, projectiveCurve, CommRingCat.ofHom_hom, Category.assoc,
    Proj.basicOpenIsoAway_hom] using hs

theorem coefficientOn_basicOpen (r θ : ℂ) (f : CurveRing r θ) {n : ℕ}
    (hf : f ∈ curveGrade r θ n) (hn : 0 < n) (c : ℂ) :
    (Proj.basicOpenIsoAway (curveGrade r θ) f hf hn).inv
      (coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (Proj.basicOpen (curveGrade r θ) f) c) =
      HomogeneousLocalization.fromZeroRingHom (curveGrade r θ) (Submonoid.powers f)
        (algebraMap ℂ (curveGrade r θ 0) c) := by
  have h := congrArg (fun k : CommRingCat.of ℂ ⟶
      Γ(projectiveCurve r θ, Proj.basicOpen (curveGrade r θ) f) => k c)
    (globalCoefficient_restriction r θ f hf hn)
  have h' : coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
      (Proj.basicOpen (curveGrade r θ) f) c =
        (Proj.basicOpenIsoAway (curveGrade r θ) f hf hn).hom
          (basicOpenCoefficient r θ f c) := h
  rw [h', Iso.hom_inv_id_apply]
  rfl

theorem coefficientOn_coordinatePatch (r θ : ℂ) (j : Fin 4) (c : ℂ) :
    (Proj.basicOpenIsoAway (curveGrade r θ) (curveMap r θ (MvPolynomial.X j))
      (coordinate_mem_grade r θ j) (by decide)).inv
      (coefficientOn (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
        (coordinateProjectivePatch r θ j) c) =
      HomogeneousLocalization.fromZeroRingHom (curveGrade r θ)
        (Submonoid.powers (curveMap r θ (MvPolynomial.X j)))
        (algebraMap ℂ (curveGrade r θ 0) c) :=
  coefficientOn_basicOpen r θ _ (coordinate_mem_grade r θ j) (by decide) c

end CycleQ2GeometricProjectiveCoefficients

end
