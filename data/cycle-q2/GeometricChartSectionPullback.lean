import Proposal.GeometricAffineChartSections
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Pullback of actual affine chart coefficients

A commuting square of the original scheme charts determines the pullback
of their polynomial sections on every pair of compatible subopens. The
comparison uses the actual scheme section maps and has no extra choice
of scalar normalization.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ChartSectionPullback

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricAffineChartSections

theorem restriction_square {X Y : Scheme.{0}} (j : X ⟶ Y)
    {U O : Y.Opens} {V W : X.Opens} (hO : O ≤ U) (hV : V ≤ j ⁻¹ᵁ U)
    (hW : W ≤ V) (hWO : W ≤ j ⁻¹ᵁ O) (s : Γ(Y, U)) :
    j.appLE O W hWO (Y.presheaf.map (homOfLE hO).op s) =
      X.presheaf.map (homOfLE hW).op (j.appLE U V hV s) :=
  (ConcreteCategory.congr_hom (j.map_appLE hWO (homOfLE hO).op) s).trans
    (ConcreteCategory.congr_hom (j.appLE_map hV (homOfLE hW).op) s).symm

variable {X Y : Scheme.{0}} {U : Y.Opens} {V : X.Opens}
  {A B : Type} [CommRing A] [CommRing B]
  (j : X ⟶ Y) (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (eV : V.toScheme ≅ Spec (CommRingCat.of B))
  (φ : A →+* B) (hV : V ≤ j ⁻¹ᵁ U)
  (hc : eV.inv ≫ V.ι ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ e.inv ≫ U.ι)

include hc in
theorem chartSection_pullback_top (a : A) :
    j.appLE U V hV (chartSection e (Over.mk (𝟙 U)) a) =
      chartSection eV (Over.mk (𝟙 V)) (φ a) := by
  have h₁ : eV.inv ≫ j.resLE U V hV =
      Spec.map (CommRingCat.ofHom φ) ≫ e.inv := by
    apply (cancel_mono U.ι).mp
    simpa only [Category.assoc, Scheme.Hom.resLE_comp_ι] using hc
  have h₂ : j.resLE U V hV ≫ e.hom =
      eV.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    have h := congrArg (fun k => eV.hom ≫ k ≫ e.hom) h₁
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using h
  have happ := congrArg (fun k => k.appTop) h₂
  simp only [Scheme.Hom.comp_appTop] at happ
  have hcat : CommRingCat.ofHom φ ≫
      CommRingCat.ofHom (chartSection eV (Over.mk (𝟙 V))) =
      CommRingCat.ofHom (chartSection e (Over.mk (𝟙 U))) ≫ j.appLE U V hV := by
    rw [chartSection_top, chartSection_top]
    calc
      _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          ((Spec.map (CommRingCat.ofHom φ)).appTop ≫ eV.hom.appTop) ≫
          V.topIso.hom := by
        rw [Scheme.ΓSpecIso_inv_naturality_assoc]
        simp only [Category.assoc]
      _ = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (e.hom.appTop ≫ (j.resLE U V hV).appTop) ≫ V.topIso.hom := by
        rw [← happ]
      _ = _ := by
        simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
          Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (ConcreteCategory.congr_hom hcat a).symm

include hV hc in
/-- The chart square controls coefficient pullback on arbitrary compatible
subopens, not merely on the full affine chart. -/
theorem chartSection_pullback
    (O : Y.Opens) (hO : O ≤ U) (W : X.Opens) (hW : W ≤ V)
    (hWO : W ≤ j ⁻¹ᵁ O) (a : A) :
    j.appLE O W hWO (chartSection e (Over.mk (homOfLE hO)) a) =
      chartSection eV (Over.mk (homOfLE hW)) (φ a) := by
  have hO' := chartSection_naturality e
    (Over.homMk (homOfLE hO) : Over.mk (homOfLE hO) ⟶ Over.mk (𝟙 U)) a
  have hW' := chartSection_naturality eV
    (Over.homMk (homOfLE hW) : Over.mk (homOfLE hW) ⟶ Over.mk (𝟙 V)) (φ a)
  calc
    _ = j.appLE O W hWO
        (Y.presheaf.map (homOfLE hO).op (chartSection e (Over.mk (𝟙 U)) a)) :=
      congrArg (j.appLE O W hWO) hO'.symm
    _ = X.presheaf.map (homOfLE hW).op
        (j.appLE U V hV (chartSection e (Over.mk (𝟙 U)) a)) :=
      restriction_square j hO hV hW hWO _
    _ = X.presheaf.map (homOfLE hW).op
        (chartSection eV (Over.mk (𝟙 V)) (φ a)) :=
      congrArg (X.presheaf.map (homOfLE hW).op)
        (chartSection_pullback_top j e eV φ hV hc a)
    _ = _ := hW'

#print axioms chartSection_pullback_top
#print axioms chartSection_pullback

end CycleQ2ChartSectionPullback

end
