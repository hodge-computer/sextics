import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Descent of module exactness along an open cover

A covering family of open immersions jointly detects equality of scheme
module morphisms. This detects epimorphisms and monomorphisms. Pullback
preserves cokernels, so the monomorphism criterion for the map out of
the cokernel also detects exactness of a short complex.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricOpenCoverModuleExactness

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

variable {ι : Type} {X : Scheme.{0}} {V : ι → Scheme.{0}}
  (j : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (j i)]
  (cover : (⨆ i, (j i).opensRange) = ⊤)

include cover

/-- Pullbacks along a jointly covering family of open immersions
jointly detect equality of module maps. -/
theorem hom_ext_of_open_pullbacks {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ i, (Scheme.Modules.pullback (j i)).map f =
      (Scheme.Modules.pullback (j i)).map g) : f = g := by
  have hr (i : ι) : (Scheme.Modules.restrictFunctor (j i)).map f =
      (Scheme.Modules.restrictFunctor (j i)).map g := by
    let e := Scheme.Modules.restrictFunctorIsoPullback (j i)
    apply (cancel_mono (e.hom.app N)).mp
    exact (e.hom.naturality f).trans
      ((congrArg (e.hom.app M ≫ ·) (h i)).trans (e.hom.naturality g).symm)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
  intro x hx
  have hx' : x ∈ (⨆ i, (j i).opensRange) := by rw [cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
  let W := (j i) ⁻¹ᵁ U.unop
  have hw : (j i) ''ᵁ W ≤ U.unop := (j i).image_preimage_le U.unop
  refine ⟨(j i) ''ᵁ W, hw, ?_, ?_⟩
  · change x ∈ (j i) ''ᵁ (j i) ⁻¹ᵁ U.unop
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact ⟨hi, hx⟩
  · change N.val.map (homOfLE hw).op (f.val.app U s) =
      N.val.map (homOfLE hw).op (g.val.app U s)
    rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
    exact congrArg (fun k : (Scheme.Modules.restrictFunctor (j i)).obj M ⟶
      (Scheme.Modules.restrictFunctor (j i)).obj N =>
        k.val.app (op W) (M.val.map (homOfLE hw).op s)) (hr i)

theorem epi_of_open_pullbacks {M N : X.Modules} (q : M ⟶ N)
    (hq : ∀ i, Epi ((Scheme.Modules.pullback (j i)).map q)) : Epi q := by
  constructor
  intro Z f g h
  apply hom_ext_of_open_pullbacks j cover
  intro i
  let F := Scheme.Modules.pullback (j i)
  let := hq i
  apply (cancel_epi (F.map q)).mp
  exact (F.map_comp q f).symm.trans ((congrArg F.map h).trans (F.map_comp q g))

theorem mono_of_open_pullbacks {M N : X.Modules} (q : M ⟶ N)
    (hq : ∀ i, Mono ((Scheme.Modules.pullback (j i)).map q)) : Mono q := by
  constructor
  intro Z f g h
  apply hom_ext_of_open_pullbacks j cover
  intro i
  let F := Scheme.Modules.pullback (j i)
  let := hq i
  apply (cancel_mono (F.map q)).mp
  exact (F.map_comp f q).symm.trans ((congrArg F.map h).trans (F.map_comp g q))

theorem exact_of_open_pullbacks (S : ShortComplex X.Modules)
    (h : ∀ i, (S.map (Scheme.Modules.pullback (j i))).Exact) : S.Exact := by
  apply S.exact_iff_mono_cokernel_desc.mpr
  apply mono_of_open_pullbacks j cover
  intro i
  let F := Scheme.Modules.pullback (j i)
  apply (mono_comp_iff_of_isIso (cokernelComparison S.f F) _).mp
  rw [cokernelComparison_map_desc]
  exact (h i).mono_cokernelDesc

theorem shortExact_of_open_pullbacks (S : ShortComplex X.Modules)
    (h : ∀ i, (S.map (Scheme.Modules.pullback (j i))).ShortExact) : S.ShortExact :=
  ShortComplex.ShortExact.mk'
    (exact_of_open_pullbacks j cover S fun i => (h i).exact)
    (mono_of_open_pullbacks j cover S.f fun i => (h i).mono_f)
    (epi_of_open_pullbacks j cover S.g fun i => (h i).epi_g)

end CycleQ2GeometricOpenCoverModuleExactness

end

#print axioms CycleQ2GeometricOpenCoverModuleExactness.hom_ext_of_open_pullbacks
#print axioms CycleQ2GeometricOpenCoverModuleExactness.shortExact_of_open_pullbacks
