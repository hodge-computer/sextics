import Proposal.GeometricGradedCechDescent
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Additive-sheaf exactness from module splittings on an open cover

A splitting of a complex of modules restricts to a splitting of its
sections over each open. When such splittings exist on covering scheme
charts, their image opens give a basis on which the underlying additive
complex is sectionwise short exact.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricOpenCoverAdditiveExactness

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CycleQ2GeometricSheafLocalExactness

def additiveComplex {X : Scheme.{0}} (S : ShortComplex X.Modules) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) := by
  letI := moduleSheaf_toSheaf_preservesZeroMorphisms (X := (X : TopCat)) X.ringCatSheaf
  exact S.map (SheafOfModules.toSheaf X.ringCatSheaf)

theorem sections_of_splitting {X : Scheme.{0}} {S : ShortComplex X.Modules}
    (t : S.Splitting) (U : X.Opens) :
    Function.Injective (S.f.val.app (op U)) ∧
    Function.Exact (S.f.val.app (op U)) (S.g.val.app (op U)) ∧
    Function.Surjective (S.g.val.app (op U)) := by
  have h₁ (a : S.X₁.val.obj (op U)) : t.r.val.app (op U) (S.f.val.app (op U) a) = a :=
    congrArg (fun k => k.val.app (op U) a) t.f_r
  have h₃ (a : S.X₃.val.obj (op U)) : S.g.val.app (op U) (t.s.val.app (op U) a) = a :=
    congrArg (fun k => k.val.app (op U) a) t.s_g
  refine ⟨Function.LeftInverse.injective h₁, ?_, Function.RightInverse.surjective h₃⟩
  intro x
  constructor
  · intro hx
    refine ⟨t.r.val.app (op U) x, ?_⟩
    have h := congrArg (fun k => k.val.app (op U) x) t.id
    change S.f.val.app (op U) (t.r.val.app (op U) x) +
      t.s.val.app (op U) (S.g.val.app (op U) x) = x at h
    simpa only [hx, map_zero, add_zero] using h
  · rintro ⟨a, rfl⟩
    exact congrArg (fun k => k.val.app (op U) a) S.zero

theorem additiveShortExact_of_open_splittings {X : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}}
    (j : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (j i)] (cover : (⨆ i, (j i).opensRange) = ⊤)
    (S : ShortComplex X.Modules) (t : ∀ i, (S.map (Scheme.Modules.pullback (j i))).Splitting) :
    (additiveComplex S).ShortExact := by
  let B : Set X.Opens := {U | ∃ (i : ι) (W : (V i).Opens), (j i) ''ᵁ W = U}
  have hB : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    intro U x hx
    have hx' : x ∈ (⨆ i, (j i).opensRange) := by rw [cover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
    refine ⟨(j i) ''ᵁ (j i) ⁻¹ᵁ U, ⟨i, (j i) ⁻¹ᵁ U, rfl⟩, ?_, (j i).image_preimage_le U⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact ⟨hi, hx⟩
  have h (U : X.Opens) (hU : U ∈ B) :
      Function.Injective (S.f.val.app (op U)) ∧
      Function.Exact (S.f.val.app (op U)) (S.g.val.app (op U)) ∧
      Function.Surjective (S.g.val.app (op U)) := by
    obtain ⟨i, W, rfl⟩ := hU
    let e := (Scheme.Modules.restrictFunctorIsoPullback (j i)).symm
    let := Functor.preservesZeroMorphisms_of_iso e
    exact sections_of_splitting ((t i).ofIso (S.mapNatIso e)) W
  exact additiveSheaf_shortExact_of_basis (additiveComplex S) B hB
    (fun U hU => (h U hU).1) (fun U hU => (h U hU).2.1) (fun U hU => (h U hU).2.2)

end CycleQ2GeometricOpenCoverAdditiveExactness

end

#print axioms CycleQ2GeometricOpenCoverAdditiveExactness.additiveShortExact_of_open_splittings
