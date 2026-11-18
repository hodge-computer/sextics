import Proposal.GeometricLiteralThreefoldExteriorDerivative

/-! Exterior differentiation of two-forms on a threefold chart covered by exact frames.

A two-form is a sum of expressions `f dg ∧ dh`. Their candidate derivatives
`df ∧ dg ∧ dh` restrict to the exterior derivative on every exact frame. On
a chart where these restrictions detect three-forms, this determines one
additive exterior differential on the original ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2LiteralThreefoldExteriorDescent

open CycleQ2LiteralThreefoldCartan CycleQ2LiteralThreefoldExteriorDerivative
  CycleQ2ExteriorSectionNaturality CycleQ2GeometricAffineOverlap Module

variable {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]

/-- Every exact three-dimensional frame sees the derivative of `ω` as `z`. -/
def Represents (ω : Forms A 2) (z : Forms A 3) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra ℂ B] (φ : A →ₐ[ℂ] B)
    (b : Basis (Fin 3) B (OneForms B)) (u : Fin 3 → B)
    (_ : ∀ i, b i = KaehlerDifferential.D ℂ B (u i)),
    exteriorDifferentialMap φ 3 z = exteriorD2 b (exteriorDifferentialMap φ 2 ω)

private theorem exact_symbol (f g h : A) :
    Represents (f • exteriorPower.ιMulti A 2 ![KaehlerDifferential.D ℂ A g,
        KaehlerDifferential.D ℂ A h])
      (exteriorPower.ιMulti A 3 ![KaehlerDifferential.D ℂ A f, KaehlerDifferential.D ℂ A g,
        KaehlerDifferential.D ℂ A h]) := by
  intro B _ _ φ b u hu
  rw [LinearMap.map_smulₛₗ, exteriorDifferentialMap_wedge, exteriorDifferentialMap_wedge]
  have h₂ : (fun l => differentialMap φ
      (![KaehlerDifferential.D ℂ A g, KaehlerDifferential.D ℂ A h] l)) =
      ![KaehlerDifferential.D ℂ B (φ g), KaehlerDifferential.D ℂ B (φ h)] := by
    funext l
    fin_cases l <;> apply differentialMap_D
  have h₃ : (fun l => differentialMap φ
      (![KaehlerDifferential.D ℂ A f, KaehlerDifferential.D ℂ A g,
        KaehlerDifferential.D ℂ A h] l)) =
      ![KaehlerDifferential.D ℂ B (φ f), KaehlerDifferential.D ℂ B (φ g),
        KaehlerDifferential.D ℂ B (φ h)] := by
    funext l
    fin_cases l <;> apply differentialMap_D
  rw [h₂, h₃]
  exact (exteriorD2_exact_wedge b u hu (φ f) (φ g) (φ h)).symm

private theorem represents_add {ω η : Forms A 2} {z t : Forms A 3}
    (h : Represents ω z) (g : Represents η t) : Represents (ω + η) (z + t) := by
  intro B _ _ φ b u hu
  change _ = additive b _
  rw [map_add, map_add, map_add]
  exact congrArg₂ (· + ·) (h B φ b u hu) (g B φ b u hu)

private theorem represents_zero : Represents (0 : Forms A 2) 0 := by
  intro B _ _ φ b u hu
  change _ = additive b _
  exact (map_zero (exteriorDifferentialMap φ 3)).trans
    ((congrArg (additive b) (map_zero (exteriorDifferentialMap φ 2))).trans
      (map_zero (additive b))).symm

/-- A single three-form on the original ring has the correct restrictions. -/
theorem exists_representative (ω : Forms A 2) : ∃ z, Represents ω z := by
  let d := KaehlerDifferential.D ℂ A
  have hω : ω ∈ Submodule.span A (exteriorPower.ιMulti A 2 ''
      {m : Fin 2 → OneForms A | Set.range m ⊆ Set.range d}) := by
    rw [exteriorPower.ιMulti_span_of_span A 2 _ (KaehlerDifferential.span_range_derivation ℂ A)]
    trivial
  suffices h : ∀ c : A, ∃ z, Represents (c • ω) z by simpa using h 1
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨g, hg⟩ := hm (Set.mem_range_self 0)
    obtain ⟨h, hh⟩ := hm (Set.mem_range_self 1)
    have e : m = ![d g, d h] := by
      funext l
      fin_cases l
      · exact hg.symm
      · exact hh.symm
    rw [e]
    intro c
    exact ⟨_, exact_symbol c g h⟩
  | zero =>
    intro c
    rw [smul_zero]
    exact ⟨0, represents_zero⟩
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨z, hz⟩ := hx c
    obtain ⟨t, ht⟩ := hy c
    rw [smul_add]
    exact ⟨z + t, represents_add hz ht⟩
  | smul r x _ hx =>
    intro c
    rw [smul_smul]
    exact hx (c * r)

/-- A candidate is unique if maps to exact frames jointly detect three-forms. -/
def Separated (A : Type) [CommRing A] [Algebra ℂ A] : Prop :=
  ∀ z t : Forms A 3, Represents (0 : Forms A 2) (z - t) → z = t

theorem unique (hA : Separated A) {ω : Forms A 2} {z t : Forms A 3}
    (hz : Represents ω z) (ht : Represents ω t) : z = t := by
  apply hA
  intro B _ _ φ b u hu
  change _ = additive b _
  rw [map_sub, hz B φ b u hu, ht B φ b u hu, sub_self, map_zero, map_zero]

/-- The exterior differential on the chart prior to passing to any gradient open. -/
def differential (hA : Separated A) : Forms A 2 →+ Forms A 3 where
  toFun ω := (exists_representative ω).choose
  map_zero' := unique hA (exists_representative 0).choose_spec represents_zero
  map_add' x y := unique hA (exists_representative (x+y)).choose_spec
    (represents_add (exists_representative x).choose_spec (exists_representative y).choose_spec)

theorem differential_represents (hA : Separated A) (ω : Forms A 2) :
    Represents ω (differential hA ω) := (exists_representative ω).choose_spec

theorem map_comp {C : Type} [CommRing C] [Algebra ℂ C]
    (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C) (n : ℕ) (ω : Forms A n) :
    exteriorDifferentialMap g n (exteriorDifferentialMap f n ω) =
      exteriorDifferentialMap (g.comp f) n ω :=
  (CycleQ2GeometricExteriorSheaf.exteriorMap_composition f.toRingHom g.toRingHom (g.comp f).toRingHom
    (differentialSemilinearMap f) (differentialSemilinearMap g)
    (differentialSemilinearMap (g.comp f)) (fun _ => rfl)
    (fun z => (differentialMap_comp f g z).symm) n ω).symm

/-- Pullback commutes with the unlocalized exterior differential. -/
theorem differential_natural (hA : Separated A) (hB : Separated B)
    (f : A →ₐ[ℂ] B) (ω : Forms A 2) :
    exteriorDifferentialMap f 3 (differential hA ω) =
      differential hB (exteriorDifferentialMap f 2 ω) := by
  apply unique hB _ (differential_represents hB _)
  intro C _ _ g b u hu
  rw [map_comp, map_comp]
  exact differential_represents hA ω C (g.comp f) b u hu

theorem differential_exact (hA : Separated A) (f g h : A) :
    differential hA (f • exteriorPower.ιMulti A 2 ![KaehlerDifferential.D ℂ A g,
      KaehlerDifferential.D ℂ A h]) =
      exteriorPower.ιMulti A 3 ![KaehlerDifferential.D ℂ A f, KaehlerDifferential.D ℂ A g,
        KaehlerDifferential.D ℂ A h] :=
  unique hA (differential_represents hA _) (exact_symbol f g h)

end CycleQ2LiteralThreefoldExteriorDescent
end

#print axioms CycleQ2LiteralThreefoldExteriorDescent.differential_exact
