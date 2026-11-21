import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper closure of a parameter family reaches every specialization

Formalizes the proper-image step in Section 5 of the written cycle-q2 proof.
Given a proper parameter space `P → S` and a section over a dense open of
`S`, use the native scheme-theoretic image of that section, not all of `P`.
Its structure map is proved proper and surjective. Every base change is
therefore proper and surjective, including a pencil disjoint from the
original dense open. Points are obtained in the actual scheme pullback.

When the section is quasi-compact, the underlying closed subset is exactly
the closure of its image. Closed incidence conditions satisfied by the
original section are retained in this closure and after base change.

The proper flag-Hilbert space and its original section are geometric inputs
still to be constructed for cycle-q2. No cycle-class specialization,
finite/etale multisection, Betti/de Rham comparison, or residue vanishing is
asserted here. In particular no hypothesis is a renamed protected residue
exactness claim. The original protected theorem is unchanged.

Prepared for fqlx with OpenAI ChatGPT assistance, 15 November 2026.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CycleQ2ProperParameterSpecialization

variable {S P V T : Scheme.{u}} (p : P ⟶ S) (s : V ⟶ P)

/-- The native scheme-theoretic image of the original parameter map. -/
abbrev parameterClosure : Scheme.{u} := s.image

/-- The original structure map restricted to that closed subscheme. -/
def closureToBase : parameterClosure s ⟶ S := s.imageι ≫ p

@[reassoc (attr := simp)]
theorem toImage_closureToBase : s.toImage ≫ closureToBase p s = s ≫ p := by
  simp only [closureToBase, Scheme.Hom.toImage_imageι_assoc]

/-- Properness is inherited through the actual closed immersion. -/
instance closureToBase_isProper [IsProper p] : IsProper (closureToBase p s) := by
  dsimp only [closureToBase]
  infer_instance

/-- A dominant original parameter map makes its image closure dominant.
No quasi-compactness assumption is needed for this implication. -/
theorem closureToBase_isDominant [IsDominant (s ≫ p)] :
    IsDominant (closureToBase p s) := by
  have : IsDominant (s.toImage ≫ closureToBase p s) := by
    rw [toImage_closureToBase]
    infer_instance
  exact IsDominant.of_comp s.toImage (closureToBase p s)

/-- The closed image of a proper map containing a dense image is all of the
base. Surjectivity is proved, not supplied as a parameter-space hypothesis. -/
theorem closureToBase_surjective [IsProper p] [IsDominant (s ≫ p)] :
    Surjective (closureToBase p s) := by
  have : IsDominant (closureToBase p s) := closureToBase_isDominant p s
  exact surjective_of_isDominant_of_isClosed_range _
    (closureToBase p s).isClosedMap.isClosed_range

/-- Under the standard quasi-compactness hypothesis this really is the
closure of the original image, rather than an unrelated proper model. -/
theorem range_imageι [QuasiCompact s] :
    Set.range s.imageι = closure (Set.range s) := by
  change Set.range s.ker.subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]

/-- Any closed incidence condition satisfied by the parameter map is
preserved in its closure. This is a topological containment theorem,
not a claim about cohomology classes or scheme-theoretic multiplicities. -/
theorem imageι_mem_of_closed [QuasiCompact s]
    (Z : Set P) (hZ : IsClosed Z) (hs : Set.range s ⊆ Z)
    (x : parameterClosure s) : s.imageι x ∈ Z := by
  apply closure_minimal hs hZ
  rw [← range_imageι s]
  exact ⟨x, rfl⟩

/-- The genuine scheme pullback along any new base, including the exact
pencil even when it does not meet the original construction open. -/
abbrev specializedParameters (b : T ⟶ S) : Scheme.{u} :=
  pullback (closureToBase p s) b

abbrev specializationToBase (b : T ⟶ S) : specializedParameters p s b ⟶ T :=
  pullback.snd (closureToBase p s) b

/-- Remember the parameter in the original ambient proper space. -/
def specializationToParameter (b : T ⟶ S) : specializedParameters p s b ⟶ P :=
  pullback.fst (closureToBase p s) b ≫ s.imageι

@[reassoc]
theorem specialization_over_base (b : T ⟶ S) :
    specializationToParameter p s b ≫ p = specializationToBase p s b ≫ b := by
  change (pullback.fst (closureToBase p s) b ≫ s.imageι) ≫ p = _
  rw [Category.assoc]
  exact pullback.condition

instance specializationToBase_isProper [IsProper p] (b : T ⟶ S) :
    IsProper (specializationToBase p s b) := by
  dsimp only [specializationToBase]
  infer_instance

/-- Surjectivity is stable under arbitrary scheme base change; no density,
flatness, or dominance of the new pencil map is assumed. -/
theorem specializationToBase_surjective [IsProper p] [IsDominant (s ≫ p)]
    (b : T ⟶ S) : Surjective (specializationToBase p s b) := by
  have : Surjective (closureToBase p s) := closureToBase_surjective p s
  dsimp only [specializationToBase]
  infer_instance

/-- An actual parameter point above every point of the new base, together
with its original parameter map and the exact base compatibility. -/
theorem exists_specialized_parameter [IsProper p] [IsDominant (s ≫ p)]
    (b : T ⟶ S) (t : T) :
    ∃ x : specializedParameters p s b,
      specializationToBase p s b x = t ∧
      p (specializationToParameter p s b x) = b t := by
  have : Surjective (specializationToBase p s b) :=
    specializationToBase_surjective p s b
  obtain ⟨x, hx⟩ := (specializationToBase p s b).surjective t
  refine ⟨x, hx, ?_⟩
  have h := congrArg (fun f : specializedParameters p s b ⟶ S => f x)
    (specialization_over_base p s b)
  simpa only [Scheme.Hom.comp_apply, hx] using h

/-- Closed incidence conditions are still satisfied by the original
parameter underlying every base-changed point. -/
theorem specialized_parameter_mem_of_closed [QuasiCompact s]
    (b : T ⟶ S) (Z : Set P) (hZ : IsClosed Z) (hs : Set.range s ⊆ Z)
    (x : specializedParameters p s b) :
    specializationToParameter p s b x ∈ Z :=
  imageι_mem_of_closed s Z hZ hs (pullback.fst (closureToBase p s) b x)

section DenseOpenSection

variable (U : S.Opens) (σ : U.toScheme ⟶ P)
variable (hU : Dense (U : Set S)) (hσ : σ ≫ p = U.ι)

include hU hσ

/-- The dominant map needed above is supplied by the original section on
the original dense open. It is not an independent dominance assumption. -/
theorem section_isDominant : IsDominant (σ ≫ p) := by
  rw [hσ]
  constructor
  change Dense (Set.range U.ι)
  simpa only [Scheme.Opens.range_ι] using hU

/-- Closed proper parameter model attached to the given dense-open section. -/
theorem denseOpenSection_proper_surjective [IsProper p] :
    IsProper (closureToBase p σ) ∧ Surjective (closureToBase p σ) := by
  have : IsDominant (σ ≫ p) := section_isDominant p U σ hU hσ
  exact ⟨inferInstance, closureToBase_surjective p σ⟩

/-- The specialization endpoint used after a proper flag-Hilbert parameter
space and its dense-open section have been constructed. -/
theorem denseOpenSection_specialization [IsProper p] (b : T ⟶ S) :
    IsProper (specializationToBase p σ b) ∧
    Surjective (specializationToBase p σ b) ∧
    ∀ t : T, ∃ x : specializedParameters p σ b,
      specializationToBase p σ b x = t ∧
      p (specializationToParameter p σ b x) = b t := by
  have : IsDominant (σ ≫ p) := section_isDominant p U σ hU hσ
  exact ⟨inferInstance, specializationToBase_surjective p σ b,
    exists_specialized_parameter p σ b⟩

end DenseOpenSection

end CycleQ2ProperParameterSpecialization

end

#print axioms CycleQ2ProperParameterSpecialization.denseOpenSection_specialization
#print axioms CycleQ2ProperParameterSpecialization.specialized_parameter_mem_of_closed
