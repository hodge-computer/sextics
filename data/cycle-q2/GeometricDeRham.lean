import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Proposal.GeometricFormalInputs04

/-!
# The actual rational de Rham complex as a Mathlib cochain complex

Source-only continuation of Part IV.6 of the written nonconstructive proof.
This file has not been elaborated or compiled.

The existing source provides the genuine Kahler differential, its exterior
powers, the differentials through degree four, and their square-zero
identities. Here they are assembled into a `CochainComplex (ModuleCat C) N`.
Its degree-four homology is canonically identified with the existing quotient
of actual four-forms by actual exact forms. Thus a future geometric comparison
can use Mathlib's homology API without replacing the protected rational-form
target by an unrelated cohomology model.

This construction does not assert the algebraic de Rham comparison theorem,
construct Betti cohomology, or prove vanishing of the protected residue.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

namespace CycleQ2GeometricDeRham

open CycleQ2AffineDifferentials CycleQ2AffineExterior
open CycleQ2AffineDeRhamComplex

/-- The actual rational forms in degrees zero through four. The tail is
the zero module. The genuine fifth exterior power is already proved zero
in `CycleQ2AffineTopCohomology.formFiveSubsingleton`. -/
def object : ℕ → ModuleCat ℂ
  | 0 => ModuleCat.of ℂ K
  | 1 => ModuleCat.of ℂ Omega
  | 2 => ModuleCat.of ℂ (Form 2)
  | 3 => ModuleCat.of ℂ (Form 3)
  | 4 => ModuleCat.of ℂ (Form 4)
  | _ + 5 => ModuleCat.of ℂ (Fin 0 → ℂ)

/-- Every nonzero differential is an existing map on actual forms. In
particular, the degree-three map is exactly the protected `exteriorD3`. -/
def differential : (n : ℕ) → (object n ⟶ object (n + 1))
  | 0 => ModuleCat.ofHom d.toLinearMap
  | 1 => ModuleCat.ofHom exteriorD1
  | 2 => ModuleCat.ofHom exteriorD2
  | 3 => ModuleCat.ofHom exteriorD3
  | _ + 4 => 0

theorem differential_comp (n : ℕ) :
    differential n ≫ differential (n + 1) = 0 := by
  cases n with
  | zero =>
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      exact exteriorD1_d a
  | succ n =>
      cases n with
      | zero =>
          apply ModuleCat.hom_ext
          exact exteriorD2_comp_exteriorD1
      | succ n =>
          cases n with
          | zero =>
              apply ModuleCat.hom_ext
              exact exteriorD3_comp_exteriorD2
          | succ n =>
              cases n with
              | zero =>
                  change ModuleCat.ofHom exteriorD3 ≫ 0 = 0
                  exact CategoryTheory.Limits.comp_zero
              | succ n =>
                  change (0 : object (n + 4) ⟶ object (n + 5)) ≫ 0 = 0
                  exact CategoryTheory.Limits.zero_comp

/-- A bounded cochain complex with the original rational exterior
derivatives, not a complex introduced by assuming the desired exactness. -/
def complex : CochainComplex (ModuleCat ℂ) ℕ :=
  CochainComplex.of object differential differential_comp

@[simp] theorem complex_d_succ (n : ℕ) :
    complex.d n (n + 1) = differential n :=
  CochainComplex.of_d object differential n

@[simp] theorem complex_d_three :
    complex.d 3 4 = ModuleCat.ofHom exteriorD3 := by
  simpa only [differential] using complex_d_succ 3

@[simp] theorem complex_d_four : complex.d 4 5 = 0 := by
  simpa only [differential] using complex_d_succ 4

/-- The actual incoming and outgoing maps in degree four. -/
abbrev topShortComplex : ShortComplex (ModuleCat ℂ) :=
  complex.sc' 3 4 5

theorem topShortComplex_f :
    topShortComplex.f = ModuleCat.ofHom exteriorD3 :=
  complex_d_three

theorem topShortComplex_g : topShortComplex.g = 0 :=
  complex_d_four

/-- The concrete cokernel is the quotient already used by the protected
residue construction. No new vanishing hypothesis enters this isomorphism. -/
def topOpcyclesIso :
    topShortComplex.opcycles ≅
      ModuleCat.of ℂ CycleQ2AffineTopCohomology.TopDeRham := by
  have hf : topShortComplex.f.hom = exteriorD3 :=
    congrArg ModuleCat.Hom.hom topShortComplex_f
  have h := topShortComplex.moduleCatOpcyclesIso
  change topShortComplex.opcycles ≅
    ModuleCat.of ℂ ((Form 4) ⧸ LinearMap.range topShortComplex.f.hom) at h
  rw [hf] at h
  exact h

/-- With zero outgoing differential, homology is canonically the cokernel
of the actual degree-three differential. -/
def topShortHomologyIso :
    topShortComplex.homology ≅
      ModuleCat.of ℂ CycleQ2AffineTopCohomology.TopDeRham :=
  topShortComplex.asIsoHomologyι topShortComplex_g ≪≫ topOpcyclesIso

/-- The degree-four homology of the complete cochain complex agrees with
the existing rational de Rham quotient. -/
def homologyIso :
    complex.homology 4 ≅
      ModuleCat.of ℂ CycleQ2AffineTopCohomology.TopDeRham :=
  complex.homologyIsoSc' 3 4 5
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 3 4 from rfl))
    ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 4 5 from rfl)) ≪≫
      topShortHomologyIso

/-- The class of an actual rational four-form in Mathlib's degree-four
homology, transported along the canonical cokernel identification. -/
def classOf : Form 4 →ₗ[ℂ] complex.homology 4 :=
  homologyIso.inv.hom.comp CycleQ2AffineTopCohomology.classOf

@[simp] theorem homologyIso_classOf (ω : Form 4) :
    homologyIso.hom (classOf ω) =
      CycleQ2AffineTopCohomology.classOf ω := by
  change homologyIso.hom
      (homologyIso.inv (CycleQ2AffineTopCohomology.classOf ω)) = _
  have h := congrArg
    (fun f : ModuleCat.of ℂ CycleQ2AffineTopCohomology.TopDeRham ⟶
        ModuleCat.of ℂ CycleQ2AffineTopCohomology.TopDeRham =>
      f (CycleQ2AffineTopCohomology.classOf ω)) homologyIso.inv_hom_id
  change homologyIso.hom
    (homologyIso.inv (CycleQ2AffineTopCohomology.classOf ω)) =
      CycleQ2AffineTopCohomology.classOf ω at h
  exact h

theorem classOf_eq_zero_iff (ω : Form 4) :
    classOf ω = 0 ↔ ∃ η : Form 3, exteriorD3 η = ω := by
  constructor
  · intro h
    apply (CycleQ2AffineTopCohomology.classOf_eq_zero_iff ω).mp
    have h' := congrArg homologyIso.hom h
    change homologyIso.hom (classOf ω) = homologyIso.hom 0 at h'
    rw [homologyIso_classOf, map_zero] at h'
    exact h'
  · rintro ⟨η, rfl⟩
    simp only [classOf, LinearMap.comp_apply,
      CycleQ2AffineTopCohomology.classOf_exteriorD3, map_zero]

/-- The class is tied to the exact fixed numerator and residue density. -/
def residueClass : complex.homology 4 :=
  classOf (CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA)

theorem residueClass_eq_zero_iff :
    residueClass = 0 ↔
      ∃ η : Form 3, exteriorD3 η =
        CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA :=
  classOf_eq_zero_iff _

/-- The homology formulation returns the unchanged protected certificate.
Actual vanishing must be supplied by the geometric argument. -/
theorem protected_certificate_of_residueClass_eq_zero
    (h : residueClass = 0) :
    HodgeComputer.HasCertificate
      HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm
    (residueClass_eq_zero_iff.mp h)

end CycleQ2GeometricDeRham

end
