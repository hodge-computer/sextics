import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.FinitePresentation

/-!
# Smoothness of an algebra retract over a Noetherian base

A split algebra surjection from a formally smooth algebra supplies a
section of its first infinitesimal thickening, so formal smoothness
descends to the retract. For a smooth source over a Noetherian base,
surjectivity also gives finite type, hence finite presentation.

The intended application is the degree-zero chart of a weighted cone:
the chart includes into the full coordinate localization, and coordinate
normalization supplies its algebra retraction. Those concrete maps and
their retraction identity are separate constructions.

Source-only draft: no Lean elaboration, compilation, or kernel replay
has been run. Prepared for `fqlx` with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false

namespace CycleQ2GeometricSmoothRetract

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

/-- A section of the algebra surjection also splits its first
infinitesimal thickening. -/
theorem formallySmooth_of_retract [Algebra.FormallySmooth R A]
    (i : B →ₐ[R] A) (r : A →ₐ[R] B)
    (h : r.comp i = AlgHom.id R B) : Algebra.FormallySmooth R B := by
  exact Algebra.FormallySmooth.of_split r
    ((Ideal.Quotient.mkₐ R (RingHom.ker r.toRingHom ^ 2)).comp i)
    (AlgHom.ext fun b => AlgHom.congr_fun h b)

/-- A retract of a smooth algebra over a Noetherian base is smooth.
Noetherianity is used only to promote finite type to finite presentation. -/
theorem smooth_of_retract [IsNoetherianRing R] [Algebra.Smooth R A]
    (i : B →ₐ[R] A) (r : A →ₐ[R] B)
    (h : r.comp i = AlgHom.id R B) : Algebra.Smooth R B := by
  have hr : Function.Surjective r := fun b =>
    ⟨i b, AlgHom.congr_fun h b⟩
  exact
    { formallySmooth := formallySmooth_of_retract i r h
      finitePresentation := Algebra.FinitePresentation.of_finiteType.mp
        (Algebra.FiniteType.of_surjective r hr) }

end CycleQ2GeometricSmoothRetract

#print axioms CycleQ2GeometricSmoothRetract.formallySmooth_of_retract
#print axioms CycleQ2GeometricSmoothRetract.smooth_of_retract
