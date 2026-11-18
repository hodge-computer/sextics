import Proposal.GenericSourceReductions
import Proposal.GenericSourceCoordinates
import Proposal.ConcreteLine
import Mathlib.RingTheory.AdjoinRoot

noncomputable section
namespace GenericSpecialization
open Polynomial

abbrev E := AdjoinRoot P

def sourceRawFamily : Fin 8 → Polynomial ℚ :=
  ![sourceRaw_0, sourceRaw_1, sourceRaw_2, sourceRaw_3,
    sourceRaw_4, sourceRaw_5, sourceRaw_6, sourceRaw_7]

theorem sourceRawFamily_eq (i : Fin 8) :
    AdjoinRoot.mk P (sourceRawFamily i) = AdjoinRoot.mk P (sourcePolyFamily i) := by
  apply AdjoinRoot.mk_eq_mk.mpr
  fin_cases i
  · exact ⟨sourceQuotient_0, source_reduction_0⟩
  · exact ⟨sourceQuotient_1, source_reduction_1⟩
  · exact ⟨sourceQuotient_2, source_reduction_2⟩
  · exact ⟨sourceQuotient_3, source_reduction_3⟩
  · exact ⟨sourceQuotient_4, source_reduction_4⟩
  · exact ⟨sourceQuotient_5, source_reduction_5⟩
  · exact ⟨sourceQuotient_6, source_reduction_6⟩
  · exact ⟨sourceQuotient_7, source_reduction_7⟩

theorem sourceCoefficients_mk (i : Fin 8) :
    QuadricContact.ConcreteLine.sourceCoefficients
      (40 : E) 80 160 (algebraMap ℚ E (180/7))
      (AdjoinRoot.mk P line_x) (AdjoinRoot.mk P line_y)
      (AdjoinRoot.mk P line_z) (AdjoinRoot.mk P line_w) i
    = AdjoinRoot.mk P (sourcePolyFamily i) := by
  rw [← sourceRawFamily_eq i]
  fin_cases i <;>
    simp only [QuadricContact.ConcreteLine.sourceCoefficients, sourceRawFamily,
      Matrix.cons_val_zero, Matrix.cons_val_succ,
      Matrix.cons_val_zero', Matrix.cons_val_succ',
      sourceRaw_0, sourceRaw_1, sourceRaw_2, sourceRaw_3,
      sourceRaw_4, sourceRaw_5, sourceRaw_6, sourceRaw_7,
      map_add, map_sub, map_mul, map_pow, map_ofNat, AdjoinRoot.mk_C,
      AdjoinRoot.algebraMap_eq] <;>
    ring

end GenericSpecialization
