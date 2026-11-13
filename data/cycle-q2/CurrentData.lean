import Proposal.CurrentAtoms047

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def baseD : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00013 ^ 2 * a00014 ^ 10 * a00015 ^ 2 * a00018 ^ 2 * a00026 ^ 1 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 2)
theorem h_baseD : baseD.IsHomogeneous 3726 := by
  unfold baseD
  exact ((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00013.pow 2)).mul (ha00014.pow 10)).mul (ha00015.pow 2)).mul (ha00018.pow 2)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 2))

@[irreducible]
def exportedF : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07989 ^ 1)
theorem h_exportedF : exportedF.IsHomogeneous 6 := by
  unfold exportedF
  exact ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07989.pow 1))

@[irreducible]
def exportedA : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 2 * a00001 ^ 2 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 1)
theorem h_exportedA : exportedA.IsHomogeneous 12 := by
  unfold exportedA
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 2)).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 1))

@[irreducible]
def baseN0 : Poly := (C ((-125 : ℂ) / (17496 : ℂ)) * a00000 ^ 2 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a07960 ^ 1 * a07982 ^ 1)
theorem h_baseN0 : baseN0.IsHomogeneous 3733 := by
  unfold baseN0
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-125 : ℂ) / (17496 : ℂ))).mul (ha00000.pow 2)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha07960.pow 1)).mul (ha07982.pow 1))

@[irreducible]
def baseN1 : Poly := (C ((125 : ℂ) / (2916 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a00010 ^ 1 * a07960 ^ 1 * a07984 ^ 1)
theorem h_baseN1 : baseN1.IsHomogeneous 3733 := by
  unfold baseN1
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((125 : ℂ) / (2916 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00010.pow 1)).mul (ha07960.pow 1)).mul (ha07984.pow 1))

@[irreducible]
def baseN2 : Poly := (C ((0 : ℂ) / (1 : ℂ)))
theorem h_baseN2 : baseN2.IsHomogeneous 3733 := by
  unfold baseN2
  convert isHomogeneous_zero (R := ℂ) (σ := Fin 6) 3733 using 1 <;> simp

@[irreducible]
def baseN3 : Poly := (C ((-125 : ℂ) / (17496 : ℂ)) * a00000 ^ 1 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 1 * a07960 ^ 1 * a07986 ^ 1)
theorem h_baseN3 : baseN3.IsHomogeneous 3733 := by
  unfold baseN3
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-125 : ℂ) / (17496 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha07960.pow 1)).mul (ha07986.pow 1))

@[irreducible]
def baseN4 : Poly := (C ((125 : ℂ) / (2916 : ℂ)) * a00000 ^ 1 * a00003 ^ 1 * a00004 ^ 3 * a00005 ^ 1 * a00010 ^ 1 * a07960 ^ 1 * a07987 ^ 1)
theorem h_baseN4 : baseN4.IsHomogeneous 3733 := by
  unfold baseN4
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((125 : ℂ) / (2916 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00010.pow 1)).mul (ha07960.pow 1)).mul (ha07987.pow 1))

@[irreducible]
def baseN5 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a00010 ^ 1 * a00014 ^ 3 * a00015 ^ 1 * a00016 ^ 1 * a00018 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 4 * a00105 ^ 4 * a00123 ^ 3 * a00124 ^ 5 * a00134 ^ 11 * a07824 ^ 1 * a07952 ^ 1 * a07960 ^ 2)
theorem h_baseN5 : baseN5.IsHomogeneous 3733 := by
  unfold baseN5
  exact ((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00010.pow 1)).mul (ha00014.pow 3)).mul (ha00015.pow 1)).mul (ha00016.pow 1)).mul (ha00018.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 4)).mul (ha00105.pow 4)).mul (ha00123.pow 3)).mul (ha00124.pow 5)).mul (ha00134.pow 11)).mul (ha07824.pow 1)).mul (ha07952.pow 1)).mul (ha07960.pow 2))

@[irreducible]
def baseR : Poly := (C ((-125 : ℂ) / (81 : ℂ)) * a00000 ^ 1 * a00003 ^ 1 * a00004 ^ 2 * a00012 ^ 1 * a00013 ^ 1 * a00014 ^ 9 * a00015 ^ 3 * a00016 ^ 1 * a00018 ^ 3 * a00026 ^ 2 * a00033 ^ 2 * a00034 ^ 3 * a00042 ^ 4 * a00100 ^ 4 * a00101 ^ 6 * a00103 ^ 6 * a00105 ^ 3 * a00106 ^ 1 * a00123 ^ 3 * a00124 ^ 5 * a00134 ^ 10 * a07824 ^ 1 * a07960 ^ 4 * a13851 ^ 1)
theorem h_baseR : baseR.IsHomogeneous 7452 := by
  unfold baseR
  exact (((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-125 : ℂ) / (81 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 9)).mul (ha00015.pow 3)).mul (ha00016.pow 1)).mul (ha00018.pow 3)).mul (ha00026.pow 2)).mul (ha00033.pow 2)).mul (ha00034.pow 3)).mul (ha00042.pow 4)).mul (ha00100.pow 4)).mul (ha00101.pow 6)).mul (ha00103.pow 6)).mul (ha00105.pow 3)).mul (ha00106.pow 1)).mul (ha00123.pow 3)).mul (ha00124.pow 5)).mul (ha00134.pow 10)).mul (ha07824.pow 1)).mul (ha07960.pow 4)).mul (ha13851.pow 1))

@[irreducible]
def baseQ : Poly := (C ((500 : ℂ) / (81 : ℂ)) * a00000 ^ 1 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 1 * a00013 ^ 2 * a00014 ^ 12 * a00015 ^ 2 * a00018 ^ 4 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 1 * a13873 ^ 1)
theorem h_baseQ : baseQ.IsHomogeneous 7446 := by
  unfold baseQ
  exact ((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((500 : ℂ) / (81 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 2)).mul (ha00014.pow 12)).mul (ha00015.pow 2)).mul (ha00018.pow 4)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 1)).mul (ha13873.pow 1))

@[irreducible]
def baseN (i : Fin 6) : Poly :=
  ![baseN0, baseN1, baseN2, baseN3, baseN4, baseN5] i

theorem h_baseN (i : Fin 6) : (baseN i).IsHomogeneous 3733 := by
  fin_cases i
  · simpa [baseN] using h_baseN0
  · simpa [baseN] using h_baseN1
  · simpa [baseN] using h_baseN2
  · simpa [baseN] using h_baseN3
  · simpa [baseN] using h_baseN4
  · simpa [baseN] using h_baseN5

/-- Exact source binding, not a sampled equality. -/
theorem exportedF_eq_originalF : exportedF = CycleQ2Workspace.originalF := by
  unfold exportedF a07989 a07988 a00000 a00001 a00002 a00003 a00004 a00005
  unfold CycleQ2Workspace.originalF HodgeSubmission.F
  norm_num <;> ring

theorem exportedA_eq_originalA : exportedA = CycleQ2Workspace.originalA := by
  unfold exportedA a00000 a00001 a00002 a00003 a00004 a00005
  unfold CycleQ2Workspace.originalA HodgeSubmission.A
  norm_num <;> ring

/-- This is the literal original cleared defect of the actual saved data. -/
def literalDefect : Poly :=
  HodgeComputer.defect CycleQ2Workspace.originalF CycleQ2Workspace.originalA baseD 2 baseN

/-- An explicit comparison polynomial. No theorem claiming it is zero is assumed. -/
def transportError : Poly :=
  literalDefect + CycleQ2Workspace.originalF ^ 2 * baseR -
    CycleQ2Workspace.originalF ^ 3 * baseQ

/-- Formalizing the archived generic derivation means proving this proposition. -/
def ArchivedPartialIdentityGoal : Prop := transportError = 0

#print axioms exportedF_eq_originalF
#print axioms exportedA_eq_originalA
#print axioms h_baseN
end CycleQ2Concrete
