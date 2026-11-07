import Proposal.CurrentAtoms011

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a04864 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00850 ^ 1 * a01035 ^ 1)
theorem ha04864 : a04864.IsHomogeneous 987 := by
  unfold a04864
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00850.pow 1)).mul (ha01035.pow 1)))

@[irreducible]
def a04865 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a02395 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04858 ^ 1)
theorem ha04865 : a04865.IsHomogeneous 1254 := by
  unfold a04865
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha02395.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04858.pow 1)))

@[irreducible]
def a04866 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a04865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04864 ^ 1)
theorem ha04866 : a04866.IsHomogeneous 1320 := by
  unfold a04866
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha04865.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04864.pow 1)))

@[irreducible]
def a04867 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a01979 ^ 1)
theorem ha04867 : a04867.IsHomogeneous 690 := by
  unfold a04867
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a04868 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04867 ^ 1)
theorem ha04868 : a04868.IsHomogeneous 1023 := by
  unfold a04868
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04864.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04867.pow 1)))

@[irreducible]
def a04869 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04866 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04868 ^ 1)
theorem ha04869 : a04869.IsHomogeneous 1356 := by
  unfold a04869
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04866.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04868.pow 1)))

@[irreducible]
def a04870 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a01290 ^ 1)
theorem ha04870 : a04870.IsHomogeneous 1113 := by
  unfold a04870
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a04871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00492 ^ 1 * a01196 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a02687 ^ 1)
theorem ha04871 : a04871.IsHomogeneous 1386 := by
  unfold a04871
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00492.pow 1)).mul (ha01196.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a04872 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a04871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04870 ^ 1)
theorem ha04872 : a04872.IsHomogeneous 1446 := by
  unfold a04872
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha04871.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04870.pow 1)))

@[irreducible]
def a04873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a02860 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a01290 ^ 1)
theorem ha04873 : a04873.IsHomogeneous 840 := by
  unfold a04873
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha02860.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a04874 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04873 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a04870 ^ 1)
theorem ha04874 : a04874.IsHomogeneous 1173 := by
  unfold a04874
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04873.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha04870.pow 1)))

@[irreducible]
def a04875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04874 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a04872 ^ 1)
theorem ha04875 : a04875.IsHomogeneous 1506 := by
  unfold a04875
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04874.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha04872.pow 1)))

@[irreducible]
def a04876 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a01313 ^ 1)
theorem ha04876 : a04876.IsHomogeneous 1029 := by
  unfold a04876
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a04877 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00501 ^ 1 * a01196 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a02687 ^ 1)
theorem ha04877 : a04877.IsHomogeneous 1326 := by
  unfold a04877
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00501.pow 1)).mul (ha01196.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a04878 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04877 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04876 ^ 1)
theorem ha04878 : a04878.IsHomogeneous 1362 := by
  unfold a04878
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04877.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04876.pow 1)))

@[irreducible]
def a04879 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a02904 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a01313 ^ 1)
theorem ha04879 : a04879.IsHomogeneous 732 := by
  unfold a04879
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha02904.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a04880 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04879 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04876 ^ 1)
theorem ha04880 : a04880.IsHomogeneous 1065 := by
  unfold a04880
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04879.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04876.pow 1)))

@[irreducible]
def a04881 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04880 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04878 ^ 1)
theorem ha04881 : a04881.IsHomogeneous 1398 := by
  unfold a04881
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04880.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04878.pow 1)))

@[irreducible]
def a04882 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a02540 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00804 ^ 1 * a01103 ^ 1)
theorem ha04882 : a04882.IsHomogeneous 1168 := by
  unfold a04882
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha02540.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a04883 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a01103 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a01886 ^ 1)
theorem ha04883 : a04883.IsHomogeneous 1441 := by
  unfold a04883
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha01103.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a04884 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04882 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a04883 ^ 1)
theorem ha04884 : a04884.IsHomogeneous 1501 := by
  unfold a04884
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04882.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha04883.pow 1)))

@[irreducible]
def a04885 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a02538 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a01102 ^ 1)
theorem ha04885 : a04885.IsHomogeneous 433 := by
  unfold a04885
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha02538.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha01102.pow 1)))

@[irreducible]
def a04886 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00834 ^ 1 * a01102 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00398 ^ 1 * a01946 ^ 1)
theorem ha04886 : a04886.IsHomogeneous 433 := by
  unfold a04886
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00834.pow 1)).mul (ha01102.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00398.pow 1)).mul (ha01946.pow 1)))

@[irreducible]
def a04887 : Poly := (C ((-18 : ℂ) / (1 : ℂ)) * a04886 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04885 ^ 1)
theorem ha04887 : a04887.IsHomogeneous 433 := by
  unfold a04887
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha04886.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04885.pow 1)))

@[irreducible]
def a04888 : Poly := (C ((-5 : ℂ) / (1 : ℂ)) * a00823 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a02413 ^ 1)
theorem ha04888 : a04888.IsHomogeneous 132 := by
  unfold a04888
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1 : ℂ))).mul (ha00823.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a04889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00506 ^ 1)
theorem ha04889 : a04889.IsHomogeneous 18 := by
  unfold a04889
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a04890 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1)
theorem ha04890 : a04890.IsHomogeneous 18 := by
  unfold a04890
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a04891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04889 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a04890 ^ 1)
theorem ha04891 : a04891.IsHomogeneous 18 := by
  unfold a04891
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04889.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha04890.pow 1)))

@[irreducible]
def a04892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00541 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04889 ^ 1)
theorem ha04892 : a04892.IsHomogeneous 18 := by
  unfold a04892
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00541.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04889.pow 1)))

@[irreducible]
def a04893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04891 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04892 ^ 1)
theorem ha04893 : a04893.IsHomogeneous 18 := by
  unfold a04893
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04892.pow 1)))

@[irreducible]
def a04894 : Poly := (C ((-21 : ℂ) / (5 : ℂ)) * a04893 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01461 ^ 1)
theorem ha04894 : a04894.IsHomogeneous 18 := by
  unfold a04894
  exact (((isHomogeneous_C (σ := Fin 6) ((-21 : ℂ) / (5 : ℂ))).mul (ha04893.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01461.pow 1)))

@[irreducible]
def a04895 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04894 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a02413 ^ 1)
theorem ha04895 : a04895.IsHomogeneous 132 := by
  unfold a04895
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04894.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a04896 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04888 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04895 ^ 1)
theorem ha04896 : a04896.IsHomogeneous 132 := by
  unfold a04896
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04888.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04895.pow 1)))

@[irreducible]
def a04897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00823 ^ 1 * a01041 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00003 ^ 3 * a00368 ^ 1 * a01923 ^ 1)
theorem ha04897 : a04897.IsHomogeneous 132 := by
  unfold a04897
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00823.pow 1)).mul (ha01041.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00003.pow 3)).mul (ha00368.pow 1)).mul (ha01923.pow 1)))

@[irreducible]
def a04898 : Poly := (C ((-5 : ℂ) / (1 : ℂ)) * a04897 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04888 ^ 1)
theorem ha04898 : a04898.IsHomogeneous 132 := by
  unfold a04898
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1 : ℂ))).mul (ha04897.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04888.pow 1)))

@[irreducible]
def a04899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04898 ^ 1)
theorem ha04899 : a04899.IsHomogeneous 132 := by
  unfold a04899
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04896.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04898.pow 1)))

@[irreducible]
def a04900 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a01264 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00480 ^ 1 * a01207 ^ 1)
theorem ha04900 : a04900.IsHomogeneous 157 := by
  unfold a04900
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha01264.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00480.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a04901 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00480 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00148 ^ 1 * a02710 ^ 1)
theorem ha04901 : a04901.IsHomogeneous 151 := by
  unfold a04901
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00480.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00148.pow 1)).mul (ha02710.pow 1)))

@[irreducible]
def a04902 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a04900 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04901 ^ 1)
theorem ha04902 : a04902.IsHomogeneous 157 := by
  unfold a04902
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha04900.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04901.pow 1)))

@[irreducible]
def a04903 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a01264 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a02814 ^ 1)
theorem ha04903 : a04903.IsHomogeneous 157 := by
  unfold a04903
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha01264.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha02814.pow 1)))

@[irreducible]
def a04904 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04900 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04903 ^ 1)
theorem ha04904 : a04904.IsHomogeneous 157 := by
  unfold a04904
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04900.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04903.pow 1)))

@[irreducible]
def a04905 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a04904 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04902 ^ 1)
theorem ha04905 : a04905.IsHomogeneous 157 := by
  unfold a04905
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha04904.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04902.pow 1)))

@[irreducible]
def a04906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04905 ^ 1) + (C ((4 : ℂ) / (375 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a00014 ^ 2 * a04899 ^ 1)
theorem ha04906 : a04906.IsHomogeneous 157 := by
  unfold a04906
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04905.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (375 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha04899.pow 1)))

@[irreducible]
def a04907 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00298 ^ 1 * a02499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1 * a01083 ^ 1)
theorem ha04907 : a04907.IsHomogeneous 186 := by
  unfold a04907
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00298.pow 1)).mul (ha02499.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha01083.pow 1)))

@[irreducible]
def a04908 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00389 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a01083 ^ 1)
theorem ha04908 : a04908.IsHomogeneous 177 := by
  unfold a04908
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00389.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha01083.pow 1)))

@[irreducible]
def a04909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04908 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04907 ^ 1)
theorem ha04909 : a04909.IsHomogeneous 186 := by
  unfold a04909
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04908.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04907.pow 1)))

@[irreducible]
def a04910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a02432 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00829 ^ 1 * a01048 ^ 1)
theorem ha04910 : a04910.IsHomogeneous 117 := by
  unfold a04910
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha02432.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00829.pow 1)).mul (ha01048.pow 1)))

@[irreducible]
def a04911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a01045 ^ 1)
theorem ha04911 : a04911.IsHomogeneous 30 := by
  unfold a04911
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha01045.pow 1)))

@[irreducible]
def a04912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01045 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02425 ^ 1)
theorem ha04912 : a04912.IsHomogeneous 33 := by
  unfold a04912
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01045.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02425.pow 1)))

@[irreducible]
def a04913 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04911 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a04912 ^ 1)
theorem ha04913 : a04913.IsHomogeneous 36 := by
  unfold a04913
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04911.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha04912.pow 1)))

@[irreducible]
def a04914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00316 ^ 1)
theorem ha04914 : a04914.IsHomogeneous 27 := by
  unfold a04914
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a04915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00864 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00316 ^ 1)
theorem ha04915 : a04915.IsHomogeneous 36 := by
  unfold a04915
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a04916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04915 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04914 ^ 1)
theorem ha04916 : a04916.IsHomogeneous 36 := by
  unfold a04916
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04915.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04914.pow 1)))

@[irreducible]
def a04917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00317 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00865 ^ 1)
theorem ha04917 : a04917.IsHomogeneous 27 := by
  unfold a04917
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a04918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04917 ^ 1)
theorem ha04918 : a04918.IsHomogeneous 33 := by
  unfold a04918
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04914.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04917.pow 1)))

@[irreducible]
def a04919 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04916 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a04918 ^ 1)
theorem ha04919 : a04919.IsHomogeneous 39 := by
  unfold a04919
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04916.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha04918.pow 1)))

@[irreducible]
def a04920 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02425 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a04919 ^ 1)
theorem ha04920 : a04920.IsHomogeneous 45 := by
  unfold a04920
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02425.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha04919.pow 1)))

@[irreducible]
def a04921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a04912 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04920 ^ 1)
theorem ha04921 : a04921.IsHomogeneous 45 := by
  unfold a04921
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha04912.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04920.pow 1)))

@[irreducible]
def a04922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04913 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a04921 ^ 1)
theorem ha04922 : a04922.IsHomogeneous 45 := by
  unfold a04922
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04913.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha04921.pow 1)))

@[irreducible]
def a04923 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00133 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00324 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00133 ^ 1)
theorem ha04923 : a04923.IsHomogeneous 18 := by
  unfold a04923
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a04924 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1)
theorem ha04924 : a04924.IsHomogeneous 18 := by
  unfold a04924
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a04925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00032 ^ 1)
theorem ha04925 : a04925.IsHomogeneous 12 := by
  unfold a04925
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)))

@[irreducible]
def a04926 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04924 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a04923 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a04925 ^ 1)
theorem ha04926 : a04926.IsHomogeneous 24 := by
  unfold a04926
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04924.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha04923.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha04925.pow 1)))

@[irreducible]
def a04927 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00133 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00324 ^ 1)
theorem ha04927 : a04927.IsHomogeneous 18 := by
  unfold a04927
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a04928 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1)
theorem ha04928 : a04928.IsHomogeneous 18 := by
  unfold a04928
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)))

@[irreducible]
def a04929 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04927 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a04923 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a04928 ^ 1)
theorem ha04929 : a04929.IsHomogeneous 24 := by
  unfold a04929
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04927.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha04923.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha04928.pow 1)))

@[irreducible]
def a04930 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00133 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00032 ^ 1 * a00864 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00130 ^ 1 * a00316 ^ 1)
theorem ha04930 : a04930.IsHomogeneous 24 := by
  unfold a04930
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a04931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04924 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a04927 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a04930 ^ 1)
theorem ha04931 : a04931.IsHomogeneous 24 := by
  unfold a04931
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04924.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha04927.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha04930.pow 1)))

@[irreducible]
def a04932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04926 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a04929 ^ 1)
theorem ha04932 : a04932.IsHomogeneous 30 := by
  unfold a04932
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04931.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04926.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha04929.pow 1)))

@[irreducible]
def a04933 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a04932 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04922 ^ 1)
theorem ha04933 : a04933.IsHomogeneous 45 := by
  unfold a04933
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha04932.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04922.pow 1)))

@[irreducible]
def a04934 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00100 ^ 1 * a04933 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02432 ^ 1)
theorem ha04934 : a04934.IsHomogeneous 81 := by
  unfold a04934
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00100.pow 1)).mul (ha04933.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02432.pow 1)))

@[irreducible]
def a04935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a04934 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04910 ^ 1)
theorem ha04935 : a04935.IsHomogeneous 117 := by
  unfold a04935
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha04934.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04910.pow 1)))

@[irreducible]
def a04936 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00829 ^ 1 * a01048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00370 ^ 1 * a01938 ^ 1)
theorem ha04936 : a04936.IsHomogeneous 117 := by
  unfold a04936
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00829.pow 1)).mul (ha01048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00370.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a04937 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a04936 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04910 ^ 1)
theorem ha04937 : a04937.IsHomogeneous 117 := by
  unfold a04937
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha04936.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04910.pow 1)))

@[irreducible]
def a04938 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04937 ^ 1)
theorem ha04938 : a04938.IsHomogeneous 117 := by
  unfold a04938
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04935.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04937.pow 1)))

@[irreducible]
def a04939 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00484 ^ 1 * a01223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00459 ^ 1 * a01275 ^ 1)
theorem ha04939 : a04939.IsHomogeneous 142 := by
  unfold a04939
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00484.pow 1)).mul (ha01223.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00459.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a04940 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a02744 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a01223 ^ 1)
theorem ha04940 : a04940.IsHomogeneous 136 := by
  unfold a04940
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha02744.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha01223.pow 1)))

@[irreducible]
def a04941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04940 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04939 ^ 1)
theorem ha04941 : a04941.IsHomogeneous 142 := by
  unfold a04941
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04940.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04939.pow 1)))

@[irreducible]
def a04942 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00459 ^ 1 * a01275 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a02837 ^ 1)
theorem ha04942 : a04942.IsHomogeneous 149 := by
  unfold a04942
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha01275.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha02837.pow 1)))

@[irreducible]
def a04943 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a04939 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04942 ^ 1)
theorem ha04943 : a04943.IsHomogeneous 149 := by
  unfold a04943
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha04939.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04942.pow 1)))

@[irreducible]
def a04944 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a04941 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04943 ^ 1)
theorem ha04944 : a04944.IsHomogeneous 149 := by
  unfold a04944
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha04941.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04943.pow 1)))

@[irreducible]
def a04945 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a04938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04944 ^ 1)
theorem ha04945 : a04945.IsHomogeneous 149 := by
  unfold a04945
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha04938.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04944.pow 1)))

@[irreducible]
def a04946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01081 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a02496 ^ 1)
theorem ha04946 : a04946.IsHomogeneous 138 := by
  unfold a04946
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01081.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha02496.pow 1)))

@[irreducible]
def a04947 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00388 ^ 1 * a01841 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01081 ^ 1)
theorem ha04947 : a04947.IsHomogeneous 138 := by
  unfold a04947
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00388.pow 1)).mul (ha01841.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01081.pow 1)))

@[irreducible]
def a04948 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04946 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04947 ^ 1)
theorem ha04948 : a04948.IsHomogeneous 138 := by
  unfold a04948
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04946.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04947.pow 1)))

@[irreducible]
def a04949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00819 ^ 1 * a01052 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00301 ^ 1 * a02441 ^ 1)
theorem ha04949 : a04949.IsHomogeneous 119 := by
  unfold a04949
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00819.pow 1)).mul (ha01052.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a04950 : Poly := (C ((-14 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a01847 ^ 1)
theorem ha04950 : a04950.IsHomogeneous 13 := by
  unfold a04950
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-14 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01847.pow 1)))

@[irreducible]
def a04951 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a04950 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a02441 ^ 1)
theorem ha04951 : a04951.IsHomogeneous 113 := by
  unfold a04951
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha04950.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a04952 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04949 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a04951 ^ 1)
theorem ha04952 : a04952.IsHomogeneous 119 := by
  unfold a04952
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha04951.pow 1)))

@[irreducible]
def a04953 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00819 ^ 1 * a01052 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00009 ^ 1 * a00372 ^ 1 * a01917 ^ 1)
theorem ha04953 : a04953.IsHomogeneous 125 := by
  unfold a04953
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00819.pow 1)).mul (ha01052.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a04954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04953 ^ 1)
theorem ha04954 : a04954.IsHomogeneous 125 := by
  unfold a04954
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04949.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04953.pow 1)))

@[irreducible]
def a04955 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04952 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04954 ^ 1)
theorem ha04955 : a04955.IsHomogeneous 125 := by
  unfold a04955
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04952.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04954.pow 1)))

@[irreducible]
def a04956 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00476 ^ 1 * a01228 ^ 1)
theorem ha04956 : a04956.IsHomogeneous 124 := by
  unfold a04956
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha01258.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00476.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a04957 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00146 ^ 1 * a02754 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00476 ^ 1 * a01228 ^ 1)
theorem ha04957 : a04957.IsHomogeneous 118 := by
  unfold a04957
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha02754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00476.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a04958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04957 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04956 ^ 1)
theorem ha04958 : a04958.IsHomogeneous 124 := by
  unfold a04958
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04957.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04956.pow 1)))

@[irreducible]
def a04959 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00461 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a02806 ^ 1)
theorem ha04959 : a04959.IsHomogeneous 125 := by
  unfold a04959
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00461.pow 1)).mul (ha01258.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha02806.pow 1)))

@[irreducible]
def a04960 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04959 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a04956 ^ 1)
theorem ha04960 : a04960.IsHomogeneous 125 := by
  unfold a04960
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04959.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha04956.pow 1)))

@[irreducible]
def a04961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04960 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a04958 ^ 1)
theorem ha04961 : a04961.IsHomogeneous 125 := by
  unfold a04961
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04960.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha04958.pow 1)))

@[irreducible]
def a04962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04955 ^ 1) + (C ((125 : ℂ) / (18 : ℂ)) * a04961 ^ 1)
theorem ha04962 : a04962.IsHomogeneous 125 := by
  unfold a04962
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04955.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((125 : ℂ) / (18 : ℂ))).mul (ha04961.pow 1)))

@[irreducible]
def a04963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a02493 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00812 ^ 1 * a01079 ^ 1)
theorem ha04963 : a04963.IsHomogeneous 123 := by
  unfold a04963
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha02493.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00812.pow 1)).mul (ha01079.pow 1)))

@[irreducible]
def a04964 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00387 ^ 1 * a01903 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a01079 ^ 1)
theorem ha04964 : a04964.IsHomogeneous 117 := by
  unfold a04964
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00387.pow 1)).mul (ha01903.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha01079.pow 1)))

@[irreducible]
def a04965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04963 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a04964 ^ 1)
theorem ha04965 : a04965.IsHomogeneous 123 := by
  unfold a04965
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha04964.pow 1)))

@[irreducible]
def a04966 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02461 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00712 ^ 1 * a01060 ^ 1)
theorem ha04966 : a04966.IsHomogeneous 89 := by
  unfold a04966
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02461.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00712.pow 1)).mul (ha01060.pow 1)))

@[irreducible]
def a04967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00375 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00712 ^ 1 * a01060 ^ 1)
theorem ha04967 : a04967.IsHomogeneous 88 := by
  unfold a04967
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00375.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00712.pow 1)).mul (ha01060.pow 1)))

@[irreducible]
def a04968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a04967 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04966 ^ 1)
theorem ha04968 : a04968.IsHomogeneous 89 := by
  unfold a04968
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha04967.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04966.pow 1)))

@[irreducible]
def a04969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01041 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a02413 ^ 1)
theorem ha04969 : a04969.IsHomogeneous 39 := by
  unfold a04969
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a04970 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00368 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01041 ^ 1)
theorem ha04970 : a04970.IsHomogeneous 33 := by
  unfold a04970
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a04971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04969 ^ 1)
theorem ha04971 : a04971.IsHomogeneous 39 := by
  unfold a04971
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04970.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04969.pow 1)))

@[irreducible]
def a04972 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a02413 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00042 ^ 1 * a04894 ^ 1)
theorem ha04972 : a04972.IsHomogeneous 42 := by
  unfold a04972
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00042.pow 1)).mul (ha04894.pow 1)))

@[irreducible]
def a04973 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04969 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a04972 ^ 1)
theorem ha04973 : a04973.IsHomogeneous 42 := by
  unfold a04973
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04969.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha04972.pow 1)))

@[irreducible]
def a04974 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04971 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04973 ^ 1)
theorem ha04974 : a04974.IsHomogeneous 42 := by
  unfold a04974
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04971.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04973.pow 1)))

@[irreducible]
def a04975 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00455 ^ 1)
theorem ha04975 : a04975.IsHomogeneous 18 := by
  unfold a04975
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a04976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00864 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00316 ^ 1 * a00455 ^ 1)
theorem ha04976 : a04976.IsHomogeneous 18 := by
  unfold a04976
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00316.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a04977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04975 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a04976 ^ 1)
theorem ha04977 : a04977.IsHomogeneous 18 := by
  unfold a04977
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04975.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha04976.pow 1)))

@[irreducible]
def a04978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02710 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01207 ^ 1)
theorem ha04978 : a04978.IsHomogeneous 18 := by
  unfold a04978
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02710.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1)))

@[irreducible]
def a04979 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04975 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a04978 ^ 1)
theorem ha04979 : a04979.IsHomogeneous 18 := by
  unfold a04979
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04975.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha04978.pow 1)))

@[irreducible]
def a04980 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04977 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04979 ^ 1)
theorem ha04980 : a04980.IsHomogeneous 18 := by
  unfold a04980
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04977.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04979.pow 1)))

@[irreducible]
def a04981 : Poly := (C ((-8 : ℂ) / (81 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a04974 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a04980 ^ 1)
theorem ha04981 : a04981.IsHomogeneous 47 := by
  unfold a04981
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (81 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha04974.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha04980.pow 1)))

@[irreducible]
def a04982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00506 ^ 1)
theorem ha04982 : a04982.IsHomogeneous 42 := by
  unfold a04982
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a04983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00155 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00506 ^ 1)
theorem ha04983 : a04983.IsHomogeneous 42 := by
  unfold a04983
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a04984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04982 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a04983 ^ 1)
theorem ha04984 : a04984.IsHomogeneous 42 := by
  unfold a04984
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04982.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha04983.pow 1)))

@[irreducible]
def a04985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01896 ^ 1)
theorem ha04985 : a04985.IsHomogeneous 33 := by
  unfold a04985
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a04986 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04985 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04983 ^ 1)
theorem ha04986 : a04986.IsHomogeneous 42 := by
  unfold a04986
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04985.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04983.pow 1)))

@[irreducible]
def a04987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04984 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a04986 ^ 1)
theorem ha04987 : a04987.IsHomogeneous 42 := by
  unfold a04987
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04984.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha04986.pow 1)))

@[irreducible]
def a04988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04981 ^ 1) + (C ((8 : ℂ) / (1215 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a04987 ^ 1)
theorem ha04988 : a04988.IsHomogeneous 47 := by
  unfold a04988
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04981.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1215 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha04987.pow 1)))

@[irreducible]
def a04989 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a04988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02461 ^ 1)
theorem ha04989 : a04989.IsHomogeneous 89 := by
  unfold a04989
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha04988.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02461.pow 1)))

@[irreducible]
def a04990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04966 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04989 ^ 1)
theorem ha04990 : a04990.IsHomogeneous 89 := by
  unfold a04990
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04966.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04989.pow 1)))

@[irreducible]
def a04991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04968 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04990 ^ 1)
theorem ha04991 : a04991.IsHomogeneous 89 := by
  unfold a04991
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04968.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04990.pow 1)))

@[irreducible]
def a04992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00465 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00241 ^ 1 * a01240 ^ 1)
theorem ha04992 : a04992.IsHomogeneous 89 := by
  unfold a04992
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00465.pow 1)).mul (ha00691.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00241.pow 1)).mul (ha01240.pow 1)))

@[irreducible]
def a04993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00139 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00465 ^ 1 * a00691 ^ 1)
theorem ha04993 : a04993.IsHomogeneous 89 := by
  unfold a04993
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00139.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00465.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a04994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04992 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04993 ^ 1)
theorem ha04994 : a04994.IsHomogeneous 89 := by
  unfold a04994
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04992.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04993.pow 1)))

@[irreducible]
def a04995 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01240 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02778 ^ 1)
theorem ha04995 : a04995.IsHomogeneous 88 := by
  unfold a04995
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01240.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02778.pow 1)))

@[irreducible]
def a04996 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a04995 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04992 ^ 1)
theorem ha04996 : a04996.IsHomogeneous 89 := by
  unfold a04996
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha04995.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04992.pow 1)))

@[irreducible]
def a04997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04994 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04996 ^ 1)
theorem ha04997 : a04997.IsHomogeneous 89 := by
  unfold a04997
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04994.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04996.pow 1)))

@[irreducible]
def a04998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04991 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a04997 ^ 1)
theorem ha04998 : a04998.IsHomogeneous 89 := by
  unfold a04998
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04991.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha04997.pow 1)))

@[irreducible]
def a04999 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00300 ^ 1 * a00637 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00211 ^ 1 * a00817 ^ 1)
theorem ha04999 : a04999.IsHomogeneous 106 := by
  unfold a04999
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1)).mul (ha00637.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00211.pow 1)).mul (ha00817.pow 1)))

@[irreducible]
def a05000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00300 ^ 1 * a00637 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a01581 ^ 1)
theorem ha05000 : a05000.IsHomogeneous 112 := by
  unfold a05000
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00300.pow 1)).mul (ha00637.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a05001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04999 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05000 ^ 1)
theorem ha05001 : a05001.IsHomogeneous 112 := by
  unfold a05001
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04999.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05000.pow 1)))

@[irreducible]
def a05002 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00061 ^ 1 * a01914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00817 ^ 1)
theorem ha05002 : a05002.IsHomogeneous 99 := by
  unfold a05002
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00061.pow 1)).mul (ha01914.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00817.pow 1)))

@[irreducible]
def a05003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04999 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a05002 ^ 1)
theorem ha05003 : a05003.IsHomogeneous 106 := by
  unfold a05003
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04999.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha05002.pow 1)))

@[irreducible]
def a05004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05003 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05001 ^ 1)
theorem ha05004 : a05004.IsHomogeneous 112 := by
  unfold a05004
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05003.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05001.pow 1)))

@[irreducible]
def a05005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05004 ^ 1) + (C ((1 : ℂ) / (128 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a04998 ^ 1)
theorem ha05005 : a05005.IsHomogeneous 112 := by
  unfold a05005
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05004.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (128 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha04998.pow 1)))

@[irreducible]
def a05006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02474 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00712 ^ 1 * a01067 ^ 1)
theorem ha05006 : a05006.IsHomogeneous 89 := by
  unfold a05006
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02474.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00712.pow 1)).mul (ha01067.pow 1)))

@[irreducible]
def a05007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00379 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00712 ^ 1 * a01067 ^ 1)
theorem ha05007 : a05007.IsHomogeneous 88 := by
  unfold a05007
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00379.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00712.pow 1)).mul (ha01067.pow 1)))

@[irreducible]
def a05008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05006 ^ 1)
theorem ha05008 : a05008.IsHomogeneous 89 := by
  unfold a05008
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05007.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05006.pow 1)))

@[irreducible]
def a05009 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a04974 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a04980 ^ 1)
theorem ha05009 : a05009.IsHomogeneous 47 := by
  unfold a05009
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha04974.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha04980.pow 1)))

@[irreducible]
def a05010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05009 ^ 1) + (C ((1 : ℂ) / (405 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a04987 ^ 1)
theorem ha05010 : a05010.IsHomogeneous 47 := by
  unfold a05010
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05009.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (405 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha04987.pow 1)))

@[irreducible]
def a05011 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a05010 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02474 ^ 1)
theorem ha05011 : a05011.IsHomogeneous 89 := by
  unfold a05011
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha05010.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02474.pow 1)))

@[irreducible]
def a05012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05011 ^ 1)
theorem ha05012 : a05012.IsHomogeneous 89 := by
  unfold a05012
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05011.pow 1)))

@[irreducible]
def a05013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05012 ^ 1)
theorem ha05013 : a05013.IsHomogeneous 89 := by
  unfold a05013
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05008.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05012.pow 1)))

@[irreducible]
def a05014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00469 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00241 ^ 1 * a01248 ^ 1)
theorem ha05014 : a05014.IsHomogeneous 89 := by
  unfold a05014
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00469.pow 1)).mul (ha00691.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00241.pow 1)).mul (ha01248.pow 1)))

@[irreducible]
def a05015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00141 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00469 ^ 1 * a00691 ^ 1)
theorem ha05015 : a05015.IsHomogeneous 89 := by
  unfold a05015
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00141.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00469.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a05016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05015 ^ 1)
theorem ha05016 : a05016.IsHomogeneous 89 := by
  unfold a05016
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05015.pow 1)))

@[irreducible]
def a05017 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02792 ^ 1)
theorem ha05017 : a05017.IsHomogeneous 88 := by
  unfold a05017
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02792.pow 1)))

@[irreducible]
def a05018 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05017 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05014 ^ 1)
theorem ha05018 : a05018.IsHomogeneous 89 := by
  unfold a05018
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05017.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05014.pow 1)))

@[irreducible]
def a05019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05016 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05018 ^ 1)
theorem ha05019 : a05019.IsHomogeneous 89 := by
  unfold a05019
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05016.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05018.pow 1)))

@[irreducible]
def a05020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05013 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a05019 ^ 1)
theorem ha05020 : a05020.IsHomogeneous 89 := by
  unfold a05020
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05013.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha05019.pow 1)))

@[irreducible]
def a05021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05004 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a05020 ^ 1)
theorem ha05021 : a05021.IsHomogeneous 112 := by
  unfold a05021
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05004.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha05020.pow 1)))

@[irreducible]
def a05022 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a05021 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05005 ^ 1)
theorem ha05022 : a05022.IsHomogeneous 112 := by
  unfold a05022
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha05021.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05005.pow 1)))

@[irreducible]
def a05023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02484 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00712 ^ 1 * a01074 ^ 1)
theorem ha05023 : a05023.IsHomogeneous 89 := by
  unfold a05023
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02484.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00712.pow 1)).mul (ha01074.pow 1)))

@[irreducible]
def a05024 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a04974 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a04980 ^ 1)
theorem ha05024 : a05024.IsHomogeneous 47 := by
  unfold a05024
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha04974.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha04980.pow 1)))

@[irreducible]
def a05025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05024 ^ 1) + (C ((2 : ℂ) / (405 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a04987 ^ 1)
theorem ha05025 : a05025.IsHomogeneous 47 := by
  unfold a05025
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05024.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (405 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha04987.pow 1)))

@[irreducible]
def a05026 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a05025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02484 ^ 1)
theorem ha05026 : a05026.IsHomogeneous 89 := by
  unfold a05026
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha05025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02484.pow 1)))

@[irreducible]
def a05027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05023 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05026 ^ 1)
theorem ha05027 : a05027.IsHomogeneous 89 := by
  unfold a05027
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05023.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05026.pow 1)))

@[irreducible]
def a05028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00384 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00712 ^ 1 * a01074 ^ 1)
theorem ha05028 : a05028.IsHomogeneous 88 := by
  unfold a05028
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00384.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00712.pow 1)).mul (ha01074.pow 1)))

@[irreducible]
def a05029 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05028 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05023 ^ 1)
theorem ha05029 : a05029.IsHomogeneous 89 := by
  unfold a05029
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05028.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05023.pow 1)))

@[irreducible]
def a05030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05027 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05029 ^ 1)
theorem ha05030 : a05030.IsHomogeneous 89 := by
  unfold a05030
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05027.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05029.pow 1)))

@[irreducible]
def a05031 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00473 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00241 ^ 1 * a01253 ^ 1)
theorem ha05031 : a05031.IsHomogeneous 89 := by
  unfold a05031
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00473.pow 1)).mul (ha00691.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00241.pow 1)).mul (ha01253.pow 1)))

@[irreducible]
def a05032 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a01253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02799 ^ 1)
theorem ha05032 : a05032.IsHomogeneous 88 := by
  unfold a05032
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha01253.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02799.pow 1)))

@[irreducible]
def a05033 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05031 ^ 1)
theorem ha05033 : a05033.IsHomogeneous 89 := by
  unfold a05033
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05031.pow 1)))

@[irreducible]
def a05034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00144 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00473 ^ 1 * a00691 ^ 1)
theorem ha05034 : a05034.IsHomogeneous 89 := by
  unfold a05034
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00144.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00473.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a05035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05031 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05034 ^ 1)
theorem ha05035 : a05035.IsHomogeneous 89 := by
  unfold a05035
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05031.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05034.pow 1)))

@[irreducible]
def a05036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05033 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05035 ^ 1)
theorem ha05036 : a05036.IsHomogeneous 89 := by
  unfold a05036
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05033.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05035.pow 1)))

@[irreducible]
def a05037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05030 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a05036 ^ 1)
theorem ha05037 : a05037.IsHomogeneous 89 := by
  unfold a05037
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05030.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha05036.pow 1)))

@[irreducible]
def a05038 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05004 ^ 1) + (C ((5 : ℂ) / (288 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a05037 ^ 1)
theorem ha05038 : a05038.IsHomogeneous 112 := by
  unfold a05038
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05004.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (288 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha05037.pow 1)))

@[irreducible]
def a05039 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a05038 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05022 ^ 1)
theorem ha05039 : a05039.IsHomogeneous 112 := by
  unfold a05039
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha05038.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05022.pow 1)))

@[irreducible]
def a05040 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a05039 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00299 ^ 1 * a02493 ^ 1)
theorem ha05040 : a05040.IsHomogeneous 130 := by
  unfold a05040
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha05039.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha02493.pow 1)))

@[irreducible]
def a05041 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05040 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a04963 ^ 1)
theorem ha05041 : a05041.IsHomogeneous 130 := by
  unfold a05041
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05040.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha04963.pow 1)))

@[irreducible]
def a05042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05041 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a04965 ^ 1)
theorem ha05042 : a05042.IsHomogeneous 130 := by
  unfold a05042
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05041.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha04965.pow 1)))

@[irreducible]
def a05043 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a05042 ^ 1) + (C ((1 : ℂ) / (200 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a04962 ^ 1)
theorem ha05043 : a05043.IsHomogeneous 136 := by
  unfold a05043
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha05042.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (200 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha04962.pow 1)))

@[irreducible]
def a05044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05043 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a02496 ^ 1)
theorem ha05044 : a05044.IsHomogeneous 142 := by
  unfold a05044
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05043.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha02496.pow 1)))

@[irreducible]
def a05045 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05044 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00003 ^ 4 * a04946 ^ 1)
theorem ha05045 : a05045.IsHomogeneous 142 := by
  unfold a05045
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05044.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00003.pow 4)).mul (ha04946.pow 1)))

@[irreducible]
def a05046 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05045 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a00003 ^ 4 * a04948 ^ 1)
theorem ha05046 : a05046.IsHomogeneous 142 := by
  unfold a05046
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05045.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha00003.pow 4)).mul (ha04948.pow 1)))

@[irreducible]
def a05047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 3 * a05046 ^ 1) + (C ((1 : ℂ) / (640 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a04945 ^ 1)
theorem ha05047 : a05047.IsHomogeneous 160 := by
  unfold a05047
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 3)).mul (ha05046.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (640 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha04945.pow 1)))

@[irreducible]
def a05048 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a02499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00126 ^ 1 * a05047 ^ 1)
theorem ha05048 : a05048.IsHomogeneous 192 := by
  unfold a05048
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha02499.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00126.pow 1)).mul (ha05047.pow 1)))

@[irreducible]
def a05049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05048 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a04907 ^ 1)
theorem ha05049 : a05049.IsHomogeneous 192 := by
  unfold a05049
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha04907.pow 1)))

@[irreducible]
def a05050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05049 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a04909 ^ 1)
theorem ha05050 : a05050.IsHomogeneous 192 := by
  unfold a05050
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05049.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha04909.pow 1)))

@[irreducible]
def a05051 : Poly := (C ((-5 : ℂ) / (432 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a04906 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05050 ^ 1)
theorem ha05051 : a05051.IsHomogeneous 192 := by
  unfold a05051
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (432 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha04906.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05050.pow 1)))

@[irreducible]
def a05052 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00492 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00489 ^ 1 * a01290 ^ 1)
theorem ha05052 : a05052.IsHomogeneous 404 := by
  unfold a05052
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00492.pow 1)).mul (ha01284.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00489.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a05053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00492 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a02851 ^ 1)
theorem ha05053 : a05053.IsHomogeneous 380 := by
  unfold a05053
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00492.pow 1)).mul (ha01284.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha02851.pow 1)))

@[irreducible]
def a05054 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a05053 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05052 ^ 1)
theorem ha05054 : a05054.IsHomogeneous 404 := by
  unfold a05054
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha05053.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05052.pow 1)))

@[irreducible]
def a05055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a02860 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a01290 ^ 1)
theorem ha05055 : a05055.IsHomogeneous 428 := by
  unfold a05055
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha02860.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a05056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05055 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a05052 ^ 1)
theorem ha05056 : a05056.IsHomogeneous 428 := by
  unfold a05056
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05055.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha05052.pow 1)))

@[irreducible]
def a05057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05056 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a05054 ^ 1)
theorem ha05057 : a05057.IsHomogeneous 428 := by
  unfold a05057
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05056.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha05054.pow 1)))

@[irreducible]
def a05058 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a02533 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00836 ^ 1 * a01099 ^ 1)
theorem ha05058 : a05058.IsHomogeneous 367 := by
  unfold a05058
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha02533.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00836.pow 1)).mul (ha01099.pow 1)))

@[irreducible]
def a05059 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00100 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00506 ^ 1)
theorem ha05059 : a05059.IsHomogeneous 54 := by
  unfold a05059
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a05060 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00831 ^ 1)
theorem ha05060 : a05060.IsHomogeneous 90 := by
  unfold a05060
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00831.pow 1)))

@[irreducible]
def a05061 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a05059 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05060 ^ 1)
theorem ha05061 : a05061.IsHomogeneous 90 := by
  unfold a05061
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha05059.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05060.pow 1)))

@[irreducible]
def a05062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00155 ^ 1 * a00831 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a01941 ^ 1)
theorem ha05062 : a05062.IsHomogeneous 126 := by
  unfold a05062
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00155.pow 1)).mul (ha00831.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha01941.pow 1)))

@[irreducible]
def a05063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a05060 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05062 ^ 1)
theorem ha05063 : a05063.IsHomogeneous 126 := by
  unfold a05063
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha05060.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05062.pow 1)))

@[irreducible]
def a05064 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a05061 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05063 ^ 1)
theorem ha05064 : a05064.IsHomogeneous 126 := by
  unfold a05064
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha05061.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05063.pow 1)))

@[irreducible]
def a05065 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a01281 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00316 ^ 1 * a00487 ^ 1)
theorem ha05065 : a05065.IsHomogeneous 127 := by
  unfold a05065
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha01281.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00316.pow 1)).mul (ha00487.pow 1)))

@[irreducible]
def a05066 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00487 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a00864 ^ 1)
theorem ha05066 : a05066.IsHomogeneous 91 := by
  unfold a05066
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00487.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05067 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a05065 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a05066 ^ 1)
theorem ha05067 : a05067.IsHomogeneous 127 := by
  unfold a05067
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha05065.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha05066.pow 1)))

@[irreducible]
def a05068 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a02847 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01281 ^ 1)
theorem ha05068 : a05068.IsHomogeneous 133 := by
  unfold a05068
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha02847.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01281.pow 1)))

@[irreducible]
def a05069 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a05068 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05065 ^ 1)
theorem ha05069 : a05069.IsHomogeneous 133 := by
  unfold a05069
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha05068.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05065.pow 1)))

@[irreducible]
def a05070 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a05069 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05067 ^ 1)
theorem ha05070 : a05070.IsHomogeneous 133 := by
  unfold a05070
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha05069.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05067.pow 1)))

@[irreducible]
def a05071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05070 ^ 1) + (C ((6 : ℂ) / (25 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a05064 ^ 1)
theorem ha05071 : a05071.IsHomogeneous 133 := by
  unfold a05071
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05070.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (25 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha05064.pow 1)))

@[irreducible]
def a05072 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01097 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a02530 ^ 1)
theorem ha05072 : a05072.IsHomogeneous 160 := by
  unfold a05072
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01097.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha02530.pow 1)))

@[irreducible]
def a05073 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00395 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01097 ^ 1)
theorem ha05073 : a05073.IsHomogeneous 154 := by
  unfold a05073
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00395.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01097.pow 1)))

@[irreducible]
def a05074 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a05073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05072 ^ 1)
theorem ha05074 : a05074.IsHomogeneous 160 := by
  unfold a05074
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha05073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05072.pow 1)))

@[irreducible]
def a05075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a01092 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00260 ^ 1 * a02520 ^ 1)
theorem ha05075 : a05075.IsHomogeneous 145 := by
  unfold a05075
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00260.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a05076 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a00712 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a01702 ^ 1)
theorem ha05076 : a05076.IsHomogeneous 142 := by
  unfold a05076
  exact ((((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha00712.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a05077 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a05075 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a05076 ^ 1)
theorem ha05077 : a05077.IsHomogeneous 145 := by
  unfold a05077
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha05075.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha05076.pow 1)))

@[irreducible]
def a05078 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00211 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00637 ^ 1)
theorem ha05078 : a05078.IsHomogeneous 94 := by
  unfold a05078
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00211.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a05079 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01581 ^ 1)
theorem ha05079 : a05079.IsHomogeneous 94 := by
  unfold a05079
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a05080 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a05079 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05078 ^ 1)
theorem ha05080 : a05080.IsHomogeneous 94 := by
  unfold a05080
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha05079.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05078.pow 1)))

@[irreducible]
def a05081 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a01702 ^ 1)
theorem ha05081 : a05081.IsHomogeneous 93 := by
  unfold a05081
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a05082 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a05081 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05078 ^ 1)
theorem ha05082 : a05082.IsHomogeneous 94 := by
  unfold a05082
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha05081.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05078.pow 1)))

@[irreducible]
def a05083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05080 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05082 ^ 1)
theorem ha05083 : a05083.IsHomogeneous 94 := by
  unfold a05083
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05080.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05082.pow 1)))

@[irreducible]
def a05084 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00691 ^ 1)
theorem ha05084 : a05084.IsHomogeneous 102 := by
  unfold a05084
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a05085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00691 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05084 ^ 1)
theorem ha05085 : a05085.IsHomogeneous 102 := by
  unfold a05085
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00691.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05084.pow 1)))

@[irreducible]
def a05086 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a05085 ^ 1) + (C ((216 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a05083 ^ 1)
theorem ha05086 : a05086.IsHomogeneous 107 := by
  unfold a05086
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha05085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((216 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha05083.pow 1)))

@[irreducible]
def a05087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05086 ^ 1) + (C ((216 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a05083 ^ 1)
theorem ha05087 : a05087.IsHomogeneous 107 := by
  unfold a05087
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((216 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha05083.pow 1)))

@[irreducible]
def a05088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a05087 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a02520 ^ 1)
theorem ha05088 : a05088.IsHomogeneous 145 := by
  unfold a05088
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha05087.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a05089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05075 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a05088 ^ 1)
theorem ha05089 : a05089.IsHomogeneous 145 := by
  unfold a05089
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05075.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha05088.pow 1)))

@[irreducible]
def a05090 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a05089 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05077 ^ 1)
theorem ha05090 : a05090.IsHomogeneous 145 := by
  unfold a05090
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha05089.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05077.pow 1)))

@[irreducible]
def a05091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00484 ^ 1 * a00691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a01275 ^ 1)
theorem ha05091 : a05091.IsHomogeneous 140 := by
  unfold a05091
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00484.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a05092 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a00691 ^ 1)
theorem ha05092 : a05092.IsHomogeneous 138 := by
  unfold a05092
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a05093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a05092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05091 ^ 1)
theorem ha05093 : a05093.IsHomogeneous 140 := by
  unfold a05093
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha05092.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05091.pow 1)))

@[irreducible]
def a05094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a01275 ^ 1)
theorem ha05094 : a05094.IsHomogeneous 140 := by
  unfold a05094
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a05095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05091 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05094 ^ 1)
theorem ha05095 : a05095.IsHomogeneous 140 := by
  unfold a05095
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05091.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05094.pow 1)))

@[irreducible]
def a05096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05093 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05095 ^ 1)
theorem ha05096 : a05096.IsHomogeneous 140 := by
  unfold a05096
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05093.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05095.pow 1)))

@[irreducible]
def a05097 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a05096 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05090 ^ 1)
theorem ha05097 : a05097.IsHomogeneous 145 := by
  unfold a05097
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha05096.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05090.pow 1)))

@[irreducible]
def a05098 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00260 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00829 ^ 1)
theorem ha05098 : a05098.IsHomogeneous 132 := by
  unfold a05098
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a05099 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a01581 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00637 ^ 1)
theorem ha05099 : a05099.IsHomogeneous 94 := by
  unfold a05099
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha01581.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a05100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a05099 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05098 ^ 1)
theorem ha05100 : a05100.IsHomogeneous 132 := by
  unfold a05100
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha05099.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05098.pow 1)))

@[irreducible]
def a05101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00061 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00211 ^ 1 * a00829 ^ 1)
theorem ha05101 : a05101.IsHomogeneous 132 := by
  unfold a05101
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00061.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00211.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a05102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05098 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a05101 ^ 1)
theorem ha05102 : a05102.IsHomogeneous 132 := by
  unfold a05102
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05098.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha05101.pow 1)))

@[irreducible]
def a05103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05102 ^ 1)
theorem ha05103 : a05103.IsHomogeneous 132 := by
  unfold a05103
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05100.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05102.pow 1)))

@[irreducible]
def a05104 : Poly := (C ((-1728 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a05103 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05097 ^ 1)
theorem ha05104 : a05104.IsHomogeneous 145 := by
  unfold a05104
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1728 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha05103.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05097.pow 1)))

@[irreducible]
def a05105 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00042 ^ 1 * a05104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a02530 ^ 1)
theorem ha05105 : a05105.IsHomogeneous 169 := by
  unfold a05105
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00042.pow 1)).mul (ha05104.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha02530.pow 1)))

@[irreducible]
def a05106 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a05072 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05105 ^ 1)
theorem ha05106 : a05106.IsHomogeneous 169 := by
  unfold a05106
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha05072.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05105.pow 1)))

@[irreducible]
def a05107 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a05074 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05106 ^ 1)
theorem ha05107 : a05107.IsHomogeneous 169 := by
  unfold a05107
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha05074.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05106.pow 1)))

@[irreducible]
def a05108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05107 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a05071 ^ 1)
theorem ha05108 : a05108.IsHomogeneous 169 := by
  unfold a05108
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05107.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha05071.pow 1)))

@[irreducible]
def a05109 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a05108 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a02533 ^ 1)
theorem ha05109 : a05109.IsHomogeneous 277 := by
  unfold a05109
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha05108.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha02533.pow 1)))

@[irreducible]
def a05110 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a05109 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05058 ^ 1)
theorem ha05110 : a05110.IsHomogeneous 367 := by
  unfold a05110
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha05109.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05058.pow 1)))

@[irreducible]
def a05111 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00836 ^ 1 * a01099 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00396 ^ 1 * a01949 ^ 1)
theorem ha05111 : a05111.IsHomogeneous 391 := by
  unfold a05111
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00836.pow 1)).mul (ha01099.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00396.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a05112 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a05058 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05111 ^ 1)
theorem ha05112 : a05112.IsHomogeneous 391 := by
  unfold a05112
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha05058.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05111.pow 1)))

@[irreducible]
def a05113 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a05110 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05112 ^ 1)
theorem ha05113 : a05113.IsHomogeneous 391 := by
  unfold a05113
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha05110.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05112.pow 1)))

@[irreducible]
def a05114 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a05057 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a05113 ^ 1)
theorem ha05114 : a05114.IsHomogeneous 433 := by
  unfold a05114
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha05057.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha05113.pow 1)))

@[irreducible]
def a05115 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00001 ^ 1 * a00042 ^ 4 * a00100 ^ 4 * a05051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05114 ^ 1)
theorem ha05115 : a05115.IsHomogeneous 433 := by
  unfold a05115
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00001.pow 1)).mul (ha00042.pow 4)).mul (ha00100.pow 4)).mul (ha05051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05114.pow 1)))

@[irreducible]
def a05116 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a02538 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a05115 ^ 1)
theorem ha05116 : a05116.IsHomogeneous 433 := by
  unfold a05116
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha02538.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha05115.pow 1)))

@[irreducible]
def a05117 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04885 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05116 ^ 1)
theorem ha05117 : a05117.IsHomogeneous 433 := by
  unfold a05117
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04885.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05116.pow 1)))

@[irreducible]
def a05118 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04887 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05117 ^ 1)
theorem ha05118 : a05118.IsHomogeneous 433 := by
  unfold a05118
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04887.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05117.pow 1)))

@[irreducible]
def a05119 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a02540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a05118 ^ 1)
theorem ha05119 : a05119.IsHomogeneous 859 := by
  unfold a05119
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha02540.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha05118.pow 1)))

end CycleQ2Concrete
