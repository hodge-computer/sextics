import Proposal.CurrentAtoms007

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a03840 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03839 ^ 1)
theorem ha03840 : a03840.IsHomogeneous 388 := by
  unfold a03840
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03839.pow 1)))

@[irreducible]
def a03841 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00124 ^ 1 * a03840 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00290 ^ 1 * a01863 ^ 1)
theorem ha03841 : a03841.IsHomogeneous 509 := by
  unfold a03841
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha03840.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00290.pow 1)).mul (ha01863.pow 1)))

@[irreducible]
def a03842 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a03787 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a03841 ^ 1)
theorem ha03842 : a03842.IsHomogeneous 570 := by
  unfold a03842
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha03787.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha03841.pow 1)))

@[irreducible]
def a03843 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03842 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a03788 ^ 1)
theorem ha03843 : a03843.IsHomogeneous 576 := by
  unfold a03843
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03842.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha03788.pow 1)))

@[irreducible]
def a03844 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03843 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a03826 ^ 1)
theorem ha03844 : a03844.IsHomogeneous 582 := by
  unfold a03844
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03843.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha03826.pow 1)))

@[irreducible]
def a03845 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a01866 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a03844 ^ 1)
theorem ha03845 : a03845.IsHomogeneous 697 := by
  unfold a03845
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha01866.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha03844.pow 1)))

@[irreducible]
def a03846 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03779 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a03845 ^ 1)
theorem ha03846 : a03846.IsHomogeneous 812 := by
  unfold a03846
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03779.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha03845.pow 1)))

@[irreducible]
def a03847 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00124 ^ 1 * a03846 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03785 ^ 1)
theorem ha03847 : a03847.IsHomogeneous 872 := by
  unfold a03847
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00124.pow 1)).mul (ha03846.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03785.pow 1)))

@[irreducible]
def a03848 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00287 ^ 1 * a01868 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00117 ^ 1 * a03847 ^ 1)
theorem ha03848 : a03848.IsHomogeneous 938 := by
  unfold a03848
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00287.pow 1)).mul (ha01868.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00117.pow 1)).mul (ha03847.pow 1)))

@[irreducible]
def a03849 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a03577 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a03848 ^ 1)
theorem ha03849 : a03849.IsHomogeneous 980 := by
  unfold a03849
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha03577.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha03848.pow 1)))

@[irreducible]
def a03850 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a03578 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a03849 ^ 1)
theorem ha03850 : a03850.IsHomogeneous 1022 := by
  unfold a03850
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha03578.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha03849.pow 1)))

@[irreducible]
def a03851 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a03778 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a03850 ^ 1)
theorem ha03851 : a03851.IsHomogeneous 1064 := by
  unfold a03851
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha03778.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha03850.pow 1)))

@[irreducible]
def a03852 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00294 ^ 1 * a01871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00125 ^ 1 * a03851 ^ 1)
theorem ha03852 : a03852.IsHomogeneous 1169 := by
  unfold a03852
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00294.pow 1)).mul (ha01871.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00125.pow 1)).mul (ha03851.pow 1)))

@[irreducible]
def a03853 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03573 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03852 ^ 1)
theorem ha03853 : a03853.IsHomogeneous 1169 := by
  unfold a03853
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03573.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03852.pow 1)))

@[irreducible]
def a03854 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03853 ^ 1)
theorem ha03854 : a03854.IsHomogeneous 1169 := by
  unfold a03854
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03575.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03853.pow 1)))

@[irreducible]
def a03855 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a01702 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00712 ^ 1 * a00798 ^ 1)
theorem ha03855 : a03855.IsHomogeneous 126 := by
  unfold a03855
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00712.pow 1)).mul (ha00798.pow 1)))

@[irreducible]
def a03856 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00712 ^ 1 * a00798 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a01877 ^ 1)
theorem ha03856 : a03856.IsHomogeneous 127 := by
  unfold a03856
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00712.pow 1)).mul (ha00798.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha01877.pow 1)))

@[irreducible]
def a03857 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03855 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a03856 ^ 1)
theorem ha03857 : a03857.IsHomogeneous 127 := by
  unfold a03857
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03855.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha03856.pow 1)))

@[irreducible]
def a03858 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a01702 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00125 ^ 1 * a03562 ^ 1)
theorem ha03858 : a03858.IsHomogeneous 126 := by
  unfold a03858
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00125.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a03859 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03855 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03858 ^ 1)
theorem ha03859 : a03859.IsHomogeneous 126 := by
  unfold a03859
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03855.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03858.pow 1)))

@[irreducible]
def a03860 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a03859 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03857 ^ 1)
theorem ha03860 : a03860.IsHomogeneous 127 := by
  unfold a03860
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha03859.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03857.pow 1)))

@[irreducible]
def a03861 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00001 ^ 1 * a00003 ^ 1 * a00005 ^ 1 * a00012 ^ 3 * a03250 ^ 1) + (C ((-1 : ℂ) / (48 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 2 * a03370 ^ 1) + (C ((-1 : ℂ) / (6912 : ℂ)) * a00000 ^ 1 * a00001 ^ 14 * a00002 ^ 3 * a00004 ^ 5 * a00005 ^ 4 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 4 * a00012 ^ 4 * a00014 ^ 1 * a03121 ^ 1) + (C ((1 : ℂ) / (384 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 1 * a03534 ^ 1)
theorem ha03861 : a03861.IsHomogeneous 78 := by
  unfold a03861
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha03250.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (48 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha03370.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6912 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 14)).mul (ha00002.pow 3)).mul (ha00004.pow 5)).mul (ha00005.pow 4)).mul (ha03562.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 4)).mul (ha00012.pow 4)).mul (ha00014.pow 1)).mul (ha03121.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (384 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a03862 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a01877 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a03861 ^ 1)
theorem ha03862 : a03862.IsHomogeneous 121 := by
  unfold a03862
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha01877.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03861.pow 1)))

@[irreducible]
def a03863 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a03862 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03856 ^ 1)
theorem ha03863 : a03863.IsHomogeneous 127 := by
  unfold a03863
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha03862.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03856.pow 1)))

@[irreducible]
def a03864 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03857 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a03863 ^ 1)
theorem ha03864 : a03864.IsHomogeneous 127 := by
  unfold a03864
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03857.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha03863.pow 1)))

@[irreducible]
def a03865 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03860 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03864 ^ 1)
theorem ha03865 : a03865.IsHomogeneous 127 := by
  unfold a03865
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03860.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03864.pow 1)))

@[irreducible]
def a03866 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a01880 ^ 1)
theorem ha03866 : a03866.IsHomogeneous 406 := by
  unfold a03866
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha01880.pow 1)))

@[irreducible]
def a03867 : Poly := (C ((-5 : ℂ) / (72 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03866 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03574 ^ 1)
theorem ha03867 : a03867.IsHomogeneous 661 := by
  unfold a03867
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03866.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03574.pow 1)))

@[irreducible]
def a03868 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03575 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03867 ^ 1)
theorem ha03868 : a03868.IsHomogeneous 915 := by
  unfold a03868
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03575.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03867.pow 1)))

@[irreducible]
def a03869 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03854 ^ 1)
theorem ha03869 : a03869.IsHomogeneous 1169 := by
  unfold a03869
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03868.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03854.pow 1)))

@[irreducible]
def a03870 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a01883 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a03869 ^ 1)
theorem ha03870 : a03870.IsHomogeneous 1248 := by
  unfold a03870
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha01883.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha03869.pow 1)))

@[irreducible]
def a03871 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02916 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a03870 ^ 1)
theorem ha03871 : a03871.IsHomogeneous 1327 := by
  unfold a03871
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02916.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha03870.pow 1)))

@[irreducible]
def a03872 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a03871 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02917 ^ 1)
theorem ha03872 : a03872.IsHomogeneous 1406 := by
  unfold a03872
  exact ((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha03871.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02917.pow 1)))

@[irreducible]
def a03873 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03572 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a03872 ^ 1)
theorem ha03873 : a03873.IsHomogeneous 1485 := by
  unfold a03873
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03572.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha03872.pow 1)))

@[irreducible]
def a03874 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a01886 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a03873 ^ 1)
theorem ha03874 : a03874.IsHomogeneous 1593 := by
  unfold a03874
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha01886.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha03873.pow 1)))

@[irreducible]
def a03875 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02912 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a03874 ^ 1)
theorem ha03875 : a03875.IsHomogeneous 1683 := by
  unfold a03875
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02912.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha03874.pow 1)))

@[irreducible]
def a03876 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a03875 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02914 ^ 1)
theorem ha03876 : a03876.IsHomogeneous 1743 := by
  unfold a03876
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha03875.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02914.pow 1)))

@[irreducible]
def a03877 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00305 ^ 1 * a01926 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00825 ^ 1 * a00834 ^ 1)
theorem ha03877 : a03877.IsHomogeneous 282 := by
  unfold a03877
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00305.pow 1)).mul (ha01926.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00825.pow 1)).mul (ha00834.pow 1)))

@[irreducible]
def a03878 : Poly := (C ((-5 : ℂ) / (81 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00825 ^ 1 * a00834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00304 ^ 1 * a01946 ^ 1)
theorem ha03878 : a03878.IsHomogeneous 342 := by
  unfold a03878
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (81 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00825.pow 1)).mul (ha00834.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00304.pow 1)).mul (ha01946.pow 1)))

@[irreducible]
def a03879 : Poly := (C ((-5 : ℂ) / (81 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a03877 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03878 ^ 1)
theorem ha03879 : a03879.IsHomogeneous 342 := by
  unfold a03879
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (81 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha03877.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03878.pow 1)))

@[irreducible]
def a03880 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00303 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a00823 ^ 1)
theorem ha03880 : a03880.IsHomogeneous 147 := by
  unfold a03880
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00303.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha00823.pow 1)))

@[irreducible]
def a03881 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00809 ^ 1 * a00823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a01923 ^ 1)
theorem ha03881 : a03881.IsHomogeneous 153 := by
  unfold a03881
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha00823.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha01923.pow 1)))

@[irreducible]
def a03882 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a03880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03881 ^ 1)
theorem ha03882 : a03882.IsHomogeneous 153 := by
  unfold a03882
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha03880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03881.pow 1)))

@[irreducible]
def a03883 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00317 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00865 ^ 1)
theorem ha03883 : a03883.IsHomogeneous 27 := by
  unfold a03883
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03884 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01545 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03883 ^ 1)
theorem ha03884 : a03884.IsHomogeneous 27 := by
  unfold a03884
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01545.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03883.pow 1)))

@[irreducible]
def a03885 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01546 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03884 ^ 1)
theorem ha03885 : a03885.IsHomogeneous 27 := by
  unfold a03885
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01546.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03884.pow 1)))

@[irreducible]
def a03886 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a02008 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00865 ^ 1)
theorem ha03886 : a03886.IsHomogeneous 27 := by
  unfold a03886
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03887 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03883 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a03886 ^ 1)
theorem ha03887 : a03887.IsHomogeneous 27 := by
  unfold a03887
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03883.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha03886.pow 1)))

@[irreducible]
def a03888 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03884 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03887 ^ 1)
theorem ha03888 : a03888.IsHomogeneous 27 := by
  unfold a03888
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03887.pow 1)))

@[irreducible]
def a03889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03885 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03888 ^ 1)
theorem ha03889 : a03889.IsHomogeneous 27 := by
  unfold a03889
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03885.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03888.pow 1)))

@[irreducible]
def a03890 : Poly := (C ((-1 : ℂ) / (45 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03417 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03889 ^ 1)
theorem ha03890 : a03890.IsHomogeneous 27 := by
  unfold a03890
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (45 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03889.pow 1)))

@[irreducible]
def a03891 : Poly := (C ((-7 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a03890 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a01896 ^ 1)
theorem ha03891 : a03891.IsHomogeneous 141 := by
  unfold a03891
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha03890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a03892 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03891 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03880 ^ 1)
theorem ha03892 : a03892.IsHomogeneous 147 := by
  unfold a03892
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03880.pow 1)))

@[irreducible]
def a03893 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a03892 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03882 ^ 1)
theorem ha03893 : a03893.IsHomogeneous 153 := by
  unfold a03893
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha03892.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03882.pow 1)))

@[irreducible]
def a03894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00821 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00302 ^ 1 * a01841 ^ 1)
theorem ha03894 : a03894.IsHomogeneous 126 := by
  unfold a03894
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00821.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00302.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a03895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00821 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a01920 ^ 1)
theorem ha03895 : a03895.IsHomogeneous 126 := by
  unfold a03895
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00821.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha01920.pow 1)))

@[irreducible]
def a03896 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03894 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03895 ^ 1)
theorem ha03896 : a03896.IsHomogeneous 126 := by
  unfold a03896
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03894.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03895.pow 1)))

@[irreducible]
def a03897 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00302 ^ 1 * a01841 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a03803 ^ 1)
theorem ha03897 : a03897.IsHomogeneous 126 := by
  unfold a03897
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00302.pow 1)).mul (ha01841.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha03803.pow 1)))

@[irreducible]
def a03898 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a03897 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03894 ^ 1)
theorem ha03898 : a03898.IsHomogeneous 126 := by
  unfold a03898
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha03897.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03894.pow 1)))

@[irreducible]
def a03899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03898 ^ 1)
theorem ha03899 : a03899.IsHomogeneous 126 := by
  unfold a03899
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03896.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03898.pow 1)))

@[irreducible]
def a03900 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a00819 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00301 ^ 1 * a01903 ^ 1)
theorem ha03900 : a03900.IsHomogeneous 117 := by
  unfold a03900
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha00819.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a03901 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00812 ^ 1 * a00819 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a01917 ^ 1)
theorem ha03901 : a03901.IsHomogeneous 123 := by
  unfold a03901
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00812.pow 1)).mul (ha00819.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a03902 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03900 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03901 ^ 1)
theorem ha03902 : a03902.IsHomogeneous 123 := by
  unfold a03902
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03900.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03901.pow 1)))

@[irreducible]
def a03903 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a03811 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a01903 ^ 1)
theorem ha03903 : a03903.IsHomogeneous 111 := by
  unfold a03903
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha03811.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a03904 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03900 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a03903 ^ 1)
theorem ha03904 : a03904.IsHomogeneous 117 := by
  unfold a03904
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03900.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha03903.pow 1)))

@[irreducible]
def a03905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03904 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03902 ^ 1)
theorem ha03905 : a03905.IsHomogeneous 123 := by
  unfold a03905
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03904.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03902.pow 1)))

@[irreducible]
def a03906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00712 ^ 1 * a00817 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00300 ^ 1 * a01702 ^ 1)
theorem ha03906 : a03906.IsHomogeneous 105 := by
  unfold a03906
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00712.pow 1)).mul (ha00817.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00300.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a03907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a00817 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a01914 ^ 1)
theorem ha03907 : a03907.IsHomogeneous 99 := by
  unfold a03907
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha00817.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha01914.pow 1)))

@[irreducible]
def a03908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03907 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03906 ^ 1)
theorem ha03908 : a03908.IsHomogeneous 105 := by
  unfold a03908
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03907.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03906.pow 1)))

@[irreducible]
def a03909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a03562 ^ 1) + (C ((81 : ℂ) / (4 : ℂ)) * a00300 ^ 1 * a01702 ^ 1)
theorem ha03909 : a03909.IsHomogeneous 105 := by
  unfold a03909
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha03562.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (4 : ℂ))).mul (ha00300.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a03910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03906 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a03909 ^ 1)
theorem ha03910 : a03910.IsHomogeneous 105 := by
  unfold a03910
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03906.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha03909.pow 1)))

@[irreducible]
def a03911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03908 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03910 ^ 1)
theorem ha03911 : a03911.IsHomogeneous 105 := by
  unfold a03911
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03908.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03910.pow 1)))

@[irreducible]
def a03912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00317 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00298 ^ 1 * a00865 ^ 1)
theorem ha03912 : a03912.IsHomogeneous 51 := by
  unfold a03912
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00317.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00298.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03913 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00809 ^ 1)
theorem ha03913 : a03913.IsHomogeneous 48 := by
  unfold a03913
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a03914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03913 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03912 ^ 1)
theorem ha03914 : a03914.IsHomogeneous 51 := by
  unfold a03914
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03913.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03912.pow 1)))

@[irreducible]
def a03915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00865 ^ 1)
theorem ha03915 : a03915.IsHomogeneous 51 := by
  unfold a03915
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03912 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a03915 ^ 1)
theorem ha03916 : a03916.IsHomogeneous 51 := by
  unfold a03916
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03912.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha03915.pow 1)))

@[irreducible]
def a03917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03916 ^ 1)
theorem ha03917 : a03917.IsHomogeneous 51 := by
  unfold a03917
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03914.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03916.pow 1)))

@[irreducible]
def a03918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a01896 ^ 1) + (C ((7 : ℂ) / (81 : ℂ)) * a00042 ^ 1 * a03890 ^ 1)
theorem ha03918 : a03918.IsHomogeneous 51 := by
  unfold a03918
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (81 : ℂ))).mul (ha00042.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a03919 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03913 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03918 ^ 1)
theorem ha03919 : a03919.IsHomogeneous 51 := by
  unfold a03919
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03913.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03918.pow 1)))

@[irreducible]
def a03920 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03919 ^ 1)
theorem ha03920 : a03920.IsHomogeneous 51 := by
  unfold a03920
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03914.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03919.pow 1)))

@[irreducible]
def a03921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03917 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03920 ^ 1)
theorem ha03921 : a03921.IsHomogeneous 51 := by
  unfold a03921
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03917.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03920.pow 1)))

@[irreducible]
def a03922 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a03921 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01914 ^ 1)
theorem ha03922 : a03922.IsHomogeneous 93 := by
  unfold a03922
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03921.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01914.pow 1)))

@[irreducible]
def a03923 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03922 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03907 ^ 1)
theorem ha03923 : a03923.IsHomogeneous 99 := by
  unfold a03923
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03922.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03907.pow 1)))

@[irreducible]
def a03924 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03923 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03908 ^ 1)
theorem ha03924 : a03924.IsHomogeneous 105 := by
  unfold a03924
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03923.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03908.pow 1)))

@[irreducible]
def a03925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03911 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03924 ^ 1)
theorem ha03925 : a03925.IsHomogeneous 105 := by
  unfold a03925
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03911.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03924.pow 1)))

@[irreducible]
def a03926 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a03925 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a01917 ^ 1)
theorem ha03926 : a03926.IsHomogeneous 123 := by
  unfold a03926
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha03925.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha01917.pow 1)))

@[irreducible]
def a03927 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03901 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a03926 ^ 1)
theorem ha03927 : a03927.IsHomogeneous 123 := by
  unfold a03927
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03901.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha03926.pow 1)))

@[irreducible]
def a03928 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03902 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03927 ^ 1)
theorem ha03928 : a03928.IsHomogeneous 123 := by
  unfold a03928
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03902.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03927.pow 1)))

@[irreducible]
def a03929 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03905 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03928 ^ 1)
theorem ha03929 : a03929.IsHomogeneous 123 := by
  unfold a03929
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03905.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03928.pow 1)))

@[irreducible]
def a03930 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03929 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01920 ^ 1)
theorem ha03930 : a03930.IsHomogeneous 129 := by
  unfold a03930
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03929.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01920.pow 1)))

@[irreducible]
def a03931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03930 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03895 ^ 1)
theorem ha03931 : a03931.IsHomogeneous 129 := by
  unfold a03931
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03930.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03895.pow 1)))

@[irreducible]
def a03932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03931 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03896 ^ 1)
theorem ha03932 : a03932.IsHomogeneous 129 := by
  unfold a03932
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03931.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03896.pow 1)))

@[irreducible]
def a03933 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03932 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03899 ^ 1)
theorem ha03933 : a03933.IsHomogeneous 129 := by
  unfold a03933
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03932.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03899.pow 1)))

@[irreducible]
def a03934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a03933 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a01923 ^ 1)
theorem ha03934 : a03934.IsHomogeneous 159 := by
  unfold a03934
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha03933.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha01923.pow 1)))

@[irreducible]
def a03935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03934 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03881 ^ 1)
theorem ha03935 : a03935.IsHomogeneous 159 := by
  unfold a03935
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03934.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03881.pow 1)))

@[irreducible]
def a03936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03935 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03882 ^ 1)
theorem ha03936 : a03936.IsHomogeneous 159 := by
  unfold a03936
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03882.pow 1)))

@[irreducible]
def a03937 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03936 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03893 ^ 1)
theorem ha03937 : a03937.IsHomogeneous 159 := by
  unfold a03937
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03936.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03893.pow 1)))

@[irreducible]
def a03938 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a01926 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a03937 ^ 1)
theorem ha03938 : a03938.IsHomogeneous 222 := by
  unfold a03938
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha01926.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha03937.pow 1)))

@[irreducible]
def a03939 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a03938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03877 ^ 1)
theorem ha03939 : a03939.IsHomogeneous 282 := by
  unfold a03939
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha03938.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03877.pow 1)))

@[irreducible]
def a03940 : Poly := (C ((-5 : ℂ) / (81 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a03939 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03879 ^ 1)
theorem ha03940 : a03940.IsHomogeneous 342 := by
  unfold a03940
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (81 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha03939.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03879.pow 1)))

@[irreducible]
def a03941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00833 ^ 1 * a01929 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00305 ^ 1 * a01944 ^ 1)
theorem ha03941 : a03941.IsHomogeneous 240 := by
  unfold a03941
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00833.pow 1)).mul (ha01929.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00305.pow 1)).mul (ha01944.pow 1)))

@[irreducible]
def a03942 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a01944 ^ 1)
theorem ha03942 : a03942.IsHomogeneous 174 := by
  unfold a03942
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha00833.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha01944.pow 1)))

@[irreducible]
def a03943 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 2)
theorem ha03943 : a03943.IsHomogeneous 132 := by
  unfold a03943
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 2)))

@[irreducible]
def a03944 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03943 ^ 1)
theorem ha03944 : a03944.IsHomogeneous 132 := by
  unfold a03944
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03943.pow 1)))

@[irreducible]
def a03945 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a03942 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a03944 ^ 1)
theorem ha03945 : a03945.IsHomogeneous 198 := by
  unfold a03945
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha03942.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha03944.pow 1)))

@[irreducible]
def a03946 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00833 ^ 1 * a01929 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a03945 ^ 1)
theorem ha03946 : a03946.IsHomogeneous 264 := by
  unfold a03946
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).mul (ha01929.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha03945.pow 1)))

@[irreducible]
def a03947 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a03941 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03946 ^ 1)
theorem ha03947 : a03947.IsHomogeneous 264 := by
  unfold a03947
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha03941.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03946.pow 1)))

@[irreducible]
def a03948 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00831 ^ 1)
theorem ha03948 : a03948.IsHomogeneous 105 := by
  unfold a03948
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00831.pow 1)))

@[irreducible]
def a03949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01941 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00317 ^ 1 * a00831 ^ 1)
theorem ha03949 : a03949.IsHomogeneous 147 := by
  unfold a03949
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01941.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00317.pow 1)).mul (ha00831.pow 1)))

@[irreducible]
def a03950 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03949 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a03948 ^ 1)
theorem ha03950 : a03950.IsHomogeneous 147 := by
  unfold a03950
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03949.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03948.pow 1)))

@[irreducible]
def a03951 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a02008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00865 ^ 1)
theorem ha03951 : a03951.IsHomogeneous 63 := by
  unfold a03951
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03952 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a03951 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03948 ^ 1)
theorem ha03952 : a03952.IsHomogeneous 105 := by
  unfold a03952
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03951.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03948.pow 1)))

@[irreducible]
def a03953 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03950 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a03952 ^ 1)
theorem ha03953 : a03953.IsHomogeneous 147 := by
  unfold a03953
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03950.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03952.pow 1)))

@[irreducible]
def a03954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00712 ^ 1 * a00829 ^ 1)
theorem ha03954 : a03954.IsHomogeneous 129 := by
  unfold a03954
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00712.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a03955 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00712 ^ 1 * a00829 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01938 ^ 1)
theorem ha03955 : a03955.IsHomogeneous 129 := by
  unfold a03955
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00712.pow 1)).mul (ha00829.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a03956 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a03955 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03954 ^ 1)
theorem ha03956 : a03956.IsHomogeneous 129 := by
  unfold a03956
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha03955.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03954.pow 1)))

@[irreducible]
def a03957 : Poly := (C ((-2 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01702 ^ 1)
theorem ha03957 : a03957.IsHomogeneous 93 := by
  unfold a03957
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03562.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a03958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a03957 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03954 ^ 1)
theorem ha03958 : a03958.IsHomogeneous 129 := by
  unfold a03958
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha03957.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03954.pow 1)))

@[irreducible]
def a03959 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03956 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03958 ^ 1)
theorem ha03959 : a03959.IsHomogeneous 129 := by
  unfold a03959
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03956.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03958.pow 1)))

@[irreducible]
def a03960 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01702 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00712 ^ 2)
theorem ha03960 : a03960.IsHomogeneous 93 := by
  unfold a03960
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01702.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 2)))

@[irreducible]
def a03961 : Poly := (C ((-4 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01702 ^ 1)
theorem ha03961 : a03961.IsHomogeneous 93 := by
  unfold a03961
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03562.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a03962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03960 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03961 ^ 1)
theorem ha03962 : a03962.IsHomogeneous 93 := by
  unfold a03962
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03960.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03961.pow 1)))

@[irreducible]
def a03963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03960 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03962 ^ 1)
theorem ha03963 : a03963.IsHomogeneous 93 := by
  unfold a03963
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03960.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03962.pow 1)))

@[irreducible]
def a03964 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a03963 ^ 1)
theorem ha03964 : a03964.IsHomogeneous 129 := by
  unfold a03964
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a03965 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a03964 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03955 ^ 1)
theorem ha03965 : a03965.IsHomogeneous 129 := by
  unfold a03965
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha03964.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03955.pow 1)))

@[irreducible]
def a03966 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a03965 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03956 ^ 1)
theorem ha03966 : a03966.IsHomogeneous 129 := by
  unfold a03966
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha03965.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03956.pow 1)))

@[irreducible]
def a03967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03959 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03966 ^ 1)
theorem ha03967 : a03967.IsHomogeneous 129 := by
  unfold a03967
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03959.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03966.pow 1)))

@[irreducible]
def a03968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a03967 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a01941 ^ 1)
theorem ha03968 : a03968.IsHomogeneous 153 := by
  unfold a03968
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha03967.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01941.pow 1)))

@[irreducible]
def a03969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03968 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03949 ^ 1)
theorem ha03969 : a03969.IsHomogeneous 153 := by
  unfold a03969
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03968.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03949.pow 1)))

@[irreducible]
def a03970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03969 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03950 ^ 1)
theorem ha03970 : a03970.IsHomogeneous 153 := by
  unfold a03970
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03969.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03950.pow 1)))

@[irreducible]
def a03971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03970 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03953 ^ 1)
theorem ha03971 : a03971.IsHomogeneous 153 := by
  unfold a03971
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03953.pow 1)))

@[irreducible]
def a03972 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a01944 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a03971 ^ 1)
theorem ha03972 : a03972.IsHomogeneous 216 := by
  unfold a03972
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha01944.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha03971.pow 1)))

@[irreducible]
def a03973 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03941 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a03972 ^ 1)
theorem ha03973 : a03973.IsHomogeneous 240 := by
  unfold a03973
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03941.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha03972.pow 1)))

@[irreducible]
def a03974 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a03973 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03947 ^ 1)
theorem ha03974 : a03974.IsHomogeneous 264 := by
  unfold a03974
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha03973.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03947.pow 1)))

@[irreducible]
def a03975 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a03974 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00304 ^ 1 * a01946 ^ 1)
theorem ha03975 : a03975.IsHomogeneous 312 := by
  unfold a03975
  exact (((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha03974.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00304.pow 1)).mul (ha01946.pow 1)))

@[irreducible]
def a03976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a03975 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03878 ^ 1)
theorem ha03976 : a03976.IsHomogeneous 342 := by
  unfold a03976
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha03975.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03878.pow 1)))

@[irreducible]
def a03977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03879 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03976 ^ 1)
theorem ha03977 : a03977.IsHomogeneous 342 := by
  unfold a03977
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03879.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03976.pow 1)))

@[irreducible]
def a03978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03940 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03977 ^ 1)
theorem ha03978 : a03978.IsHomogeneous 342 := by
  unfold a03978
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03940.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03977.pow 1)))

@[irreducible]
def a03979 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a01949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a03978 ^ 1)
theorem ha03979 : a03979.IsHomogeneous 768 := by
  unfold a03979
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha01949.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha03978.pow 1)))

@[irreducible]
def a03980 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a02913 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03979 ^ 1)
theorem ha03980 : a03980.IsHomogeneous 1101 := by
  unfold a03980
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha02913.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03979.pow 1)))

@[irreducible]
def a03981 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a02914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03980 ^ 1)
theorem ha03981 : a03981.IsHomogeneous 1434 := by
  unfold a03981
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha02914.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03980.pow 1)))

@[irreducible]
def a03982 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a03876 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03981 ^ 1)
theorem ha03982 : a03982.IsHomogeneous 1767 := by
  unfold a03982
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha03876.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03981.pow 1)))

@[irreducible]
def a03983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a00850 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a01886 ^ 1)
theorem ha03983 : a03983.IsHomogeneous 1302 := by
  unfold a03983
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha00850.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a03984 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00804 ^ 1 * a00850 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a01979 ^ 1)
theorem ha03984 : a03984.IsHomogeneous 1005 := by
  unfold a03984
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha00850.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a03985 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a03983 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03984 ^ 1)
theorem ha03985 : a03985.IsHomogeneous 1338 := by
  unfold a03985
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha03983.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03984.pow 1)))

@[irreducible]
def a03986 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a01886 ^ 1)
theorem ha03986 : a03986.IsHomogeneous 1569 := by
  unfold a03986
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a03987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03983 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a03986 ^ 1)
theorem ha03987 : a03987.IsHomogeneous 1635 := by
  unfold a03987
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03983.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha03986.pow 1)))

@[irreducible]
def a03988 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a03987 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03985 ^ 1)
theorem ha03988 : a03988.IsHomogeneous 1671 := by
  unfold a03988
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha03987.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03985.pow 1)))

@[irreducible]
def a03989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00846 ^ 1 * a00848 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00260 ^ 1 * a01970 ^ 1)
theorem ha03989 : a03989.IsHomogeneous 174 := by
  unfold a03989
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00846.pow 1)).mul (ha00848.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01970.pow 1)))

@[irreducible]
def a03990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00309 ^ 1 * a01976 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a00846 ^ 1 * a00848 ^ 1)
theorem ha03990 : a03990.IsHomogeneous 210 := by
  unfold a03990
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00309.pow 1)).mul (ha01976.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha00846.pow 1)).mul (ha00848.pow 1)))

@[irreducible]
def a03991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03990 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a03989 ^ 1)
theorem ha03991 : a03991.IsHomogeneous 210 := by
  unfold a03991
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03990.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha03989.pow 1)))

@[irreducible]
def a03992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00308 ^ 1 * a01841 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00843 ^ 1)
theorem ha03992 : a03992.IsHomogeneous 90 := by
  unfold a03992
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00308.pow 1)).mul (ha01841.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00843.pow 1)))

@[irreducible]
def a03993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01965 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00843 ^ 1)
theorem ha03993 : a03993.IsHomogeneous 84 := by
  unfold a03993
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01965.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00843.pow 1)))

@[irreducible]
def a03994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03992 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03993 ^ 1)
theorem ha03994 : a03994.IsHomogeneous 90 := by
  unfold a03994
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03992.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03993.pow 1)))

@[irreducible]
def a03995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00298 ^ 1 * a01903 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a00841 ^ 1)
theorem ha03995 : a03995.IsHomogeneous 75 := by
  unfold a03995
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha01903.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha00841.pow 1)))

@[irreducible]
def a03996 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a00841 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a01962 ^ 1)
theorem ha03996 : a03996.IsHomogeneous 75 := by
  unfold a03996
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha00841.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha01962.pow 1)))

@[irreducible]
def a03997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03995 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03996 ^ 1)
theorem ha03997 : a03997.IsHomogeneous 75 := by
  unfold a03997
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03995.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03996.pow 1)))

@[irreducible]
def a03998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a01903 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00126 ^ 1 * a03811 ^ 1)
theorem ha03998 : a03998.IsHomogeneous 45 := by
  unfold a03998
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha01903.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00126.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a03999 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a03998 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03995 ^ 1)
theorem ha03999 : a03999.IsHomogeneous 75 := by
  unfold a03999
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha03998.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03995.pow 1)))

@[irreducible]
def a04000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03997 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03999 ^ 1)
theorem ha04000 : a04000.IsHomogeneous 75 := by
  unfold a04000
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03997.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03999.pow 1)))

@[irreducible]
def a04001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a01896 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00809 ^ 2)
theorem ha04001 : a04001.IsHomogeneous 57 := by
  unfold a04001
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00809.pow 2)))

@[irreducible]
def a04002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a03890 ^ 1) + (C ((81 : ℂ) / (7 : ℂ)) * a00298 ^ 1 * a01896 ^ 1)
theorem ha04002 : a04002.IsHomogeneous 57 := by
  unfold a04002
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha03890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (7 : ℂ))).mul (ha00298.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a04003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04001 ^ 1) + (C ((7 : ℂ) / (81 : ℂ)) * a04002 ^ 1)
theorem ha04003 : a04003.IsHomogeneous 57 := by
  unfold a04003
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (81 : ℂ))).mul (ha04002.pow 1)))

@[irreducible]
def a04004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04001 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04003 ^ 1)
theorem ha04004 : a04004.IsHomogeneous 57 := by
  unfold a04004
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04003.pow 1)))

@[irreducible]
def a04005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a04004 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00299 ^ 1 * a01962 ^ 1)
theorem ha04005 : a04005.IsHomogeneous 75 := by
  unfold a04005
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha04004.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00299.pow 1)).mul (ha01962.pow 1)))

@[irreducible]
def a04006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03996 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a04005 ^ 1)
theorem ha04006 : a04006.IsHomogeneous 75 := by
  unfold a04006
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03996.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha04005.pow 1)))

@[irreducible]
def a04007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03997 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a04006 ^ 1)
theorem ha04007 : a04007.IsHomogeneous 75 := by
  unfold a04007
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03997.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha04006.pow 1)))

@[irreducible]
def a04008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04000 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04007 ^ 1)
theorem ha04008 : a04008.IsHomogeneous 75 := by
  unfold a04008
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04000.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04007.pow 1)))

@[irreducible]
def a04009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04008 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01965 ^ 1)
theorem ha04009 : a04009.IsHomogeneous 81 := by
  unfold a04009
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01965.pow 1)))

@[irreducible]
def a04010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04009 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03993 ^ 1)
theorem ha04010 : a04010.IsHomogeneous 87 := by
  unfold a04010
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04009.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03993.pow 1)))

@[irreducible]
def a04011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04010 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03994 ^ 1)
theorem ha04011 : a04011.IsHomogeneous 93 := by
  unfold a04011
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04010.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03994.pow 1)))

@[irreducible]
def a04012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a03803 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00308 ^ 1 * a01841 ^ 1)
theorem ha04012 : a04012.IsHomogeneous 66 := by
  unfold a04012
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha03803.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00308.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a04013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a04012 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03992 ^ 1)
theorem ha04013 : a04013.IsHomogeneous 96 := by
  unfold a04013
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha04012.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03992.pow 1)))

@[irreducible]
def a04014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04013 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03994 ^ 1)
theorem ha04014 : a04014.IsHomogeneous 96 := by
  unfold a04014
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04013.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03994.pow 1)))

@[irreducible]
def a04015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04011 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a04014 ^ 1)
theorem ha04015 : a04015.IsHomogeneous 99 := by
  unfold a04015
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04011.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha04014.pow 1)))

@[irreducible]
def a04016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01970 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a04015 ^ 1)
theorem ha04016 : a04016.IsHomogeneous 135 := by
  unfold a04016
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha04015.pow 1)))

@[irreducible]
def a04017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03989 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a04016 ^ 1)
theorem ha04017 : a04017.IsHomogeneous 174 := by
  unfold a04017
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03989.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha04016.pow 1)))

@[irreducible]
def a04018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03991 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a04017 ^ 1)
theorem ha04018 : a04018.IsHomogeneous 210 := by
  unfold a04018
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03991.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha04017.pow 1)))

@[irreducible]
def a04019 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00260 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a01974 ^ 1)
theorem ha04019 : a04019.IsHomogeneous 168 := by
  unfold a04019
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha01974.pow 1)))

@[irreducible]
def a04020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01938 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a03963 ^ 1)
theorem ha04020 : a04020.IsHomogeneous 129 := by
  unfold a04020
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a04021 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a04020 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04019 ^ 1)
theorem ha04021 : a04021.IsHomogeneous 168 := by
  unfold a04021
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha04020.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04019.pow 1)))

@[irreducible]
def a04022 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00829 ^ 1)
theorem ha04022 : a04022.IsHomogeneous 126 := by
  unfold a04022
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a04023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (8 : ℂ)) * a00829 ^ 1)
theorem ha04023 : a04023.IsHomogeneous 84 := by
  unfold a04023
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00829.pow 1)))

@[irreducible]
def a04024 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a04023 ^ 1)
theorem ha04024 : a04024.IsHomogeneous 84 := by
  unfold a04024
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha04023.pow 1)))

@[irreducible]
def a04025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04024 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04022 ^ 1)
theorem ha04025 : a04025.IsHomogeneous 126 := by
  unfold a04025
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04024.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04022.pow 1)))

@[irreducible]
def a04026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a01974 ^ 1)
theorem ha04026 : a04026.IsHomogeneous 168 := by
  unfold a04026
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha01974.pow 1)))

@[irreducible]
def a04027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04019 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04026 ^ 1)
theorem ha04027 : a04027.IsHomogeneous 168 := by
  unfold a04027
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04019.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04026.pow 1)))

@[irreducible]
def a04028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04021 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04027 ^ 1)
theorem ha04028 : a04028.IsHomogeneous 168 := by
  unfold a04028
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04021.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04027.pow 1)))

@[irreducible]
def a04029 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a04028 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00309 ^ 1 * a01976 ^ 1)
theorem ha04029 : a04029.IsHomogeneous 216 := by
  unfold a04029
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04028.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00309.pow 1)).mul (ha01976.pow 1)))

@[irreducible]
def a04030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a04029 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a03990 ^ 1)
theorem ha04030 : a04030.IsHomogeneous 246 := by
  unfold a04030
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha04029.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha03990.pow 1)))

@[irreducible]
def a04031 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04030 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a03991 ^ 1)
theorem ha04031 : a04031.IsHomogeneous 246 := by
  unfold a04031
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04030.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha03991.pow 1)))

@[irreducible]
def a04032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04031 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04018 ^ 1)
theorem ha04032 : a04032.IsHomogeneous 246 := by
  unfold a04032
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04031.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04018.pow 1)))

@[irreducible]
def a04033 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a04032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a01979 ^ 1)
theorem ha04033 : a04033.IsHomogeneous 672 := by
  unfold a04033
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha04032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a04034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04033 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03984 ^ 1)
theorem ha04034 : a04034.IsHomogeneous 1005 := by
  unfold a04034
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04033.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03984.pow 1)))

@[irreducible]
def a04035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04034 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03985 ^ 1)
theorem ha04035 : a04035.IsHomogeneous 1338 := by
  unfold a04035
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04034.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03985.pow 1)))

@[irreducible]
def a04036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03988 ^ 1)
theorem ha04036 : a04036.IsHomogeneous 1671 := by
  unfold a04036
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04035.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03988.pow 1)))

@[irreducible]
def a04037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03982 ^ 1) + (C ((64 : ℂ) / (243 : ℂ)) * a00042 ^ 4 * a04036 ^ 1)
theorem ha04037 : a04037.IsHomogeneous 1767 := by
  unfold a04037
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03982.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (243 : ℂ))).mul (ha00042.pow 4)).mul (ha04036.pow 1)))

@[irreducible]
def a04038 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a01983 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a04037 ^ 1)
theorem ha04038 : a04038.IsHomogeneous 1827 := by
  unfold a04038
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha01983.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha04037.pow 1)))

@[irreducible]
def a04039 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02909 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a04038 ^ 1)
theorem ha04039 : a04039.IsHomogeneous 1887 := by
  unfold a04039
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02909.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha04038.pow 1)))

@[irreducible]
def a04040 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02911 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a04039 ^ 1)
theorem ha04040 : a04040.IsHomogeneous 1947 := by
  unfold a04040
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02911.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha04039.pow 1)))

@[irreducible]
def a04041 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00327 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00880 ^ 1 * a01986 ^ 1)
theorem ha04041 : a04041.IsHomogeneous 348 := by
  unfold a04041
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00327.pow 1)).mul (ha02041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00880.pow 1)).mul (ha01986.pow 1)))

@[irreducible]
def a04042 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a02041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a00880 ^ 1)
theorem ha04042 : a04042.IsHomogeneous 246 := by
  unfold a04042
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha02041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha00880.pow 1)))

@[irreducible]
def a04043 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00134 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 2)
theorem ha04043 : a04043.IsHomogeneous 204 := by
  unfold a04043
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 2)))

@[irreducible]
def a04044 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00134 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04043 ^ 1)
theorem ha04044 : a04044.IsHomogeneous 204 := by
  unfold a04044
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04043.pow 1)))

@[irreducible]
def a04045 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00134 ^ 1 * a04042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a04044 ^ 1)
theorem ha04045 : a04045.IsHomogeneous 306 := by
  unfold a04045
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00134.pow 1)).mul (ha04042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha04044.pow 1)))

@[irreducible]
def a04046 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00134 ^ 1 * a00880 ^ 1 * a01986 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a04045 ^ 1)
theorem ha04046 : a04046.IsHomogeneous 408 := by
  unfold a04046
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00134.pow 1)).mul (ha00880.pow 1)).mul (ha01986.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha04045.pow 1)))

@[irreducible]
def a04047 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00134 ^ 1 * a04041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04046 ^ 1)
theorem ha04047 : a04047.IsHomogeneous 408 := by
  unfold a04047
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00134.pow 1)).mul (ha04041.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04046.pow 1)))

@[irreducible]
def a04048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00876 ^ 1 * a00878 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a02032 ^ 1)
theorem ha04048 : a04048.IsHomogeneous 141 := by
  unfold a04048
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00876.pow 1)).mul (ha00878.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha02032.pow 1)))

@[irreducible]
def a04049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00326 ^ 1 * a02038 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00876 ^ 1 * a00878 ^ 1)
theorem ha04049 : a04049.IsHomogeneous 183 := by
  unfold a04049
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00326.pow 1)).mul (ha02038.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00876.pow 1)).mul (ha00878.pow 1)))

@[irreducible]
def a04050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04049 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a04048 ^ 1)
theorem ha04050 : a04050.IsHomogeneous 183 := by
  unfold a04050
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04049.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha04048.pow 1)))

@[irreducible]
def a04051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00298 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00298 ^ 1 * a00317 ^ 1)
theorem ha04051 : a04051.IsHomogeneous 51 := by
  unfold a04051
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a04052 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00865 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00298 ^ 1 * a00317 ^ 1)
theorem ha04052 : a04052.IsHomogeneous 51 := by
  unfold a04052
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a04053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00126 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00298 ^ 1)
theorem ha04053 : a04053.IsHomogeneous 51 := by
  unfold a04053
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00126.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a04054 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04051 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a04053 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a04052 ^ 1)
theorem ha04054 : a04054.IsHomogeneous 51 := by
  unfold a04054
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha04053.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha04052.pow 1)))

@[irreducible]
def a04055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00042 ^ 1 * a01896 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00809 ^ 1)
theorem ha04055 : a04055.IsHomogeneous 51 := by
  unfold a04055
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00042.pow 1)).mul (ha01896.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a04056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00298 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00809 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00298 ^ 1)
theorem ha04056 : a04056.IsHomogeneous 54 := by
  unfold a04056
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00809.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a04057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04056 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04055 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04051 ^ 1)
theorem ha04057 : a04057.IsHomogeneous 54 := by
  unfold a04057
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04056.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04055.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04051.pow 1)))

@[irreducible]
def a04058 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00129 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00298 ^ 1)
theorem ha04058 : a04058.IsHomogeneous 54 := by
  unfold a04058
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a04059 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04053 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04056 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a04058 ^ 1)
theorem ha04059 : a04059.IsHomogeneous 54 := by
  unfold a04059
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04053.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04056.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha04058.pow 1)))

@[irreducible]
def a04060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04057 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04059 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04054 ^ 1)
theorem ha04060 : a04060.IsHomogeneous 54 := by
  unfold a04060
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04057.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04059.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04054.pow 1)))

@[irreducible]
def a04061 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a00865 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00317 ^ 1 * a00809 ^ 1)
theorem ha04061 : a04061.IsHomogeneous 51 := by
  unfold a04061
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00317.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a04062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00809 ^ 1)
theorem ha04062 : a04062.IsHomogeneous 48 := by
  unfold a04062
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a04063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04051 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04062 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a04061 ^ 1)
theorem ha04063 : a04063.IsHomogeneous 51 := by
  unfold a04063
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04051.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04062.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha04061.pow 1)))

@[irreducible]
def a04064 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a02008 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a00865 ^ 1)
theorem ha04064 : a04064.IsHomogeneous 51 := by
  unfold a04064
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha02008.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a04065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04052 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04064 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a04061 ^ 1)
theorem ha04065 : a04065.IsHomogeneous 51 := by
  unfold a04065
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04052.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04064.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha04061.pow 1)))

@[irreducible]
def a04066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04063 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a04065 ^ 1)
theorem ha04066 : a04066.IsHomogeneous 51 := by
  unfold a04066
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04063.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha04065.pow 1)))

@[irreducible]
def a04067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01896 ^ 1) + (C ((14 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a03890 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a01896 ^ 1)
theorem ha04067 : a04067.IsHomogeneous 51 := by
  unfold a04067
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha03890.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a04068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04055 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a04067 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a04062 ^ 1)
theorem ha04068 : a04068.IsHomogeneous 51 := by
  unfold a04068
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04055.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha04067.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha04062.pow 1)))

@[irreducible]
def a04069 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04057 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04068 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04063 ^ 1)
theorem ha04069 : a04069.IsHomogeneous 54 := by
  unfold a04069
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04057.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04068.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04063.pow 1)))

@[irreducible]
def a04070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04060 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04069 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04066 ^ 1)
theorem ha04070 : a04070.IsHomogeneous 54 := by
  unfold a04070
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04060.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04069.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04066.pow 1)))

@[irreducible]
def a04071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01617 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00655 ^ 1 * a00865 ^ 1)
theorem ha04071 : a04071.IsHomogeneous 54 := by
  unfold a04071
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00655.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a04072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a02008 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00655 ^ 1 * a00865 ^ 1)
theorem ha04072 : a04072.IsHomogeneous 54 := by
  unfold a04072
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00655.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a04073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04071 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a04072 ^ 1)
theorem ha04073 : a04073.IsHomogeneous 54 := by
  unfold a04073
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha04072.pow 1)))

@[irreducible]
def a04074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a03432 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00317 ^ 1 * a01617 ^ 1)
theorem ha04074 : a04074.IsHomogeneous 54 := by
  unfold a04074
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha03432.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)).mul (ha01617.pow 1)))

@[irreducible]
def a04075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04071 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a04074 ^ 1)
theorem ha04075 : a04075.IsHomogeneous 54 := by
  unfold a04075
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha04074.pow 1)))

@[irreducible]
def a04076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04075 ^ 1)
theorem ha04076 : a04076.IsHomogeneous 54 := by
  unfold a04076
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04075.pow 1)))

@[irreducible]
def a04077 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01324 ^ 1)
theorem ha04077 : a04077.IsHomogeneous 6 := by
  unfold a04077
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)))

@[irreducible]
def a04078 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00504 ^ 1)
theorem ha04078 : a04078.IsHomogeneous 6 := by
  unfold a04078
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00504.pow 1)))

@[irreducible]
def a04079 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04077 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a04078 ^ 1)
theorem ha04079 : a04079.IsHomogeneous 6 := by
  unfold a04079
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04077.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha04078.pow 1)))

@[irreducible]
def a04080 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01324 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a02931 ^ 1)
theorem ha04080 : a04080.IsHomogeneous 6 := by
  unfold a04080
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha02931.pow 1)))

@[irreducible]
def a04081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04077 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04080 ^ 1)
theorem ha04081 : a04081.IsHomogeneous 6 := by
  unfold a04081
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04077.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04080.pow 1)))

@[irreducible]
def a04082 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04079 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04081 ^ 1)
theorem ha04082 : a04082.IsHomogeneous 6 := by
  unfold a04082
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04079.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04081.pow 1)))

@[irreducible]
def a04083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04078 ^ 1)
theorem ha04083 : a04083.IsHomogeneous 12 := by
  unfold a04083
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04078.pow 1)))

@[irreducible]
def a04084 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04083 ^ 1) + (C ((10 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04079 ^ 1)
theorem ha04084 : a04084.IsHomogeneous 12 := by
  unfold a04084
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04083.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04079.pow 1)))

@[irreducible]
def a04085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04084 ^ 1) + (C ((10 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a04082 ^ 1)
theorem ha04085 : a04085.IsHomogeneous 12 := by
  unfold a04085
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04084.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha04082.pow 1)))

@[irreducible]
def a04086 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a04085 ^ 1) + (C ((7 : ℂ) / (54 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3)
theorem ha04086 : a04086.IsHomogeneous 18 := by
  unfold a04086
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha04085.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (54 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a04087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a04086 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a02008 ^ 1)
theorem ha04087 : a04087.IsHomogeneous 54 := by
  unfold a04087
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a04088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04072 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a04087 ^ 1)
theorem ha04088 : a04088.IsHomogeneous 54 := by
  unfold a04088
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04072.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha04087.pow 1)))

@[irreducible]
def a04089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04073 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a04088 ^ 1)
theorem ha04089 : a04089.IsHomogeneous 54 := by
  unfold a04089
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha04088.pow 1)))

@[irreducible]
def a04090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04076 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04089 ^ 1)
theorem ha04090 : a04090.IsHomogeneous 54 := by
  unfold a04090
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04076.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04089.pow 1)))

@[irreducible]
def a04091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00201 ^ 1 * a00317 ^ 1)
theorem ha04091 : a04091.IsHomogeneous 48 := by
  unfold a04091
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00201.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a04092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a00865 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a00621 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00201 ^ 1 * a00317 ^ 1)
theorem ha04092 : a04092.IsHomogeneous 54 := by
  unfold a04092
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00201.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a04093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a01555 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00130 ^ 1 * a00317 ^ 1 * a00621 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00621 ^ 1)
theorem ha04093 : a04093.IsHomogeneous 54 := by
  unfold a04093
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha01555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a04094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04092 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a04093 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a04091 ^ 1)
theorem ha04094 : a04094.IsHomogeneous 54 := by
  unfold a04094
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04092.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha04093.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha04091.pow 1)))

@[irreducible]
def a04095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00054 ^ 1 * a00865 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00201 ^ 1 * a00317 ^ 1)
theorem ha04095 : a04095.IsHomogeneous 51 := by
  unfold a04095
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00054.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00201.pow 1)).mul (ha00317.pow 1)))

end CycleQ2Concrete
