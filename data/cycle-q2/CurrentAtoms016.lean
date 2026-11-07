import Proposal.CurrentAtoms015

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a05888 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05850 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05887 ^ 1)
theorem ha05888 : a05888.IsHomogeneous 36 := by
  unfold a05888
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05850.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05887.pow 1)))

@[irreducible]
def a05889 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00316 ^ 1 * a01340 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00513 ^ 1 * a00864 ^ 1)
theorem ha05889 : a05889.IsHomogeneous 30 := by
  unfold a05889
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00316.pow 1)).mul (ha01340.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00513.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05890 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00513 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00157 ^ 1 * a02007 ^ 1)
theorem ha05890 : a05890.IsHomogeneous 30 := by
  unfold a05890
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00513.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00157.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a05891 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05890 ^ 1)
theorem ha05891 : a05891.IsHomogeneous 30 := by
  unfold a05891
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05889.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05890.pow 1)))

@[irreducible]
def a05892 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01340 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a02956 ^ 1)
theorem ha05892 : a05892.IsHomogeneous 24 := by
  unfold a05892
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01340.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha02956.pow 1)))

@[irreducible]
def a05893 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05892 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05889 ^ 1)
theorem ha05893 : a05893.IsHomogeneous 30 := by
  unfold a05893
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05892.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05889.pow 1)))

@[irreducible]
def a05894 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05891 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05893 ^ 1)
theorem ha05894 : a05894.IsHomogeneous 30 := by
  unfold a05894
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05893.pow 1)))

@[irreducible]
def a05895 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a04085 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a02007 ^ 1)
theorem ha05895 : a05895.IsHomogeneous 24 := by
  unfold a05895
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha04085.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a05896 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05890 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a05895 ^ 1)
theorem ha05896 : a05896.IsHomogeneous 30 := by
  unfold a05896
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05890.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha05895.pow 1)))

@[irreducible]
def a05897 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05891 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05896 ^ 1)
theorem ha05897 : a05897.IsHomogeneous 30 := by
  unfold a05897
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05891.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05896.pow 1)))

@[irreducible]
def a05898 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05894 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05897 ^ 1)
theorem ha05898 : a05898.IsHomogeneous 30 := by
  unfold a05898
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05894.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05897.pow 1)))

@[irreducible]
def a05899 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05784 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02956 ^ 1)
theorem ha05899 : a05899.IsHomogeneous 30 := by
  unfold a05899
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05784.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02956.pow 1)))

@[irreducible]
def a05900 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05899 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05892 ^ 1)
theorem ha05900 : a05900.IsHomogeneous 30 := by
  unfold a05900
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05899.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05892.pow 1)))

@[irreducible]
def a05901 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05893 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a05900 ^ 1)
theorem ha05901 : a05901.IsHomogeneous 30 := by
  unfold a05901
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05893.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha05900.pow 1)))

@[irreducible]
def a05902 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05894 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05901 ^ 1)
theorem ha05902 : a05902.IsHomogeneous 30 := by
  unfold a05902
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05894.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05901.pow 1)))

@[irreducible]
def a05903 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05898 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05902 ^ 1)
theorem ha05903 : a05903.IsHomogeneous 30 := by
  unfold a05903
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05898.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05902.pow 1)))

@[irreducible]
def a05904 : Poly := (C ((-1 : ℂ) / (192 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a05888 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a05903 ^ 1)
theorem ha05904 : a05904.IsHomogeneous 49 := by
  unfold a05904
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (192 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha05888.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha05903.pow 1)))

@[irreducible]
def a05905 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a00520 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a00506 ^ 1)
theorem ha05905 : a05905.IsHomogeneous 30 := by
  unfold a05905
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha00520.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a05906 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00506 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00155 ^ 1 * a00520 ^ 1)
theorem ha05906 : a05906.IsHomogeneous 18 := by
  unfold a05906
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00155.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a05907 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a01356 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1 * a00520 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a00520 ^ 1)
theorem ha05907 : a05907.IsHomogeneous 30 := by
  unfold a05907
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha01356.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha00520.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a05908 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05905 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a05907 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05906 ^ 1)
theorem ha05908 : a05908.IsHomogeneous 30 := by
  unfold a05908
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05905.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha05907.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05906.pow 1)))

@[irreducible]
def a05909 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00506 ^ 1)
theorem ha05909 : a05909.IsHomogeneous 24 := by
  unfold a05909
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a05910 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a02935 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1 * a01327 ^ 1)
theorem ha05910 : a05910.IsHomogeneous 24 := by
  unfold a05910
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a05911 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05905 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a05910 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a05909 ^ 1)
theorem ha05911 : a05911.IsHomogeneous 30 := by
  unfold a05911
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05905.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha05910.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha05909.pow 1)))

@[irreducible]
def a05912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00155 ^ 1)
theorem ha05912 : a05912.IsHomogeneous 18 := by
  unfold a05912
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a05913 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05912 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05909 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a05906 ^ 1)
theorem ha05913 : a05913.IsHomogeneous 24 := by
  unfold a05913
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05912.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05909.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha05906.pow 1)))

@[irreducible]
def a05914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05908 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05911 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a05913 ^ 1)
theorem ha05914 : a05914.IsHomogeneous 30 := by
  unfold a05914
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05908.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05911.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha05913.pow 1)))

@[irreducible]
def a05915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00520 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a01356 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00520 ^ 1)
theorem ha05915 : a05915.IsHomogeneous 18 := by
  unfold a05915
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00520.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha01356.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a05916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00520 ^ 1)
theorem ha05916 : a05916.IsHomogeneous 12 := by
  unfold a05916
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00520.pow 1)))

@[irreducible]
def a05917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05906 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a05916 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a05915 ^ 1)
theorem ha05917 : a05917.IsHomogeneous 18 := by
  unfold a05917
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05906.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha05916.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha05915.pow 1)))

@[irreducible]
def a05918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a02985 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01356 ^ 1)
theorem ha05918 : a05918.IsHomogeneous 30 := by
  unfold a05918
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha01356.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a05919 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05907 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05918 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05915 ^ 1)
theorem ha05919 : a05919.IsHomogeneous 30 := by
  unfold a05919
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05907.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05918.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05915.pow 1)))

@[irreducible]
def a05920 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05908 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a05919 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05917 ^ 1)
theorem ha05920 : a05920.IsHomogeneous 30 := by
  unfold a05920
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05908.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha05919.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05917.pow 1)))

@[irreducible]
def a05921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha05921 : a05921.IsHomogeneous 12 := by
  unfold a05921
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a05922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05912 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a05921 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05916 ^ 1)
theorem ha05922 : a05922.IsHomogeneous 18 := by
  unfold a05922
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05912.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha05921.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05916.pow 1)))

@[irreducible]
def a05923 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05922 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05913 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a05917 ^ 1)
theorem ha05923 : a05923.IsHomogeneous 24 := by
  unfold a05923
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05922.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05913.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha05917.pow 1)))

@[irreducible]
def a05924 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05920 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a05923 ^ 1)
theorem ha05924 : a05924.IsHomogeneous 30 := by
  unfold a05924
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05914.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05920.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha05923.pow 1)))

@[irreducible]
def a05925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00506 ^ 1 * a00520 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a01356 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a00520 ^ 1 * a01327 ^ 1)
theorem ha05925 : a05925.IsHomogeneous 36 := by
  unfold a05925
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1)).mul (ha00520.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha01356.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a05926 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00025 ^ 1 * a02935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00520 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a01327 ^ 1)
theorem ha05926 : a05926.IsHomogeneous 24 := by
  unfold a05926
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00520.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a05927 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05905 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05925 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05926 ^ 1)
theorem ha05927 : a05927.IsHomogeneous 36 := by
  unfold a05927
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05905.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05925.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05926.pow 1)))

@[irreducible]
def a05928 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a02985 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a01356 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a01356 ^ 1)
theorem ha05928 : a05928.IsHomogeneous 36 := by
  unfold a05928
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha02985.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a05929 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05907 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a05928 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a05925 ^ 1)
theorem ha05929 : a05929.IsHomogeneous 36 := by
  unfold a05929
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05907.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha05928.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha05925.pow 1)))

@[irreducible]
def a05930 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05908 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05927 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a05929 ^ 1)
theorem ha05930 : a05930.IsHomogeneous 36 := by
  unfold a05930
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05908.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05927.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha05929.pow 1)))

@[irreducible]
def a05931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a05754 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a02935 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a02935 ^ 1)
theorem ha05931 : a05931.IsHomogeneous 24 := by
  unfold a05931
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha05754.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a05932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05910 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a05931 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05926 ^ 1)
theorem ha05932 : a05932.IsHomogeneous 30 := by
  unfold a05932
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05910.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha05931.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05926.pow 1)))

@[irreducible]
def a05933 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05911 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05927 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a05932 ^ 1)
theorem ha05933 : a05933.IsHomogeneous 36 := by
  unfold a05933
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05911.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05927.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha05932.pow 1)))

@[irreducible]
def a05934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05914 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05930 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05933 ^ 1)
theorem ha05934 : a05934.IsHomogeneous 36 := by
  unfold a05934
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05914.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05930.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05933.pow 1)))

@[irreducible]
def a05935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a05834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a02985 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a02985 ^ 1)
theorem ha05935 : a05935.IsHomogeneous 30 := by
  unfold a05935
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha05834.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha02985.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02985.pow 1)))

@[irreducible]
def a05936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05918 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a05935 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a05928 ^ 1)
theorem ha05936 : a05936.IsHomogeneous 36 := by
  unfold a05936
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05918.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha05935.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha05928.pow 1)))

@[irreducible]
def a05937 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05919 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05929 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05936 ^ 1)
theorem ha05937 : a05937.IsHomogeneous 36 := by
  unfold a05937
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05919.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05929.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05936.pow 1)))

@[irreducible]
def a05938 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05920 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05930 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a05937 ^ 1)
theorem ha05938 : a05938.IsHomogeneous 36 := by
  unfold a05938
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05920.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05930.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha05937.pow 1)))

@[irreducible]
def a05939 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05924 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05934 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05938 ^ 1)
theorem ha05939 : a05939.IsHomogeneous 36 := by
  unfold a05939
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05924.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05934.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05938.pow 1)))

@[irreducible]
def a05940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00130 ^ 1 * a00316 ^ 1 * a00547 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00168 ^ 1 * a00316 ^ 1)
theorem ha05940 : a05940.IsHomogeneous 30 := by
  unfold a05940
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00168.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a05941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1 * a00316 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00547 ^ 1)
theorem ha05941 : a05941.IsHomogeneous 18 := by
  unfold a05941
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).mul (ha00316.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00547.pow 1)))

@[irreducible]
def a05942 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00130 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00316 ^ 1 * a00547 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00547 ^ 1)
theorem ha05942 : a05942.IsHomogeneous 30 := by
  unfold a05942
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a05943 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05940 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a05942 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05941 ^ 1)
theorem ha05943 : a05943.IsHomogeneous 30 := by
  unfold a05943
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05940.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha05942.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05941.pow 1)))

@[irreducible]
def a05944 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00168 ^ 1 * a00316 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00316 ^ 1)
theorem ha05944 : a05944.IsHomogeneous 18 := by
  unfold a05944
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00168.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a05945 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a02007 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a00864 ^ 1)
theorem ha05945 : a05945.IsHomogeneous 30 := by
  unfold a05945
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05940 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05945 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05944 ^ 1)
theorem ha05946 : a05946.IsHomogeneous 30 := by
  unfold a05946
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05940.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05945.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05944.pow 1)))

@[irreducible]
def a05947 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00168 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00037 ^ 1)
theorem ha05947 : a05947.IsHomogeneous 12 := by
  unfold a05947
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)))

@[irreducible]
def a05948 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05941 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a05944 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a05947 ^ 1)
theorem ha05948 : a05948.IsHomogeneous 18 := by
  unfold a05948
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05941.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha05944.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha05947.pow 1)))

@[irreducible]
def a05949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05943 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05946 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05948 ^ 1)
theorem ha05949 : a05949.IsHomogeneous 30 := by
  unfold a05949
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05943.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05946.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05948.pow 1)))

@[irreducible]
def a05950 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00547 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00547 ^ 1)
theorem ha05950 : a05950.IsHomogeneous 24 := by
  unfold a05950
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01412.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00547.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00547.pow 1)))

@[irreducible]
def a05951 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00547 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00168 ^ 1)
theorem ha05951 : a05951.IsHomogeneous 18 := by
  unfold a05951
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00547.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00168.pow 1)))

@[irreducible]
def a05952 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05951 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05950 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05941 ^ 1)
theorem ha05952 : a05952.IsHomogeneous 24 := by
  unfold a05952
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05951.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05950.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05941.pow 1)))

@[irreducible]
def a05953 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a03085 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01412 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a01412 ^ 1)
theorem ha05953 : a05953.IsHomogeneous 24 := by
  unfold a05953
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a05954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05942 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a05953 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a05950 ^ 1)
theorem ha05954 : a05954.IsHomogeneous 30 := by
  unfold a05954
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05942.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha05953.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha05950.pow 1)))

@[irreducible]
def a05955 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05943 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a05954 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a05952 ^ 1)
theorem ha05955 : a05955.IsHomogeneous 30 := by
  unfold a05955
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05943.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha05954.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha05952.pow 1)))

@[irreducible]
def a05956 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00037 ^ 1)
theorem ha05956 : a05956.IsHomogeneous 12 := by
  unfold a05956
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00037.pow 1)))

@[irreducible]
def a05957 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05951 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a05956 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05947 ^ 1)
theorem ha05957 : a05957.IsHomogeneous 18 := by
  unfold a05957
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05951.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha05956.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05947.pow 1)))

@[irreducible]
def a05958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05957 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05952 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05948 ^ 1)
theorem ha05958 : a05958.IsHomogeneous 24 := by
  unfold a05958
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05957.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05952.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05948.pow 1)))

@[irreducible]
def a05959 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05955 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a05958 ^ 1)
theorem ha05959 : a05959.IsHomogeneous 30 := by
  unfold a05959
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05949.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05955.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha05958.pow 1)))

@[irreducible]
def a05960 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1 * a00547 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a00547 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1 * a01412 ^ 1)
theorem ha05960 : a05960.IsHomogeneous 36 := by
  unfold a05960
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).mul (ha00547.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha00864.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a05961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00168 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00547 ^ 1 * a00864 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a00864 ^ 1)
theorem ha05961 : a05961.IsHomogeneous 36 := by
  unfold a05961
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a05962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05940 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a05961 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a05960 ^ 1)
theorem ha05962 : a05962.IsHomogeneous 36 := by
  unfold a05962
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05940.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha05961.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha05960.pow 1)))

@[irreducible]
def a05963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a01412 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a03085 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01412 ^ 1)
theorem ha05963 : a05963.IsHomogeneous 24 := by
  unfold a05963
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha03085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a05964 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05942 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05960 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a05963 ^ 1)
theorem ha05964 : a05964.IsHomogeneous 36 := by
  unfold a05964
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05942.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05960.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha05963.pow 1)))

@[irreducible]
def a05965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05943 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05962 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a05964 ^ 1)
theorem ha05965 : a05965.IsHomogeneous 36 := by
  unfold a05965
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05943.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05962.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha05964.pow 1)))

@[irreducible]
def a05966 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a04085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a02007 ^ 1)
theorem ha05966 : a05966.IsHomogeneous 30 := by
  unfold a05966
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha02007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a05967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05945 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a05966 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a05961 ^ 1)
theorem ha05967 : a05967.IsHomogeneous 36 := by
  unfold a05967
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05945.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha05966.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha05961.pow 1)))

@[irreducible]
def a05968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05946 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05962 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05967 ^ 1)
theorem ha05968 : a05968.IsHomogeneous 36 := by
  unfold a05968
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05946.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05962.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05967.pow 1)))

@[irreducible]
def a05969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05965 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05968 ^ 1)
theorem ha05969 : a05969.IsHomogeneous 36 := by
  unfold a05969
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05949.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05965.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05968.pow 1)))

@[irreducible]
def a05970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a01327 ^ 1)
theorem ha05970 : a05970.IsHomogeneous 12 := by
  unfold a05970
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha01327.pow 1)))

@[irreducible]
def a05971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00506 ^ 1)
theorem ha05971 : a05971.IsHomogeneous 12 := by
  unfold a05971
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)))

@[irreducible]
def a05972 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05970 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a05971 ^ 1)
theorem ha05972 : a05972.IsHomogeneous 12 := by
  unfold a05972
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05970.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha05971.pow 1)))

@[irreducible]
def a05973 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02935 ^ 1)
theorem ha05973 : a05973.IsHomogeneous 6 := by
  unfold a05973
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01327.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02935.pow 1)))

@[irreducible]
def a05974 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05970 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a05973 ^ 1)
theorem ha05974 : a05974.IsHomogeneous 12 := by
  unfold a05974
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha05973.pow 1)))

@[irreducible]
def a05975 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05972 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05974 ^ 1)
theorem ha05975 : a05975.IsHomogeneous 12 := by
  unfold a05975
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05972.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05974.pow 1)))

@[irreducible]
def a05976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1)
theorem ha05976 : a05976.IsHomogeneous 6 := by
  unfold a05976
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)))

@[irreducible]
def a05977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05976 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05971 ^ 1)
theorem ha05977 : a05977.IsHomogeneous 12 := by
  unfold a05977
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05976.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05971.pow 1)))

@[irreducible]
def a05978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05972 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a05977 ^ 1)
theorem ha05978 : a05978.IsHomogeneous 12 := by
  unfold a05978
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05972.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha05977.pow 1)))

@[irreducible]
def a05979 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05975 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05978 ^ 1)
theorem ha05979 : a05979.IsHomogeneous 12 := by
  unfold a05979
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05975.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05978.pow 1)))

@[irreducible]
def a05980 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a05754 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02935 ^ 1)
theorem ha05980 : a05980.IsHomogeneous 12 := by
  unfold a05980
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha05754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02935.pow 1)))

@[irreducible]
def a05981 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05980 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05973 ^ 1)
theorem ha05981 : a05981.IsHomogeneous 12 := by
  unfold a05981
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05980.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05973.pow 1)))

@[irreducible]
def a05982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05974 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a05981 ^ 1)
theorem ha05982 : a05982.IsHomogeneous 12 := by
  unfold a05982
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05974.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha05981.pow 1)))

@[irreducible]
def a05983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05975 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05982 ^ 1)
theorem ha05983 : a05983.IsHomogeneous 12 := by
  unfold a05983
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05975.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05982.pow 1)))

@[irreducible]
def a05984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05979 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05983 ^ 1)
theorem ha05984 : a05984.IsHomogeneous 12 := by
  unfold a05984
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05979.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05983.pow 1)))

@[irreducible]
def a05985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a02949 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a01335 ^ 1)
theorem ha05985 : a05985.IsHomogeneous 12 := by
  unfold a05985
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha02949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha01335.pow 1)))

@[irreducible]
def a05986 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05985 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a03108 ^ 1)
theorem ha05986 : a05986.IsHomogeneous 12 := by
  unfold a05986
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05985.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha03108.pow 1)))

@[irreducible]
def a05987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03109 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a05986 ^ 1)
theorem ha05987 : a05987.IsHomogeneous 12 := by
  unfold a05987
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03109.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha05986.pow 1)))

@[irreducible]
def a05988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a05775 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a02949 ^ 1)
theorem ha05988 : a05988.IsHomogeneous 12 := by
  unfold a05988
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha05775.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha02949.pow 1)))

@[irreducible]
def a05989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05985 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a05988 ^ 1)
theorem ha05989 : a05989.IsHomogeneous 12 := by
  unfold a05989
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05985.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha05988.pow 1)))

@[irreducible]
def a05990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05986 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05989 ^ 1)
theorem ha05990 : a05990.IsHomogeneous 12 := by
  unfold a05990
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05986.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05989.pow 1)))

@[irreducible]
def a05991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05987 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a05990 ^ 1)
theorem ha05991 : a05991.IsHomogeneous 12 := by
  unfold a05991
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05987.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha05990.pow 1)))

@[irreducible]
def a05992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03112 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05987 ^ 1)
theorem ha05992 : a05992.IsHomogeneous 12 := by
  unfold a05992
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03112.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05987.pow 1)))

@[irreducible]
def a05993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05991 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05992 ^ 1)
theorem ha05993 : a05993.IsHomogeneous 12 := by
  unfold a05993
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05991.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05992.pow 1)))

@[irreducible]
def a05994 : Poly := (C ((-7 : ℂ) / (3 : ℂ)) * a05993 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05984 ^ 1)
theorem ha05994 : a05994.IsHomogeneous 12 := by
  unfold a05994
  exact (((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (3 : ℂ))).mul (ha05993.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05984.pow 1)))

@[irreducible]
def a05995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a05994 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a03085 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a03085 ^ 1)
theorem ha05995 : a05995.IsHomogeneous 24 := by
  unfold a05995
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha05994.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha03085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha03085.pow 1)))

@[irreducible]
def a05996 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05953 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05995 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a05963 ^ 1)
theorem ha05996 : a05996.IsHomogeneous 30 := by
  unfold a05996
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05953.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05995.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha05963.pow 1)))

@[irreducible]
def a05997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05954 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05964 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a05996 ^ 1)
theorem ha05997 : a05997.IsHomogeneous 36 := by
  unfold a05997
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05954.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05964.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha05996.pow 1)))

@[irreducible]
def a05998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05955 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05965 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a05997 ^ 1)
theorem ha05998 : a05998.IsHomogeneous 36 := by
  unfold a05998
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05955.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05965.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha05997.pow 1)))

@[irreducible]
def a05999 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05959 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05969 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05998 ^ 1)
theorem ha05999 : a05999.IsHomogeneous 36 := by
  unfold a05999
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05959.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05969.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05998.pow 1)))

@[irreducible]
def a06000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05939 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05999 ^ 1)
theorem ha06000 : a06000.IsHomogeneous 36 := by
  unfold a06000
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05939.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05999.pow 1)))

@[irreducible]
def a06001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00316 ^ 1 * a00555 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00316 ^ 1 * a00324 ^ 1)
theorem ha06001 : a06001.IsHomogeneous 30 := by
  unfold a06001
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a06002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00171 ^ 1 * a00316 ^ 1 * a00324 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00324 ^ 1 * a00555 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00171 ^ 1)
theorem ha06002 : a06002.IsHomogeneous 24 := by
  unfold a06002
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a06003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00316 ^ 1 * a00555 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a00555 ^ 1)
theorem ha06003 : a06003.IsHomogeneous 24 := by
  unfold a06003
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a06004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06001 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06003 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a06002 ^ 1)
theorem ha06004 : a06004.IsHomogeneous 30 := by
  unfold a06004
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06001.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06003.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha06002.pow 1)))

@[irreducible]
def a06005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00324 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00171 ^ 1 * a00316 ^ 1 * a00324 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00316 ^ 1)
theorem ha06005 : a06005.IsHomogeneous 24 := by
  unfold a06005
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00324.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00171.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a06006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a00864 ^ 1)
theorem ha06006 : a06006.IsHomogeneous 30 := by
  unfold a06006
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06001 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06006 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a06005 ^ 1)
theorem ha06007 : a06007.IsHomogeneous 30 := by
  unfold a06007
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06006.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha06005.pow 1)))

@[irreducible]
def a06008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00171 ^ 1)
theorem ha06008 : a06008.IsHomogeneous 12 := by
  unfold a06008
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00171.pow 1)))

@[irreducible]
def a06009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06002 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06005 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06008 ^ 1)
theorem ha06009 : a06009.IsHomogeneous 24 := by
  unfold a06009
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06002.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06005.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06008.pow 1)))

@[irreducible]
def a06010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06007 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a06009 ^ 1)
theorem ha06010 : a06010.IsHomogeneous 30 := by
  unfold a06010
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06007.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha06009.pow 1)))

@[irreducible]
def a06011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a01429 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00324 ^ 1 * a00555 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00555 ^ 1)
theorem ha06011 : a06011.IsHomogeneous 24 := by
  unfold a06011
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a06012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00555 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00171 ^ 1)
theorem ha06012 : a06012.IsHomogeneous 18 := by
  unfold a06012
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00555.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00171.pow 1)))

@[irreducible]
def a06013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06002 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a06011 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06012 ^ 1)
theorem ha06013 : a06013.IsHomogeneous 24 := by
  unfold a06013
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06002.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha06011.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06012.pow 1)))

@[irreducible]
def a06014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a01429 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a01429 ^ 1)
theorem ha06014 : a06014.IsHomogeneous 24 := by
  unfold a06014
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a06015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06011 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a06014 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a06003 ^ 1)
theorem ha06015 : a06015.IsHomogeneous 30 := by
  unfold a06015
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06011.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha06014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha06003.pow 1)))

@[irreducible]
def a06016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06004 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a06015 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a06013 ^ 1)
theorem ha06016 : a06016.IsHomogeneous 30 := by
  unfold a06016
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha06015.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha06013.pow 1)))

@[irreducible]
def a06017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00171 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1)
theorem ha06017 : a06017.IsHomogeneous 12 := by
  unfold a06017
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00171.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)))

@[irreducible]
def a06018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06012 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06017 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06008 ^ 1)
theorem ha06018 : a06018.IsHomogeneous 18 := by
  unfold a06018
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06012.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06017.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06008.pow 1)))

@[irreducible]
def a06019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06013 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a06018 ^ 1)
theorem ha06019 : a06019.IsHomogeneous 24 := by
  unfold a06019
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06013.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha06018.pow 1)))

@[irreducible]
def a06020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06010 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06016 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a06019 ^ 1)
theorem ha06020 : a06020.IsHomogeneous 30 := by
  unfold a06020
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06010.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06016.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha06019.pow 1)))

@[irreducible]
def a06021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00316 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00316 ^ 1 * a00555 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00555 ^ 1 * a00864 ^ 1)
theorem ha06021 : a06021.IsHomogeneous 30 := by
  unfold a06021
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha01429.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00171 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a00864 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1 * a00864 ^ 1)
theorem ha06022 : a06022.IsHomogeneous 36 := by
  unfold a06022
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha02007.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06001 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a06022 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06021 ^ 1)
theorem ha06023 : a06023.IsHomogeneous 36 := by
  unfold a06023
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha06022.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06021.pow 1)))

@[irreducible]
def a06024 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00316 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a03116 ^ 1)
theorem ha06024 : a06024.IsHomogeneous 24 := by
  unfold a06024
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha03116.pow 1)))

@[irreducible]
def a06025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06003 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a06024 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a06021 ^ 1)
theorem ha06025 : a06025.IsHomogeneous 30 := by
  unfold a06025
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06003.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha06024.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha06021.pow 1)))

@[irreducible]
def a06026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06023 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06025 ^ 1)
theorem ha06026 : a06026.IsHomogeneous 36 := by
  unfold a06026
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06023.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06025.pow 1)))

@[irreducible]
def a06027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a04085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a02007 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a02007 ^ 1)
theorem ha06027 : a06027.IsHomogeneous 30 := by
  unfold a06027
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha04085.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a06028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06027 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06022 ^ 1)
theorem ha06028 : a06028.IsHomogeneous 36 := by
  unfold a06028
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06006.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06027.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06022.pow 1)))

@[irreducible]
def a06029 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06023 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a06028 ^ 1)
theorem ha06029 : a06029.IsHomogeneous 36 := by
  unfold a06029
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06007.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06023.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha06028.pow 1)))

@[irreducible]
def a06030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06010 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06029 ^ 1)
theorem ha06030 : a06030.IsHomogeneous 36 := by
  unfold a06030
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06010.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06026.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06029.pow 1)))

@[irreducible]
def a06031 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00510 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a01335 ^ 1)
theorem ha06031 : a06031.IsHomogeneous 6 := by
  unfold a06031
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha01335.pow 1)))

@[irreducible]
def a06032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00510 ^ 1)
theorem ha06032 : a06032.IsHomogeneous 12 := by
  unfold a06032
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)))

@[irreducible]
def a06033 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06032 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a06031 ^ 1)
theorem ha06033 : a06033.IsHomogeneous 12 := by
  unfold a06033
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha06031.pow 1)))

@[irreducible]
def a06034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01335 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a02949 ^ 1)
theorem ha06034 : a06034.IsHomogeneous 6 := by
  unfold a06034
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01335.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha02949.pow 1)))

@[irreducible]
def a06035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06031 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a06034 ^ 1)
theorem ha06035 : a06035.IsHomogeneous 6 := by
  unfold a06035
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06031.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha06034.pow 1)))

@[irreducible]
def a06036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06033 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a06035 ^ 1)
theorem ha06036 : a06036.IsHomogeneous 12 := by
  unfold a06036
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06033.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha06035.pow 1)))

@[irreducible]
def a06037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01330 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06032 ^ 1)
theorem ha06037 : a06037.IsHomogeneous 12 := by
  unfold a06037
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01330.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06032.pow 1)))

@[irreducible]
def a06038 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06033 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06037 ^ 1)
theorem ha06038 : a06038.IsHomogeneous 12 := by
  unfold a06038
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06033.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06037.pow 1)))

@[irreducible]
def a06039 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06036 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06038 ^ 1)
theorem ha06039 : a06039.IsHomogeneous 12 := by
  unfold a06039
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06036.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06038.pow 1)))

@[irreducible]
def a06040 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a05775 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02949 ^ 1)
theorem ha06040 : a06040.IsHomogeneous 12 := by
  unfold a06040
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha05775.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02949.pow 1)))

@[irreducible]
def a06041 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06040 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06034 ^ 1)
theorem ha06041 : a06041.IsHomogeneous 12 := by
  unfold a06041
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06040.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06034.pow 1)))

@[irreducible]
def a06042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06041 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06035 ^ 1)
theorem ha06042 : a06042.IsHomogeneous 12 := by
  unfold a06042
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06035.pow 1)))

@[irreducible]
def a06043 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06036 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06042 ^ 1)
theorem ha06043 : a06043.IsHomogeneous 12 := by
  unfold a06043
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06036.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06042.pow 1)))

@[irreducible]
def a06044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06039 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06043 ^ 1)
theorem ha06044 : a06044.IsHomogeneous 12 := by
  unfold a06044
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06039.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06043.pow 1)))

@[irreducible]
def a06045 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a06044 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a03116 ^ 1)
theorem ha06045 : a06045.IsHomogeneous 24 := by
  unfold a06045
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha06044.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha03116.pow 1)))

@[irreducible]
def a06046 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06014 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a06045 ^ 1) + (C ((45 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a06024 ^ 1)
theorem ha06046 : a06046.IsHomogeneous 30 := by
  unfold a06046
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha06045.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha06024.pow 1)))

@[irreducible]
def a06047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06015 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a06046 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a06025 ^ 1)
theorem ha06047 : a06047.IsHomogeneous 36 := by
  unfold a06047
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06015.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha06046.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha06025.pow 1)))

@[irreducible]
def a06048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06016 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06026 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a06047 ^ 1)
theorem ha06048 : a06048.IsHomogeneous 36 := by
  unfold a06048
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06016.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06026.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha06047.pow 1)))

@[irreducible]
def a06049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06020 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06030 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06048 ^ 1)
theorem ha06049 : a06049.IsHomogeneous 36 := by
  unfold a06049
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06020.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06030.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06048.pow 1)))

@[irreducible]
def a06050 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a06049 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05904 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a06000 ^ 1)
theorem ha06050 : a06050.IsHomogeneous 49 := by
  unfold a06050
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha06049.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05904.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha06000.pow 1)))

@[irreducible]
def a06051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01373 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00528 ^ 1 * a00864 ^ 1)
theorem ha06051 : a06051.IsHomogeneous 30 := by
  unfold a06051
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01373.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00528.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06052 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00161 ^ 1 * a02007 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00528 ^ 1 * a00864 ^ 1)
theorem ha06052 : a06052.IsHomogeneous 36 := by
  unfold a06052
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00161.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00528.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a06053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06052 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a06051 ^ 1)
theorem ha06053 : a06053.IsHomogeneous 36 := by
  unfold a06053
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06052.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha06051.pow 1)))

@[irreducible]
def a06054 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a01373 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03016 ^ 1)
theorem ha06054 : a06054.IsHomogeneous 30 := by
  unfold a06054
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha01373.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03016.pow 1)))

@[irreducible]
def a06055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06054 ^ 1)
theorem ha06055 : a06055.IsHomogeneous 30 := by
  unfold a06055
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06054.pow 1)))

@[irreducible]
def a06056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06053 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a06055 ^ 1)
theorem ha06056 : a06056.IsHomogeneous 36 := by
  unfold a06056
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06053.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha06055.pow 1)))

@[irreducible]
def a06057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a04085 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00161 ^ 1 * a02007 ^ 1)
theorem ha06057 : a06057.IsHomogeneous 30 := by
  unfold a06057
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha04085.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a06058 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06052 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a06057 ^ 1)
theorem ha06058 : a06058.IsHomogeneous 36 := by
  unfold a06058
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06052.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha06057.pow 1)))

@[irreducible]
def a06059 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06053 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06058 ^ 1)
theorem ha06059 : a06059.IsHomogeneous 36 := by
  unfold a06059
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06053.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06058.pow 1)))

@[irreducible]
def a06060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06056 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06059 ^ 1)
theorem ha06060 : a06060.IsHomogeneous 36 := by
  unfold a06060
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06056.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06059.pow 1)))

@[irreducible]
def a06061 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05883 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03016 ^ 1)
theorem ha06061 : a06061.IsHomogeneous 30 := by
  unfold a06061
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05883.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03016.pow 1)))

@[irreducible]
def a06062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06061 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06054 ^ 1)
theorem ha06062 : a06062.IsHomogeneous 36 := by
  unfold a06062
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06061.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06054.pow 1)))

@[irreducible]
def a06063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06062 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06055 ^ 1)
theorem ha06063 : a06063.IsHomogeneous 36 := by
  unfold a06063
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06062.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06055.pow 1)))

@[irreducible]
def a06064 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06056 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a06063 ^ 1)
theorem ha06064 : a06064.IsHomogeneous 36 := by
  unfold a06064
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06056.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha06063.pow 1)))

@[irreducible]
def a06065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06060 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06064 ^ 1)
theorem ha06065 : a06065.IsHomogeneous 36 := by
  unfold a06065
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06060.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06064.pow 1)))

@[irreducible]
def a06066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00577 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a01473 ^ 1)
theorem ha06066 : a06066.IsHomogeneous 36 := by
  unfold a06066
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00577.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a06067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00179 ^ 1 * a02935 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00577 ^ 1 * a01327 ^ 1)
theorem ha06067 : a06067.IsHomogeneous 30 := by
  unfold a06067
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00179.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00577.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06067 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a06066 ^ 1)
theorem ha06068 : a06068.IsHomogeneous 36 := by
  unfold a06068
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06067.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha06066.pow 1)))

@[irreducible]
def a06069 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a03191 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00506 ^ 1 * a01473 ^ 1)
theorem ha06069 : a06069.IsHomogeneous 36 := by
  unfold a06069
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha03191.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a06070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06066 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a06069 ^ 1)
theorem ha06070 : a06070.IsHomogeneous 36 := by
  unfold a06070
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06066.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha06069.pow 1)))

@[irreducible]
def a06071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06068 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a06070 ^ 1)
theorem ha06071 : a06071.IsHomogeneous 36 := by
  unfold a06071
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06068.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha06070.pow 1)))

@[irreducible]
def a06072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a02935 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00040 ^ 1 * a05754 ^ 1)
theorem ha06072 : a06072.IsHomogeneous 24 := by
  unfold a06072
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a06073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06072 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06067 ^ 1)
theorem ha06073 : a06073.IsHomogeneous 30 := by
  unfold a06073
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06072.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06067.pow 1)))

@[irreducible]
def a06074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06068 ^ 1)
theorem ha06074 : a06074.IsHomogeneous 36 := by
  unfold a06074
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06068.pow 1)))

@[irreducible]
def a06075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06074 ^ 1)
theorem ha06075 : a06075.IsHomogeneous 36 := by
  unfold a06075
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06074.pow 1)))

@[irreducible]
def a06076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1)
theorem ha06076 : a06076.IsHomogeneous 18 := by
  unfold a06076
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a06077 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00506 ^ 1)
theorem ha06077 : a06077.IsHomogeneous 18 := by
  unfold a06077
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00506.pow 1)))

@[irreducible]
def a06078 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00506 ^ 1)
theorem ha06078 : a06078.IsHomogeneous 12 := by
  unfold a06078
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)))

@[irreducible]
def a06079 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06076 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06077 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06078 ^ 1)
theorem ha06079 : a06079.IsHomogeneous 18 := by
  unfold a06079
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06076.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06077.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06078.pow 1)))

@[irreducible]
def a06080 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01327 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1)
theorem ha06080 : a06080.IsHomogeneous 18 := by
  unfold a06080
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1)
theorem ha06081 : a06081.IsHomogeneous 18 := by
  unfold a06081
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a06082 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06076 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06080 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06081 ^ 1)
theorem ha06082 : a06082.IsHomogeneous 18 := by
  unfold a06082
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06076.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06080.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06081.pow 1)))

@[irreducible]
def a06083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02935 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a01327 ^ 1)
theorem ha06083 : a06083.IsHomogeneous 12 := by
  unfold a06083
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02935.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06084 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06077 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06080 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a06083 ^ 1)
theorem ha06084 : a06084.IsHomogeneous 18 := by
  unfold a06084
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06077.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06080.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha06083.pow 1)))

@[irreducible]
def a06085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06079 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06082 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06084 ^ 1)
theorem ha06085 : a06085.IsHomogeneous 18 := by
  unfold a06085
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06079.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06082.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06084.pow 1)))

@[irreducible]
def a06086 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1)
theorem ha06086 : a06086.IsHomogeneous 6 := by
  unfold a06086
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a06087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha06087 : a06087.IsHomogeneous 12 := by
  unfold a06087
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a06088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06087 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06076 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06086 ^ 1)
theorem ha06088 : a06088.IsHomogeneous 18 := by
  unfold a06088
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06087.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06076.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06086.pow 1)))

@[irreducible]
def a06089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06078 ^ 1)
theorem ha06089 : a06089.IsHomogeneous 12 := by
  unfold a06089
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06086.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06078.pow 1)))

@[irreducible]
def a06090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06079 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06088 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06089 ^ 1)
theorem ha06090 : a06090.IsHomogeneous 18 := by
  unfold a06090
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06079.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06088.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06089.pow 1)))

@[irreducible]
def a06091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha06091 : a06091.IsHomogeneous 12 := by
  unfold a06091
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a06092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06087 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a06091 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06081 ^ 1)
theorem ha06092 : a06092.IsHomogeneous 18 := by
  unfold a06092
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06087.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha06091.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06081.pow 1)))

@[irreducible]
def a06093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06082 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06088 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06092 ^ 1)
theorem ha06093 : a06093.IsHomogeneous 18 := by
  unfold a06093
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06082.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06088.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06092.pow 1)))

@[irreducible]
def a06094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06090 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06093 ^ 1)
theorem ha06094 : a06094.IsHomogeneous 18 := by
  unfold a06094
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06085.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06090.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06093.pow 1)))

@[irreducible]
def a06095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00506 ^ 1)
theorem ha06095 : a06095.IsHomogeneous 18 := by
  unfold a06095
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00506.pow 1)))

@[irreducible]
def a06096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a02935 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a01327 ^ 1)
theorem ha06096 : a06096.IsHomogeneous 18 := by
  unfold a06096
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a06097 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06077 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06096 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a06095 ^ 1)
theorem ha06097 : a06097.IsHomogeneous 18 := by
  unfold a06097
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06077.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06096.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha06095.pow 1)))

@[irreducible]
def a06098 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1)
theorem ha06098 : a06098.IsHomogeneous 18 := by
  unfold a06098
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a06099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06078 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06095 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06098 ^ 1)
theorem ha06099 : a06099.IsHomogeneous 18 := by
  unfold a06099
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06078.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06095.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06098.pow 1)))

@[irreducible]
def a06100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06079 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06097 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a06099 ^ 1)
theorem ha06100 : a06100.IsHomogeneous 18 := by
  unfold a06100
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06079.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06097.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha06099.pow 1)))

@[irreducible]
def a06101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a05754 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a02935 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a02935 ^ 1)
theorem ha06101 : a06101.IsHomogeneous 18 := by
  unfold a06101
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a06102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06096 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a06083 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06101 ^ 1)
theorem ha06102 : a06102.IsHomogeneous 18 := by
  unfold a06102
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06096.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha06083.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06101.pow 1)))

@[irreducible]
def a06103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06084 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06097 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a06102 ^ 1)
theorem ha06103 : a06103.IsHomogeneous 18 := by
  unfold a06103
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06084.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06097.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha06102.pow 1)))

@[irreducible]
def a06104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06100 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06103 ^ 1)
theorem ha06104 : a06104.IsHomogeneous 18 := by
  unfold a06104
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06085.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06100.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06103.pow 1)))

@[irreducible]
def a06105 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1)
theorem ha06105 : a06105.IsHomogeneous 12 := by
  unfold a06105
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a06106 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06105 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06098 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a06086 ^ 1)
theorem ha06106 : a06106.IsHomogeneous 18 := by
  unfold a06106
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06105.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06098.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha06086.pow 1)))

@[irreducible]
def a06107 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06089 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06099 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06106 ^ 1)
theorem ha06107 : a06107.IsHomogeneous 18 := by
  unfold a06107
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06089.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06099.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06106.pow 1)))

@[irreducible]
def a06108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06090 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06100 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a06107 ^ 1)
theorem ha06108 : a06108.IsHomogeneous 18 := by
  unfold a06108
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06090.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06100.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha06107.pow 1)))

@[irreducible]
def a06109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06094 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06108 ^ 1)
theorem ha06109 : a06109.IsHomogeneous 18 := by
  unfold a06109
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06094.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06104.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06108.pow 1)))

@[irreducible]
def a06110 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00570 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a01461 ^ 1)
theorem ha06110 : a06110.IsHomogeneous 18 := by
  unfold a06110
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00570.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha01461.pow 1)))

@[irreducible]
def a06111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00176 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00570 ^ 1)
theorem ha06111 : a06111.IsHomogeneous 18 := by
  unfold a06111
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00176.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00570.pow 1)))

@[irreducible]
def a06112 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06110 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a06111 ^ 1)
theorem ha06112 : a06112.IsHomogeneous 18 := by
  unfold a06112
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06110.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha06111.pow 1)))

@[irreducible]
def a06113 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00176 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00032 ^ 1)
theorem ha06113 : a06113.IsHomogeneous 12 := by
  unfold a06113
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00176.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a06114 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a06113 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06111 ^ 1)
theorem ha06114 : a06114.IsHomogeneous 18 := by
  unfold a06114
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha06113.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06111.pow 1)))

@[irreducible]
def a06115 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06112 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a06114 ^ 1)
theorem ha06115 : a06115.IsHomogeneous 18 := by
  unfold a06115
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06112.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha06114.pow 1)))

@[irreducible]
def a06116 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01461 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a03172 ^ 1)
theorem ha06116 : a06116.IsHomogeneous 18 := by
  unfold a06116
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha03172.pow 1)))

@[irreducible]
def a06117 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06110 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a06116 ^ 1)
theorem ha06117 : a06117.IsHomogeneous 18 := by
  unfold a06117
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06110.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha06116.pow 1)))

@[irreducible]
def a06118 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06112 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06117 ^ 1)
theorem ha06118 : a06118.IsHomogeneous 18 := by
  unfold a06118
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06112.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06117.pow 1)))

@[irreducible]
def a06119 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06118 ^ 1)
theorem ha06119 : a06119.IsHomogeneous 18 := by
  unfold a06119
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06115.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06118.pow 1)))

@[irreducible]
def a06120 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a01335 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00510 ^ 1)
theorem ha06120 : a06120.IsHomogeneous 12 := by
  unfold a06120
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha01335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)))

@[irreducible]
def a06121 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a02949 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00324 ^ 1 * a01335 ^ 1)
theorem ha06121 : a06121.IsHomogeneous 12 := by
  unfold a06121
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha02949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00324.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a06122 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06120 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a06121 ^ 1)
theorem ha06122 : a06122.IsHomogeneous 12 := by
  unfold a06122
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06120.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha06121.pow 1)))

@[irreducible]
def a06123 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a05775 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00133 ^ 1 * a02949 ^ 1)
theorem ha06123 : a06123.IsHomogeneous 12 := by
  unfold a06123
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha05775.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00133.pow 1)).mul (ha02949.pow 1)))

@[irreducible]
def a06124 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06121 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a06123 ^ 1)
theorem ha06124 : a06124.IsHomogeneous 12 := by
  unfold a06124
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06121.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha06123.pow 1)))

@[irreducible]
def a06125 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06122 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a06124 ^ 1)
theorem ha06125 : a06125.IsHomogeneous 12 := by
  unfold a06125
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06122.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha06124.pow 1)))

@[irreducible]
def a06126 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01424 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a06120 ^ 1)
theorem ha06126 : a06126.IsHomogeneous 12 := by
  unfold a06126
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01424.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha06120.pow 1)))

@[irreducible]
def a06127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06122 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a06126 ^ 1)
theorem ha06127 : a06127.IsHomogeneous 12 := by
  unfold a06127
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06122.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha06126.pow 1)))

@[irreducible]
def a06128 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06125 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06127 ^ 1)
theorem ha06128 : a06128.IsHomogeneous 12 := by
  unfold a06128
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06125.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06127.pow 1)))

@[irreducible]
def a06129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06126 ^ 1)
theorem ha06129 : a06129.IsHomogeneous 12 := by
  unfold a06129
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06126.pow 1)))

@[irreducible]
def a06130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06127 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a06129 ^ 1)
theorem ha06130 : a06130.IsHomogeneous 12 := by
  unfold a06130
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06127.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha06129.pow 1)))

@[irreducible]
def a06131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06128 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06130 ^ 1)
theorem ha06131 : a06131.IsHomogeneous 12 := by
  unfold a06131
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06128.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06130.pow 1)))

@[irreducible]
def a06132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a06131 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a03172 ^ 1)
theorem ha06132 : a06132.IsHomogeneous 18 := by
  unfold a06132
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha06131.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha03172.pow 1)))

@[irreducible]
def a06133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06116 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a06132 ^ 1)
theorem ha06133 : a06133.IsHomogeneous 18 := by
  unfold a06133
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06116.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha06132.pow 1)))

@[irreducible]
def a06134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06117 ^ 1) + (C ((5 : ℂ) / (8 : ℂ)) * a06133 ^ 1)
theorem ha06134 : a06134.IsHomogeneous 18 := by
  unfold a06134
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06117.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (8 : ℂ))).mul (ha06133.pow 1)))

@[irreducible]
def a06135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06134 ^ 1)
theorem ha06135 : a06135.IsHomogeneous 18 := by
  unfold a06135
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06118.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06134.pow 1)))

@[irreducible]
def a06136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06119 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06135 ^ 1)
theorem ha06136 : a06136.IsHomogeneous 18 := by
  unfold a06136
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06119.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06135.pow 1)))

@[irreducible]
def a06137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00574 ^ 1 * a01335 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00510 ^ 1 * a01469 ^ 1)
theorem ha06137 : a06137.IsHomogeneous 18 := by
  unfold a06137
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00574.pow 1)).mul (ha01335.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)).mul (ha01469.pow 1)))

@[irreducible]
def a06138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1 * a02949 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00574 ^ 1 * a01335 ^ 1)
theorem ha06138 : a06138.IsHomogeneous 18 := by
  unfold a06138
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha02949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00574.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a06139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06137 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a06138 ^ 1)
theorem ha06139 : a06139.IsHomogeneous 18 := by
  unfold a06139
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06137.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha06138.pow 1)))

@[irreducible]
def a06140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a02949 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00025 ^ 1 * a05775 ^ 1)
theorem ha06140 : a06140.IsHomogeneous 12 := by
  unfold a06140
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha02949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00025.pow 1)).mul (ha05775.pow 1)))

@[irreducible]
def a06141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a06140 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06138 ^ 1)
theorem ha06141 : a06141.IsHomogeneous 18 := by
  unfold a06141
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha06140.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06138.pow 1)))

@[irreducible]
def a06142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06139 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a06141 ^ 1)
theorem ha06142 : a06142.IsHomogeneous 18 := by
  unfold a06142
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha06141.pow 1)))

@[irreducible]
def a06143 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a03186 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00510 ^ 1 * a01469 ^ 1)
theorem ha06143 : a06143.IsHomogeneous 18 := by
  unfold a06143
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha03186.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)).mul (ha01469.pow 1)))

end CycleQ2Concrete
