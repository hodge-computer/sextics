import Proposal.CurrentAtoms023

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a07936 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 5 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00032 ^ 1 * a07873 ^ 1 * a07927 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07935 ^ 1)
theorem ha07936 : a07936.IsHomogeneous 49 := by
  unfold a07936
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00032.pow 1)).mul (ha07873.pow 1)).mul (ha07927.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07935.pow 1)))

@[irreducible]
def a07937 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 5 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00009 ^ 1 * a00014 ^ 2 * a00025 ^ 1 * a07868 ^ 1 * a07873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07895 ^ 1 * a07920 ^ 1)
theorem ha07937 : a07937.IsHomogeneous 55 := by
  unfold a07937
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).mul (ha07868.pow 1)).mul (ha07873.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07895.pow 1)).mul (ha07920.pow 1)))

@[irreducible]
def a07938 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a07873 ^ 1 * a07927 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07937 ^ 1)
theorem ha07938 : a07938.IsHomogeneous 55 := by
  unfold a07938
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha07873.pow 1)).mul (ha07927.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07937.pow 1)))

@[irreducible]
def a07939 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07889 ^ 1 * a07936 ^ 1)
theorem ha07939 : a07939.IsHomogeneous 55 := by
  unfold a07939
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)).mul (ha07936.pow 1)))

@[irreducible]
def a07940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 3 * a07868 ^ 1 * a07932 ^ 1 * a07939 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07918 ^ 1 * a07931 ^ 1)
theorem ha07940 : a07940.IsHomogeneous 169 := by
  unfold a07940
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 3)).mul (ha07868.pow 1)).mul (ha07932.pow 1)).mul (ha07939.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07918.pow 1)).mul (ha07931.pow 1)))

@[irreducible]
def a07941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07931 ^ 1 * a07932 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 3 * a07918 ^ 1 * a07939 ^ 1)
theorem ha07941 : a07941.IsHomogeneous 175 := by
  unfold a07941
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07931.pow 1)).mul (ha07932.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 3)).mul (ha07918.pow 1)).mul (ha07939.pow 1)))

@[irreducible]
def a07942 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a07940 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07941 ^ 2)
theorem ha07942 : a07942.IsHomogeneous 356 := by
  unfold a07942
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha07940.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07941.pow 2)))

@[irreducible]
def a07943 : Poly := (C ((-1296 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00025 ^ 1 * a07873 ^ 1 * a07904 ^ 1 * a07905 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07872 ^ 1 * a07875 ^ 1 * a07912 ^ 1)
theorem ha07943 : a07943.IsHomogeneous 160 := by
  unfold a07943
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1296 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00025.pow 1)).mul (ha07873.pow 1)).mul (ha07904.pow 1)).mul (ha07905.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07872.pow 1)).mul (ha07875.pow 1)).mul (ha07912.pow 1)))

@[irreducible]
def a07944 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a07913 ^ 1 * a07940 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07941 ^ 1 * a07943 ^ 1)
theorem ha07944 : a07944.IsHomogeneous 341 := by
  unfold a07944
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha07913.pow 1)).mul (ha07940.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07941.pow 1)).mul (ha07943.pow 1)))

@[irreducible]
def a07945 : Poly := (C ((-1 : ℂ) / (324 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a07940 ^ 1 * a07943 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07913 ^ 1 * a07941 ^ 1)
theorem ha07945 : a07945.IsHomogeneous 340 := by
  unfold a07945
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (324 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha07940.pow 1)).mul (ha07943.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07913.pow 1)).mul (ha07941.pow 1)))

@[irreducible]
def a07946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a07944 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a07945 ^ 1)
theorem ha07946 : a07946.IsHomogeneous 342 := by
  unfold a07946
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha07944.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha07945.pow 1)))

@[irreducible]
def a07947 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00005 ^ 6) + (C ((-1 : ℂ) / (6 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 6)
theorem ha07947 : a07947.IsHomogeneous 6 := by
  unfold a07947
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 6)))

@[irreducible]
def a07948 : Poly := (C ((-7776 : ℂ) / (1 : ℂ)) * a00002 ^ 2 * a00005 ^ 2 * a00105 ^ 2 * a07864 ^ 1 * a07942 ^ 1 * a07947 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 2 * a00012 ^ 1 * a00013 ^ 1 * a00014 ^ 6 * a00103 ^ 3 * a00106 ^ 2 * a00123 ^ 1 * a00124 ^ 1 * a07867 ^ 1 * a07946 ^ 1)
theorem ha07948 : a07948.IsHomogeneous 814 := by
  unfold a07948
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7776 : ℂ) / (1 : ℂ))).mul (ha00002.pow 2)).mul (ha00005.pow 2)).mul (ha00105.pow 2)).mul (ha07864.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 2)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 6)).mul (ha00103.pow 3)).mul (ha00106.pow 2)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07867.pow 1)).mul (ha07946.pow 1)))

@[irreducible]
def a07949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1)
theorem ha07949 : a07949.IsHomogeneous 6 := by
  unfold a07949
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)))

@[irreducible]
def a07950 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00007 ^ 1)
theorem ha07950 : a07950.IsHomogeneous 6 := by
  unfold a07950
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)))

@[irreducible]
def a07951 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a07950 ^ 1)
theorem ha07951 : a07951.IsHomogeneous 12 := by
  unfold a07951
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha07950.pow 1)))

@[irreducible]
def a07952 : Poly := (C ((-1 : ℂ) / (23328 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00013 ^ 1 * a00018 ^ 2 * a00033 ^ 1 * a07948 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00014 ^ 6 * a00034 ^ 3 * a00103 ^ 3 * a00106 ^ 2 * a00123 ^ 1 * a00124 ^ 1 * a07867 ^ 1 * a07942 ^ 1 * a07949 ^ 1 * a07951 ^ 1)
theorem ha07952 : a07952.IsHomogeneous 937 := by
  unfold a07952
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (23328 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00013.pow 1)).mul (ha00018.pow 2)).mul (ha00033.pow 1)).mul (ha07948.pow 1)).add ((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00014.pow 6)).mul (ha00034.pow 3)).mul (ha00103.pow 3)).mul (ha00106.pow 2)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07949.pow 1)).mul (ha07951.pow 1)))

@[irreducible]
def a07953 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 3 * a00001 ^ 1 * a00003 ^ 1 * a00004 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00028 ^ 1)
theorem ha07953 : a07953.IsHomogeneous 6 := by
  unfold a07953
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 3)).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00028.pow 1)))

@[irreducible]
def a07954 : Poly := (C ((-11664 : ℂ) / (1 : ℂ)) * a00026 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 6 * a00003 ^ 3 * a00034 ^ 3)
theorem ha07954 : a07954.IsHomogeneous 108 := by
  unfold a07954
  exact (((isHomogeneous_C (σ := Fin 6) ((-11664 : ℂ) / (1 : ℂ))).mul (ha00026.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 6)).mul (ha00003.pow 3)).mul (ha00034.pow 3)))

@[irreducible]
def a07955 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00005 ^ 1 * a02121 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 3 * a00136 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00012 ^ 1 * a00940 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 2 * a00367 ^ 1) + (C ((9 : ℂ) / (20 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 4 * a00014 ^ 1 * a00100 ^ 1 * a00125 ^ 1)
theorem ha07955 : a07955.IsHomogeneous 148 := by
  unfold a07955
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00005.pow 1)).mul (ha02121.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00136.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00012.pow 1)).mul (ha00940.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00367.pow 1))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (20 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 4)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00125.pow 1)))

@[irreducible]
def a07956 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00001 ^ 1 * a00004 ^ 1 * a00101 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00013 ^ 2 * a07955 ^ 1)
theorem ha07956 : a07956.IsHomogeneous 160 := by
  unfold a07956
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00101.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00013.pow 2)).mul (ha07955.pow 1)))

@[irreducible]
def a07957 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00005 ^ 1 * a02121 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 2 * a00367 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00012 ^ 1 * a00940 ^ 1) + (C ((3 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 3 * a00136 ^ 1) + (C ((9 : ℂ) / (100 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 4 * a00014 ^ 1 * a00100 ^ 1 * a00125 ^ 1)
theorem ha07957 : a07957.IsHomogeneous 148 := by
  unfold a07957
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00005.pow 1)).mul (ha02121.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00367.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00012.pow 1)).mul (ha00940.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00136.pow 1))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (100 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 4)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00125.pow 1)))

@[irreducible]
def a07958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00013 ^ 1 * a07957 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00001 ^ 1 * a00004 ^ 1 * a00101 ^ 2)
theorem ha07958 : a07958.IsHomogeneous 160 := by
  unfold a07958
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha07957.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00101.pow 2)))

@[irreducible]
def a07959 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00000 ^ 6 * a00003 ^ 3 * a00013 ^ 1 * a00018 ^ 1 * a00033 ^ 1 * a00034 ^ 2 * a07958 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00026 ^ 1 * a07954 ^ 1 * a07956 ^ 1)
theorem ha07959 : a07959.IsHomogeneous 328 := by
  unfold a07959
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00000.pow 6)).mul (ha00003.pow 3)).mul (ha00013.pow 1)).mul (ha00018.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 2)).mul (ha07958.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00026.pow 1)).mul (ha07954.pow 1)).mul (ha07956.pow 1)))

@[irreducible]
def a07960 : Poly := (C ((-36 : ℂ) / (1 : ℂ)) * a07824 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 2 * a00003 ^ 1 * a00015 ^ 2 * a00034 ^ 1)
theorem ha07960 : a07960.IsHomogeneous 48 := by
  unfold a07960
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (1 : ℂ))).mul (ha07824.pow 2)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 2)).mul (ha00003.pow 1)).mul (ha00015.pow 2)).mul (ha00034.pow 1)))

@[irreducible]
def a07961 : Poly := (C ((-144 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a00018 ^ 1 * a00033 ^ 1 * a07824 ^ 2 * a07954 ^ 1 * a07958 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00034 ^ 1 * a07959 ^ 1 * a07960 ^ 1)
theorem ha07961 : a07961.IsHomogeneous 409 := by
  unfold a07961
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha00018.pow 1)).mul (ha00033.pow 1)).mul (ha07824.pow 2)).mul (ha07954.pow 1)).mul (ha07958.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00034.pow 1)).mul (ha07959.pow 1)).mul (ha07960.pow 1)))

@[irreducible]
def a07962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00008 ^ 1 * a00014 ^ 2) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 3 * a00128 ^ 1)
theorem ha07962 : a07962.IsHomogeneous 22 := by
  unfold a07962
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00008.pow 1)).mul (ha00014.pow 2)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00128.pow 1)))

@[irreducible]
def a07963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a07962 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 4 * a00018 ^ 1)
theorem ha07963 : a07963.IsHomogeneous 28 := by
  unfold a07963
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha07962.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 4)).mul (ha00018.pow 1)))

@[irreducible]
def a07964 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00014 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 5 * a00001 ^ 2 * a00003 ^ 1 * a00004 ^ 2 * a00132 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 5 * a00001 ^ 2 * a00003 ^ 1 * a00004 ^ 2 * a00131 ^ 1)
theorem ha07964 : a07964.IsHomogeneous 16 := by
  unfold a07964
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00156.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 2)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00132.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 2)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00131.pow 1)))

@[irreducible]
def a07965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00018 ^ 1 * a00019 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00018 ^ 1 * a00025 ^ 1 * a07964 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00019 ^ 1 * a00025 ^ 1 * a07962 ^ 1)
theorem ha07965 : a07965.IsHomogeneous 46 := by
  unfold a07965
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00018.pow 1)).mul (ha00019.pow 1)).mul (ha00130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00018.pow 1)).mul (ha00025.pow 1)).mul (ha07964.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00019.pow 1)).mul (ha00025.pow 1)).mul (ha07962.pow 1)))

@[irreducible]
def a07966 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00004 ^ 1 * a07965 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00018 ^ 1 * a07963 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 3 * a00003 ^ 1 * a00019 ^ 2 * a07964 ^ 1)
theorem ha07966 : a07966.IsHomogeneous 52 := by
  unfold a07966
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha07965.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00018.pow 1)).mul (ha07963.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 3)).mul (ha00003.pow 1)).mul (ha00019.pow 2)).mul (ha07964.pow 1)))

@[irreducible]
def a07967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a07962 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00018 ^ 1 * a00130 ^ 1)
theorem ha07967 : a07967.IsHomogeneous 30 := by
  unfold a07967
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha07962.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00018.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a07968 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a07967 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00019 ^ 1 * a07964 ^ 1)
theorem ha07968 : a07968.IsHomogeneous 33 := by
  unfold a07968
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha07967.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00019.pow 1)).mul (ha07964.pow 1)))

@[irreducible]
def a07969 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00034 ^ 1 * a07966 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00026 ^ 1 * a07968 ^ 1)
theorem ha07969 : a07969.IsHomogeneous 87 := by
  unfold a07969
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00034.pow 1)).mul (ha07966.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00026.pow 1)).mul (ha07968.pow 1)))

@[irreducible]
def a07970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07830 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 1)
theorem ha07970 : a07970.IsHomogeneous 11 := by
  unfold a07970
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07830.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 1)))

@[irreducible]
def a07971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00019 ^ 1 * a07970 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00002 ^ 3 * a00018 ^ 1)
theorem ha07971 : a07971.IsHomogeneous 27 := by
  unfold a07971
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00019.pow 1)).mul (ha07970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00002.pow 3)).mul (ha00018.pow 1)))

@[irreducible]
def a07972 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a00025 ^ 1 * a07971 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00018 ^ 1 * a07970 ^ 1) + (C ((1 : ℂ) / (432 : ℂ)) * a00000 ^ 3 * a00002 ^ 3 * a00003 ^ 3 * a00019 ^ 2)
theorem ha07972 : a07972.IsHomogeneous 41 := by
  unfold a07972
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00025.pow 1)).mul (ha07971.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00018.pow 1)).mul (ha07970.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 3)).mul (ha00003.pow 3)).mul (ha00019.pow 2)))

@[irreducible]
def a07973 : Poly := (C ((-18 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00025 ^ 1 * a07970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00019 ^ 1)
theorem ha07973 : a07973.IsHomogeneous 20 := by
  unfold a07973
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00025.pow 1)).mul (ha07970.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00019.pow 1)))

@[irreducible]
def a07974 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00026 ^ 1 * a07973 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00034 ^ 1 * a07972 ^ 1)
theorem ha07974 : a07974.IsHomogeneous 74 := by
  unfold a07974
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00026.pow 1)).mul (ha07973.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00034.pow 1)).mul (ha07972.pow 1)))

@[irreducible]
def a07975 : Poly := (C ((-1 : ℂ) / (4000 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 5 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 4 * a00105 ^ 4 * a00123 ^ 3 * a00124 ^ 5 * a00134 ^ 11 * a07948 ^ 1 * a07974 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00013 ^ 1 * a00106 ^ 1 * a00107 ^ 1 * a07823 ^ 1 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07969 ^ 1)
theorem ha07975 : a07975.IsHomogeneous 3417 := by
  unfold a07975
  exact ((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4000 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 5)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 4)).mul (ha00105.pow 4)).mul (ha00123.pow 3)).mul (ha00124.pow 5)).mul (ha00134.pow 11)).mul (ha07948.pow 1)).mul (ha07974.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha07823.pow 1)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07969.pow 1)))

@[irreducible]
def a07976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a00018 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a07960 ^ 1 * a07975 ^ 1) + (C ((1 : ℂ) / (31104000 : ℂ)) * a00001 ^ 8 * a00002 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 3 * a00034 ^ 1 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 5 * a00103 ^ 5 * a00105 ^ 5 * a00106 ^ 1 * a00107 ^ 1 * a00117 ^ 1 * a00123 ^ 5 * a00124 ^ 5 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07961 ^ 1)
theorem ha07976 : a07976.IsHomogeneous 3612 := by
  unfold a07976
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha00018.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha07960.pow 1)).mul (ha07975.pow 1)).add ((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (31104000 : ℂ))).mul (ha00001.pow 8)).mul (ha00002.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 3)).mul (ha00034.pow 1)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 5)).mul (ha00103.pow 5)).mul (ha00105.pow 5)).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 5)).mul (ha00124.pow 5)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07961.pow 1)))

@[irreducible]
def a07977 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 5 * a00009 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00009 ^ 1)
theorem ha07977 : a07977.IsHomogeneous 11 := by
  unfold a07977
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 5)).mul (ha00009.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00009.pow 1)))

@[irreducible]
def a07978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00018 ^ 1 * a07824 ^ 1 * a07949 ^ 1 * a07977 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00003 ^ 1 * a00013 ^ 1 * a00014 ^ 2 * a00015 ^ 1 * a00021 ^ 1 * a07947 ^ 1)
theorem ha07978 : a07978.IsHomogeneous 65 := by
  unfold a07978
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00018.pow 1)).mul (ha07824.pow 1)).mul (ha07949.pow 1)).mul (ha07977.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 2)).mul (ha00015.pow 1)).mul (ha00021.pow 1)).mul (ha07947.pow 1)))

@[irreducible]
def a07979 : Poly := (C ((-4374 : ℂ) / (125 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 9 * a00026 ^ 1 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07960 ^ 1 * a07978 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00018 ^ 1 * a07824 ^ 1 * a07976 ^ 1)
theorem ha07979 : a07979.IsHomogeneous 3661 := by
  unfold a07979
  exact (((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-4374 : ℂ) / (125 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 9)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07960.pow 1)).mul (ha07978.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00018.pow 1)).mul (ha07824.pow 1)).mul (ha07976.pow 1)))

@[irreducible]
def a07980 : Poly := (C ((-729 : ℂ) / (250 : ℂ)) * a00001 ^ 2 * a00014 ^ 3 * a00018 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 4 * a00105 ^ 4 * a00123 ^ 3 * a00124 ^ 5 * a00134 ^ 11 * a07824 ^ 1 * a07831 ^ 1 * a07952 ^ 1 * a07960 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07953 ^ 1 * a07979 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a00012 ^ 1 * a00013 ^ 1 * a00024 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00106 ^ 1 * a07826 ^ 1 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 1) + (C ((729 : ℂ) / (250 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 3 * a00003 ^ 1 * a00012 ^ 1 * a00013 ^ 1 * a00014 ^ 11 * a00015 ^ 1 * a00021 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07829 ^ 1 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 1)
theorem ha07980 : a07980.IsHomogeneous 3667 := by
  unfold a07980
  exact (((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-729 : ℂ) / (250 : ℂ))).mul (ha00001.pow 2)).mul (ha00014.pow 3)).mul (ha00018.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 4)).mul (ha00105.pow 4)).mul (ha00123.pow 3)).mul (ha00124.pow 5)).mul (ha00134.pow 11)).mul (ha07824.pow 1)).mul (ha07831.pow 1)).mul (ha07952.pow 1)).mul (ha07960.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07953.pow 1)).mul (ha07979.pow 1))).add ((((((((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00024.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00106.pow 1)).mul (ha07826.pow 1)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 1))).add (((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((729 : ℂ) / (250 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 11)).mul (ha00015.pow 1)).mul (ha00021.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07829.pow 1)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 1)))

@[irreducible]
def a07981 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00010 ^ 1 * a00015 ^ 1 * a07980 ^ 1) + (C ((729 : ℂ) / (125 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 3 * a00003 ^ 1 * a00012 ^ 1 * a00013 ^ 1 * a00014 ^ 10 * a00018 ^ 2 * a00023 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 1)
theorem ha07981 : a07981.IsHomogeneous 3679 := by
  unfold a07981
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00010.pow 1)).mul (ha00015.pow 1)).mul (ha07980.pow 1)).add ((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((729 : ℂ) / (125 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 10)).mul (ha00018.pow 2)).mul (ha00023.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 1)))

@[irreducible]
def a07982 : Poly := (C ((-729 : ℂ) / (125 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 3 * a00003 ^ 1 * a00010 ^ 1 * a00012 ^ 1 * a00013 ^ 1 * a00014 ^ 10 * a00022 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07981 ^ 1)
theorem ha07982 : a07982.IsHomogeneous 3679 := by
  unfold a07982
  exact (((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-729 : ℂ) / (125 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00010.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 10)).mul (ha00022.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07981.pow 1)))

@[irreducible]
def a07983 : Poly := (C ((-243 : ℂ) / (125 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 3 * a00003 ^ 1 * a00011 ^ 1 * a00012 ^ 1 * a00013 ^ 1 * a00014 ^ 10 * a00018 ^ 2 * a00026 ^ 1 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00015 ^ 1 * a00016 ^ 1 * a07979 ^ 1)
theorem ha07983 : a07983.IsHomogeneous 3673 := by
  unfold a07983
  exact (((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-243 : ℂ) / (125 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00011.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 10)).mul (ha00018.pow 2)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00015.pow 1)).mul (ha00016.pow 1)).mul (ha07979.pow 1)))

@[irreducible]
def a07984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07983 ^ 1) + (C ((243 : ℂ) / (250 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 3 * a00003 ^ 1 * a00012 ^ 1 * a00013 ^ 1 * a00014 ^ 10 * a00022 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 1)
theorem ha07984 : a07984.IsHomogeneous 3673 := by
  unfold a07984
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07983.pow 1)).add (((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((243 : ℂ) / (250 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 10)).mul (ha00022.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 1)))

@[irreducible]
def a07985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 2 * a00003 ^ 1 * a00014 ^ 10 * a00018 ^ 2 * a00023 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 1 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11) + (C ((125 : ℂ) / (729 : ℂ)) * a00010 ^ 1 * a00015 ^ 1 * a00016 ^ 1 * a07826 ^ 1)
theorem ha07985 : a07985.IsHomogeneous 3018 := by
  unfold a07985
  exact (((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 2)).mul (ha00003.pow 1)).mul (ha00014.pow 10)).mul (ha00018.pow 2)).mul (ha00023.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 1)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).add (((((isHomogeneous_C (σ := Fin 6) ((125 : ℂ) / (729 : ℂ))).mul (ha00010.pow 1)).mul (ha00015.pow 1)).mul (ha00016.pow 1)).mul (ha07826.pow 1)))

@[irreducible]
def a07986 : Poly := (C ((-1458 : ℂ) / (125 : ℂ)) * a00002 ^ 1 * a00012 ^ 1 * a00013 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00106 ^ 1 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 1 * a07985 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07981 ^ 1) + (C ((729 : ℂ) / (125 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 3 * a00003 ^ 1 * a00010 ^ 1 * a00012 ^ 1 * a00013 ^ 1 * a00014 ^ 10 * a00022 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 1)
theorem ha07986 : a07986.IsHomogeneous 3679 := by
  unfold a07986
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-1458 : ℂ) / (125 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00106.pow 1)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 1)).mul (ha07985.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07981.pow 1))).add ((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((729 : ℂ) / (125 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00010.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 10)).mul (ha00022.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 1)))

@[irreducible]
def a07987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07983 ^ 1) + (C ((729 : ℂ) / (250 : ℂ)) * a00000 ^ 1 * a00001 ^ 2 * a00002 ^ 3 * a00003 ^ 1 * a00012 ^ 1 * a00013 ^ 1 * a00014 ^ 10 * a00022 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00034 ^ 3 * a00042 ^ 5 * a00100 ^ 5 * a00101 ^ 7 * a00103 ^ 7 * a00105 ^ 4 * a00106 ^ 2 * a00123 ^ 4 * a00124 ^ 6 * a00134 ^ 11 * a07867 ^ 1 * a07942 ^ 1 * a07947 ^ 1 * a07960 ^ 1)
theorem ha07987 : a07987.IsHomogeneous 3673 := by
  unfold a07987
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07983.pow 1)).add (((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((729 : ℂ) / (250 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00012.pow 1)).mul (ha00013.pow 1)).mul (ha00014.pow 10)).mul (ha00022.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 5)).mul (ha00101.pow 7)).mul (ha00103.pow 7)).mul (ha00105.pow 4)).mul (ha00106.pow 2)).mul (ha00123.pow 4)).mul (ha00124.pow 6)).mul (ha00134.pow 11)).mul (ha07867.pow 1)).mul (ha07942.pow 1)).mul (ha07947.pow 1)).mul (ha07960.pow 1)))

@[irreducible]
def a07988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 3 * a00001 ^ 1 * a00003 ^ 1 * a00004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1)
theorem ha07988 : a07988.IsHomogeneous 6 := by
  unfold a07988
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 3)).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)))

@[irreducible]
def a07989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 6) + (C ((1 : ℂ) / (2 : ℂ)) * a07988 ^ 1)
theorem ha07989 : a07989.IsHomogeneous 6 := by
  unfold a07989
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 6))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 6))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 6))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07988.pow 1)))

@[irreducible]
def a07990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00005 ^ 5)
theorem ha07990 : a07990.IsHomogeneous 5 := by
  unfold a07990
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00005.pow 5)))

@[irreducible]
def a07991 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a07990 ^ 1)
theorem ha07991 : a07991.IsHomogeneous 11 := by
  unfold a07991
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha07990.pow 1)))

@[irreducible]
def a07992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a07949 ^ 1 * a07991 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07949 ^ 1 * a07951 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a07951 ^ 1)
theorem ha07992 : a07992.IsHomogeneous 18 := by
  unfold a07992
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha07949.pow 1)).mul (ha07991.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07949.pow 1)).mul (ha07951.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha07951.pow 1)))

@[irreducible]
def a07993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1) + (C ((108 : ℂ) / (1 : ℂ)) * a00005 ^ 5)
theorem ha07993 : a07993.IsHomogeneous 5 := by
  unfold a07993
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (1 : ℂ))).mul (ha00005.pow 5)))

@[irreducible]
def a07994 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a07947 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a07993 ^ 1)
theorem ha07994 : a07994.IsHomogeneous 11 := by
  unfold a07994
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha07947.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha07993.pow 1)))

@[irreducible]
def a07995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a07949 ^ 1 * a07951 ^ 1 * a07994 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a07947 ^ 1 * a07992 ^ 1)
theorem ha07995 : a07995.IsHomogeneous 30 := by
  unfold a07995
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha07949.pow 1)).mul (ha07951.pow 1)).mul (ha07994.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha07947.pow 1)).mul (ha07992.pow 1)))

@[irreducible]
def a07996 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00002 ^ 2 * a00003 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00009 ^ 1)
theorem ha07996 : a07996.IsHomogeneous 8 := by
  unfold a07996
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 2)).mul (ha00003.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00009.pow 1)))

@[irreducible]
def a07997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a07977 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00001 ^ 1 * a00002 ^ 1 * a00004 ^ 1 * a07949 ^ 1 * a07996 ^ 1)
theorem ha07997 : a07997.IsHomogeneous 17 := by
  unfold a07997
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha07977.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha07949.pow 1)).mul (ha07996.pow 1)))

@[irreducible]
def a07998 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00013 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a07947 ^ 1)
theorem ha07998 : a07998.IsHomogeneous 12 := by
  unfold a07998
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00013.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha07947.pow 1)))

@[irreducible]
def a07999 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a07949 ^ 1 * a07977 ^ 1 * a07998 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a07947 ^ 1 * a07997 ^ 1)
theorem ha07999 : a07999.IsHomogeneous 29 := by
  unfold a07999
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha07949.pow 1)).mul (ha07977.pow 1)).mul (ha07998.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha07947.pow 1)).mul (ha07997.pow 1)))

@[irreducible]
def a08000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a07999 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a07995 ^ 1)
theorem ha08000 : a08000.IsHomogeneous 30 := by
  unfold a08000
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha07999.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha07995.pow 1)))

@[irreducible]
def a08001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 2 * a00005 ^ 1 * a00013 ^ 1 * a00125 ^ 1)
theorem ha08001 : a08001.IsHomogeneous 79 := by
  unfold a08001
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 2)).mul (ha00005.pow 1)).mul (ha00013.pow 1)).mul (ha00125.pow 1)))

@[irreducible]
def a08002 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a00008 ^ 1 * a00009 ^ 1) + (C ((-1 : ℂ) / (432 : ℂ)) * a00000 ^ 8 * a00001 ^ 2 * a00002 ^ 6 * a00003 ^ 4 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00008 ^ 2 * a00009 ^ 2) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 3 * a00005 ^ 3 * a00009 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00008 ^ 1)
theorem ha08002 : a08002.IsHomogeneous 24 := by
  unfold a08002
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00008.pow 1)).mul (ha00009.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (432 : ℂ))).mul (ha00000.pow 8)).mul (ha00001.pow 2)).mul (ha00002.pow 6)).mul (ha00003.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00008.pow 2)).mul (ha00009.pow 2))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 3)).mul (ha00005.pow 3)).mul (ha00009.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00008.pow 1)))

@[irreducible]
def a08003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00018 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00029 ^ 1)
theorem ha08003 : a08003.IsHomogeneous 24 := by
  unfold a08003
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00018.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00029.pow 1)))

@[irreducible]
def a08004 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a00019 ^ 1 * a00032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a08003 ^ 1)
theorem ha08004 : a08004.IsHomogeneous 30 := by
  unfold a08004
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00019.pow 1)).mul (ha00032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha08003.pow 1)))

@[irreducible]
def a08005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00029 ^ 1 * a00034 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00018 ^ 1 * a08004 ^ 1)
theorem ha08005 : a08005.IsHomogeneous 57 := by
  unfold a08005
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00029.pow 1)).mul (ha00034.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00018.pow 1)).mul (ha08004.pow 1)))

@[irreducible]
def a08006 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 2 * a00005 ^ 1 * a00013 ^ 1 * a00125 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08001 ^ 1)
theorem ha08006 : a08006.IsHomogeneous 79 := by
  unfold a08006
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 2)).mul (ha00005.pow 1)).mul (ha00013.pow 1)).mul (ha00125.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08001.pow 1)))

@[irreducible]
def a08007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a08001 ^ 1 * a08005 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00012 ^ 1 * a00018 ^ 1 * a00034 ^ 1 * a08006 ^ 1)
theorem ha08007 : a08007.IsHomogeneous 142 := by
  unfold a08007
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha08001.pow 1)).mul (ha08005.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00012.pow 1)).mul (ha00018.pow 1)).mul (ha00034.pow 1)).mul (ha08006.pow 1)))

@[irreducible]
def a08008 : Poly := (C ((-3 : ℂ) / (32 : ℂ)) * a00012 ^ 6 * a00014 ^ 6 * a00034 ^ 1 * a08002 ^ 1 * a08007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00013 ^ 2 * a00014 ^ 2 * a00018 ^ 1 * a00033 ^ 1 * a07958 ^ 1) + (C ((9 : ℂ) / (16 : ℂ)) * a00012 ^ 6 * a00013 ^ 1 * a00026 ^ 1 * a00033 ^ 1 * a00034 ^ 1 * a08001 ^ 1)
theorem ha08008 : a08008.IsHomogeneous 271 := by
  unfold a08008
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (32 : ℂ))).mul (ha00012.pow 6)).mul (ha00014.pow 6)).mul (ha00034.pow 1)).mul (ha08002.pow 1)).mul (ha08007.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00013.pow 2)).mul (ha00014.pow 2)).mul (ha00018.pow 1)).mul (ha00033.pow 1)).mul (ha07958.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (16 : ℂ))).mul (ha00012.pow 6)).mul (ha00013.pow 1)).mul (ha00026.pow 1)).mul (ha00033.pow 1)).mul (ha00034.pow 1)).mul (ha08001.pow 1)))

@[irreducible]
def a08009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00014 ^ 8 * a00034 ^ 3 * a00101 ^ 2 * a00103 ^ 2 * a00106 ^ 1 * a00124 ^ 1 * a08000 ^ 1) + (C ((1 : ℂ) / (2916 : ℂ)) * a00001 ^ 6 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 3 * a00018 ^ 1 * a00105 ^ 1 * a00107 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a07947 ^ 2 * a08008 ^ 1)
theorem ha08009 : a08009.IsHomogeneous 503 := by
  unfold a08009
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00014.pow 8)).mul (ha00034.pow 3)).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00106.pow 1)).mul (ha00124.pow 1)).mul (ha08000.pow 1)).add ((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2916 : ℂ))).mul (ha00001.pow 6)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 3)).mul (ha00018.pow 1)).mul (ha00105.pow 1)).mul (ha00107.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha07947.pow 2)).mul (ha08008.pow 1)))

@[irreducible]
def a08010 : Poly := (C ((-1 : ℂ) / (432 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00012 ^ 3) + (C ((1 : ℂ) / (144 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00012 ^ 1)
theorem ha08010 : a08010.IsHomogeneous 21 := by
  unfold a08010
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (432 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00006.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00012.pow 3))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00012.pow 1)))

@[irreducible]
def a08011 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00012 ^ 2 * a00014 ^ 2) + (C ((-1 : ℂ) / (93312 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 3 * a00004 ^ 6 * a00005 ^ 1 * a00017 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00014 ^ 3 * a08010 ^ 1)
theorem ha08011 : a08011.IsHomogeneous 40 := by
  unfold a08011
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (93312 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 6)).mul (ha00005.pow 1)).mul (ha00017.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha08010.pow 1)))

@[irreducible]
def a08012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a08011 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00103 ^ 1)
theorem ha08012 : a08012.IsHomogeneous 42 := by
  unfold a08012
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha08011.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)))

@[irreducible]
def a08013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00012 ^ 2 * a00014 ^ 2) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00014 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00009 ^ 1)
theorem ha08013 : a08013.IsHomogeneous 25 := by
  unfold a08013
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00014.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00009.pow 1)))

@[irreducible]
def a08014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a08013 ^ 1)
theorem ha08014 : a08014.IsHomogeneous 25 := by
  unfold a08014
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha08013.pow 1)))

@[irreducible]
def a08015 : Poly := (C ((-1 : ℂ) / (288 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 4 * a00005 ^ 2 * a00025 ^ 2 * a08014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00104 ^ 1 * a08013 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00009 ^ 1 * a00025 ^ 1 * a08012 ^ 1)
theorem ha08015 : a08015.IsHomogeneous 61 := by
  unfold a08015
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (288 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00025.pow 2)).mul (ha08014.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00104.pow 1)).mul (ha08013.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha08012.pow 1)))

@[irreducible]
def a08016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00119 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00012 ^ 2 * a00014 ^ 2) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 8 * a00003 ^ 3 * a00004 ^ 4 * a00005 ^ 1 * a00017 ^ 1)
theorem ha08016 : a08016.IsHomogeneous 31 := by
  unfold a08016
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00119.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 2))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 8)).mul (ha00003.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00017.pow 1)))

@[irreducible]
def a08017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00118 ^ 1 * a08016 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00120 ^ 1 * a08015 ^ 1)
theorem ha08017 : a08017.IsHomogeneous 92 := by
  unfold a08017
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00118.pow 1)).mul (ha08016.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00120.pow 1)).mul (ha08015.pow 1)))

@[irreducible]
def a08018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08013 ^ 1)
theorem ha08018 : a08018.IsHomogeneous 25 := by
  unfold a08018
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08013.pow 1)))

@[irreducible]
def a08019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a08011 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00025 ^ 1 * a08018 ^ 1)
theorem ha08019 : a08019.IsHomogeneous 46 := by
  unfold a08019
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha08011.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00025.pow 1)).mul (ha08018.pow 1)))

@[irreducible]
def a08020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a08019 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a08011 ^ 1)
theorem ha08020 : a08020.IsHomogeneous 88 := by
  unfold a08020
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha08019.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha08011.pow 1)))

@[irreducible]
def a08021 : Poly := (C ((-1 : ℂ) / (108 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00025 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a08013 ^ 1)
theorem ha08021 : a08021.IsHomogeneous 31 := by
  unfold a08021
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00025.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha08013.pow 1)))

@[irreducible]
def a08022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00122 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a08021 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00122 ^ 1 * a08011 ^ 1)
theorem ha08022 : a08022.IsHomogeneous 73 := by
  unfold a08022
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00122.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha08021.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00122.pow 1)).mul (ha08011.pow 1)))

@[irreducible]
def a08023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a08017 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 5 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00032 ^ 1 * a08022 ^ 1) + (C ((162 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00025 ^ 1 * a08020 ^ 1)
theorem ha08023 : a08023.IsHomogeneous 95 := by
  unfold a08023
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha08017.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00032.pow 1)).mul (ha08022.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((162 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00025.pow 1)).mul (ha08020.pow 1)))

@[irreducible]
def a08024 : Poly := (C ((-1 : ℂ) / (432 : ℂ)) * a00005 ^ 1 * a00103 ^ 1 * a00110 ^ 1 * a00123 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a00123 ^ 1 * a08011 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00106 ^ 1 * a08023 ^ 1)
theorem ha08024 : a08024.IsHomogeneous 155 := by
  unfold a08024
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (432 : ℂ))).mul (ha00005.pow 1)).mul (ha00103.pow 1)).mul (ha00110.pow 1)).mul (ha00123.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha00123.pow 1)).mul (ha08011.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha08023.pow 1)))

@[irreducible]
def a08025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3) + (C ((432 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00012 ^ 2)
theorem ha08025 : a08025.IsHomogeneous 15 := by
  unfold a08025
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).add (((isHomogeneous_C (σ := Fin 6) ((432 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00012.pow 2)))

@[irreducible]
def a08026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00009 ^ 1 * a08025 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00012 ^ 1)
theorem ha08026 : a08026.IsHomogeneous 22 := by
  unfold a08026
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha08025.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a08027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a08026 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00109 ^ 1)
theorem ha08027 : a08027.IsHomogeneous 24 := by
  unfold a08027
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha08026.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00109.pow 1)))

@[irreducible]
def a08028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3) + (C ((3240 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00012 ^ 2)
theorem ha08028 : a08028.IsHomogeneous 15 := by
  unfold a08028
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).add (((isHomogeneous_C (σ := Fin 6) ((3240 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00012.pow 2)))

@[irreducible]
def a08029 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00009 ^ 1 * a08028 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00012 ^ 1)
theorem ha08029 : a08029.IsHomogeneous 22 := by
  unfold a08029
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha08028.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a08030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00111 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08029 ^ 1)
theorem ha08030 : a08030.IsHomogeneous 22 := by
  unfold a08030
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00111.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08029.pow 1)))

@[irreducible]
def a08031 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00107 ^ 1 * a08030 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00012 ^ 1 * a08027 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00107 ^ 1 * a08027 ^ 1)
theorem ha08031 : a08031.IsHomogeneous 30 := by
  unfold a08031
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00107.pow 1)).mul (ha08030.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00012.pow 1)).mul (ha08027.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00107.pow 1)).mul (ha08027.pow 1)))

@[irreducible]
def a08032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00109 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00005 ^ 2 * a08026 ^ 1)
theorem ha08032 : a08032.IsHomogeneous 24 := by
  unfold a08032
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00109.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00005.pow 2)).mul (ha08026.pow 1)))

@[irreducible]
def a08033 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3) + (C ((9720 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00012 ^ 2)
theorem ha08033 : a08033.IsHomogeneous 15 := by
  unfold a08033
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).add (((isHomogeneous_C (σ := Fin 6) ((9720 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00012.pow 2)))

@[irreducible]
def a08034 : Poly := (C ((-1 : ℂ) / (144 : ℂ)) * a00005 ^ 3 * a00109 ^ 1 * a00110 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a08032 ^ 1)
theorem ha08034 : a08034.IsHomogeneous 42 := by
  unfold a08034
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (144 : ℂ))).mul (ha00005.pow 3)).mul (ha00109.pow 1)).mul (ha00110.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha08032.pow 1)))

@[irreducible]
def a08035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 4 * a00009 ^ 1 * a00012 ^ 2) + (C ((1 : ℂ) / (1080 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 1 * a00009 ^ 1) + (C ((1 : ℂ) / (6480 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00012 ^ 1)
theorem ha08035 : a08035.IsHomogeneous 22 := by
  unfold a08035
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 4)).mul (ha00009.pow 1)).mul (ha00012.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1080 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00009.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6480 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a08036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00114 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a08035 ^ 1)
theorem ha08036 : a08036.IsHomogeneous 22 := by
  unfold a08036
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00114.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha08035.pow 1)))

@[irreducible]
def a08037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00115 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1)
theorem ha08037 : a08037.IsHomogeneous 13 := by
  unfold a08037
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00115.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)))

@[irreducible]
def a08038 : Poly := (C ((-1 : ℂ) / (324 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00107 ^ 1 * a08037 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a08036 ^ 1)
theorem ha08038 : a08038.IsHomogeneous 28 := by
  unfold a08038
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (324 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00107.pow 1)).mul (ha08037.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha08036.pow 1)))

@[irreducible]
def a08039 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00114 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a08035 ^ 1)
theorem ha08039 : a08039.IsHomogeneous 22 := by
  unfold a08039
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00114.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha08035.pow 1)))

@[irreducible]
def a08040 : Poly := (C ((-1 : ℂ) / (144 : ℂ)) * a00005 ^ 3 * a00110 ^ 1 * a00114 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a08039 ^ 1)
theorem ha08040 : a08040.IsHomogeneous 40 := by
  unfold a08040
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (144 : ℂ))).mul (ha00005.pow 3)).mul (ha00110.pow 1)).mul (ha00114.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha08039.pow 1)))

@[irreducible]
def a08041 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a00114 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a08040 ^ 1)
theorem ha08041 : a08041.IsHomogeneous 40 := by
  unfold a08041
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha00114.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha08040.pow 1)))

@[irreducible]
def a08042 : Poly := (C ((-216 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a08041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08034 ^ 1)
theorem ha08042 : a08042.IsHomogeneous 42 := by
  unfold a08042
  exact ((((isHomogeneous_C (σ := Fin 6) ((-216 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha08041.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08034.pow 1)))

@[irreducible]
def a08043 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1 * a00104 ^ 1 * a08013 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00025 ^ 1 * a08012 ^ 1)
theorem ha08043 : a08043.IsHomogeneous 55 := by
  unfold a08043
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00104.pow 1)).mul (ha08013.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00025.pow 1)).mul (ha08012.pow 1)))

@[irreducible]
def a08044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00120 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a08016 ^ 1)
theorem ha08044 : a08044.IsHomogeneous 31 := by
  unfold a08044
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00120.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha08016.pow 1)))

@[irreducible]
def a08045 : Poly := (C ((-1 : ℂ) / (432 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a08044 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08011 ^ 1)
theorem ha08045 : a08045.IsHomogeneous 40 := by
  unfold a08045
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (432 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha08044.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08011.pow 1)))

@[irreducible]
def a08046 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a08045 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00032 ^ 1 * a08018 ^ 1)
theorem ha08046 : a08046.IsHomogeneous 46 := by
  unfold a08046
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha08045.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00032.pow 1)).mul (ha08018.pow 1)))

@[irreducible]
def a08047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07833 ^ 1 * a08043 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a08046 ^ 1)
theorem ha08047 : a08047.IsHomogeneous 103 := by
  unfold a08047
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07833.pow 1)).mul (ha08043.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha08046.pow 1)))

@[irreducible]
def a08048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a00117 ^ 1 * a08047 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00105 ^ 1 * a07833 ^ 1 * a08042 ^ 1)
theorem ha08048 : a08048.IsHomogeneous 145 := by
  unfold a08048
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha00117.pow 1)).mul (ha08047.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00105.pow 1)).mul (ha07833.pow 1)).mul (ha08042.pow 1)))

@[irreducible]
def a08049 : Poly := (C ((-144 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a08031 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00110 ^ 1 * a00112 ^ 1)
theorem ha08049 : a08049.IsHomogeneous 48 := by
  unfold a08049
  exact ((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha08031.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00110.pow 1)).mul (ha00112.pow 1)))

@[irreducible]
def a08050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07834 ^ 1)
theorem ha08050 : a08050.IsHomogeneous 13 := by
  unfold a08050
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00115.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07834.pow 1)))

@[irreducible]
def a08051 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00107 ^ 1 * a08050 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a08027 ^ 1)
theorem ha08051 : a08051.IsHomogeneous 30 := by
  unfold a08051
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00107.pow 1)).mul (ha08050.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha08027.pow 1)))

@[irreducible]
def a08052 : Poly := (C ((-216 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a08051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00110 ^ 1 * a07835 ^ 1)
theorem ha08052 : a08052.IsHomogeneous 48 := by
  unfold a08052
  exact ((((isHomogeneous_C (σ := Fin 6) ((-216 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha08051.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00110.pow 1)).mul (ha07835.pow 1)))

@[irreducible]
def a08053 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3) + (C ((1 : ℂ) / (1 : ℂ)) * a08033 ^ 1)
theorem ha08053 : a08053.IsHomogeneous 15 := by
  unfold a08053
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08033.pow 1)))

@[irreducible]
def a08054 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00109 ^ 1 * a08053 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07836 ^ 1 * a08032 ^ 1)
theorem ha08054 : a08054.IsHomogeneous 39 := by
  unfold a08054
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00109.pow 1)).mul (ha08053.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07836.pow 1)).mul (ha08032.pow 1)))

@[irreducible]
def a08055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00107 ^ 1 * a08054 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a08052 ^ 1)
theorem ha08055 : a08055.IsHomogeneous 48 := by
  unfold a08055
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00107.pow 1)).mul (ha08054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha08052.pow 1)))

@[irreducible]
def a08056 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a08055 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08049 ^ 1)
theorem ha08056 : a08056.IsHomogeneous 48 := by
  unfold a08056
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha08055.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08049.pow 1)))

@[irreducible]
def a08057 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00005 ^ 3 * a00110 ^ 1 * a00116 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a08038 ^ 1)
theorem ha08057 : a08057.IsHomogeneous 46 := by
  unfold a08057
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00005.pow 3)).mul (ha00110.pow 1)).mul (ha00116.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha08038.pow 1)))

@[irreducible]
def a08058 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00114 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08039 ^ 1)
theorem ha08058 : a08058.IsHomogeneous 22 := by
  unfold a08058
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00114.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08039.pow 1)))

@[irreducible]
def a08059 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08057 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00107 ^ 1 * a08058 ^ 1)
theorem ha08059 : a08059.IsHomogeneous 46 := by
  unfold a08059
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08057.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00107.pow 1)).mul (ha08058.pow 1)))

@[irreducible]
def a08060 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a08059 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08057 ^ 1)
theorem ha08060 : a08060.IsHomogeneous 46 := by
  unfold a08060
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha08059.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08057.pow 1)))

@[irreducible]
def a08061 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07840 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08060 ^ 1)
theorem ha08061 : a08061.IsHomogeneous 46 := by
  unfold a08061
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07840.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08060.pow 1)))

@[irreducible]
def a08062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00107 ^ 1 * a08040 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a08061 ^ 1)
theorem ha08062 : a08062.IsHomogeneous 46 := by
  unfold a08062
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00107.pow 1)).mul (ha08040.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha08061.pow 1)))

@[irreducible]
def a08063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a08062 ^ 1) + (C ((1 : ℂ) / (124416 : ℂ)) * a08056 ^ 1)
theorem ha08063 : a08063.IsHomogeneous 48 := by
  unfold a08063
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha08062.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (124416 : ℂ))).mul (ha08056.pow 1)))

@[irreducible]
def a08064 : Poly := (C ((-288 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a08063 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07842 ^ 1 * a08043 ^ 1)
theorem ha08064 : a08064.IsHomogeneous 103 := by
  unfold a08064
  exact ((((isHomogeneous_C (σ := Fin 6) ((-288 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha08063.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07842.pow 1)).mul (ha08043.pow 1)))

@[irreducible]
def a08065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a08064 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00107 ^ 1 * a08048 ^ 1)
theorem ha08065 : a08065.IsHomogeneous 158 := by
  unfold a08065
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha08064.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00107.pow 1)).mul (ha08048.pow 1)))

@[irreducible]
def a08066 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a07843 ^ 1 * a08024 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00106 ^ 1 * a00123 ^ 1 * a08065 ^ 1)
theorem ha08066 : a08066.IsHomogeneous 315 := by
  unfold a08066
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha07843.pow 1)).mul (ha08024.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha00123.pow 1)).mul (ha08065.pow 1)))

@[irreducible]
def a08067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a00117 ^ 1 * a08043 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00105 ^ 1 * a08042 ^ 1)
theorem ha08067 : a08067.IsHomogeneous 97 := by
  unfold a08067
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha00117.pow 1)).mul (ha08043.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00105.pow 1)).mul (ha08042.pow 1)))

@[irreducible]
def a08068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00120 ^ 1 * a08011 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a08016 ^ 1)
theorem ha08068 : a08068.IsHomogeneous 73 := by
  unfold a08068
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00120.pow 1)).mul (ha08011.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha08016.pow 1)))

@[irreducible]
def a08069 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00005 ^ 3 * a00103 ^ 1 * a00110 ^ 1 * a00120 ^ 1 * a00123 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00103 ^ 1 * a00106 ^ 1 * a00120 ^ 1 * a08023 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a00123 ^ 1 * a08068 ^ 1)
theorem ha08069 : a08069.IsHomogeneous 188 := by
  unfold a08069
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00005.pow 3)).mul (ha00103.pow 1)).mul (ha00110.pow 1)).mul (ha00120.pow 1)).mul (ha00123.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha00120.pow 1)).mul (ha08023.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha00123.pow 1)).mul (ha08068.pow 1)))

@[irreducible]
def a08070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08018 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00032 ^ 1)
theorem ha08070 : a08070.IsHomogeneous 25 := by
  unfold a08070
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08018.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a08071 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00025 ^ 2 * a08070 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a08045 ^ 1) + (C ((1 : ℂ) / (81 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00009 ^ 1 * a00032 ^ 1 * a08018 ^ 1)
theorem ha08071 : a08071.IsHomogeneous 52 := by
  unfold a08071
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00025.pow 2)).mul (ha08070.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha08045.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (81 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00009.pow 1)).mul (ha00032.pow 1)).mul (ha08018.pow 1)))

@[irreducible]
def a08072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00120 ^ 1 * a08071 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07845 ^ 1 * a08016 ^ 1)
theorem ha08072 : a08072.IsHomogeneous 85 := by
  unfold a08072
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00120.pow 1)).mul (ha08071.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07845.pow 1)).mul (ha08016.pow 1)))

@[irreducible]
def a08073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00118 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a08015 ^ 1)
theorem ha08073 : a08073.IsHomogeneous 61 := by
  unfold a08073
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00118.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha08015.pow 1)))

@[irreducible]
def a08074 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08072 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a07847 ^ 1 * a08073 ^ 1)
theorem ha08074 : a08074.IsHomogeneous 87 := by
  unfold a08074
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08072.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha07847.pow 1)).mul (ha08073.pow 1)))

@[irreducible]
def a08075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00120 ^ 1 * a08019 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00121 ^ 1 * a08016 ^ 1)
theorem ha08075 : a08075.IsHomogeneous 79 := by
  unfold a08075
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00120.pow 1)).mul (ha08019.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00121.pow 1)).mul (ha08016.pow 1)))

@[irreducible]
def a08076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08013 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00032 ^ 1)
theorem ha08076 : a08076.IsHomogeneous 25 := by
  unfold a08076
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08013.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a08077 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00000 ^ 4 * a00003 ^ 2 * a00025 ^ 1 * a08076 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a08016 ^ 1)
theorem ha08077 : a08077.IsHomogeneous 37 := by
  unfold a08077
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 4)).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha08076.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha08016.pow 1)))

@[irreducible]
def a08078 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a07850 ^ 1 * a08011 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a08077 ^ 1)
theorem ha08078 : a08078.IsHomogeneous 79 := by
  unfold a08078
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha07850.pow 1)).mul (ha08011.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha08077.pow 1)))

@[irreducible]
def a08079 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08075 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08078 ^ 1)
theorem ha08079 : a08079.IsHomogeneous 79 := by
  unfold a08079
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08075.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08078.pow 1)))

@[irreducible]
def a08080 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00120 ^ 1 * a00122 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00120 ^ 1 * a08021 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a08016 ^ 1)
theorem ha08080 : a08080.IsHomogeneous 62 := by
  unfold a08080
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00120.pow 1)).mul (ha00122.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00120.pow 1)).mul (ha08021.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha08016.pow 1)))

@[irreducible]
def a08081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a08011 ^ 1)
theorem ha08081 : a08081.IsHomogeneous 42 := by
  unfold a08081
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha08011.pow 1)))

@[irreducible]
def a08082 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00122 ^ 1 * a08011 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a08021 ^ 1)
theorem ha08082 : a08082.IsHomogeneous 73 := by
  unfold a08082
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00122.pow 1)).mul (ha08011.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha08021.pow 1)))

@[irreducible]
def a08083 : Poly := (C ((-1 : ℂ) / (432 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a08080 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08082 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00058 ^ 1 * a08081 ^ 1)
theorem ha08083 : a08083.IsHomogeneous 73 := by
  unfold a08083
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (432 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha08080.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08082.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00058.pow 1)).mul (ha08081.pow 1)))

@[irreducible]
def a08084 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 2 * a00004 ^ 1 * a00032 ^ 1 * a08083 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08074 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00025 ^ 1 * a08079 ^ 1)
theorem ha08084 : a08084.IsHomogeneous 87 := by
  unfold a08084
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00032.pow 1)).mul (ha08083.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08074.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00025.pow 1)).mul (ha08079.pow 1)))

@[irreducible]
def a08085 : Poly := (C ((-1 : ℂ) / (432 : ℂ)) * a00005 ^ 3 * a00103 ^ 1 * a00110 ^ 1 * a07853 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00106 ^ 1 * a07853 ^ 1 * a08011 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00103 ^ 1 * a00106 ^ 1 * a08084 ^ 1)
theorem ha08085 : a08085.IsHomogeneous 147 := by
  unfold a08085
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (432 : ℂ))).mul (ha00005.pow 3)).mul (ha00103.pow 1)).mul (ha00110.pow 1)).mul (ha07853.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00106.pow 1)).mul (ha07853.pow 1)).mul (ha08011.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha08084.pow 1)))

@[irreducible]
def a08086 : Poly := (C ((-1 : ℂ) / (144 : ℂ)) * a00005 ^ 3 * a00110 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00106 ^ 1)
theorem ha08086 : a08086.IsHomogeneous 18 := by
  unfold a08086
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (144 : ℂ))).mul (ha00005.pow 3)).mul (ha00110.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)))

@[irreducible]
def a08087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00103 ^ 1 * a00106 ^ 1 * a08023 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a08086 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00106 ^ 1 * a00123 ^ 1 * a08011 ^ 1)
theorem ha08087 : a08087.IsHomogeneous 157 := by
  unfold a08087
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha08023.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha08086.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00106.pow 1)).mul (ha00123.pow 1)).mul (ha08011.pow 1)))

@[irreducible]
def a08088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00106 ^ 1 * a08085 ^ 1) + (C ((1 : ℂ) / (432 : ℂ)) * a00004 ^ 1 * a00106 ^ 1 * a08069 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00103 ^ 1 * a08087 ^ 1)
theorem ha08088 : a08088.IsHomogeneous 207 := by
  unfold a08088
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha08085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00004.pow 1)).mul (ha00106.pow 1)).mul (ha08069.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00103.pow 1)).mul (ha08087.pow 1)))

@[irreducible]
def a08089 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00123 ^ 1 * a08088 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a07854 ^ 1 * a08024 ^ 1)
theorem ha08089 : a08089.IsHomogeneous 304 := by
  unfold a08089
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00123.pow 1)).mul (ha08088.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha07854.pow 1)).mul (ha08024.pow 1)))

@[irreducible]
def a08090 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a07854 ^ 1 * a08067 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00117 ^ 1 * a08089 ^ 1)
theorem ha08090 : a08090.IsHomogeneous 383 := by
  unfold a08090
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha07854.pow 1)).mul (ha08067.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha08089.pow 1)))

@[irreducible]
def a08091 : Poly := (C ((-16 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00105 ^ 1 * a00107 ^ 1 * a08090 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a08066 ^ 1)
theorem ha08091 : a08091.IsHomogeneous 454 := by
  unfold a08091
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha00107.pow 1)).mul (ha08090.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha08066.pow 1)))

@[irreducible]
def a08092 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a00117 ^ 1 * a08024 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a08067 ^ 1)
theorem ha08092 : a08092.IsHomogeneous 236 := by
  unfold a08092
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha08024.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha08067.pow 1)))

@[irreducible]
def a08093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00102 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a08010 ^ 1)
theorem ha08093 : a08093.IsHomogeneous 24 := by
  unfold a08093
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00102.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha08010.pow 1)))

@[irreducible]
def a08094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00102 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a08010 ^ 1)
theorem ha08094 : a08094.IsHomogeneous 24 := by
  unfold a08094
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00102.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha08010.pow 1)))

@[irreducible]
def a08095 : Poly := (C ((-1 : ℂ) / (46656 : ℂ)) * a00000 ^ 8 * a00001 ^ 8 * a00002 ^ 8 * a00003 ^ 4 * a00004 ^ 4 * a00005 ^ 2 * a00012 ^ 4) + (C ((-1 : ℂ) / (46656 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 3 * a00004 ^ 6 * a00005 ^ 1 * a08093 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00009 ^ 2 * a00102 ^ 1 * a08010 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 3 * a00005 ^ 1 * a00009 ^ 1 * a00012 ^ 6) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00009 ^ 1 * a00012 ^ 2 * a08094 ^ 1)
theorem ha08095 : a08095.IsHomogeneous 58 := by
  unfold a08095
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (46656 : ℂ))).mul (ha00000.pow 8)).mul (ha00001.pow 8)).mul (ha00002.pow 8)).mul (ha00003.pow 4)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00012.pow 4)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (46656 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 6)).mul (ha00005.pow 1)).mul (ha08093.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00009.pow 2)).mul (ha00102.pow 1)).mul (ha08010.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 3)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00012.pow 6))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00009.pow 1)).mul (ha00012.pow 2)).mul (ha08094.pow 1)))

@[irreducible]
def a08096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a08043 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a08095 ^ 1)
theorem ha08096 : a08096.IsHomogeneous 115 := by
  unfold a08096
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha08043.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha08095.pow 1)))

@[irreducible]
def a08097 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a00124 ^ 1 * a08023 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a08096 ^ 1)
theorem ha08097 : a08097.IsHomogeneous 212 := by
  unfold a08097
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha08023.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha08096.pow 1)))

@[irreducible]
def a08098 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00106 ^ 1 * a00117 ^ 1 * a08097 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a08092 ^ 1)
theorem ha08098 : a08098.IsHomogeneous 296 := by
  unfold a08098
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha00117.pow 1)).mul (ha08097.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha08092.pow 1)))

@[irreducible]
def a08099 : Poly := (C ((-5 : ℂ) / (432 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00119 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08094 ^ 1)
theorem ha08099 : a08099.IsHomogeneous 24 := by
  unfold a08099
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (432 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00119.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08094.pow 1)))

@[irreducible]
def a08100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a08010 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00102 ^ 1)
theorem ha08100 : a08100.IsHomogeneous 24 := by
  unfold a08100
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha08010.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00102.pow 1)))

@[irreducible]
def a08101 : Poly := (C ((-1 : ℂ) / (108 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00119 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08100 ^ 1)
theorem ha08101 : a08101.IsHomogeneous 24 := by
  unfold a08101
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (108 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00119.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08100.pow 1)))

@[irreducible]
def a08102 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00009 ^ 1 * a00012 ^ 2 * a08101 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 2 * a00119 ^ 1 * a08094 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 9 * a00001 ^ 8 * a00003 ^ 3 * a00004 ^ 4 * a00005 ^ 1 * a08099 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00000 ^ 8 * a00001 ^ 4 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 4)
theorem ha08102 : a08102.IsHomogeneous 49 := by
  unfold a08102
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00009.pow 1)).mul (ha00012.pow 2)).mul (ha08101.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 2)).mul (ha00119.pow 1)).mul (ha08094.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 8)).mul (ha00003.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha08099.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 8)).mul (ha00001.pow 4)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 4)))

@[irreducible]
def a08103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07858 ^ 1 * a08043 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00105 ^ 1 * a08102 ^ 1)
theorem ha08103 : a08103.IsHomogeneous 104 := by
  unfold a08103
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07858.pow 1)).mul (ha08043.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00105.pow 1)).mul (ha08102.pow 1)))

@[irreducible]
def a08104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a08046 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a07833 ^ 1 * a08043 ^ 1)
theorem ha08104 : a08104.IsHomogeneous 103 := by
  unfold a08104
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha08046.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha07833.pow 1)).mul (ha08043.pow 1)))

@[irreducible]
def a08105 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a07833 ^ 1 * a08095 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00124 ^ 1 * a08104 ^ 1)
theorem ha08105 : a08105.IsHomogeneous 163 := by
  unfold a08105
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha07833.pow 1)).mul (ha08095.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00124.pow 1)).mul (ha08104.pow 1)))

@[irreducible]
def a08106 : Poly := (C ((-216 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a08105 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00105 ^ 1 * a08103 ^ 1)
theorem ha08106 : a08106.IsHomogeneous 164 := by
  unfold a08106
  exact ((((isHomogeneous_C (σ := Fin 6) ((-216 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha08105.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha08103.pow 1)))

@[irreducible]
def a08107 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a08106 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a07859 ^ 1 * a08023 ^ 1)
theorem ha08107 : a08107.IsHomogeneous 261 := by
  unfold a08107
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha08106.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha07859.pow 1)).mul (ha08023.pow 1)))

@[irreducible]
def a08108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a07853 ^ 1 * a08023 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00123 ^ 1 * a08084 ^ 1)
theorem ha08108 : a08108.IsHomogeneous 184 := by
  unfold a08108
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha07853.pow 1)).mul (ha08023.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00123.pow 1)).mul (ha08084.pow 1)))

@[irreducible]
def a08109 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a08108 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a07853 ^ 1 * a08023 ^ 1)
theorem ha08109 : a08109.IsHomogeneous 184 := by
  unfold a08109
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha08108.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha07853.pow 1)).mul (ha08023.pow 1)))

@[irreducible]
def a08110 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a08109 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a07853 ^ 1 * a08096 ^ 1)
theorem ha08110 : a08110.IsHomogeneous 299 := by
  unfold a08110
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha08109.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha07853.pow 1)).mul (ha08096.pow 1)))

@[irreducible]
def a08111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00105 ^ 1 * a08110 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00004 ^ 1 * a00123 ^ 1 * a08107 ^ 1)
theorem ha08111 : a08111.IsHomogeneous 359 := by
  unfold a08111
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha08110.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00004.pow 1)).mul (ha00123.pow 1)).mul (ha08107.pow 1)))

@[irreducible]
def a08112 : Poly := (C ((-96 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00106 ^ 1 * a00117 ^ 1 * a00124 ^ 1 * a08111 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07860 ^ 1 * a08098 ^ 1)
theorem ha08112 : a08112.IsHomogeneous 503 := by
  unfold a08112
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha00117.pow 1)).mul (ha00124.pow 1)).mul (ha08111.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07860.pow 1)).mul (ha08098.pow 1)))

@[irreducible]
def a08113 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a08013 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00104 ^ 1 * a08011 ^ 1)
theorem ha08113 : a08113.IsHomogeneous 67 := by
  unfold a08113
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha08013.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00104.pow 1)).mul (ha08011.pow 1)))

@[irreducible]
def a08114 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00103 ^ 1 * a08011 ^ 1) + (C ((1 : ℂ) / (432 : ℂ)) * a00000 ^ 3 * a00002 ^ 6 * a00003 ^ 3 * a00005 ^ 1 * a00104 ^ 2 * a08013 ^ 1) + (C ((1 : ℂ) / (864 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00025 ^ 1 * a08113 ^ 1)
theorem ha08114 : a08114.IsHomogeneous 88 := by
  unfold a08114
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00103.pow 1)).mul (ha08011.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 6)).mul (ha00003.pow 3)).mul (ha00005.pow 1)).mul (ha00104.pow 2)).mul (ha08013.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (864 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00025.pow 1)).mul (ha08113.pow 1)))

@[irreducible]
def a08115 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07861 ^ 1 * a08023 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a08114 ^ 1)
theorem ha08115 : a08115.IsHomogeneous 185 := by
  unfold a08115
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07861.pow 1)).mul (ha08023.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha08114.pow 1)))

@[irreducible]
def a08116 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a08046 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a07833 ^ 1 * a08011 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a07833 ^ 1 * a08023 ^ 1)
theorem ha08116 : a08116.IsHomogeneous 185 := by
  unfold a08116
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha08046.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha07833.pow 1)).mul (ha08011.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha07833.pow 1)).mul (ha08023.pow 1)))

@[irreducible]
def a08117 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a00120 ^ 1 * a08023 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00123 ^ 1 * a08016 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00120 ^ 1 * a00123 ^ 1 * a08043 ^ 1)
theorem ha08117 : a08117.IsHomogeneous 183 := by
  unfold a08117
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha00120.pow 1)).mul (ha08023.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha08016.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00120.pow 1)).mul (ha00123.pow 1)).mul (ha08043.pow 1)))

@[irreducible]
def a08118 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a08084 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a07853 ^ 1 * a08043 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a07853 ^ 1 * a08011 ^ 1)
theorem ha08118 : a08118.IsHomogeneous 184 := by
  unfold a08118
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha08084.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha07853.pow 1)).mul (ha08043.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha07853.pow 1)).mul (ha08011.pow 1)))

@[irreducible]
def a08119 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a08118 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a08117 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a08116 ^ 1)
theorem ha08119 : a08119.IsHomogeneous 187 := by
  unfold a08119
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha08118.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha08117.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha08116.pow 1)))

@[irreducible]
def a08120 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a08119 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a07862 ^ 1 * a08095 ^ 1)
theorem ha08120 : a08120.IsHomogeneous 247 := by
  unfold a08120
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha08119.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha07862.pow 1)).mul (ha08095.pow 1)))

@[irreducible]
def a08121 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00004 ^ 1 * a00123 ^ 1 * a08115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 6 * a08120 ^ 1)
theorem ha08121 : a08121.IsHomogeneous 283 := by
  unfold a08121
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00004.pow 1)).mul (ha00123.pow 1)).mul (ha08115.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 6)).mul (ha08120.pow 1)))

@[irreducible]
def a08122 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a08121 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a07863 ^ 1 * a08043 ^ 1)
theorem ha08122 : a08122.IsHomogeneous 340 := by
  unfold a08122
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha08121.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha07863.pow 1)).mul (ha08043.pow 1)))

@[irreducible]
def a08123 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a08023 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a08011 ^ 1)
theorem ha08123 : a08123.IsHomogeneous 137 := by
  unfold a08123
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha08023.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha08011.pow 1)))

@[irreducible]
def a08124 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00123 ^ 1 * a08122 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00105 ^ 1 * a07863 ^ 1 * a08123 ^ 1)
theorem ha08124 : a08124.IsHomogeneous 479 := by
  unfold a08124
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha08122.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00105.pow 1)).mul (ha07863.pow 1)).mul (ha08123.pow 1)))

@[irreducible]
def a08125 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00106 ^ 1 * a00117 ^ 1 * a00124 ^ 1 * a08124 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07863 ^ 1 * a08098 ^ 1)
theorem ha08125 : a08125.IsHomogeneous 581 := by
  unfold a08125
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00106.pow 1)).mul (ha00117.pow 1)).mul (ha00124.pow 1)).mul (ha08124.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07863.pow 1)).mul (ha08098.pow 1)))

@[irreducible]
def a08126 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 6 * a00124 ^ 2 * a08091 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00014 ^ 6 * a00103 ^ 1 * a00106 ^ 1 * a00107 ^ 1 * a08112 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00106 ^ 1 * a00107 ^ 1 * a08125 ^ 1)
theorem ha08126 : a08126.IsHomogeneous 610 := by
  unfold a08126
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 6)).mul (ha00124.pow 2)).mul (ha08091.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00014.pow 6)).mul (ha00103.pow 1)).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha08112.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00106.pow 1)).mul (ha00107.pow 1)).mul (ha08125.pow 1)))

@[irreducible]
def a08127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00012 ^ 2) + (C ((1 : ℂ) / (1080 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3)
theorem ha08127 : a08127.IsHomogeneous 15 := by
  unfold a08127
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00012.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1080 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a08128 : Poly := (C ((-1 : ℂ) / (2160 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00012 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00014 ^ 1 * a08127 ^ 1)
theorem ha08128 : a08128.IsHomogeneous 22 := by
  unfold a08128
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2160 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00012.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha08127.pow 1)))

@[irreducible]
def a08129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00118 ^ 1 * a08128 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a07865 ^ 1 * a08015 ^ 1)
theorem ha08129 : a08129.IsHomogeneous 83 := by
  unfold a08129
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00118.pow 1)).mul (ha08128.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha07865.pow 1)).mul (ha08015.pow 1)))

@[irreducible]
def a08130 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a00002 ^ 4 * a00003 ^ 1 * a00012 ^ 1 * a08082 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a08129 ^ 1)
theorem ha08130 : a08130.IsHomogeneous 84 := by
  unfold a08130
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00012.pow 1)).mul (ha08082.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha08129.pow 1)))

@[irreducible]
def a08131 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00123 ^ 1 * a08130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a07866 ^ 1 * a08023 ^ 1)
theorem ha08131 : a08131.IsHomogeneous 181 := by
  unfold a08131
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00123.pow 1)).mul (ha08130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha07866.pow 1)).mul (ha08023.pow 1)))

@[irreducible]
def a08132 : Poly := (C ((-144 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00103 ^ 1 * a00105 ^ 1 * a00106 ^ 1 * a00124 ^ 1 * a07864 ^ 1 * a08131 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07867 ^ 1 * a08126 ^ 1)
theorem ha08132 : a08132.IsHomogeneous 713 := by
  unfold a08132
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00106.pow 1)).mul (ha00124.pow 1)).mul (ha07864.pow 1)).mul (ha08131.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07867.pow 1)).mul (ha08126.pow 1)))

@[irreducible]
def a08133 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00106 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a07864 ^ 1 * a07867 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a08132 ^ 1)
theorem ha08133 : a08133.IsHomogeneous 719 := by
  unfold a08133
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00106.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha07864.pow 1)).mul (ha07867.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha08132.pow 1)))

@[irreducible]
def a08134 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00017 ^ 1 * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2)
theorem ha08134 : a08134.IsHomogeneous 19 := by
  unfold a08134
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00017.pow 1)).mul (ha07889.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a08135 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a08134 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 3 * a07889 ^ 1)
theorem ha08135 : a08135.IsHomogeneous 30 := by
  unfold a08135
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha08134.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha07889.pow 1)))

@[irreducible]
def a08136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08135 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07870 ^ 1 * a07889 ^ 1)
theorem ha08136 : a08136.IsHomogeneous 36 := by
  unfold a08136
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08135.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07870.pow 1)).mul (ha07889.pow 1)))

@[irreducible]
def a08137 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00032 ^ 1 * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2)
theorem ha08137 : a08137.IsHomogeneous 19 := by
  unfold a08137
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00032.pow 1)).mul (ha07889.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a08138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 1 * a07871 ^ 1 * a08137 ^ 1) + (C ((108 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00025 ^ 1 * a08136 ^ 1)
theorem ha08138 : a08138.IsHomogeneous 43 := by
  unfold a08138
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha07871.pow 1)).mul (ha08137.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00025.pow 1)).mul (ha08136.pow 1)))

@[irreducible]
def a08139 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1)
theorem ha08139 : a08139.IsHomogeneous 6 := by
  unfold a08139
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)))

@[irreducible]
def a08140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08139 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00005 ^ 6)
theorem ha08140 : a08140.IsHomogeneous 6 := by
  unfold a08140
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)))

@[irreducible]
def a08141 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a07873 ^ 1 * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08140 ^ 1)
theorem ha08141 : a08141.IsHomogeneous 12 := by
  unfold a08141
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha07873.pow 1)).mul (ha07889.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08140.pow 1)))

@[irreducible]
def a08142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07872 ^ 1 * a08138 ^ 1) + (C ((324 : ℂ) / (1 : ℂ)) * a00000 ^ 2 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 6 * a00025 ^ 2 * a07873 ^ 1 * a08141 ^ 1)
theorem ha08142 : a08142.IsHomogeneous 86 := by
  unfold a08142
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07872.pow 1)).mul (ha08138.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((324 : ℂ) / (1 : ℂ))).mul (ha00000.pow 2)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 6)).mul (ha00025.pow 2)).mul (ha07873.pow 1)).mul (ha08141.pow 1)))

@[irreducible]
def a08143 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07872 ^ 1 * a08142 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07874 ^ 1 * a08138 ^ 1)
theorem ha08143 : a08143.IsHomogeneous 129 := by
  unfold a08143
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07872.pow 1)).mul (ha08142.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07874.pow 1)).mul (ha08138.pow 1)))

@[irreducible]
def a08144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07872 ^ 1 * a08140 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a07873 ^ 1 * a08138 ^ 1)
theorem ha08144 : a08144.IsHomogeneous 49 := by
  unfold a08144
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07872.pow 1)).mul (ha08140.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha07873.pow 1)).mul (ha08138.pow 1)))

@[irreducible]
def a08145 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a07872 ^ 1 * a07873 ^ 1 * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07872 ^ 1 * a08140 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a08144 ^ 1)
theorem ha08145 : a08145.IsHomogeneous 55 := by
  unfold a08145
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha07872.pow 1)).mul (ha07873.pow 1)).mul (ha07889.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07872.pow 1)).mul (ha08140.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha08144.pow 1)))

@[irreducible]
def a08146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08143 ^ 1) + (C ((324 : ℂ) / (1 : ℂ)) * a00000 ^ 2 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 6 * a00025 ^ 2 * a07873 ^ 1 * a08145 ^ 1)
theorem ha08146 : a08146.IsHomogeneous 129 := by
  unfold a08146
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08143.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((324 : ℂ) / (1 : ℂ))).mul (ha00000.pow 2)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 6)).mul (ha00025.pow 2)).mul (ha07873.pow 1)).mul (ha08145.pow 1)))

@[irreducible]
def a08147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08139 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00005 ^ 6)
theorem ha08147 : a08147.IsHomogeneous 6 := by
  unfold a08147
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)))

@[irreducible]
def a08148 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a08147 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1)
theorem ha08148 : a08148.IsHomogeneous 6 := by
  unfold a08148
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha08147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)))

@[irreducible]
def a08149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08139 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00005 ^ 6)
theorem ha08149 : a08149.IsHomogeneous 6 := by
  unfold a08149
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)))

@[irreducible]
def a08150 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07878 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08149 ^ 1)
theorem ha08150 : a08150.IsHomogeneous 6 := by
  unfold a08150
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07878.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08149.pow 1)))

@[irreducible]
def a08151 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a08139 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a08150 ^ 1)
theorem ha08151 : a08151.IsHomogeneous 19 := by
  unfold a08151
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha08139.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha08150.pow 1)))

@[irreducible]
def a08152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a08150 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08151 ^ 1)
theorem ha08152 : a08152.IsHomogeneous 19 := by
  unfold a08152
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha08150.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08151.pow 1)))

@[irreducible]
def a08153 : Poly := (C ((-30 : ℂ) / (1 : ℂ)) * a00005 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a07889 ^ 1)
theorem ha08153 : a08153.IsHomogeneous 6 := by
  unfold a08153
  exact (((isHomogeneous_C (σ := Fin 6) ((-30 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)))

@[irreducible]
def a08154 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a08153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07881 ^ 1)
theorem ha08154 : a08154.IsHomogeneous 6 := by
  unfold a08154
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha08153.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07881.pow 1)))

@[irreducible]
def a08155 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a08139 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a08154 ^ 1)
theorem ha08155 : a08155.IsHomogeneous 19 := by
  unfold a08155
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha08139.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha08154.pow 1)))

@[irreducible]
def a08156 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08152 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a08155 ^ 1)
theorem ha08156 : a08156.IsHomogeneous 19 := by
  unfold a08156
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08152.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha08155.pow 1)))

@[irreducible]
def a08157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a08156 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07883 ^ 1 * a08148 ^ 1)
theorem ha08157 : a08157.IsHomogeneous 25 := by
  unfold a08157
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha08156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07883.pow 1)).mul (ha08148.pow 1)))

@[irreducible]
def a08158 : Poly := (C ((-1 : ℂ) / (486 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a08149 ^ 1)
theorem ha08158 : a08158.IsHomogeneous 18 := by
  unfold a08158
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (486 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha08149.pow 1)))

@[irreducible]
def a08159 : Poly := (C ((-1 : ℂ) / (486 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a08158 ^ 1)
theorem ha08159 : a08159.IsHomogeneous 18 := by
  unfold a08159
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (486 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08158.pow 1)))

@[irreducible]
def a08160 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a08153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07881 ^ 1)
theorem ha08160 : a08160.IsHomogeneous 6 := by
  unfold a08160
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha08153.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07881.pow 1)))

@[irreducible]
def a08161 : Poly := (C ((-1 : ℂ) / (486 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a08160 ^ 1)
theorem ha08161 : a08161.IsHomogeneous 18 := by
  unfold a08161
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (486 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha08160.pow 1)))

@[irreducible]
def a08162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08159 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08161 ^ 1)
theorem ha08162 : a08162.IsHomogeneous 18 := by
  unfold a08162
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08159.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08161.pow 1)))

@[irreducible]
def a08163 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07887 ^ 1 * a08147 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a07887 ^ 1 * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07877 ^ 1 * a08162 ^ 1)
theorem ha08163 : a08163.IsHomogeneous 30 := by
  unfold a08163
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07887.pow 1)).mul (ha08147.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha07887.pow 1)).mul (ha07889.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07877.pow 1)).mul (ha08162.pow 1)))

@[irreducible]
def a08164 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a08163 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a08157 ^ 1)
theorem ha08164 : a08164.IsHomogeneous 36 := by
  unfold a08164
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha08163.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha08157.pow 1)))

@[irreducible]
def a08165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07878 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a08149 ^ 1)
theorem ha08165 : a08165.IsHomogeneous 6 := by
  unfold a08165
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07878.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha08149.pow 1)))

@[irreducible]
def a08166 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a07889 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1)
theorem ha08166 : a08166.IsHomogeneous 6 := by
  unfold a08166
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha07889.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)))

@[irreducible]
def a08167 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a08166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a08165 ^ 1)
theorem ha08167 : a08167.IsHomogeneous 19 := by
  unfold a08167
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha08166.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha08165.pow 1)))

@[irreducible]
def a08168 : Poly := (C ((-90 : ℂ) / (1 : ℂ)) * a00005 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a07889 ^ 1)
theorem ha08168 : a08168.IsHomogeneous 6 := by
  unfold a08168
  exact (((isHomogeneous_C (σ := Fin 6) ((-90 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)))

@[irreducible]
def a08169 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a08168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07889 ^ 1)
theorem ha08169 : a08169.IsHomogeneous 6 := by
  unfold a08169
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha08168.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)))

@[irreducible]
def a08170 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08147 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a08169 ^ 1)
theorem ha08170 : a08170.IsHomogeneous 6 := by
  unfold a08170
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha08169.pow 1)))

@[irreducible]
def a08171 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a07890 ^ 1 * a08167 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07879 ^ 1 * a08170 ^ 1)
theorem ha08171 : a08171.IsHomogeneous 25 := by
  unfold a08171
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha07890.pow 1)).mul (ha08167.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07879.pow 1)).mul (ha08170.pow 1)))

@[irreducible]
def a08172 : Poly := (C ((-1 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a08150 ^ 1)
theorem ha08172 : a08172.IsHomogeneous 18 := by
  unfold a08172
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha08150.pow 1)))

@[irreducible]
def a08173 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07889 ^ 1 * a08172 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07868 ^ 1 * a07884 ^ 1 * a08168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07884 ^ 1 * a07889 ^ 2)
theorem ha08173 : a08173.IsHomogeneous 30 := by
  unfold a08173
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07889.pow 1)).mul (ha08172.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07868.pow 1)).mul (ha07884.pow 1)).mul (ha08168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07884.pow 1)).mul (ha07889.pow 2)))

@[irreducible]
def a08174 : Poly := (C ((-1 : ℂ) / (324 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a08171 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a08173 ^ 1)
theorem ha08174 : a08174.IsHomogeneous 36 := by
  unfold a08174
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (324 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha08171.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha08173.pow 1)))

@[irreducible]
def a08175 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a08174 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08164 ^ 1)
theorem ha08175 : a08175.IsHomogeneous 36 := by
  unfold a08175
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha08174.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08164.pow 1)))

@[irreducible]
def a08176 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1)
theorem ha08176 : a08176.IsHomogeneous 13 := by
  unfold a08176
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)))

@[irreducible]
def a08177 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08176 ^ 1)
theorem ha08177 : a08177.IsHomogeneous 13 := by
  unfold a08177
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08176.pow 1)))

@[irreducible]
def a08178 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a08177 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07894 ^ 1 * a08148 ^ 1)
theorem ha08178 : a08178.IsHomogeneous 19 := by
  unfold a08178
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha08177.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07894.pow 1)).mul (ha08148.pow 1)))

@[irreducible]
def a08179 : Poly := (C ((-10 : ℂ) / (1 : ℂ)) * a00005 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a07889 ^ 1)
theorem ha08179 : a08179.IsHomogeneous 6 := by
  unfold a08179
  exact (((isHomogeneous_C (σ := Fin 6) ((-10 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07889.pow 1)))

@[irreducible]
def a08180 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a08179 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07895 ^ 1)
theorem ha08180 : a08180.IsHomogeneous 6 := by
  unfold a08180
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha08179.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07895.pow 1)))

@[irreducible]
def a08181 : Poly := (C ((-1 : ℂ) / (1944 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a08139 ^ 1)
theorem ha08181 : a08181.IsHomogeneous 18 := by
  unfold a08181
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1944 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha08139.pow 1)))

@[irreducible]
def a08182 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a08180 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a08181 ^ 1)
theorem ha08182 : a08182.IsHomogeneous 18 := by
  unfold a08182
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha08180.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha08181.pow 1)))

@[irreducible]
def a08183 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a07897 ^ 1 * a08147 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07877 ^ 1 * a08182 ^ 1)
theorem ha08183 : a08183.IsHomogeneous 24 := by
  unfold a08183
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha07897.pow 1)).mul (ha08147.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07877.pow 1)).mul (ha08182.pow 1)))

@[irreducible]
def a08184 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a08183 ^ 1) + (C ((1 : ℂ) / (162 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a08178 ^ 1)
theorem ha08184 : a08184.IsHomogeneous 30 := by
  unfold a08184
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha08183.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (162 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha08178.pow 1)))

@[irreducible]
def a08185 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a08179 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07895 ^ 1)
theorem ha08185 : a08185.IsHomogeneous 6 := by
  unfold a08185
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha08179.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07895.pow 1)))

@[irreducible]
def a08186 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a08139 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a08185 ^ 1)
theorem ha08186 : a08186.IsHomogeneous 19 := by
  unfold a08186
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha08139.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha08185.pow 1)))

@[irreducible]
def a08187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07899 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08186 ^ 1)
theorem ha08187 : a08187.IsHomogeneous 19 := by
  unfold a08187
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07899.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08186.pow 1)))

@[irreducible]
def a08188 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 1 * a08180 ^ 1)
theorem ha08188 : a08188.IsHomogeneous 18 := by
  unfold a08188
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 1)).mul (ha08180.pow 1)))

@[irreducible]
def a08189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a08139 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a08147 ^ 1)
theorem ha08189 : a08189.IsHomogeneous 6 := by
  unfold a08189
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha08147.pow 1)))

@[irreducible]
def a08190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07900 ^ 1 * a08189 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07901 ^ 1 * a08188 ^ 1)
theorem ha08190 : a08190.IsHomogeneous 24 := by
  unfold a08190
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07900.pow 1)).mul (ha08189.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07901.pow 1)).mul (ha08188.pow 1)))

@[irreducible]
def a08191 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a08190 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a08187 ^ 1)
theorem ha08191 : a08191.IsHomogeneous 30 := by
  unfold a08191
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha08190.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha08187.pow 1)))

end CycleQ2Concrete
