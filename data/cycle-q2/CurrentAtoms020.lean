import Proposal.CurrentAtoms019

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a06912 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1 * a03597 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00574 ^ 1 * a01721 ^ 1)
theorem ha06912 : a06912.IsHomogeneous 31 := by
  unfold a06912
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha03597.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00574.pow 1)).mul (ha01721.pow 1)))

@[irreducible]
def a06913 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06911 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a06912 ^ 1)
theorem ha06913 : a06913.IsHomogeneous 31 := by
  unfold a06913
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06911.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha06912.pow 1)))

@[irreducible]
def a06914 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a03186 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00721 ^ 1 * a01469 ^ 1)
theorem ha06914 : a06914.IsHomogeneous 31 := by
  unfold a06914
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha03186.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)).mul (ha01469.pow 1)))

@[irreducible]
def a06915 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06911 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a06914 ^ 1)
theorem ha06915 : a06915.IsHomogeneous 31 := by
  unfold a06915
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06911.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha06914.pow 1)))

@[irreducible]
def a06916 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06913 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06915 ^ 1)
theorem ha06916 : a06916.IsHomogeneous 31 := by
  unfold a06916
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06913.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06915.pow 1)))

@[irreducible]
def a06917 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a03597 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00025 ^ 1 * a06781 ^ 1)
theorem ha06917 : a06917.IsHomogeneous 25 := by
  unfold a06917
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha03597.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00025.pow 1)).mul (ha06781.pow 1)))

@[irreducible]
def a06918 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a06917 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06912 ^ 1)
theorem ha06918 : a06918.IsHomogeneous 31 := by
  unfold a06918
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha06917.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06912.pow 1)))

@[irreducible]
def a06919 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06913 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a06918 ^ 1)
theorem ha06919 : a06919.IsHomogeneous 31 := by
  unfold a06919
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06913.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha06918.pow 1)))

@[irreducible]
def a06920 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06916 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06919 ^ 1)
theorem ha06920 : a06920.IsHomogeneous 31 := by
  unfold a06920
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06916.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06919.pow 1)))

@[irreducible]
def a06921 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a06152 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00264 ^ 1 * a03186 ^ 1)
theorem ha06921 : a06921.IsHomogeneous 31 := by
  unfold a06921
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha06152.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).mul (ha03186.pow 1)))

@[irreducible]
def a06922 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06914 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a06921 ^ 1)
theorem ha06922 : a06922.IsHomogeneous 31 := by
  unfold a06922
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06914.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha06921.pow 1)))

@[irreducible]
def a06923 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06915 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a06922 ^ 1)
theorem ha06923 : a06923.IsHomogeneous 31 := by
  unfold a06923
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06915.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha06922.pow 1)))

@[irreducible]
def a06924 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06916 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06923 ^ 1)
theorem ha06924 : a06924.IsHomogeneous 31 := by
  unfold a06924
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06916.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06923.pow 1)))

@[irreducible]
def a06925 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06920 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06924 ^ 1)
theorem ha06925 : a06925.IsHomogeneous 31 := by
  unfold a06925
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06920.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06924.pow 1)))

@[irreducible]
def a06926 : Poly := (C ((-7 : ℂ) / (576 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 4 * a00005 ^ 2 * a06925 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1 * a06910 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a06895 ^ 1)
theorem ha06926 : a06926.IsHomogeneous 55 := by
  unfold a06926
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (576 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha06925.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha06910.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha06895.pow 1)))

@[irreducible]
def a06927 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00276 ^ 1 * a03686 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 1 * a00120 ^ 1 * a06926 ^ 1)
theorem ha06927 : a06927.IsHomogeneous 87 := by
  unfold a06927
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00276.pow 1)).mul (ha03686.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 1)).mul (ha00120.pow 1)).mul (ha06926.pow 1)))

@[irreducible]
def a06928 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06927 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06857 ^ 1)
theorem ha06928 : a06928.IsHomogeneous 88 := by
  unfold a06928
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06927.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06857.pow 1)))

@[irreducible]
def a06929 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06858 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06928 ^ 1)
theorem ha06929 : a06929.IsHomogeneous 88 := by
  unfold a06929
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06858.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06928.pow 1)))

@[irreducible]
def a06930 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06929 ^ 1)
theorem ha06930 : a06930.IsHomogeneous 88 := by
  unfold a06930
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06861.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06929.pow 1)))

@[irreducible]
def a06931 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00119 ^ 1 * a04085 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00012 ^ 2 * a05754 ^ 1) + (C ((7 : ℂ) / (54 : ℂ)) * a00000 ^ 9 * a00001 ^ 8 * a00003 ^ 3 * a00004 ^ 4 * a00005 ^ 1)
theorem ha06931 : a06931.IsHomogeneous 25 := by
  unfold a06931
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00119.pow 1)).mul (ha04085.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00012.pow 2)).mul (ha05754.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (54 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 8)).mul (ha00003.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 1)))

@[irreducible]
def a06932 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00118 ^ 1 * a06931 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00275 ^ 1 * a03690 ^ 1)
theorem ha06932 : a06932.IsHomogeneous 86 := by
  unfold a06932
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00118.pow 1)).mul (ha06931.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00275.pow 1)).mul (ha03690.pow 1)))

@[irreducible]
def a06933 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06932 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a06859 ^ 1)
theorem ha06933 : a06933.IsHomogeneous 88 := by
  unfold a06933
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06932.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha06859.pow 1)))

@[irreducible]
def a06934 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06860 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a06933 ^ 1)
theorem ha06934 : a06934.IsHomogeneous 88 := by
  unfold a06934
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06860.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha06933.pow 1)))

@[irreducible]
def a06935 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06934 ^ 1)
theorem ha06935 : a06935.IsHomogeneous 88 := by
  unfold a06935
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06861.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06934.pow 1)))

@[irreducible]
def a06936 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06930 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06935 ^ 1)
theorem ha06936 : a06936.IsHomogeneous 88 := by
  unfold a06936
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06930.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06935.pow 1)))

@[irreducible]
def a06937 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1 * a00280 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00280 ^ 1 * a00717 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00262 ^ 1 * a00762 ^ 1)
theorem ha06937 : a06937.IsHomogeneous 86 := by
  unfold a06937
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).mul (ha00280.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00280.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00262.pow 1)).mul (ha00762.pow 1)))

@[irreducible]
def a06938 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00130 ^ 1 * a00280 ^ 1 * a01716 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00130 ^ 1 * a00717 ^ 1 * a00762 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00280 ^ 1 * a00717 ^ 1)
theorem ha06938 : a06938.IsHomogeneous 92 := by
  unfold a06938
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00130.pow 1)).mul (ha00280.pow 1)).mul (ha01716.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)).mul (ha00762.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00280.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a06939 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00130 ^ 1 * a00262 ^ 1 * a01801 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00130 ^ 1 * a00717 ^ 1 * a00762 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00262 ^ 1 * a00762 ^ 1)
theorem ha06939 : a06939.IsHomogeneous 92 := by
  unfold a06939
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha01801.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)).mul (ha00762.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)).mul (ha00762.pow 1)))

@[irreducible]
def a06940 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06937 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a06938 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a06939 ^ 1)
theorem ha06940 : a06940.IsHomogeneous 92 := by
  unfold a06940
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06937.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha06938.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha06939.pow 1)))

@[irreducible]
def a06941 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a00717 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00121 ^ 1 * a01716 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00280 ^ 1 * a00717 ^ 1)
theorem ha06941 : a06941.IsHomogeneous 88 := by
  unfold a06941
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha00717.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00121.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00280.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a06942 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a00262 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00121 ^ 1 * a00717 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00280 ^ 1)
theorem ha06942 : a06942.IsHomogeneous 88 := by
  unfold a06942
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00121.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a06943 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06941 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a06942 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a06937 ^ 1)
theorem ha06943 : a06943.IsHomogeneous 88 := by
  unfold a06943
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06941.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha06942.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha06937.pow 1)))

@[irreducible]
def a06944 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00280 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00121 ^ 1 * a00130 ^ 1 * a03590 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 4 * a00121 ^ 1 * a01716 ^ 1)
theorem ha06944 : a06944.IsHomogeneous 91 := by
  unfold a06944
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00280.pow 1)).mul (ha01716.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00121.pow 1)).mul (ha00130.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 4)).mul (ha00121.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a06945 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06944 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06938 ^ 1) + (C ((35 : ℂ) / (72 : ℂ)) * a00003 ^ 4 * a06941 ^ 1)
theorem ha06945 : a06945.IsHomogeneous 92 := by
  unfold a06945
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06944.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06938.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (72 : ℂ))).mul (ha00003.pow 4)).mul (ha06941.pow 1)))

@[irreducible]
def a06946 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a06943 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a06940 ^ 1) + (C ((72 : ℂ) / (35 : ℂ)) * a06945 ^ 1)
theorem ha06946 : a06946.IsHomogeneous 92 := by
  unfold a06946
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha06943.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha06940.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (35 : ℂ))).mul (ha06945.pow 1)))

@[irreducible]
def a06947 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00762 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a01801 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00762 ^ 1)
theorem ha06947 : a06947.IsHomogeneous 88 := by
  unfold a06947
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00762.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha01801.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00762.pow 1)))

@[irreducible]
def a06948 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00280 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00103 ^ 1 * a00762 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00280 ^ 1)
theorem ha06948 : a06948.IsHomogeneous 88 := by
  unfold a06948
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00280.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00103.pow 1)).mul (ha00762.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00280.pow 1)))

@[irreducible]
def a06949 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06947 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a06948 ^ 1) + (C ((54 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a06937 ^ 1)
theorem ha06949 : a06949.IsHomogeneous 88 := by
  unfold a06949
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06947.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha06948.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha06937.pow 1)))

@[irreducible]
def a06950 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00262 ^ 1 * a01801 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00130 ^ 1 * a03728 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 4 * a00103 ^ 1 * a01801 ^ 1)
theorem ha06950 : a06950.IsHomogeneous 91 := by
  unfold a06950
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha01801.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00130.pow 1)).mul (ha03728.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 4)).mul (ha00103.pow 1)).mul (ha01801.pow 1)))

@[irreducible]
def a06951 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06950 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06939 ^ 1) + (C ((35 : ℂ) / (72 : ℂ)) * a00003 ^ 4 * a06947 ^ 1)
theorem ha06951 : a06951.IsHomogeneous 92 := by
  unfold a06951
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06950.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06939.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (72 : ℂ))).mul (ha00003.pow 4)).mul (ha06947.pow 1)))

@[irreducible]
def a06952 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a06949 ^ 1) + (C ((54 : ℂ) / (5 : ℂ)) * a06940 ^ 1) + (C ((72 : ℂ) / (35 : ℂ)) * a06951 ^ 1)
theorem ha06952 : a06952.IsHomogeneous 92 := by
  unfold a06952
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha06949.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (5 : ℂ))).mul (ha06940.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (35 : ℂ))).mul (ha06951.pow 1)))

@[irreducible]
def a06953 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00121 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00103 ^ 1 * a00280 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00121 ^ 1 * a00262 ^ 1)
theorem ha06953 : a06953.IsHomogeneous 90 := by
  unfold a06953
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00121.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00103.pow 1)).mul (ha00280.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00121.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a06954 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06953 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06942 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06948 ^ 1)
theorem ha06954 : a06954.IsHomogeneous 90 := by
  unfold a06954
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06953.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06942.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06948.pow 1)))

@[irreducible]
def a06955 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06954 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a06949 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a06943 ^ 1)
theorem ha06955 : a06955.IsHomogeneous 90 := by
  unfold a06955
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06954.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha06949.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha06943.pow 1)))

@[irreducible]
def a06956 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06955 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a06952 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a06946 ^ 1)
theorem ha06956 : a06956.IsHomogeneous 92 := by
  unfold a06956
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06955.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha06952.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha06946.pow 1)))

@[irreducible]
def a06957 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a00717 ^ 1 * a01801 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00025 ^ 1 * a00762 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00717 ^ 1 * a00762 ^ 1)
theorem ha06957 : a06957.IsHomogeneous 92 := by
  unfold a06957
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha00717.pow 1)).mul (ha01801.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00025.pow 1)).mul (ha00762.pow 1)).mul (ha01716.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00717.pow 1)).mul (ha00762.pow 1)))

@[irreducible]
def a06958 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00762 ^ 1 * a01716 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00280 ^ 1 * a03590 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00280 ^ 1 * a01716 ^ 1)
theorem ha06958 : a06958.IsHomogeneous 91 := by
  unfold a06958
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00762.pow 1)).mul (ha01716.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00280.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00280.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a06959 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06958 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06957 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a06938 ^ 1)
theorem ha06959 : a06959.IsHomogeneous 92 := by
  unfold a06959
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06958.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06957.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha06938.pow 1)))

@[irreducible]
def a06960 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00717 ^ 1 * a01801 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00262 ^ 1 * a03728 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00262 ^ 1 * a01801 ^ 1)
theorem ha06960 : a06960.IsHomogeneous 91 := by
  unfold a06960
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00717.pow 1)).mul (ha01801.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00262.pow 1)).mul (ha03728.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00262.pow 1)).mul (ha01801.pow 1)))

@[irreducible]
def a06961 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06960 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06957 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a06939 ^ 1)
theorem ha06961 : a06961.IsHomogeneous 92 := by
  unfold a06961
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06960.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06957.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha06939.pow 1)))

@[irreducible]
def a06962 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06940 ^ 1) + (C ((5 : ℂ) / (63 : ℂ)) * a06959 ^ 1) + (C ((5 : ℂ) / (63 : ℂ)) * a06961 ^ 1)
theorem ha06962 : a06962.IsHomogeneous 92 := by
  unfold a06962
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06940.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (63 : ℂ))).mul (ha06959.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (63 : ℂ))).mul (ha06961.pow 1)))

@[irreducible]
def a06963 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00121 ^ 1 * a06772 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00121 ^ 1 * a00130 ^ 1 * a03590 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00280 ^ 1 * a03590 ^ 1)
theorem ha06963 : a06963.IsHomogeneous 90 := by
  unfold a06963
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00121.pow 1)).mul (ha06772.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00121.pow 1)).mul (ha00130.pow 1)).mul (ha03590.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00280.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a06964 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06944 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a06963 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a06958 ^ 1)
theorem ha06964 : a06964.IsHomogeneous 91 := by
  unfold a06964
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06944.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha06963.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha06958.pow 1)))

@[irreducible]
def a06965 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06964 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06945 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a06959 ^ 1)
theorem ha06965 : a06965.IsHomogeneous 92 := by
  unfold a06965
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06964.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06945.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha06959.pow 1)))

@[irreducible]
def a06966 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06946 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a06962 ^ 1) + (C ((72 : ℂ) / (35 : ℂ)) * a06965 ^ 1)
theorem ha06966 : a06966.IsHomogeneous 92 := by
  unfold a06966
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06946.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha06962.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (35 : ℂ))).mul (ha06965.pow 1)))

@[irreducible]
def a06967 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00717 ^ 1)
theorem ha06967 : a06967.IsHomogeneous 40 := by
  unfold a06967
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha01716.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00717.pow 1)))

@[irreducible]
def a06968 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00717 ^ 1)
theorem ha06968 : a06968.IsHomogeneous 40 := by
  unfold a06968
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00717.pow 1)))

@[irreducible]
def a06969 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06967 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a06968 ^ 1)
theorem ha06969 : a06969.IsHomogeneous 40 := by
  unfold a06969
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06967.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha06968.pow 1)))

@[irreducible]
def a06970 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00262 ^ 1)
theorem ha06970 : a06970.IsHomogeneous 42 := by
  unfold a06970
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)))

@[irreducible]
def a06971 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06970 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06968 ^ 1)
theorem ha06971 : a06971.IsHomogeneous 42 := by
  unfold a06971
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06968.pow 1)))

@[irreducible]
def a06972 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06971 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06969 ^ 1)
theorem ha06972 : a06972.IsHomogeneous 42 := by
  unfold a06972
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06971.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06969.pow 1)))

@[irreducible]
def a06973 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01716 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a03590 ^ 1)
theorem ha06973 : a06973.IsHomogeneous 39 := by
  unfold a06973
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01716.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha03590.pow 1)))

@[irreducible]
def a06974 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06973 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06967 ^ 1)
theorem ha06974 : a06974.IsHomogeneous 40 := by
  unfold a06974
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06973.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06967.pow 1)))

@[irreducible]
def a06975 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06969 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06974 ^ 1)
theorem ha06975 : a06975.IsHomogeneous 40 := by
  unfold a06975
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06969.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06974.pow 1)))

@[irreducible]
def a06976 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06972 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06975 ^ 1)
theorem ha06976 : a06976.IsHomogeneous 42 := by
  unfold a06976
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06972.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06975.pow 1)))

@[irreducible]
def a06977 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a06772 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03590 ^ 1)
theorem ha06977 : a06977.IsHomogeneous 42 := by
  unfold a06977
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha06772.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03590.pow 1)))

@[irreducible]
def a06978 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06977 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06973 ^ 1)
theorem ha06978 : a06978.IsHomogeneous 42 := by
  unfold a06978
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06977.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06973.pow 1)))

@[irreducible]
def a06979 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06978 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06974 ^ 1)
theorem ha06979 : a06979.IsHomogeneous 42 := by
  unfold a06979
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06978.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06974.pow 1)))

@[irreducible]
def a06980 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06979 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06975 ^ 1)
theorem ha06980 : a06980.IsHomogeneous 42 := by
  unfold a06980
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06979.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06975.pow 1)))

@[irreducible]
def a06981 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06976 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a06980 ^ 1)
theorem ha06981 : a06981.IsHomogeneous 42 := by
  unfold a06981
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06976.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha06980.pow 1)))

@[irreducible]
def a06982 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a03597 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a01721 ^ 1)
theorem ha06982 : a06982.IsHomogeneous 25 := by
  unfold a06982
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha03597.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha01721.pow 1)))

@[irreducible]
def a06983 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06982 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a03749 ^ 1)
theorem ha06983 : a06983.IsHomogeneous 25 := by
  unfold a06983
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06982.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha03749.pow 1)))

@[irreducible]
def a06984 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03750 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a06983 ^ 1)
theorem ha06984 : a06984.IsHomogeneous 25 := by
  unfold a06984
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03750.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha06983.pow 1)))

@[irreducible]
def a06985 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03751 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06984 ^ 1)
theorem ha06985 : a06985.IsHomogeneous 25 := by
  unfold a06985
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03751.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06984.pow 1)))

@[irreducible]
def a06986 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a06781 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a03597 ^ 1)
theorem ha06986 : a06986.IsHomogeneous 25 := by
  unfold a06986
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha06781.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha03597.pow 1)))

@[irreducible]
def a06987 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06982 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06986 ^ 1)
theorem ha06987 : a06987.IsHomogeneous 25 := by
  unfold a06987
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06982.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06986.pow 1)))

@[irreducible]
def a06988 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06983 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06987 ^ 1)
theorem ha06988 : a06988.IsHomogeneous 25 := by
  unfold a06988
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06983.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06987.pow 1)))

@[irreducible]
def a06989 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06984 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a06988 ^ 1)
theorem ha06989 : a06989.IsHomogeneous 25 := by
  unfold a06989
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06984.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha06988.pow 1)))

@[irreducible]
def a06990 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06985 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06989 ^ 1)
theorem ha06990 : a06990.IsHomogeneous 25 := by
  unfold a06990
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06985.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06989.pow 1)))

@[irreducible]
def a06991 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06981 ^ 1) + (C ((7 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a06990 ^ 1)
theorem ha06991 : a06991.IsHomogeneous 42 := by
  unfold a06991
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06981.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha06990.pow 1)))

@[irreducible]
def a06992 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00103 ^ 1 * a06991 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00130 ^ 1 * a03728 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1 * a03728 ^ 1)
theorem ha06992 : a06992.IsHomogeneous 90 := by
  unfold a06992
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00103.pow 1)).mul (ha06991.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)).mul (ha03728.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)).mul (ha03728.pow 1)))

@[irreducible]
def a06993 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06950 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00003 ^ 1 * a06992 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a06960 ^ 1)
theorem ha06993 : a06993.IsHomogeneous 91 := by
  unfold a06993
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06950.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00003.pow 1)).mul (ha06992.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha06960.pow 1)))

@[irreducible]
def a06994 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06993 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06951 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a06961 ^ 1)
theorem ha06994 : a06994.IsHomogeneous 92 := by
  unfold a06994
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06993.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06951.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha06961.pow 1)))

@[irreducible]
def a06995 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06952 ^ 1) + (C ((54 : ℂ) / (5 : ℂ)) * a06962 ^ 1) + (C ((72 : ℂ) / (35 : ℂ)) * a06994 ^ 1)
theorem ha06995 : a06995.IsHomogeneous 92 := by
  unfold a06995
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06952.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (5 : ℂ))).mul (ha06962.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (35 : ℂ))).mul (ha06994.pow 1)))

@[irreducible]
def a06996 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06956 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a06995 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a06966 ^ 1)
theorem ha06996 : a06996.IsHomogeneous 92 := by
  unfold a06996
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06956.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha06995.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha06966.pow 1)))

@[irreducible]
def a06997 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00133 ^ 1 * a00283 ^ 1 * a01716 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00133 ^ 1 * a00717 ^ 1 * a00769 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00283 ^ 1 * a00324 ^ 1 * a00717 ^ 1)
theorem ha06997 : a06997.IsHomogeneous 77 := by
  unfold a06997
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00133.pow 1)).mul (ha00283.pow 1)).mul (ha01716.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00133.pow 1)).mul (ha00717.pow 1)).mul (ha00769.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00283.pow 1)).mul (ha00324.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a06998 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00717 ^ 1 * a00769 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 5 * a00133 ^ 1 * a00262 ^ 1 * a01816 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00262 ^ 1 * a00324 ^ 1 * a00769 ^ 1)
theorem ha06998 : a06998.IsHomogeneous 76 := by
  unfold a06998
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00717.pow 1)).mul (ha00769.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 5)).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha01816.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00262.pow 1)).mul (ha00324.pow 1)).mul (ha00769.pow 1)))

@[irreducible]
def a06999 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00262 ^ 1 * a00324 ^ 1 * a00769 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00283 ^ 1 * a00324 ^ 1 * a00717 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00262 ^ 1 * a00283 ^ 1)
theorem ha06999 : a06999.IsHomogeneous 77 := by
  unfold a06999
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00262.pow 1)).mul (ha00324.pow 1)).mul (ha00769.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00283.pow 1)).mul (ha00324.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00262.pow 1)).mul (ha00283.pow 1)))

@[irreducible]
def a07000 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a06998 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a06997 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a06999 ^ 1)
theorem ha07000 : a07000.IsHomogeneous 77 := by
  unfold a07000
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha06998.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha06997.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha06999.pow 1)))

@[irreducible]
def a07001 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00717 ^ 1 * a00769 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00032 ^ 1 * a00769 ^ 1 * a01716 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00032 ^ 1 * a00717 ^ 1 * a01816 ^ 1)
theorem ha07001 : a07001.IsHomogeneous 76 := by
  unfold a07001
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00717.pow 1)).mul (ha00769.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00032.pow 1)).mul (ha00769.pow 1)).mul (ha01716.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00032.pow 1)).mul (ha00717.pow 1)).mul (ha01816.pow 1)))

@[irreducible]
def a07002 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00283 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00283 ^ 1 * a03590 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 1 * a00032 ^ 1 * a00769 ^ 1 * a01716 ^ 1)
theorem ha07002 : a07002.IsHomogeneous 76 := by
  unfold a07002
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00283.pow 1)).mul (ha01716.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00283.pow 1)).mul (ha03590.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 1)).mul (ha00032.pow 1)).mul (ha00769.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a07003 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a07001 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a07002 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a06997 ^ 1)
theorem ha07003 : a07003.IsHomogeneous 77 := by
  unfold a07003
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha07001.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha07002.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha06997.pow 1)))

@[irreducible]
def a07004 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00262 ^ 1 * a03756 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00133 ^ 1 * a00262 ^ 1 * a01816 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00032 ^ 1 * a00717 ^ 1 * a01816 ^ 1)
theorem ha07004 : a07004.IsHomogeneous 71 := by
  unfold a07004
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00262.pow 1)).mul (ha03756.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha01816.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00032.pow 1)).mul (ha00717.pow 1)).mul (ha01816.pow 1)))

@[irreducible]
def a07005 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06998 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07001 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 5 * a07004 ^ 1)
theorem ha07005 : a07005.IsHomogeneous 76 := by
  unfold a07005
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06998.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07001.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 5)).mul (ha07004.pow 1)))

@[irreducible]
def a07006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a07005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07000 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07003 ^ 1)
theorem ha07006 : a07006.IsHomogeneous 77 := by
  unfold a07006
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha07005.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07000.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07003.pow 1)))

@[irreducible]
def a07007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00122 ^ 1 * a00324 ^ 1 * a01716 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00283 ^ 1 * a00324 ^ 1 * a00717 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00122 ^ 1 * a00717 ^ 1)
theorem ha07007 : a07007.IsHomogeneous 77 := by
  unfold a07007
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00122.pow 1)).mul (ha00324.pow 1)).mul (ha01716.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00283.pow 1)).mul (ha00324.pow 1)).mul (ha00717.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00122.pow 1)).mul (ha00717.pow 1)))

@[irreducible]
def a07008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a00324 ^ 1 * a01716 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00122 ^ 1 * a00133 ^ 1 * a03590 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00283 ^ 1 * a01716 ^ 1)
theorem ha07008 : a07008.IsHomogeneous 76 := by
  unfold a07008
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha00324.pow 1)).mul (ha01716.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00122.pow 1)).mul (ha00133.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00283.pow 1)).mul (ha01716.pow 1)))

@[irreducible]
def a07009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a07008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07007 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a06997 ^ 1)
theorem ha07009 : a07009.IsHomogeneous 77 := by
  unfold a07009
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha07008.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07007.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha06997.pow 1)))

@[irreducible]
def a07010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a00262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a00717 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00262 ^ 1 * a00283 ^ 1)
theorem ha07010 : a07010.IsHomogeneous 71 := by
  unfold a07010
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha00717.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00262.pow 1)).mul (ha00283.pow 1)))

@[irreducible]
def a07011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07010 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a06999 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a07007 ^ 1)
theorem ha07011 : a07011.IsHomogeneous 77 := by
  unfold a07011
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07010.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha06999.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha07007.pow 1)))

@[irreducible]
def a07012 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07000 ^ 1) + (C ((14 : ℂ) / (5 : ℂ)) * a07009 ^ 1) + (C ((84 : ℂ) / (5 : ℂ)) * a07011 ^ 1)
theorem ha07012 : a07012.IsHomogeneous 77 := by
  unfold a07012
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07000.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (5 : ℂ))).mul (ha07009.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((84 : ℂ) / (5 : ℂ))).mul (ha07011.pow 1)))

@[irreducible]
def a07013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00122 ^ 1 * a06772 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00122 ^ 1 * a00133 ^ 1 * a03590 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00283 ^ 1 * a03590 ^ 1)
theorem ha07013 : a07013.IsHomogeneous 73 := by
  unfold a07013
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00122.pow 1)).mul (ha06772.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00122.pow 1)).mul (ha00133.pow 1)).mul (ha03590.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00283.pow 1)).mul (ha03590.pow 1)))

@[irreducible]
def a07014 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07002 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a07013 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a07008 ^ 1)
theorem ha07014 : a07014.IsHomogeneous 76 := by
  unfold a07014
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07002.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha07013.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha07008.pow 1)))

@[irreducible]
def a07015 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a07014 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a07003 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a07009 ^ 1)
theorem ha07015 : a07015.IsHomogeneous 77 := by
  unfold a07015
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha07014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha07003.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha07009.pow 1)))

@[irreducible]
def a07016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07012 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a07015 ^ 1)
theorem ha07016 : a07016.IsHomogeneous 77 := by
  unfold a07016
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07012.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha07015.pow 1)))

@[irreducible]
def a07017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00262 ^ 1 * a00324 ^ 1 * a00769 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00103 ^ 1 * a00324 ^ 1 * a01816 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a00103 ^ 1 * a00769 ^ 1)
theorem ha07017 : a07017.IsHomogeneous 76 := by
  unfold a07017
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00262.pow 1)).mul (ha00324.pow 1)).mul (ha00769.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00103.pow 1)).mul (ha00324.pow 1)).mul (ha01816.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha00103.pow 1)).mul (ha00769.pow 1)))

@[irreducible]
def a07018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00133 ^ 1 * a03756 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00133 ^ 1 * a00262 ^ 1 * a01816 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00103 ^ 1 * a00324 ^ 1 * a01816 ^ 1)
theorem ha07018 : a07018.IsHomogeneous 73 := by
  unfold a07018
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00133.pow 1)).mul (ha03756.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00133.pow 1)).mul (ha00262.pow 1)).mul (ha01816.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00103.pow 1)).mul (ha00324.pow 1)).mul (ha01816.pow 1)))

@[irreducible]
def a07019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06998 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00003 ^ 3 * a07018 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a07017 ^ 1)
theorem ha07019 : a07019.IsHomogeneous 76 := by
  unfold a07019
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06998.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00003.pow 3)).mul (ha07018.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha07017.pow 1)))

@[irreducible]
def a07020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00769 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00283 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00262 ^ 1 * a00283 ^ 1)
theorem ha07020 : a07020.IsHomogeneous 73 := by
  unfold a07020
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00769.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00283.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00262.pow 1)).mul (ha00283.pow 1)))

@[irreducible]
def a07021 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a07017 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06999 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a07020 ^ 1)
theorem ha07021 : a07021.IsHomogeneous 77 := by
  unfold a07021
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha07017.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06999.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha07020.pow 1)))

@[irreducible]
def a07022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a07019 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07000 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a07021 ^ 1)
theorem ha07022 : a07022.IsHomogeneous 77 := by
  unfold a07022
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha07019.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07000.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha07021.pow 1)))

@[irreducible]
def a07023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00721 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 5 * a01721 ^ 1)
theorem ha07023 : a07023.IsHomogeneous 24 := by
  unfold a07023
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00721.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 5)).mul (ha01721.pow 1)))

@[irreducible]
def a07024 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00264 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00721 ^ 1)
theorem ha07024 : a07024.IsHomogeneous 25 := by
  unfold a07024
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00721.pow 1)))

@[irreducible]
def a07025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07024 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a07023 ^ 1)
theorem ha07025 : a07025.IsHomogeneous 25 := by
  unfold a07025
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07024.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha07023.pow 1)))

@[irreducible]
def a07026 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00264 ^ 1)
theorem ha07026 : a07026.IsHomogeneous 25 := by
  unfold a07026
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00264.pow 1)))

@[irreducible]
def a07027 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07024 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a07026 ^ 1)
theorem ha07027 : a07027.IsHomogeneous 25 := by
  unfold a07027
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07024.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha07026.pow 1)))

@[irreducible]
def a07028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07027 ^ 1)
theorem ha07028 : a07028.IsHomogeneous 25 := by
  unfold a07028
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07027.pow 1)))

@[irreducible]
def a07029 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01721 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a03597 ^ 1)
theorem ha07029 : a07029.IsHomogeneous 19 := by
  unfold a07029
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01721.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha03597.pow 1)))

@[irreducible]
def a07030 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07023 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 5 * a07029 ^ 1)
theorem ha07030 : a07030.IsHomogeneous 24 := by
  unfold a07030
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07023.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 5)).mul (ha07029.pow 1)))

@[irreducible]
def a07031 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07025 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a07030 ^ 1)
theorem ha07031 : a07031.IsHomogeneous 25 := by
  unfold a07031
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha07030.pow 1)))

@[irreducible]
def a07032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07028 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07031 ^ 1)
theorem ha07032 : a07032.IsHomogeneous 25 := by
  unfold a07032
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07028.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07031.pow 1)))

@[irreducible]
def a07033 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a06781 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03597 ^ 1)
theorem ha07033 : a07033.IsHomogeneous 25 := by
  unfold a07033
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha06781.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03597.pow 1)))

@[irreducible]
def a07034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07033 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a07029 ^ 1)
theorem ha07034 : a07034.IsHomogeneous 25 := by
  unfold a07034
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07033.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha07029.pow 1)))

@[irreducible]
def a07035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07034 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a07030 ^ 1)
theorem ha07035 : a07035.IsHomogeneous 25 := by
  unfold a07035
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07034.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha07030.pow 1)))

@[irreducible]
def a07036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07031 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a07035 ^ 1)
theorem ha07036 : a07036.IsHomogeneous 25 := by
  unfold a07036
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07031.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha07035.pow 1)))

@[irreducible]
def a07037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07036 ^ 1)
theorem ha07037 : a07037.IsHomogeneous 25 := by
  unfold a07037
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07036.pow 1)))

@[irreducible]
def a07038 : Poly := (C ((-7 : ℂ) / (81 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a06152 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07037 ^ 1)
theorem ha07038 : a07038.IsHomogeneous 25 := by
  unfold a07038
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (81 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha06152.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07037.pow 1)))

@[irreducible]
def a07039 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00103 ^ 1 * a07038 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00133 ^ 1 * a03756 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00032 ^ 1 * a00262 ^ 1 * a03756 ^ 1)
theorem ha07039 : a07039.IsHomogeneous 73 := by
  unfold a07039
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00103.pow 1)).mul (ha07038.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00133.pow 1)).mul (ha03756.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00032.pow 1)).mul (ha00262.pow 1)).mul (ha03756.pow 1)))

@[irreducible]
def a07040 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07018 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a07039 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a07004 ^ 1)
theorem ha07040 : a07040.IsHomogeneous 73 := by
  unfold a07040
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07018.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha07039.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha07004.pow 1)))

@[irreducible]
def a07041 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07019 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00003 ^ 3 * a07040 ^ 1)
theorem ha07041 : a07041.IsHomogeneous 76 := by
  unfold a07041
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07005.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07019.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00003.pow 3)).mul (ha07040.pow 1)))

@[irreducible]
def a07042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a07041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07022 ^ 1)
theorem ha07042 : a07042.IsHomogeneous 77 := by
  unfold a07042
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha07041.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07006.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07022.pow 1)))

@[irreducible]
def a07043 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00122 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00103 ^ 1 * a00283 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00122 ^ 1 * a00262 ^ 1)
theorem ha07043 : a07043.IsHomogeneous 73 := by
  unfold a07043
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00122.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00103.pow 1)).mul (ha00283.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00122.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a07044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07020 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a07043 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a07010 ^ 1)
theorem ha07044 : a07044.IsHomogeneous 73 := by
  unfold a07044
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07020.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha07043.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha07010.pow 1)))

@[irreducible]
def a07045 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a07044 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a07011 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a07021 ^ 1)
theorem ha07045 : a07045.IsHomogeneous 77 := by
  unfold a07045
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha07044.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha07011.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha07021.pow 1)))

@[irreducible]
def a07046 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07012 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07022 ^ 1) + (C ((28 : ℂ) / (5 : ℂ)) * a07045 ^ 1)
theorem ha07046 : a07046.IsHomogeneous 77 := by
  unfold a07046
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07012.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07022.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((28 : ℂ) / (5 : ℂ))).mul (ha07045.pow 1)))

@[irreducible]
def a07047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07016 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07046 ^ 1)
theorem ha07047 : a07047.IsHomogeneous 77 := by
  unfold a07047
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07016.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07042.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07046.pow 1)))

@[irreducible]
def a07048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a06936 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00000 ^ 5 * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a07047 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a06996 ^ 1)
theorem ha07048 : a07048.IsHomogeneous 93 := by
  unfold a07048
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha06936.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha07047.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha06996.pow 1)))

@[irreducible]
def a07049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00262 ^ 1 * a03764 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 5 * a00103 ^ 1 * a03764 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a07048 ^ 1)
theorem ha07049 : a07049.IsHomogeneous 141 := by
  unfold a07049
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00262.pow 1)).mul (ha03764.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 5)).mul (ha00103.pow 1)).mul (ha03764.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha07048.pow 1)))

@[irreducible]
def a07050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00103 ^ 1 * a06836 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a07049 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a06843 ^ 1)
theorem ha07050 : a07050.IsHomogeneous 183 := by
  unfold a07050
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00103.pow 1)).mul (ha06836.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha07049.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha06843.pow 1)))

@[irreducible]
def a07051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a06837 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a06844 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a07050 ^ 1)
theorem ha07051 : a07051.IsHomogeneous 183 := by
  unfold a07051
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha06837.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha06844.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha07050.pow 1)))

@[irreducible]
def a07052 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06838 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a07051 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a06845 ^ 1)
theorem ha07052 : a07052.IsHomogeneous 183 := by
  unfold a07052
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06838.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha07051.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha06845.pow 1)))

@[irreducible]
def a07053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a06839 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07052 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a06855 ^ 1)
theorem ha07053 : a07053.IsHomogeneous 183 := by
  unfold a07053
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha06839.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07052.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha06855.pow 1)))

@[irreducible]
def a07054 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a07053 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00286 ^ 1 * a03768 ^ 1)
theorem ha07054 : a07054.IsHomogeneous 329 := by
  unfold a07054
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha07053.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00286.pow 1)).mul (ha03768.pow 1)))

@[irreducible]
def a07055 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a07054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06805 ^ 1)
theorem ha07055 : a07055.IsHomogeneous 475 := by
  unfold a07055
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha07054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06805.pow 1)))

@[irreducible]
def a07056 : Poly := (C ((-5 : ℂ) / (3888 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a07055 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06806 ^ 1)
theorem ha07056 : a07056.IsHomogeneous 621 := by
  unfold a07056
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3888 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha07055.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06806.pow 1)))

@[irreducible]
def a07057 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00123 ^ 1 * a07056 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a06819 ^ 1)
theorem ha07057 : a07057.IsHomogeneous 725 := by
  unfold a07057
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha07056.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06819.pow 1)))

@[irreducible]
def a07058 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00271 ^ 1 * a03771 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00117 ^ 1 * a07057 ^ 1)
theorem ha07058 : a07058.IsHomogeneous 804 := by
  unfold a07058
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00271.pow 1)).mul (ha03771.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha07057.pow 1)))

@[irreducible]
def a07059 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06754 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a07058 ^ 1)
theorem ha07059 : a07059.IsHomogeneous 859 := by
  unfold a07059
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06754.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha07058.pow 1)))

@[irreducible]
def a07060 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06755 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a07059 ^ 1)
theorem ha07060 : a07060.IsHomogeneous 914 := by
  unfold a07060
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06755.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha07059.pow 1)))

@[irreducible]
def a07061 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06756 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07060 ^ 1)
theorem ha07061 : a07061.IsHomogeneous 914 := by
  unfold a07061
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06756.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07060.pow 1)))

@[irreducible]
def a07062 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a06803 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07061 ^ 1)
theorem ha07062 : a07062.IsHomogeneous 914 := by
  unfold a07062
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha06803.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07061.pow 1)))

@[irreducible]
def a07063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a07062 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a00291 ^ 1 * a03775 ^ 1)
theorem ha07063 : a07063.IsHomogeneous 1029 := by
  unfold a07063
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07062.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha00291.pow 1)).mul (ha03775.pow 1)))

@[irreducible]
def a07064 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a07063 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a06746 ^ 1)
theorem ha07064 : a07064.IsHomogeneous 1144 := by
  unfold a07064
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07063.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha06746.pow 1)))

@[irreducible]
def a07065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a07064 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a06747 ^ 1)
theorem ha07065 : a07065.IsHomogeneous 1204 := by
  unfold a07065
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha07064.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha06747.pow 1)))

@[irreducible]
def a07066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a07065 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a06750 ^ 1)
theorem ha07066 : a07066.IsHomogeneous 1264 := by
  unfold a07066
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha07065.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha06750.pow 1)))

@[irreducible]
def a07067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00792 ^ 1 * a03783 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a01833 ^ 1 * a01866 ^ 1)
theorem ha07067 : a07067.IsHomogeneous 1030 := by
  unfold a07067
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00792.pow 1)).mul (ha03783.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha01833.pow 1)).mul (ha01866.pow 1)))

@[irreducible]
def a07068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01833 ^ 1 * a01866 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00291 ^ 1 * a03844 ^ 1)
theorem ha07068 : a07068.IsHomogeneous 915 := by
  unfold a07068
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01833.pow 1)).mul (ha01866.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00291.pow 1)).mul (ha03844.pow 1)))

@[irreducible]
def a07069 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07067 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a07068 ^ 1)
theorem ha07069 : a07069.IsHomogeneous 1030 := by
  unfold a07069
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07067.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07068.pow 1)))

@[irreducible]
def a07070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00792 ^ 1 * a03781 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00291 ^ 1 * a01866 ^ 1)
theorem ha07070 : a07070.IsHomogeneous 812 := by
  unfold a07070
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00792.pow 1)).mul (ha03781.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00291.pow 1)).mul (ha01866.pow 1)))

@[irreducible]
def a07071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a01866 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a03844 ^ 1)
theorem ha07071 : a07071.IsHomogeneous 697 := by
  unfold a07071
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha01866.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha03844.pow 1)))

@[irreducible]
def a07072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07070 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a07071 ^ 1)
theorem ha07072 : a07072.IsHomogeneous 812 := by
  unfold a07072
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07070.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07071.pow 1)))

@[irreducible]
def a07073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a00792 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a01866 ^ 1)
theorem ha07073 : a07073.IsHomogeneous 594 := by
  unfold a07073
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha00792.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha01866.pow 1)))

@[irreducible]
def a07074 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00124 ^ 1 * a00792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 2)
theorem ha07074 : a07074.IsHomogeneous 436 := by
  unfold a07074
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 2)))

@[irreducible]
def a07075 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00124 ^ 1 * a00792 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07074 ^ 1)
theorem ha07075 : a07075.IsHomogeneous 436 := by
  unfold a07075
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07074.pow 1)))

@[irreducible]
def a07076 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00124 ^ 1 * a07073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a07075 ^ 1)
theorem ha07076 : a07076.IsHomogeneous 654 := by
  unfold a07076
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00124.pow 1)).mul (ha07073.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha07075.pow 1)))

@[irreducible]
def a07077 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00124 ^ 1 * a00792 ^ 1 * a03781 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a07076 ^ 1)
theorem ha07077 : a07077.IsHomogeneous 872 := by
  unfold a07077
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).mul (ha03781.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha07076.pow 1)))

@[irreducible]
def a07078 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00124 ^ 1 * a07070 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07077 ^ 1)
theorem ha07078 : a07078.IsHomogeneous 872 := by
  unfold a07078
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00124.pow 1)).mul (ha07070.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07077.pow 1)))

@[irreducible]
def a07079 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00124 ^ 1 * a07072 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07078 ^ 1)
theorem ha07079 : a07079.IsHomogeneous 872 := by
  unfold a07079
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00124.pow 1)).mul (ha07072.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07078.pow 1)))

@[irreducible]
def a07080 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00124 ^ 1 * a00792 ^ 1 * a03783 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00291 ^ 1 * a07079 ^ 1)
theorem ha07080 : a07080.IsHomogeneous 1090 := by
  unfold a07080
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00124.pow 1)).mul (ha00792.pow 1)).mul (ha03783.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00291.pow 1)).mul (ha07079.pow 1)))

@[irreducible]
def a07081 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00124 ^ 1 * a07067 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07080 ^ 1)
theorem ha07081 : a07081.IsHomogeneous 1090 := by
  unfold a07081
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00124.pow 1)).mul (ha07067.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07080.pow 1)))

@[irreducible]
def a07082 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00124 ^ 1 * a07069 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07081 ^ 1)
theorem ha07082 : a07082.IsHomogeneous 1090 := by
  unfold a07082
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00124.pow 1)).mul (ha07069.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07081.pow 1)))

@[irreducible]
def a07083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00790 ^ 1 * a01855 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00787 ^ 1 * a01863 ^ 1)
theorem ha07083 : a07083.IsHomogeneous 479 := by
  unfold a07083
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00790.pow 1)).mul (ha01855.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00787.pow 1)).mul (ha01863.pow 1)))

@[irreducible]
def a07084 : Poly := (C ((-1 : ℂ) / (96 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00285 ^ 1 * a03823 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00790 ^ 1 * a01855 ^ 1)
theorem ha07084 : a07084.IsHomogeneous 387 := by
  unfold a07084
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (96 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha03823.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00790.pow 1)).mul (ha01855.pow 1)))

@[irreducible]
def a07085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07084 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07083 ^ 1)
theorem ha07085 : a07085.IsHomogeneous 485 := by
  unfold a07085
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07084.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07083.pow 1)))

@[irreducible]
def a07086 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00290 ^ 1 * a03840 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00787 ^ 1 * a01863 ^ 1)
theorem ha07086 : a07086.IsHomogeneous 570 := by
  unfold a07086
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00290.pow 1)).mul (ha03840.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00787.pow 1)).mul (ha01863.pow 1)))

@[irreducible]
def a07087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a07083 ^ 1)
theorem ha07087 : a07087.IsHomogeneous 576 := by
  unfold a07087
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha07083.pow 1)))

@[irreducible]
def a07088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07087 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a07085 ^ 1)
theorem ha07088 : a07088.IsHomogeneous 582 := by
  unfold a07088
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07087.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha07085.pow 1)))

@[irreducible]
def a07089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00265 ^ 1 * a00289 ^ 1 * a01841 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00289 ^ 1 * a00785 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00155 ^ 1 * a00265 ^ 1 * a00783 ^ 1)
theorem ha07089 : a07089.IsHomogeneous 180 := by
  unfold a07089
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)).mul (ha01841.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00289.pow 1)).mul (ha00785.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)))

@[irreducible]
def a07090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00155 ^ 1 * a00265 ^ 1 * a00783 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00783 ^ 1 * a00785 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a01848 ^ 1)
theorem ha07090 : a07090.IsHomogeneous 174 := by
  unfold a07090
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00783.pow 1)).mul (ha00785.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha01848.pow 1)))

@[irreducible]
def a07091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00783 ^ 1 * a00785 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00289 ^ 1 * a00785 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00289 ^ 1 * a01852 ^ 1)
theorem ha07091 : a07091.IsHomogeneous 174 := by
  unfold a07091
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00783.pow 1)).mul (ha00785.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00289.pow 1)).mul (ha00785.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a07092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07089 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07091 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07090 ^ 1)
theorem ha07092 : a07092.IsHomogeneous 180 := by
  unfold a07092
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07089.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07091.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07090.pow 1)))

@[irreducible]
def a07093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a00155 ^ 1 * a01848 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00783 ^ 1 * a01841 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00265 ^ 1 * a00783 ^ 1)
theorem ha07093 : a07093.IsHomogeneous 125 := by
  unfold a07093
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha01848.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00783.pow 1)).mul (ha01841.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00265.pow 1)).mul (ha00783.pow 1)))

@[irreducible]
def a07094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00289 ^ 1 * a03803 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00783 ^ 1 * a01841 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a00289 ^ 1 * a01841 ^ 1)
theorem ha07094 : a07094.IsHomogeneous 131 := by
  unfold a07094
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00289.pow 1)).mul (ha03803.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00783.pow 1)).mul (ha01841.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a07095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a07094 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a07093 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07089 ^ 1)
theorem ha07095 : a07095.IsHomogeneous 186 := by
  unfold a07095
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha07094.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha07093.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07089.pow 1)))

@[irreducible]
def a07096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00155 ^ 1 * a01848 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a03812 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a01848 ^ 1)
theorem ha07096 : a07096.IsHomogeneous 118 := by
  unfold a07096
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00155.pow 1)).mul (ha01848.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha03812.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha01848.pow 1)))

@[irreducible]
def a07097 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a07096 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a07093 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07090 ^ 1)
theorem ha07097 : a07097.IsHomogeneous 180 := by
  unfold a07097
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha07096.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha07093.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07090.pow 1)))

@[irreducible]
def a07098 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07095 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a07097 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07092 ^ 1)
theorem ha07098 : a07098.IsHomogeneous 186 := by
  unfold a07098
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07095.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha07097.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07092.pow 1)))

@[irreducible]
def a07099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00785 ^ 1 * a01841 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00155 ^ 1 * a00289 ^ 1 * a00785 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00124 ^ 1 * a00155 ^ 1 * a01852 ^ 1)
theorem ha07099 : a07099.IsHomogeneous 182 := by
  unfold a07099
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00785.pow 1)).mul (ha01841.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00289.pow 1)).mul (ha00785.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00155.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a07100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00265 ^ 1 * a03803 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00785 ^ 1 * a01841 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a00289 ^ 1 * a01841 ^ 1)
theorem ha07100 : a07100.IsHomogeneous 188 := by
  unfold a07100
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00265.pow 1)).mul (ha03803.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00785.pow 1)).mul (ha01841.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha00289.pow 1)).mul (ha01841.pow 1)))

@[irreducible]
def a07101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07100 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a07099 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a07089 ^ 1)
theorem ha07101 : a07101.IsHomogeneous 188 := by
  unfold a07101
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07100.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha07099.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha07089.pow 1)))

@[irreducible]
def a07102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00155 ^ 1 * a01852 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00289 ^ 1 * a01852 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00124 ^ 1 * a03819 ^ 1)
theorem ha07102 : a07102.IsHomogeneous 175 := by
  unfold a07102
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00155.pow 1)).mul (ha01852.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha01852.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha03819.pow 1)))

@[irreducible]
def a07103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07099 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a07091 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a07102 ^ 1)
theorem ha07103 : a07103.IsHomogeneous 182 := by
  unfold a07103
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07099.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha07091.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha07102.pow 1)))

@[irreducible]
def a07104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07101 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a07103 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a07092 ^ 1)
theorem ha07104 : a07104.IsHomogeneous 188 := by
  unfold a07104
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07101.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha07103.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha07092.pow 1)))

@[irreducible]
def a07105 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01839 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00014 ^ 1)
theorem ha07105 : a07105.IsHomogeneous 6 := by
  unfold a07105
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01839.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a07106 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01839 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03800 ^ 1)
theorem ha07106 : a07106.IsHomogeneous 12 := by
  unfold a07106
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01839.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03800.pow 1)))

@[irreducible]
def a07107 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07105 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07106 ^ 1)
theorem ha07107 : a07107.IsHomogeneous 12 := by
  unfold a07107
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07105.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07106.pow 1)))

@[irreducible]
def a07108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha07108 : a07108.IsHomogeneous 6 := by
  unfold a07108
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a07109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07108 ^ 1) + (C ((25 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07105 ^ 1)
theorem ha07109 : a07109.IsHomogeneous 12 := by
  unfold a07109
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07108.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07105.pow 1)))

@[irreducible]
def a07110 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07109 ^ 1) + (C ((25 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07107 ^ 1)
theorem ha07110 : a07110.IsHomogeneous 18 := by
  unfold a07110
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07109.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07107.pow 1)))

@[irreducible]
def a07111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha07111 : a07111.IsHomogeneous 6 := by
  unfold a07111
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a07112 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00518 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1)
theorem ha07112 : a07112.IsHomogeneous 6 := by
  unfold a07112
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00518.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a07113 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07111 ^ 1) + (C ((10 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07112 ^ 1)
theorem ha07113 : a07113.IsHomogeneous 12 := by
  unfold a07113
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07111.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07112.pow 1)))

@[irreducible]
def a07114 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01353 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00518 ^ 1)
theorem ha07114 : a07114.IsHomogeneous 12 := by
  unfold a07114
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01353.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00518.pow 1)))

@[irreducible]
def a07115 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07114 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07112 ^ 1)
theorem ha07115 : a07115.IsHomogeneous 12 := by
  unfold a07115
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07114.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07112.pow 1)))

@[irreducible]
def a07116 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07113 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07115 ^ 1)
theorem ha07116 : a07116.IsHomogeneous 18 := by
  unfold a07116
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07113.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07115.pow 1)))

@[irreducible]
def a07117 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07116 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a03800 ^ 1)
theorem ha07117 : a07117.IsHomogeneous 18 := by
  unfold a07117
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07116.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha03800.pow 1)))

@[irreducible]
def a07118 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07117 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a07106 ^ 1)
theorem ha07118 : a07118.IsHomogeneous 18 := by
  unfold a07118
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07117.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha07106.pow 1)))

@[irreducible]
def a07119 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07118 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a07107 ^ 1)
theorem ha07119 : a07119.IsHomogeneous 18 := by
  unfold a07119
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07118.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha07107.pow 1)))

@[irreducible]
def a07120 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07110 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a07119 ^ 1)
theorem ha07120 : a07120.IsHomogeneous 24 := by
  unfold a07120
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07110.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha07119.pow 1)))

@[irreducible]
def a07121 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a07120 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00289 ^ 1 * a03803 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00265 ^ 1 * a03803 ^ 1)
theorem ha07121 : a07121.IsHomogeneous 139 := by
  unfold a07121
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha07120.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00289.pow 1)).mul (ha03803.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00265.pow 1)).mul (ha03803.pow 1)))

@[irreducible]
def a07122 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a07121 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a07094 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07100 ^ 1)
theorem ha07122 : a07122.IsHomogeneous 194 := by
  unfold a07122
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha07121.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha07094.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07100.pow 1)))

@[irreducible]
def a07123 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07122 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a07095 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07101 ^ 1)
theorem ha07123 : a07123.IsHomogeneous 194 := by
  unfold a07123
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07122.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha07095.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07101.pow 1)))

@[irreducible]
def a07124 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07123 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a07098 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07104 ^ 1)
theorem ha07124 : a07124.IsHomogeneous 194 := by
  unfold a07124
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07123.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha07098.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07104.pow 1)))

@[irreducible]
def a07125 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00783 ^ 1 * a00785 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00785 ^ 1 * a01848 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00783 ^ 1 * a01852 ^ 1)
theorem ha07125 : a07125.IsHomogeneous 173 := by
  unfold a07125
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00783.pow 1)).mul (ha00785.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00785.pow 1)).mul (ha01848.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00783.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a07126 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a00265 ^ 1 * a03812 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00785 ^ 1 * a01848 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a00265 ^ 1 * a01848 ^ 1)
theorem ha07126 : a07126.IsHomogeneous 173 := by
  unfold a07126
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha03812.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00785.pow 1)).mul (ha01848.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha01848.pow 1)))

@[irreducible]
def a07127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a07090 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a07125 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a07126 ^ 1)
theorem ha07127 : a07127.IsHomogeneous 179 := by
  unfold a07127
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha07090.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha07125.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha07126.pow 1)))

@[irreducible]
def a07128 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00289 ^ 1 * a03819 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00289 ^ 1 * a01852 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00783 ^ 1 * a01852 ^ 1)
theorem ha07128 : a07128.IsHomogeneous 173 := by
  unfold a07128
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha03819.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00289.pow 1)).mul (ha01852.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00783.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a07129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a07091 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07125 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a07128 ^ 1)
theorem ha07129 : a07129.IsHomogeneous 179 := by
  unfold a07129
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha07091.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07125.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha07128.pow 1)))

@[irreducible]
def a07130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a07092 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07129 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a07127 ^ 1)
theorem ha07130 : a07130.IsHomogeneous 185 := by
  unfold a07130
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha07092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha07127.pow 1)))

@[irreducible]
def a07131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00781 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha07131 : a07131.IsHomogeneous 6 := by
  unfold a07131
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00781.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a07132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07131 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha07132 : a07132.IsHomogeneous 6 := by
  unfold a07132
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07131.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a07133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00102 ^ 2 * a07132 ^ 1) + (C ((7 : ℂ) / (36 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 3 * a00005 ^ 3 * a00012 ^ 6) + (C ((7 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00102 ^ 1)
theorem ha07133 : a07133.IsHomogeneous 54 := by
  unfold a07133
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00102.pow 2)).mul (ha07132.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (36 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 6))).add (((((((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00102.pow 1)))

@[irreducible]
def a07134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00265 ^ 1 * a03812 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a07133 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a03812 ^ 1)
theorem ha07134 : a07134.IsHomogeneous 117 := by
  unfold a07134
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00265.pow 1)).mul (ha03812.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha07133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha03812.pow 1)))

@[irreducible]
def a07135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00105 ^ 1 * a07134 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07126 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a07096 ^ 1)
theorem ha07135 : a07135.IsHomogeneous 179 := by
  unfold a07135
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha07134.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07126.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha07096.pow 1)))

@[irreducible]
def a07136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a07097 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a07135 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07127 ^ 1)
theorem ha07136 : a07136.IsHomogeneous 185 := by
  unfold a07136
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha07097.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha07135.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07127.pow 1)))

@[irreducible]
def a07137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a07098 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a07136 ^ 1) + (C ((16 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07130 ^ 1)
theorem ha07137 : a07137.IsHomogeneous 191 := by
  unfold a07137
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha07098.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha07136.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07130.pow 1)))

@[irreducible]
def a07138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a03601 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00723 ^ 1 * a01724 ^ 1)
theorem ha07138 : a07138.IsHomogeneous 107 := by
  unfold a07138
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha03601.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00723.pow 1)).mul (ha01724.pow 1)))

@[irreducible]
def a07139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00723 ^ 1 * a01724 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a07138 ^ 1)
theorem ha07139 : a07139.IsHomogeneous 107 := by
  unfold a07139
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00723.pow 1)).mul (ha01724.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha07138.pow 1)))

@[irreducible]
def a07140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00105 ^ 1 * a06786 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a03601 ^ 1)
theorem ha07140 : a07140.IsHomogeneous 107 := by
  unfold a07140
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00105.pow 1)).mul (ha06786.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha03601.pow 1)))

@[irreducible]
def a07141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07138 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a07140 ^ 1)
theorem ha07141 : a07141.IsHomogeneous 107 := by
  unfold a07141
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07138.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha07140.pow 1)))

@[irreducible]
def a07142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07139 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a07141 ^ 1)
theorem ha07142 : a07142.IsHomogeneous 107 := by
  unfold a07142
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha07141.pow 1)))

@[irreducible]
def a07143 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07139 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a07142 ^ 1)
theorem ha07143 : a07143.IsHomogeneous 107 := by
  unfold a07143
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha07142.pow 1)))

@[irreducible]
def a07144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00289 ^ 1 * a03819 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a07143 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 5 * a00124 ^ 1 * a03819 ^ 1)
theorem ha07144 : a07144.IsHomogeneous 173 := by
  unfold a07144
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00289.pow 1)).mul (ha03819.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha07143.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).mul (ha00124.pow 1)).mul (ha03819.pow 1)))

@[irreducible]
def a07145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a07102 ^ 1) + (C ((8 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a07128 ^ 1) + (C ((8 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a07144 ^ 1)
theorem ha07145 : a07145.IsHomogeneous 179 := by
  unfold a07145
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha07102.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha07128.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha07144.pow 1)))

@[irreducible]
def a07146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07103 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07129 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07145 ^ 1)
theorem ha07146 : a07146.IsHomogeneous 185 := by
  unfold a07146
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07145.pow 1)))

@[irreducible]
def a07147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07104 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a07146 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07130 ^ 1)
theorem ha07147 : a07147.IsHomogeneous 191 := by
  unfold a07147
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha07146.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07130.pow 1)))

@[irreducible]
def a07148 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07124 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07137 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07147 ^ 1)
theorem ha07148 : a07148.IsHomogeneous 197 := by
  unfold a07148
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07124.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07137.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07147.pow 1)))

@[irreducible]
def a07149 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00285 ^ 1 * a03823 ^ 1)
theorem ha07149 : a07149.IsHomogeneous 295 := by
  unfold a07149
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07148.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00285.pow 1)).mul (ha03823.pow 1)))

@[irreducible]
def a07150 : Poly := (C ((-1 : ℂ) / (96 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07149 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07084 ^ 1)
theorem ha07150 : a07150.IsHomogeneous 393 := by
  unfold a07150
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (96 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07149.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07084.pow 1)))

@[irreducible]
def a07151 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07150 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07085 ^ 1)
theorem ha07151 : a07151.IsHomogeneous 491 := by
  unfold a07151
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07150.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07085.pow 1)))

@[irreducible]
def a07152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a07088 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a07151 ^ 1)
theorem ha07152 : a07152.IsHomogeneous 588 := by
  unfold a07152
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha07088.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha07151.pow 1)))

@[irreducible]
def a07153 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1 * a03831 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01858 ^ 1 * a01861 ^ 1)
theorem ha07153 : a07153.IsHomogeneous 485 := by
  unfold a07153
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)).mul (ha03831.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01858.pow 1)).mul (ha01861.pow 1)))

@[irreducible]
def a07154 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00285 ^ 1 * a03837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01858 ^ 1 * a01861 ^ 1)
theorem ha07154 : a07154.IsHomogeneous 387 := by
  unfold a07154
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha03837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01858.pow 1)).mul (ha01861.pow 1)))

@[irreducible]
def a07155 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07153 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07154 ^ 1)
theorem ha07155 : a07155.IsHomogeneous 485 := by
  unfold a07155
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07153.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07154.pow 1)))

@[irreducible]
def a07156 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a00285 ^ 1 * a01861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1 * a03828 ^ 1)
theorem ha07156 : a07156.IsHomogeneous 388 := by
  unfold a07156
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha00285.pow 1)).mul (ha01861.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)).mul (ha03828.pow 1)))

@[irreducible]
def a07157 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a01861 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a00789 ^ 1)
theorem ha07157 : a07157.IsHomogeneous 291 := by
  unfold a07157
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha01861.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha00789.pow 1)))

@[irreducible]
def a07158 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00789 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 2)
theorem ha07158 : a07158.IsHomogeneous 194 := by
  unfold a07158
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00789.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 2)))

@[irreducible]
def a07159 : Poly := (C ((-36 : ℂ) / (1 : ℂ)) * a07158 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1)
theorem ha07159 : a07159.IsHomogeneous 194 := by
  unfold a07159
  exact (((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (1 : ℂ))).mul (ha07158.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)))

@[irreducible]
def a07160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a07159 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07157 ^ 1)
theorem ha07160 : a07160.IsHomogeneous 291 := by
  unfold a07160
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha07159.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07157.pow 1)))

@[irreducible]
def a07161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a07160 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00789 ^ 1 * a03828 ^ 1)
theorem ha07161 : a07161.IsHomogeneous 388 := by
  unfold a07161
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha07160.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00789.pow 1)).mul (ha03828.pow 1)))

@[irreducible]
def a07162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07156 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07161 ^ 1)
theorem ha07162 : a07162.IsHomogeneous 388 := by
  unfold a07162
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07161.pow 1)))

@[irreducible]
def a07163 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a03837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a01861 ^ 1)
theorem ha07163 : a07163.IsHomogeneous 290 := by
  unfold a07163
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha03837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha01861.pow 1)))

@[irreducible]
def a07164 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00123 ^ 1 * a07163 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07156 ^ 1)
theorem ha07164 : a07164.IsHomogeneous 388 := by
  unfold a07164
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00123.pow 1)).mul (ha07163.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07156.pow 1)))

@[irreducible]
def a07165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a07162 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07164 ^ 1)
theorem ha07165 : a07165.IsHomogeneous 388 := by
  unfold a07165
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07162.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07164.pow 1)))

@[irreducible]
def a07166 : Poly := (C ((-5 : ℂ) / (144 : ℂ)) * a00789 ^ 1 * a03831 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00285 ^ 1 * a07165 ^ 1)
theorem ha07166 : a07166.IsHomogeneous 485 := by
  unfold a07166
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (144 : ℂ))).mul (ha00789.pow 1)).mul (ha03831.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00285.pow 1)).mul (ha07165.pow 1)))

@[irreducible]
def a07167 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a07166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a07153 ^ 1)
theorem ha07167 : a07167.IsHomogeneous 485 := by
  unfold a07167
  exact (((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha07166.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha07153.pow 1)))

end CycleQ2Concrete
