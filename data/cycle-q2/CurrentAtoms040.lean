import Proposal.CurrentAtoms039

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a12032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11995 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a12031 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12028 ^ 1)
theorem ha12032 : a12032.IsHomogeneous 39 := by
  unfold a12032
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11995.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha12031.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12028.pow 1)))

@[irreducible]
def a12033 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12032 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12030 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a11996 ^ 1)
theorem ha12033 : a12033.IsHomogeneous 45 := by
  unfold a12033
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12030.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha11996.pow 1)))

@[irreducible]
def a12034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a06376 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a03330 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a03330 ^ 1)
theorem ha12034 : a12034.IsHomogeneous 42 := by
  unfold a12034
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha06376.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha03330.pow 1)))

@[irreducible]
def a12035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12034 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a12000 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a12029 ^ 1)
theorem ha12035 : a12035.IsHomogeneous 45 := by
  unfold a12035
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12034.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha12000.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha12029.pow 1)))

@[irreducible]
def a12036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12001 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a12030 ^ 1) + (C ((2 : ℂ) / (105 : ℂ)) * a12035 ^ 1)
theorem ha12036 : a12036.IsHomogeneous 45 := by
  unfold a12036
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12001.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha12030.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (105 : ℂ))).mul (ha12035.pow 1)))

@[irreducible]
def a12037 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12002 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a12033 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12036 ^ 1)
theorem ha12037 : a12037.IsHomogeneous 45 := by
  unfold a12037
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12002.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha12033.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12036.pow 1)))

@[irreducible]
def a12038 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00054 ^ 1 * a10779 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a05754 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00201 ^ 1 * a05754 ^ 1)
theorem ha12038 : a12038.IsHomogeneous 42 := by
  unfold a12038
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha10779.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha05754.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a12039 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12006 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a12038 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a12031 ^ 1)
theorem ha12039 : a12039.IsHomogeneous 42 := by
  unfold a12039
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha12038.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha12031.pow 1)))

@[irreducible]
def a12040 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12007 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12039 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a12032 ^ 1)
theorem ha12040 : a12040.IsHomogeneous 42 := by
  unfold a12040
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12007.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12039.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha12032.pow 1)))

@[irreducible]
def a12041 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12040 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a12008 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12033 ^ 1)
theorem ha12041 : a12041.IsHomogeneous 45 := by
  unfold a12041
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12040.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha12008.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12033.pow 1)))

@[irreducible]
def a12042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12012 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a12041 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12037 ^ 1)
theorem ha12042 : a12042.IsHomogeneous 45 := by
  unfold a12042
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12012.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha12041.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12037.pow 1)))

@[irreducible]
def a12043 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a06376 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a06376 ^ 1) + (C ((45 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a11703 ^ 1)
theorem ha12043 : a12043.IsHomogeneous 36 := by
  unfold a12043
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha06376.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha06376.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha11703.pow 1)))

@[irreducible]
def a12044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12019 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a12043 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a12034 ^ 1)
theorem ha12044 : a12044.IsHomogeneous 42 := by
  unfold a12044
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12019.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha12043.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha12034.pow 1)))

@[irreducible]
def a12045 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12044 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12020 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a12035 ^ 1)
theorem ha12045 : a12045.IsHomogeneous 45 := by
  unfold a12045
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12044.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12020.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha12035.pow 1)))

@[irreducible]
def a12046 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12021 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12036 ^ 1) + (C ((4 : ℂ) / (35 : ℂ)) * a12045 ^ 1)
theorem ha12046 : a12046.IsHomogeneous 45 := by
  unfold a12046
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12021.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12036.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (35 : ℂ))).mul (ha12045.pow 1)))

@[irreducible]
def a12047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12022 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12037 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a12046 ^ 1)
theorem ha12047 : a12047.IsHomogeneous 45 := by
  unfold a12047
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12022.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12037.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha12046.pow 1)))

@[irreducible]
def a12048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12027 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12042 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12047 ^ 1)
theorem ha12048 : a12048.IsHomogeneous 45 := by
  unfold a12048
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12027.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12042.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12047.pow 1)))

@[irreducible]
def a12049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a10903 ^ 1) + (C ((7 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a12048 ^ 1)
theorem ha12049 : a12049.IsHomogeneous 50 := by
  unfold a12049
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha10903.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha12048.pow 1)))

@[irreducible]
def a12050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11991 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12049 ^ 1)
theorem ha12050 : a12050.IsHomogeneous 50 := by
  unfold a12050
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11991.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12049.pow 1)))

@[irreducible]
def a12051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11992 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12050 ^ 1)
theorem ha12051 : a12051.IsHomogeneous 50 := by
  unfold a12051
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11992.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12050.pow 1)))

@[irreducible]
def a12052 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12049 ^ 1) + (C ((7 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a12048 ^ 1)
theorem ha12052 : a12052.IsHomogeneous 50 := by
  unfold a12052
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12049.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha12048.pow 1)))

@[irreducible]
def a12053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12050 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12052 ^ 1)
theorem ha12053 : a12053.IsHomogeneous 50 := by
  unfold a12053
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12050.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12052.pow 1)))

@[irreducible]
def a12054 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12053 ^ 1)
theorem ha12054 : a12054.IsHomogeneous 50 := by
  unfold a12054
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12053.pow 1)))

@[irreducible]
def a12055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00324 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00324 ^ 1 * a00555 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00555 ^ 1)
theorem ha12055 : a12055.IsHomogeneous 39 := by
  unfold a12055
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a12056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00171 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a00324 ^ 1 * a00555 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00324 ^ 1 * a00865 ^ 1)
theorem ha12056 : a12056.IsHomogeneous 45 := by
  unfold a12056
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a12057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00171 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00317 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00555 ^ 1)
theorem ha12057 : a12057.IsHomogeneous 39 := by
  unfold a12057
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00171.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a12058 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12055 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12057 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12056 ^ 1)
theorem ha12058 : a12058.IsHomogeneous 45 := by
  unfold a12058
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12055.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12057.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12056.pow 1)))

@[irreducible]
def a12059 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00317 ^ 1 * a01429 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00555 ^ 1 * a00865 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00317 ^ 1 * a00324 ^ 1 * a00555 ^ 1)
theorem ha12059 : a12059.IsHomogeneous 39 := by
  unfold a12059
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00555.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00317.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a12060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00133 ^ 1 * a00317 ^ 1 * a01429 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00129 ^ 1 * a00324 ^ 1 * a01429 ^ 1)
theorem ha12060 : a12060.IsHomogeneous 39 := by
  unfold a12060
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a12061 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12055 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a12060 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12059 ^ 1)
theorem ha12061 : a12061.IsHomogeneous 39 := by
  unfold a12061
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12055.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha12060.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12059.pow 1)))

@[irreducible]
def a12062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a02008 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00555 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00324 ^ 1 * a00865 ^ 1)
theorem ha12062 : a12062.IsHomogeneous 45 := by
  unfold a12062
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha02008.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00555.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a12063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12059 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a12062 ^ 1) + (C ((42 : ℂ) / (5 : ℂ)) * a12056 ^ 1)
theorem ha12063 : a12063.IsHomogeneous 45 := by
  unfold a12063
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12059.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha12062.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((42 : ℂ) / (5 : ℂ))).mul (ha12056.pow 1)))

@[irreducible]
def a12064 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12061 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12058 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12063 ^ 1)
theorem ha12064 : a12064.IsHomogeneous 45 := by
  unfold a12064
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12061.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12058.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12063.pow 1)))

@[irreducible]
def a12065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01429 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00555 ^ 1)
theorem ha12065 : a12065.IsHomogeneous 36 := by
  unfold a12065
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00555.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a12066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a03116 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01429 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00324 ^ 1 * a01429 ^ 1)
theorem ha12066 : a12066.IsHomogeneous 42 := by
  unfold a12066
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01429.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a12067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12066 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12065 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a12055 ^ 1)
theorem ha12067 : a12067.IsHomogeneous 42 := by
  unfold a12067
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12066.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12065.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha12055.pow 1)))

@[irreducible]
def a12068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00171 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00555 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00171 ^ 1)
theorem ha12068 : a12068.IsHomogeneous 42 := by
  unfold a12068
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00171.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a12069 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12068 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12065 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a12057 ^ 1)
theorem ha12069 : a12069.IsHomogeneous 42 := by
  unfold a12069
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12068.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12065.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha12057.pow 1)))

@[irreducible]
def a12070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12067 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12069 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12058 ^ 1)
theorem ha12070 : a12070.IsHomogeneous 45 := by
  unfold a12070
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12067.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12069.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12058.pow 1)))

@[irreducible]
def a12071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a06044 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a03116 ^ 1)
theorem ha12071 : a12071.IsHomogeneous 42 := by
  unfold a12071
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha06044.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha03116.pow 1)))

@[irreducible]
def a12072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12066 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a12071 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a12060 ^ 1)
theorem ha12072 : a12072.IsHomogeneous 42 := by
  unfold a12072
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12066.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha12071.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha12060.pow 1)))

@[irreducible]
def a12073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12067 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12072 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a12061 ^ 1)
theorem ha12073 : a12073.IsHomogeneous 42 := by
  unfold a12073
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12067.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12072.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha12061.pow 1)))

@[irreducible]
def a12074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12070 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12064 ^ 1)
theorem ha12074 : a12074.IsHomogeneous 45 := by
  unfold a12074
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12070.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12064.pow 1)))

@[irreducible]
def a12075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00171 ^ 1 * a00317 ^ 1)
theorem ha12075 : a12075.IsHomogeneous 33 := by
  unfold a12075
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00171.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a12076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00171 ^ 1 * a00324 ^ 1 * a00865 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00865 ^ 1)
theorem ha12076 : a12076.IsHomogeneous 39 := by
  unfold a12076
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a12077 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a12075 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00014 ^ 1 * a12076 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a12056 ^ 1)
theorem ha12077 : a12077.IsHomogeneous 45 := by
  unfold a12077
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha12075.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00014.pow 1)).mul (ha12076.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha12056.pow 1)))

@[irreducible]
def a12078 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00129 ^ 1 * a00171 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1)
theorem ha12078 : a12078.IsHomogeneous 33 := by
  unfold a12078
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00129.pow 1)).mul (ha00171.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a12079 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12075 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a12078 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a12057 ^ 1)
theorem ha12079 : a12079.IsHomogeneous 39 := by
  unfold a12079
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12075.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha12078.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha12057.pow 1)))

@[irreducible]
def a12080 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12079 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12077 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a12058 ^ 1)
theorem ha12080 : a12080.IsHomogeneous 45 := by
  unfold a12080
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12079.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12077.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha12058.pow 1)))

@[irreducible]
def a12081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a04086 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a02008 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a02008 ^ 1)
theorem ha12081 : a12081.IsHomogeneous 36 := by
  unfold a12081
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha04086.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a12082 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a12081 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a12062 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a12076 ^ 1)
theorem ha12082 : a12082.IsHomogeneous 45 := by
  unfold a12082
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha12081.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha12062.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha12076.pow 1)))

@[irreducible]
def a12083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12063 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a12082 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a12077 ^ 1)
theorem ha12083 : a12083.IsHomogeneous 45 := by
  unfold a12083
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12063.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha12082.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha12077.pow 1)))

@[irreducible]
def a12084 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12064 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a12080 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12083 ^ 1)
theorem ha12084 : a12084.IsHomogeneous 45 := by
  unfold a12084
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12064.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha12080.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12083.pow 1)))

@[irreducible]
def a12085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00171 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1)
theorem ha12085 : a12085.IsHomogeneous 36 := by
  unfold a12085
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00171.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a12086 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12085 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12068 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a12078 ^ 1)
theorem ha12086 : a12086.IsHomogeneous 42 := by
  unfold a12086
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12085.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12068.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha12078.pow 1)))

@[irreducible]
def a12087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12069 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12086 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a12079 ^ 1)
theorem ha12087 : a12087.IsHomogeneous 42 := by
  unfold a12087
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12069.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12086.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha12079.pow 1)))

@[irreducible]
def a12088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12087 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12070 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a12080 ^ 1)
theorem ha12088 : a12088.IsHomogeneous 45 := by
  unfold a12088
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12087.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12070.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha12080.pow 1)))

@[irreducible]
def a12089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12074 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12088 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12084 ^ 1)
theorem ha12089 : a12089.IsHomogeneous 45 := by
  unfold a12089
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12074.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12088.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12084.pow 1)))

@[irreducible]
def a12090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00317 ^ 1 * a03116 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00865 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a00317 ^ 1 * a01429 ^ 1)
theorem ha12090 : a12090.IsHomogeneous 39 := by
  unfold a12090
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00317.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00865.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a12091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00865 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00555 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00555 ^ 1 * a02008 ^ 1)
theorem ha12091 : a12091.IsHomogeneous 39 := by
  unfold a12091
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00865.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00555.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a12092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12059 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12090 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12091 ^ 1)
theorem ha12092 : a12092.IsHomogeneous 39 := by
  unfold a12092
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12059.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12090.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12091.pow 1)))

@[irreducible]
def a12093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00129 ^ 1 * a06044 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00129 ^ 1 * a00133 ^ 1 * a03116 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00032 ^ 1 * a00317 ^ 1 * a03116 ^ 1)
theorem ha12093 : a12093.IsHomogeneous 39 := by
  unfold a12093
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha06044.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha03116.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00032.pow 1)).mul (ha00317.pow 1)).mul (ha03116.pow 1)))

@[irreducible]
def a12094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12060 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a12093 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a12090 ^ 1)
theorem ha12094 : a12094.IsHomogeneous 39 := by
  unfold a12094
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12060.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha12093.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha12090.pow 1)))

@[irreducible]
def a12095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12061 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a12094 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12092 ^ 1)
theorem ha12095 : a12095.IsHomogeneous 39 := by
  unfold a12095
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12061.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha12094.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12092.pow 1)))

@[irreducible]
def a12096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00171 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1 * a02008 ^ 1)
theorem ha12096 : a12096.IsHomogeneous 42 := by
  unfold a12096
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha04086.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a12097 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12096 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12062 ^ 1) + (C ((10 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12091 ^ 1)
theorem ha12097 : a12097.IsHomogeneous 45 := by
  unfold a12097
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12096.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12062.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12091.pow 1)))

@[irreducible]
def a12098 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12063 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a12097 ^ 1)
theorem ha12098 : a12098.IsHomogeneous 45 := by
  unfold a12098
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12092.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12063.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha12097.pow 1)))

@[irreducible]
def a12099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12095 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12064 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12098 ^ 1)
theorem ha12099 : a12099.IsHomogeneous 45 := by
  unfold a12099
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12095.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12064.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12098.pow 1)))

@[irreducible]
def a12100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00042 ^ 1 * a11215 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a06044 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00129 ^ 1 * a06044 ^ 1)
theorem ha12100 : a12100.IsHomogeneous 42 := by
  unfold a12100
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00042.pow 1)).mul (ha11215.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha06044.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha06044.pow 1)))

@[irreducible]
def a12101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12100 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12093 ^ 1)
theorem ha12101 : a12101.IsHomogeneous 42 := by
  unfold a12101
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12100.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12093.pow 1)))

@[irreducible]
def a12102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12072 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a12101 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a12094 ^ 1)
theorem ha12102 : a12102.IsHomogeneous 42 := by
  unfold a12102
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12072.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha12101.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha12094.pow 1)))

@[irreducible]
def a12103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12102 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a12095 ^ 1)
theorem ha12103 : a12103.IsHomogeneous 42 := by
  unfold a12103
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12102.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha12095.pow 1)))

@[irreducible]
def a12104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12103 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12074 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12099 ^ 1)
theorem ha12104 : a12104.IsHomogeneous 45 := by
  unfold a12104
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12103.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12074.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12099.pow 1)))

@[irreducible]
def a12105 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a07558 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a04086 ^ 1)
theorem ha12105 : a12105.IsHomogeneous 36 := by
  unfold a12105
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha07558.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha04086.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a12106 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12081 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a12096 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12105 ^ 1)
theorem ha12106 : a12106.IsHomogeneous 42 := by
  unfold a12106
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12081.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha12096.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12105.pow 1)))

@[irreducible]
def a12107 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12106 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12082 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a12097 ^ 1)
theorem ha12107 : a12107.IsHomogeneous 45 := by
  unfold a12107
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12106.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12082.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha12097.pow 1)))

@[irreducible]
def a12108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12083 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12098 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a12107 ^ 1)
theorem ha12108 : a12108.IsHomogeneous 45 := by
  unfold a12108
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12083.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12098.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha12107.pow 1)))

@[irreducible]
def a12109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12084 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12099 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12108 ^ 1)
theorem ha12109 : a12109.IsHomogeneous 45 := by
  unfold a12109
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12084.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12099.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12108.pow 1)))

@[irreducible]
def a12110 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12089 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12104 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a12109 ^ 1)
theorem ha12110 : a12110.IsHomogeneous 45 := by
  unfold a12110
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12089.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12104.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha12109.pow 1)))

@[irreducible]
def a12111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00207 ^ 1 * a00324 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00324 ^ 1 * a00506 ^ 1 * a00632 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00207 ^ 1 * a00506 ^ 1)
theorem ha12111 : a12111.IsHomogeneous 30 := by
  unfold a12111
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).mul (ha00506.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a12112 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00506 ^ 1 * a01575 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00632 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (8 : ℂ)) * a00324 ^ 1 * a00506 ^ 1 * a00632 ^ 1)
theorem ha12112 : a12112.IsHomogeneous 30 := by
  unfold a12112
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha01575.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00632.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (8 : ℂ))).mul (ha00324.pow 1)).mul (ha00506.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a12113 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a02935 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00632 ^ 1 * a01327 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a01327 ^ 1)
theorem ha12113 : a12113.IsHomogeneous 24 := by
  unfold a12113
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00632.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a12114 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12113 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a12111 ^ 1) + (C ((168 : ℂ) / (5 : ℂ)) * a12112 ^ 1)
theorem ha12114 : a12114.IsHomogeneous 30 := by
  unfold a12114
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12113.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha12111.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((168 : ℂ) / (5 : ℂ))).mul (ha12112.pow 1)))

@[irreducible]
def a12115 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a00324 ^ 1 * a01575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00324 ^ 1 * a00506 ^ 1 * a00632 ^ 1)
theorem ha12115 : a12115.IsHomogeneous 30 := by
  unfold a12115
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00324.pow 1)).mul (ha00506.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a12116 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00632 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00207 ^ 1 * a00506 ^ 1)
theorem ha12116 : a12116.IsHomogeneous 24 := by
  unfold a12116
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00632.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00207.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a12117 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12116 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a12111 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a12115 ^ 1)
theorem ha12117 : a12117.IsHomogeneous 30 := by
  unfold a12117
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12116.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha12111.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha12115.pow 1)))

@[irreducible]
def a12118 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a03363 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00506 ^ 1 * a01575 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00324 ^ 1 * a01575 ^ 1)
theorem ha12118 : a12118.IsHomogeneous 24 := by
  unfold a12118
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha01575.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a12119 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12118 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a12112 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a12115 ^ 1)
theorem ha12119 : a12119.IsHomogeneous 30 := by
  unfold a12119
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12118.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha12112.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha12115.pow 1)))

@[irreducible]
def a12120 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12114 ^ 1) + (C ((14 : ℂ) / (1 : ℂ)) * a12119 ^ 1) + (C ((42 : ℂ) / (1 : ℂ)) * a12117 ^ 1)
theorem ha12120 : a12120.IsHomogeneous 30 := by
  unfold a12120
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12114.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (1 : ℂ))).mul (ha12119.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((42 : ℂ) / (1 : ℂ))).mul (ha12117.pow 1)))

@[irreducible]
def a12121 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00207 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a01327 ^ 1)
theorem ha12121 : a12121.IsHomogeneous 24 := by
  unfold a12121
  exact (((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00207.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a12122 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00207 ^ 1 * a00324 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a02935 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a01327 ^ 1)
theorem ha12122 : a12122.IsHomogeneous 24 := by
  unfold a12122
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00207.pow 1)).mul (ha00324.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a12123 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a12111 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12121 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a12122 ^ 1)
theorem ha12123 : a12123.IsHomogeneous 30 := by
  unfold a12123
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha12111.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12121.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha12122.pow 1)))

@[irreducible]
def a12124 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a02935 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a05754 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a02935 ^ 1)
theorem ha12124 : a12124.IsHomogeneous 24 := by
  unfold a12124
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha05754.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a12125 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a12122 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a12124 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12113 ^ 1)
theorem ha12125 : a12125.IsHomogeneous 24 := by
  unfold a12125
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha12122.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha12124.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12113.pow 1)))

@[irreducible]
def a12126 : Poly := (C ((-21 : ℂ) / (1 : ℂ)) * a12123 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12125 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12114 ^ 1)
theorem ha12126 : a12126.IsHomogeneous 30 := by
  unfold a12126
  exact ((((isHomogeneous_C (σ := Fin 6) ((-21 : ℂ) / (1 : ℂ))).mul (ha12123.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12125.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12114.pow 1)))

@[irreducible]
def a12127 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00506 ^ 1)
theorem ha12127 : a12127.IsHomogeneous 24 := by
  unfold a12127
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a12128 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a12121 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a12127 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12116 ^ 1)
theorem ha12128 : a12128.IsHomogeneous 24 := by
  unfold a12128
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha12121.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha12127.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12116.pow 1)))

@[irreducible]
def a12129 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a12123 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12128 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12117 ^ 1)
theorem ha12129 : a12129.IsHomogeneous 30 := by
  unfold a12129
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha12123.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12128.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12117.pow 1)))

@[irreducible]
def a12130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12120 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12126 ^ 1) + (C ((42 : ℂ) / (1 : ℂ)) * a12129 ^ 1)
theorem ha12130 : a12130.IsHomogeneous 30 := by
  unfold a12130
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12120.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12126.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((42 : ℂ) / (1 : ℂ))).mul (ha12129.pow 1)))

@[irreducible]
def a12131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00632 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00632 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01575 ^ 1)
theorem ha12131 : a12131.IsHomogeneous 18 := by
  unfold a12131
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00632.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a12132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00324 ^ 1 * a01575 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a03363 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01575 ^ 1)
theorem ha12132 : a12132.IsHomogeneous 18 := by
  unfold a12132
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha03363.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a12133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a12131 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a12132 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12115 ^ 1)
theorem ha12133 : a12133.IsHomogeneous 30 := by
  unfold a12133
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha12131.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha12132.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12115.pow 1)))

@[irreducible]
def a12134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00207 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00632 ^ 1)
theorem ha12134 : a12134.IsHomogeneous 18 := by
  unfold a12134
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a12135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12131 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a12134 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a12116 ^ 1)
theorem ha12135 : a12135.IsHomogeneous 24 := by
  unfold a12135
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12131.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha12134.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha12116.pow 1)))

@[irreducible]
def a12136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12135 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12133 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a12117 ^ 1)
theorem ha12136 : a12136.IsHomogeneous 30 := by
  unfold a12136
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12135.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12133.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha12117.pow 1)))

@[irreducible]
def a12137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00155 ^ 1 * a03363 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a06426 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a03363 ^ 1)
theorem ha12137 : a12137.IsHomogeneous 18 := by
  unfold a12137
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha06426.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha03363.pow 1)))

@[irreducible]
def a12138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12132 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a12137 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12118 ^ 1)
theorem ha12138 : a12138.IsHomogeneous 24 := by
  unfold a12138
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12132.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha12137.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12118.pow 1)))

@[irreducible]
def a12139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12138 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12133 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12119 ^ 1)
theorem ha12139 : a12139.IsHomogeneous 30 := by
  unfold a12139
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12138.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12133.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12119.pow 1)))

@[irreducible]
def a12140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12120 ^ 1) + (C ((294 : ℂ) / (5 : ℂ)) * a12136 ^ 1) + (C ((294 : ℂ) / (5 : ℂ)) * a12139 ^ 1)
theorem ha12140 : a12140.IsHomogeneous 30 := by
  unfold a12140
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12120.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((294 : ℂ) / (5 : ℂ))).mul (ha12136.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((294 : ℂ) / (5 : ℂ))).mul (ha12139.pow 1)))

@[irreducible]
def a12141 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00058 ^ 1)
theorem ha12141 : a12141.IsHomogeneous 18 := by
  unfold a12141
  exact (((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)))

@[irreducible]
def a12142 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a12141 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a12127 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12134 ^ 1)
theorem ha12142 : a12142.IsHomogeneous 24 := by
  unfold a12142
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha12141.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha12127.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12134.pow 1)))

@[irreducible]
def a12143 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12128 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12142 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a12135 ^ 1)
theorem ha12143 : a12143.IsHomogeneous 24 := by
  unfold a12143
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12128.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12142.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha12135.pow 1)))

@[irreducible]
def a12144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12143 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12129 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a12136 ^ 1)
theorem ha12144 : a12144.IsHomogeneous 30 := by
  unfold a12144
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12143.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12129.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha12136.pow 1)))

@[irreducible]
def a12145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12140 ^ 1) + (C ((42 : ℂ) / (1 : ℂ)) * a12144 ^ 1)
theorem ha12145 : a12145.IsHomogeneous 30 := by
  unfold a12145
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12140.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((42 : ℂ) / (1 : ℂ))).mul (ha12144.pow 1)))

@[irreducible]
def a12146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00632 ^ 1 * a02935 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00632 ^ 1 * a01327 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a01327 ^ 1 * a01575 ^ 1)
theorem ha12146 : a12146.IsHomogeneous 24 := by
  unfold a12146
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00632.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00632.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha01327.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a12147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00506 ^ 1 * a03363 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a01327 ^ 1 * a01575 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00506 ^ 1 * a01575 ^ 1)
theorem ha12147 : a12147.IsHomogeneous 24 := by
  unfold a12147
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha03363.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha01327.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00506.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a12148 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12146 ^ 1) + (C ((24 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12147 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a12112 ^ 1)
theorem ha12148 : a12148.IsHomogeneous 30 := by
  unfold a12148
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12146.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12147.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha12112.pow 1)))

@[irreducible]
def a12149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a05754 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a02935 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00032 ^ 1 * a00632 ^ 1 * a02935 ^ 1)
theorem ha12149 : a12149.IsHomogeneous 24 := by
  unfold a12149
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00032.pow 1)).mul (ha00632.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a12150 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12113 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12149 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a12146 ^ 1)
theorem ha12150 : a12150.IsHomogeneous 24 := by
  unfold a12150
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12113.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12149.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha12146.pow 1)))

@[irreducible]
def a12151 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12150 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12114 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a12148 ^ 1)
theorem ha12151 : a12151.IsHomogeneous 30 := by
  unfold a12151
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12150.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12114.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha12148.pow 1)))

@[irreducible]
def a12152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00155 ^ 1 * a06426 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a03363 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00506 ^ 1 * a03363 ^ 1)
theorem ha12152 : a12152.IsHomogeneous 24 := by
  unfold a12152
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha06426.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha03363.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha03363.pow 1)))

@[irreducible]
def a12153 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12118 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12152 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a12147 ^ 1)
theorem ha12153 : a12153.IsHomogeneous 24 := by
  unfold a12153
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12118.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12152.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha12147.pow 1)))

@[irreducible]
def a12154 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12119 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a12148 ^ 1)
theorem ha12154 : a12154.IsHomogeneous 30 := by
  unfold a12154
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12153.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12119.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha12148.pow 1)))

@[irreducible]
def a12155 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12120 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12151 ^ 1) + (C ((14 : ℂ) / (1 : ℂ)) * a12154 ^ 1)
theorem ha12155 : a12155.IsHomogeneous 30 := by
  unfold a12155
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12120.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12151.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (1 : ℂ))).mul (ha12154.pow 1)))

@[irreducible]
def a12156 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a05754 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00058 ^ 1 * a10779 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a05754 ^ 1)
theorem ha12156 : a12156.IsHomogeneous 24 := by
  unfold a12156
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha05754.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha10779.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha05754.pow 1)))

@[irreducible]
def a12157 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a12149 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12124 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a12156 ^ 1)
theorem ha12157 : a12157.IsHomogeneous 24 := by
  unfold a12157
  exact ((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha12149.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12124.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha12156.pow 1)))

@[irreducible]
def a12158 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a12157 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12125 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12150 ^ 1)
theorem ha12158 : a12158.IsHomogeneous 24 := by
  unfold a12158
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha12157.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12125.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12150.pow 1)))

@[irreducible]
def a12159 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12158 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12151 ^ 1)
theorem ha12159 : a12159.IsHomogeneous 30 := by
  unfold a12159
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12158.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12126.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12151.pow 1)))

@[irreducible]
def a12160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12159 ^ 1)
theorem ha12160 : a12160.IsHomogeneous 30 := by
  unfold a12160
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12155.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12159.pow 1)))

@[irreducible]
def a12161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a06426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a06426 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a11778 ^ 1)
theorem ha12161 : a12161.IsHomogeneous 18 := by
  unfold a12161
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha06426.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha06426.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha11778.pow 1)))

@[irreducible]
def a12162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12137 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12161 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12152 ^ 1)
theorem ha12162 : a12162.IsHomogeneous 24 := by
  unfold a12162
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12137.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12161.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12152.pow 1)))

@[irreducible]
def a12163 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12138 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12153 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12162 ^ 1)
theorem ha12163 : a12163.IsHomogeneous 24 := by
  unfold a12163
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12138.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12153.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12162.pow 1)))

@[irreducible]
def a12164 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a12163 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12139 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a12154 ^ 1)
theorem ha12164 : a12164.IsHomogeneous 30 := by
  unfold a12164
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha12163.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12139.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha12154.pow 1)))

@[irreducible]
def a12165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12140 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12155 ^ 1) + (C ((294 : ℂ) / (5 : ℂ)) * a12164 ^ 1)
theorem ha12165 : a12165.IsHomogeneous 30 := by
  unfold a12165
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12140.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12155.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((294 : ℂ) / (5 : ℂ))).mul (ha12164.pow 1)))

@[irreducible]
def a12166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12145 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12160 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12165 ^ 1)
theorem ha12166 : a12166.IsHomogeneous 30 := by
  unfold a12166
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12145.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12160.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12165.pow 1)))

@[irreducible]
def a12167 : Poly := (C ((-1 : ℂ) / (2268 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a12166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12110 ^ 1)
theorem ha12167 : a12167.IsHomogeneous 45 := by
  unfold a12167
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2268 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha12166.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12110.pow 1)))

@[irreducible]
def a12168 : Poly := (C ((-1 : ℂ) / (2268 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a12166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12110 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12167 ^ 1)
theorem ha12168 : a12168.IsHomogeneous 45 := by
  unfold a12168
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2268 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha12166.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12110.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12167.pow 1)))

@[irreducible]
def a12169 : Poly := (C ((-1 : ℂ) / (1134 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a12166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12167 ^ 1)
theorem ha12169 : a12169.IsHomogeneous 45 := by
  unfold a12169
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1134 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha12166.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12167.pow 1)))

@[irreducible]
def a12170 : Poly := (C ((-1 : ℂ) / (756 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a12166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12168 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12169 ^ 1)
theorem ha12170 : a12170.IsHomogeneous 45 := by
  unfold a12170
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (756 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha12166.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12168.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12169.pow 1)))

@[irreducible]
def a12171 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a12054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a11934 ^ 1) + (C ((56 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a12170 ^ 1)
theorem ha12171 : a12171.IsHomogeneous 50 := by
  unfold a12171
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha12054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11934.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((56 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha12170.pow 1)))

@[irreducible]
def a12172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00655 ^ 1 * a02007 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00864 ^ 1 * a01617 ^ 1)
theorem ha12172 : a12172.IsHomogeneous 45 := by
  unfold a12172
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00655.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00864.pow 1)).mul (ha01617.pow 1)))

@[irreducible]
def a12173 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00316 ^ 1 * a03432 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00864 ^ 1 * a01617 ^ 1)
theorem ha12173 : a12173.IsHomogeneous 45 := by
  unfold a12173
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha03432.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00864.pow 1)).mul (ha01617.pow 1)))

@[irreducible]
def a12174 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12172 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a12173 ^ 1)
theorem ha12174 : a12174.IsHomogeneous 45 := by
  unfold a12174
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12172.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha12173.pow 1)))

@[irreducible]
def a12175 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a04085 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00655 ^ 1 * a02007 ^ 1)
theorem ha12175 : a12175.IsHomogeneous 48 := by
  unfold a12175
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha04085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00655.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a12176 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12175 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12172 ^ 1)
theorem ha12176 : a12176.IsHomogeneous 48 := by
  unfold a12176
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12175.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12172.pow 1)))

@[irreducible]
def a12177 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12176 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12174 ^ 1)
theorem ha12177 : a12177.IsHomogeneous 48 := by
  unfold a12177
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12176.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12174.pow 1)))

@[irreducible]
def a12178 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a03432 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a06529 ^ 1)
theorem ha12178 : a12178.IsHomogeneous 39 := by
  unfold a12178
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha03432.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha06529.pow 1)))

@[irreducible]
def a12179 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12178 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12173 ^ 1)
theorem ha12179 : a12179.IsHomogeneous 45 := by
  unfold a12179
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12178.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12173.pow 1)))

@[irreducible]
def a12180 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12174 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a12179 ^ 1)
theorem ha12180 : a12180.IsHomogeneous 45 := by
  unfold a12180
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12174.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha12179.pow 1)))

@[irreducible]
def a12181 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12177 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12180 ^ 1)
theorem ha12181 : a12181.IsHomogeneous 48 := by
  unfold a12181
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12177.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12180.pow 1)))

@[irreducible]
def a12182 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a07557 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00218 ^ 1 * a04085 ^ 1)
theorem ha12182 : a12182.IsHomogeneous 48 := by
  unfold a12182
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha07557.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00218.pow 1)).mul (ha04085.pow 1)))

@[irreducible]
def a12183 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12175 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a12182 ^ 1)
theorem ha12183 : a12183.IsHomogeneous 48 := by
  unfold a12183
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12175.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha12182.pow 1)))

@[irreducible]
def a12184 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12176 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12183 ^ 1)
theorem ha12184 : a12184.IsHomogeneous 48 := by
  unfold a12184
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12176.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12183.pow 1)))

@[irreducible]
def a12185 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12177 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12184 ^ 1)
theorem ha12185 : a12185.IsHomogeneous 48 := by
  unfold a12185
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12177.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12184.pow 1)))

@[irreducible]
def a12186 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12181 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12185 ^ 1)
theorem ha12186 : a12186.IsHomogeneous 48 := by
  unfold a12186
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12181.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12185.pow 1)))

@[irreducible]
def a12187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a11923 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a06529 ^ 1)
theorem ha12187 : a12187.IsHomogeneous 36 := by
  unfold a12187
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha11923.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha06529.pow 1)))

@[irreducible]
def a12188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12187 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12178 ^ 1)
theorem ha12188 : a12188.IsHomogeneous 42 := by
  unfold a12188
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12187.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12178.pow 1)))

@[irreducible]
def a12189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12188 ^ 1) + (C ((15 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12179 ^ 1)
theorem ha12189 : a12189.IsHomogeneous 48 := by
  unfold a12189
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12188.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12179.pow 1)))

@[irreducible]
def a12190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12189 ^ 1) + (C ((27 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a12180 ^ 1)
theorem ha12190 : a12190.IsHomogeneous 48 := by
  unfold a12190
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12189.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha12180.pow 1)))

@[irreducible]
def a12191 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12181 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a12190 ^ 1)
theorem ha12191 : a12191.IsHomogeneous 48 := by
  unfold a12191
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12181.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha12190.pow 1)))

@[irreducible]
def a12192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12186 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12191 ^ 1)
theorem ha12192 : a12192.IsHomogeneous 48 := by
  unfold a12192
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12186.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12191.pow 1)))

@[irreducible]
def a12193 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11562 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a12192 ^ 1)
theorem ha12193 : a12193.IsHomogeneous 48 := by
  unfold a12193
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha12192.pow 1)))

@[irreducible]
def a12194 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12193 ^ 1)
theorem ha12194 : a12194.IsHomogeneous 48 := by
  unfold a12194
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12193.pow 1)))

@[irreducible]
def a12195 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12194 ^ 1)
theorem ha12195 : a12195.IsHomogeneous 48 := by
  unfold a12195
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12194.pow 1)))

@[irreducible]
def a12196 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12192 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a12193 ^ 1)
theorem ha12196 : a12196.IsHomogeneous 48 := by
  unfold a12196
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12192.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha12193.pow 1)))

@[irreducible]
def a12197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12194 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a12196 ^ 1)
theorem ha12197 : a12197.IsHomogeneous 48 := by
  unfold a12197
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12194.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha12196.pow 1)))

@[irreducible]
def a12198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12195 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12197 ^ 1)
theorem ha12198 : a12198.IsHomogeneous 48 := by
  unfold a12198
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12195.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12197.pow 1)))

@[irreducible]
def a12199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12195 ^ 1)
theorem ha12199 : a12199.IsHomogeneous 48 := by
  unfold a12199
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12195.pow 1)))

@[irreducible]
def a12200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12198 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12199 ^ 1)
theorem ha12200 : a12200.IsHomogeneous 48 := by
  unfold a12200
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12198.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12199.pow 1)))

@[irreducible]
def a12201 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11623 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a11709 ^ 1)
theorem ha12201 : a12201.IsHomogeneous 48 := by
  unfold a12201
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha11709.pow 1)))

@[irreducible]
def a12202 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11623 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12201 ^ 1)
theorem ha12202 : a12202.IsHomogeneous 48 := by
  unfold a12202
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12201.pow 1)))

@[irreducible]
def a12203 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11623 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12202 ^ 1)
theorem ha12203 : a12203.IsHomogeneous 48 := by
  unfold a12203
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11623.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12202.pow 1)))

@[irreducible]
def a12204 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11709 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a12201 ^ 1)
theorem ha12204 : a12204.IsHomogeneous 48 := by
  unfold a12204
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11709.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha12201.pow 1)))

@[irreducible]
def a12205 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12202 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a12204 ^ 1)
theorem ha12205 : a12205.IsHomogeneous 48 := by
  unfold a12205
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12202.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha12204.pow 1)))

@[irreducible]
def a12206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12203 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12205 ^ 1)
theorem ha12206 : a12206.IsHomogeneous 48 := by
  unfold a12206
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12203.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12205.pow 1)))

@[irreducible]
def a12207 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a11709 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12204 ^ 1)
theorem ha12207 : a12207.IsHomogeneous 48 := by
  unfold a12207
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha11709.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12204.pow 1)))

@[irreducible]
def a12208 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12205 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a12207 ^ 1)
theorem ha12208 : a12208.IsHomogeneous 48 := by
  unfold a12208
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12205.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha12207.pow 1)))

@[irreducible]
def a12209 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12206 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12208 ^ 1)
theorem ha12209 : a12209.IsHomogeneous 48 := by
  unfold a12209
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12206.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12208.pow 1)))

@[irreducible]
def a12210 : Poly := (C ((-245 : ℂ) / (81 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a11784 ^ 1) + (C ((-2 : ℂ) / (9 : ℂ)) * a12209 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12200 ^ 1)
theorem ha12210 : a12210.IsHomogeneous 48 := by
  unfold a12210
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-245 : ℂ) / (81 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha11784.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha12209.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12200.pow 1)))

@[irreducible]
def a12211 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00003 ^ 1 * a00012 ^ 5 * a10904 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 3 * a00012 ^ 3 * a11520 ^ 1) + (C ((-1 : ℂ) / (96 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a11787 ^ 1) + (C ((-1 : ℂ) / (23040 : ℂ)) * a00000 ^ 1 * a00001 ^ 18 * a00002 ^ 6 * a00003 ^ 1 * a00004 ^ 6 * a00005 ^ 6 * a12210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 2 * a00012 ^ 4 * a11222 ^ 1) + (C ((1 : ℂ) / (4608 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 6 * a00004 ^ 5 * a00005 ^ 5 * a00012 ^ 1 * a12171 ^ 1)
theorem ha12211 : a12211.IsHomogeneous 86 := by
  unfold a12211
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00003.pow 1)).mul (ha00012.pow 5)).mul (ha10904.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00012.pow 3)).mul (ha11520.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (96 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha11787.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (23040 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 18)).mul (ha00002.pow 6)).mul (ha00003.pow 1)).mul (ha00004.pow 6)).mul (ha00005.pow 6)).mul (ha12210.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00012.pow 4)).mul (ha11222.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4608 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 6)).mul (ha00004.pow 5)).mul (ha00005.pow 5)).mul (ha00012.pow 1)).mul (ha12171.pow 1)))

@[irreducible]
def a12212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00101 ^ 1 * a12211 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a06726 ^ 1)
theorem ha12212 : a12212.IsHomogeneous 172 := by
  unfold a12212
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha12211.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha06726.pow 1)))

@[irreducible]
def a12213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12212 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a10758 ^ 1)
theorem ha12213 : a12213.IsHomogeneous 178 := by
  unfold a12213
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12212.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha10758.pow 1)))

@[irreducible]
def a12214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10759 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a12213 ^ 1)
theorem ha12214 : a12214.IsHomogeneous 178 := by
  unfold a12214
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10759.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha12213.pow 1)))

@[irreducible]
def a12215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10760 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12214 ^ 1)
theorem ha12215 : a12215.IsHomogeneous 178 := by
  unfold a12215
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10760.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12214.pow 1)))

@[irreducible]
def a12216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10760 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a12215 ^ 1)
theorem ha12216 : a12216.IsHomogeneous 178 := by
  unfold a12216
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10760.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha12215.pow 1)))

@[irreducible]
def a12217 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00101 ^ 1 * a12216 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a06730 ^ 1)
theorem ha12217 : a12217.IsHomogeneous 264 := by
  unfold a12217
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha12216.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha06730.pow 1)))

@[irreducible]
def a12218 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00101 ^ 1 * a12217 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10730 ^ 1)
theorem ha12218 : a12218.IsHomogeneous 350 := by
  unfold a12218
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha12217.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10730.pow 1)))

@[irreducible]
def a12219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10731 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a12218 ^ 1)
theorem ha12219 : a12219.IsHomogeneous 430 := by
  unfold a12219
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10731.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha12218.pow 1)))

@[irreducible]
def a12220 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a12219 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a10732 ^ 1)
theorem ha12220 : a12220.IsHomogeneous 510 := by
  unfold a12220
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha12219.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10732.pow 1)))

@[irreducible]
def a12221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a10756 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12220 ^ 1)
theorem ha12221 : a12221.IsHomogeneous 510 := by
  unfold a12221
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha10756.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12220.pow 1)))

@[irreducible]
def a12222 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a12221 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00101 ^ 1 * a00295 ^ 1 * a06734 ^ 1)
theorem ha12222 : a12222.IsHomogeneous 893 := by
  unfold a12222
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha12221.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00101.pow 1)).mul (ha00295.pow 1)).mul (ha06734.pow 1)))

@[irreducible]
def a12223 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12222 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00101 ^ 1 * a10720 ^ 1)
theorem ha12223 : a12223.IsHomogeneous 1147 := by
  unfold a12223
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12222.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00101.pow 1)).mul (ha10720.pow 1)))

@[irreducible]
def a12224 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12223 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00101 ^ 1 * a10721 ^ 1)
theorem ha12224 : a12224.IsHomogeneous 1401 := by
  unfold a12224
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12223.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00101.pow 1)).mul (ha10721.pow 1)))

@[irreducible]
def a12225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12224 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00101 ^ 1 * a10722 ^ 1)
theorem ha12225 : a12225.IsHomogeneous 1655 := by
  unfold a12225
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12224.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00101.pow 1)).mul (ha10722.pow 1)))

@[irreducible]
def a12226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12225 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00101 ^ 1 * a10726 ^ 1)
theorem ha12226 : a12226.IsHomogeneous 1909 := by
  unfold a12226
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12225.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00101.pow 1)).mul (ha10726.pow 1)))

@[irreducible]
def a12227 : Poly := (C ((-5 : ℂ) / (144 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01871 ^ 1 * a01880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00800 ^ 1 * a03851 ^ 1)
theorem ha12227 : a12227.IsHomogeneous 1181 := by
  unfold a12227
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (144 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01871.pow 1)).mul (ha01880.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00800.pow 1)).mul (ha03851.pow 1)))

@[irreducible]
def a12228 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a01871 ^ 1 * a01880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00795 ^ 1 * a03865 ^ 1)
theorem ha12228 : a12228.IsHomogeneous 926 := by
  unfold a12228
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha01871.pow 1)).mul (ha01880.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00795.pow 1)).mul (ha03865.pow 1)))

@[irreducible]
def a12229 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12227 ^ 1) + (C ((5 : ℂ) / (648 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12228 ^ 1)
theorem ha12229 : a12229.IsHomogeneous 1181 := by
  unfold a12229
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12227.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (648 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12228.pow 1)))

@[irreducible]
def a12230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00294 ^ 1 * a07192 ^ 1) + (C ((3 : ℂ) / (40 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00800 ^ 1 * a03851 ^ 1)
theorem ha12230 : a12230.IsHomogeneous 1435 := by
  unfold a12230
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00294.pow 1)).mul (ha07192.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (40 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00800.pow 1)).mul (ha03851.pow 1)))

@[irreducible]
def a12231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12230 ^ 1) + (C ((3 : ℂ) / (40 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12227 ^ 1)
theorem ha12231 : a12231.IsHomogeneous 1435 := by
  unfold a12231
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12230.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (40 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12227.pow 1)))

@[irreducible]
def a12232 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12231 ^ 1) + (C ((3 : ℂ) / (40 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12229 ^ 1)
theorem ha12232 : a12232.IsHomogeneous 1435 := by
  unfold a12232
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12231.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (40 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12229.pow 1)))

@[irreducible]
def a12233 : Poly := (C ((-5 : ℂ) / (96 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a07212 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00795 ^ 1 * a03865 ^ 1)
theorem ha12233 : a12233.IsHomogeneous 671 := by
  unfold a12233
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (96 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha07212.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00795.pow 1)).mul (ha03865.pow 1)))

@[irreducible]
def a12234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12233 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12228 ^ 1)
theorem ha12234 : a12234.IsHomogeneous 926 := by
  unfold a12234
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12233.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12228.pow 1)))

@[irreducible]
def a12235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12229 ^ 1) + (C ((5 : ℂ) / (648 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12234 ^ 1)
theorem ha12235 : a12235.IsHomogeneous 1181 := by
  unfold a12235
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12229.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (648 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12234.pow 1)))

@[irreducible]
def a12236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12232 ^ 1) + (C ((3 : ℂ) / (40 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a12235 ^ 1)
theorem ha12236 : a12236.IsHomogeneous 1435 := by
  unfold a12236
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12232.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (40 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha12235.pow 1)))

@[irreducible]
def a12237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a01830 ^ 1 * a01868 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00793 ^ 1 * a03775 ^ 1)
theorem ha12237 : a12237.IsHomogeneous 1320 := by
  unfold a12237
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha01830.pow 1)).mul (ha01868.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00793.pow 1)).mul (ha03775.pow 1)))

@[irreducible]
def a12238 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a01830 ^ 1 * a01868 ^ 1) + (C ((16 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00778 ^ 1 * a03847 ^ 1)
theorem ha12238 : a12238.IsHomogeneous 1338 := by
  unfold a12238
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha01830.pow 1)).mul (ha01868.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00778.pow 1)).mul (ha03847.pow 1)))

@[irreducible]
def a12239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a12238 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12237 ^ 1)
theorem ha12239 : a12239.IsHomogeneous 1380 := by
  unfold a12239
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha12238.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12237.pow 1)))

@[irreducible]
def a12240 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a00291 ^ 1 * a07062 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a00793 ^ 1 * a03775 ^ 1)
theorem ha12240 : a12240.IsHomogeneous 1247 := by
  unfold a12240
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00291.pow 1)).mul (ha07062.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha00793.pow 1)).mul (ha03775.pow 1)))

@[irreducible]
def a12241 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00124 ^ 1 * a12240 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a12237 ^ 1)
theorem ha12241 : a12241.IsHomogeneous 1362 := by
  unfold a12241
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha12240.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha12237.pow 1)))

@[irreducible]
def a12242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12241 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a12239 ^ 1)
theorem ha12242 : a12242.IsHomogeneous 1422 := by
  unfold a12242
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12241.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha12239.pow 1)))

@[irreducible]
def a12243 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00778 ^ 1 * a03847 ^ 1) + (C ((10 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00287 ^ 1 * a07187 ^ 1)
theorem ha12243 : a12243.IsHomogeneous 1356 := by
  unfold a12243
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00778.pow 1)).mul (ha03847.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00287.pow 1)).mul (ha07187.pow 1)))

@[irreducible]
def a12244 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12238 ^ 1) + (C ((16 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a12243 ^ 1)
theorem ha12244 : a12244.IsHomogeneous 1398 := by
  unfold a12244
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12238.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha12243.pow 1)))

@[irreducible]
def a12245 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a12244 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12239 ^ 1)
theorem ha12245 : a12245.IsHomogeneous 1440 := by
  unfold a12245
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha12244.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12239.pow 1)))

@[irreducible]
def a12246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a12242 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00103 ^ 1 * a12245 ^ 1)
theorem ha12246 : a12246.IsHomogeneous 1482 := by
  unfold a12246
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha12242.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00103.pow 1)).mul (ha12245.pow 1)))

@[irreducible]
def a12247 : Poly := (C ((-1 : ℂ) / (108 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00776 ^ 1 * a03612 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01739 ^ 1 * a01827 ^ 1)
theorem ha12247 : a12247.IsHomogeneous 624 := by
  unfold a12247
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (108 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00776.pow 1)).mul (ha03612.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01739.pow 1)).mul (ha01827.pow 1)))

@[irreducible]
def a12248 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a01739 ^ 1 * a01827 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00734 ^ 1 * a03771 ^ 1)
theorem ha12248 : a12248.IsHomogeneous 769 := by
  unfold a12248
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha01739.pow 1)).mul (ha01827.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00734.pow 1)).mul (ha03771.pow 1)))

@[irreducible]
def a12249 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12247 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12248 ^ 1)
theorem ha12249 : a12249.IsHomogeneous 769 := by
  unfold a12249
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12247.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12248.pow 1)))

@[irreducible]
def a12250 : Poly := (C ((-5 : ℂ) / (72 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00286 ^ 1 * a06799 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00776 ^ 1 * a03612 ^ 1)
theorem ha12250 : a12250.IsHomogeneous 479 := by
  unfold a12250
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00286.pow 1)).mul (ha06799.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00776.pow 1)).mul (ha03612.pow 1)))

@[irreducible]
def a12251 : Poly := (C ((-1 : ℂ) / (108 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12247 ^ 1)
theorem ha12251 : a12251.IsHomogeneous 624 := by
  unfold a12251
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (108 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12250.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12247.pow 1)))

@[irreducible]
def a12252 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12251 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12249 ^ 1)
theorem ha12252 : a12252.IsHomogeneous 769 := by
  unfold a12252
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12251.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12249.pow 1)))

@[irreducible]
def a12253 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00734 ^ 1 * a03771 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00271 ^ 1 * a07057 ^ 1)
theorem ha12253 : a12253.IsHomogeneous 859 := by
  unfold a12253
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00734.pow 1)).mul (ha03771.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00271.pow 1)).mul (ha07057.pow 1)))

@[irreducible]
def a12254 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a12253 ^ 1)
theorem ha12254 : a12254.IsHomogeneous 914 := by
  unfold a12254
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha12253.pow 1)))

@[irreducible]
def a12255 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12249 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12254 ^ 1)
theorem ha12255 : a12255.IsHomogeneous 914 := by
  unfold a12255
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12249.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12254.pow 1)))

@[irreducible]
def a12256 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a12252 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12255 ^ 1)
theorem ha12256 : a12256.IsHomogeneous 914 := by
  unfold a12256
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha12252.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12255.pow 1)))

@[irreducible]
def a12257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00732 ^ 1 * a03604 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a01726 ^ 1 * a01736 ^ 1)
theorem ha12257 : a12257.IsHomogeneous 187 := by
  unfold a12257
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00732.pow 1)).mul (ha03604.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha01726.pow 1)).mul (ha01736.pow 1)))

@[irreducible]
def a12258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00105 ^ 1 * a00724 ^ 1 * a03608 ^ 1) + (C ((1 : ℂ) / (28 : ℂ)) * a01726 ^ 1 * a01736 ^ 1)
theorem ha12258 : a12258.IsHomogeneous 187 := by
  unfold a12258
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00105.pow 1)).mul (ha00724.pow 1)).mul (ha03608.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (28 : ℂ))).mul (ha01726.pow 1)).mul (ha01736.pow 1)))

@[irreducible]
def a12259 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12257 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a12258 ^ 1)
theorem ha12259 : a12259.IsHomogeneous 187 := by
  unfold a12259
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12257.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha12258.pow 1)))

@[irreducible]
def a12260 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00732 ^ 1 * a03604 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00270 ^ 1 * a06790 ^ 1)
theorem ha12260 : a12260.IsHomogeneous 187 := by
  unfold a12260
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00732.pow 1)).mul (ha03604.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00270.pow 1)).mul (ha06790.pow 1)))

@[irreducible]
def a12261 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12257 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12260 ^ 1)
theorem ha12261 : a12261.IsHomogeneous 187 := by
  unfold a12261
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12257.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12260.pow 1)))

@[irreducible]
def a12262 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12259 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12261 ^ 1)
theorem ha12262 : a12262.IsHomogeneous 187 := by
  unfold a12262
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12259.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12261.pow 1)))

@[irreducible]
def a12263 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00724 ^ 1) + (C ((1 : ℂ) / (16 : ℂ)) * a00105 ^ 1 * a00265 ^ 1)
theorem ha12263 : a12263.IsHomogeneous 110 := by
  unfold a12263
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00724.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (16 : ℂ))).mul (ha00105.pow 1)).mul (ha00265.pow 1)))

@[irreducible]
def a12264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00105 ^ 1 * a03608 ^ 1 * a12263 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12258 ^ 1)
theorem ha12264 : a12264.IsHomogeneous 187 := by
  unfold a12264
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00105.pow 1)).mul (ha03608.pow 1)).mul (ha12263.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12258.pow 1)))

@[irreducible]
def a12265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12259 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a12264 ^ 1)
theorem ha12265 : a12265.IsHomogeneous 187 := by
  unfold a12265
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12259.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha12264.pow 1)))

@[irreducible]
def a12266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12265 ^ 1)
theorem ha12266 : a12266.IsHomogeneous 187 := by
  unfold a12266
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12262.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12265.pow 1)))

@[irreducible]
def a12267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00785 ^ 1 * a03601 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a01724 ^ 1 * a01852 ^ 1)
theorem ha12267 : a12267.IsHomogeneous 162 := by
  unfold a12267
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00785.pow 1)).mul (ha03601.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha01724.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a12268 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00723 ^ 1 * a03819 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01724 ^ 1 * a01852 ^ 1)
theorem ha12268 : a12268.IsHomogeneous 162 := by
  unfold a12268
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00723.pow 1)).mul (ha03819.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01724.pow 1)).mul (ha01852.pow 1)))

@[irreducible]
def a12269 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12267 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a12268 ^ 1)
theorem ha12269 : a12269.IsHomogeneous 162 := by
  unfold a12269
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12267.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha12268.pow 1)))

@[irreducible]
def a12270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00105 ^ 1 * a00265 ^ 1 * a06786 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00785 ^ 1 * a03601 ^ 1)
theorem ha12270 : a12270.IsHomogeneous 162 := by
  unfold a12270
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha06786.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00785.pow 1)).mul (ha03601.pow 1)))

@[irreducible]
def a12271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12267 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a12270 ^ 1)
theorem ha12271 : a12271.IsHomogeneous 162 := by
  unfold a12271
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12267.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha12270.pow 1)))

@[irreducible]
def a12272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12269 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12271 ^ 1)
theorem ha12272 : a12272.IsHomogeneous 162 := by
  unfold a12272
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12271.pow 1)))

@[irreducible]
def a12273 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00265 ^ 1 * a07143 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00723 ^ 1 * a03819 ^ 1)
theorem ha12273 : a12273.IsHomogeneous 162 := by
  unfold a12273
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00265.pow 1)).mul (ha07143.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00723.pow 1)).mul (ha03819.pow 1)))

@[irreducible]
def a12274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12268 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a12273 ^ 1)
theorem ha12274 : a12274.IsHomogeneous 162 := by
  unfold a12274
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12268.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha12273.pow 1)))

@[irreducible]
def a12275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12269 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a12274 ^ 1)
theorem ha12275 : a12275.IsHomogeneous 162 := by
  unfold a12275
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha12274.pow 1)))

@[irreducible]
def a12276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12272 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12275 ^ 1)
theorem ha12276 : a12276.IsHomogeneous 162 := by
  unfold a12276
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12272.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12275.pow 1)))

@[irreducible]
def a12277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a06772 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03590 ^ 1)
theorem ha12277 : a12277.IsHomogeneous 42 := by
  unfold a12277
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha06772.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03590.pow 1)))

@[irreducible]
def a12278 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12277 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a06973 ^ 1)
theorem ha12278 : a12278.IsHomogeneous 42 := by
  unfold a12278
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12277.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha06973.pow 1)))

@[irreducible]
def a12279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12278 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 2 * a06974 ^ 1)
theorem ha12279 : a12279.IsHomogeneous 42 := by
  unfold a12279
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12278.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 2)).mul (ha06974.pow 1)))

@[irreducible]
def a12280 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12279 ^ 1) + (C ((35 : ℂ) / (6 : ℂ)) * a00003 ^ 2 * a06975 ^ 1)
theorem ha12280 : a12280.IsHomogeneous 42 := by
  unfold a12280
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12279.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (6 : ℂ))).mul (ha00003.pow 2)).mul (ha06975.pow 1)))

@[irreducible]
def a12281 : Poly := (C ((-7 : ℂ) / (87480 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 3 * a00004 ^ 6 * a00005 ^ 3) + (C ((-1 : ℂ) / (3240 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a10779 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00102 ^ 1 * a07557 ^ 1)
theorem ha12281 : a12281.IsHomogeneous 36 := by
  unfold a12281
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (87480 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3240 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha10779.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00102.pow 1)).mul (ha07557.pow 1)))

@[irreducible]
def a12282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a12281 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a06772 ^ 1)
theorem ha12282 : a12282.IsHomogeneous 42 := by
  unfold a12282
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha12281.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha06772.pow 1)))

@[irreducible]
def a12283 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12277 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a12282 ^ 1)
theorem ha12283 : a12283.IsHomogeneous 42 := by
  unfold a12283
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12277.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha12282.pow 1)))

@[irreducible]
def a12284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12278 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12283 ^ 1)
theorem ha12284 : a12284.IsHomogeneous 42 := by
  unfold a12284
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12278.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12283.pow 1)))

@[irreducible]
def a12285 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12279 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12284 ^ 1)
theorem ha12285 : a12285.IsHomogeneous 42 := by
  unfold a12285
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12279.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12284.pow 1)))

@[irreducible]
def a12286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12280 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12285 ^ 1)
theorem ha12286 : a12286.IsHomogeneous 42 := by
  unfold a12286
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12280.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12285.pow 1)))

@[irreducible]
def a12287 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a06976 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a12280 ^ 1)
theorem ha12287 : a12287.IsHomogeneous 42 := by
  unfold a12287
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha06976.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha12280.pow 1)))

end CycleQ2Concrete
