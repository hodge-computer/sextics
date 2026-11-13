import Proposal.CurrentAtoms001

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a01024 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01020 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a01014 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01005 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00014 ^ 1 * a01023 ^ 1)
theorem ha01024 : a01024.IsHomogeneous 48 := by
  unfold a01024
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01020.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha01014.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01005.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00014.pow 1)).mul (ha01023.pow 1)))

@[irreducible]
def a01025 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00100 ^ 1 * a00362 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00046 ^ 1 * a00100 ^ 2 * a00134 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00082 ^ 1 * a00445 ^ 1)
theorem ha01025 : a01025.IsHomogeneous 196 := by
  unfold a01025
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00100.pow 1)).mul (ha00362.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00046.pow 1)).mul (ha00100.pow 2)).mul (ha00134.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00082.pow 1)).mul (ha00445.pow 1)))

@[irreducible]
def a01026 : Poly := (C ((-3 : ℂ) / (40 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 5 * a00100 ^ 3 * a01024 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01025 ^ 1)
theorem ha01026 : a01026.IsHomogeneous 196 := by
  unfold a01026
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (40 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 5)).mul (ha00100.pow 3)).mul (ha01024.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01025.pow 1)))

@[irreducible]
def a01027 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 3 * a00125 ^ 1 * a00126 ^ 2 * a00127 ^ 1 * a01026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00997 ^ 1)
theorem ha01027 : a01027.IsHomogeneous 455 := by
  unfold a01027
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00125.pow 1)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha01026.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00997.pow 1)))

@[irreducible]
def a01028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a01027 ^ 1) + (C ((125 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00042 ^ 2 * a00126 ^ 1 * a00364 ^ 1 * a00445 ^ 1)
theorem ha01028 : a01028.IsHomogeneous 932 := by
  unfold a01028
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha01027.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((125 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 2)).mul (ha00126.pow 1)).mul (ha00364.pow 1)).mul (ha00445.pow 1)))

@[irreducible]
def a01029 : Poly := (C ((-1 : ℂ) / (48 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a00014 ^ 1 * a00211 ^ 1) + (C ((1 : ℂ) / (240 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 1 * a00260 ^ 1)
theorem ha01029 : a01029.IsHomogeneous 66 := by
  unfold a01029
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (48 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00241.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00211.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (240 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a01030 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a00365 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00125 ^ 1 * a01029 ^ 1)
theorem ha01030 : a01030.IsHomogeneous 135 := by
  unfold a01030
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha00365.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00125.pow 1)).mul (ha01029.pow 1)))

@[irreducible]
def a01031 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00241 ^ 1)
theorem ha01031 : a01031.IsHomogeneous 55 := by
  unfold a01031
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a01032 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00261 ^ 1 * a00366 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a01031 ^ 1)
theorem ha01032 : a01032.IsHomogeneous 134 := by
  unfold a01032
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00261.pow 1)).mul (ha00366.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha01031.pow 1)))

@[irreducible]
def a01033 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01030 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00004 ^ 1 * a01032 ^ 1)
theorem ha01033 : a01033.IsHomogeneous 135 := by
  unfold a01033
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01030.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00004.pow 1)).mul (ha01032.pow 1)))

@[irreducible]
def a01034 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a00367 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01033 ^ 1)
theorem ha01034 : a01034.IsHomogeneous 413 := by
  unfold a01034
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha00367.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01033.pow 1)))

@[irreducible]
def a01035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a00367 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a01034 ^ 1)
theorem ha01035 : a01035.IsHomogeneous 492 := by
  unfold a01035
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha00367.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha01034.pow 1)))

@[irreducible]
def a01036 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a00367 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01035 ^ 1)
theorem ha01036 : a01036.IsHomogeneous 600 := by
  unfold a01036
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha00367.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01035.pow 1)))

@[irreducible]
def a01037 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a00367 ^ 1)
theorem ha01037 : a01037.IsHomogeneous 576 := by
  unfold a01037
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha00367.pow 1)))

@[irreducible]
def a01038 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a00452 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a00492 ^ 1)
theorem ha01038 : a01038.IsHomogeneous 708 := by
  unfold a01038
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha00452.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha00492.pow 1)))

@[irreducible]
def a01039 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a00452 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a00501 ^ 1)
theorem ha01039 : a01039.IsHomogeneous 648 := by
  unfold a01039
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha00452.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha00501.pow 1)))

@[irreducible]
def a01040 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha01040 : a01040.IsHomogeneous 12 := by
  unfold a01040
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01041 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a01040 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00176 ^ 1)
theorem ha01041 : a01041.IsHomogeneous 12 := by
  unfold a01041
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha01040.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00176.pow 1)))

@[irreducible]
def a01042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01041 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00303 ^ 1 * a00368 ^ 1)
theorem ha01042 : a01042.IsHomogeneous 120 := by
  unfold a01042
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00303.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a01043 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00148 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00480 ^ 1)
theorem ha01043 : a01043.IsHomogeneous 145 := by
  unfold a01043
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00148.pow 1)).mul (ha00455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00480.pow 1)))

@[irreducible]
def a01044 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01043 ^ 1) + (C ((4 : ℂ) / (225 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a00014 ^ 2 * a01042 ^ 1)
theorem ha01044 : a01044.IsHomogeneous 145 := by
  unfold a01044
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01043.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (225 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha01042.pow 1)))

@[irreducible]
def a01045 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1)
theorem ha01045 : a01045.IsHomogeneous 27 := by
  unfold a01045
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a01046 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a01045 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00042 ^ 1)
theorem ha01046 : a01046.IsHomogeneous 33 := by
  unfold a01046
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha01045.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a01047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00133 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00032 ^ 1)
theorem ha01047 : a01047.IsHomogeneous 18 := by
  unfold a01047
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a01048 : Poly := (C ((-1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a01047 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01046 ^ 1)
theorem ha01048 : a01048.IsHomogeneous 33 := by
  unfold a01048
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha01047.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01046.pow 1)))

@[irreducible]
def a01049 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00370 ^ 1)
theorem ha01049 : a01049.IsHomogeneous 72 := by
  unfold a01049
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00370.pow 1)))

@[irreducible]
def a01050 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a00459 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a00484 ^ 1)
theorem ha01050 : a01050.IsHomogeneous 139 := by
  unfold a01050
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00459.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha00484.pow 1)))

@[irreducible]
def a01051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01050 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1 * a01049 ^ 1)
theorem ha01051 : a01051.IsHomogeneous 139 := by
  unfold a01051
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01050.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha01049.pow 1)))

@[irreducible]
def a01052 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00006 ^ 1 * a00131 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1)
theorem ha01052 : a01052.IsHomogeneous 17 := by
  unfold a01052
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00006.pow 1)).mul (ha00131.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)))

@[irreducible]
def a01053 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a01052 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00301 ^ 1 * a00372 ^ 1)
theorem ha01053 : a01053.IsHomogeneous 115 := by
  unfold a01053
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha01052.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00301.pow 1)).mul (ha00372.pow 1)))

@[irreducible]
def a01054 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00146 ^ 1 * a00461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a00476 ^ 1)
theorem ha01054 : a01054.IsHomogeneous 121 := by
  unfold a01054
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha00461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha00476.pow 1)))

@[irreducible]
def a01055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01054 ^ 1) + (C ((3 : ℂ) / (50 : ℂ)) * a00014 ^ 1 * a01053 ^ 1)
theorem ha01055 : a01055.IsHomogeneous 121 := by
  unfold a01055
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01054.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (50 : ℂ))).mul (ha00014.pow 1)).mul (ha01053.pow 1)))

@[irreducible]
def a01056 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01041 ^ 1)
theorem ha01056 : a01056.IsHomogeneous 36 := by
  unfold a01056
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a01057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1)
theorem ha01057 : a01057.IsHomogeneous 12 := by
  unfold a01057
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)))

@[irreducible]
def a01058 : Poly := (C ((-8 : ℂ) / (81 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01056 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01057 ^ 1)
theorem ha01058 : a01058.IsHomogeneous 43 := by
  unfold a01058
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (81 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01056.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01057.pow 1)))

@[irreducible]
def a01059 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00155 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha01059 : a01059.IsHomogeneous 36 := by
  unfold a01059
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a01060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01058 ^ 1) + (C ((4 : ℂ) / (81 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01059 ^ 1)
theorem ha01060 : a01060.IsHomogeneous 43 := by
  unfold a01060
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01058.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (81 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01059.pow 1)))

@[irreducible]
def a01061 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00375 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01060 ^ 1)
theorem ha01061 : a01061.IsHomogeneous 79 := by
  unfold a01061
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00375.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01060.pow 1)))

@[irreducible]
def a01062 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00139 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00465 ^ 1)
theorem ha01062 : a01062.IsHomogeneous 79 := by
  unfold a01062
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00139.pow 1)).mul (ha00241.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00465.pow 1)))

@[irreducible]
def a01063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01061 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a01062 ^ 1)
theorem ha01063 : a01063.IsHomogeneous 79 := by
  unfold a01063
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01061.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha01062.pow 1)))

@[irreducible]
def a01064 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00061 ^ 1 * a00300 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00211 ^ 1)
theorem ha01064 : a01064.IsHomogeneous 102 := by
  unfold a01064
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00061.pow 1)).mul (ha00300.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00211.pow 1)))

@[irreducible]
def a01065 : Poly := (C ((-9 : ℂ) / (320 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01063 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01064 ^ 1)
theorem ha01065 : a01065.IsHomogeneous 102 := by
  unfold a01065
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (320 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01063.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01064.pow 1)))

@[irreducible]
def a01066 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01056 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01057 ^ 1)
theorem ha01066 : a01066.IsHomogeneous 43 := by
  unfold a01066
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01056.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01057.pow 1)))

@[irreducible]
def a01067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01066 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01059 ^ 1)
theorem ha01067 : a01067.IsHomogeneous 43 := by
  unfold a01067
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01066.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01059.pow 1)))

@[irreducible]
def a01068 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00379 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01067 ^ 1)
theorem ha01068 : a01068.IsHomogeneous 79 := by
  unfold a01068
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00379.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01067.pow 1)))

@[irreducible]
def a01069 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00141 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00469 ^ 1)
theorem ha01069 : a01069.IsHomogeneous 79 := by
  unfold a01069
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00141.pow 1)).mul (ha00241.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00469.pow 1)))

@[irreducible]
def a01070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01068 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a01069 ^ 1)
theorem ha01070 : a01070.IsHomogeneous 79 := by
  unfold a01070
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01068.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha01069.pow 1)))

@[irreducible]
def a01071 : Poly := (C ((-1 : ℂ) / (40 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01070 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01064 ^ 1)
theorem ha01071 : a01071.IsHomogeneous 102 := by
  unfold a01071
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (40 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01070.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01064.pow 1)))

@[irreducible]
def a01072 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a01071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01065 ^ 1)
theorem ha01072 : a01072.IsHomogeneous 102 := by
  unfold a01072
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha01071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01065.pow 1)))

@[irreducible]
def a01073 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01056 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01057 ^ 1)
theorem ha01073 : a01073.IsHomogeneous 43 := by
  unfold a01073
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01056.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01057.pow 1)))

@[irreducible]
def a01074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01073 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01059 ^ 1)
theorem ha01074 : a01074.IsHomogeneous 43 := by
  unfold a01074
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01073.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01059.pow 1)))

@[irreducible]
def a01075 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00384 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01074 ^ 1)
theorem ha01075 : a01075.IsHomogeneous 79 := by
  unfold a01075
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00384.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01074.pow 1)))

@[irreducible]
def a01076 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00144 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00473 ^ 1)
theorem ha01076 : a01076.IsHomogeneous 79 := by
  unfold a01076
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00144.pow 1)).mul (ha00241.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00473.pow 1)))

@[irreducible]
def a01077 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01075 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a01076 ^ 1)
theorem ha01077 : a01077.IsHomogeneous 79 := by
  unfold a01077
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01075.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha01076.pow 1)))

@[irreducible]
def a01078 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01077 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01064 ^ 1)
theorem ha01078 : a01078.IsHomogeneous 102 := by
  unfold a01078
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01077.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01064.pow 1)))

@[irreducible]
def a01079 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a01078 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01072 ^ 1)
theorem ha01079 : a01079.IsHomogeneous 102 := by
  unfold a01079
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha01078.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01072.pow 1)))

@[irreducible]
def a01080 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a00387 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a01079 ^ 1)
theorem ha01080 : a01080.IsHomogeneous 120 := by
  unfold a01080
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha00387.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha01079.pow 1)))

@[irreducible]
def a01081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a01080 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a01055 ^ 1)
theorem ha01081 : a01081.IsHomogeneous 132 := by
  unfold a01081
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha01080.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha01055.pow 1)))

@[irreducible]
def a01082 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00388 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01081 ^ 1)
theorem ha01082 : a01082.IsHomogeneous 132 := by
  unfold a01082
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00388.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01081.pow 1)))

@[irreducible]
def a01083 : Poly := (C ((-9 : ℂ) / (1600 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a01051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 3 * a01082 ^ 1)
theorem ha01083 : a01083.IsHomogeneous 150 := by
  unfold a01083
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1600 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha01051.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 3)).mul (ha01082.pow 1)))

@[irreducible]
def a01084 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00389 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01083 ^ 1)
theorem ha01084 : a01084.IsHomogeneous 180 := by
  unfold a01084
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00389.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01083.pow 1)))

@[irreducible]
def a01085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01084 ^ 1) + (C ((1 : ℂ) / (16 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a01044 ^ 1)
theorem ha01085 : a01085.IsHomogeneous 180 := by
  unfold a01085
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01084.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (16 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha01044.pow 1)))

@[irreducible]
def a01086 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a00489 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a00492 ^ 1)
theorem ha01086 : a01086.IsHomogeneous 296 := by
  unfold a01086
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha00489.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha00492.pow 1)))

@[irreducible]
def a01087 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00100 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1)
theorem ha01087 : a01087.IsHomogeneous 42 := by
  unfold a01087
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00100.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)))

@[irreducible]
def a01088 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00082 ^ 1 * a00100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00487 ^ 1)
theorem ha01088 : a01088.IsHomogeneous 85 := by
  unfold a01088
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00487.pow 1)))

@[irreducible]
def a01089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01088 ^ 1) + (C ((3 : ℂ) / (10 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00100 ^ 1 * a01087 ^ 1)
theorem ha01089 : a01089.IsHomogeneous 85 := by
  unfold a01089
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01088.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (10 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha01087.pow 1)))

@[irreducible]
def a01090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00211 ^ 1)
theorem ha01090 : a01090.IsHomogeneous 84 := by
  unfold a01090
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)))

@[irreducible]
def a01091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 1 * a00241 ^ 1) + (C ((72 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a01090 ^ 1)
theorem ha01091 : a01091.IsHomogeneous 97 := by
  unfold a01091
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha00241.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha01090.pow 1)))

@[irreducible]
def a01092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01091 ^ 1) + (C ((72 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a01090 ^ 1)
theorem ha01092 : a01092.IsHomogeneous 97 := by
  unfold a01092
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01091.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha01090.pow 1)))

@[irreducible]
def a01093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a00393 ^ 1)
theorem ha01093 : a01093.IsHomogeneous 133 := by
  unfold a01093
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha00393.pow 1)))

@[irreducible]
def a01094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1)
theorem ha01094 : a01094.IsHomogeneous 85 := by
  unfold a01094
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)))

@[irreducible]
def a01095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 1 * a01094 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01093 ^ 1)
theorem ha01095 : a01095.IsHomogeneous 133 := by
  unfold a01095
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha01094.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01093.pow 1)))

@[irreducible]
def a01096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00100 ^ 1 * a00211 ^ 1)
theorem ha01096 : a01096.IsHomogeneous 84 := by
  unfold a01096
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)))

@[irreducible]
def a01097 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01095 ^ 1) + (C ((144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a01096 ^ 1)
theorem ha01097 : a01097.IsHomogeneous 133 := by
  unfold a01097
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01095.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha01096.pow 1)))

@[irreducible]
def a01098 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00129 ^ 1 * a00395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01097 ^ 1)
theorem ha01098 : a01098.IsHomogeneous 157 := by
  unfold a01098
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00129.pow 1)).mul (ha00395.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01097.pow 1)))

@[irreducible]
def a01099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01098 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a00100 ^ 1 * a01089 ^ 1)
theorem ha01099 : a01099.IsHomogeneous 157 := by
  unfold a01099
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01098.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha01089.pow 1)))

@[irreducible]
def a01100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a00396 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01099 ^ 1)
theorem ha01100 : a01100.IsHomogeneous 229 := by
  unfold a01100
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha00396.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01099.pow 1)))

@[irreducible]
def a01101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a00126 ^ 1 * a01100 ^ 1) + (C ((27 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a01086 ^ 1)
theorem ha01101 : a01101.IsHomogeneous 301 := by
  unfold a01101
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha01100.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01086.pow 1)))

@[irreducible]
def a01102 : Poly := (C ((-48 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00042 ^ 2 * a00100 ^ 2 * a01085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01101 ^ 1)
theorem ha01102 : a01102.IsHomogeneous 301 := by
  unfold a01102
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 2)).mul (ha01085.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01101.pow 1)))

@[irreducible]
def a01103 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a01102 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a00398 ^ 1)
theorem ha01103 : a01103.IsHomogeneous 301 := by
  unfold a01103
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha01102.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha00398.pow 1)))

@[irreducible]
def a01104 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a00398 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a01103 ^ 1)
theorem ha01104 : a01104.IsHomogeneous 727 := by
  unfold a01104
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha00398.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a01105 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01041 ^ 1)
theorem ha01105 : a01105.IsHomogeneous 42 := by
  unfold a01105
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a01106 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01105 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00025 ^ 1 * a00455 ^ 1)
theorem ha01106 : a01106.IsHomogeneous 49 := by
  unfold a01106
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01105.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a01107 : Poly := (C ((-2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01105 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01106 ^ 1)
theorem ha01107 : a01107.IsHomogeneous 49 := by
  unfold a01107
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01105.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01106.pow 1)))

@[irreducible]
def a01108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a01107 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a00400 ^ 1)
theorem ha01108 : a01108.IsHomogeneous 67 := by
  unfold a01108
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha01107.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha00400.pow 1)))

@[irreducible]
def a01109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a00494 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a00461 ^ 1)
theorem ha01109 : a01109.IsHomogeneous 60 := by
  unfold a01109
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha00494.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha00461.pow 1)))

@[irreducible]
def a01110 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a01108 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a01109 ^ 1)
theorem ha01110 : a01110.IsHomogeneous 73 := by
  unfold a01110
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha01108.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha01109.pow 1)))

@[irreducible]
def a01111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00298 ^ 1 * a00372 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00126 ^ 1 * a01052 ^ 1)
theorem ha01111 : a01111.IsHomogeneous 49 := by
  unfold a01111
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00298.pow 1)).mul (ha00372.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00126.pow 1)).mul (ha01052.pow 1)))

@[irreducible]
def a01112 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01110 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01111 ^ 1)
theorem ha01112 : a01112.IsHomogeneous 79 := by
  unfold a01112
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01110.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01111.pow 1)))

@[irreducible]
def a01113 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00402 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01112 ^ 1)
theorem ha01113 : a01113.IsHomogeneous 85 := by
  unfold a01113
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00402.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01112.pow 1)))

@[irreducible]
def a01114 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00126 ^ 1 * a00153 ^ 1 * a00484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00501 ^ 1)
theorem ha01114 : a01114.IsHomogeneous 212 := by
  unfold a01114
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha00484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00501.pow 1)))

@[irreducible]
def a01115 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a00393 ^ 1)
theorem ha01115 : a01115.IsHomogeneous 181 := by
  unfold a01115
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha00393.pow 1)))

@[irreducible]
def a01116 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a01114 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00126 ^ 1 * a01115 ^ 1)
theorem ha01116 : a01116.IsHomogeneous 217 := by
  unfold a01116
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01114.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00126.pow 1)).mul (ha01115.pow 1)))

@[irreducible]
def a01117 : Poly := (C ((-9 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00100 ^ 3 * a01113 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01116 ^ 1)
theorem ha01117 : a01117.IsHomogeneous 217 := by
  unfold a01117
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00100.pow 3)).mul (ha01113.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01116.pow 1)))

@[irreducible]
def a01118 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00404 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01117 ^ 1)
theorem ha01118 : a01118.IsHomogeneous 217 := by
  unfold a01118
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00404.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01117.pow 1)))

@[irreducible]
def a01119 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a01118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a00404 ^ 1)
theorem ha01119 : a01119.IsHomogeneous 643 := by
  unfold a01119
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha01118.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha00404.pow 1)))

@[irreducible]
def a01120 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 3 * a00042 ^ 3 * a00100 ^ 1 * a00126 ^ 1 * a01037 ^ 1) + (C ((-16 : ℂ) / (9 : ℂ)) * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 3 * a01119 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a01104 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 3 * a01039 ^ 1) + (C ((2 : ℂ) / (3125 : ℂ)) * a00001 ^ 10 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 4 * a00042 ^ 3 * a00100 ^ 4 * a00296 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00042 ^ 1 * a01038 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 3 * a00042 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a01036 ^ 1)
theorem ha01120 : a01120.IsHomogeneous 739 := by
  unfold a01120
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 3)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha01037.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha01119.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha01104.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha01039.pow 1))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3125 : ℂ))).mul (ha00001.pow 10)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 4)).mul (ha00042.pow 3)).mul (ha00100.pow 4)).mul (ha00296.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00042.pow 1)).mul (ha01038.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha01036.pow 1)))

@[irreducible]
def a01121 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00368 ^ 1) + (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01041 ^ 1)
theorem ha01121 : a01121.IsHomogeneous 36 := by
  unfold a01121
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a01122 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1)
theorem ha01122 : a01122.IsHomogeneous 12 := by
  unfold a01122
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)))

@[irreducible]
def a01123 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01121 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01122 ^ 1)
theorem ha01123 : a01123.IsHomogeneous 43 := by
  unfold a01123
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01121.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01122.pow 1)))

@[irreducible]
def a01124 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01121 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01123 ^ 1)
theorem ha01124 : a01124.IsHomogeneous 43 := by
  unfold a01124
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01121.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01123.pow 1)))

@[irreducible]
def a01125 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha01125 : a01125.IsHomogeneous 36 := by
  unfold a01125
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a01126 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01122 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01125 ^ 1)
theorem ha01126 : a01126.IsHomogeneous 43 := by
  unfold a01126
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01122.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01125.pow 1)))

@[irreducible]
def a01127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01123 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01126 ^ 1)
theorem ha01127 : a01127.IsHomogeneous 43 := by
  unfold a01127
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01123.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01126.pow 1)))

@[irreducible]
def a01128 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01124 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01127 ^ 1)
theorem ha01128 : a01128.IsHomogeneous 43 := by
  unfold a01128
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01124.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01127.pow 1)))

@[irreducible]
def a01129 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01121 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01124 ^ 1)
theorem ha01129 : a01129.IsHomogeneous 43 := by
  unfold a01129
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01121.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01124.pow 1)))

@[irreducible]
def a01130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01128 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01129 ^ 1)
theorem ha01130 : a01130.IsHomogeneous 43 := by
  unfold a01130
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01128.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01129.pow 1)))

@[irreducible]
def a01131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01126 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a01125 ^ 1)
theorem ha01131 : a01131.IsHomogeneous 43 := by
  unfold a01131
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01126.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha01125.pow 1)))

@[irreducible]
def a01132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01127 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01131 ^ 1)
theorem ha01132 : a01132.IsHomogeneous 43 := by
  unfold a01132
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01127.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01131.pow 1)))

@[irreducible]
def a01133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01128 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01132 ^ 1)
theorem ha01133 : a01133.IsHomogeneous 43 := by
  unfold a01133
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01128.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01132.pow 1)))

@[irreducible]
def a01134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01133 ^ 1)
theorem ha01134 : a01134.IsHomogeneous 43 := by
  unfold a01134
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01133.pow 1)))

@[irreducible]
def a01135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00559 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00643 ^ 1)
theorem ha01135 : a01135.IsHomogeneous 53 := by
  unfold a01135
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00559.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00643.pow 1)))

@[irreducible]
def a01136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00559 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00638 ^ 1)
theorem ha01136 : a01136.IsHomogeneous 44 := by
  unfold a01136
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00559.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00638.pow 1)))

@[irreducible]
def a01137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01136 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01135 ^ 1)
theorem ha01137 : a01137.IsHomogeneous 53 := by
  unfold a01137
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01136.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01135.pow 1)))

@[irreducible]
def a01138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01136 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00638 ^ 1)
theorem ha01138 : a01138.IsHomogeneous 44 := by
  unfold a01138
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01136.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00638.pow 1)))

@[irreducible]
def a01139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01138 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01137 ^ 1)
theorem ha01139 : a01139.IsHomogeneous 53 := by
  unfold a01139
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01138.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01137.pow 1)))

@[irreducible]
def a01140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01135 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00643 ^ 1)
theorem ha01140 : a01140.IsHomogeneous 53 := by
  unfold a01140
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01135.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00643.pow 1)))

@[irreducible]
def a01141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01137 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01140 ^ 1)
theorem ha01141 : a01141.IsHomogeneous 53 := by
  unfold a01141
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01137.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01140.pow 1)))

@[irreducible]
def a01142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01139 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01141 ^ 1)
theorem ha01142 : a01142.IsHomogeneous 53 := by
  unfold a01142
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01141.pow 1)))

@[irreducible]
def a01143 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01138 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00638 ^ 1)
theorem ha01143 : a01143.IsHomogeneous 44 := by
  unfold a01143
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01138.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00638.pow 1)))

@[irreducible]
def a01144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01143 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01139 ^ 1)
theorem ha01144 : a01144.IsHomogeneous 53 := by
  unfold a01144
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01143.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01139.pow 1)))

@[irreducible]
def a01145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01142 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01144 ^ 1)
theorem ha01145 : a01145.IsHomogeneous 53 := by
  unfold a01145
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01142.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01144.pow 1)))

@[irreducible]
def a01146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00516 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00663 ^ 1)
theorem ha01146 : a01146.IsHomogeneous 47 := by
  unfold a01146
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00516.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00663.pow 1)))

@[irreducible]
def a01147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00516 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01146 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00663 ^ 1)
theorem ha01147 : a01147.IsHomogeneous 47 := by
  unfold a01147
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00516.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01146.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00663.pow 1)))

@[irreducible]
def a01148 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01146 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00663 ^ 1)
theorem ha01148 : a01148.IsHomogeneous 47 := by
  unfold a01148
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01146.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00663.pow 1)))

@[irreducible]
def a01149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01147 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01148 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00663 ^ 1)
theorem ha01149 : a01149.IsHomogeneous 47 := by
  unfold a01149
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01148.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00663.pow 1)))

@[irreducible]
def a01150 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00516 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00669 ^ 1)
theorem ha01150 : a01150.IsHomogeneous 47 := by
  unfold a01150
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00516.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00669.pow 1)))

@[irreducible]
def a01151 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01146 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01150 ^ 1)
theorem ha01151 : a01151.IsHomogeneous 47 := by
  unfold a01151
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01146.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01150.pow 1)))

@[irreducible]
def a01152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00516 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01150 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00669 ^ 1)
theorem ha01152 : a01152.IsHomogeneous 47 := by
  unfold a01152
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00516.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01150.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00669.pow 1)))

@[irreducible]
def a01153 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01147 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01151 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01152 ^ 1)
theorem ha01153 : a01153.IsHomogeneous 47 := by
  unfold a01153
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01151.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01152.pow 1)))

@[irreducible]
def a01154 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01151 ^ 1)
theorem ha01154 : a01154.IsHomogeneous 47 := by
  unfold a01154
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01148.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01151.pow 1)))

@[irreducible]
def a01155 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01149 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01154 ^ 1)
theorem ha01155 : a01155.IsHomogeneous 47 := by
  unfold a01155
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01149.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01153.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01154.pow 1)))

@[irreducible]
def a01156 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01150 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00669 ^ 1)
theorem ha01156 : a01156.IsHomogeneous 47 := by
  unfold a01156
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01150.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00669.pow 1)))

@[irreducible]
def a01157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01151 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01156 ^ 1)
theorem ha01157 : a01157.IsHomogeneous 47 := by
  unfold a01157
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01151.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01156.pow 1)))

@[irreducible]
def a01158 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01152 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01156 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00669 ^ 1)
theorem ha01158 : a01158.IsHomogeneous 47 := by
  unfold a01158
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01152.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01156.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00669.pow 1)))

@[irreducible]
def a01159 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01157 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01158 ^ 1)
theorem ha01159 : a01159.IsHomogeneous 47 := by
  unfold a01159
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01153.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01157.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01158.pow 1)))

@[irreducible]
def a01160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01154 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01157 ^ 1)
theorem ha01160 : a01160.IsHomogeneous 47 := by
  unfold a01160
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01154.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01157.pow 1)))

@[irreducible]
def a01161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01159 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01160 ^ 1)
theorem ha01161 : a01161.IsHomogeneous 47 := by
  unfold a01161
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01159.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01160.pow 1)))

@[irreducible]
def a01162 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00058 ^ 1 * a00129 ^ 1 * a00156 ^ 1) + (C ((-1 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00058 ^ 1 * a00510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00156 ^ 1 * a00207 ^ 1)
theorem ha01162 : a01162.IsHomogeneous 48 := by
  unfold a01162
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00058.pow 1)).mul (ha00510.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a01163 : Poly := (C ((-48 : ℂ) / (7 : ℂ)) * a01162 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00679 ^ 1)
theorem ha01163 : a01163.IsHomogeneous 48 := by
  unfold a01163
  exact (((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (7 : ℂ))).mul (ha01162.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00679.pow 1)))

@[irreducible]
def a01164 : Poly := (C ((-48 : ℂ) / (7 : ℂ)) * a01162 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00679 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01163 ^ 1)
theorem ha01164 : a01164.IsHomogeneous 48 := by
  unfold a01164
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (7 : ℂ))).mul (ha01162.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00679.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01163.pow 1)))

@[irreducible]
def a01165 : Poly := (C ((-1 : ℂ) / (15552 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00683 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01162 ^ 1)
theorem ha01165 : a01165.IsHomogeneous 48 := by
  unfold a01165
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15552 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01162.pow 1)))

@[irreducible]
def a01166 : Poly := (C ((-1 : ℂ) / (15552 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00683 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01162 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01165 ^ 1)
theorem ha01166 : a01166.IsHomogeneous 48 := by
  unfold a01166
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15552 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01162.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01165.pow 1)))

@[irreducible]
def a01167 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00679 ^ 1) + (C ((1 : ℂ) / (2268 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00683 ^ 1)
theorem ha01167 : a01167.IsHomogeneous 42 := by
  unfold a01167
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00679.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2268 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00683.pow 1)))

@[irreducible]
def a01168 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00679 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01167 ^ 1) + (C ((1 : ℂ) / (2268 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00683 ^ 1)
theorem ha01168 : a01168.IsHomogeneous 42 := by
  unfold a01168
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00679.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01167.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2268 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00683.pow 1)))

@[irreducible]
def a01169 : Poly := (C ((-48 : ℂ) / (7 : ℂ)) * a01166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01164 ^ 1)
theorem ha01169 : a01169.IsHomogeneous 48 := by
  unfold a01169
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (7 : ℂ))).mul (ha01166.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01168.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01164.pow 1)))

@[irreducible]
def a01170 : Poly := (C ((-1 : ℂ) / (7776 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00683 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01165 ^ 1)
theorem ha01170 : a01170.IsHomogeneous 48 := by
  unfold a01170
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (7776 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01165.pow 1)))

@[irreducible]
def a01171 : Poly := (C ((-1 : ℂ) / (5184 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00683 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01166 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01170 ^ 1)
theorem ha01171 : a01171.IsHomogeneous 48 := by
  unfold a01171
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5184 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00683.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01166.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01170.pow 1)))

@[irreducible]
def a01172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01167 ^ 1) + (C ((1 : ℂ) / (1134 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00683 ^ 1)
theorem ha01172 : a01172.IsHomogeneous 42 := by
  unfold a01172
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01167.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1134 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00683.pow 1)))

@[irreducible]
def a01173 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01168 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01172 ^ 1) + (C ((1 : ℂ) / (756 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00683 ^ 1)
theorem ha01173 : a01173.IsHomogeneous 42 := by
  unfold a01173
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01168.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01172.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (756 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00683.pow 1)))

@[irreducible]
def a01174 : Poly := (C ((-48 : ℂ) / (7 : ℂ)) * a01171 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01169 ^ 1)
theorem ha01174 : a01174.IsHomogeneous 48 := by
  unfold a01174
  exact ((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (7 : ℂ))).mul (ha01171.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01173.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01169.pow 1)))

@[irreducible]
def a01175 : Poly := (C ((-7 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a01174 ^ 1) + (C ((-5 : ℂ) / (12 : ℂ)) * a01145 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a01134 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01161 ^ 1)
theorem ha01175 : a01175.IsHomogeneous 53 := by
  unfold a01175
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha01174.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha01145.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha01134.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01161.pow 1)))

@[irreducible]
def a01176 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a00362 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00931 ^ 1)
theorem ha01176 : a01176.IsHomogeneous 188 := by
  unfold a01176
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha00362.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00931.pow 1)))

@[irreducible]
def a01177 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00134 ^ 1 * a00211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00327 ^ 1)
theorem ha01177 : a01177.IsHomogeneous 144 := by
  unfold a01177
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha00211.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00327.pow 1)))

@[irreducible]
def a01178 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a01177 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a01176 ^ 1)
theorem ha01178 : a01178.IsHomogeneous 193 := by
  unfold a01178
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha01177.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01176.pow 1)))

@[irreducible]
def a01179 : Poly := (C ((-3 : ℂ) / (125 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 3 * a00100 ^ 3 * a01175 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01178 ^ 1)
theorem ha01179 : a01179.IsHomogeneous 193 := by
  unfold a01179
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (125 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 3)).mul (ha00100.pow 3)).mul (ha01175.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01178.pow 1)))

@[irreducible]
def a01180 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00445 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01179 ^ 1)
theorem ha01180 : a01180.IsHomogeneous 193 := by
  unfold a01180
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00445.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01179.pow 1)))

@[irreducible]
def a01181 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a01180 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a00445 ^ 1)
theorem ha01181 : a01181.IsHomogeneous 751 := by
  unfold a01181
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha01180.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha00445.pow 1)))

@[irreducible]
def a01182 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00134 ^ 2 * a01120 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 2 * a00126 ^ 1 * a01181 ^ 1)
theorem ha01182 : a01182.IsHomogeneous 859 := by
  unfold a01182
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00134.pow 2)).mul (ha01120.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00126.pow 1)).mul (ha01181.pow 1)))

@[irreducible]
def a01183 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a00715 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a00451 ^ 1)
theorem ha01183 : a01183.IsHomogeneous 570 := by
  unfold a01183
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha00715.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha00451.pow 1)))

@[irreducible]
def a01184 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00136 ^ 1 * a00795 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a00450 ^ 1)
theorem ha01184 : a01184.IsHomogeneous 666 := by
  unfold a01184
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00136.pow 1)).mul (ha00795.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha00450.pow 1)))

@[irreducible]
def a01185 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00293 ^ 1 * a00447 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00135 ^ 1 * a00798 ^ 1)
theorem ha01185 : a01185.IsHomogeneous 130 := by
  unfold a01185
  exact ((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00293.pow 1)).mul (ha00447.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00135.pow 1)).mul (ha00798.pow 1)))

@[irreducible]
def a01186 : Poly := (C ((-18 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00691 ^ 1)
theorem ha01186 : a01186.IsHomogeneous 59 := by
  unfold a01186
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a01187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00125 ^ 1 * a01186 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00293 ^ 1 * a00447 ^ 1)
theorem ha01187 : a01187.IsHomogeneous 130 := by
  unfold a01187
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00125.pow 1)).mul (ha01186.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00293.pow 1)).mul (ha00447.pow 1)))

@[irreducible]
def a01188 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a01187 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01185 ^ 1)
theorem ha01188 : a01188.IsHomogeneous 130 := by
  unfold a01188
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha01187.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01185.pow 1)))

@[irreducible]
def a01189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00101 ^ 1 * a00712 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00260 ^ 1 * a00261 ^ 1)
theorem ha01189 : a01189.IsHomogeneous 127 := by
  unfold a01189
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00101.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00260.pow 1)).mul (ha00261.pow 1)))

@[irreducible]
def a01190 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a00261 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00100 ^ 1 * a00713 ^ 1)
theorem ha01190 : a01190.IsHomogeneous 127 := by
  unfold a01190
  exact ((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha00261.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00100.pow 1)).mul (ha00713.pow 1)))

@[irreducible]
def a01191 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a01190 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01189 ^ 1)
theorem ha01191 : a01191.IsHomogeneous 127 := by
  unfold a01191
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha01190.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01189.pow 1)))

@[irreducible]
def a01192 : Poly := (C ((-18 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a01191 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a01188 ^ 1)
theorem ha01192 : a01192.IsHomogeneous 134 := by
  unfold a01192
  exact (((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha01191.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha01188.pow 1)))

@[irreducible]
def a01193 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a00450 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01192 ^ 1)
theorem ha01193 : a01193.IsHomogeneous 412 := by
  unfold a01193
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha00450.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01192.pow 1)))

@[irreducible]
def a01194 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01184 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01193 ^ 1)
theorem ha01194 : a01194.IsHomogeneous 666 := by
  unfold a01194
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01184.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01193.pow 1)))

@[irreducible]
def a01195 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a00451 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a01194 ^ 1)
theorem ha01195 : a01195.IsHomogeneous 745 := by
  unfold a01195
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha00451.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha01194.pow 1)))

@[irreducible]
def a01196 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01183 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a01195 ^ 1)
theorem ha01196 : a01196.IsHomogeneous 824 := by
  unfold a01196
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01183.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha01195.pow 1)))

@[irreducible]
def a01197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a00452 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01196 ^ 1)
theorem ha01197 : a01197.IsHomogeneous 932 := by
  unfold a01197
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha00452.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01196.pow 1)))

@[irreducible]
def a01198 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a00452 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a00836 ^ 1)
theorem ha01198 : a01198.IsHomogeneous 689 := by
  unfold a01198
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha00452.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha00836.pow 1)))

@[irreducible]
def a01199 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a01197 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01198 ^ 1)
theorem ha01199 : a01199.IsHomogeneous 1022 := by
  unfold a01199
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha01197.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01198.pow 1)))

@[irreducible]
def a01200 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a00452 ^ 1)
theorem ha01200 : a01200.IsHomogeneous 908 := by
  unfold a01200
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha00452.pow 1)))

@[irreducible]
def a01201 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a00452 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a00850 ^ 1)
theorem ha01201 : a01201.IsHomogeneous 641 := by
  unfold a01201
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha00452.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha00850.pow 1)))

@[irreducible]
def a01202 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a01200 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01201 ^ 1)
theorem ha01202 : a01202.IsHomogeneous 974 := by
  unfold a01202
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha01200.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01201.pow 1)))

@[irreducible]
def a01203 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a00804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a00492 ^ 1)
theorem ha01203 : a01203.IsHomogeneous 1030 := by
  unfold a01203
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha00804.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha00492.pow 1)))

@[irreducible]
def a01204 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00305 ^ 1 * a00491 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00151 ^ 1 * a00834 ^ 1)
theorem ha01204 : a01204.IsHomogeneous 295 := by
  unfold a01204
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00305.pow 1)).mul (ha00491.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha00834.pow 1)))

@[irreducible]
def a01205 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1)
theorem ha01205 : a01205.IsHomogeneous 6 := by
  unfold a01205
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a01206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha01206 : a01206.IsHomogeneous 12 := by
  unfold a01206
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01207 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01206 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01205 ^ 1)
theorem ha01207 : a01207.IsHomogeneous 12 := by
  unfold a01207
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01206.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01205.pow 1)))

@[irreducible]
def a01208 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a00455 ^ 1)
theorem ha01208 : a01208.IsHomogeneous 126 := by
  unfold a01208
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a01209 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a00303 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00823 ^ 1)
theorem ha01209 : a01209.IsHomogeneous 126 := by
  unfold a01209
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha00303.pow 1)).mul (ha00455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00823.pow 1)))

@[irreducible]
def a01210 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a01209 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01208 ^ 1)
theorem ha01210 : a01210.IsHomogeneous 126 := by
  unfold a01210
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha01209.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01208.pow 1)))

@[irreducible]
def a01211 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00148 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00480 ^ 1)
theorem ha01211 : a01211.IsHomogeneous 169 := by
  unfold a01211
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00148.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00480.pow 1)))

@[irreducible]
def a01212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1)
theorem ha01212 : a01212.IsHomogeneous 24 := by
  unfold a01212
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)))

@[irreducible]
def a01213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00317 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 2)
theorem ha01213 : a01213.IsHomogeneous 45 := by
  unfold a01213
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 2)))

@[irreducible]
def a01214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a01213 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00129 ^ 1)
theorem ha01214 : a01214.IsHomogeneous 51 := by
  unfold a01214
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha01213.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a01215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01214 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a01212 ^ 1)
theorem ha01215 : a01215.IsHomogeneous 51 := by
  unfold a01215
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01214.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha01212.pow 1)))

@[irreducible]
def a01216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00042 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00129 ^ 1 * a00130 ^ 1)
theorem ha01216 : a01216.IsHomogeneous 36 := by
  unfold a01216
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00042.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01217 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1 * a00133 ^ 1)
theorem ha01217 : a01217.IsHomogeneous 36 := by
  unfold a01217
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a01218 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00032 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a00133 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00129 ^ 1 * a00130 ^ 1)
theorem ha01218 : a01218.IsHomogeneous 33 := by
  unfold a01218
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01216 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a01217 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a01218 ^ 1)
theorem ha01219 : a01219.IsHomogeneous 36 := by
  unfold a01219
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01216.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha01217.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha01218.pow 1)))

@[irreducible]
def a01220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 2) + (C ((21 : ℂ) / (4 : ℂ)) * a00032 ^ 1 * a00324 ^ 1)
theorem ha01220 : a01220.IsHomogeneous 12 := by
  unfold a01220
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00032.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 2) + (C ((21 : ℂ) / (2 : ℂ)) * a00649 ^ 1)
theorem ha01221 : a01221.IsHomogeneous 12 := by
  unfold a01221
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00649.pow 1)))

@[irreducible]
def a01222 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01220 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01221 ^ 1)
theorem ha01222 : a01222.IsHomogeneous 12 := by
  unfold a01222
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01220.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01221.pow 1)))

@[irreducible]
def a01223 : Poly := (C ((-1 : ℂ) / (540 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a01219 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01215 ^ 1) + (C ((1 : ℂ) / (524880 : ℂ)) * a00000 ^ 18 * a00001 ^ 6 * a00003 ^ 3 * a00004 ^ 6 * a00032 ^ 1 * a01222 ^ 1)
theorem ha01223 : a01223.IsHomogeneous 51 := by
  unfold a01223
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (540 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha01219.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01215.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (524880 : ℂ))).mul (ha00000.pow 18)).mul (ha00001.pow 6)).mul (ha00003.pow 3)).mul (ha00004.pow 6)).mul (ha00032.pow 1)).mul (ha01222.pow 1)))

@[irreducible]
def a01224 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a01223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00459 ^ 1)
theorem ha01224 : a01224.IsHomogeneous 93 := by
  unfold a01224
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01223.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00459.pow 1)))

@[irreducible]
def a01225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a00459 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00137 ^ 1 * a00829 ^ 1)
theorem ha01225 : a01225.IsHomogeneous 138 := by
  unfold a01225
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha00459.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00137.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a01226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a01224 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01225 ^ 1)
theorem ha01226 : a01226.IsHomogeneous 138 := by
  unfold a01226
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01224.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01225.pow 1)))

@[irreducible]
def a01227 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00478 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00147 ^ 1 * a00155 ^ 1)
theorem ha01227 : a01227.IsHomogeneous 127 := by
  unfold a01227
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00478.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00147.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a01228 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00782 ^ 1) + (C ((1 : ℂ) / (1080 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3)
theorem ha01228 : a01228.IsHomogeneous 15 := by
  unfold a01228
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00782.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1080 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a01229 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a01228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a00461 ^ 1)
theorem ha01229 : a01229.IsHomogeneous 111 := by
  unfold a01229
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha01228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha00461.pow 1)))

@[irreducible]
def a01230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00301 ^ 1 * a00461 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00138 ^ 1 * a00819 ^ 1)
theorem ha01230 : a01230.IsHomogeneous 120 := by
  unfold a01230
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha00461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00138.pow 1)).mul (ha00819.pow 1)))

@[irreducible]
def a01231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01229 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01230 ^ 1)
theorem ha01231 : a01231.IsHomogeneous 120 := by
  unfold a01231
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01229.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01230.pow 1)))

@[irreducible]
def a01232 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00146 ^ 1 * a00812 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a00476 ^ 1)
theorem ha01232 : a01232.IsHomogeneous 118 := by
  unfold a01232
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha00812.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha00476.pow 1)))

@[irreducible]
def a01233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00139 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00465 ^ 1)
theorem ha01233 : a01233.IsHomogeneous 78 := by
  unfold a01233
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00139.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00465.pow 1)))

@[irreducible]
def a01234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1)
theorem ha01234 : a01234.IsHomogeneous 33 := by
  unfold a01234
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a01207 ^ 1)
theorem ha01235 : a01235.IsHomogeneous 39 := by
  unfold a01235
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a01236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01234 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01235 ^ 1)
theorem ha01236 : a01236.IsHomogeneous 39 := by
  unfold a01236
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01234.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01235.pow 1)))

@[irreducible]
def a01237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00316 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha01237 : a01237.IsHomogeneous 36 := by
  unfold a01237
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a01238 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00809 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00298 ^ 1)
theorem ha01238 : a01238.IsHomogeneous 33 := by
  unfold a01238
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00298.pow 1)))

@[irreducible]
def a01239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01238 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a01237 ^ 1)
theorem ha01239 : a01239.IsHomogeneous 39 := by
  unfold a01239
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01238.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha01237.pow 1)))

@[irreducible]
def a01240 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01236 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a01239 ^ 1)
theorem ha01240 : a01240.IsHomogeneous 39 := by
  unfold a01240
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01236.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha01239.pow 1)))

@[irreducible]
def a01241 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00465 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01240 ^ 1)
theorem ha01241 : a01241.IsHomogeneous 78 := by
  unfold a01241
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00465.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01240.pow 1)))

@[irreducible]
def a01242 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a01241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01233 ^ 1)
theorem ha01242 : a01242.IsHomogeneous 78 := by
  unfold a01242
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha01241.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01233.pow 1)))

@[irreducible]
def a01243 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00042 ^ 1 * a00126 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00241 ^ 1 * a00300 ^ 1)
theorem ha01243 : a01243.IsHomogeneous 109 := by
  unfold a01243
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00691.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00241.pow 1)).mul (ha00300.pow 1)))

@[irreducible]
def a01244 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a00300 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00082 ^ 1 * a00817 ^ 1)
theorem ha01244 : a01244.IsHomogeneous 103 := by
  unfold a01244
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha00300.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00817.pow 1)))

@[irreducible]
def a01245 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a01243 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01244 ^ 1)
theorem ha01245 : a01245.IsHomogeneous 109 := by
  unfold a01245
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha01243.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01244.pow 1)))

@[irreducible]
def a01246 : Poly := (C ((-81 : ℂ) / (50 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01245 ^ 1)
theorem ha01246 : a01246.IsHomogeneous 109 := by
  unfold a01246
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-81 : ℂ) / (50 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01242.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01245.pow 1)))

@[irreducible]
def a01247 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00141 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00469 ^ 1)
theorem ha01247 : a01247.IsHomogeneous 78 := by
  unfold a01247
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00141.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00469.pow 1)))

@[irreducible]
def a01248 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01236 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a01239 ^ 1)
theorem ha01248 : a01248.IsHomogeneous 39 := by
  unfold a01248
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01236.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha01239.pow 1)))

@[irreducible]
def a01249 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00469 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01248 ^ 1)
theorem ha01249 : a01249.IsHomogeneous 78 := by
  unfold a01249
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00469.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01248.pow 1)))

@[irreducible]
def a01250 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a01249 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01247 ^ 1)
theorem ha01250 : a01250.IsHomogeneous 78 := by
  unfold a01250
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha01249.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01247.pow 1)))

@[irreducible]
def a01251 : Poly := (C ((-54 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01245 ^ 1)
theorem ha01251 : a01251.IsHomogeneous 109 := by
  unfold a01251
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-54 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01250.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01245.pow 1)))

@[irreducible]
def a01252 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a01251 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01246 ^ 1)
theorem ha01252 : a01252.IsHomogeneous 109 := by
  unfold a01252
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha01251.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01246.pow 1)))

@[irreducible]
def a01253 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01236 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a01239 ^ 1)
theorem ha01253 : a01253.IsHomogeneous 39 := by
  unfold a01253
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01236.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha01239.pow 1)))

@[irreducible]
def a01254 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00473 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01253 ^ 1)
theorem ha01254 : a01254.IsHomogeneous 78 := by
  unfold a01254
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00473.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01253.pow 1)))

@[irreducible]
def a01255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00144 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00473 ^ 1)
theorem ha01255 : a01255.IsHomogeneous 78 := by
  unfold a01255
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00144.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00473.pow 1)))

@[irreducible]
def a01256 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a01255 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01254 ^ 1)
theorem ha01256 : a01256.IsHomogeneous 78 := by
  unfold a01256
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha01255.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01254.pow 1)))

@[irreducible]
def a01257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01245 ^ 1) + (C ((27 : ℂ) / (10 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a01256 ^ 1)
theorem ha01257 : a01257.IsHomogeneous 109 := by
  unfold a01257
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01245.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (10 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha01256.pow 1)))

@[irreducible]
def a01258 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a01257 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01252 ^ 1)
theorem ha01258 : a01258.IsHomogeneous 109 := by
  unfold a01258
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha01257.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01252.pow 1)))

@[irreducible]
def a01259 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00127 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a00476 ^ 1)
theorem ha01259 : a01259.IsHomogeneous 127 := by
  unfold a01259
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00127.pow 1)).mul (ha01258.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha00476.pow 1)))

@[irreducible]
def a01260 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01259 ^ 1)
theorem ha01260 : a01260.IsHomogeneous 127 := by
  unfold a01260
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01259.pow 1)))

@[irreducible]
def a01261 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a01260 ^ 1) + (C ((6 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a01231 ^ 1)
theorem ha01261 : a01261.IsHomogeneous 133 := by
  unfold a01261
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha01260.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha01231.pow 1)))

@[irreducible]
def a01262 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00478 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01261 ^ 1)
theorem ha01262 : a01262.IsHomogeneous 133 := by
  unfold a01262
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00478.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01261.pow 1)))

@[irreducible]
def a01263 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a01262 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01227 ^ 1)
theorem ha01263 : a01263.IsHomogeneous 133 := by
  unfold a01263
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha01262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01227.pow 1)))

@[irreducible]
def a01264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a01263 ^ 1) + (C ((243 : ℂ) / (1250 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a01226 ^ 1)
theorem ha01264 : a01264.IsHomogeneous 145 := by
  unfold a01264
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha01263.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((243 : ℂ) / (1250 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01226.pow 1)))

@[irreducible]
def a01265 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00480 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01264 ^ 1)
theorem ha01265 : a01265.IsHomogeneous 175 := by
  unfold a01265
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00480.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01264.pow 1)))

@[irreducible]
def a01266 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01265 ^ 1)
theorem ha01266 : a01266.IsHomogeneous 175 := by
  unfold a01266
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01211.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01265.pow 1)))

@[irreducible]
def a01267 : Poly := (C ((-27 : ℂ) / (125 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 6 * a01210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01266 ^ 1)
theorem ha01267 : a01267.IsHomogeneous 175 := by
  unfold a01267
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (125 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 6)).mul (ha01210.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01266.pow 1)))

@[irreducible]
def a01268 : Poly := (C ((-5 : ℂ) / (54 : ℂ)) * a00100 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1)
theorem ha01268 : a01268.IsHomogeneous 42 := by
  unfold a01268
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (54 : ℂ))).mul (ha00100.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)))

@[irreducible]
def a01269 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00100 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00831 ^ 1)
theorem ha01269 : a01269.IsHomogeneous 84 := by
  unfold a01269
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00831.pow 1)))

@[irreducible]
def a01270 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00100 ^ 1 * a01268 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01269 ^ 1)
theorem ha01270 : a01270.IsHomogeneous 84 := by
  unfold a01270
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00100.pow 1)).mul (ha01268.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01269.pow 1)))

@[irreducible]
def a01271 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00487 ^ 1)
theorem ha01271 : a01271.IsHomogeneous 106 := by
  unfold a01271
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00487.pow 1)))

@[irreducible]
def a01272 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00082 ^ 1 * a00100 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00484 ^ 1)
theorem ha01272 : a01272.IsHomogeneous 127 := by
  unfold a01272
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00484.pow 1)))

@[irreducible]
def a01273 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00691 ^ 1)
theorem ha01273 : a01273.IsHomogeneous 91 := by
  unfold a01273
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha00260.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a01274 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00082 ^ 1 * a00712 ^ 1)
theorem ha01274 : a01274.IsHomogeneous 91 := by
  unfold a01274
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00260.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00082.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a01275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01273 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a01274 ^ 1)
theorem ha01275 : a01275.IsHomogeneous 91 := by
  unfold a01275
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01273.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha01274.pow 1)))

@[irreducible]
def a01276 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a00484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01275 ^ 1)
theorem ha01276 : a01276.IsHomogeneous 127 := by
  unfold a01276
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha00484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a01277 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a01276 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01272 ^ 1)
theorem ha01277 : a01277.IsHomogeneous 127 := by
  unfold a01277
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha01276.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01272.pow 1)))

@[irreducible]
def a01278 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00260 ^ 1)
theorem ha01278 : a01278.IsHomogeneous 91 := by
  unfold a01278
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a01279 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00829 ^ 1)
theorem ha01279 : a01279.IsHomogeneous 127 := by
  unfold a01279
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a01280 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a01279 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a01278 ^ 1)
theorem ha01280 : a01280.IsHomogeneous 127 := by
  unfold a01280
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha01279.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha01278.pow 1)))

@[irreducible]
def a01281 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01277 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01280 ^ 1)
theorem ha01281 : a01281.IsHomogeneous 127 := by
  unfold a01281
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01277.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01280.pow 1)))

@[irreducible]
def a01282 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00129 ^ 1 * a00487 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01281 ^ 1)
theorem ha01282 : a01282.IsHomogeneous 151 := by
  unfold a01282
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00129.pow 1)).mul (ha00487.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01281.pow 1)))

@[irreducible]
def a01283 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a01271 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01282 ^ 1)
theorem ha01283 : a01283.IsHomogeneous 151 := by
  unfold a01283
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha01271.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01282.pow 1)))

@[irreducible]
def a01284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01283 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1 * a01270 ^ 1)
theorem ha01284 : a01284.IsHomogeneous 151 := by
  unfold a01284
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01283.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha01270.pow 1)))

@[irreducible]
def a01285 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a00489 ^ 1)
theorem ha01285 : a01285.IsHomogeneous 223 := by
  unfold a01285
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01284.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha00489.pow 1)))

@[irreducible]
def a01286 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a00489 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a00836 ^ 1)
theorem ha01286 : a01286.IsHomogeneous 277 := by
  unfold a01286
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha00489.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha00836.pow 1)))

@[irreducible]
def a01287 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a01285 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01286 ^ 1)
theorem ha01287 : a01287.IsHomogeneous 277 := by
  unfold a01287
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha01285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01286.pow 1)))

@[irreducible]
def a01288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a01287 ^ 1) + (C ((25 : ℂ) / (81 : ℂ)) * a00042 ^ 2 * a00100 ^ 2 * a01267 ^ 1)
theorem ha01288 : a01288.IsHomogeneous 295 := by
  unfold a01288
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha01287.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (81 : ℂ))).mul (ha00042.pow 2)).mul (ha00100.pow 2)).mul (ha01267.pow 1)))

@[irreducible]
def a01289 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a00491 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01288 ^ 1)
theorem ha01289 : a01289.IsHomogeneous 295 := by
  unfold a01289
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha00491.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01288.pow 1)))

@[irreducible]
def a01290 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a01289 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01204 ^ 1)
theorem ha01290 : a01290.IsHomogeneous 295 := by
  unfold a01290
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha01289.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01204.pow 1)))

@[irreducible]
def a01291 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a00492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a01290 ^ 1)
theorem ha01291 : a01291.IsHomogeneous 721 := by
  unfold a01291
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha00492.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a01292 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a01203 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01291 ^ 1)
theorem ha01292 : a01292.IsHomogeneous 1054 := by
  unfold a01292
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha01203.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01291.pow 1)))

@[irreducible]
def a01293 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a00804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a00501 ^ 1)
theorem ha01293 : a01293.IsHomogeneous 970 := by
  unfold a01293
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha00804.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha00501.pow 1)))

@[irreducible]
def a01294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00153 ^ 1 * a00848 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a00500 ^ 1)
theorem ha01294 : a01294.IsHomogeneous 211 := by
  unfold a01294
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha00848.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha00500.pow 1)))

@[irreducible]
def a01295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a00494 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a00812 ^ 1)
theorem ha01295 : a01295.IsHomogeneous 57 := by
  unfold a01295
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha00494.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha00812.pow 1)))

@[irreducible]
def a01296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1 * a01207 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00455 ^ 1)
theorem ha01296 : a01296.IsHomogeneous 48 := by
  unfold a01296
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1)).mul (ha01207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a01297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00809 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00298 ^ 1 * a00455 ^ 1)
theorem ha01297 : a01297.IsHomogeneous 42 := by
  unfold a01297
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00298.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a01298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01296 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01297 ^ 1)
theorem ha01298 : a01298.IsHomogeneous 48 := by
  unfold a01298
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01296.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01297.pow 1)))

@[irreducible]
def a01299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a00494 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00127 ^ 1 * a01298 ^ 1)
theorem ha01299 : a01299.IsHomogeneous 66 := by
  unfold a01299
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha00494.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00127.pow 1)).mul (ha01298.pow 1)))

@[irreducible]
def a01300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01299 ^ 1)
theorem ha01300 : a01300.IsHomogeneous 66 := by
  unfold a01300
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01295.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01299.pow 1)))

@[irreducible]
def a01301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00461 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00126 ^ 1 * a01228 ^ 1)
theorem ha01301 : a01301.IsHomogeneous 45 := by
  unfold a01301
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00126.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a01302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00298 ^ 1 * a00461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a00841 ^ 1)
theorem ha01302 : a01302.IsHomogeneous 78 := by
  unfold a01302
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha00461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha00841.pow 1)))

@[irreducible]
def a01303 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a01301 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01302 ^ 1)
theorem ha01303 : a01303.IsHomogeneous 78 := by
  unfold a01303
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha01301.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01302.pow 1)))

@[irreducible]
def a01304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a01300 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a01303 ^ 1)
theorem ha01304 : a01304.IsHomogeneous 78 := by
  unfold a01304
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha01300.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha01303.pow 1)))

@[irreducible]
def a01305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00497 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01304 ^ 1)
theorem ha01305 : a01305.IsHomogeneous 84 := by
  unfold a01305
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00497.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01304.pow 1)))

@[irreducible]
def a01306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00152 ^ 1 * a00155 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00497 ^ 1)
theorem ha01306 : a01306.IsHomogeneous 84 := by
  unfold a01306
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00152.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00497.pow 1)))

@[irreducible]
def a01307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01306 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01305 ^ 1)
theorem ha01307 : a01307.IsHomogeneous 90 := by
  unfold a01307
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01306.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01305.pow 1)))

@[irreducible]
def a01308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a00484 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a01275 ^ 1)
theorem ha01308 : a01308.IsHomogeneous 175 := by
  unfold a01308
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha00484.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a01309 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00126 ^ 1 * a00310 ^ 1 * a00484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00850 ^ 1)
theorem ha01309 : a01309.IsHomogeneous 205 := by
  unfold a01309
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha00484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00850.pow 1)))

@[irreducible]
def a01310 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a01309 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a01308 ^ 1)
theorem ha01310 : a01310.IsHomogeneous 205 := by
  unfold a01310
  exact (((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha01309.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha01308.pow 1)))

@[irreducible]
def a01311 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a01310 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00100 ^ 3 * a01307 ^ 1)
theorem ha01311 : a01311.IsHomogeneous 211 := by
  unfold a01311
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha01310.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 3)).mul (ha01307.pow 1)))

@[irreducible]
def a01312 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a01311 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00500 ^ 1)
theorem ha01312 : a01312.IsHomogeneous 211 := by
  unfold a01312
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha01311.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00500.pow 1)))

@[irreducible]
def a01313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01294 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01312 ^ 1)
theorem ha01313 : a01313.IsHomogeneous 211 := by
  unfold a01313
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01294.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01312.pow 1)))

@[irreducible]
def a01314 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a01313 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a00501 ^ 1)
theorem ha01314 : a01314.IsHomogeneous 637 := by
  unfold a01314
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha01313.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha00501.pow 1)))

@[irreducible]
def a01315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01314 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01293 ^ 1)
theorem ha01315 : a01315.IsHomogeneous 970 := by
  unfold a01315
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01314.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01293.pow 1)))

@[irreducible]
def a01316 : Poly := (C ((-64 : ℂ) / (9 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 3 * a01315 ^ 1) + (C ((-4 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 3 * a01202 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a01199 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a01292 ^ 1)
theorem ha01316 : a01316.IsHomogeneous 1064 := by
  unfold a01316
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-64 : ℂ) / (9 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha01315.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha01202.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha01199.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha01292.pow 1)))

@[irreducible]
def a01317 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00312 ^ 1 * a00881 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00327 ^ 1 * a00853 ^ 1)
theorem ha01317 : a01317.IsHomogeneous 1131 := by
  unfold a01317
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00312.pow 1)).mul (ha00881.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00327.pow 1)).mul (ha00853.pow 1)))

@[irreducible]
def a01318 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a00804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a00836 ^ 1)
theorem ha01318 : a01318.IsHomogeneous 1011 := by
  unfold a01318
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha00804.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha00836.pow 1)))

@[irreducible]
def a01319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00295 ^ 1 * a00715 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a00802 ^ 1)
theorem ha01319 : a01319.IsHomogeneous 813 := by
  unfold a01319
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00295.pow 1)).mul (ha00715.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha00802.pow 1)))

@[irreducible]
def a01320 : Poly := (C ((-5 : ℂ) / (192 : ℂ)) * a00714 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 2)
theorem ha01320 : a01320.IsHomogeneous 170 := by
  unfold a01320
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (192 : ℂ))).mul (ha00714.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 2)))

@[irreducible]
def a01321 : Poly := (C ((-192 : ℂ) / (5 : ℂ)) * a01320 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00714 ^ 1)
theorem ha01321 : a01321.IsHomogeneous 170 := by
  unfold a01321
  exact (((isHomogeneous_C (σ := Fin 6) ((-192 : ℂ) / (5 : ℂ))).mul (ha01320.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00714.pow 1)))

@[irreducible]
def a01322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00513 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a00506 ^ 1)
theorem ha01322 : a01322.IsHomogeneous 24 := by
  unfold a01322
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00513.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01323 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6)
theorem ha01323 : a01323.IsHomogeneous 6 := by
  unfold a01323
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a01324 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01323 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha01324 : a01324.IsHomogeneous 6 := by
  unfold a01324
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01323.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a01325 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00504 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a01324 ^ 1)
theorem ha01325 : a01325.IsHomogeneous 6 := by
  unfold a01325
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)))

@[irreducible]
def a01326 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00509 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a01325 ^ 1)
theorem ha01326 : a01326.IsHomogeneous 6 := by
  unfold a01326
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00509.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha01325.pow 1)))

@[irreducible]
def a01327 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01326 ^ 1)
theorem ha01327 : a01327.IsHomogeneous 6 := by
  unfold a01327
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01326.pow 1)))

@[irreducible]
def a01328 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a01327 ^ 1)
theorem ha01328 : a01328.IsHomogeneous 24 := by
  unfold a01328
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a01329 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01322 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a01328 ^ 1)
theorem ha01329 : a01329.IsHomogeneous 24 := by
  unfold a01329
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01322.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha01328.pow 1)))

@[irreducible]
def a01330 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1)
theorem ha01330 : a01330.IsHomogeneous 6 := by
  unfold a01330
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a01331 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00511 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1)
theorem ha01331 : a01331.IsHomogeneous 12 := by
  unfold a01331
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00511.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a01332 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01331 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01330 ^ 1)
theorem ha01332 : a01332.IsHomogeneous 12 := by
  unfold a01332
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01331.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01330.pow 1)))

@[irreducible]
def a01333 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00504 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a01324 ^ 1)
theorem ha01333 : a01333.IsHomogeneous 6 := by
  unfold a01333
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha01324.pow 1)))

@[irreducible]
def a01334 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01333 ^ 1)
theorem ha01334 : a01334.IsHomogeneous 6 := by
  unfold a01334
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01333.pow 1)))

@[irreducible]
def a01335 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01334 ^ 1)
theorem ha01335 : a01335.IsHomogeneous 6 := by
  unfold a01335
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01334.pow 1)))

@[irreducible]
def a01336 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a00510 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a01335 ^ 1)
theorem ha01336 : a01336.IsHomogeneous 12 := by
  unfold a01336
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha00510.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a01337 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a00510 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01336 ^ 1)
theorem ha01337 : a01337.IsHomogeneous 12 := by
  unfold a01337
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha00510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01336.pow 1)))

@[irreducible]
def a01338 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a01337 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00511 ^ 1)
theorem ha01338 : a01338.IsHomogeneous 18 := by
  unfold a01338
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha01337.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00511.pow 1)))

@[irreducible]
def a01339 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01338 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a01331 ^ 1)
theorem ha01339 : a01339.IsHomogeneous 18 := by
  unfold a01339
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01338.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha01331.pow 1)))

@[irreducible]
def a01340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01339 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a01332 ^ 1)
theorem ha01340 : a01340.IsHomogeneous 18 := by
  unfold a01340
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01339.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha01332.pow 1)))

@[irreducible]
def a01341 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00513 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01340 ^ 1)
theorem ha01341 : a01341.IsHomogeneous 24 := by
  unfold a01341
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00513.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01340.pow 1)))

@[irreducible]
def a01342 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01322 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01341 ^ 1)
theorem ha01342 : a01342.IsHomogeneous 24 := by
  unfold a01342
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01322.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01341.pow 1)))

@[irreducible]
def a01343 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01329 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01342 ^ 1)
theorem ha01343 : a01343.IsHomogeneous 24 := by
  unfold a01343
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01329.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01342.pow 1)))

@[irreducible]
def a01344 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1)
theorem ha01344 : a01344.IsHomogeneous 18 := by
  unfold a01344
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01345 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00520 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1)
theorem ha01345 : a01345.IsHomogeneous 18 := by
  unfold a01345
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00520.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01346 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha01346 : a01346.IsHomogeneous 12 := by
  unfold a01346
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a01347 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01344 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01345 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a01346 ^ 1)
theorem ha01347 : a01347.IsHomogeneous 18 := by
  unfold a01347
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01344.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01345.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha01346.pow 1)))

@[irreducible]
def a01348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00025 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00520 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1)
theorem ha01348 : a01348.IsHomogeneous 18 := by
  unfold a01348
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00520.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01349 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a00316 ^ 1)
theorem ha01349 : a01349.IsHomogeneous 24 := by
  unfold a01349
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a01350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01349 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01344 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01348 ^ 1)
theorem ha01350 : a01350.IsHomogeneous 24 := by
  unfold a01350
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01349.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01344.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01348.pow 1)))

@[irreducible]
def a01351 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6)
theorem ha01351 : a01351.IsHomogeneous 6 := by
  unfold a01351
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a01352 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1)
theorem ha01352 : a01352.IsHomogeneous 6 := by
  unfold a01352
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)))

@[irreducible]
def a01353 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01351 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01352 ^ 1)
theorem ha01353 : a01353.IsHomogeneous 12 := by
  unfold a01353
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01351.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01352.pow 1)))

@[irreducible]
def a01354 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00316 ^ 1)
theorem ha01354 : a01354.IsHomogeneous 18 := by
  unfold a01354
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a01355 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01354 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01352 ^ 1)
theorem ha01355 : a01355.IsHomogeneous 18 := by
  unfold a01355
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01354.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01352.pow 1)))

@[irreducible]
def a01356 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01353 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01355 ^ 1)
theorem ha01356 : a01356.IsHomogeneous 18 := by
  unfold a01356
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01353.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01355.pow 1)))

@[irreducible]
def a01357 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a01356 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00520 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00520 ^ 1)
theorem ha01357 : a01357.IsHomogeneous 24 := by
  unfold a01357
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha01356.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a01358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01357 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01345 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01348 ^ 1)
theorem ha01358 : a01358.IsHomogeneous 24 := by
  unfold a01358
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01357.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01345.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01348.pow 1)))

@[irreducible]
def a01359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01350 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01358 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01347 ^ 1)
theorem ha01359 : a01359.IsHomogeneous 24 := by
  unfold a01359
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01350.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01358.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01347.pow 1)))

@[irreducible]
def a01360 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00007 ^ 2 * a01359 ^ 1) + (C ((2 : ℂ) / (135 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00005 ^ 3 * a01343 ^ 1)
theorem ha01360 : a01360.IsHomogeneous 39 := by
  unfold a01360
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00007.pow 2)).mul (ha01359.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (135 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00005.pow 3)).mul (ha01343.pow 1)))

@[irreducible]
def a01361 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00155 ^ 1 * a00528 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00161 ^ 1 * a00506 ^ 1)
theorem ha01361 : a01361.IsHomogeneous 30 := by
  unfold a01361
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00155.pow 1)).mul (ha00528.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00161.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01362 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00161 ^ 1 * a00506 ^ 1)
theorem ha01362 : a01362.IsHomogeneous 30 := by
  unfold a01362
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01363 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01361 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a01362 ^ 1)
theorem ha01363 : a01363.IsHomogeneous 30 := by
  unfold a01363
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01361.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha01362.pow 1)))

@[irreducible]
def a01364 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00130 ^ 1)
theorem ha01364 : a01364.IsHomogeneous 12 := by
  unfold a01364
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)))

@[irreducible]
def a01365 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00025 ^ 1)
theorem ha01365 : a01365.IsHomogeneous 12 := by
  unfold a01365
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)))

@[irreducible]
def a01366 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha01366 : a01366.IsHomogeneous 12 := by
  unfold a01366
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01364 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01365 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01366 ^ 1)
theorem ha01367 : a01367.IsHomogeneous 18 := by
  unfold a01367
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01364.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01365.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01366.pow 1)))

@[irreducible]
def a01368 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1)
theorem ha01368 : a01368.IsHomogeneous 18 := by
  unfold a01368
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a01369 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1)
theorem ha01369 : a01369.IsHomogeneous 12 := by
  unfold a01369
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)))

@[irreducible]
def a01370 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01368 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01364 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a01369 ^ 1)
theorem ha01370 : a01370.IsHomogeneous 18 := by
  unfold a01370
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01364.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha01369.pow 1)))

@[irreducible]
def a01371 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00864 ^ 1)
theorem ha01371 : a01371.IsHomogeneous 24 := by
  unfold a01371
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a01372 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01371 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01366 ^ 1)
theorem ha01372 : a01372.IsHomogeneous 24 := by
  unfold a01372
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01368.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01371.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01366.pow 1)))

@[irreducible]
def a01373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01367 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01370 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01372 ^ 1)
theorem ha01373 : a01373.IsHomogeneous 24 := by
  unfold a01373
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01367.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01370.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01372.pow 1)))

@[irreducible]
def a01374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00528 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a01373 ^ 1)
theorem ha01374 : a01374.IsHomogeneous 24 := by
  unfold a01374
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha01373.pow 1)))

@[irreducible]
def a01375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01374 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01361 ^ 1)
theorem ha01375 : a01375.IsHomogeneous 30 := by
  unfold a01375
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01374.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01361.pow 1)))

@[irreducible]
def a01376 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01375 ^ 1)
theorem ha01376 : a01376.IsHomogeneous 30 := by
  unfold a01376
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01363.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01375.pow 1)))

@[irreducible]
def a01377 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a00316 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00513 ^ 1)
theorem ha01377 : a01377.IsHomogeneous 18 := by
  unfold a01377
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00513.pow 1)))

@[irreducible]
def a01378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00864 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a00316 ^ 1)
theorem ha01378 : a01378.IsHomogeneous 18 := by
  unfold a01378
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a01379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01377 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a01378 ^ 1)
theorem ha01379 : a01379.IsHomogeneous 18 := by
  unfold a01379
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01377.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha01378.pow 1)))

@[irreducible]
def a01380 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00513 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a01340 ^ 1)
theorem ha01380 : a01380.IsHomogeneous 18 := by
  unfold a01380
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00513.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha01340.pow 1)))

@[irreducible]
def a01381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01377 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a01380 ^ 1)
theorem ha01381 : a01381.IsHomogeneous 18 := by
  unfold a01381
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01377.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha01380.pow 1)))

@[irreducible]
def a01382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01379 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01381 ^ 1)
theorem ha01382 : a01382.IsHomogeneous 18 := by
  unfold a01382
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01379.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01381.pow 1)))

@[irreducible]
def a01383 : Poly := (C ((-1 : ℂ) / (96 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a01376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00003 ^ 5 * a00005 ^ 2 * a00014 ^ 2 * a01382 ^ 1)
theorem ha01383 : a01383.IsHomogeneous 42 := by
  unfold a01383
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (96 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01376.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01382.pow 1)))

@[irreducible]
def a01384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00506 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1 * a00155 ^ 1)
theorem ha01384 : a01384.IsHomogeneous 24 := by
  unfold a01384
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a01385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00130 ^ 1 * a00520 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1)
theorem ha01385 : a01385.IsHomogeneous 18 := by
  unfold a01385
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00130.pow 1)).mul (ha00520.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)))

@[irreducible]
def a01386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1)
theorem ha01386 : a01386.IsHomogeneous 12 := by
  unfold a01386
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)))

@[irreducible]
def a01387 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01385 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01386 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a01384 ^ 1)
theorem ha01387 : a01387.IsHomogeneous 24 := by
  unfold a01387
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01385.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01386.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha01384.pow 1)))

@[irreducible]
def a01388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00020 ^ 1 * a00025 ^ 1 * a00506 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a00520 ^ 1)
theorem ha01388 : a01388.IsHomogeneous 24 := by
  unfold a01388
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a01389 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a00506 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a00506 ^ 1)
theorem ha01389 : a01389.IsHomogeneous 30 := by
  unfold a01389
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01327.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01390 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01388 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a01389 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a01384 ^ 1)
theorem ha01390 : a01390.IsHomogeneous 30 := by
  unfold a01390
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01388.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha01389.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha01384.pow 1)))

@[irreducible]
def a01391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a00520 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00025 ^ 1 * a01356 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00520 ^ 1)
theorem ha01391 : a01391.IsHomogeneous 24 := by
  unfold a01391
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00520.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).mul (ha01356.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a01392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01385 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01388 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a01391 ^ 1)
theorem ha01392 : a01392.IsHomogeneous 24 := by
  unfold a01392
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01385.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01388.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha01391.pow 1)))

@[irreducible]
def a01393 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01392 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01387 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01390 ^ 1)
theorem ha01393 : a01393.IsHomogeneous 30 := by
  unfold a01393
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01392.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01387.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01390.pow 1)))

@[irreducible]
def a01394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00130 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00168 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1)
theorem ha01394 : a01394.IsHomogeneous 18 := by
  unfold a01394
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)))

@[irreducible]
def a01395 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00168 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00130 ^ 1 * a00547 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00168 ^ 1)
theorem ha01395 : a01395.IsHomogeneous 24 := by
  unfold a01395
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a01396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00037 ^ 1)
theorem ha01396 : a01396.IsHomogeneous 12 := by
  unfold a01396
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00037.pow 1)))

@[irreducible]
def a01397 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01394 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a01395 ^ 1) + (C ((7 : ℂ) / (45 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01396 ^ 1)
theorem ha01397 : a01397.IsHomogeneous 24 := by
  unfold a01397
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01394.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha01395.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (45 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01396.pow 1)))

@[irreducible]
def a01398 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a00316 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a00547 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1)
theorem ha01398 : a01398.IsHomogeneous 24 := by
  unfold a01398
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a01399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00037 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a00316 ^ 1)
theorem ha01399 : a01399.IsHomogeneous 24 := by
  unfold a01399
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha00316.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a01400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01398 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a01399 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01394 ^ 1)
theorem ha01400 : a01400.IsHomogeneous 24 := by
  unfold a01400
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01398.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha01399.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01394.pow 1)))

@[irreducible]
def a01401 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00506 ^ 1)
theorem ha01401 : a01401.IsHomogeneous 12 := by
  unfold a01401
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)))

@[irreducible]
def a01402 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1)
theorem ha01402 : a01402.IsHomogeneous 6 := by
  unfold a01402
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a01403 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01402 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01401 ^ 1)
theorem ha01403 : a01403.IsHomogeneous 12 := by
  unfold a01403
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01402.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01401.pow 1)))

@[irreducible]
def a01404 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00506 ^ 1)
theorem ha01404 : a01404.IsHomogeneous 12 := by
  unfold a01404
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha01327.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)))

@[irreducible]
def a01405 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01401 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a01404 ^ 1)
theorem ha01405 : a01405.IsHomogeneous 12 := by
  unfold a01405
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01401.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha01404.pow 1)))

@[irreducible]
def a01406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01403 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01405 ^ 1)
theorem ha01406 : a01406.IsHomogeneous 12 := by
  unfold a01406
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01403.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01405.pow 1)))

@[irreducible]
def a01407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00130 ^ 1 * a00510 ^ 1)
theorem ha01407 : a01407.IsHomogeneous 12 := by
  unfold a01407
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00130.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a01408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a01335 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00510 ^ 1)
theorem ha01408 : a01408.IsHomogeneous 12 := by
  unfold a01408
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha01335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a01409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01407 ^ 1) + (C ((5 : ℂ) / (84 : ℂ)) * a01408 ^ 1)
theorem ha01409 : a01409.IsHomogeneous 12 := by
  unfold a01409
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01407.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (84 : ℂ))).mul (ha01408.pow 1)))

@[irreducible]
def a01410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00553 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01407 ^ 1)
theorem ha01410 : a01410.IsHomogeneous 12 := by
  unfold a01410
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00553.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01407.pow 1)))

@[irreducible]
def a01411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01409 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01410 ^ 1)
theorem ha01411 : a01411.IsHomogeneous 12 := by
  unfold a01411
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01409.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01410.pow 1)))

@[irreducible]
def a01412 : Poly := (C ((-28 : ℂ) / (5 : ℂ)) * a01411 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01406 ^ 1)
theorem ha01412 : a01412.IsHomogeneous 12 := by
  unfold a01412
  exact (((isHomogeneous_C (σ := Fin 6) ((-28 : ℂ) / (5 : ℂ))).mul (ha01411.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01406.pow 1)))

@[irreducible]
def a01413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00547 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a01412 ^ 1)
theorem ha01413 : a01413.IsHomogeneous 30 := by
  unfold a01413
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00547.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a01414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01398 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a01413 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01395 ^ 1)
theorem ha01414 : a01414.IsHomogeneous 30 := by
  unfold a01414
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01398.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha01413.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01395.pow 1)))

@[irreducible]
def a01415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01400 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01414 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01397 ^ 1)
theorem ha01415 : a01415.IsHomogeneous 30 := by
  unfold a01415
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01400.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01414.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01397.pow 1)))

@[irreducible]
def a01416 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01393 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a01415 ^ 1)
theorem ha01416 : a01416.IsHomogeneous 30 := by
  unfold a01416
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01393.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha01415.pow 1)))

@[irreducible]
def a01417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00133 ^ 1 * a00316 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00171 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1)
theorem ha01417 : a01417.IsHomogeneous 18 := by
  unfold a01417
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01418 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00171 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00555 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00324 ^ 1)
theorem ha01418 : a01418.IsHomogeneous 24 := by
  unfold a01418
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00171 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1)
theorem ha01419 : a01419.IsHomogeneous 18 := by
  unfold a01419
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00171.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a01420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01417 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a01418 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01419 ^ 1)
theorem ha01420 : a01420.IsHomogeneous 24 := by
  unfold a01420
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha01418.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01419.pow 1)))

@[irreducible]
def a01421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1)
theorem ha01421 : a01421.IsHomogeneous 24 := by
  unfold a01421
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a01422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00032 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a00316 ^ 1)
theorem ha01422 : a01422.IsHomogeneous 24 := by
  unfold a01422
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00032.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a01423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01421 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01417 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a01422 ^ 1)
theorem ha01423 : a01423.IsHomogeneous 24 := by
  unfold a01423
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01421.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01417.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha01422.pow 1)))

@[irreducible]
def a01424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00510 ^ 1)
theorem ha01424 : a01424.IsHomogeneous 12 := by
  unfold a01424
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)))

@[irreducible]
def a01425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1)
theorem ha01425 : a01425.IsHomogeneous 6 := by
  unfold a01425
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a01426 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01425 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01424 ^ 1)
theorem ha01426 : a01426.IsHomogeneous 12 := by
  unfold a01426
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01425.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01424.pow 1)))

@[irreducible]
def a01427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a01335 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00510 ^ 1)
theorem ha01427 : a01427.IsHomogeneous 12 := by
  unfold a01427
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha01335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)))

@[irreducible]
def a01428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01424 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a01427 ^ 1)
theorem ha01428 : a01428.IsHomogeneous 12 := by
  unfold a01428
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01424.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha01427.pow 1)))

@[irreducible]
def a01429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01428 ^ 1)
theorem ha01429 : a01429.IsHomogeneous 12 := by
  unfold a01429
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01428.pow 1)))

@[irreducible]
def a01430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00555 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00555 ^ 1)
theorem ha01430 : a01430.IsHomogeneous 24 := by
  unfold a01430
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a01431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01421 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a01430 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01418 ^ 1)
theorem ha01431 : a01431.IsHomogeneous 30 := by
  unfold a01431
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01421.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha01430.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01418.pow 1)))

@[irreducible]
def a01432 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01423 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01431 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01420 ^ 1)
theorem ha01432 : a01432.IsHomogeneous 30 := by
  unfold a01432
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01423.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01431.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01420.pow 1)))

@[irreducible]
def a01433 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a01432 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01383 ^ 1) + (C ((3 : ℂ) / (40 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a01416 ^ 1)
theorem ha01433 : a01433.IsHomogeneous 42 := by
  unfold a01433
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01432.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01383.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (40 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01416.pow 1)))

@[irreducible]
def a01434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00161 ^ 1 * a00316 ^ 1)
theorem ha01434 : a01434.IsHomogeneous 24 := by
  unfold a01434
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00528.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a01435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00864 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00161 ^ 1 * a00316 ^ 1)
theorem ha01435 : a01435.IsHomogeneous 24 := by
  unfold a01435
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00161.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a01436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01434 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a01435 ^ 1)
theorem ha01436 : a01436.IsHomogeneous 24 := by
  unfold a01436
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01434.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha01435.pow 1)))

@[irreducible]
def a01437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01373 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00528 ^ 1)
theorem ha01437 : a01437.IsHomogeneous 24 := by
  unfold a01437
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01373.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00528.pow 1)))

@[irreducible]
def a01438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01434 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a01437 ^ 1)
theorem ha01438 : a01438.IsHomogeneous 24 := by
  unfold a01438
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01434.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha01437.pow 1)))

@[irreducible]
def a01439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01436 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01438 ^ 1)
theorem ha01439 : a01439.IsHomogeneous 24 := by
  unfold a01439
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01436.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01438.pow 1)))

@[irreducible]
def a01440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00577 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a00506 ^ 1)
theorem ha01440 : a01440.IsHomogeneous 30 := by
  unfold a01440
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00577.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00040 ^ 1 * a01327 ^ 1)
theorem ha01441 : a01441.IsHomogeneous 30 := by
  unfold a01441
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a01442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01440 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a01441 ^ 1)
theorem ha01442 : a01442.IsHomogeneous 30 := by
  unfold a01442
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01440.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha01441.pow 1)))

@[irreducible]
def a01443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a00506 ^ 1)
theorem ha01443 : a01443.IsHomogeneous 18 := by
  unfold a01443
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha01444 : a01444.IsHomogeneous 12 := by
  unfold a01444
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a01445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha01445 : a01445.IsHomogeneous 12 := by
  unfold a01445
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01444 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a01445 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a01443 ^ 1)
theorem ha01446 : a01446.IsHomogeneous 18 := by
  unfold a01446
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01444.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha01445.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha01443.pow 1)))

@[irreducible]
def a01447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00506 ^ 1)
theorem ha01447 : a01447.IsHomogeneous 24 := by
  unfold a01447
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00025 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00506 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00506 ^ 1)
theorem ha01448 : a01448.IsHomogeneous 24 := by
  unfold a01448
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01449 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01443 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a01448 ^ 1) + (C ((14 : ℂ) / (5 : ℂ)) * a01447 ^ 1)
theorem ha01449 : a01449.IsHomogeneous 24 := by
  unfold a01449
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01443.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha01448.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (5 : ℂ))).mul (ha01447.pow 1)))

@[irreducible]
def a01450 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1)
theorem ha01450 : a01450.IsHomogeneous 12 := by
  unfold a01450
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a01451 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01444 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01450 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a01447 ^ 1)
theorem ha01451 : a01451.IsHomogeneous 24 := by
  unfold a01451
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01444.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01450.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha01447.pow 1)))

@[irreducible]
def a01452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01446 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01451 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a01449 ^ 1)
theorem ha01452 : a01452.IsHomogeneous 24 := by
  unfold a01452
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01446.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01451.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha01449.pow 1)))

@[irreducible]
def a01453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00176 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00032 ^ 1)
theorem ha01453 : a01453.IsHomogeneous 12 := by
  unfold a01453
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00176.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a01454 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00176 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00570 ^ 1)
theorem ha01454 : a01454.IsHomogeneous 18 := by
  unfold a01454
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00176.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00570.pow 1)))

@[irreducible]
def a01455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01453 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01454 ^ 1)
theorem ha01455 : a01455.IsHomogeneous 18 := by
  unfold a01455
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01453.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01454.pow 1)))

@[irreducible]
def a01456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a01335 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a00510 ^ 1)
theorem ha01456 : a01456.IsHomogeneous 12 := by
  unfold a01456
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha01335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a01457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00510 ^ 1) + (C ((21 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00324 ^ 1)
theorem ha01457 : a01457.IsHomogeneous 18 := by
  unfold a01457
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00510.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01458 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01456 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a01457 ^ 1)
theorem ha01458 : a01458.IsHomogeneous 18 := by
  unfold a01458
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01456.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha01457.pow 1)))

@[irreducible]
def a01459 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00156 ^ 1 * a00324 ^ 1)
theorem ha01459 : a01459.IsHomogeneous 12 := by
  unfold a01459
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00156.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01460 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01459 ^ 1) + (C ((1 : ℂ) / (42 : ℂ)) * a01457 ^ 1)
theorem ha01460 : a01460.IsHomogeneous 18 := by
  unfold a01460
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01459.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (42 : ℂ))).mul (ha01457.pow 1)))

@[irreducible]
def a01461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01458 ^ 1) + (C ((84 : ℂ) / (5 : ℂ)) * a01460 ^ 1)
theorem ha01461 : a01461.IsHomogeneous 18 := by
  unfold a01461
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01458.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((84 : ℂ) / (5 : ℂ))).mul (ha01460.pow 1)))

@[irreducible]
def a01462 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00570 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00009 ^ 1 * a01461 ^ 1)
theorem ha01462 : a01462.IsHomogeneous 24 := by
  unfold a01462
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00570.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00009.pow 1)).mul (ha01461.pow 1)))

@[irreducible]
def a01463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01454 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a01462 ^ 1)
theorem ha01463 : a01463.IsHomogeneous 24 := by
  unfold a01463
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01454.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha01462.pow 1)))

@[irreducible]
def a01464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01463 ^ 1)
theorem ha01464 : a01464.IsHomogeneous 24 := by
  unfold a01464
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01455.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01463.pow 1)))

@[irreducible]
def a01465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00510 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00025 ^ 1 * a01335 ^ 1)
theorem ha01465 : a01465.IsHomogeneous 12 := by
  unfold a01465
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00510.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00025.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a01466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00130 ^ 1 * a00510 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00574 ^ 1)
theorem ha01466 : a01466.IsHomogeneous 24 := by
  unfold a01466
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha00510.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a01467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01465 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01466 ^ 1)
theorem ha01467 : a01467.IsHomogeneous 24 := by
  unfold a01467
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01465.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01466.pow 1)))

@[irreducible]
def a01468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1)
theorem ha01468 : a01468.IsHomogeneous 6 := by
  unfold a01468
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)))

@[irreducible]
def a01469 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a01468 ^ 1)
theorem ha01469 : a01469.IsHomogeneous 6 := by
  unfold a01469
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha01468.pow 1)))

@[irreducible]
def a01470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01469 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00156 ^ 1 * a00574 ^ 1)
theorem ha01470 : a01470.IsHomogeneous 18 := by
  unfold a01470
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01469.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00156.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a01471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01470 ^ 1) + (C ((1 : ℂ) / (14 : ℂ)) * a01466 ^ 1)
theorem ha01471 : a01471.IsHomogeneous 24 := by
  unfold a01471
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01470.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (14 : ℂ))).mul (ha01466.pow 1)))

@[irreducible]
def a01472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01467 ^ 1) + (C ((14 : ℂ) / (1 : ℂ)) * a01471 ^ 1)
theorem ha01472 : a01472.IsHomogeneous 24 := by
  unfold a01472
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01467.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (1 : ℂ))).mul (ha01471.pow 1)))

@[irreducible]
def a01473 : Poly := (C ((-20 : ℂ) / (3 : ℂ)) * a01464 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01452 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a01472 ^ 1)
theorem ha01473 : a01473.IsHomogeneous 24 := by
  unfold a01473
  exact ((((isHomogeneous_C (σ := Fin 6) ((-20 : ℂ) / (3 : ℂ))).mul (ha01464.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01452.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha01472.pow 1)))

@[irreducible]
def a01474 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00577 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01473 ^ 1)
theorem ha01474 : a01474.IsHomogeneous 30 := by
  unfold a01474
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00577.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a01475 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01440 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01474 ^ 1)
theorem ha01475 : a01475.IsHomogeneous 30 := by
  unfold a01475
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01440.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01474.pow 1)))

@[irreducible]
def a01476 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01442 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01475 ^ 1)
theorem ha01476 : a01476.IsHomogeneous 30 := by
  unfold a01476
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01442.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01475.pow 1)))

@[irreducible]
def a01477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01439 ^ 1) + (C ((1 : ℂ) / (2430 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a01476 ^ 1)
theorem ha01477 : a01477.IsHomogeneous 45 := by
  unfold a01477
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01439.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2430 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01476.pow 1)))

@[irreducible]
def a01478 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00513 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00157 ^ 1 * a00317 ^ 1)
theorem ha01478 : a01478.IsHomogeneous 39 := by
  unfold a01478
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00513.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00157.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01479 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00513 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a01340 ^ 1)
theorem ha01479 : a01479.IsHomogeneous 45 := by
  unfold a01479
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00513.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha01340.pow 1)))

@[irreducible]
def a01480 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01478 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01479 ^ 1)
theorem ha01480 : a01480.IsHomogeneous 45 := by
  unfold a01480
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01478.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01479.pow 1)))

@[irreducible]
def a01481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a00317 ^ 1)
theorem ha01481 : a01481.IsHomogeneous 33 := by
  unfold a01481
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01482 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01478 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a01481 ^ 1)
theorem ha01482 : a01482.IsHomogeneous 39 := by
  unfold a01482
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01478.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha01481.pow 1)))

@[irreducible]
def a01483 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01482 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01480 ^ 1)
theorem ha01483 : a01483.IsHomogeneous 45 := by
  unfold a01483
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01482.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01480.pow 1)))

@[irreducible]
def a01484 : Poly := (C ((-5 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01439 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a01483 ^ 1)
theorem ha01484 : a01484.IsHomogeneous 51 := by
  unfold a01484
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01439.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha01483.pow 1)))

@[irreducible]
def a01485 : Poly := (C ((-5 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a01477 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01484 ^ 1)
theorem ha01485 : a01485.IsHomogeneous 51 := by
  unfold a01485
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha01477.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01484.pow 1)))

@[irreducible]
def a01486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00130 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a00168 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a00155 ^ 1)
theorem ha01486 : a01486.IsHomogeneous 24 := by
  unfold a01486
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00168.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a01487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00547 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00168 ^ 1)
theorem ha01487 : a01487.IsHomogeneous 24 := by
  unfold a01487
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a01488 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1)
theorem ha01488 : a01488.IsHomogeneous 12 := by
  unfold a01488
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)))

@[irreducible]
def a01489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01486 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a01487 ^ 1) + (C ((7 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01488 ^ 1)
theorem ha01489 : a01489.IsHomogeneous 24 := by
  unfold a01489
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01486.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha01487.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01488.pow 1)))

@[irreducible]
def a01490 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a00547 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a00168 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a00506 ^ 1)
theorem ha01490 : a01490.IsHomogeneous 30 := by
  unfold a01490
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00547.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00168.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01491 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a00506 ^ 1)
theorem ha01491 : a01491.IsHomogeneous 30 := by
  unfold a01491
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha00506.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01492 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01490 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a01491 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01486 ^ 1)
theorem ha01492 : a01492.IsHomogeneous 30 := by
  unfold a01492
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01490.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha01491.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01486.pow 1)))

@[irreducible]
def a01493 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a01412 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00547 ^ 1)
theorem ha01493 : a01493.IsHomogeneous 30 := by
  unfold a01493
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha00547.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a01494 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01490 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01493 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01487 ^ 1)
theorem ha01494 : a01494.IsHomogeneous 30 := by
  unfold a01494
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01490.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01493.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01487.pow 1)))

@[irreducible]
def a01495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01494 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01489 ^ 1)
theorem ha01495 : a01495.IsHomogeneous 30 := by
  unfold a01495
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01492.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01494.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01489.pow 1)))

@[irreducible]
def a01496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a01359 ^ 1) + (C ((1 : ℂ) / (2160 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a01495 ^ 1)
theorem ha01496 : a01496.IsHomogeneous 45 := by
  unfold a01496
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha01359.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2160 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha01495.pow 1)))

@[irreducible]
def a01497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00133 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a00155 ^ 1 * a00171 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1 * a00324 ^ 1)
theorem ha01497 : a01497.IsHomogeneous 24 := by
  unfold a01497
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00133.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00171.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00155 ^ 1 * a00171 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00555 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00324 ^ 1)
theorem ha01498 : a01498.IsHomogeneous 24 := by
  unfold a01498
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00171.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a01499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1 * a00324 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00171 ^ 1 * a00324 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1)
theorem ha01499 : a01499.IsHomogeneous 18 := by
  unfold a01499
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a01500 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01497 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01498 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a01499 ^ 1)
theorem ha01500 : a01500.IsHomogeneous 24 := by
  unfold a01500
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01497.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01498.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha01499.pow 1)))

@[irreducible]
def a01501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00155 ^ 1 * a00555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a00171 ^ 1)
theorem ha01501 : a01501.IsHomogeneous 30 := by
  unfold a01501
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha00555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a01502 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a01327 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a00506 ^ 1)
theorem ha01502 : a01502.IsHomogeneous 30 := by
  unfold a01502
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00506.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a01503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01501 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01497 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01502 ^ 1)
theorem ha01503 : a01503.IsHomogeneous 30 := by
  unfold a01503
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01501.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01497.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01502.pow 1)))

@[irreducible]
def a01504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a00555 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a01429 ^ 1)
theorem ha01504 : a01504.IsHomogeneous 24 := by
  unfold a01504
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a01505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01504 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01501 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a01498 ^ 1)
theorem ha01505 : a01505.IsHomogeneous 30 := by
  unfold a01505
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01504.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01501.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha01498.pow 1)))

@[irreducible]
def a01506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01503 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01505 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01500 ^ 1)
theorem ha01506 : a01506.IsHomogeneous 30 := by
  unfold a01506
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01503.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01505.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01500.pow 1)))

@[irreducible]
def a01507 : Poly := (C ((-1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00004 ^ 3 * a00005 ^ 1 * a01506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01485 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a01496 ^ 1)
theorem ha01507 : a01507.IsHomogeneous 51 := by
  unfold a01507
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha01506.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01485.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha01496.pow 1)))

@[irreducible]
def a01508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00577 ^ 1)
theorem ha01508 : a01508.IsHomogeneous 24 := by
  unfold a01508
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00577.pow 1)))

@[irreducible]
def a01509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00040 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a00316 ^ 1)
theorem ha01509 : a01509.IsHomogeneous 24 := by
  unfold a01509
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00040.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a01510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01508 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a01509 ^ 1)
theorem ha01510 : a01510.IsHomogeneous 24 := by
  unfold a01510
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01508.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha01509.pow 1)))

@[irreducible]
def a01511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00577 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01473 ^ 1)
theorem ha01511 : a01511.IsHomogeneous 30 := by
  unfold a01511
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00577.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a01512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01508 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a01511 ^ 1)
theorem ha01512 : a01512.IsHomogeneous 30 := by
  unfold a01512
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01508.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha01511.pow 1)))

@[irreducible]
def a01513 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01512 ^ 1)
theorem ha01513 : a01513.IsHomogeneous 30 := by
  unfold a01513
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01512.pow 1)))

@[irreducible]
def a01514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00161 ^ 1 * a00317 ^ 1)
theorem ha01514 : a01514.IsHomogeneous 45 := by
  unfold a01514
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00528.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00161.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01515 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01373 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00528 ^ 1)
theorem ha01515 : a01515.IsHomogeneous 48 := by
  unfold a01515
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01373.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00528.pow 1)))

@[irreducible]
def a01516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01514 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a01515 ^ 1)
theorem ha01516 : a01516.IsHomogeneous 51 := by
  unfold a01516
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01514.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha01515.pow 1)))

@[irreducible]
def a01517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00865 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00161 ^ 1 * a00317 ^ 1)
theorem ha01517 : a01517.IsHomogeneous 39 := by
  unfold a01517
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00161.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01518 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01514 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a01517 ^ 1)
theorem ha01518 : a01518.IsHomogeneous 45 := by
  unfold a01518
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01514.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha01517.pow 1)))

@[irreducible]
def a01519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01518 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01516 ^ 1)
theorem ha01519 : a01519.IsHomogeneous 51 := by
  unfold a01519
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01518.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01516.pow 1)))

@[irreducible]
def a01520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01519 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01513 ^ 1)
theorem ha01520 : a01520.IsHomogeneous 58 := by
  unfold a01520
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01519.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01513.pow 1)))

@[irreducible]
def a01521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01376 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a01513 ^ 1)
theorem ha01521 : a01521.IsHomogeneous 30 := by
  unfold a01521
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01376.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha01513.pow 1)))

@[irreducible]
def a01522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01520 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01521 ^ 1)
theorem ha01522 : a01522.IsHomogeneous 58 := by
  unfold a01522
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01520.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01521.pow 1)))

@[irreducible]
def a01523 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01520 ^ 1)
theorem ha01523 : a01523.IsHomogeneous 58 := by
  unfold a01523
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01520.pow 1)))

@[irreducible]
def a01524 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01522 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01523 ^ 1)
theorem ha01524 : a01524.IsHomogeneous 58 := by
  unfold a01524
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01522.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01523.pow 1)))

@[irreducible]
def a01525 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00520 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a00042 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00020 ^ 1 * a00129 ^ 1 * a00130 ^ 1)
theorem ha01525 : a01525.IsHomogeneous 42 := by
  unfold a01525
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00042.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00129 ^ 1 * a00130 ^ 1)
theorem ha01526 : a01526.IsHomogeneous 39 := by
  unfold a01526
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01527 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00042 ^ 1)
theorem ha01527 : a01527.IsHomogeneous 36 := by
  unfold a01527
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a01528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01525 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01526 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01527 ^ 1)
theorem ha01528 : a01528.IsHomogeneous 45 := by
  unfold a01528
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01525.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01526.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01527.pow 1)))

@[irreducible]
def a01529 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00025 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a00520 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00129 ^ 1 * a00130 ^ 1)
theorem ha01529 : a01529.IsHomogeneous 39 := by
  unfold a01529
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00520.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a01530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00130 ^ 1 * a00520 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a01356 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1 * a00520 ^ 1)
theorem ha01530 : a01530.IsHomogeneous 48 := by
  unfold a01530
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha01356.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a01531 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01525 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01530 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01529 ^ 1)
theorem ha01531 : a01531.IsHomogeneous 48 := by
  unfold a01531
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01525.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01530.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01529.pow 1)))

@[irreducible]
def a01532 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a00317 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a00317 ^ 1)
theorem ha01532 : a01532.IsHomogeneous 39 := by
  unfold a01532
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a01533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01526 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a01532 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01529 ^ 1)
theorem ha01533 : a01533.IsHomogeneous 45 := by
  unfold a01533
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01526.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha01532.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01529.pow 1)))

@[irreducible]
def a01534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01531 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01533 ^ 1)
theorem ha01534 : a01534.IsHomogeneous 51 := by
  unfold a01534
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01531.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01528.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01533.pow 1)))

@[irreducible]
def a01535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a01534 ^ 1) + (C ((1 : ℂ) / (432 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a01415 ^ 1)
theorem ha01535 : a01535.IsHomogeneous 58 := by
  unfold a01535
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha01534.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha01415.pow 1)))

end CycleQ2Concrete
