import Proposal.CurrentAtoms012

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a05120 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a04882 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05119 ^ 1)
theorem ha05120 : a05120.IsHomogeneous 1192 := by
  unfold a05120
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha04882.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05119.pow 1)))

@[irreducible]
def a05121 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a04884 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05120 ^ 1)
theorem ha05121 : a05121.IsHomogeneous 1525 := by
  unfold a05121
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha04884.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05120.pow 1)))

@[irreducible]
def a05122 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00804 ^ 1 * a01118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a02574 ^ 1)
theorem ha05122 : a05122.IsHomogeneous 1060 := by
  unfold a05122
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha01118.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha02574.pow 1)))

@[irreducible]
def a05123 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a01118 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a01886 ^ 1)
theorem ha05123 : a05123.IsHomogeneous 1357 := by
  unfold a05123
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha01118.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a05124 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a05123 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05122 ^ 1)
theorem ha05124 : a05124.IsHomogeneous 1393 := by
  unfold a05124
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha05123.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05122.pow 1)))

@[irreducible]
def a05125 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02572 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a01117 ^ 1)
theorem ha05125 : a05125.IsHomogeneous 301 := by
  unfold a05125
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02572.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha01117.pow 1)))

@[irreducible]
def a05126 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00404 ^ 1 * a01976 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a01117 ^ 1)
theorem ha05126 : a05126.IsHomogeneous 301 := by
  unfold a05126
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00404.pow 1)).mul (ha01976.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha01117.pow 1)))

@[irreducible]
def a05127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05125 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05126 ^ 1)
theorem ha05127 : a05127.IsHomogeneous 301 := by
  unfold a05127
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05125.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05126.pow 1)))

@[irreducible]
def a05128 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01112 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a02561 ^ 1)
theorem ha05128 : a05128.IsHomogeneous 85 := by
  unfold a05128
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01112.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha02561.pow 1)))

@[irreducible]
def a05129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00812 ^ 1 * a01107 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a02551 ^ 1)
theorem ha05129 : a05129.IsHomogeneous 70 := by
  unfold a05129
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00812.pow 1)).mul (ha01107.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha02551.pow 1)))

@[irreducible]
def a05130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a01107 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00400 ^ 1 * a01903 ^ 1)
theorem ha05130 : a05130.IsHomogeneous 64 := by
  unfold a05130
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha01107.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00400.pow 1)).mul (ha01903.pow 1)))

@[irreducible]
def a05131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05129 ^ 1)
theorem ha05131 : a05131.IsHomogeneous 70 := by
  unfold a05131
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05129.pow 1)))

@[irreducible]
def a05132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02413 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1 * a01041 ^ 1)
theorem ha05132 : a05132.IsHomogeneous 48 := by
  unfold a05132
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02413.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a05133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a04894 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a02413 ^ 1)
theorem ha05133 : a05133.IsHomogeneous 48 := by
  unfold a05133
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha04894.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a05134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05132 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a05133 ^ 1)
theorem ha05134 : a05134.IsHomogeneous 48 := by
  unfold a05134
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05132.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha05133.pow 1)))

@[irreducible]
def a05135 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00368 ^ 1 * a01896 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a01041 ^ 1)
theorem ha05135 : a05135.IsHomogeneous 39 := by
  unfold a05135
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1)).mul (ha01896.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a05136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05132 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a05135 ^ 1)
theorem ha05136 : a05136.IsHomogeneous 48 := by
  unfold a05136
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05132.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha05135.pow 1)))

@[irreducible]
def a05137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05134 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05136 ^ 1)
theorem ha05137 : a05137.IsHomogeneous 48 := by
  unfold a05137
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05134.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05136.pow 1)))

@[irreducible]
def a05138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02710 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00455 ^ 1 * a01207 ^ 1)
theorem ha05138 : a05138.IsHomogeneous 24 := by
  unfold a05138
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02710.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00455.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a05139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05138 ^ 1)
theorem ha05139 : a05139.IsHomogeneous 24 := by
  unfold a05139
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha01207.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05138.pow 1)))

@[irreducible]
def a05140 : Poly := (C ((-2 : ℂ) / (135 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a05137 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a05139 ^ 1)
theorem ha05140 : a05140.IsHomogeneous 53 := by
  unfold a05140
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (135 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha05137.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha05139.pow 1)))

@[irreducible]
def a05141 : Poly := (C ((-2 : ℂ) / (135 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a05137 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05140 ^ 1)
theorem ha05141 : a05141.IsHomogeneous 53 := by
  unfold a05141
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (135 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha05137.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05140.pow 1)))

@[irreducible]
def a05142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a05141 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00299 ^ 1 * a02551 ^ 1)
theorem ha05142 : a05142.IsHomogeneous 71 := by
  unfold a05142
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha05141.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00299.pow 1)).mul (ha02551.pow 1)))

@[irreducible]
def a05143 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05142 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a05129 ^ 1)
theorem ha05143 : a05143.IsHomogeneous 71 := by
  unfold a05143
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05142.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha05129.pow 1)))

@[irreducible]
def a05144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05143 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a05131 ^ 1)
theorem ha05144 : a05144.IsHomogeneous 71 := by
  unfold a05144
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05143.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha05131.pow 1)))

@[irreducible]
def a05145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00494 ^ 1 * a01228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a01298 ^ 1)
theorem ha05145 : a05145.IsHomogeneous 63 := by
  unfold a05145
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00494.pow 1)).mul (ha01228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha01298.pow 1)))

@[irreducible]
def a05146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00494 ^ 1 * a01228 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a02754 ^ 1)
theorem ha05146 : a05146.IsHomogeneous 57 := by
  unfold a05146
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00494.pow 1)).mul (ha01228.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha02754.pow 1)))

@[irreducible]
def a05147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05146 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05145 ^ 1)
theorem ha05147 : a05147.IsHomogeneous 63 := by
  unfold a05147
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05146.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05145.pow 1)))

@[irreducible]
def a05148 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00461 ^ 1 * a01298 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00138 ^ 1 * a02879 ^ 1)
theorem ha05148 : a05148.IsHomogeneous 69 := by
  unfold a05148
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha01298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00138.pow 1)).mul (ha02879.pow 1)))

@[irreducible]
def a05149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05145 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05148 ^ 1)
theorem ha05149 : a05149.IsHomogeneous 69 := by
  unfold a05149
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05145.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05148.pow 1)))

@[irreducible]
def a05150 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05147 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05149 ^ 1)
theorem ha05150 : a05150.IsHomogeneous 69 := by
  unfold a05150
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05149.pow 1)))

@[irreducible]
def a05151 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a05144 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a05150 ^ 1)
theorem ha05151 : a05151.IsHomogeneous 77 := by
  unfold a05151
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha05144.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha05150.pow 1)))

@[irreducible]
def a05152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00298 ^ 1 * a02441 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00841 ^ 1 * a01052 ^ 1)
theorem ha05152 : a05152.IsHomogeneous 77 := by
  unfold a05152
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha02441.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00841.pow 1)).mul (ha01052.pow 1)))

@[irreducible]
def a05153 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a02441 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00003 ^ 4 * a00126 ^ 1 * a04950 ^ 1)
theorem ha05153 : a05153.IsHomogeneous 47 := by
  unfold a05153
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha02441.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 4)).mul (ha00126.pow 1)).mul (ha04950.pow 1)))

@[irreducible]
def a05154 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a05153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05152 ^ 1)
theorem ha05154 : a05154.IsHomogeneous 77 := by
  unfold a05154
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha05153.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05152.pow 1)))

@[irreducible]
def a05155 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00841 ^ 1 * a01052 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00009 ^ 1 * a00372 ^ 1 * a01962 ^ 1)
theorem ha05155 : a05155.IsHomogeneous 77 := by
  unfold a05155
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00841.pow 1)).mul (ha01052.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha01962.pow 1)))

@[irreducible]
def a05156 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05152 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a05155 ^ 1)
theorem ha05156 : a05156.IsHomogeneous 77 := by
  unfold a05156
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05152.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha05155.pow 1)))

@[irreducible]
def a05157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05154 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05156 ^ 1)
theorem ha05157 : a05157.IsHomogeneous 77 := by
  unfold a05157
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05154.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05156.pow 1)))

@[irreducible]
def a05158 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05151 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a05157 ^ 1)
theorem ha05158 : a05158.IsHomogeneous 77 := by
  unfold a05158
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05151.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha05157.pow 1)))

@[irreducible]
def a05159 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05158 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 4 * a02561 ^ 1)
theorem ha05159 : a05159.IsHomogeneous 83 := by
  unfold a05159
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05158.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 4)).mul (ha02561.pow 1)))

@[irreducible]
def a05160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a05128 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05159 ^ 1)
theorem ha05160 : a05160.IsHomogeneous 89 := by
  unfold a05160
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha05128.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05159.pow 1)))

@[irreducible]
def a05161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00402 ^ 1 * a01841 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a01112 ^ 1)
theorem ha05161 : a05161.IsHomogeneous 91 := by
  unfold a05161
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00402.pow 1)).mul (ha01841.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01112.pow 1)))

@[irreducible]
def a05162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05161 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05128 ^ 1)
theorem ha05162 : a05162.IsHomogeneous 91 := by
  unfold a05162
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05161.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05128.pow 1)))

@[irreducible]
def a05163 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05160 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00003 ^ 4 * a05162 ^ 1)
theorem ha05163 : a05163.IsHomogeneous 95 := by
  unfold a05163
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05160.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 4)).mul (ha05162.pow 1)))

@[irreducible]
def a05164 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a01313 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a00501 ^ 1 * a01275 ^ 1)
theorem ha05164 : a05164.IsHomogeneous 296 := by
  unfold a05164
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha01313.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha00501.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a05165 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a02837 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00501 ^ 1 * a01275 ^ 1)
theorem ha05165 : a05165.IsHomogeneous 260 := by
  unfold a05165
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha02837.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00501.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a05166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05164 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a05165 ^ 1)
theorem ha05166 : a05166.IsHomogeneous 296 := by
  unfold a05166
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05164.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha05165.pow 1)))

@[irreducible]
def a05167 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02904 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00484 ^ 1 * a01313 ^ 1)
theorem ha05167 : a05167.IsHomogeneous 296 := by
  unfold a05167
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02904.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a05168 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05164 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05167 ^ 1)
theorem ha05168 : a05168.IsHomogeneous 296 := by
  unfold a05168
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05164.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05167.pow 1)))

@[irreducible]
def a05169 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05168 ^ 1)
theorem ha05169 : a05169.IsHomogeneous 296 := by
  unfold a05169
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05166.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05168.pow 1)))

@[irreducible]
def a05170 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00850 ^ 1 * a01092 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a02520 ^ 1)
theorem ha05170 : a05170.IsHomogeneous 259 := by
  unfold a05170
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00850.pow 1)).mul (ha01092.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a05171 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a05087 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a02520 ^ 1)
theorem ha05171 : a05171.IsHomogeneous 193 := by
  unfold a05171
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha05087.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a05172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05170 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a05171 ^ 1)
theorem ha05172 : a05172.IsHomogeneous 259 := by
  unfold a05172
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05170.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha05171.pow 1)))

@[irreducible]
def a05173 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a01979 ^ 1)
theorem ha05173 : a05173.IsHomogeneous 295 := by
  unfold a05173
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a05174 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a05170 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05173 ^ 1)
theorem ha05174 : a05174.IsHomogeneous 295 := by
  unfold a05174
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha05170.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05173.pow 1)))

@[irreducible]
def a05175 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a05172 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05174 ^ 1)
theorem ha05175 : a05175.IsHomogeneous 295 := by
  unfold a05175
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha05172.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05174.pow 1)))

@[irreducible]
def a05176 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a05175 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a05169 ^ 1)
theorem ha05176 : a05176.IsHomogeneous 301 := by
  unfold a05176
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha05175.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha05169.pow 1)))

@[irreducible]
def a05177 : Poly := (C ((-1 : ℂ) / (20 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00100 ^ 5 * a05163 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05176 ^ 1)
theorem ha05177 : a05177.IsHomogeneous 301 := by
  unfold a05177
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (20 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00100.pow 5)).mul (ha05163.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05176.pow 1)))

@[irreducible]
def a05178 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02572 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05177 ^ 1)
theorem ha05178 : a05178.IsHomogeneous 301 := by
  unfold a05178
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02572.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05177.pow 1)))

@[irreducible]
def a05179 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05125 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05178 ^ 1)
theorem ha05179 : a05179.IsHomogeneous 301 := by
  unfold a05179
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05125.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05178.pow 1)))

@[irreducible]
def a05180 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05127 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05179 ^ 1)
theorem ha05180 : a05180.IsHomogeneous 301 := by
  unfold a05180
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05127.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05179.pow 1)))

@[irreducible]
def a05181 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a05180 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a02574 ^ 1)
theorem ha05181 : a05181.IsHomogeneous 727 := by
  unfold a05181
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha05180.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha02574.pow 1)))

@[irreducible]
def a05182 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05181 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05122 ^ 1)
theorem ha05182 : a05182.IsHomogeneous 1060 := by
  unfold a05182
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05181.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05122.pow 1)))

@[irreducible]
def a05183 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05182 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05124 ^ 1)
theorem ha05183 : a05183.IsHomogeneous 1393 := by
  unfold a05183
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05182.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05124.pow 1)))

@[irreducible]
def a05184 : Poly := (C ((-288 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 3 * a00042 ^ 2 * a00100 ^ 1 * a04863 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a05121 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00042 ^ 1 * a04875 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 5 * a04881 ^ 1) + (C ((4 : ℂ) / (16875 : ℂ)) * a00001 ^ 10 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 4 * a00042 ^ 5 * a00100 ^ 6 * a01886 ^ 1) + (C ((64 : ℂ) / (27 : ℂ)) * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 5 * a05183 ^ 1) + (C ((128 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 3 * a00042 ^ 5 * a00100 ^ 1 * a04869 ^ 1)
theorem ha05184 : a05184.IsHomogeneous 1537 := by
  unfold a05184
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-288 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha04863.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha05121.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00042.pow 1)).mul (ha04875.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha04881.pow 1))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (16875 : ℂ))).mul (ha00001.pow 10)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 4)).mul (ha00042.pow 5)).mul (ha00100.pow 6)).mul (ha01886.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((64 : ℂ) / (27 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha05183.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((128 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 1)).mul (ha04869.pow 1)))

@[irreducible]
def a05185 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00883 ^ 1 * a01180 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00328 ^ 1 * a02655 ^ 1)
theorem ha05185 : a05185.IsHomogeneous 1282 := by
  unfold a05185
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00883.pow 1)).mul (ha01180.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00328.pow 1)).mul (ha02655.pow 1)))

@[irreducible]
def a05186 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02653 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a01179 ^ 1)
theorem ha05186 : a05186.IsHomogeneous 277 := by
  unfold a05186
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02653.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha01179.pow 1)))

@[irreducible]
def a05187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a02038 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00878 ^ 1 * a01179 ^ 1)
theorem ha05187 : a05187.IsHomogeneous 277 := by
  unfold a05187
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha02038.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00878.pow 1)).mul (ha01179.pow 1)))

@[irreducible]
def a05188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05186 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a05187 ^ 1)
theorem ha05188 : a05188.IsHomogeneous 277 := by
  unfold a05188
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05186.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha05187.pow 1)))

@[irreducible]
def a05189 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00368 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01041 ^ 1)
theorem ha05189 : a05189.IsHomogeneous 33 := by
  unfold a05189
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a05190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a02413 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01041 ^ 1)
theorem ha05190 : a05190.IsHomogeneous 42 := by
  unfold a05190
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha02413.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a05191 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00368 ^ 1) + (C ((-3 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a01041 ^ 1)
theorem ha05191 : a05191.IsHomogeneous 36 := by
  unfold a05191
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00368.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a05192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05191 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05190 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a05189 ^ 1)
theorem ha05192 : a05192.IsHomogeneous 42 := by
  unfold a05192
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05191.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05190.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha05189.pow 1)))

@[irreducible]
def a05193 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a01041 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a02413 ^ 1)
theorem ha05193 : a05193.IsHomogeneous 39 := by
  unfold a05193
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01041.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha01041.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a05194 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00368 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00368 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a01041 ^ 1)
theorem ha05194 : a05194.IsHomogeneous 33 := by
  unfold a05194
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a05195 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05189 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05194 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05193 ^ 1)
theorem ha05195 : a05195.IsHomogeneous 39 := by
  unfold a05195
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05189.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05194.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05193.pow 1)))

@[irreducible]
def a05196 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02413 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a04894 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a02413 ^ 1)
theorem ha05196 : a05196.IsHomogeneous 42 := by
  unfold a05196
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02413.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha04894.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a05197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05190 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05196 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a05193 ^ 1)
theorem ha05197 : a05197.IsHomogeneous 42 := by
  unfold a05197
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05190.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05196.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha05193.pow 1)))

@[irreducible]
def a05198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05192 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05197 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a05195 ^ 1)
theorem ha05198 : a05198.IsHomogeneous 42 := by
  unfold a05198
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05192.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05197.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha05195.pow 1)))

@[irreducible]
def a05199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00455 ^ 1)
theorem ha05199 : a05199.IsHomogeneous 12 := by
  unfold a05199
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00455.pow 1)))

@[irreducible]
def a05200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a01207 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00455 ^ 1)
theorem ha05200 : a05200.IsHomogeneous 18 := by
  unfold a05200
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00455.pow 1)))

@[irreducible]
def a05201 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00025 ^ 1)
theorem ha05201 : a05201.IsHomogeneous 12 := by
  unfold a05201
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)))

@[irreducible]
def a05202 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05200 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a05199 ^ 1)
theorem ha05202 : a05202.IsHomogeneous 18 := by
  unfold a05202
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05201.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05200.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha05199.pow 1)))

@[irreducible]
def a05203 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00455 ^ 1)
theorem ha05203 : a05203.IsHomogeneous 18 := by
  unfold a05203
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00455.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a05204 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00316 ^ 1 * a00455 ^ 1)
theorem ha05204 : a05204.IsHomogeneous 18 := by
  unfold a05204
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00316.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a05205 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05203 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a05204 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a05199 ^ 1)
theorem ha05205 : a05205.IsHomogeneous 18 := by
  unfold a05205
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05203.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha05204.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha05199.pow 1)))

@[irreducible]
def a05206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02710 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01207 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a01207 ^ 1)
theorem ha05206 : a05206.IsHomogeneous 18 := by
  unfold a05206
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02710.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a05207 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05200 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a05206 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05203 ^ 1)
theorem ha05207 : a05207.IsHomogeneous 24 := by
  unfold a05207
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05200.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha05206.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05203.pow 1)))

@[irreducible]
def a05208 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05202 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05207 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a05205 ^ 1)
theorem ha05208 : a05208.IsHomogeneous 24 := by
  unfold a05208
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05202.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05207.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha05205.pow 1)))

@[irreducible]
def a05209 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a05198 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a05208 ^ 1)
theorem ha05209 : a05209.IsHomogeneous 49 := by
  unfold a05209
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha05198.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha05208.pow 1)))

@[irreducible]
def a05210 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a05198 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05209 ^ 1)
theorem ha05210 : a05210.IsHomogeneous 49 := by
  unfold a05210
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha05198.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05209.pow 1)))

@[irreducible]
def a05211 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00506 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00298 ^ 1)
theorem ha05211 : a05211.IsHomogeneous 42 := by
  unfold a05211
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00506.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a05212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00298 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00155 ^ 1 * a00809 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a00506 ^ 1)
theorem ha05212 : a05212.IsHomogeneous 42 := by
  unfold a05212
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00298.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a05213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00126 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a00506 ^ 1)
theorem ha05213 : a05213.IsHomogeneous 42 := by
  unfold a05213
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a05214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05211 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a05213 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a05212 ^ 1)
theorem ha05214 : a05214.IsHomogeneous 42 := by
  unfold a05214
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05211.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha05213.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha05212.pow 1)))

@[irreducible]
def a05215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00298 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1)
theorem ha05215 : a05215.IsHomogeneous 36 := by
  unfold a05215
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a05216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha05216 : a05216.IsHomogeneous 36 := by
  unfold a05216
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a05217 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05215 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a05216 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a05211 ^ 1)
theorem ha05217 : a05217.IsHomogeneous 42 := by
  unfold a05217
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05215.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha05216.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha05211.pow 1)))

@[irreducible]
def a05218 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00809 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a01896 ^ 1)
theorem ha05218 : a05218.IsHomogeneous 33 := by
  unfold a05218
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1)))

@[irreducible]
def a05219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05215 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05212 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a05218 ^ 1)
theorem ha05219 : a05219.IsHomogeneous 42 := by
  unfold a05219
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05215.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05212.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha05218.pow 1)))

@[irreducible]
def a05220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05214 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a05217 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a05219 ^ 1)
theorem ha05220 : a05220.IsHomogeneous 42 := by
  unfold a05220
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05214.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha05217.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha05219.pow 1)))

@[irreducible]
def a05221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a05208 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a05220 ^ 1)
theorem ha05221 : a05221.IsHomogeneous 49 := by
  unfold a05221
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha05208.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha05220.pow 1)))

@[irreducible]
def a05222 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05209 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05221 ^ 1)
theorem ha05222 : a05222.IsHomogeneous 49 := by
  unfold a05222
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05209.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05221.pow 1)))

@[irreducible]
def a05223 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05222 ^ 1)
theorem ha05223 : a05223.IsHomogeneous 49 := by
  unfold a05223
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05210.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05222.pow 1)))

@[irreducible]
def a05224 : Poly := (C ((-4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a05198 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05210 ^ 1)
theorem ha05224 : a05224.IsHomogeneous 49 := by
  unfold a05224
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha05198.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05210.pow 1)))

@[irreducible]
def a05225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05224 ^ 1)
theorem ha05225 : a05225.IsHomogeneous 49 := by
  unfold a05225
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05223.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05224.pow 1)))

@[irreducible]
def a05226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05221 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a05220 ^ 1)
theorem ha05226 : a05226.IsHomogeneous 49 := by
  unfold a05226
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05221.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha05220.pow 1)))

@[irreducible]
def a05227 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05222 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05226 ^ 1)
theorem ha05227 : a05227.IsHomogeneous 49 := by
  unfold a05227
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05222.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05226.pow 1)))

@[irreducible]
def a05228 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05227 ^ 1)
theorem ha05228 : a05228.IsHomogeneous 49 := by
  unfold a05228
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05223.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05227.pow 1)))

@[irreducible]
def a05229 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05225 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05228 ^ 1)
theorem ha05229 : a05229.IsHomogeneous 49 := by
  unfold a05229
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05225.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05228.pow 1)))

@[irreducible]
def a05230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a03127 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03388 ^ 1)
theorem ha05230 : a05230.IsHomogeneous 50 := by
  unfold a05230
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha03127.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03388.pow 1)))

@[irreducible]
def a05231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a03127 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03376 ^ 1)
theorem ha05231 : a05231.IsHomogeneous 50 := by
  unfold a05231
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha03127.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03376.pow 1)))

@[irreducible]
def a05232 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05230 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05231 ^ 1)
theorem ha05232 : a05232.IsHomogeneous 50 := by
  unfold a05232
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05230.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05231.pow 1)))

@[irreducible]
def a05233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05231 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03376 ^ 1)
theorem ha05233 : a05233.IsHomogeneous 50 := by
  unfold a05233
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05231.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03376.pow 1)))

@[irreducible]
def a05234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05233 ^ 1)
theorem ha05234 : a05234.IsHomogeneous 50 := by
  unfold a05234
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05233.pow 1)))

@[irreducible]
def a05235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05230 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03388 ^ 1)
theorem ha05235 : a05235.IsHomogeneous 50 := by
  unfold a05235
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05230.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03388.pow 1)))

@[irreducible]
def a05236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05235 ^ 1)
theorem ha05236 : a05236.IsHomogeneous 50 := by
  unfold a05236
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05235.pow 1)))

@[irreducible]
def a05237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05234 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05236 ^ 1)
theorem ha05237 : a05237.IsHomogeneous 50 := by
  unfold a05237
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05234.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05236.pow 1)))

@[irreducible]
def a05238 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05233 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03376 ^ 1)
theorem ha05238 : a05238.IsHomogeneous 50 := by
  unfold a05238
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05233.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03376.pow 1)))

@[irreducible]
def a05239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05234 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05238 ^ 1)
theorem ha05239 : a05239.IsHomogeneous 50 := by
  unfold a05239
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05234.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05238.pow 1)))

@[irreducible]
def a05240 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05237 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05239 ^ 1)
theorem ha05240 : a05240.IsHomogeneous 50 := by
  unfold a05240
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05237.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05239.pow 1)))

@[irreducible]
def a05241 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a02970 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03451 ^ 1)
theorem ha05241 : a05241.IsHomogeneous 50 := by
  unfold a05241
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha02970.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03451.pow 1)))

@[irreducible]
def a05242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a02970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05241 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03451 ^ 1)
theorem ha05242 : a05242.IsHomogeneous 50 := by
  unfold a05242
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha02970.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05241.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03451.pow 1)))

@[irreducible]
def a05243 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05241 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03451 ^ 1)
theorem ha05243 : a05243.IsHomogeneous 50 := by
  unfold a05243
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05241.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03451.pow 1)))

@[irreducible]
def a05244 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05243 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03451 ^ 1)
theorem ha05244 : a05244.IsHomogeneous 50 := by
  unfold a05244
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05242.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05243.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03451.pow 1)))

@[irreducible]
def a05245 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a02970 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03473 ^ 1)
theorem ha05245 : a05245.IsHomogeneous 50 := by
  unfold a05245
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha02970.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03473.pow 1)))

@[irreducible]
def a05246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05245 ^ 1)
theorem ha05246 : a05246.IsHomogeneous 50 := by
  unfold a05246
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05241.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05245.pow 1)))

@[irreducible]
def a05247 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a02970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05245 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03473 ^ 1)
theorem ha05247 : a05247.IsHomogeneous 50 := by
  unfold a05247
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha02970.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05245.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03473.pow 1)))

@[irreducible]
def a05248 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05246 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05247 ^ 1)
theorem ha05248 : a05248.IsHomogeneous 50 := by
  unfold a05248
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05242.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05246.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05247.pow 1)))

@[irreducible]
def a05249 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05243 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05246 ^ 1)
theorem ha05249 : a05249.IsHomogeneous 50 := by
  unfold a05249
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05243.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05246.pow 1)))

@[irreducible]
def a05250 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05244 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05249 ^ 1)
theorem ha05250 : a05250.IsHomogeneous 50 := by
  unfold a05250
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05244.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05248.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05249.pow 1)))

@[irreducible]
def a05251 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05245 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03473 ^ 1)
theorem ha05251 : a05251.IsHomogeneous 50 := by
  unfold a05251
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05245.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03473.pow 1)))

@[irreducible]
def a05252 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05246 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05251 ^ 1)
theorem ha05252 : a05252.IsHomogeneous 50 := by
  unfold a05252
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05246.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05251.pow 1)))

@[irreducible]
def a05253 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05247 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05251 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03473 ^ 1)
theorem ha05253 : a05253.IsHomogeneous 50 := by
  unfold a05253
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05247.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05251.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03473.pow 1)))

@[irreducible]
def a05254 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05252 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05253 ^ 1)
theorem ha05254 : a05254.IsHomogeneous 50 := by
  unfold a05254
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05248.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05252.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05253.pow 1)))

@[irreducible]
def a05255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05249 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05252 ^ 1)
theorem ha05255 : a05255.IsHomogeneous 50 := by
  unfold a05255
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05249.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05252.pow 1)))

@[irreducible]
def a05256 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05250 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05254 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05255 ^ 1)
theorem ha05256 : a05256.IsHomogeneous 50 := by
  unfold a05256
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05250.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05254.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05255.pow 1)))

@[irreducible]
def a05257 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00207 ^ 1 * a00510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00129 ^ 1 * a01335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00317 ^ 1 * a00510 ^ 1)
theorem ha05257 : a05257.IsHomogeneous 39 := by
  unfold a05257
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00207.pow 1)).mul (ha00510.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00129.pow 1)).mul (ha01335.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00317.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a05258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1 * a01335 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00510 ^ 1 * a00632 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00207 ^ 1 * a00510 ^ 1)
theorem ha05258 : a05258.IsHomogeneous 42 := by
  unfold a05258
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).mul (ha01335.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00510.pow 1)).mul (ha00632.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00207.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a05259 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1 * a01335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00058 ^ 1 * a02949 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00129 ^ 1 * a01335 ^ 1)
theorem ha05259 : a05259.IsHomogeneous 42 := by
  unfold a05259
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).mul (ha01335.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00058.pow 1)).mul (ha02949.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00129.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a05260 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a05257 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a05259 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05258 ^ 1)
theorem ha05260 : a05260.IsHomogeneous 42 := by
  unfold a05260
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha05257.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha05259.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05258.pow 1)))

@[irreducible]
def a05261 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00156 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00207 ^ 1 * a00510 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00207 ^ 1 * a00317 ^ 1)
theorem ha05261 : a05261.IsHomogeneous 45 := by
  unfold a05261
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00207.pow 1)).mul (ha00510.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a05262 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00207 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00156 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00317 ^ 1 * a00510 ^ 1)
theorem ha05262 : a05262.IsHomogeneous 45 := by
  unfold a05262
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00156.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00317.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a05263 : Poly := (C ((-5 : ℂ) / (42 : ℂ)) * a05262 ^ 1) + (C ((-5 : ℂ) / (168 : ℂ)) * a00003 ^ 6 * a05257 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05261 ^ 1)
theorem ha05263 : a05263.IsHomogeneous 45 := by
  unfold a05263
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (42 : ℂ))).mul (ha05262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (168 : ℂ))).mul (ha00003.pow 6)).mul (ha05257.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05261.pow 1)))

@[irreducible]
def a05264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00156 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00510 ^ 1 * a00632 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00042 ^ 1 * a00156 ^ 1 * a01575 ^ 1)
theorem ha05264 : a05264.IsHomogeneous 45 := by
  unfold a05264
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00156.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00510.pow 1)).mul (ha00632.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00156.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a05265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05261 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05264 ^ 1) + (C ((5 : ℂ) / (126 : ℂ)) * a00003 ^ 3 * a05258 ^ 1)
theorem ha05265 : a05265.IsHomogeneous 45 := by
  unfold a05265
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05261.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05264.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (126 : ℂ))).mul (ha00003.pow 3)).mul (ha05258.pow 1)))

@[irreducible]
def a05266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05263 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05265 ^ 1) + (C ((5 : ℂ) / (126 : ℂ)) * a00003 ^ 3 * a05260 ^ 1)
theorem ha05266 : a05266.IsHomogeneous 45 := by
  unfold a05266
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05263.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05265.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (126 : ℂ))).mul (ha00003.pow 3)).mul (ha05260.pow 1)))

@[irreducible]
def a05267 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a05266 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03499 ^ 1)
theorem ha05267 : a05267.IsHomogeneous 45 := by
  unfold a05267
  exact (((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha05266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03499.pow 1)))

@[irreducible]
def a05268 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a05266 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03499 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05267 ^ 1)
theorem ha05268 : a05268.IsHomogeneous 45 := by
  unfold a05268
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha05266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03499.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05267.pow 1)))

@[irreducible]
def a05269 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05266 ^ 1) + (C ((1 : ℂ) / (11664 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03519 ^ 1)
theorem ha05269 : a05269.IsHomogeneous 45 := by
  unfold a05269
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05266.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (11664 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03519.pow 1)))

@[irreducible]
def a05270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05266 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05269 ^ 1) + (C ((1 : ℂ) / (11664 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03519 ^ 1)
theorem ha05270 : a05270.IsHomogeneous 45 := by
  unfold a05270
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05269.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (11664 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03519.pow 1)))

@[irreducible]
def a05271 : Poly := (C ((-1 : ℂ) / (1458 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03499 ^ 1)
theorem ha05271 : a05271.IsHomogeneous 45 := by
  unfold a05271
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1458 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03499.pow 1)))

@[irreducible]
def a05272 : Poly := (C ((-1 : ℂ) / (1458 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03499 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05271 ^ 1)
theorem ha05272 : a05272.IsHomogeneous 45 := by
  unfold a05272
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1458 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03499.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05271.pow 1)))

@[irreducible]
def a05273 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a05270 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05268 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05272 ^ 1)
theorem ha05273 : a05273.IsHomogeneous 45 := by
  unfold a05273
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha05270.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05268.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05272.pow 1)))

@[irreducible]
def a05274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05269 ^ 1) + (C ((1 : ℂ) / (5832 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03519 ^ 1)
theorem ha05274 : a05274.IsHomogeneous 45 := by
  unfold a05274
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05269.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5832 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03519.pow 1)))

@[irreducible]
def a05275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05270 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05274 ^ 1) + (C ((1 : ℂ) / (3888 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03519 ^ 1)
theorem ha05275 : a05275.IsHomogeneous 45 := by
  unfold a05275
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05270.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05274.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3888 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03519.pow 1)))

@[irreducible]
def a05276 : Poly := (C ((-1 : ℂ) / (729 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05271 ^ 1)
theorem ha05276 : a05276.IsHomogeneous 45 := by
  unfold a05276
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (729 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05271.pow 1)))

@[irreducible]
def a05277 : Poly := (C ((-1 : ℂ) / (486 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05272 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a05276 ^ 1)
theorem ha05277 : a05277.IsHomogeneous 45 := by
  unfold a05277
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (486 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05272.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha05276.pow 1)))

@[irreducible]
def a05278 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a05275 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05273 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05277 ^ 1)
theorem ha05278 : a05278.IsHomogeneous 45 := by
  unfold a05278
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha05275.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05273.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05277.pow 1)))

@[irreducible]
def a05279 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a05256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05240 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a05229 ^ 1) + (C ((14 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a05278 ^ 1)
theorem ha05279 : a05279.IsHomogeneous 50 := by
  unfold a05279
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha05256.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05240.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha05229.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha05278.pow 1)))

@[irreducible]
def a05280 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a02104 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00691 ^ 1 * a00931 ^ 1)
theorem ha05280 : a05280.IsHomogeneous 236 := by
  unfold a05280
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha02104.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00691.pow 1)).mul (ha00931.pow 1)))

@[irreducible]
def a05281 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00362 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00691 ^ 1 * a00931 ^ 1)
theorem ha05281 : a05281.IsHomogeneous 198 := by
  unfold a05281
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00362.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00691.pow 1)).mul (ha00931.pow 1)))

@[irreducible]
def a05282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05280 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a05281 ^ 1)
theorem ha05282 : a05282.IsHomogeneous 236 := by
  unfold a05282
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05280.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha05281.pow 1)))

@[irreducible]
def a05283 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a02104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a04232 ^ 1)
theorem ha05283 : a05283.IsHomogeneous 272 := by
  unfold a05283
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha02104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha04232.pow 1)))

@[irreducible]
def a05284 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a05280 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05283 ^ 1)
theorem ha05284 : a05284.IsHomogeneous 272 := by
  unfold a05284
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha05280.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05283.pow 1)))

@[irreducible]
def a05285 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a05282 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05284 ^ 1)
theorem ha05285 : a05285.IsHomogeneous 272 := by
  unfold a05285
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha05282.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05284.pow 1)))

@[irreducible]
def a05286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00327 ^ 1 * a00637 ^ 1)
theorem ha05286 : a05286.IsHomogeneous 192 := by
  unfold a05286
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00880.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00327.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a05287 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a00637 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a00134 ^ 1 * a01581 ^ 1)
theorem ha05287 : a05287.IsHomogeneous 154 := by
  unfold a05287
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha00637.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha01581.pow 1)))

@[irreducible]
def a05288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05286 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a05287 ^ 1)
theorem ha05288 : a05288.IsHomogeneous 192 := by
  unfold a05288
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05286.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha05287.pow 1)))

@[irreducible]
def a05289 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a00211 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a02041 ^ 1)
theorem ha05289 : a05289.IsHomogeneous 228 := by
  unfold a05289
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)).mul (ha00880.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha02041.pow 1)))

@[irreducible]
def a05290 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a05286 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05289 ^ 1)
theorem ha05290 : a05290.IsHomogeneous 228 := by
  unfold a05290
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha05286.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05289.pow 1)))

@[irreducible]
def a05291 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a05288 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05290 ^ 1)
theorem ha05291 : a05291.IsHomogeneous 228 := by
  unfold a05291
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha05288.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05290.pow 1)))

@[irreducible]
def a05292 : Poly := (C ((-432 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a05291 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a05285 ^ 1)
theorem ha05292 : a05292.IsHomogeneous 277 := by
  unfold a05292
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha05291.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha05285.pow 1)))

@[irreducible]
def a05293 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05292 ^ 1) + (C ((1 : ℂ) / (900 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 5 * a00100 ^ 5 * a05279 ^ 1)
theorem ha05293 : a05293.IsHomogeneous 277 := by
  unfold a05293
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05292.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (900 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 5)).mul (ha00100.pow 5)).mul (ha05279.pow 1)))

@[irreducible]
def a05294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02653 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a05293 ^ 1)
theorem ha05294 : a05294.IsHomogeneous 277 := by
  unfold a05294
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02653.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha05293.pow 1)))

@[irreducible]
def a05295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05186 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05294 ^ 1)
theorem ha05295 : a05295.IsHomogeneous 277 := by
  unfold a05295
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05186.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05294.pow 1)))

@[irreducible]
def a05296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05188 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05295 ^ 1)
theorem ha05296 : a05296.IsHomogeneous 277 := by
  unfold a05296
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05188.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05295.pow 1)))

@[irreducible]
def a05297 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a05296 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a02655 ^ 1)
theorem ha05297 : a05297.IsHomogeneous 835 := by
  unfold a05297
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha05296.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha02655.pow 1)))

@[irreducible]
def a05298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05185 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a05297 ^ 1)
theorem ha05298 : a05298.IsHomogeneous 1282 := by
  unfold a05298
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05185.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha05297.pow 1)))

@[irreducible]
def a05299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a02046 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00883 ^ 1 * a01180 ^ 1)
theorem ha05299 : a05299.IsHomogeneous 1699 := by
  unfold a05299
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha02046.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00883.pow 1)).mul (ha01180.pow 1)))

@[irreducible]
def a05300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05299 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a05185 ^ 1)
theorem ha05300 : a05300.IsHomogeneous 1699 := by
  unfold a05300
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05299.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha05185.pow 1)))

@[irreducible]
def a05301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05300 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a05298 ^ 1)
theorem ha05301 : a05301.IsHomogeneous 1699 := by
  unfold a05301
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05300.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha05298.pow 1)))

@[irreducible]
def a05302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 2 * a05301 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00134 ^ 4 * a05184 ^ 1)
theorem ha05302 : a05302.IsHomogeneous 1777 := by
  unfold a05302
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha05301.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00134.pow 4)).mul (ha05184.pow 1)))

@[irreducible]
def a05303 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a02109 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a04239 ^ 1)
theorem ha05303 : a05303.IsHomogeneous 2198 := by
  unfold a05303
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha02109.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha04239.pow 1)))

@[irreducible]
def a05304 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00934 ^ 1 * a02043 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00881 ^ 1 * a02109 ^ 1)
theorem ha05304 : a05304.IsHomogeneous 1841 := by
  unfold a05304
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00934.pow 1)).mul (ha02043.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00881.pow 1)).mul (ha02109.pow 1)))

@[irreducible]
def a05305 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05303 ^ 1)
theorem ha05305 : a05305.IsHomogeneous 2198 := by
  unfold a05305
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05304.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05303.pow 1)))

@[irreducible]
def a05306 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00836 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a01949 ^ 1)
theorem ha05306 : a05306.IsHomogeneous 1094 := by
  unfold a05306
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00836.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha01949.pow 1)))

@[irreducible]
def a05307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00836 ^ 1 * a01196 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a02687 ^ 1)
theorem ha05307 : a05307.IsHomogeneous 1367 := by
  unfold a05307
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00836.pow 1)).mul (ha01196.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a05308 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05307 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05306 ^ 1)
theorem ha05308 : a05308.IsHomogeneous 1427 := by
  unfold a05308
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05307.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05306.pow 1)))

@[irreducible]
def a05309 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00715 ^ 1 * a01194 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00451 ^ 1 * a01707 ^ 1)
theorem ha05309 : a05309.IsHomogeneous 915 := by
  unfold a05309
  exact (((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00715.pow 1)).mul (ha01194.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00451.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a05310 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00715 ^ 1 * a01194 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a02684 ^ 1)
theorem ha05310 : a05310.IsHomogeneous 1090 := by
  unfold a05310
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00715.pow 1)).mul (ha01194.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha02684.pow 1)))

@[irreducible]
def a05311 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a05310 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05309 ^ 1)
theorem ha05311 : a05311.IsHomogeneous 1169 := by
  unfold a05311
  exact ((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha05310.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05309.pow 1)))

@[irreducible]
def a05312 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a03569 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00451 ^ 1 * a01707 ^ 1)
theorem ha05312 : a05312.IsHomogeneous 740 := by
  unfold a05312
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha03569.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00451.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a05313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05312 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a05309 ^ 1)
theorem ha05313 : a05313.IsHomogeneous 994 := by
  unfold a05313
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05312.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha05309.pow 1)))

@[irreducible]
def a05314 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05313 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a05311 ^ 1)
theorem ha05314 : a05314.IsHomogeneous 1248 := by
  unfold a05314
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05313.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha05311.pow 1)))

@[irreducible]
def a05315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00450 ^ 1 * a01871 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00795 ^ 1 * a01192 ^ 1)
theorem ha05315 : a05315.IsHomogeneous 932 := by
  unfold a05315
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00450.pow 1)).mul (ha01871.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00795.pow 1)).mul (ha01192.pow 1)))

@[irreducible]
def a05316 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00795 ^ 1 * a01192 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a02681 ^ 1)
theorem ha05316 : a05316.IsHomogeneous 678 := by
  unfold a05316
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00795.pow 1)).mul (ha01192.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha02681.pow 1)))

@[irreducible]
def a05317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05315 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05316 ^ 1)
theorem ha05317 : a05317.IsHomogeneous 932 := by
  unfold a05317
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05315.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05316.pow 1)))

@[irreducible]
def a05318 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00136 ^ 1 * a03851 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00450 ^ 1 * a01871 ^ 1)
theorem ha05318 : a05318.IsHomogeneous 1186 := by
  unfold a05318
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00136.pow 1)).mul (ha03851.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00450.pow 1)).mul (ha01871.pow 1)))

@[irreducible]
def a05319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05318 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05315 ^ 1)
theorem ha05319 : a05319.IsHomogeneous 1186 := by
  unfold a05319
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05318.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05315.pow 1)))

@[irreducible]
def a05320 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05319 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05317 ^ 1)
theorem ha05320 : a05320.IsHomogeneous 1186 := by
  unfold a05320
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05319.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05317.pow 1)))

@[irreducible]
def a05321 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00798 ^ 1 * a01186 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00447 ^ 1 * a01877 ^ 1)
theorem ha05321 : a05321.IsHomogeneous 140 := by
  unfold a05321
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00798.pow 1)).mul (ha01186.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00447.pow 1)).mul (ha01877.pow 1)))

@[irreducible]
def a05322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00798 ^ 1 * a01186 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00293 ^ 1 * a02671 ^ 1)
theorem ha05322 : a05322.IsHomogeneous 140 := by
  unfold a05322
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00798.pow 1)).mul (ha01186.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00293.pow 1)).mul (ha02671.pow 1)))

@[irreducible]
def a05323 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05321 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05322 ^ 1)
theorem ha05323 : a05323.IsHomogeneous 140 := by
  unfold a05323
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05321.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05322.pow 1)))

@[irreducible]
def a05324 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00447 ^ 1 * a01877 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00135 ^ 1 * a03861 ^ 1)
theorem ha05324 : a05324.IsHomogeneous 134 := by
  unfold a05324
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00447.pow 1)).mul (ha01877.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00135.pow 1)).mul (ha03861.pow 1)))

@[irreducible]
def a05325 : Poly := (C ((-15 : ℂ) / (16 : ℂ)) * a05321 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05324 ^ 1)
theorem ha05325 : a05325.IsHomogeneous 140 := by
  unfold a05325
  exact (((isHomogeneous_C (σ := Fin 6) ((-15 : ℂ) / (16 : ℂ))).mul (ha05321.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05324.pow 1)))

@[irreducible]
def a05326 : Poly := (C ((-16 : ℂ) / (15 : ℂ)) * a05325 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05323 ^ 1)
theorem ha05326 : a05326.IsHomogeneous 140 := by
  unfold a05326
  exact (((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (15 : ℂ))).mul (ha05325.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05323.pow 1)))

@[irreducible]
def a05327 : Poly := (C ((-2 : ℂ) / (45 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00012 ^ 1 * a03534 ^ 1)
theorem ha05327 : a05327.IsHomogeneous 58 := by
  unfold a05327
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha03562.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00012.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a05328 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00125 ^ 1 * a05327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a02671 ^ 1)
theorem ha05328 : a05328.IsHomogeneous 134 := by
  unfold a05328
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00125.pow 1)).mul (ha05327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha02671.pow 1)))

@[irreducible]
def a05329 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a05328 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a05322 ^ 1)
theorem ha05329 : a05329.IsHomogeneous 140 := by
  unfold a05329
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha05328.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha05322.pow 1)))

@[irreducible]
def a05330 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05323 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a05329 ^ 1)
theorem ha05330 : a05330.IsHomogeneous 140 := by
  unfold a05330
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05323.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha05329.pow 1)))

@[irreducible]
def a05331 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05326 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05330 ^ 1)
theorem ha05331 : a05331.IsHomogeneous 140 := by
  unfold a05331
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05326.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05330.pow 1)))

@[irreducible]
def a05332 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a01702 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00712 ^ 1 * a00713 ^ 1)
theorem ha05332 : a05332.IsHomogeneous 136 := by
  unfold a05332
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00712.pow 1)).mul (ha00713.pow 1)))

@[irreducible]
def a05333 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00712 ^ 1 * a00713 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a01703 ^ 1)
theorem ha05333 : a05333.IsHomogeneous 137 := by
  unfold a05333
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00712.pow 1)).mul (ha00713.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha01703.pow 1)))

@[irreducible]
def a05334 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05332 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a05333 ^ 1)
theorem ha05334 : a05334.IsHomogeneous 137 := by
  unfold a05334
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05332.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha05333.pow 1)))

@[irreducible]
def a05335 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a01702 ^ 1) + (C ((1 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00101 ^ 1 * a03562 ^ 1)
theorem ha05335 : a05335.IsHomogeneous 136 := by
  unfold a05335
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a05336 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05332 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05335 ^ 1)
theorem ha05336 : a05336.IsHomogeneous 136 := by
  unfold a05336
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05332.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05335.pow 1)))

@[irreducible]
def a05337 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a05336 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05334 ^ 1)
theorem ha05337 : a05337.IsHomogeneous 137 := by
  unfold a05337
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha05336.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05334.pow 1)))

@[irreducible]
def a05338 : Poly := (C ((-9 : ℂ) / (2 : ℂ)) * a00260 ^ 1 * a01703 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a03563 ^ 1)
theorem ha05338 : a05338.IsHomogeneous 131 := by
  unfold a05338
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (2 : ℂ))).mul (ha00260.pow 1)).mul (ha01703.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03563.pow 1)))

@[irreducible]
def a05339 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a05338 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05333 ^ 1)
theorem ha05339 : a05339.IsHomogeneous 137 := by
  unfold a05339
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha05338.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05333.pow 1)))

@[irreducible]
def a05340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05334 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a05339 ^ 1)
theorem ha05340 : a05340.IsHomogeneous 137 := by
  unfold a05340
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05334.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha05339.pow 1)))

@[irreducible]
def a05341 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05337 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a05340 ^ 1)
theorem ha05341 : a05341.IsHomogeneous 137 := by
  unfold a05341
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05337.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05340.pow 1)))

@[irreducible]
def a05342 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a05331 ^ 1) + (C ((24 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a05341 ^ 1)
theorem ha05342 : a05342.IsHomogeneous 144 := by
  unfold a05342
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha05331.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha05341.pow 1)))

@[irreducible]
def a05343 : Poly := (C ((-5 : ℂ) / (48 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05342 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a02681 ^ 1)
theorem ha05343 : a05343.IsHomogeneous 423 := by
  unfold a05343
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (48 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05342.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha02681.pow 1)))

@[irreducible]
def a05344 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05316 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05343 ^ 1)
theorem ha05344 : a05344.IsHomogeneous 678 := by
  unfold a05344
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05316.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05343.pow 1)))

@[irreducible]
def a05345 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05317 ^ 1) + (C ((5 : ℂ) / (108 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05344 ^ 1)
theorem ha05345 : a05345.IsHomogeneous 932 := by
  unfold a05345
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05317.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (108 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05344.pow 1)))

@[irreducible]
def a05346 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a05320 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05345 ^ 1)
theorem ha05346 : a05346.IsHomogeneous 1186 := by
  unfold a05346
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha05320.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05345.pow 1)))

@[irreducible]
def a05347 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a02684 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a05346 ^ 1)
theorem ha05347 : a05347.IsHomogeneous 1265 := by
  unfold a05347
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha02684.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha05346.pow 1)))

@[irreducible]
def a05348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05310 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a05347 ^ 1)
theorem ha05348 : a05348.IsHomogeneous 1344 := by
  unfold a05348
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05310.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha05347.pow 1)))

@[irreducible]
def a05349 : Poly := (C ((-96 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a05348 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05311 ^ 1)
theorem ha05349 : a05349.IsHomogeneous 1423 := by
  unfold a05349
  exact ((((isHomogeneous_C (σ := Fin 6) ((-96 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha05348.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05311.pow 1)))

@[irreducible]
def a05350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05314 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a05349 ^ 1)
theorem ha05350 : a05350.IsHomogeneous 1502 := by
  unfold a05350
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05314.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha05349.pow 1)))

@[irreducible]
def a05351 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a02687 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a05350 ^ 1)
theorem ha05351 : a05351.IsHomogeneous 1610 := by
  unfold a05351
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha02687.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha05350.pow 1)))

@[irreducible]
def a05352 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05307 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a05351 ^ 1)
theorem ha05352 : a05352.IsHomogeneous 1700 := by
  unfold a05352
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05307.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha05351.pow 1)))

@[irreducible]
def a05353 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05352 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05308 ^ 1)
theorem ha05353 : a05353.IsHomogeneous 1760 := by
  unfold a05353
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05352.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05308.pow 1)))

@[irreducible]
def a05354 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a01949 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a03978 ^ 1)
theorem ha05354 : a05354.IsHomogeneous 821 := by
  unfold a05354
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha01949.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha03978.pow 1)))

@[irreducible]
def a05355 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05306 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05354 ^ 1)
theorem ha05355 : a05355.IsHomogeneous 1154 := by
  unfold a05355
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05306.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05354.pow 1)))

@[irreducible]
def a05356 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05308 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05355 ^ 1)
theorem ha05356 : a05356.IsHomogeneous 1487 := by
  unfold a05356
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05308.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05355.pow 1)))

@[irreducible]
def a05357 : Poly := (C ((-8 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05353 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05356 ^ 1)
theorem ha05357 : a05357.IsHomogeneous 1820 := by
  unfold a05357
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05353.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05356.pow 1)))

@[irreducible]
def a05358 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a01979 ^ 1)
theorem ha05358 : a05358.IsHomogeneous 1022 := by
  unfold a05358
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a05359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00850 ^ 1 * a01196 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a02687 ^ 1)
theorem ha05359 : a05359.IsHomogeneous 1319 := by
  unfold a05359
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00850.pow 1)).mul (ha01196.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a05360 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a05359 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05358 ^ 1)
theorem ha05360 : a05360.IsHomogeneous 1355 := by
  unfold a05360
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha05359.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05358.pow 1)))

@[irreducible]
def a05361 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a05350 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a02687 ^ 1)
theorem ha05361 : a05361.IsHomogeneous 1586 := by
  unfold a05361
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha05350.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha02687.pow 1)))

@[irreducible]
def a05362 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05359 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a05361 ^ 1)
theorem ha05362 : a05362.IsHomogeneous 1652 := by
  unfold a05362
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05359.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha05361.pow 1)))

@[irreducible]
def a05363 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a05362 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05360 ^ 1)
theorem ha05363 : a05363.IsHomogeneous 1688 := by
  unfold a05363
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha05362.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05360.pow 1)))

@[irreducible]
def a05364 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a01979 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a04032 ^ 1)
theorem ha05364 : a05364.IsHomogeneous 725 := by
  unfold a05364
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha01979.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha04032.pow 1)))

@[irreducible]
def a05365 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a05358 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05364 ^ 1)
theorem ha05365 : a05365.IsHomogeneous 1058 := by
  unfold a05365
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha05358.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05364.pow 1)))

@[irreducible]
def a05366 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a05360 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05365 ^ 1)
theorem ha05366 : a05366.IsHomogeneous 1391 := by
  unfold a05366
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha05360.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05365.pow 1)))

@[irreducible]
def a05367 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a05363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05366 ^ 1)
theorem ha05367 : a05367.IsHomogeneous 1724 := by
  unfold a05367
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha05363.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05366.pow 1)))

@[irreducible]
def a05368 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a01290 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00492 ^ 1 * a01886 ^ 1)
theorem ha05368 : a05368.IsHomogeneous 1435 := by
  unfold a05368
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha01290.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00492.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a05369 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a02860 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00804 ^ 1 * a01290 ^ 1)
theorem ha05369 : a05369.IsHomogeneous 1162 := by
  unfold a05369
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha02860.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a05370 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05369 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05368 ^ 1)
theorem ha05370 : a05370.IsHomogeneous 1495 := by
  unfold a05370
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05369.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05368.pow 1)))

@[irreducible]
def a05371 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00492 ^ 1 * a01886 ^ 1)
theorem ha05371 : a05371.IsHomogeneous 1708 := by
  unfold a05371
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00492.pow 1)).mul (ha01886.pow 1)))

@[irreducible]
def a05372 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05368 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05371 ^ 1)
theorem ha05372 : a05372.IsHomogeneous 1768 := by
  unfold a05372
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05371.pow 1)))

@[irreducible]
def a05373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a05370 ^ 1) + (C ((32 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a05372 ^ 1)
theorem ha05373 : a05373.IsHomogeneous 1828 := by
  unfold a05373
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha05370.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha05372.pow 1)))

@[irreducible]
def a05374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00491 ^ 1 * a01946 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00834 ^ 1 * a01288 ^ 1)
theorem ha05374 : a05374.IsHomogeneous 427 := by
  unfold a05374
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00491.pow 1)).mul (ha01946.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00834.pow 1)).mul (ha01288.pow 1)))

@[irreducible]
def a05375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a02857 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00834 ^ 1 * a01288 ^ 1)
theorem ha05375 : a05375.IsHomogeneous 427 := by
  unfold a05375
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha02857.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00834.pow 1)).mul (ha01288.pow 1)))

end CycleQ2Concrete
