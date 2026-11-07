import Proposal.CurrentAtoms003

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a02048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00455 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00042 ^ 1)
theorem ha02048 : a02048.IsHomogeneous 36 := by
  unfold a02048
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00455.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a02049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1)
theorem ha02049 : a02049.IsHomogeneous 33 := by
  unfold a02049
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a02050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00455 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00455 ^ 1)
theorem ha02050 : a02050.IsHomogeneous 42 := by
  unfold a02050
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00455.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a02051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02050 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02049 ^ 1)
theorem ha02051 : a02051.IsHomogeneous 42 := by
  unfold a02051
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02048.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02050.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02049.pow 1)))

@[irreducible]
def a02052 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00126 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha02052 : a02052.IsHomogeneous 36 := by
  unfold a02052
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a02053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00316 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha02053 : a02053.IsHomogeneous 36 := by
  unfold a02053
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00316.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a02054 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00298 ^ 1)
theorem ha02054 : a02054.IsHomogeneous 36 := by
  unfold a02054
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00298.pow 1)))

@[irreducible]
def a02055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02052 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a02053 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a02054 ^ 1)
theorem ha02055 : a02055.IsHomogeneous 42 := by
  unfold a02055
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02052.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha02053.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha02054.pow 1)))

@[irreducible]
def a02056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02051 ^ 1) + (C ((8 : ℂ) / (27 : ℂ)) * a02055 ^ 1)
theorem ha02056 : a02056.IsHomogeneous 42 := by
  unfold a02056
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (27 : ℂ))).mul (ha02055.pow 1)))

@[irreducible]
def a02057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02056 ^ 1)
theorem ha02057 : a02057.IsHomogeneous 42 := by
  unfold a02057
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02056.pow 1)))

@[irreducible]
def a02058 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02057 ^ 1)
theorem ha02058 : a02058.IsHomogeneous 42 := by
  unfold a02058
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02057.pow 1)))

@[irreducible]
def a02059 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02055 ^ 1) + (C ((27 : ℂ) / (8 : ℂ)) * a02056 ^ 1)
theorem ha02059 : a02059.IsHomogeneous 42 := by
  unfold a02059
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02055.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (8 : ℂ))).mul (ha02056.pow 1)))

@[irreducible]
def a02060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02057 ^ 1) + (C ((8 : ℂ) / (27 : ℂ)) * a02059 ^ 1)
theorem ha02060 : a02060.IsHomogeneous 42 := by
  unfold a02060
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02057.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (27 : ℂ))).mul (ha02059.pow 1)))

@[irreducible]
def a02061 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02058 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02060 ^ 1)
theorem ha02061 : a02061.IsHomogeneous 42 := by
  unfold a02061
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02058.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02060.pow 1)))

@[irreducible]
def a02062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02051 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02058 ^ 1)
theorem ha02062 : a02062.IsHomogeneous 42 := by
  unfold a02062
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02058.pow 1)))

@[irreducible]
def a02063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02061 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02062 ^ 1)
theorem ha02063 : a02063.IsHomogeneous 42 := by
  unfold a02063
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02061.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02062.pow 1)))

@[irreducible]
def a02064 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02055 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02059 ^ 1)
theorem ha02064 : a02064.IsHomogeneous 42 := by
  unfold a02064
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02055.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02059.pow 1)))

@[irreducible]
def a02065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02060 ^ 1) + (C ((8 : ℂ) / (27 : ℂ)) * a02064 ^ 1)
theorem ha02065 : a02065.IsHomogeneous 42 := by
  unfold a02065
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02060.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (27 : ℂ))).mul (ha02064.pow 1)))

@[irreducible]
def a02066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02061 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02065 ^ 1)
theorem ha02066 : a02066.IsHomogeneous 42 := by
  unfold a02066
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02061.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02065.pow 1)))

@[irreducible]
def a02067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02063 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02066 ^ 1)
theorem ha02067 : a02067.IsHomogeneous 42 := by
  unfold a02067
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02063.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02066.pow 1)))

@[irreducible]
def a02068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01518 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a01681 ^ 1)
theorem ha02068 : a02068.IsHomogeneous 51 := by
  unfold a02068
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01518.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha01681.pow 1)))

@[irreducible]
def a02069 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02068 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a01681 ^ 1)
theorem ha02069 : a02069.IsHomogeneous 51 := by
  unfold a02069
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02068.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha01681.pow 1)))

@[irreducible]
def a02070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01518 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02068 ^ 1)
theorem ha02070 : a02070.IsHomogeneous 51 := by
  unfold a02070
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01518.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02068.pow 1)))

@[irreducible]
def a02071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02069 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02070 ^ 1)
theorem ha02071 : a02071.IsHomogeneous 51 := by
  unfold a02071
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02069.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02070.pow 1)))

@[irreducible]
def a02072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01518 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02070 ^ 1)
theorem ha02072 : a02072.IsHomogeneous 51 := by
  unfold a02072
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01518.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02070.pow 1)))

@[irreducible]
def a02073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02072 ^ 1)
theorem ha02073 : a02073.IsHomogeneous 51 := by
  unfold a02073
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02072.pow 1)))

@[irreducible]
def a02074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02069 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a01681 ^ 1)
theorem ha02074 : a02074.IsHomogeneous 51 := by
  unfold a02074
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02069.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha01681.pow 1)))

@[irreducible]
def a02075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02074 ^ 1)
theorem ha02075 : a02075.IsHomogeneous 51 := by
  unfold a02075
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02074.pow 1)))

@[irreducible]
def a02076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02075 ^ 1)
theorem ha02076 : a02076.IsHomogeneous 51 := by
  unfold a02076
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02075.pow 1)))

@[irreducible]
def a02077 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01518 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02072 ^ 1)
theorem ha02077 : a02077.IsHomogeneous 51 := by
  unfold a02077
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01518.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02072.pow 1)))

@[irreducible]
def a02078 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02077 ^ 1)
theorem ha02078 : a02078.IsHomogeneous 51 := by
  unfold a02078
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02077.pow 1)))

@[irreducible]
def a02079 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02076 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02078 ^ 1)
theorem ha02079 : a02079.IsHomogeneous 51 := by
  unfold a02079
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02076.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02078.pow 1)))

@[irreducible]
def a02080 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01540 ^ 1)
theorem ha02080 : a02080.IsHomogeneous 45 := by
  unfold a02080
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01540.pow 1)))

@[irreducible]
def a02081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02080 ^ 1)
theorem ha02081 : a02081.IsHomogeneous 45 := by
  unfold a02081
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02080.pow 1)))

@[irreducible]
def a02082 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02080 ^ 1)
theorem ha02082 : a02082.IsHomogeneous 45 := by
  unfold a02082
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01540.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02080.pow 1)))

@[irreducible]
def a02083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01528 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02081 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02082 ^ 1)
theorem ha02083 : a02083.IsHomogeneous 45 := by
  unfold a02083
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02081.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02082.pow 1)))

@[irreducible]
def a02084 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02081 ^ 1)
theorem ha02084 : a02084.IsHomogeneous 45 := by
  unfold a02084
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02081.pow 1)))

@[irreducible]
def a02085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01528 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a02084 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a02083 ^ 1)
theorem ha02085 : a02085.IsHomogeneous 45 := by
  unfold a02085
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha02084.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha02083.pow 1)))

@[irreducible]
def a02086 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02080 ^ 1)
theorem ha02086 : a02086.IsHomogeneous 45 := by
  unfold a02086
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02080.pow 1)))

@[irreducible]
def a02087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02081 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02086 ^ 1)
theorem ha02087 : a02087.IsHomogeneous 45 := by
  unfold a02087
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02081.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02086.pow 1)))

@[irreducible]
def a02088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01540 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02082 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02086 ^ 1)
theorem ha02088 : a02088.IsHomogeneous 45 := by
  unfold a02088
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02082.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02086.pow 1)))

@[irreducible]
def a02089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02083 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02088 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02087 ^ 1)
theorem ha02089 : a02089.IsHomogeneous 45 := by
  unfold a02089
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02083.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02088.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02087.pow 1)))

@[irreducible]
def a02090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02084 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02087 ^ 1)
theorem ha02090 : a02090.IsHomogeneous 45 := by
  unfold a02090
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02084.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02087.pow 1)))

@[irreducible]
def a02091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02085 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a02090 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a02089 ^ 1)
theorem ha02091 : a02091.IsHomogeneous 45 := by
  unfold a02091
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02085.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha02090.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha02089.pow 1)))

@[irreducible]
def a02092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02086 ^ 1)
theorem ha02092 : a02092.IsHomogeneous 45 := by
  unfold a02092
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02086.pow 1)))

@[irreducible]
def a02093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02087 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02092 ^ 1)
theorem ha02093 : a02093.IsHomogeneous 45 := by
  unfold a02093
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02087.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02092.pow 1)))

@[irreducible]
def a02094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01540 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a02092 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a02088 ^ 1)
theorem ha02094 : a02094.IsHomogeneous 45 := by
  unfold a02094
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha02092.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha02088.pow 1)))

@[irreducible]
def a02095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02089 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02093 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a02094 ^ 1)
theorem ha02095 : a02095.IsHomogeneous 45 := by
  unfold a02095
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02089.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02093.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha02094.pow 1)))

@[irreducible]
def a02096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02090 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02093 ^ 1)
theorem ha02096 : a02096.IsHomogeneous 45 := by
  unfold a02096
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02090.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02093.pow 1)))

@[irreducible]
def a02097 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02091 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a02096 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a02095 ^ 1)
theorem ha02097 : a02097.IsHomogeneous 45 := by
  unfold a02097
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02091.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha02096.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha02095.pow 1)))

@[irreducible]
def a02098 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a02079 ^ 1) + (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02067 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02097 ^ 1) + (C ((14 : ℂ) / (243 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a01565 ^ 1)
theorem ha02098 : a02098.IsHomogeneous 51 := by
  unfold a02098
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha02079.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02067.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02097.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (243 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha01565.pow 1)))

@[irreducible]
def a02099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00327 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00134 ^ 1 * a00691 ^ 1)
theorem ha02099 : a02099.IsHomogeneous 151 := by
  unfold a02099
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00327.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a02100 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a00327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00880 ^ 1)
theorem ha02100 : a02100.IsHomogeneous 187 := by
  unfold a02100
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha00327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00880.pow 1)))

@[irreducible]
def a02101 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a02099 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02100 ^ 1)
theorem ha02101 : a02101.IsHomogeneous 187 := by
  unfold a02101
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha02099.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02100.pow 1)))

@[irreducible]
def a02102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02101 ^ 1) + (C ((1 : ℂ) / (120 : ℂ)) * a00001 ^ 5 * a00003 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 3 * a02098 ^ 1)
theorem ha02102 : a02102.IsHomogeneous 187 := by
  unfold a02102
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02101.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (120 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 3)).mul (ha02098.pow 1)))

@[irreducible]
def a02103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00930 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a02102 ^ 1)
theorem ha02103 : a02103.IsHomogeneous 187 := by
  unfold a02103
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00930.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha02102.pow 1)))

@[irreducible]
def a02104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02047 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02103 ^ 1)
theorem ha02104 : a02104.IsHomogeneous 187 := by
  unfold a02104
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02047.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02103.pow 1)))

@[irreducible]
def a02105 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a02104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a00931 ^ 1)
theorem ha02105 : a02105.IsHomogeneous 745 := by
  unfold a02105
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha02104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha00931.pow 1)))

@[irreducible]
def a02106 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a00883 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00328 ^ 1 * a00931 ^ 1)
theorem ha02106 : a02106.IsHomogeneous 1192 := by
  unfold a02106
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha00883.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00328.pow 1)).mul (ha00931.pow 1)))

@[irreducible]
def a02107 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02106 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a02105 ^ 1)
theorem ha02107 : a02107.IsHomogeneous 1192 := by
  unfold a02107
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02106.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha02105.pow 1)))

@[irreducible]
def a02108 : Poly := (C ((-9 : ℂ) / (50 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a02046 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a02107 ^ 1)
theorem ha02108 : a02108.IsHomogeneous 1609 := by
  unfold a02108
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (50 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha02046.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha02107.pow 1)))

@[irreducible]
def a02109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a02108 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 4 * a01316 ^ 1)
theorem ha02109 : a02109.IsHomogeneous 1637 := by
  unfold a02109
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha02108.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 4)).mul (ha01316.pow 1)))

@[irreducible]
def a02110 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a00934 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02109 ^ 1)
theorem ha02110 : a02110.IsHomogeneous 1637 := by
  unfold a02110
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha00934.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02109.pow 1)))

@[irreducible]
def a02111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a00934 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00364 ^ 1 * a00881 ^ 1)
theorem ha02111 : a02111.IsHomogeneous 1280 := by
  unfold a02111
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha00934.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00364.pow 1)).mul (ha00881.pow 1)))

@[irreducible]
def a02112 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02111 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02110 ^ 1)
theorem ha02112 : a02112.IsHomogeneous 1637 := by
  unfold a02112
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02111.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02110.pow 1)))

@[irreducible]
def a02113 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00364 ^ 1 * a00931 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a00935 ^ 1)
theorem ha02113 : a02113.IsHomogeneous 1281 := by
  unfold a02113
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00364.pow 1)).mul (ha00931.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha00935.pow 1)))

@[irreducible]
def a02114 : Poly := (C ((-27 : ℂ) / (250 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a02112 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a02113 ^ 1)
theorem ha02114 : a02114.IsHomogeneous 1698 := by
  unfold a02114
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (250 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha02112.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha02113.pow 1)))

@[irreducible]
def a02115 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a02114 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a01182 ^ 1)
theorem ha02115 : a02115.IsHomogeneous 1705 := by
  unfold a02115
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha02114.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha01182.pow 1)))

@[irreducible]
def a02116 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02115 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a00937 ^ 1)
theorem ha02116 : a02116.IsHomogeneous 1705 := by
  unfold a02116
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02115.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha00937.pow 1)))

@[irreducible]
def a02117 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00362 ^ 1 * a00937 ^ 1) + (C ((3 : ℂ) / (200 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a02116 ^ 1)
theorem ha02117 : a02117.IsHomogeneous 1766 := by
  unfold a02117
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00362.pow 1)).mul (ha00937.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (200 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha02116.pow 1)))

@[irreducible]
def a02118 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a01028 ^ 1) + (C ((25 : ℂ) / (192 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a02117 ^ 1)
theorem ha02118 : a02118.IsHomogeneous 1778 := by
  unfold a02118
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha01028.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (192 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha02117.pow 1)))

@[irreducible]
def a02119 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00046 ^ 1) + (C ((-1 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 1 * a00082 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a00012 ^ 4 * a00014 ^ 3 * a00039 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00061 ^ 1) + (C ((1 : ℂ) / (5760 : ℂ)) * a00000 ^ 1 * a00001 ^ 14 * a00002 ^ 3 * a00004 ^ 5 * a00005 ^ 4 * a00014 ^ 1 * a00100 ^ 1)
theorem ha02119 : a02119.IsHomogeneous 69 := by
  unfold a02119
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00046.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha00082.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 3)).mul (ha00039.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00061.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5760 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 14)).mul (ha00002.pow 3)).mul (ha00004.pow 5)).mul (ha00005.pow 4)).mul (ha00014.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a02120 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00012 ^ 2 * a00014 ^ 1 * a00061 ^ 1) + (C ((-1 : ℂ) / (720 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 3 * a00004 ^ 5 * a00005 ^ 3 * a00014 ^ 1 * a00100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00014 ^ 2 * a00046 ^ 1) + (C ((1 : ℂ) / (192 : ℂ)) * a00000 ^ 1 * a00001 ^ 8 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 2 * a00012 ^ 1 * a00082 ^ 1)
theorem ha02120 : a02120.IsHomogeneous 67 := by
  unfold a02120
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00061.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (720 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 3)).mul (ha00004.pow 5)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00046.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (192 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00082.pow 1)))

@[irreducible]
def a02121 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a02120 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00125 ^ 1 * a02119 ^ 1)
theorem ha02121 : a02121.IsHomogeneous 146 := by
  unfold a02121
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha02120.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00125.pow 1)).mul (ha02119.pow 1)))

@[irreducible]
def a02122 : Poly := (C ((-25 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00025 ^ 1 * a00148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1)
theorem ha02122 : a02122.IsHomogeneous 147 := by
  unfold a02122
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00025.pow 1)).mul (ha00148.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)))

@[irreducible]
def a02123 : Poly := (C ((-50 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00002 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a00368 ^ 1 * a00389 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a02122 ^ 1)
theorem ha02123 : a02123.IsHomogeneous 159 := by
  unfold a02123
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-50 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00368.pow 1)).mul (ha00389.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha02122.pow 1)))

@[irreducible]
def a02124 : Poly := (C ((-200 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00025 ^ 1 * a00976 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02123 ^ 1)
theorem ha02124 : a02124.IsHomogeneous 159 := by
  unfold a02124
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-200 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00025.pow 1)).mul (ha00976.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02123.pow 1)))

@[irreducible]
def a02125 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2)
theorem ha02125 : a02125.IsHomogeneous 30 := by
  unfold a02125
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00042.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a02126 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02125 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2)
theorem ha02126 : a02126.IsHomogeneous 30 := by
  unfold a02126
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02125.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a02127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00032 ^ 1)
theorem ha02127 : a02127.IsHomogeneous 19 := by
  unfold a02127
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a02128 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02127 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2) + (C ((2 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00032 ^ 1)
theorem ha02128 : a02128.IsHomogeneous 19 := by
  unfold a02128
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02127.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a02129 : Poly := (C ((-1 : ℂ) / (144 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00025 ^ 1 * a02128 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a02126 ^ 1)
theorem ha02129 : a02129.IsHomogeneous 36 := by
  unfold a02129
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00025.pow 1)).mul (ha02128.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha02126.pow 1)))

@[irreducible]
def a02130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 1 * a00950 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a02129 ^ 1)
theorem ha02130 : a02130.IsHomogeneous 85 := by
  unfold a02130
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha00950.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha02129.pow 1)))

@[irreducible]
def a02131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02130 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00370 ^ 1 * a00393 ^ 1)
theorem ha02131 : a02131.IsHomogeneous 121 := by
  unfold a02131
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00370.pow 1)).mul (ha00393.pow 1)))

@[irreducible]
def a02132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a00982 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 2 * a02131 ^ 1)
theorem ha02132 : a02132.IsHomogeneous 141 := by
  unfold a02132
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha00982.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha02131.pow 1)))

@[irreducible]
def a02133 : Poly := (C ((-1 : ℂ) / (432 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00009 ^ 2)
theorem ha02133 : a02133.IsHomogeneous 19 := by
  unfold a02133
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (432 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00009.pow 2)))

@[irreducible]
def a02134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00146 ^ 1 * a00953 ^ 1) + (C ((3 : ℂ) / (25 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a02133 ^ 1)
theorem ha02134 : a02134.IsHomogeneous 121 := by
  unfold a02134
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00146.pow 1)).mul (ha00953.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (25 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02133.pow 1)))

@[irreducible]
def a02135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00372 ^ 1 * a00387 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a02134 ^ 1)
theorem ha02135 : a02135.IsHomogeneous 121 := by
  unfold a02135
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00372.pow 1)).mul (ha00387.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha02134.pow 1)))

@[irreducible]
def a02136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00138 ^ 1 * a00974 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a02135 ^ 1)
theorem ha02136 : a02136.IsHomogeneous 123 := by
  unfold a02136
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00138.pow 1)).mul (ha00974.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha02135.pow 1)))

@[irreducible]
def a02137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00368 ^ 1)
theorem ha02137 : a02137.IsHomogeneous 25 := by
  unfold a02137
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a02138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02137 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1)
theorem ha02138 : a02138.IsHomogeneous 25 := by
  unfold a02138
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02137.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)))

@[irreducible]
def a02139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00958 ^ 1) + (C ((3 : ℂ) / (20 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a02138 ^ 1)
theorem ha02139 : a02139.IsHomogeneous 79 := by
  unfold a02139
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00958.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (20 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha02138.pow 1)))

@[irreducible]
def a02140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00375 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a02139 ^ 1)
theorem ha02140 : a02140.IsHomogeneous 79 := by
  unfold a02140
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00375.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha02139.pow 1)))

@[irreducible]
def a02141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00046 ^ 1 * a00139 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a02140 ^ 1)
theorem ha02141 : a02141.IsHomogeneous 81 := by
  unfold a02141
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00046.pow 1)).mul (ha00139.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha02140.pow 1)))

@[irreducible]
def a02142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02141 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a00039 ^ 1 * a00042 ^ 1 * a00126 ^ 1)
theorem ha02142 : a02142.IsHomogeneous 81 := by
  unfold a02142
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02141.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00039.pow 1)).mul (ha00042.pow 1)).mul (ha00126.pow 1)))

@[irreducible]
def a02143 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a00042 ^ 1)
theorem ha02143 : a02143.IsHomogeneous 31 := by
  unfold a02143
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a02144 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02143 ^ 1)
theorem ha02144 : a02144.IsHomogeneous 31 := by
  unfold a02144
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00368.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02143.pow 1)))

@[irreducible]
def a02145 : Poly := (C ((-5 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00082 ^ 1 * a00963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a02144 ^ 1)
theorem ha02145 : a02145.IsHomogeneous 81 := by
  unfold a02145
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00082.pow 1)).mul (ha00963.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha02144.pow 1)))

@[irreducible]
def a02146 : Poly := (C ((-20 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00061 ^ 1 * a00379 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02145 ^ 1)
theorem ha02146 : a02146.IsHomogeneous 81 := by
  unfold a02146
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-20 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00061.pow 1)).mul (ha00379.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02145.pow 1)))

@[irreducible]
def a02147 : Poly := (C ((-40 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00046 ^ 1 * a00141 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02146 ^ 1)
theorem ha02147 : a02147.IsHomogeneous 81 := by
  unfold a02147
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-40 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00046.pow 1)).mul (ha00141.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02146.pow 1)))

@[irreducible]
def a02148 : Poly := (C ((-80 : ℂ) / (3 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a00039 ^ 1 * a00042 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02147 ^ 1)
theorem ha02148 : a02148.IsHomogeneous 81 := by
  unfold a02148
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-80 : ℂ) / (3 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00039.pow 1)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02147.pow 1)))

@[irreducible]
def a02149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02142 ^ 1) + (C ((1 : ℂ) / (100 : ℂ)) * a02148 ^ 1)
theorem ha02149 : a02149.IsHomogeneous 81 := by
  unfold a02149
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02142.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (100 : ℂ))).mul (ha02148.pow 1)))

@[irreducible]
def a02150 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a00042 ^ 1)
theorem ha02150 : a02150.IsHomogeneous 31 := by
  unfold a02150
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a02151 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02150 ^ 1)
theorem ha02151 : a02151.IsHomogeneous 31 := by
  unfold a02151
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00368.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02150.pow 1)))

@[irreducible]
def a02152 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02151 ^ 1)
theorem ha02152 : a02152.IsHomogeneous 31 := by
  unfold a02152
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02151.pow 1)))

@[irreducible]
def a02153 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00082 ^ 1 * a00970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a02152 ^ 1)
theorem ha02153 : a02153.IsHomogeneous 81 := by
  unfold a02153
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00082.pow 1)).mul (ha00970.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha02152.pow 1)))

@[irreducible]
def a02154 : Poly := (C ((-18 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00061 ^ 1 * a00384 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02153 ^ 1)
theorem ha02154 : a02154.IsHomogeneous 81 := by
  unfold a02154
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00061.pow 1)).mul (ha00384.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02153.pow 1)))

@[irreducible]
def a02155 : Poly := (C ((-16 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00046 ^ 1 * a00144 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02154 ^ 1)
theorem ha02155 : a02155.IsHomogeneous 81 := by
  unfold a02155
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00046.pow 1)).mul (ha00144.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02154.pow 1)))

@[irreducible]
def a02156 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a00039 ^ 1 * a00042 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02155 ^ 1)
theorem ha02156 : a02156.IsHomogeneous 81 := by
  unfold a02156
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00039.pow 1)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02155.pow 1)))

@[irreducible]
def a02157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02149 ^ 1) + (C ((1 : ℂ) / (60 : ℂ)) * a02156 ^ 1)
theorem ha02157 : a02157.IsHomogeneous 81 := by
  unfold a02157
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02149.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (60 : ℂ))).mul (ha02156.pow 1)))

@[irreducible]
def a02158 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 3 * a00127 ^ 1 * a02157 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a02136 ^ 1)
theorem ha02158 : a02158.IsHomogeneous 123 := by
  unfold a02158
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00127.pow 1)).mul (ha02157.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha02136.pow 1)))

@[irreducible]
def a02159 : Poly := (C ((-50 : ℂ) / (3 : ℂ)) * a00014 ^ 3 * a02158 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02132 ^ 1)
theorem ha02159 : a02159.IsHomogeneous 141 := by
  unfold a02159
  exact ((((isHomogeneous_C (σ := Fin 6) ((-50 : ℂ) / (3 : ℂ))).mul (ha00014.pow 3)).mul (ha02158.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02132.pow 1)))

@[irreducible]
def a02160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02159 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 2 * a02124 ^ 1)
theorem ha02160 : a02160.IsHomogeneous 171 := by
  unfold a02160
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02159.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 2)).mul (ha02124.pow 1)))

@[irreducible]
def a02161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00082 ^ 1 * a00100 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00395 ^ 1)
theorem ha02161 : a02161.IsHomogeneous 98 := by
  unfold a02161
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00395.pow 1)))

@[irreducible]
def a02162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00985 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00100 ^ 1 * a02161 ^ 1)
theorem ha02162 : a02162.IsHomogeneous 136 := by
  unfold a02162
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00985.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00100.pow 1)).mul (ha02161.pow 1)))

@[irreducible]
def a02163 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00082 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 1 * a00003 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a00039 ^ 1 * a00100 ^ 1)
theorem ha02163 : a02163.IsHomogeneous 80 := by
  unfold a02163
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00082.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha00039.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a02164 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a02163 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00061 ^ 2)
theorem ha02164 : a02164.IsHomogeneous 85 := by
  unfold a02164
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha02163.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00061.pow 2)))

@[irreducible]
def a02165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00046 ^ 1 * a00082 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02164 ^ 1)
theorem ha02165 : a02165.IsHomogeneous 85 := by
  unfold a02165
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00046.pow 1)).mul (ha00082.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02164.pow 1)))

@[irreducible]
def a02166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02165 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a00039 ^ 1 * a00100 ^ 1)
theorem ha02166 : a02166.IsHomogeneous 85 := by
  unfold a02166
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02165.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00039.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a02167 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a02166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00082 ^ 1 * a00982 ^ 1)
theorem ha02167 : a02167.IsHomogeneous 134 := by
  unfold a02167
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha02166.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha00982.pow 1)))

@[irreducible]
def a02168 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02167 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00061 ^ 1 * a00393 ^ 1)
theorem ha02168 : a02168.IsHomogeneous 134 := by
  unfold a02168
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02167.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00061.pow 1)).mul (ha00393.pow 1)))

@[irreducible]
def a02169 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02168 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 3 * a00005 ^ 2 * a00014 ^ 2 * a00046 ^ 1 * a00082 ^ 1 * a00100 ^ 1)
theorem ha02169 : a02169.IsHomogeneous 134 := by
  unfold a02169
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02168.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00046.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a02170 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02169 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 4 * a00039 ^ 1 * a00100 ^ 2)
theorem ha02170 : a02170.IsHomogeneous 134 := by
  unfold a02170
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02169.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00039.pow 1)).mul (ha00100.pow 2)))

@[irreducible]
def a02171 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02170 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a02162 ^ 1)
theorem ha02171 : a02171.IsHomogeneous 158 := by
  unfold a02171
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02170.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02162.pow 1)))

@[irreducible]
def a02172 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 3 * a00100 ^ 1 * a00126 ^ 2 * a00127 ^ 1 * a02171 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00042 ^ 2 * a00126 ^ 1 * a00151 ^ 1 * a00986 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00150 ^ 1 * a00988 ^ 1) + (C ((25 : ℂ) / (1728 : ℂ)) * a00000 ^ 1 * a00042 ^ 1 * a00396 ^ 1 * a00398 ^ 1)
theorem ha02172 : a02172.IsHomogeneous 375 := by
  unfold a02172
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 3)).mul (ha00100.pow 1)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha02171.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00042.pow 2)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha00986.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00150.pow 1)).mul (ha00988.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (1728 : ℂ))).mul (ha00000.pow 1)).mul (ha00042.pow 1)).mul (ha00396.pow 1)).mul (ha00398.pow 1)))

@[irreducible]
def a02173 : Poly := (C ((-9 : ℂ) / (200 : ℂ)) * a00001 ^ 6 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a00042 ^ 3 * a00100 ^ 3 * a02160 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02172 ^ 1)
theorem ha02173 : a02173.IsHomogeneous 375 := by
  unfold a02173
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (200 : ℂ))).mul (ha00001.pow 6)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00100.pow 3)).mul (ha02160.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02172.pow 1)))

@[irreducible]
def a02174 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a00126 ^ 1)
theorem ha02174 : a02174.IsHomogeneous 37 := by
  unfold a02174
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 2)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00126.pow 1)))

@[irreducible]
def a02175 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1 * a00368 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a02174 ^ 1)
theorem ha02175 : a02175.IsHomogeneous 37 := by
  unfold a02175
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00368.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02174.pow 1)))

@[irreducible]
def a02176 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a02175 ^ 1)
theorem ha02176 : a02176.IsHomogeneous 37 := by
  unfold a02176
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02175.pow 1)))

@[irreducible]
def a02177 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02176 ^ 1)
theorem ha02177 : a02177.IsHomogeneous 37 := by
  unfold a02177
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00126.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02176.pow 1)))

@[irreducible]
def a02178 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00025 ^ 1 * a00138 ^ 1 * a00991 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a00127 ^ 1 * a02177 ^ 1)
theorem ha02178 : a02178.IsHomogeneous 67 := by
  unfold a02178
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00025.pow 1)).mul (ha00138.pow 1)).mul (ha00991.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00127.pow 1)).mul (ha02177.pow 1)))

@[irreducible]
def a02179 : Poly := (C ((-3 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 1 * a00009 ^ 1 * a00372 ^ 1 * a00400 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02178 ^ 1)
theorem ha02179 : a02179.IsHomogeneous 73 := by
  unfold a02179
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha00400.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02178.pow 1)))

@[irreducible]
def a02180 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a00953 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02179 ^ 1)
theorem ha02180 : a02180.IsHomogeneous 73 := by
  unfold a02180
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha00953.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02179.pow 1)))

@[irreducible]
def a02181 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00126 ^ 2 * a02133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a02180 ^ 1)
theorem ha02181 : a02181.IsHomogeneous 85 := by
  unfold a02181
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00126.pow 2)).mul (ha02133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha02180.pow 1)))

@[irreducible]
def a02182 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00100 ^ 2 * a00126 ^ 2 * a00127 ^ 1 * a02166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 3 * a00005 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a00982 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00082 ^ 1 * a00996 ^ 1) + (C ((25 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a00393 ^ 1 * a00404 ^ 1)
theorem ha02182 : a02182.IsHomogeneous 267 := by
  unfold a02182
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha02166.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha00982.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha00996.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha00393.pow 1)).mul (ha00404.pow 1)))

@[irreducible]
def a02183 : Poly := (C ((-3 : ℂ) / (400 : ℂ)) * a00001 ^ 7 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 3 * a00014 ^ 4 * a00100 ^ 4 * a02181 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02182 ^ 1)
theorem ha02183 : a02183.IsHomogeneous 267 := by
  unfold a02183
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (400 : ℂ))).mul (ha00001.pow 7)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00014.pow 4)).mul (ha00100.pow 4)).mul (ha02181.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02182.pow 1)))

@[irreducible]
def a02184 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00012 ^ 4 * a00014 ^ 2 * a00042 ^ 4 * a00125 ^ 1 * a02183 ^ 1) + (C ((-3 : ℂ) / (1 : ℂ)) * a00012 ^ 4 * a00125 ^ 1 * a02173 ^ 1) + (C ((-3 : ℂ) / (2000 : ℂ)) * a00000 ^ 1 * a00001 ^ 11 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 5 * a00042 ^ 4 * a00100 ^ 5 * a00367 ^ 1) + (C ((-1 : ℂ) / (5 : ℂ)) * a00001 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 5 * a00042 ^ 4 * a00100 ^ 3 * a00126 ^ 2 * a00127 ^ 1 * a02121 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 4 * a00042 ^ 4 * a00100 ^ 2 * a00126 ^ 1 * a00153 ^ 1 * a00940 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00042 ^ 1 * a00136 ^ 1 * a00988 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 3 * a00100 ^ 2 * a00126 ^ 1 * a00151 ^ 1 * a00940 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 4 * a00136 ^ 1 * a00996 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00042 ^ 2 * a00100 ^ 1 * a00367 ^ 1 * a00398 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00012 ^ 2 * a00014 ^ 3 * a00042 ^ 4 * a00100 ^ 1 * a00367 ^ 1 * a00404 ^ 1)
theorem ha02184 : a02184.IsHomogeneous 468 := by
  unfold a02184
  exact (((((((((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha00125.pow 1)).mul (ha02183.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00012.pow 4)).mul (ha00125.pow 1)).mul (ha02173.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2000 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 11)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 5)).mul (ha00042.pow 4)).mul (ha00100.pow 5)).mul (ha00367.pow 1))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00001.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 5)).mul (ha00042.pow 4)).mul (ha00100.pow 3)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha02121.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 4)).mul (ha00100.pow 2)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha00940.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00042.pow 1)).mul (ha00136.pow 1)).mul (ha00988.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00100.pow 2)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha00940.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha00136.pow 1)).mul (ha00996.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha00367.pow 1)).mul (ha00398.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 3)).mul (ha00042.pow 4)).mul (ha00100.pow 1)).mul (ha00367.pow 1)).mul (ha00404.pow 1)))

@[irreducible]
def a02185 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00368 ^ 1)
theorem ha02185 : a02185.IsHomogeneous 25 := by
  unfold a02185
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a02186 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a00042 ^ 1)
theorem ha02186 : a02186.IsHomogeneous 31 := by
  unfold a02186
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a02187 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a02185 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02186 ^ 1)
theorem ha02187 : a02187.IsHomogeneous 31 := by
  unfold a02187
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha02185.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02186.pow 1)))

@[irreducible]
def a02188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00368 ^ 1)
theorem ha02188 : a02188.IsHomogeneous 25 := by
  unfold a02188
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a02189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02185 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a02188 ^ 1)
theorem ha02189 : a02189.IsHomogeneous 25 := by
  unfold a02189
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02185.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha02188.pow 1)))

@[irreducible]
def a02190 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a02189 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02187 ^ 1)
theorem ha02190 : a02190.IsHomogeneous 31 := by
  unfold a02190
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha02189.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02187.pow 1)))

@[irreducible]
def a02191 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00009 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00040 ^ 1 * a00155 ^ 1)
theorem ha02191 : a02191.IsHomogeneous 33 := by
  unfold a02191
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00040.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a02192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00009 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (1944 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00040 ^ 1 * a00155 ^ 1)
theorem ha02192 : a02192.IsHomogeneous 33 := by
  unfold a02192
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1944 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00040.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a02193 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02191 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a02192 ^ 1)
theorem ha02193 : a02193.IsHomogeneous 33 := by
  unfold a02193
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02191.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha02192.pow 1)))

@[irreducible]
def a02194 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a00129 ^ 1)
theorem ha02194 : a02194.IsHomogeneous 27 := by
  unfold a02194
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a02195 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a02191 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a02194 ^ 1)
theorem ha02195 : a02195.IsHomogeneous 39 := by
  unfold a02195
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha02191.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha02194.pow 1)))

@[irreducible]
def a02196 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a02193 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02195 ^ 1)
theorem ha02196 : a02196.IsHomogeneous 39 := by
  unfold a02196
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha02193.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02195.pow 1)))

@[irreducible]
def a02197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00009 ^ 1 * a00014 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00045 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00037 ^ 1)
theorem ha02197 : a02197.IsHomogeneous 25 := by
  unfold a02197
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00045.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00037.pow 1)))

@[irreducible]
def a02198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00045 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02197 ^ 1)
theorem ha02198 : a02198.IsHomogeneous 25 := by
  unfold a02198
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00045.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02197.pow 1)))

@[irreducible]
def a02199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00058 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1)
theorem ha02199 : a02199.IsHomogeneous 36 := by
  unfold a02199
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).mul (ha00156.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00058.pow 1)).mul (ha00156.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a02200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02199 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00058 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1)
theorem ha02200 : a02200.IsHomogeneous 36 := by
  unfold a02200
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02199.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00058.pow 1)).mul (ha00156.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a02201 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a02200 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00014 ^ 1 * a00130 ^ 1 * a02198 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a02196 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a02190 ^ 1)
theorem ha02201 : a02201.IsHomogeneous 43 := by
  unfold a02201
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha02200.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha02198.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha02196.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha02190.pow 1)))

@[irreducible]
def a02202 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00100 ^ 1 * a00445 ^ 1) + (C ((-2 : ℂ) / (5 : ℂ)) * a00001 ^ 6 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 6 * a00039 ^ 1 * a00100 ^ 3 * a00134 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00002 ^ 3 * a00005 ^ 2 * a00014 ^ 4 * a00046 ^ 1 * a00100 ^ 2 * a00362 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00082 ^ 1 * a01026 ^ 1)
theorem ha02202 : a02202.IsHomogeneous 243 := by
  unfold a02202
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00100.pow 1)).mul (ha00445.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 6)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 6)).mul (ha00039.pow 1)).mul (ha00100.pow 3)).mul (ha00134.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00046.pow 1)).mul (ha00100.pow 2)).mul (ha00362.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha01026.pow 1)))

@[irreducible]
def a02203 : Poly := (C ((-3 : ℂ) / (50 : ℂ)) * a00001 ^ 7 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 3 * a00014 ^ 7 * a00100 ^ 4 * a02201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02202 ^ 1)
theorem ha02203 : a02203.IsHomogeneous 243 := by
  unfold a02203
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (50 : ℂ))).mul (ha00001.pow 7)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00014.pow 7)).mul (ha00100.pow 4)).mul (ha02201.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02202.pow 1)))

@[irreducible]
def a02204 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00012 ^ 4 * a00014 ^ 2 * a00042 ^ 4 * a00125 ^ 1 * a00126 ^ 2 * a00127 ^ 1 * a02203 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a02184 ^ 1)
theorem ha02204 : a02204.IsHomogeneous 528 := by
  unfold a02204
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha00125.pow 1)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha02203.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha02184.pow 1)))

@[irreducible]
def a02205 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a02204 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00042 ^ 3 * a00126 ^ 1 * a00364 ^ 1 * a01026 ^ 1)
theorem ha02205 : a02205.IsHomogeneous 1005 := by
  unfold a02205
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha02204.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00042.pow 3)).mul (ha00126.pow 1)).mul (ha00364.pow 1)).mul (ha01026.pow 1)))

@[irreducible]
def a02206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a02205 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00000 ^ 1 * a00012 ^ 2 * a00042 ^ 2 * a00445 ^ 1 * a00937 ^ 1)
theorem ha02206 : a02206.IsHomogeneous 1458 := by
  unfold a02206
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha02205.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00000.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 2)).mul (ha00445.pow 1)).mul (ha00937.pow 1)))

@[irreducible]
def a02207 : Poly := (C ((-1 : ℂ) / (768 : ℂ)) * a00000 ^ 1 * a00001 ^ 8 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 2 * a00012 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00014 ^ 2 * a00188 ^ 1) + (C ((1 : ℂ) / (16 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00012 ^ 2 * a00014 ^ 1 * a00211 ^ 1) + (C ((1 : ℂ) / (3840 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 3 * a00004 ^ 5 * a00005 ^ 3 * a00014 ^ 1 * a00260 ^ 1)
theorem ha02207 : a02207.IsHomogeneous 73 := by
  unfold a02207
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (768 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00241.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00188.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (16 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00211.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3840 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 3)).mul (ha00004.pow 5)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a02208 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00125 ^ 1 * a02207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a00938 ^ 1)
theorem ha02208 : a02208.IsHomogeneous 142 := by
  unfold a02208
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00125.pow 1)).mul (ha02207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha00938.pow 1)))

@[irreducible]
def a02209 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a00014 ^ 1 * a00211 ^ 1) + (C ((1 : ℂ) / (80 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 1 * a00260 ^ 1)
theorem ha02209 : a02209.IsHomogeneous 66 := by
  unfold a02209
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00241.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00211.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (80 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a02210 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a00939 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a02209 ^ 1)
theorem ha02210 : a02210.IsHomogeneous 145 := by
  unfold a02210
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha00939.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha02209.pow 1)))

@[irreducible]
def a02211 : Poly := (C ((-1 : ℂ) / (16 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a02210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a02208 ^ 1)
theorem ha02211 : a02211.IsHomogeneous 147 := by
  unfold a02211
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (16 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha02210.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha02208.pow 1)))

@[irreducible]
def a02212 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a00940 ^ 1)
theorem ha02212 : a02212.IsHomogeneous 425 := by
  unfold a02212
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02211.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha00940.pow 1)))

@[irreducible]
def a02213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a00940 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a02212 ^ 1)
theorem ha02213 : a02213.IsHomogeneous 504 := by
  unfold a02213
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha00940.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha02212.pow 1)))

@[irreducible]
def a02214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a00940 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02213 ^ 1)
theorem ha02214 : a02214.IsHomogeneous 612 := by
  unfold a02214
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha00940.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02213.pow 1)))

@[irreducible]
def a02215 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a00940 ^ 1)
theorem ha02215 : a02215.IsHomogeneous 588 := by
  unfold a02215
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha00940.pow 1)))

@[irreducible]
def a02216 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a00492 ^ 1)
theorem ha02216 : a02216.IsHomogeneous 715 := by
  unfold a02216
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha00492.pow 1)))

@[irreducible]
def a02217 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a00501 ^ 1)
theorem ha02217 : a02217.IsHomogeneous 655 := by
  unfold a02217
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha00501.pow 1)))

@[irreducible]
def a02218 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a00452 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a01103 ^ 1)
theorem ha02218 : a02218.IsHomogeneous 780 := by
  unfold a02218
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha00452.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a02219 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a00452 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a01118 ^ 1)
theorem ha02219 : a02219.IsHomogeneous 696 := by
  unfold a02219
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha00452.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha01118.pow 1)))

@[irreducible]
def a02220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00148 ^ 1 * a01041 ^ 1) + (C ((9 : ℂ) / (4 : ℂ)) * a00368 ^ 1 * a00480 ^ 1)
theorem ha02220 : a02220.IsHomogeneous 145 := by
  unfold a02220
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00148.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (4 : ℂ))).mul (ha00368.pow 1)).mul (ha00480.pow 1)))

@[irreducible]
def a02221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00007 ^ 1 * a00014 ^ 4 * a00456 ^ 1) + (C ((25 : ℂ) / (162 : ℂ)) * a00000 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a02220 ^ 1)
theorem ha02221 : a02221.IsHomogeneous 157 := by
  unfold a02221
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 4)).mul (ha00456.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (162 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02220.pow 1)))

@[irreducible]
def a02222 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00389 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a01083 ^ 1)
theorem ha02222 : a02222.IsHomogeneous 156 := by
  unfold a02222
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00389.pow 1)).mul (ha00455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha01083.pow 1)))

@[irreducible]
def a02223 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02221 ^ 1) + (C ((50 : ℂ) / (3 : ℂ)) * a00001 ^ 1 * a02222 ^ 1)
theorem ha02223 : a02223.IsHomogeneous 157 := by
  unfold a02223
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02221.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((50 : ℂ) / (3 : ℂ))).mul (ha00001.pow 1)).mul (ha02222.pow 1)))

@[irreducible]
def a02224 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00155 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1)
theorem ha02224 : a02224.IsHomogeneous 30 := by
  unfold a02224
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a02225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a02224 ^ 1)
theorem ha02225 : a02225.IsHomogeneous 35 := by
  unfold a02225
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha02224.pow 1)))

@[irreducible]
def a02226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02225 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a02224 ^ 1)
theorem ha02226 : a02226.IsHomogeneous 35 := by
  unfold a02226
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02225.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha02224.pow 1)))

@[irreducible]
def a02227 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02225 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02226 ^ 1)
theorem ha02227 : a02227.IsHomogeneous 35 := by
  unfold a02227
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02225.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02226.pow 1)))

@[irreducible]
def a02228 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a02227 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a00945 ^ 1)
theorem ha02228 : a02228.IsHomogeneous 41 := by
  unfold a02228
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha02227.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha00945.pow 1)))

@[irreducible]
def a02229 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00032 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00130 ^ 1)
theorem ha02229 : a02229.IsHomogeneous 18 := by
  unfold a02229
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a02230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a00156 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1)
theorem ha02230 : a02230.IsHomogeneous 36 := by
  unfold a02230
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha00156.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a02231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02230 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a02229 ^ 1)
theorem ha02231 : a02231.IsHomogeneous 36 := by
  unfold a02231
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02230.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha02229.pow 1)))

@[irreducible]
def a02232 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02230 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02231 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a02229 ^ 1)
theorem ha02232 : a02232.IsHomogeneous 36 := by
  unfold a02232
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02230.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02231.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha02229.pow 1)))

@[irreducible]
def a02233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02231 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a02229 ^ 1)
theorem ha02233 : a02233.IsHomogeneous 36 := by
  unfold a02233
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02231.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha02229.pow 1)))

@[irreducible]
def a02234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02232 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02233 ^ 1) + (C ((1 : ℂ) / (432 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a02229 ^ 1)
theorem ha02234 : a02234.IsHomogeneous 36 := by
  unfold a02234
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02233.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha02229.pow 1)))

@[irreducible]
def a02235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00176 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00133 ^ 1)
theorem ha02235 : a02235.IsHomogeneous 12 := by
  unfold a02235
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00176.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a02236 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a02234 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02228 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 13 * a00001 ^ 3 * a00002 ^ 1 * a00003 ^ 3 * a00004 ^ 3 * a00032 ^ 1 * a02235 ^ 1)
theorem ha02236 : a02236.IsHomogeneous 41 := by
  unfold a02236
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha02234.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02228.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 13)).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00032.pow 1)).mul (ha02235.pow 1)))

@[irreducible]
def a02237 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a02236 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00950 ^ 1)
theorem ha02237 : a02237.IsHomogeneous 79 := by
  unfold a02237
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha02236.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00950.pow 1)))

@[irreducible]
def a02238 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00082 ^ 1 * a00100 ^ 1 * a01048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00370 ^ 1 * a00484 ^ 1)
theorem ha02238 : a02238.IsHomogeneous 115 := by
  unfold a02238
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha01048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00370.pow 1)).mul (ha00484.pow 1)))

@[irreducible]
def a02239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02237 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a02238 ^ 1)
theorem ha02239 : a02239.IsHomogeneous 115 := by
  unfold a02239
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02237.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha02238.pow 1)))

@[irreducible]
def a02240 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00393 ^ 1 * a00459 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a01092 ^ 1)
theorem ha02240 : a02240.IsHomogeneous 151 := by
  unfold a02240
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00393.pow 1)).mul (ha00459.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha01092.pow 1)))

@[irreducible]
def a02241 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02240 ^ 1) + (C ((6 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a02239 ^ 1)
theorem ha02241 : a02241.IsHomogeneous 151 := by
  unfold a02241
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02240.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha02239.pow 1)))

@[irreducible]
def a02242 : Poly := (C ((-1 : ℂ) / (144 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00131 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00006 ^ 1 * a00007 ^ 1 * a00009 ^ 1) + (C ((1 : ℂ) / (432 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 1 * a00004 ^ 3 * a00007 ^ 1)
theorem ha02242 : a02242.IsHomogeneous 22 := by
  unfold a02242
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00131.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00006.pow 1)).mul (ha00007.pow 1)).mul (ha00009.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00007.pow 1)))

@[irreducible]
def a02243 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a02242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a00953 ^ 1)
theorem ha02243 : a02243.IsHomogeneous 120 := by
  unfold a02243
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02242.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha00953.pow 1)))

@[irreducible]
def a02244 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00146 ^ 1 * a01052 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a00476 ^ 1)
theorem ha02244 : a02244.IsHomogeneous 122 := by
  unfold a02244
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha01052.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha00476.pow 1)))

@[irreducible]
def a02245 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a02244 ^ 1) + (C ((48 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a02243 ^ 1)
theorem ha02245 : a02245.IsHomogeneous 127 := by
  unfold a02245
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02244.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha02243.pow 1)))

@[irreducible]
def a02246 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00387 ^ 1 * a00461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a01079 ^ 1)
theorem ha02246 : a02246.IsHomogeneous 120 := by
  unfold a02246
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00387.pow 1)).mul (ha00461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha01079.pow 1)))

@[irreducible]
def a02247 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02245 ^ 1) + (C ((32 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a02246 ^ 1)
theorem ha02247 : a02247.IsHomogeneous 127 := by
  unfold a02247
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02245.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha02246.pow 1)))

@[irreducible]
def a02248 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01041 ^ 1)
theorem ha02248 : a02248.IsHomogeneous 12 := by
  unfold a02248
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00368.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)))

@[irreducible]
def a02249 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00463 ^ 1)
theorem ha02249 : a02249.IsHomogeneous 42 := by
  unfold a02249
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00463.pow 1)))

@[irreducible]
def a02250 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00455 ^ 1)
theorem ha02250 : a02250.IsHomogeneous 12 := by
  unfold a02250
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)))

@[irreducible]
def a02251 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02249 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02250 ^ 1)
theorem ha02251 : a02251.IsHomogeneous 42 := by
  unfold a02251
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02249.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02250.pow 1)))

@[irreducible]
def a02252 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00464 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a02251 ^ 1)
theorem ha02252 : a02252.IsHomogeneous 42 := by
  unfold a02252
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00464.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha02251.pow 1)))

@[irreducible]
def a02253 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00958 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02252 ^ 1)
theorem ha02253 : a02253.IsHomogeneous 78 := by
  unfold a02253
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00958.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02252.pow 1)))

@[irreducible]
def a02254 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00375 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01060 ^ 1)
theorem ha02254 : a02254.IsHomogeneous 86 := by
  unfold a02254
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00375.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01060.pow 1)))

@[irreducible]
def a02255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a02254 ^ 1) + (C ((32 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02253 ^ 1)
theorem ha02255 : a02255.IsHomogeneous 91 := by
  unfold a02255
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02254.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02253.pow 1)))

@[irreducible]
def a02256 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00139 ^ 1 * a00211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00465 ^ 1)
theorem ha02256 : a02256.IsHomogeneous 78 := by
  unfold a02256
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00139.pow 1)).mul (ha00211.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00465.pow 1)))

@[irreducible]
def a02257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02255 ^ 1) + (C ((48 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02256 ^ 1)
theorem ha02257 : a02257.IsHomogeneous 91 := by
  unfold a02257
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02255.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02256.pow 1)))

@[irreducible]
def a02258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00188 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00046 ^ 1 * a00300 ^ 1)
theorem ha02258 : a02258.IsHomogeneous 97 := by
  unfold a02258
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00188.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00046.pow 1)).mul (ha00300.pow 1)))

@[irreducible]
def a02259 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02258 ^ 1) + (C ((9 : ℂ) / (1024 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a02257 ^ 1)
theorem ha02259 : a02259.IsHomogeneous 97 := by
  unfold a02259
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02258.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1024 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha02257.pow 1)))

@[irreducible]
def a02260 : Poly := (C ((-1 : ℂ) / (81 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00463 ^ 1)
theorem ha02260 : a02260.IsHomogeneous 42 := by
  unfold a02260
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (81 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00463.pow 1)))

@[irreducible]
def a02261 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02260 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02250 ^ 1)
theorem ha02261 : a02261.IsHomogeneous 42 := by
  unfold a02261
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02260.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02250.pow 1)))

@[irreducible]
def a02262 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02261 ^ 1)
theorem ha02262 : a02262.IsHomogeneous 78 := by
  unfold a02262
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02261.pow 1)))

@[irreducible]
def a02263 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00379 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01067 ^ 1)
theorem ha02263 : a02263.IsHomogeneous 86 := by
  unfold a02263
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00379.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01067.pow 1)))

@[irreducible]
def a02264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a02263 ^ 1) + (C ((36 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02262 ^ 1)
theorem ha02264 : a02264.IsHomogeneous 91 := by
  unfold a02264
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02263.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02262.pow 1)))

@[irreducible]
def a02265 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00141 ^ 1 * a00211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00469 ^ 1)
theorem ha02265 : a02265.IsHomogeneous 78 := by
  unfold a02265
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00141.pow 1)).mul (ha00211.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00469.pow 1)))

@[irreducible]
def a02266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02264 ^ 1) + (C ((72 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02265 ^ 1)
theorem ha02266 : a02266.IsHomogeneous 91 := by
  unfold a02266
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02264.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02265.pow 1)))

@[irreducible]
def a02267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02258 ^ 1) + (C ((1 : ℂ) / (128 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a02266 ^ 1)
theorem ha02267 : a02267.IsHomogeneous 97 := by
  unfold a02267
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02258.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (128 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha02266.pow 1)))

@[irreducible]
def a02268 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a02267 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02259 ^ 1)
theorem ha02268 : a02268.IsHomogeneous 97 := by
  unfold a02268
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha02267.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02259.pow 1)))

@[irreducible]
def a02269 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00463 ^ 1)
theorem ha02269 : a02269.IsHomogeneous 42 := by
  unfold a02269
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00463.pow 1)))

@[irreducible]
def a02270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02269 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02250 ^ 1)
theorem ha02270 : a02270.IsHomogeneous 42 := by
  unfold a02270
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02269.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02250.pow 1)))

@[irreducible]
def a02271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00464 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02270 ^ 1)
theorem ha02271 : a02271.IsHomogeneous 42 := by
  unfold a02271
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00464.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02270.pow 1)))

@[irreducible]
def a02272 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02271 ^ 1)
theorem ha02272 : a02272.IsHomogeneous 78 := by
  unfold a02272
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00970.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02271.pow 1)))

@[irreducible]
def a02273 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00384 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01074 ^ 1)
theorem ha02273 : a02273.IsHomogeneous 86 := by
  unfold a02273
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00384.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01074.pow 1)))

@[irreducible]
def a02274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a02273 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02272 ^ 1)
theorem ha02274 : a02274.IsHomogeneous 91 := by
  unfold a02274
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02273.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02272.pow 1)))

@[irreducible]
def a02275 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00144 ^ 1 * a00211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00473 ^ 1)
theorem ha02275 : a02275.IsHomogeneous 78 := by
  unfold a02275
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00144.pow 1)).mul (ha00211.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00473.pow 1)))

@[irreducible]
def a02276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02274 ^ 1) + (C ((36 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02275 ^ 1)
theorem ha02276 : a02276.IsHomogeneous 91 := by
  unfold a02276
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02274.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((36 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02275.pow 1)))

@[irreducible]
def a02277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02258 ^ 1) + (C ((3 : ℂ) / (128 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a02276 ^ 1)
theorem ha02277 : a02277.IsHomogeneous 97 := by
  unfold a02277
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02258.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (128 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha02276.pow 1)))

@[irreducible]
def a02278 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a02277 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02268 ^ 1)
theorem ha02278 : a02278.IsHomogeneous 97 := by
  unfold a02278
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha02277.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02268.pow 1)))

@[irreducible]
def a02279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a02278 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a00974 ^ 1)
theorem ha02279 : a02279.IsHomogeneous 115 := by
  unfold a02279
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha02278.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha00974.pow 1)))

@[irreducible]
def a02280 : Poly := (C ((-3 : ℂ) / (256 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a02247 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a02279 ^ 1)
theorem ha02280 : a02280.IsHomogeneous 133 := by
  unfold a02280
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (256 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha02247.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha02279.pow 1)))

@[irreducible]
def a02281 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02280 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00975 ^ 1)
theorem ha02281 : a02281.IsHomogeneous 133 := by
  unfold a02281
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02280.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00975.pow 1)))

@[irreducible]
def a02282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 4 * a02281 ^ 1) + (C ((9 : ℂ) / (5120 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a02241 ^ 1)
theorem ha02282 : a02282.IsHomogeneous 157 := by
  unfold a02282
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 4)).mul (ha02281.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5120 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha02241.pow 1)))

@[irreducible]
def a02283 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02282 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00976 ^ 1)
theorem ha02283 : a02283.IsHomogeneous 187 := by
  unfold a02283
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02282.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00976.pow 1)))

@[irreducible]
def a02284 : Poly := (C ((-9 : ℂ) / (800 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00014 ^ 4 * a02223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02283 ^ 1)
theorem ha02284 : a02284.IsHomogeneous 187 := by
  unfold a02284
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (800 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00014.pow 4)).mul (ha02223.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02283.pow 1)))

@[irreducible]
def a02285 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00398 ^ 1 * a00489 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a01103 ^ 1)
theorem ha02285 : a02285.IsHomogeneous 368 := by
  unfold a02285
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00398.pow 1)).mul (ha00489.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a02286 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a01099 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00396 ^ 1 * a00492 ^ 1)
theorem ha02286 : a02286.IsHomogeneous 344 := by
  unfold a02286
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha01099.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00396.pow 1)).mul (ha00492.pow 1)))

@[irreducible]
def a02287 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00487 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a00155 ^ 1)
theorem ha02287 : a02287.IsHomogeneous 85 := by
  unfold a02287
  exact (((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00487.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a02288 : Poly := (C ((-5 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a02287 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a00483 ^ 1)
theorem ha02288 : a02288.IsHomogeneous 97 := by
  unfold a02288
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02287.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha00483.pow 1)))

@[irreducible]
def a02289 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00100 ^ 1 * a00395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01097 ^ 1)
theorem ha02289 : a02289.IsHomogeneous 133 := by
  unfold a02289
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00100.pow 1)).mul (ha00395.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01097.pow 1)))

@[irreducible]
def a02290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02288 ^ 1) + (C ((25 : ℂ) / (108 : ℂ)) * a02289 ^ 1)
theorem ha02290 : a02290.IsHomogeneous 133 := by
  unfold a02290
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02288.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (108 : ℂ))).mul (ha02289.pow 1)))

@[irreducible]
def a02291 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00188 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00260 ^ 1)
theorem ha02291 : a02291.IsHomogeneous 79 := by
  unfold a02291
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00188.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a02292 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00082 ^ 1 * a00211 ^ 1)
theorem ha02292 : a02292.IsHomogeneous 91 := by
  unfold a02292
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00241.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00082.pow 1)).mul (ha00211.pow 1)))

@[irreducible]
def a02293 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a02291 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a02292 ^ 1)
theorem ha02293 : a02293.IsHomogeneous 93 := by
  unfold a02293
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha02291.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha02292.pow 1)))

@[irreducible]
def a02294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02293 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a02292 ^ 1)
theorem ha02294 : a02294.IsHomogeneous 93 := by
  unfold a02294
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02293.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha02292.pow 1)))

@[irreducible]
def a02295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a02291 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02294 ^ 1)
theorem ha02295 : a02295.IsHomogeneous 93 := by
  unfold a02295
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha02291.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02294.pow 1)))

@[irreducible]
def a02296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00982 ^ 1)
theorem ha02296 : a02296.IsHomogeneous 129 := by
  unfold a02296
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02295.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00982.pow 1)))

@[irreducible]
def a02297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00241 ^ 1 * a00393 ^ 1)
theorem ha02297 : a02297.IsHomogeneous 140 := by
  unfold a02297
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00241.pow 1)).mul (ha00393.pow 1)))

@[irreducible]
def a02298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02296 ^ 1) + (C ((25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a02297 ^ 1)
theorem ha02298 : a02298.IsHomogeneous 142 := by
  unfold a02298
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02296.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha02297.pow 1)))

@[irreducible]
def a02299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00484 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a00211 ^ 1)
theorem ha02299 : a02299.IsHomogeneous 127 := by
  unfold a02299
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00484.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00211.pow 1)))

@[irreducible]
def a02300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02298 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a02299 ^ 1)
theorem ha02300 : a02300.IsHomogeneous 142 := by
  unfold a02300
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02298.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha02299.pow 1)))

@[irreducible]
def a02301 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00188 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00260 ^ 1)
theorem ha02301 : a02301.IsHomogeneous 79 := by
  unfold a02301
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00188.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a02302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02300 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1 * a02301 ^ 1)
theorem ha02302 : a02302.IsHomogeneous 142 := by
  unfold a02302
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02300.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha02301.pow 1)))

@[irreducible]
def a02303 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00985 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02302 ^ 1)
theorem ha02303 : a02303.IsHomogeneous 166 := by
  unfold a02303
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00985.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02302.pow 1)))

@[irreducible]
def a02304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02303 ^ 1) + (C ((9 : ℂ) / (40 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a02290 ^ 1)
theorem ha02304 : a02304.IsHomogeneous 166 := by
  unfold a02304
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02303.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (40 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha02290.pow 1)))

@[irreducible]
def a02305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02304 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a00986 ^ 1)
theorem ha02305 : a02305.IsHomogeneous 274 := by
  unfold a02305
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02304.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha00986.pow 1)))

@[irreducible]
def a02306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 2 * a00126 ^ 1 * a02305 ^ 1) + (C ((25 : ℂ) / (64 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00042 ^ 1 * a02286 ^ 1) + (C ((25 : ℂ) / (64 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a02285 ^ 1)
theorem ha02306 : a02306.IsHomogeneous 370 := by
  unfold a02306
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00126.pow 1)).mul (ha02305.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (64 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00042.pow 1)).mul (ha02286.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (64 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha02285.pow 1)))

@[irreducible]
def a02307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02306 ^ 1) + (C ((20 : ℂ) / (3 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00042 ^ 3 * a00100 ^ 3 * a02284 ^ 1)
theorem ha02307 : a02307.IsHomogeneous 370 := by
  unfold a02307
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02306.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (3 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00042.pow 3)).mul (ha00100.pow 3)).mul (ha02284.pow 1)))

@[irreducible]
def a02308 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a02307 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a00988 ^ 1)
theorem ha02308 : a02308.IsHomogeneous 370 := by
  unfold a02308
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha02307.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha00988.pow 1)))

@[irreducible]
def a02309 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a00988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a02308 ^ 1)
theorem ha02309 : a02309.IsHomogeneous 796 := by
  unfold a02309
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha00988.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a02310 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00368 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a01041 ^ 1)
theorem ha02310 : a02310.IsHomogeneous 18 := by
  unfold a02310
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00368.pow 1)).mul (ha00455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a02311 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02310 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00494 ^ 1)
theorem ha02311 : a02311.IsHomogeneous 48 := by
  unfold a02311
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02310.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00494.pow 1)))

@[irreducible]
def a02312 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02310 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02311 ^ 1)
theorem ha02312 : a02312.IsHomogeneous 48 := by
  unfold a02312
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02310.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02311.pow 1)))

@[irreducible]
def a02313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00494 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02312 ^ 1)
theorem ha02313 : a02313.IsHomogeneous 48 := by
  unfold a02313
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00494.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02312.pow 1)))

@[irreducible]
def a02314 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a02313 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00299 ^ 1 * a00991 ^ 1)
theorem ha02314 : a02314.IsHomogeneous 66 := by
  unfold a02314
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha02313.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00299.pow 1)).mul (ha00991.pow 1)))

@[irreducible]
def a02315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a01107 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00400 ^ 1 * a00461 ^ 1)
theorem ha02315 : a02315.IsHomogeneous 67 := by
  unfold a02315
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha01107.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00400.pow 1)).mul (ha00461.pow 1)))

@[irreducible]
def a02316 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a02314 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a02315 ^ 1)
theorem ha02316 : a02316.IsHomogeneous 78 := by
  unfold a02316
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha02314.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha02315.pow 1)))

@[irreducible]
def a02317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a00494 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a01052 ^ 1)
theorem ha02317 : a02317.IsHomogeneous 61 := by
  unfold a02317
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha00494.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha01052.pow 1)))

@[irreducible]
def a02318 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02316 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a02317 ^ 1)
theorem ha02318 : a02318.IsHomogeneous 78 := by
  unfold a02318
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02316.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha02317.pow 1)))

@[irreducible]
def a02319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00953 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 2 * a00126 ^ 1 * a02242 ^ 1)
theorem ha02319 : a02319.IsHomogeneous 54 := by
  unfold a02319
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00953.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 2)).mul (ha00126.pow 1)).mul (ha02242.pow 1)))

@[irreducible]
def a02320 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02318 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02319 ^ 1)
theorem ha02320 : a02320.IsHomogeneous 84 := by
  unfold a02320
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02318.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02319.pow 1)))

@[irreducible]
def a02321 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02320 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00994 ^ 1)
theorem ha02321 : a02321.IsHomogeneous 90 := by
  unfold a02321
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02320.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00994.pow 1)))

@[irreducible]
def a02322 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00404 ^ 1 * a00484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01118 ^ 1)
theorem ha02322 : a02322.IsHomogeneous 260 := by
  unfold a02322
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00404.pow 1)).mul (ha00484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01118.pow 1)))

@[irreducible]
def a02323 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a00501 ^ 1)
theorem ha02323 : a02323.IsHomogeneous 260 := by
  unfold a02323
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha00501.pow 1)))

@[irreducible]
def a02324 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00310 ^ 1 * a00982 ^ 1)
theorem ha02324 : a02324.IsHomogeneous 177 := by
  unfold a02324
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02295.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00310.pow 1)).mul (ha00982.pow 1)))

@[irreducible]
def a02325 : Poly := (C ((-25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a02322 ^ 1) + (C ((-25 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a02323 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a00126 ^ 1 * a02324 ^ 1)
theorem ha02325 : a02325.IsHomogeneous 262 := by
  unfold a02325
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha02322.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha02323.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02324.pow 1)))

@[irreducible]
def a02326 : Poly := (C ((-3 : ℂ) / (80 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 4 * a02321 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02325 ^ 1)
theorem ha02326 : a02326.IsHomogeneous 262 := by
  unfold a02326
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (80 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 4)).mul (ha02321.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02325.pow 1)))

@[irreducible]
def a02327 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00996 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02326 ^ 1)
theorem ha02327 : a02327.IsHomogeneous 262 := by
  unfold a02327
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00996.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02326.pow 1)))

@[irreducible]
def a02328 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a02327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00296 ^ 1 * a00996 ^ 1)
theorem ha02328 : a02328.IsHomogeneous 688 := by
  unfold a02328
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha02327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00296.pow 1)).mul (ha00996.pow 1)))

@[irreducible]
def a02329 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 4 * a02328 ^ 1) + (C ((-1 : ℂ) / (3 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 4 * a00100 ^ 2 * a00126 ^ 1 * a02215 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 3 * a02309 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a00042 ^ 3 * a00100 ^ 2 * a00126 ^ 1 * a02214 ^ 1) + (C ((1 : ℂ) / (28800 : ℂ)) * a00000 ^ 1 * a00001 ^ 10 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 4 * a00042 ^ 4 * a00100 ^ 5 * a00452 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 3 * a00042 ^ 4 * a00100 ^ 1 * a02217 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 1 * a00042 ^ 2 * a00100 ^ 1 * a02216 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 4 * a02219 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00042 ^ 1 * a02218 ^ 1)
theorem ha02329 : a02329.IsHomogeneous 818 := by
  unfold a02329
  exact (((((((((((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha02328.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 4)).mul (ha00100.pow 2)).mul (ha00126.pow 1)).mul (ha02215.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha02309.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 3)).mul (ha00100.pow 2)).mul (ha00126.pow 1)).mul (ha02214.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (28800 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 10)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 4)).mul (ha00042.pow 4)).mul (ha00100.pow 5)).mul (ha00452.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 4)).mul (ha00100.pow 1)).mul (ha02217.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha02216.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 4)).mul (ha02219.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 1)).mul (ha02218.pow 1)))

@[irreducible]
def a02330 : Poly := (C ((-9 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00368 ^ 1) + (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01041 ^ 1)
theorem ha02330 : a02330.IsHomogeneous 12 := by
  unfold a02330
  exact (((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00368.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01041.pow 1)))

@[irreducible]
def a02331 : Poly := (C ((-1 : ℂ) / (81 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02330 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00884 ^ 1)
theorem ha02331 : a02331.IsHomogeneous 42 := by
  unfold a02331
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (81 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02330.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00884.pow 1)))

@[irreducible]
def a02332 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00455 ^ 1)
theorem ha02332 : a02332.IsHomogeneous 12 := by
  unfold a02332
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)))

@[irreducible]
def a02333 : Poly := (C ((-3 : ℂ) / (8 : ℂ)) * a02332 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02330 ^ 1)
theorem ha02333 : a02333.IsHomogeneous 12 := by
  unfold a02333
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (8 : ℂ))).mul (ha02332.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02330.pow 1)))

@[irreducible]
def a02334 : Poly := (C ((-1 : ℂ) / (81 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02333 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02331 ^ 1)
theorem ha02334 : a02334.IsHomogeneous 42 := by
  unfold a02334
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (81 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02333.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02331.pow 1)))

@[irreducible]
def a02335 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00884 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02331 ^ 1)
theorem ha02335 : a02335.IsHomogeneous 42 := by
  unfold a02335
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00884.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02331.pow 1)))

@[irreducible]
def a02336 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02334 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02335 ^ 1)
theorem ha02336 : a02336.IsHomogeneous 42 := by
  unfold a02336
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02334.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02335.pow 1)))

@[irreducible]
def a02337 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00885 ^ 1) + (C ((1 : ℂ) / (240 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02332 ^ 1)
theorem ha02337 : a02337.IsHomogeneous 42 := by
  unfold a02337
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00885.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (240 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02332.pow 1)))

@[irreducible]
def a02338 : Poly := (C ((-1 : ℂ) / (90 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02333 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02337 ^ 1)
theorem ha02338 : a02338.IsHomogeneous 42 := by
  unfold a02338
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (90 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02333.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02337.pow 1)))

@[irreducible]
def a02339 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02334 ^ 1) + (C ((10 : ℂ) / (9 : ℂ)) * a02338 ^ 1)
theorem ha02339 : a02339.IsHomogeneous 42 := by
  unfold a02339
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02334.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (9 : ℂ))).mul (ha02338.pow 1)))

@[irreducible]
def a02340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02336 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02339 ^ 1)
theorem ha02340 : a02340.IsHomogeneous 42 := by
  unfold a02340
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02336.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02339.pow 1)))

@[irreducible]
def a02341 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00524 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00596 ^ 1)
theorem ha02341 : a02341.IsHomogeneous 24 := by
  unfold a02341
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00524.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00596.pow 1)))

@[irreducible]
def a02342 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00600 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a00596 ^ 1)
theorem ha02342 : a02342.IsHomogeneous 45 := by
  unfold a02342
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00600.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha00596.pow 1)))

@[irreducible]
def a02343 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a02342 ^ 1) + (C ((1 : ℂ) / (90 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a02341 ^ 1)
theorem ha02343 : a02343.IsHomogeneous 46 := by
  unfold a02343
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha02342.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (90 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha02341.pow 1)))

@[irreducible]
def a02344 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00007 ^ 1 * a00692 ^ 1) + (C ((1 : ℂ) / (360 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00524 ^ 1)
theorem ha02344 : a02344.IsHomogeneous 52 := by
  unfold a02344
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00007.pow 1)).mul (ha00692.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (360 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00524.pow 1)))

@[irreducible]
def a02345 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02344 ^ 1) + (C ((1 : ℂ) / (360 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02341 ^ 1)
theorem ha02345 : a02345.IsHomogeneous 52 := by
  unfold a02345
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02344.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (360 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02341.pow 1)))

@[irreducible]
def a02346 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02345 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a02343 ^ 1)
theorem ha02346 : a02346.IsHomogeneous 52 := by
  unfold a02346
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02345.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha02343.pow 1)))

@[irreducible]
def a02347 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00600 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02342 ^ 1)
theorem ha02347 : a02347.IsHomogeneous 45 := by
  unfold a02347
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00600.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02342.pow 1)))

@[irreducible]
def a02348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a02347 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02343 ^ 1)
theorem ha02348 : a02348.IsHomogeneous 46 := by
  unfold a02348
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha02347.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02343.pow 1)))

@[irreducible]
def a02349 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02346 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a02348 ^ 1)
theorem ha02349 : a02349.IsHomogeneous 52 := by
  unfold a02349
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02346.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha02348.pow 1)))

@[irreducible]
def a02350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a00607 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00539 ^ 1)
theorem ha02350 : a02350.IsHomogeneous 46 := by
  unfold a02350
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha00607.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00539.pow 1)))

@[irreducible]
def a02351 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a00607 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02350 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00539 ^ 1)
theorem ha02351 : a02351.IsHomogeneous 46 := by
  unfold a02351
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha00607.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02350.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00539.pow 1)))

@[irreducible]
def a02352 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00535 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00539 ^ 1)
theorem ha02352 : a02352.IsHomogeneous 18 := by
  unfold a02352
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00535.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00539.pow 1)))

@[irreducible]
def a02353 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00535 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00539 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02352 ^ 1)
theorem ha02353 : a02353.IsHomogeneous 18 := by
  unfold a02353
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00535.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00539.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02352.pow 1)))

@[irreducible]
def a02354 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02350 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02352 ^ 1)
theorem ha02354 : a02354.IsHomogeneous 46 := by
  unfold a02354
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02350.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02352.pow 1)))

@[irreducible]
def a02355 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02351 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02354 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02353 ^ 1)
theorem ha02355 : a02355.IsHomogeneous 46 := by
  unfold a02355
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02351.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02354.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02353.pow 1)))

@[irreducible]
def a02356 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a00613 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00535 ^ 1)
theorem ha02356 : a02356.IsHomogeneous 46 := by
  unfold a02356
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha00613.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00535.pow 1)))

@[irreducible]
def a02357 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02356 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02352 ^ 1)
theorem ha02357 : a02357.IsHomogeneous 46 := by
  unfold a02357
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02356.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02352.pow 1)))

@[irreducible]
def a02358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00007 ^ 1 * a00613 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02356 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00535 ^ 1)
theorem ha02358 : a02358.IsHomogeneous 46 := by
  unfold a02358
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00007.pow 1)).mul (ha00613.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02356.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00535.pow 1)))

@[irreducible]
def a02359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02357 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02358 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02353 ^ 1)
theorem ha02359 : a02359.IsHomogeneous 46 := by
  unfold a02359
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02357.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02358.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02353.pow 1)))

@[irreducible]
def a02360 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02354 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02357 ^ 1)
theorem ha02360 : a02360.IsHomogeneous 46 := by
  unfold a02360
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02354.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02357.pow 1)))

@[irreducible]
def a02361 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02355 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02359 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02360 ^ 1)
theorem ha02361 : a02361.IsHomogeneous 46 := by
  unfold a02361
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02355.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02359.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02360.pow 1)))

@[irreducible]
def a02362 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00156 ^ 1) + (C ((-1 : ℂ) / (24 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a00207 ^ 1)
theorem ha02362 : a02362.IsHomogeneous 24 := by
  unfold a02362
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00156.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00510.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a02363 : Poly := (C ((-7 : ℂ) / (48 : ℂ)) * a00014 ^ 1 * a00551 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02362 ^ 1)
theorem ha02363 : a02363.IsHomogeneous 24 := by
  unfold a02363
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (48 : ℂ))).mul (ha00014.pow 1)).mul (ha00551.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02362.pow 1)))

@[irreducible]
def a02364 : Poly := (C ((-7 : ℂ) / (48 : ℂ)) * a00014 ^ 1 * a00551 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02362 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a02363 ^ 1)
theorem ha02364 : a02364.IsHomogeneous 24 := by
  unfold a02364
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (48 : ℂ))).mul (ha00014.pow 1)).mul (ha00551.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02362.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha02363.pow 1)))

@[irreducible]
def a02365 : Poly := (C ((-7 : ℂ) / (144 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00627 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 1 * a02362 ^ 1)
theorem ha02365 : a02365.IsHomogeneous 37 := by
  unfold a02365
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (144 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00627.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha02362.pow 1)))

@[irreducible]
def a02366 : Poly := (C ((-7 : ℂ) / (72 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00627 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02365 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 1 * a02362 ^ 1)
theorem ha02366 : a02366.IsHomogeneous 37 := by
  unfold a02366
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (72 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00627.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02365.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha02362.pow 1)))

@[irreducible]
def a02367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a00551 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00627 ^ 1)
theorem ha02367 : a02367.IsHomogeneous 37 := by
  unfold a02367
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00551.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00627.pow 1)))

@[irreducible]
def a02368 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02367 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a00551 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00627 ^ 1)
theorem ha02368 : a02368.IsHomogeneous 37 := by
  unfold a02368
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02367.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00551.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00627.pow 1)))

@[irreducible]
def a02369 : Poly := (C ((-7 : ℂ) / (48 : ℂ)) * a02368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02366 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 1 * a02364 ^ 1)
theorem ha02369 : a02369.IsHomogeneous 37 := by
  unfold a02369
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (48 : ℂ))).mul (ha02368.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02366.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha02364.pow 1)))

@[irreducible]
def a02370 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a02361 ^ 1) + (C ((-2 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00004 ^ 2 * a00014 ^ 1 * a02369 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02349 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00003 ^ 4 * a00014 ^ 1 * a02340 ^ 1)
theorem ha02370 : a02370.IsHomogeneous 52 := by
  unfold a02370
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha02361.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00014.pow 1)).mul (ha02369.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02349.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 1)).mul (ha02340.pow 1)))

@[irreducible]
def a02371 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a00445 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01180 ^ 1)
theorem ha02371 : a02371.IsHomogeneous 236 := by
  unfold a02371
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha00445.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01180.pow 1)))

@[irreducible]
def a02372 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00211 ^ 1 * a00362 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00931 ^ 1)
theorem ha02372 : a02372.IsHomogeneous 187 := by
  unfold a02372
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)).mul (ha00362.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00931.pow 1)))

@[irreducible]
def a02373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00327 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00134 ^ 1 * a00188 ^ 1)
theorem ha02373 : a02373.IsHomogeneous 139 := by
  unfold a02373
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha00188.pow 1)))

@[irreducible]
def a02374 : Poly := (C ((-5 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a02372 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 2 * a02373 ^ 1) + (C ((25 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a02371 ^ 1)
theorem ha02374 : a02374.IsHomogeneous 238 := by
  unfold a02374
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha02372.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha02373.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha02371.pow 1)))

@[irreducible]
def a02375 : Poly := (C ((-1 : ℂ) / (48 : ℂ)) * a00000 ^ 1 * a00001 ^ 6 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 5 * a00100 ^ 4 * a02370 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02374 ^ 1)
theorem ha02375 : a02375.IsHomogeneous 238 := by
  unfold a02375
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (48 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 6)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 5)).mul (ha00100.pow 4)).mul (ha02370.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02374.pow 1)))

@[irreducible]
def a02376 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01026 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02375 ^ 1)
theorem ha02376 : a02376.IsHomogeneous 238 := by
  unfold a02376
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01026.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02375.pow 1)))

@[irreducible]
def a02377 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a02376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a01026 ^ 1)
theorem ha02377 : a02377.IsHomogeneous 796 := by
  unfold a02377
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha02376.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha01026.pow 1)))

@[irreducible]
def a02378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 2 * a02329 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 3 * a00126 ^ 1 * a02377 ^ 1)
theorem ha02378 : a02378.IsHomogeneous 938 := by
  unfold a02378
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 2)).mul (ha02329.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00126.pow 1)).mul (ha02377.pow 1)))

@[irreducible]
def a02379 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00364 ^ 1 * a01180 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00445 ^ 1 * a00935 ^ 1)
theorem ha02379 : a02379.IsHomogeneous 1329 := by
  unfold a02379
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00364.pow 1)).mul (ha01180.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00445.pow 1)).mul (ha00935.pow 1)))

@[irreducible]
def a02380 : Poly := (C ((-25 : ℂ) / (1728 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00012 ^ 2 * a00042 ^ 2 * a02379 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a02378 ^ 1)
theorem ha02380 : a02380.IsHomogeneous 1391 := by
  unfold a02380
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (1728 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 2)).mul (ha02379.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha02378.pow 1)))

@[irreducible]
def a02381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a00715 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a00261 ^ 1 * a01034 ^ 1)
theorem ha02381 : a02381.IsHomogeneous 577 := by
  unfold a02381
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha00715.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha00261.pow 1)).mul (ha01034.pow 1)))

@[irreducible]
def a02382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00367 ^ 1 * a00795 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a01033 ^ 1)
theorem ha02382 : a02382.IsHomogeneous 673 := by
  unfold a02382
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00367.pow 1)).mul (ha00795.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha01033.pow 1)))

@[irreducible]
def a02383 : Poly := (C ((-8 : ℂ) / (5 : ℂ)) * a00293 ^ 1 * a01029 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00365 ^ 1 * a00798 ^ 1)
theorem ha02383 : a02383.IsHomogeneous 141 := by
  unfold a02383
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (5 : ℂ))).mul (ha00293.pow 1)).mul (ha01029.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00365.pow 1)).mul (ha00798.pow 1)))

@[irreducible]
def a02384 : Poly := (C ((-5 : ℂ) / (864 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1 * a00691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a00014 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (240 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 1 * a00712 ^ 1)
theorem ha02384 : a02384.IsHomogeneous 70 := by
  unfold a02384
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (864 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00691.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00637.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (240 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00125 ^ 1 * a02384 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00293 ^ 1 * a01029 ^ 1)
theorem ha02385 : a02385.IsHomogeneous 141 := by
  unfold a02385
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00125.pow 1)).mul (ha02384.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00293.pow 1)).mul (ha01029.pow 1)))

@[irreducible]
def a02386 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a02385 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02383 ^ 1)
theorem ha02386 : a02386.IsHomogeneous 141 := by
  unfold a02386
  exact (((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha02385.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02383.pow 1)))

@[irreducible]
def a02387 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00261 ^ 1 * a01031 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00366 ^ 1 * a00713 ^ 1)
theorem ha02387 : a02387.IsHomogeneous 140 := by
  unfold a02387
  exact ((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00261.pow 1)).mul (ha01031.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00366.pow 1)).mul (ha00713.pow 1)))

@[irreducible]
def a02388 : Poly := (C ((-36 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00691 ^ 1)
theorem ha02388 : a02388.IsHomogeneous 59 := by
  unfold a02388
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a02389 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00101 ^ 1 * a02388 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00261 ^ 1 * a01031 ^ 1)
theorem ha02389 : a02389.IsHomogeneous 140 := by
  unfold a02389
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00101.pow 1)).mul (ha02388.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00261.pow 1)).mul (ha01031.pow 1)))

@[irreducible]
def a02390 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a02389 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02387 ^ 1)
theorem ha02390 : a02390.IsHomogeneous 140 := by
  unfold a02390
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha02389.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02387.pow 1)))

@[irreducible]
def a02391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02386 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00004 ^ 1 * a02390 ^ 1)
theorem ha02391 : a02391.IsHomogeneous 141 := by
  unfold a02391
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02386.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00004.pow 1)).mul (ha02390.pow 1)))

@[irreducible]
def a02392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a01033 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02391 ^ 1)
theorem ha02392 : a02392.IsHomogeneous 419 := by
  unfold a02392
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha01033.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02391.pow 1)))

@[irreducible]
def a02393 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02382 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02392 ^ 1)
theorem ha02393 : a02393.IsHomogeneous 673 := by
  unfold a02393
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02382.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02392.pow 1)))

@[irreducible]
def a02394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a01034 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a02393 ^ 1)
theorem ha02394 : a02394.IsHomogeneous 752 := by
  unfold a02394
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha01034.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha02393.pow 1)))

@[irreducible]
def a02395 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02381 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00101 ^ 1 * a02394 ^ 1)
theorem ha02395 : a02395.IsHomogeneous 831 := by
  unfold a02395
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02381.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00101.pow 1)).mul (ha02394.pow 1)))

@[irreducible]
def a02396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a01035 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02395 ^ 1)
theorem ha02396 : a02396.IsHomogeneous 939 := by
  unfold a02396
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha01035.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02395.pow 1)))

@[irreducible]
def a02397 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a00836 ^ 1)
theorem ha02397 : a02397.IsHomogeneous 696 := by
  unfold a02397
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha00836.pow 1)))

@[irreducible]
def a02398 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a02396 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02397 ^ 1)
theorem ha02398 : a02398.IsHomogeneous 1029 := by
  unfold a02398
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02396.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02397.pow 1)))

@[irreducible]
def a02399 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a01035 ^ 1)
theorem ha02399 : a02399.IsHomogeneous 915 := by
  unfold a02399
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha01035.pow 1)))

@[irreducible]
def a02400 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a00850 ^ 1)
theorem ha02400 : a02400.IsHomogeneous 648 := by
  unfold a02400
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha00850.pow 1)))

@[irreducible]
def a02401 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a02399 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02400 ^ 1)
theorem ha02401 : a02401.IsHomogeneous 981 := by
  unfold a02401
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02399.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02400.pow 1)))

@[irreducible]
def a02402 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a00492 ^ 1)
theorem ha02402 : a02402.IsHomogeneous 1047 := by
  unfold a02402
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha00492.pow 1)))

@[irreducible]
def a02403 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a00492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a01290 ^ 1)
theorem ha02403 : a02403.IsHomogeneous 774 := by
  unfold a02403
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha00492.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a02404 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a02402 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02403 ^ 1)
theorem ha02404 : a02404.IsHomogeneous 1107 := by
  unfold a02404
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha02402.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02403.pow 1)))

@[irreducible]
def a02405 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a01196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00452 ^ 1 * a00501 ^ 1)
theorem ha02405 : a02405.IsHomogeneous 987 := by
  unfold a02405
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha01196.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00452.pow 1)).mul (ha00501.pow 1)))

@[irreducible]
def a02406 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a00501 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a01313 ^ 1)
theorem ha02406 : a02406.IsHomogeneous 690 := by
  unfold a02406
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha00501.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha01313.pow 1)))

@[irreducible]
def a02407 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a02405 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02406 ^ 1)
theorem ha02407 : a02407.IsHomogeneous 1023 := by
  unfold a02407
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha02405.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02406.pow 1)))

@[irreducible]
def a02408 : Poly := (C ((-16 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a00804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a01103 ^ 1)
theorem ha02408 : a02408.IsHomogeneous 1102 := by
  unfold a02408
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha00804.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a02409 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00398 ^ 1 * a00834 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a01102 ^ 1)
theorem ha02409 : a02409.IsHomogeneous 367 := by
  unfold a02409
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00398.pow 1)).mul (ha00834.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha01102.pow 1)))

@[irreducible]
def a02410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1)
theorem ha02410 : a02410.IsHomogeneous 18 := by
  unfold a02410
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a02411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha02411 : a02411.IsHomogeneous 12 := by
  unfold a02411
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a02412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02411 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02410 ^ 1)
theorem ha02412 : a02412.IsHomogeneous 18 := by
  unfold a02412
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02411.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02410.pow 1)))

@[irreducible]
def a02413 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a02412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00570 ^ 1)
theorem ha02413 : a02413.IsHomogeneous 18 := by
  unfold a02413
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha02412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00570.pow 1)))

@[irreducible]
def a02414 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02413 ^ 1)
theorem ha02414 : a02414.IsHomogeneous 126 := by
  unfold a02414
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha01041.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a02415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1 * a01041 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00368 ^ 1 * a00823 ^ 1)
theorem ha02415 : a02415.IsHomogeneous 126 := by
  unfold a02415
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00368.pow 1)).mul (ha00823.pow 1)))

@[irreducible]
def a02416 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a02415 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02414 ^ 1)
theorem ha02416 : a02416.IsHomogeneous 126 := by
  unfold a02416
  exact (((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha02415.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02414.pow 1)))

@[irreducible]
def a02417 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00148 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1 * a00480 ^ 1)
theorem ha02417 : a02417.IsHomogeneous 151 := by
  unfold a02417
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00148.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).mul (ha00480.pow 1)))

@[irreducible]
def a02418 : Poly := (C ((-9 : ℂ) / (5 : ℂ)) * a00455 ^ 1 * a00480 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a01264 ^ 1)
theorem ha02418 : a02418.IsHomogeneous 151 := by
  unfold a02418
  exact ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (5 : ℂ))).mul (ha00455.pow 1)).mul (ha00480.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha01264.pow 1)))

@[irreducible]
def a02419 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a02418 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02417 ^ 1)
theorem ha02419 : a02419.IsHomogeneous 151 := by
  unfold a02419
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha02418.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02417.pow 1)))

@[irreducible]
def a02420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02419 ^ 1) + (C ((4 : ℂ) / (2025 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a00014 ^ 2 * a02416 ^ 1)
theorem ha02420 : a02420.IsHomogeneous 151 := by
  unfold a02420
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02419.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (2025 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha02416.pow 1)))

@[irreducible]
def a02421 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00389 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a01083 ^ 1)
theorem ha02421 : a02421.IsHomogeneous 180 := by
  unfold a02421
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00389.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha01083.pow 1)))

@[irreducible]
def a02422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a01045 ^ 1)
theorem ha02422 : a02422.IsHomogeneous 30 := by
  unfold a02422
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha01045.pow 1)))

@[irreducible]
def a02423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00316 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1)
theorem ha02423 : a02423.IsHomogeneous 30 := by
  unfold a02423
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a02424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1)
theorem ha02424 : a02424.IsHomogeneous 27 := by
  unfold a02424
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)))

@[irreducible]
def a02425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a02423 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02424 ^ 1)
theorem ha02425 : a02425.IsHomogeneous 33 := by
  unfold a02425
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha02423.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02424.pow 1)))

@[irreducible]
def a02426 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a02425 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a01045 ^ 1)
theorem ha02426 : a02426.IsHomogeneous 39 := by
  unfold a02426
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha02425.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha01045.pow 1)))

@[irreducible]
def a02427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02426 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02422 ^ 1)
theorem ha02427 : a02427.IsHomogeneous 39 := by
  unfold a02427
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02426.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02422.pow 1)))

@[irreducible]
def a02428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00130 ^ 1)
theorem ha02428 : a02428.IsHomogeneous 18 := by
  unfold a02428
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a02429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00133 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00133 ^ 1)
theorem ha02429 : a02429.IsHomogeneous 18 := by
  unfold a02429
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a02430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00032 ^ 1 * a00316 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00133 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00130 ^ 1)
theorem ha02430 : a02430.IsHomogeneous 18 := by
  unfold a02430
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a02431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02428 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a02429 ^ 1) + (C ((15 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a02430 ^ 1)
theorem ha02431 : a02431.IsHomogeneous 24 := by
  unfold a02431
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02428.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha02429.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha02430.pow 1)))

@[irreducible]
def a02432 : Poly := (C ((-1 : ℂ) / (540 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a02431 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02427 ^ 1)
theorem ha02432 : a02432.IsHomogeneous 39 := by
  unfold a02432
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (540 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha02431.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02427.pow 1)))

@[irreducible]
def a02433 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00100 ^ 1 * a02432 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01048 ^ 1)
theorem ha02433 : a02433.IsHomogeneous 75 := by
  unfold a02433
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00100.pow 1)).mul (ha02432.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01048.pow 1)))

@[irreducible]
def a02434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00260 ^ 1 * a01048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00370 ^ 1 * a00829 ^ 1)
theorem ha02434 : a02434.IsHomogeneous 114 := by
  unfold a02434
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01048.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00370.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a02435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a02433 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02434 ^ 1)
theorem ha02435 : a02435.IsHomogeneous 114 := by
  unfold a02435
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha02433.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02434.pow 1)))

@[irreducible]
def a02436 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a01223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00459 ^ 1 * a00484 ^ 1)
theorem ha02436 : a02436.IsHomogeneous 136 := by
  unfold a02436
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha01223.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00459.pow 1)).mul (ha00484.pow 1)))

@[irreducible]
def a02437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00459 ^ 1 * a00484 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00137 ^ 1 * a01275 ^ 1)
theorem ha02437 : a02437.IsHomogeneous 145 := by
  unfold a02437
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00459.pow 1)).mul (ha00484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00137.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a02438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02436 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02437 ^ 1)
theorem ha02438 : a02438.IsHomogeneous 145 := by
  unfold a02438
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02436.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02437.pow 1)))

@[irreducible]
def a02439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02438 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a02435 ^ 1)
theorem ha02439 : a02439.IsHomogeneous 145 := by
  unfold a02439
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02438.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha02435.pow 1)))

@[irreducible]
def a02440 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a01081 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00388 ^ 1)
theorem ha02440 : a02440.IsHomogeneous 132 := by
  unfold a02440
  exact (((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha01081.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00388.pow 1)))

@[irreducible]
def a02441 : Poly := (C ((-7 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00006 ^ 1 * a00321 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00782 ^ 1)
theorem ha02441 : a02441.IsHomogeneous 17 := by
  unfold a02441
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00006.pow 1)).mul (ha00321.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00782.pow 1)))

@[irreducible]
def a02442 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a02441 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00301 ^ 1 * a01052 ^ 1)
theorem ha02442 : a02442.IsHomogeneous 113 := by
  unfold a02442
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha02441.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00301.pow 1)).mul (ha01052.pow 1)))

@[irreducible]
def a02443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00301 ^ 1 * a01052 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a00819 ^ 1)
theorem ha02443 : a02443.IsHomogeneous 121 := by
  unfold a02443
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00301.pow 1)).mul (ha01052.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha00819.pow 1)))

@[irreducible]
def a02444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a02442 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02443 ^ 1)
theorem ha02444 : a02444.IsHomogeneous 121 := by
  unfold a02444
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha02442.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02443.pow 1)))

@[irreducible]
def a02445 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00146 ^ 1 * a01228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a00476 ^ 1)
theorem ha02445 : a02445.IsHomogeneous 118 := by
  unfold a02445
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha01228.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha00476.pow 1)))

@[irreducible]
def a02446 : Poly := (C ((-5 : ℂ) / (12 : ℂ)) * a00138 ^ 1 * a01258 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00461 ^ 1 * a00476 ^ 1)
theorem ha02446 : a02446.IsHomogeneous 127 := by
  unfold a02446
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (12 : ℂ))).mul (ha00138.pow 1)).mul (ha01258.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha00476.pow 1)))

@[irreducible]
def a02447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02445 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02446 ^ 1)
theorem ha02447 : a02447.IsHomogeneous 127 := by
  unfold a02447
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02445.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02446.pow 1)))

@[irreducible]
def a02448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02444 ^ 1) + (C ((50 : ℂ) / (3 : ℂ)) * a02447 ^ 1)
theorem ha02448 : a02448.IsHomogeneous 127 := by
  unfold a02448
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02444.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((50 : ℂ) / (3 : ℂ))).mul (ha02447.pow 1)))

@[irreducible]
def a02449 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00387 ^ 1 * a00812 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a01079 ^ 1)
theorem ha02449 : a02449.IsHomogeneous 117 := by
  unfold a02449
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00387.pow 1)).mul (ha00812.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha01079.pow 1)))

@[irreducible]
def a02450 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00375 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01060 ^ 1)
theorem ha02450 : a02450.IsHomogeneous 85 := by
  unfold a02450
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00375.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01060.pow 1)))

@[irreducible]
def a02451 : Poly := (C ((-5 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01041 ^ 1)
theorem ha02451 : a02451.IsHomogeneous 33 := by
  unfold a02451
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00368.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a02452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02413 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01041 ^ 1)
theorem ha02452 : a02452.IsHomogeneous 42 := by
  unfold a02452
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02413.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a02453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02452 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02451 ^ 1)
theorem ha02453 : a02453.IsHomogeneous 42 := by
  unfold a02453
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02452.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02451.pow 1)))

@[irreducible]
def a02454 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00455 ^ 1)
theorem ha02454 : a02454.IsHomogeneous 12 := by
  unfold a02454
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00455.pow 1)))

@[irreducible]
def a02455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00455 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a01207 ^ 1)
theorem ha02455 : a02455.IsHomogeneous 12 := by
  unfold a02455
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00455.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha01207.pow 1)))

@[irreducible]
def a02456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02454 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a02455 ^ 1)
theorem ha02456 : a02456.IsHomogeneous 12 := by
  unfold a02456
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02454.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha02455.pow 1)))

@[irreducible]
def a02457 : Poly := (C ((-16 : ℂ) / (405 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a02453 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a02456 ^ 1)
theorem ha02457 : a02457.IsHomogeneous 47 := by
  unfold a02457
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (405 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha02453.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha02456.pow 1)))

@[irreducible]
def a02458 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00298 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00126 ^ 1 * a00506 ^ 1)
theorem ha02458 : a02458.IsHomogeneous 42 := by
  unfold a02458
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00126.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a02459 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00298 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1)
theorem ha02459 : a02459.IsHomogeneous 36 := by
  unfold a02459
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a02460 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02459 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02458 ^ 1)
theorem ha02460 : a02460.IsHomogeneous 42 := by
  unfold a02460
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02459.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02458.pow 1)))

@[irreducible]
def a02461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02457 ^ 1) + (C ((8 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a02460 ^ 1)
theorem ha02461 : a02461.IsHomogeneous 47 := by
  unfold a02461
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02457.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha02460.pow 1)))

@[irreducible]
def a02462 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a01060 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a02461 ^ 1)
theorem ha02462 : a02462.IsHomogeneous 85 := by
  unfold a02462
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha01060.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha02461.pow 1)))

@[irreducible]
def a02463 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a02462 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02450 ^ 1)
theorem ha02463 : a02463.IsHomogeneous 85 := by
  unfold a02463
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha02462.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02450.pow 1)))

@[irreducible]
def a02464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00139 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a00465 ^ 1)
theorem ha02464 : a02464.IsHomogeneous 85 := by
  unfold a02464
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00139.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha00465.pow 1)))

@[irreducible]
def a02465 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00465 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00082 ^ 1 * a01240 ^ 1)
theorem ha02465 : a02465.IsHomogeneous 85 := by
  unfold a02465
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00465.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00082.pow 1)).mul (ha01240.pow 1)))

@[irreducible]
def a02466 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a02465 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02464 ^ 1)
theorem ha02466 : a02466.IsHomogeneous 85 := by
  unfold a02466
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha02465.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02464.pow 1)))

@[irreducible]
def a02467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02463 ^ 1) + (C ((25 : ℂ) / (54 : ℂ)) * a02466 ^ 1)
theorem ha02467 : a02467.IsHomogeneous 85 := by
  unfold a02467
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (54 : ℂ))).mul (ha02466.pow 1)))

@[irreducible]
def a02468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00042 ^ 1 * a00126 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00211 ^ 1 * a00300 ^ 1)
theorem ha02468 : a02468.IsHomogeneous 108 := by
  unfold a02468
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00637.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00211.pow 1)).mul (ha00300.pow 1)))

@[irreducible]
def a02469 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00211 ^ 1 * a00300 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00061 ^ 1 * a00817 ^ 1)
theorem ha02469 : a02469.IsHomogeneous 102 := by
  unfold a02469
  exact ((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00211.pow 1)).mul (ha00300.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00061.pow 1)).mul (ha00817.pow 1)))

@[irreducible]
def a02470 : Poly := (C ((-5 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a02469 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02468 ^ 1)
theorem ha02470 : a02470.IsHomogeneous 108 := by
  unfold a02470
  exact ((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha02469.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02468.pow 1)))

@[irreducible]
def a02471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02470 ^ 1) + (C ((9 : ℂ) / (320 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02467 ^ 1)
theorem ha02471 : a02471.IsHomogeneous 108 := by
  unfold a02471
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02470.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (320 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02467.pow 1)))

@[irreducible]
def a02472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00379 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01067 ^ 1)
theorem ha02472 : a02472.IsHomogeneous 85 := by
  unfold a02472
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00379.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01067.pow 1)))

@[irreducible]
def a02473 : Poly := (C ((-4 : ℂ) / (45 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a02453 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a02456 ^ 1)
theorem ha02473 : a02473.IsHomogeneous 47 := by
  unfold a02473
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (45 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha02453.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha02456.pow 1)))

@[irreducible]
def a02474 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02473 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a02460 ^ 1)
theorem ha02474 : a02474.IsHomogeneous 47 := by
  unfold a02474
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02473.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha02460.pow 1)))

@[irreducible]
def a02475 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a01067 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a02474 ^ 1)
theorem ha02475 : a02475.IsHomogeneous 85 := by
  unfold a02475
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha01067.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha02474.pow 1)))

@[irreducible]
def a02476 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a02475 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02472 ^ 1)
theorem ha02476 : a02476.IsHomogeneous 85 := by
  unfold a02476
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha02475.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02472.pow 1)))

@[irreducible]
def a02477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00141 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a00469 ^ 1)
theorem ha02477 : a02477.IsHomogeneous 85 := by
  unfold a02477
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00141.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha00469.pow 1)))

@[irreducible]
def a02478 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00469 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00082 ^ 1 * a01248 ^ 1)
theorem ha02478 : a02478.IsHomogeneous 85 := by
  unfold a02478
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00469.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00082.pow 1)).mul (ha01248.pow 1)))

@[irreducible]
def a02479 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a02478 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02477 ^ 1)
theorem ha02479 : a02479.IsHomogeneous 85 := by
  unfold a02479
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha02478.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02477.pow 1)))

@[irreducible]
def a02480 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02476 ^ 1) + (C ((25 : ℂ) / (36 : ℂ)) * a02479 ^ 1)
theorem ha02480 : a02480.IsHomogeneous 85 := by
  unfold a02480
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02476.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (36 : ℂ))).mul (ha02479.pow 1)))

@[irreducible]
def a02481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02470 ^ 1) + (C ((1 : ℂ) / (40 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02480 ^ 1)
theorem ha02481 : a02481.IsHomogeneous 108 := by
  unfold a02481
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02470.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (40 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02480.pow 1)))

@[irreducible]
def a02482 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a02481 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02471 ^ 1)
theorem ha02482 : a02482.IsHomogeneous 108 := by
  unfold a02482
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha02481.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02471.pow 1)))

@[irreducible]
def a02483 : Poly := (C ((-8 : ℂ) / (135 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a02453 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a02456 ^ 1)
theorem ha02483 : a02483.IsHomogeneous 47 := by
  unfold a02483
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (135 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha02453.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha02456.pow 1)))

@[irreducible]
def a02484 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02483 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a02460 ^ 1)
theorem ha02484 : a02484.IsHomogeneous 47 := by
  unfold a02484
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02483.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha02460.pow 1)))

@[irreducible]
def a02485 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a01074 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a02484 ^ 1)
theorem ha02485 : a02485.IsHomogeneous 85 := by
  unfold a02485
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha01074.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha02484.pow 1)))

@[irreducible]
def a02486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00384 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01074 ^ 1)
theorem ha02486 : a02486.IsHomogeneous 85 := by
  unfold a02486
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00384.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01074.pow 1)))

@[irreducible]
def a02487 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a02486 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02485 ^ 1)
theorem ha02487 : a02487.IsHomogeneous 85 := by
  unfold a02487
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha02486.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02485.pow 1)))

@[irreducible]
def a02488 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00473 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00082 ^ 1 * a01253 ^ 1)
theorem ha02488 : a02488.IsHomogeneous 85 := by
  unfold a02488
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00473.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00082.pow 1)).mul (ha01253.pow 1)))

@[irreducible]
def a02489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00144 ^ 1 * a00691 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a00473 ^ 1)
theorem ha02489 : a02489.IsHomogeneous 85 := by
  unfold a02489
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00144.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha00473.pow 1)))

@[irreducible]
def a02490 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a02489 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02488 ^ 1)
theorem ha02490 : a02490.IsHomogeneous 85 := by
  unfold a02490
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha02489.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02488.pow 1)))

@[irreducible]
def a02491 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02487 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a02490 ^ 1)
theorem ha02491 : a02491.IsHomogeneous 85 := by
  unfold a02491
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02487.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha02490.pow 1)))

@[irreducible]
def a02492 : Poly := (C ((-5 : ℂ) / (288 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a02491 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02470 ^ 1)
theorem ha02492 : a02492.IsHomogeneous 108 := by
  unfold a02492
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (288 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha02491.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02470.pow 1)))

@[irreducible]
def a02493 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a02492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02482 ^ 1)
theorem ha02493 : a02493.IsHomogeneous 108 := by
  unfold a02493
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha02492.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02482.pow 1)))

@[irreducible]
def a02494 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a01079 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00127 ^ 1 * a02493 ^ 1)
theorem ha02494 : a02494.IsHomogeneous 126 := by
  unfold a02494
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha01079.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00127.pow 1)).mul (ha02493.pow 1)))

@[irreducible]
def a02495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02449 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02494 ^ 1)
theorem ha02495 : a02495.IsHomogeneous 126 := by
  unfold a02495
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02449.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02494.pow 1)))

@[irreducible]
def a02496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a02495 ^ 1) + (C ((3 : ℂ) / (400 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a02448 ^ 1)
theorem ha02496 : a02496.IsHomogeneous 138 := by
  unfold a02496
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha02495.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (400 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha02448.pow 1)))

@[irreducible]
def a02497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01081 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a02496 ^ 1)
theorem ha02497 : a02497.IsHomogeneous 138 := by
  unfold a02497
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01081.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha02496.pow 1)))

@[irreducible]
def a02498 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a02497 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a02440 ^ 1)
theorem ha02498 : a02498.IsHomogeneous 138 := by
  unfold a02498
  exact (((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha02497.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha02440.pow 1)))

@[irreducible]
def a02499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 3 * a02498 ^ 1) + (C ((27 : ℂ) / (4000 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a02439 ^ 1)
theorem ha02499 : a02499.IsHomogeneous 156 := by
  unfold a02499
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 3)).mul (ha02498.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (4000 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha02439.pow 1)))

@[irreducible]
def a02500 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a01083 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a02499 ^ 1)
theorem ha02500 : a02500.IsHomogeneous 186 := by
  unfold a02500
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha01083.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha02499.pow 1)))

@[irreducible]
def a02501 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a02421 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02500 ^ 1)
theorem ha02501 : a02501.IsHomogeneous 186 := by
  unfold a02501
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha02421.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02500.pow 1)))

@[irreducible]
def a02502 : Poly := (C ((-3 : ℂ) / (80 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a02420 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02501 ^ 1)
theorem ha02502 : a02502.IsHomogeneous 186 := by
  unfold a02502
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (80 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha02420.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02501.pow 1)))

@[irreducible]
def a02503 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a01284 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00489 ^ 1 * a00492 ^ 1)
theorem ha02503 : a02503.IsHomogeneous 338 := by
  unfold a02503
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha01284.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00489.pow 1)).mul (ha00492.pow 1)))

@[irreducible]
def a02504 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00489 ^ 1 * a00492 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a01290 ^ 1)
theorem ha02504 : a02504.IsHomogeneous 362 := by
  unfold a02504
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00489.pow 1)).mul (ha00492.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha01290.pow 1)))

@[irreducible]
def a02505 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a02503 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02504 ^ 1)
theorem ha02505 : a02505.IsHomogeneous 362 := by
  unfold a02505
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha02503.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02504.pow 1)))

@[irreducible]
def a02506 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00260 ^ 1)
theorem ha02506 : a02506.IsHomogeneous 48 := by
  unfold a02506
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a02507 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00100 ^ 1 * a00155 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00831 ^ 1)
theorem ha02507 : a02507.IsHomogeneous 84 := by
  unfold a02507
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00100.pow 1)).mul (ha00155.pow 1)).mul (ha00260.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00831.pow 1)))

@[irreducible]
def a02508 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00100 ^ 1 * a02506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02507 ^ 1)
theorem ha02508 : a02508.IsHomogeneous 84 := by
  unfold a02508
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00100.pow 1)).mul (ha02506.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02507.pow 1)))

@[irreducible]
def a02509 : Poly := (C ((-12 : ℂ) / (5 : ℂ)) * a00487 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00100 ^ 1 * a00316 ^ 1)
theorem ha02509 : a02509.IsHomogeneous 85 := by
  unfold a02509
  exact (((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (5 : ℂ))).mul (ha00487.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a02510 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00100 ^ 1 * a00487 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01281 ^ 1)
theorem ha02510 : a02510.IsHomogeneous 127 := by
  unfold a02510
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00100.pow 1)).mul (ha00487.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01281.pow 1)))

@[irreducible]
def a02511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02510 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00100 ^ 1 * a02509 ^ 1)
theorem ha02511 : a02511.IsHomogeneous 127 := by
  unfold a02511
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02510.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00100.pow 1)).mul (ha02509.pow 1)))

@[irreducible]
def a02512 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02511 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00100 ^ 1 * a02508 ^ 1)
theorem ha02512 : a02512.IsHomogeneous 127 := by
  unfold a02512
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02511.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha02508.pow 1)))

@[irreducible]
def a02513 : Poly := (C ((-5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00317 ^ 1 * a00395 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01097 ^ 1)
theorem ha02513 : a02513.IsHomogeneous 154 := by
  unfold a02513
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00317.pow 1)).mul (ha00395.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01097.pow 1)))

@[irreducible]
def a02514 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00393 ^ 1 * a00712 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01092 ^ 1)
theorem ha02514 : a02514.IsHomogeneous 139 := by
  unfold a02514
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00393.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01092.pow 1)))

@[irreducible]
def a02515 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00637 ^ 1)
theorem ha02515 : a02515.IsHomogeneous 90 := by
  unfold a02515
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00260.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00637.pow 1)))

@[irreducible]
def a02516 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00211 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00061 ^ 1 * a00712 ^ 1)
theorem ha02516 : a02516.IsHomogeneous 90 := by
  unfold a02516
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00211.pow 1)).mul (ha00260.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00061.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a02517 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02515 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a02516 ^ 1)
theorem ha02517 : a02517.IsHomogeneous 90 := by
  unfold a02517
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02515.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha02516.pow 1)))

@[irreducible]
def a02518 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a00691 ^ 1)
theorem ha02518 : a02518.IsHomogeneous 98 := by
  unfold a02518
  exact (((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a02519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a02518 ^ 1) + (C ((432 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02517 ^ 1)
theorem ha02519 : a02519.IsHomogeneous 103 := by
  unfold a02519
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02518.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((432 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02517.pow 1)))

@[irreducible]
def a02520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02519 ^ 1) + (C ((432 : ℂ) / (25 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02517 ^ 1)
theorem ha02520 : a02520.IsHomogeneous 103 := by
  unfold a02520
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02519.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((432 : ℂ) / (25 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02517.pow 1)))

@[irreducible]
def a02521 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00260 ^ 1 * a01092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02520 ^ 1)
theorem ha02521 : a02521.IsHomogeneous 139 := by
  unfold a02521
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00260.pow 1)).mul (ha01092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02520.pow 1)))

@[irreducible]
def a02522 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a02521 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02514 ^ 1)
theorem ha02522 : a02522.IsHomogeneous 139 := by
  unfold a02522
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha02521.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02514.pow 1)))

@[irreducible]
def a02523 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a00003 ^ 2 * a00082 ^ 1 * a00100 ^ 1 * a00691 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00484 ^ 1)
theorem ha02523 : a02523.IsHomogeneous 134 := by
  unfold a02523
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 2)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00691.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00484.pow 1)))

@[irreducible]
def a02524 : Poly := (C ((-18 : ℂ) / (5 : ℂ)) * a00241 ^ 1 * a00484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a01275 ^ 1)
theorem ha02524 : a02524.IsHomogeneous 134 := by
  unfold a02524
  exact ((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (5 : ℂ))).mul (ha00241.pow 1)).mul (ha00484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha01275.pow 1)))

@[irreducible]
def a02525 : Poly := (C ((-5 : ℂ) / (18 : ℂ)) * a02524 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02523 ^ 1)
theorem ha02525 : a02525.IsHomogeneous 134 := by
  unfold a02525
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (18 : ℂ))).mul (ha02524.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02523.pow 1)))

@[irreducible]
def a02526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a02525 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02522 ^ 1)
theorem ha02526 : a02526.IsHomogeneous 139 := by
  unfold a02526
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02525.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02522.pow 1)))

@[irreducible]
def a02527 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00637 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00211 ^ 1 * a00260 ^ 1)
theorem ha02527 : a02527.IsHomogeneous 90 := by
  unfold a02527
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00637.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00211.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a02528 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00211 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00829 ^ 1)
theorem ha02528 : a02528.IsHomogeneous 126 := by
  unfold a02528
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00211.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a02529 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a02528 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a02527 ^ 1)
theorem ha02529 : a02529.IsHomogeneous 126 := by
  unfold a02529
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha02528.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha02527.pow 1)))

@[irreducible]
def a02530 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02526 ^ 1) + (C ((48 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02529 ^ 1)
theorem ha02530 : a02530.IsHomogeneous 139 := by
  unfold a02530
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02526.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((48 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02529.pow 1)))

@[irreducible]
def a02531 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01097 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02530 ^ 1)
theorem ha02531 : a02531.IsHomogeneous 163 := by
  unfold a02531
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01097.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02530.pow 1)))

@[irreducible]
def a02532 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02513 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02531 ^ 1)
theorem ha02532 : a02532.IsHomogeneous 163 := by
  unfold a02532
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02513.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02531.pow 1)))

@[irreducible]
def a02533 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02532 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a02512 ^ 1)
theorem ha02533 : a02533.IsHomogeneous 163 := by
  unfold a02533
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02532.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha02512.pow 1)))

@[irreducible]
def a02534 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a02533 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00306 ^ 1 * a01099 ^ 1)
theorem ha02534 : a02534.IsHomogeneous 271 := by
  unfold a02534
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha02533.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00306.pow 1)).mul (ha01099.pow 1)))

@[irreducible]
def a02535 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00306 ^ 1 * a01099 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00396 ^ 1 * a00836 ^ 1)
theorem ha02535 : a02535.IsHomogeneous 325 := by
  unfold a02535
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00306.pow 1)).mul (ha01099.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00396.pow 1)).mul (ha00836.pow 1)))

@[irreducible]
def a02536 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a02534 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02535 ^ 1)
theorem ha02536 : a02536.IsHomogeneous 325 := by
  unfold a02536
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha02534.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02535.pow 1)))

@[irreducible]
def a02537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a02536 ^ 1) + (C ((54 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a02505 ^ 1)
theorem ha02537 : a02537.IsHomogeneous 367 := by
  unfold a02537
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha02536.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha02505.pow 1)))

@[irreducible]
def a02538 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02537 ^ 1) + (C ((80 : ℂ) / (3 : ℂ)) * a00001 ^ 1 * a00042 ^ 3 * a00100 ^ 3 * a02502 ^ 1)
theorem ha02538 : a02538.IsHomogeneous 367 := by
  unfold a02538
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02537.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((80 : ℂ) / (3 : ℂ))).mul (ha00001.pow 1)).mul (ha00042.pow 3)).mul (ha00100.pow 3)).mul (ha02502.pow 1)))

@[irreducible]
def a02539 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a01102 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02538 ^ 1)
theorem ha02539 : a02539.IsHomogeneous 367 := by
  unfold a02539
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha01102.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02538.pow 1)))

@[irreducible]
def a02540 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02409 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02539 ^ 1)
theorem ha02540 : a02540.IsHomogeneous 367 := by
  unfold a02540
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02409.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02539.pow 1)))

@[irreducible]
def a02541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a02540 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a01103 ^ 1)
theorem ha02541 : a02541.IsHomogeneous 793 := by
  unfold a02541
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha02540.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a02542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02541 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a02408 ^ 1)
theorem ha02542 : a02542.IsHomogeneous 1126 := by
  unfold a02542
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02541.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha02408.pow 1)))

@[irreducible]
def a02543 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a00804 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a01118 ^ 1)
theorem ha02543 : a02543.IsHomogeneous 1018 := by
  unfold a02543
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha00804.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha01118.pow 1)))

@[irreducible]
def a02544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01117 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00404 ^ 1 * a00848 ^ 1)
theorem ha02544 : a02544.IsHomogeneous 259 := by
  unfold a02544
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01117.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00404.pow 1)).mul (ha00848.pow 1)))

@[irreducible]
def a02545 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a01107 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00014 ^ 1 * a00400 ^ 1 * a00812 ^ 1)
theorem ha02545 : a02545.IsHomogeneous 64 := by
  unfold a02545
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha01107.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00014.pow 1)).mul (ha00400.pow 1)).mul (ha00812.pow 1)))

@[irreducible]
def a02546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a01041 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00126 ^ 1 * a02413 ^ 1)
theorem ha02546 : a02546.IsHomogeneous 48 := by
  unfold a02546
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha01041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00126.pow 1)).mul (ha02413.pow 1)))

@[irreducible]
def a02547 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00368 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a01041 ^ 1)
theorem ha02547 : a02547.IsHomogeneous 42 := by
  unfold a02547
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00368.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a02548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a02547 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02546 ^ 1)
theorem ha02548 : a02548.IsHomogeneous 48 := by
  unfold a02548
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha02547.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02546.pow 1)))

@[irreducible]
def a02549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01207 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00455 ^ 2)
theorem ha02549 : a02549.IsHomogeneous 24 := by
  unfold a02549
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01207.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00455.pow 2)))

@[irreducible]
def a02550 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a02548 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a02549 ^ 1)
theorem ha02550 : a02550.IsHomogeneous 55 := by
  unfold a02550
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha02548.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha02549.pow 1)))

@[irreducible]
def a02551 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a02548 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02550 ^ 1)
theorem ha02551 : a02551.IsHomogeneous 55 := by
  unfold a02551
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha02548.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02550.pow 1)))

@[irreducible]
def a02552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00299 ^ 1 * a01107 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00127 ^ 1 * a02551 ^ 1)
theorem ha02552 : a02552.IsHomogeneous 73 := by
  unfold a02552
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00299.pow 1)).mul (ha01107.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00127.pow 1)).mul (ha02551.pow 1)))

@[irreducible]
def a02553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02545 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02552 ^ 1)
theorem ha02553 : a02553.IsHomogeneous 73 := by
  unfold a02553
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02545.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02552.pow 1)))

@[irreducible]
def a02554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00461 ^ 1 * a00494 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a01228 ^ 1)
theorem ha02554 : a02554.IsHomogeneous 57 := by
  unfold a02554
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00461.pow 1)).mul (ha00494.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha01228.pow 1)))

@[irreducible]
def a02555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00461 ^ 1 * a00494 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00138 ^ 1 * a01298 ^ 1)
theorem ha02555 : a02555.IsHomogeneous 66 := by
  unfold a02555
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00461.pow 1)).mul (ha00494.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00138.pow 1)).mul (ha01298.pow 1)))

@[irreducible]
def a02556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a02554 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02555 ^ 1)
theorem ha02556 : a02556.IsHomogeneous 66 := by
  unfold a02556
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha02554.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02555.pow 1)))

@[irreducible]
def a02557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a02553 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a02556 ^ 1)
theorem ha02557 : a02557.IsHomogeneous 79 := by
  unfold a02557
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha02553.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha02556.pow 1)))

@[irreducible]
def a02558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a01052 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00126 ^ 1 * a02441 ^ 1)
theorem ha02558 : a02558.IsHomogeneous 47 := by
  unfold a02558
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha01052.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00126.pow 1)).mul (ha02441.pow 1)))

@[irreducible]
def a02559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00126 ^ 1 * a00298 ^ 1 * a01052 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00372 ^ 1 * a00841 ^ 1)
theorem ha02559 : a02559.IsHomogeneous 79 := by
  unfold a02559
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha01052.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00372.pow 1)).mul (ha00841.pow 1)))

end CycleQ2Concrete
