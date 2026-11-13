import Proposal.CurrentAtoms005

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a03072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03068 ^ 1)
theorem ha03072 : a03072.IsHomogeneous 12 := by
  unfold a03072
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03068.pow 1)))

@[irreducible]
def a03073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03070 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03072 ^ 1)
theorem ha03073 : a03073.IsHomogeneous 12 := by
  unfold a03073
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03070.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03072.pow 1)))

@[irreducible]
def a03074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a02935 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a01327 ^ 1)
theorem ha03074 : a03074.IsHomogeneous 12 := by
  unfold a03074
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha01327.pow 1)))

@[irreducible]
def a03075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03069 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a03074 ^ 1)
theorem ha03075 : a03075.IsHomogeneous 12 := by
  unfold a03075
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03069.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha03074.pow 1)))

@[irreducible]
def a03076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03070 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03075 ^ 1)
theorem ha03076 : a03076.IsHomogeneous 12 := by
  unfold a03076
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03070.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03075.pow 1)))

@[irreducible]
def a03077 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03076 ^ 1)
theorem ha03077 : a03077.IsHomogeneous 12 := by
  unfold a03077
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03076.pow 1)))

@[irreducible]
def a03078 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01335 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00510 ^ 1)
theorem ha03078 : a03078.IsHomogeneous 12 := by
  unfold a03078
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)))

@[irreducible]
def a03079 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01424 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a03078 ^ 1)
theorem ha03079 : a03079.IsHomogeneous 12 := by
  unfold a03079
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01424.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha03078.pow 1)))

@[irreducible]
def a03080 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02949 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01335 ^ 1)
theorem ha03080 : a03080.IsHomogeneous 12 := by
  unfold a03080
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a03081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03078 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03080 ^ 1)
theorem ha03081 : a03081.IsHomogeneous 12 := by
  unfold a03081
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03078.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03080.pow 1)))

@[irreducible]
def a03082 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03079 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a03081 ^ 1)
theorem ha03082 : a03082.IsHomogeneous 12 := by
  unfold a03082
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03079.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha03081.pow 1)))

@[irreducible]
def a03083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01426 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03079 ^ 1)
theorem ha03083 : a03083.IsHomogeneous 12 := by
  unfold a03083
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01426.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03079.pow 1)))

@[irreducible]
def a03084 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03082 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03083 ^ 1)
theorem ha03084 : a03084.IsHomogeneous 12 := by
  unfold a03084
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03082.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03083.pow 1)))

@[irreducible]
def a03085 : Poly := (C ((-7 : ℂ) / (1 : ℂ)) * a03084 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03077 ^ 1)
theorem ha03085 : a03085.IsHomogeneous 12 := by
  unfold a03085
  exact (((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (1 : ℂ))).mul (ha03084.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03077.pow 1)))

@[irreducible]
def a03086 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a03085 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01412 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01412 ^ 1)
theorem ha03086 : a03086.IsHomogeneous 24 := by
  unfold a03086
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a03087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03063 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a03086 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03057 ^ 1)
theorem ha03087 : a03087.IsHomogeneous 30 := by
  unfold a03087
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03063.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha03086.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03057.pow 1)))

@[irreducible]
def a03088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03064 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03058 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a03087 ^ 1)
theorem ha03088 : a03088.IsHomogeneous 30 := by
  unfold a03088
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03064.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03058.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha03087.pow 1)))

@[irreducible]
def a03089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03067 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03088 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03061 ^ 1)
theorem ha03089 : a03089.IsHomogeneous 30 := by
  unfold a03089
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03067.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03088.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03061.pow 1)))

@[irreducible]
def a03090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03051 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03089 ^ 1)
theorem ha03090 : a03090.IsHomogeneous 30 := by
  unfold a03090
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03089.pow 1)))

@[irreducible]
def a03091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00555 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00171 ^ 1 * a00324 ^ 1)
theorem ha03091 : a03091.IsHomogeneous 24 := by
  unfold a03091
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a03092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00133 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a00316 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00316 ^ 1 * a00324 ^ 1)
theorem ha03092 : a03092.IsHomogeneous 24 := by
  unfold a03092
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00133.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00316.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a03093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00316 ^ 1 * a00324 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00171 ^ 1 * a00324 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1)
theorem ha03093 : a03093.IsHomogeneous 18 := by
  unfold a03093
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00171.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a03094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03091 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a03092 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03093 ^ 1)
theorem ha03094 : a03094.IsHomogeneous 24 := by
  unfold a03094
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03091.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha03092.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03093.pow 1)))

@[irreducible]
def a03095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00171 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00324 ^ 1 * a00555 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00171 ^ 1)
theorem ha03095 : a03095.IsHomogeneous 18 := by
  unfold a03095
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1)).mul (ha00324.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a03096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00555 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a00555 ^ 1)
theorem ha03096 : a03096.IsHomogeneous 24 := by
  unfold a03096
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a03097 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03091 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a03096 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03095 ^ 1)
theorem ha03097 : a03097.IsHomogeneous 24 := by
  unfold a03097
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03091.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha03096.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03095.pow 1)))

@[irreducible]
def a03098 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00171 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1)
theorem ha03098 : a03098.IsHomogeneous 12 := by
  unfold a03098
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00171.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)))

@[irreducible]
def a03099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03093 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a03098 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a03095 ^ 1)
theorem ha03099 : a03099.IsHomogeneous 18 := by
  unfold a03099
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03093.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha03098.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha03095.pow 1)))

@[irreducible]
def a03100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03094 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03097 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03099 ^ 1)
theorem ha03100 : a03100.IsHomogeneous 24 := by
  unfold a03100
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03094.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03097.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03099.pow 1)))

@[irreducible]
def a03101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a00316 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00316 ^ 1 * a00555 ^ 1)
theorem ha03101 : a03101.IsHomogeneous 30 := by
  unfold a03101
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00316.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a03102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00316 ^ 1 * a00555 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00555 ^ 1)
theorem ha03102 : a03102.IsHomogeneous 24 := by
  unfold a03102
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a03103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03101 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03091 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03102 ^ 1)
theorem ha03103 : a03103.IsHomogeneous 30 := by
  unfold a03103
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03101.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03091.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03102.pow 1)))

@[irreducible]
def a03104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a00864 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a00864 ^ 1)
theorem ha03104 : a03104.IsHomogeneous 30 := by
  unfold a03104
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a03105 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03101 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03104 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a03092 ^ 1)
theorem ha03105 : a03105.IsHomogeneous 30 := by
  unfold a03105
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03101.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03104.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha03092.pow 1)))

@[irreducible]
def a03106 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03103 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03105 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03094 ^ 1)
theorem ha03106 : a03106.IsHomogeneous 30 := by
  unfold a03106
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03103.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03105.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03094.pow 1)))

@[irreducible]
def a03107 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00510 ^ 1)
theorem ha03107 : a03107.IsHomogeneous 12 := by
  unfold a03107
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)))

@[irreducible]
def a03108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01335 ^ 1)
theorem ha03108 : a03108.IsHomogeneous 6 := by
  unfold a03108
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01335.pow 1)))

@[irreducible]
def a03109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03107 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a03108 ^ 1)
theorem ha03109 : a03109.IsHomogeneous 12 := by
  unfold a03109
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03107.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha03108.pow 1)))

@[irreducible]
def a03110 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1)
theorem ha03110 : a03110.IsHomogeneous 6 := by
  unfold a03110
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a03111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03110 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03107 ^ 1)
theorem ha03111 : a03111.IsHomogeneous 12 := by
  unfold a03111
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03110.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03107.pow 1)))

@[irreducible]
def a03112 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03109 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03111 ^ 1)
theorem ha03112 : a03112.IsHomogeneous 12 := by
  unfold a03112
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03109.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03111.pow 1)))

@[irreducible]
def a03113 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a02949 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01335 ^ 1)
theorem ha03113 : a03113.IsHomogeneous 12 := by
  unfold a03113
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha02949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01335.pow 1)))

@[irreducible]
def a03114 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03113 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03108 ^ 1)
theorem ha03114 : a03114.IsHomogeneous 12 := by
  unfold a03114
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03113.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03108.pow 1)))

@[irreducible]
def a03115 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03109 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a03114 ^ 1)
theorem ha03115 : a03115.IsHomogeneous 12 := by
  unfold a03115
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03109.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha03114.pow 1)))

@[irreducible]
def a03116 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03112 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03115 ^ 1)
theorem ha03116 : a03116.IsHomogeneous 12 := by
  unfold a03116
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03112.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03115.pow 1)))

@[irreducible]
def a03117 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a03116 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a01429 ^ 1)
theorem ha03117 : a03117.IsHomogeneous 24 := by
  unfold a03117
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a03118 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03096 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03117 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03102 ^ 1)
theorem ha03118 : a03118.IsHomogeneous 30 := by
  unfold a03118
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03096.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03117.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03102.pow 1)))

@[irreducible]
def a03119 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03103 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03097 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03118 ^ 1)
theorem ha03119 : a03119.IsHomogeneous 30 := by
  unfold a03119
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03103.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03097.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03118.pow 1)))

@[irreducible]
def a03120 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03106 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03119 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03100 ^ 1)
theorem ha03120 : a03120.IsHomogeneous 30 := by
  unfold a03120
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03106.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03119.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03100.pow 1)))

@[irreducible]
def a03121 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a03120 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03031 ^ 1) + (C ((3 : ℂ) / (32 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a03090 ^ 1)
theorem ha03121 : a03121.IsHomogeneous 43 := by
  unfold a03121
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha03120.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03031.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (32 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha03090.pow 1)))

@[irreducible]
def a03122 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00161 ^ 1 * a00864 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00316 ^ 1 * a00528 ^ 1)
theorem ha03122 : a03122.IsHomogeneous 30 := by
  unfold a03122
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00316.pow 1)).mul (ha00528.pow 1)))

@[irreducible]
def a03123 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00528 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a01373 ^ 1)
theorem ha03123 : a03123.IsHomogeneous 24 := by
  unfold a03123
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00528.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha01373.pow 1)))

@[irreducible]
def a03124 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03122 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a03123 ^ 1)
theorem ha03124 : a03124.IsHomogeneous 30 := by
  unfold a03124
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03122.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha03123.pow 1)))

@[irreducible]
def a03125 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00161 ^ 1 * a00864 ^ 1)
theorem ha03125 : a03125.IsHomogeneous 30 := by
  unfold a03125
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a03126 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03122 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a03125 ^ 1)
theorem ha03126 : a03126.IsHomogeneous 30 := by
  unfold a03126
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03122.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha03125.pow 1)))

@[irreducible]
def a03127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03124 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03126 ^ 1)
theorem ha03127 : a03127.IsHomogeneous 30 := by
  unfold a03127
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03124.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03126.pow 1)))

@[irreducible]
def a03128 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03016 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a01373 ^ 1)
theorem ha03128 : a03128.IsHomogeneous 30 := by
  unfold a03128
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03016.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha01373.pow 1)))

@[irreducible]
def a03129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03128 ^ 1) + (C ((45 : ℂ) / (8 : ℂ)) * a00003 ^ 6 * a03123 ^ 1)
theorem ha03129 : a03129.IsHomogeneous 30 := by
  unfold a03129
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03128.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (8 : ℂ))).mul (ha00003.pow 6)).mul (ha03123.pow 1)))

@[irreducible]
def a03130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03124 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a03129 ^ 1)
theorem ha03130 : a03130.IsHomogeneous 30 := by
  unfold a03130
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03124.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha03129.pow 1)))

@[irreducible]
def a03131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03127 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03130 ^ 1)
theorem ha03131 : a03131.IsHomogeneous 30 := by
  unfold a03131
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03127.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03130.pow 1)))

@[irreducible]
def a03132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00577 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00179 ^ 1 * a01327 ^ 1)
theorem ha03132 : a03132.IsHomogeneous 36 := by
  unfold a03132
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00577.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00179.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a01473 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00577 ^ 1)
theorem ha03133 : a03133.IsHomogeneous 36 := by
  unfold a03133
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01473.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00577.pow 1)))

@[irreducible]
def a03134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03132 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03133 ^ 1)
theorem ha03134 : a03134.IsHomogeneous 36 := by
  unfold a03134
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03132.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03133.pow 1)))

@[irreducible]
def a03135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a01327 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00040 ^ 1 * a02935 ^ 1)
theorem ha03135 : a03135.IsHomogeneous 24 := by
  unfold a03135
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha02935.pow 1)))

@[irreducible]
def a03136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03132 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03135 ^ 1)
theorem ha03136 : a03136.IsHomogeneous 36 := by
  unfold a03136
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03132.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03135.pow 1)))

@[irreducible]
def a03137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03134 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03136 ^ 1)
theorem ha03137 : a03137.IsHomogeneous 36 := by
  unfold a03137
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03134.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03136.pow 1)))

@[irreducible]
def a03138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00506 ^ 1)
theorem ha03138 : a03138.IsHomogeneous 18 := by
  unfold a03138
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1)
theorem ha03139 : a03139.IsHomogeneous 18 := by
  unfold a03139
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00506 ^ 1)
theorem ha03140 : a03140.IsHomogeneous 18 := by
  unfold a03140
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01327.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03138 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03140 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03139 ^ 1)
theorem ha03141 : a03141.IsHomogeneous 18 := by
  unfold a03141
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03138.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03140.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03139.pow 1)))

@[irreducible]
def a03142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha03142 : a03142.IsHomogeneous 12 := by
  unfold a03142
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a03143 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00014 ^ 1)
theorem ha03143 : a03143.IsHomogeneous 6 := by
  unfold a03143
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a03144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03142 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03138 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03143 ^ 1)
theorem ha03144 : a03144.IsHomogeneous 18 := by
  unfold a03144
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03142.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03138.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03143.pow 1)))

@[irreducible]
def a03145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha03145 : a03145.IsHomogeneous 12 := by
  unfold a03145
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a03146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03142 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a03145 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03139 ^ 1)
theorem ha03146 : a03146.IsHomogeneous 18 := by
  unfold a03146
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03142.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha03145.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03139.pow 1)))

@[irreducible]
def a03147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03141 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03144 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03146 ^ 1)
theorem ha03147 : a03147.IsHomogeneous 18 := by
  unfold a03147
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03141.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03144.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03146.pow 1)))

@[irreducible]
def a03148 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00506 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1)
theorem ha03148 : a03148.IsHomogeneous 18 := by
  unfold a03148
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00506.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00506 ^ 1)
theorem ha03149 : a03149.IsHomogeneous 18 := by
  unfold a03149
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03150 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03138 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a03148 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a03149 ^ 1)
theorem ha03150 : a03150.IsHomogeneous 18 := by
  unfold a03150
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03138.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha03148.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha03149.pow 1)))

@[irreducible]
def a03151 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a02935 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a01327 ^ 1)
theorem ha03151 : a03151.IsHomogeneous 18 := by
  unfold a03151
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03140 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a03151 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a03148 ^ 1)
theorem ha03152 : a03152.IsHomogeneous 18 := by
  unfold a03152
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03140.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha03151.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha03148.pow 1)))

@[irreducible]
def a03153 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03141 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03150 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03152 ^ 1)
theorem ha03153 : a03153.IsHomogeneous 18 := by
  unfold a03153
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03141.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03150.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03152.pow 1)))

@[irreducible]
def a03154 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha03154 : a03154.IsHomogeneous 12 := by
  unfold a03154
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a03155 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03154 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03149 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03143 ^ 1)
theorem ha03155 : a03155.IsHomogeneous 18 := by
  unfold a03155
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03154.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03149.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03143.pow 1)))

@[irreducible]
def a03156 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03144 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03150 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a03155 ^ 1)
theorem ha03156 : a03156.IsHomogeneous 18 := by
  unfold a03156
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03144.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03150.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha03155.pow 1)))

@[irreducible]
def a03157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03147 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03156 ^ 1)
theorem ha03157 : a03157.IsHomogeneous 18 := by
  unfold a03157
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03153.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03156.pow 1)))

@[irreducible]
def a03158 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00176 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00570 ^ 1)
theorem ha03158 : a03158.IsHomogeneous 18 := by
  unfold a03158
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00176.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00570.pow 1)))

@[irreducible]
def a03159 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00176 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00032 ^ 1)
theorem ha03159 : a03159.IsHomogeneous 12 := by
  unfold a03159
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00176.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a03160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03159 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03158 ^ 1)
theorem ha03160 : a03160.IsHomogeneous 18 := by
  unfold a03160
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03159.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03158.pow 1)))

@[irreducible]
def a03161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00570 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a01461 ^ 1)
theorem ha03161 : a03161.IsHomogeneous 18 := by
  unfold a03161
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00570.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha01461.pow 1)))

@[irreducible]
def a03162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03158 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03161 ^ 1)
theorem ha03162 : a03162.IsHomogeneous 18 := by
  unfold a03162
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03158.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03161.pow 1)))

@[irreducible]
def a03163 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03160 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03162 ^ 1)
theorem ha03163 : a03163.IsHomogeneous 18 := by
  unfold a03163
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03160.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03162.pow 1)))

@[irreducible]
def a03164 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a01335 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00324 ^ 1 * a00510 ^ 1)
theorem ha03164 : a03164.IsHomogeneous 12 := by
  unfold a03164
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha01335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00324.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a03165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a02949 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a01335 ^ 1)
theorem ha03165 : a03165.IsHomogeneous 12 := by
  unfold a03165
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha02949.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha01335.pow 1)))

@[irreducible]
def a03166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03164 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a03165 ^ 1)
theorem ha03166 : a03166.IsHomogeneous 12 := by
  unfold a03166
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03164.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha03165.pow 1)))

@[irreducible]
def a03167 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00324 ^ 1 * a00510 ^ 1)
theorem ha03167 : a03167.IsHomogeneous 12 := by
  unfold a03167
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00324.pow 1)).mul (ha00510.pow 1)))

@[irreducible]
def a03168 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03164 ^ 1) + (C ((504 : ℂ) / (5 : ℂ)) * a03167 ^ 1)
theorem ha03168 : a03168.IsHomogeneous 12 := by
  unfold a03168
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03164.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((504 : ℂ) / (5 : ℂ))).mul (ha03167.pow 1)))

@[irreducible]
def a03169 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03166 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03168 ^ 1)
theorem ha03169 : a03169.IsHomogeneous 12 := by
  unfold a03169
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03166.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03168.pow 1)))

@[irreducible]
def a03170 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00553 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03167 ^ 1)
theorem ha03170 : a03170.IsHomogeneous 12 := by
  unfold a03170
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00553.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03167.pow 1)))

@[irreducible]
def a03171 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03168 ^ 1) + (C ((504 : ℂ) / (5 : ℂ)) * a03170 ^ 1)
theorem ha03171 : a03171.IsHomogeneous 12 := by
  unfold a03171
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03168.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((504 : ℂ) / (5 : ℂ))).mul (ha03170.pow 1)))

@[irreducible]
def a03172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03169 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03171 ^ 1)
theorem ha03172 : a03172.IsHomogeneous 12 := by
  unfold a03172
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03169.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03171.pow 1)))

@[irreducible]
def a03173 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a03172 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a01461 ^ 1)
theorem ha03173 : a03173.IsHomogeneous 18 := by
  unfold a03173
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha03172.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha01461.pow 1)))

@[irreducible]
def a03174 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03161 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a03173 ^ 1)
theorem ha03174 : a03174.IsHomogeneous 18 := by
  unfold a03174
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03161.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha03173.pow 1)))

@[irreducible]
def a03175 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03162 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03174 ^ 1)
theorem ha03175 : a03175.IsHomogeneous 18 := by
  unfold a03175
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03162.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03174.pow 1)))

@[irreducible]
def a03176 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03163 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03175 ^ 1)
theorem ha03176 : a03176.IsHomogeneous 18 := by
  unfold a03176
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03163.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03175.pow 1)))

@[irreducible]
def a03177 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1 * a01335 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00510 ^ 1 * a00574 ^ 1)
theorem ha03177 : a03177.IsHomogeneous 18 := by
  unfold a03177
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)).mul (ha01335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00510.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a03178 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a01335 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00025 ^ 1 * a02949 ^ 1)
theorem ha03178 : a03178.IsHomogeneous 12 := by
  unfold a03178
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha01335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00025.pow 1)).mul (ha02949.pow 1)))

@[irreducible]
def a03179 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a03178 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03177 ^ 1)
theorem ha03179 : a03179.IsHomogeneous 18 := by
  unfold a03179
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha03178.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03177.pow 1)))

@[irreducible]
def a03180 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1 * a01469 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00510 ^ 1 * a00574 ^ 1)
theorem ha03180 : a03180.IsHomogeneous 18 := by
  unfold a03180
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)).mul (ha01469.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00510.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a03181 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03177 ^ 1) + (C ((168 : ℂ) / (5 : ℂ)) * a03180 ^ 1)
theorem ha03181 : a03181.IsHomogeneous 18 := by
  unfold a03181
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03177.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((168 : ℂ) / (5 : ℂ))).mul (ha03180.pow 1)))

@[irreducible]
def a03182 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03179 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03181 ^ 1)
theorem ha03182 : a03182.IsHomogeneous 18 := by
  unfold a03182
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03179.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03181.pow 1)))

@[irreducible]
def a03183 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6)
theorem ha03183 : a03183.IsHomogeneous 6 := by
  unfold a03183
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a03184 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00130 ^ 1)
theorem ha03184 : a03184.IsHomogeneous 6 := by
  unfold a03184
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)))

@[irreducible]
def a03185 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03183 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03184 ^ 1)
theorem ha03185 : a03185.IsHomogeneous 6 := by
  unfold a03185
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03183.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03184.pow 1)))

@[irreducible]
def a03186 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03183 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03185 ^ 1)
theorem ha03186 : a03186.IsHomogeneous 6 := by
  unfold a03186
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03183.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03185.pow 1)))

@[irreducible]
def a03187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1 * a01469 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a03186 ^ 1)
theorem ha03187 : a03187.IsHomogeneous 12 := by
  unfold a03187
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).mul (ha01469.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha03186.pow 1)))

@[irreducible]
def a03188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03187 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03180 ^ 1)
theorem ha03188 : a03188.IsHomogeneous 18 := by
  unfold a03188
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03187.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03180.pow 1)))

@[irreducible]
def a03189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03181 ^ 1) + (C ((168 : ℂ) / (5 : ℂ)) * a03188 ^ 1)
theorem ha03189 : a03189.IsHomogeneous 18 := by
  unfold a03189
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03181.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((168 : ℂ) / (5 : ℂ))).mul (ha03188.pow 1)))

@[irreducible]
def a03190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03182 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03189 ^ 1)
theorem ha03190 : a03190.IsHomogeneous 18 := by
  unfold a03190
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03182.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03189.pow 1)))

@[irreducible]
def a03191 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a03176 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03157 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a03190 ^ 1)
theorem ha03191 : a03191.IsHomogeneous 18 := by
  unfold a03191
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha03176.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03157.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha03190.pow 1)))

@[irreducible]
def a03192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01473 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03191 ^ 1)
theorem ha03192 : a03192.IsHomogeneous 30 := by
  unfold a03192
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01473.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03191.pow 1)))

@[irreducible]
def a03193 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03192 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03133 ^ 1)
theorem ha03193 : a03193.IsHomogeneous 36 := by
  unfold a03193
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03192.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03133.pow 1)))

@[irreducible]
def a03194 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03134 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03193 ^ 1)
theorem ha03194 : a03194.IsHomogeneous 36 := by
  unfold a03194
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03134.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03193.pow 1)))

@[irreducible]
def a03195 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03137 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03194 ^ 1)
theorem ha03195 : a03195.IsHomogeneous 36 := by
  unfold a03195
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03137.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03194.pow 1)))

@[irreducible]
def a03196 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a03131 ^ 1) + (C ((1 : ℂ) / (810 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a03195 ^ 1)
theorem ha03196 : a03196.IsHomogeneous 51 := by
  unfold a03196
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha03131.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (810 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha03195.pow 1)))

@[irreducible]
def a03197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00513 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01340 ^ 1)
theorem ha03197 : a03197.IsHomogeneous 45 := by
  unfold a03197
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00513.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01340.pow 1)))

@[irreducible]
def a03198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00513 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00157 ^ 1 * a00865 ^ 1)
theorem ha03198 : a03198.IsHomogeneous 39 := by
  unfold a03198
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00513.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00157.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03198 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03197 ^ 1)
theorem ha03199 : a03199.IsHomogeneous 45 := by
  unfold a03199
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03198.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03197.pow 1)))

@[irreducible]
def a03200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a02956 ^ 1) + (C ((72 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01340 ^ 1)
theorem ha03200 : a03200.IsHomogeneous 48 := by
  unfold a03200
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha02956.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01340.pow 1)))

@[irreducible]
def a03201 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03197 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a03200 ^ 1)
theorem ha03201 : a03201.IsHomogeneous 51 := by
  unfold a03201
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03197.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha03200.pow 1)))

@[irreducible]
def a03202 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03199 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03201 ^ 1)
theorem ha03202 : a03202.IsHomogeneous 51 := by
  unfold a03202
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03199.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03201.pow 1)))

@[irreducible]
def a03203 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00157 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a02008 ^ 1)
theorem ha03203 : a03203.IsHomogeneous 33 := by
  unfold a03203
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a03204 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03198 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a03203 ^ 1)
theorem ha03204 : a03204.IsHomogeneous 39 := by
  unfold a03204
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03198.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha03203.pow 1)))

@[irreducible]
def a03205 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03204 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03199 ^ 1)
theorem ha03205 : a03205.IsHomogeneous 45 := by
  unfold a03205
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03204.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03199.pow 1)))

@[irreducible]
def a03206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03205 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03202 ^ 1)
theorem ha03206 : a03206.IsHomogeneous 51 := by
  unfold a03206
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03205.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03202.pow 1)))

@[irreducible]
def a03207 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a03131 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00005 ^ 1 * a03206 ^ 1)
theorem ha03207 : a03207.IsHomogeneous 57 := by
  unfold a03207
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha03131.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00005.pow 1)).mul (ha03206.pow 1)))

@[irreducible]
def a03208 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a03196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03207 ^ 1)
theorem ha03208 : a03208.IsHomogeneous 57 := by
  unfold a03208
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha03196.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03207.pow 1)))

@[irreducible]
def a03209 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a00547 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a00506 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a00168 ^ 1)
theorem ha03209 : a03209.IsHomogeneous 30 := by
  unfold a03209
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00547.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a03210 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a00506 ^ 1)
theorem ha03210 : a03210.IsHomogeneous 30 := by
  unfold a03210
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00506.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03211 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00155 ^ 1 * a00168 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00155 ^ 1)
theorem ha03211 : a03211.IsHomogeneous 18 := by
  unfold a03211
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00155.pow 1)).mul (ha00168.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a03212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03209 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a03210 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03211 ^ 1)
theorem ha03212 : a03212.IsHomogeneous 30 := by
  unfold a03212
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03209.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha03210.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03211.pow 1)))

@[irreducible]
def a03213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00168 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00547 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00168 ^ 1)
theorem ha03213 : a03213.IsHomogeneous 18 := by
  unfold a03213
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00168.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00547.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a03214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00130 ^ 1 * a01412 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00547 ^ 1)
theorem ha03214 : a03214.IsHomogeneous 30 := by
  unfold a03214
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00547.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a03215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03209 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03214 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03213 ^ 1)
theorem ha03215 : a03215.IsHomogeneous 30 := by
  unfold a03215
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03209.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03214.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03213.pow 1)))

@[irreducible]
def a03216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00168 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1)
theorem ha03216 : a03216.IsHomogeneous 12 := by
  unfold a03216
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00168.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)))

@[irreducible]
def a03217 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03211 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a03213 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a03216 ^ 1)
theorem ha03217 : a03217.IsHomogeneous 18 := by
  unfold a03217
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03211.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha03213.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha03216.pow 1)))

@[irreducible]
def a03218 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03212 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03215 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03217 ^ 1)
theorem ha03218 : a03218.IsHomogeneous 30 := by
  unfold a03218
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03212.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03215.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03217.pow 1)))

@[irreducible]
def a03219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a00547 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a00168 ^ 1 * a01327 ^ 1)
theorem ha03219 : a03219.IsHomogeneous 36 := by
  unfold a03219
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha00547.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a00547 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a01412 ^ 1)
theorem ha03220 : a03220.IsHomogeneous 36 := by
  unfold a03220
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00547.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha00547.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a03221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03209 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03220 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a03219 ^ 1)
theorem ha03221 : a03221.IsHomogeneous 36 := by
  unfold a03221
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03209.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03220.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha03219.pow 1)))

@[irreducible]
def a03222 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a01327 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a02935 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a01327 ^ 1)
theorem ha03222 : a03222.IsHomogeneous 24 := by
  unfold a03222
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha01327.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha02935.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03223 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03219 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03222 ^ 1)
theorem ha03223 : a03223.IsHomogeneous 36 := by
  unfold a03223
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03210.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03219.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03222.pow 1)))

@[irreducible]
def a03224 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03212 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03221 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a03223 ^ 1)
theorem ha03224 : a03224.IsHomogeneous 36 := by
  unfold a03224
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03212.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03221.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha03223.pow 1)))

@[irreducible]
def a03225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a01412 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a03085 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01412 ^ 1)
theorem ha03225 : a03225.IsHomogeneous 24 := by
  unfold a03225
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha03085.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a03226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03214 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03220 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03225 ^ 1)
theorem ha03226 : a03226.IsHomogeneous 36 := by
  unfold a03226
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03214.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03220.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03225.pow 1)))

@[irreducible]
def a03227 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03215 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03221 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03226 ^ 1)
theorem ha03227 : a03227.IsHomogeneous 36 := by
  unfold a03227
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03215.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03221.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03226.pow 1)))

@[irreducible]
def a03228 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03218 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03224 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03227 ^ 1)
theorem ha03228 : a03228.IsHomogeneous 36 := by
  unfold a03228
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03218.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03224.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03227.pow 1)))

@[irreducible]
def a03229 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a02989 ^ 1) + (C ((1 : ℂ) / (540 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a03228 ^ 1)
theorem ha03229 : a03229.IsHomogeneous 51 := by
  unfold a03229
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha02989.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (540 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha03228.pow 1)))

@[irreducible]
def a03230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00155 ^ 1 * a00555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a00506 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00171 ^ 1 * a00324 ^ 1)
theorem ha03230 : a03230.IsHomogeneous 30 := by
  unfold a03230
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a03231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00324 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (21 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a01327 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a00506 ^ 1)
theorem ha03231 : a03231.IsHomogeneous 30 := by
  unfold a03231
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00506.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (21 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03232 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00324 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00155 ^ 1 * a00171 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00155 ^ 1)
theorem ha03232 : a03232.IsHomogeneous 24 := by
  unfold a03232
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00324.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00155.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a03233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03230 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03232 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a03231 ^ 1)
theorem ha03233 : a03233.IsHomogeneous 30 := by
  unfold a03233
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03230.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03232.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha03231.pow 1)))

@[irreducible]
def a03234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00171 ^ 1 * a00324 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00324 ^ 1 * a00555 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00171 ^ 1)
theorem ha03234 : a03234.IsHomogeneous 24 := by
  unfold a03234
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a03235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00155 ^ 1 * a00555 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a00555 ^ 1)
theorem ha03235 : a03235.IsHomogeneous 24 := by
  unfold a03235
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00555.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a03236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03235 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03230 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a03234 ^ 1)
theorem ha03236 : a03236.IsHomogeneous 30 := by
  unfold a03236
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03235.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03230.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha03234.pow 1)))

@[irreducible]
def a03237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00171 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00009 ^ 1 * a00014 ^ 1)
theorem ha03237 : a03237.IsHomogeneous 12 := by
  unfold a03237
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00171.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)))

@[irreducible]
def a03238 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03232 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03234 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03237 ^ 1)
theorem ha03238 : a03238.IsHomogeneous 24 := by
  unfold a03238
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03234.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03237.pow 1)))

@[irreducible]
def a03239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03233 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03236 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03238 ^ 1)
theorem ha03239 : a03239.IsHomogeneous 30 := by
  unfold a03239
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03233.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03236.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03238.pow 1)))

@[irreducible]
def a03240 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1 * a00171 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00506 ^ 1 * a00555 ^ 1)
theorem ha03240 : a03240.IsHomogeneous 36 := by
  unfold a03240
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00506.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a03241 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00155 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a00555 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00506 ^ 1 * a00555 ^ 1)
theorem ha03241 : a03241.IsHomogeneous 30 := by
  unfold a03241
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha01429.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a03242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03230 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03240 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03241 ^ 1)
theorem ha03242 : a03242.IsHomogeneous 36 := by
  unfold a03242
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03230.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03240.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03241.pow 1)))

@[irreducible]
def a03243 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a02935 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a01327 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a01327 ^ 1)
theorem ha03243 : a03243.IsHomogeneous 24 := by
  unfold a03243
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha02935.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03244 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03231 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a03240 ^ 1) + (C ((5 : ℂ) / (42 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03243 ^ 1)
theorem ha03244 : a03244.IsHomogeneous 36 := by
  unfold a03244
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03231.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha03240.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (42 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03243.pow 1)))

@[irreducible]
def a03245 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03233 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03242 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a03244 ^ 1)
theorem ha03245 : a03245.IsHomogeneous 36 := by
  unfold a03245
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03233.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03242.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha03244.pow 1)))

@[irreducible]
def a03246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a01429 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a03116 ^ 1)
theorem ha03246 : a03246.IsHomogeneous 24 := by
  unfold a03246
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha01429.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha03116.pow 1)))

@[irreducible]
def a03247 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03235 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03246 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a03241 ^ 1)
theorem ha03247 : a03247.IsHomogeneous 30 := by
  unfold a03247
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03235.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03246.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha03241.pow 1)))

@[irreducible]
def a03248 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03247 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03236 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03242 ^ 1)
theorem ha03248 : a03248.IsHomogeneous 36 := by
  unfold a03248
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03247.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03236.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03242.pow 1)))

@[irreducible]
def a03249 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03239 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03245 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03248 ^ 1)
theorem ha03249 : a03249.IsHomogeneous 36 := by
  unfold a03249
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03239.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03245.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03248.pow 1)))

@[irreducible]
def a03250 : Poly := (C ((-1 : ℂ) / (3240 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00004 ^ 3 * a00005 ^ 1 * a03249 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03208 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a03229 ^ 1)
theorem ha03250 : a03250.IsHomogeneous 57 := by
  unfold a03250
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3240 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha03249.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03208.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha03229.pow 1)))

@[irreducible]
def a03251 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00316 ^ 1 * a00577 ^ 1)
theorem ha03251 : a03251.IsHomogeneous 30 := by
  unfold a03251
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha00864.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00316.pow 1)).mul (ha00577.pow 1)))

@[irreducible]
def a03252 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00577 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a01473 ^ 1)
theorem ha03252 : a03252.IsHomogeneous 30 := by
  unfold a03252
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00577.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha01473.pow 1)))

@[irreducible]
def a03253 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03251 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03252 ^ 1)
theorem ha03253 : a03253.IsHomogeneous 30 := by
  unfold a03253
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03251.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03252.pow 1)))

@[irreducible]
def a03254 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00040 ^ 1 * a02007 ^ 1)
theorem ha03254 : a03254.IsHomogeneous 30 := by
  unfold a03254
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha02007.pow 1)))

@[irreducible]
def a03255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03251 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03254 ^ 1)
theorem ha03255 : a03255.IsHomogeneous 30 := by
  unfold a03255
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03251.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03254.pow 1)))

@[irreducible]
def a03256 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03255 ^ 1)
theorem ha03256 : a03256.IsHomogeneous 30 := by
  unfold a03256
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03253.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03255.pow 1)))

@[irreducible]
def a03257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01473 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a03191 ^ 1)
theorem ha03257 : a03257.IsHomogeneous 24 := by
  unfold a03257
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01473.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha03191.pow 1)))

@[irreducible]
def a03258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03252 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03257 ^ 1)
theorem ha03258 : a03258.IsHomogeneous 30 := by
  unfold a03258
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03252.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03257.pow 1)))

@[irreducible]
def a03259 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03253 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03258 ^ 1)
theorem ha03259 : a03259.IsHomogeneous 30 := by
  unfold a03259
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03253.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03258.pow 1)))

@[irreducible]
def a03260 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03259 ^ 1)
theorem ha03260 : a03260.IsHomogeneous 30 := by
  unfold a03260
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03256.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03259.pow 1)))

@[irreducible]
def a03261 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00528 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a01373 ^ 1)
theorem ha03261 : a03261.IsHomogeneous 45 := by
  unfold a03261
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00528.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha01373.pow 1)))

@[irreducible]
def a03262 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00317 ^ 1 * a00528 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00161 ^ 1 * a00865 ^ 1)
theorem ha03262 : a03262.IsHomogeneous 45 := by
  unfold a03262
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00317.pow 1)).mul (ha00528.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00161.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03263 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03261 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03262 ^ 1)
theorem ha03263 : a03263.IsHomogeneous 51 := by
  unfold a03263
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03261.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03262.pow 1)))

@[irreducible]
def a03264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a03016 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a01373 ^ 1)
theorem ha03264 : a03264.IsHomogeneous 48 := by
  unfold a03264
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha03016.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha01373.pow 1)))

@[irreducible]
def a03265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03264 ^ 1) + (C ((45 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a03261 ^ 1)
theorem ha03265 : a03265.IsHomogeneous 48 := by
  unfold a03265
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha03261.pow 1)))

@[irreducible]
def a03266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03265 ^ 1) + (C ((45 : ℂ) / (8 : ℂ)) * a03263 ^ 1)
theorem ha03266 : a03266.IsHomogeneous 51 := by
  unfold a03266
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03265.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (8 : ℂ))).mul (ha03263.pow 1)))

@[irreducible]
def a03267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00161 ^ 1 * a00865 ^ 1)
theorem ha03267 : a03267.IsHomogeneous 39 := by
  unfold a03267
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03268 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03262 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a03267 ^ 1)
theorem ha03268 : a03268.IsHomogeneous 45 := by
  unfold a03268
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha03267.pow 1)))

@[irreducible]
def a03269 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03268 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03263 ^ 1)
theorem ha03269 : a03269.IsHomogeneous 51 := by
  unfold a03269
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03268.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03263.pow 1)))

@[irreducible]
def a03270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03266 ^ 1) + (C ((45 : ℂ) / (8 : ℂ)) * a03269 ^ 1)
theorem ha03270 : a03270.IsHomogeneous 51 := by
  unfold a03270
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (8 : ℂ))).mul (ha03269.pow 1)))

@[irreducible]
def a03271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03270 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a03260 ^ 1)
theorem ha03271 : a03271.IsHomogeneous 57 := by
  unfold a03271
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03270.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha03260.pow 1)))

@[irreducible]
def a03272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03020 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a03260 ^ 1)
theorem ha03272 : a03272.IsHomogeneous 30 := by
  unfold a03272
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03020.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha03260.pow 1)))

@[irreducible]
def a03273 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03271 ^ 1) + (C ((1 : ℂ) / (16 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a03272 ^ 1)
theorem ha03273 : a03273.IsHomogeneous 57 := by
  unfold a03273
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03271.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (16 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha03272.pow 1)))

@[irreducible]
def a03274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03270 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03271 ^ 1)
theorem ha03274 : a03274.IsHomogeneous 57 := by
  unfold a03274
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03270.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03271.pow 1)))

@[irreducible]
def a03275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03273 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03274 ^ 1)
theorem ha03275 : a03275.IsHomogeneous 57 := by
  unfold a03275
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03273.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03274.pow 1)))

@[irreducible]
def a03276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a00317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00520 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00020 ^ 1 * a00129 ^ 1)
theorem ha03276 : a03276.IsHomogeneous 39 := by
  unfold a03276
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a03277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00520 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00020 ^ 1 * a00129 ^ 1)
theorem ha03277 : a03277.IsHomogeneous 36 := by
  unfold a03277
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00520.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a03278 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a01356 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00042 ^ 1 * a00520 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00130 ^ 1 * a00520 ^ 1)
theorem ha03278 : a03278.IsHomogeneous 48 := by
  unfold a03278
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha01356.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00520.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a03279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03278 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03277 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03276 ^ 1)
theorem ha03279 : a03279.IsHomogeneous 48 := by
  unfold a03279
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03278.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03277.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03276.pow 1)))

@[irreducible]
def a03280 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00129 ^ 1)
theorem ha03280 : a03280.IsHomogeneous 33 := by
  unfold a03280
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a03281 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a00865 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00130 ^ 1 * a00317 ^ 1)
theorem ha03281 : a03281.IsHomogeneous 39 := by
  unfold a03281
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a03282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03276 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03280 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a03281 ^ 1)
theorem ha03282 : a03282.IsHomogeneous 45 := by
  unfold a03282
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03276.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03280.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha03281.pow 1)))

@[irreducible]
def a03283 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00042 ^ 1)
theorem ha03283 : a03283.IsHomogeneous 36 := by
  unfold a03283
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a03284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03283 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03280 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03277 ^ 1)
theorem ha03284 : a03284.IsHomogeneous 42 := by
  unfold a03284
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03283.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03280.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03277.pow 1)))

@[irreducible]
def a03285 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03284 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a03279 ^ 1) + (C ((81 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a03282 ^ 1)
theorem ha03285 : a03285.IsHomogeneous 51 := by
  unfold a03285
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03284.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha03279.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha03282.pow 1)))

@[irreducible]
def a03286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00025 ^ 1 * a00129 ^ 1 * a01356 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00130 ^ 1 * a00520 ^ 1)
theorem ha03286 : a03286.IsHomogeneous 45 := by
  unfold a03286
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha00520.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha01356.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00520.pow 1)))

@[irreducible]
def a03287 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a00520 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00025 ^ 1 * a00865 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00020 ^ 1 * a00130 ^ 1 * a00317 ^ 1)
theorem ha03287 : a03287.IsHomogeneous 39 := by
  unfold a03287
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha00520.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00020.pow 1)).mul (ha00130.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a03288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03276 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a03287 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03286 ^ 1)
theorem ha03288 : a03288.IsHomogeneous 45 := by
  unfold a03288
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03276.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha03287.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03286.pow 1)))

@[irreducible]
def a03289 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a02985 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a01356 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1 * a01356 ^ 1)
theorem ha03289 : a03289.IsHomogeneous 48 := by
  unfold a03289
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha02985.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha01356.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha01356.pow 1)))

@[irreducible]
def a03290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03278 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a03289 ^ 1) + (C ((45 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a03286 ^ 1)
theorem ha03290 : a03290.IsHomogeneous 48 := by
  unfold a03290
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03278.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha03289.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha03286.pow 1)))

@[irreducible]
def a03291 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03279 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03290 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a03288 ^ 1)
theorem ha03291 : a03291.IsHomogeneous 48 := by
  unfold a03291
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03279.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03290.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha03288.pow 1)))

@[irreducible]
def a03292 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a02008 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a00865 ^ 1)
theorem ha03292 : a03292.IsHomogeneous 39 := by
  unfold a03292
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha02008.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03293 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03287 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a03292 ^ 1) + (C ((14 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a03281 ^ 1)
theorem ha03293 : a03293.IsHomogeneous 45 := by
  unfold a03293
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03287.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha03292.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha03281.pow 1)))

@[irreducible]
def a03294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03288 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03282 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a03293 ^ 1)
theorem ha03294 : a03294.IsHomogeneous 51 := by
  unfold a03294
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03288.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03282.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha03293.pow 1)))

@[irreducible]
def a03295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03291 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a03285 ^ 1) + (C ((27 : ℂ) / (2 : ℂ)) * a03294 ^ 1)
theorem ha03295 : a03295.IsHomogeneous 51 := by
  unfold a03295
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03291.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha03285.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (2 : ℂ))).mul (ha03294.pow 1)))

@[irreducible]
def a03296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03295 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a03089 ^ 1)
theorem ha03296 : a03296.IsHomogeneous 57 := by
  unfold a03296
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03295.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha03089.pow 1)))

@[irreducible]
def a03297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03296 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a03090 ^ 1)
theorem ha03297 : a03297.IsHomogeneous 57 := by
  unfold a03297
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03296.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha03090.pow 1)))

@[irreducible]
def a03298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a00316 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00201 ^ 1)
theorem ha03298 : a03298.IsHomogeneous 39 := by
  unfold a03298
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a03299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a00864 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00054 ^ 1 * a00316 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00130 ^ 1 * a00201 ^ 1 * a00316 ^ 1)
theorem ha03299 : a03299.IsHomogeneous 48 := by
  unfold a03299
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00316.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a03300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00316 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1)
theorem ha03300 : a03300.IsHomogeneous 36 := by
  unfold a03300
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a03301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03299 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03300 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03298 ^ 1)
theorem ha03301 : a03301.IsHomogeneous 48 := by
  unfold a03301
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03299.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03300.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03298.pow 1)))

@[irreducible]
def a03302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00621 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00201 ^ 1)
theorem ha03302 : a03302.IsHomogeneous 33 := by
  unfold a03302
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00201.pow 1)))

@[irreducible]
def a03303 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00621 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01555 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00621 ^ 1)
theorem ha03303 : a03303.IsHomogeneous 39 := by
  unfold a03303
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a03304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03303 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03302 ^ 1)
theorem ha03304 : a03304.IsHomogeneous 45 := by
  unfold a03304
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03303.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03302.pow 1)))

@[irreducible]
def a03305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00054 ^ 1)
theorem ha03305 : a03305.IsHomogeneous 36 := by
  unfold a03305
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00054.pow 1)))

@[irreducible]
def a03306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03305 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03302 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03300 ^ 1)
theorem ha03306 : a03306.IsHomogeneous 42 := by
  unfold a03306
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03305.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03302.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03300.pow 1)))

@[irreducible]
def a03307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03306 ^ 1) + (C ((18 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a03301 ^ 1) + (C ((81 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a03304 ^ 1)
theorem ha03307 : a03307.IsHomogeneous 51 := by
  unfold a03307
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03306.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha03301.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((81 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha03304.pow 1)))

@[irreducible]
def a03308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00316 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a00201 ^ 1 * a00864 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00201 ^ 1 * a00316 ^ 1)
theorem ha03308 : a03308.IsHomogeneous 45 := by
  unfold a03308
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a03309 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00316 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a01555 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00621 ^ 1)
theorem ha03309 : a03309.IsHomogeneous 39 := by
  unfold a03309
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00316.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a03310 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03298 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a03309 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03308 ^ 1)
theorem ha03310 : a03310.IsHomogeneous 45 := by
  unfold a03310
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha03309.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03308.pow 1)))

@[irreducible]
def a03311 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00054 ^ 1 * a02007 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a00864 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00201 ^ 1 * a00864 ^ 1)
theorem ha03311 : a03311.IsHomogeneous 48 := by
  unfold a03311
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha02007.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha00864.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a03312 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03299 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a03311 ^ 1) + (C ((15 : ℂ) / (8 : ℂ)) * a00003 ^ 3 * a03308 ^ 1)
theorem ha03312 : a03312.IsHomogeneous 48 := by
  unfold a03312
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03299.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha03311.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (8 : ℂ))).mul (ha00003.pow 3)).mul (ha03308.pow 1)))

@[irreducible]
def a03313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03301 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03312 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a03310 ^ 1)
theorem ha03313 : a03313.IsHomogeneous 48 := by
  unfold a03313
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03301.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03312.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha03310.pow 1)))

@[irreducible]
def a03314 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00317 ^ 1)
theorem ha03314 : a03314.IsHomogeneous 21 := by
  unfold a03314
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00317.pow 1)))

@[irreducible]
def a03315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1)
theorem ha03315 : a03315.IsHomogeneous 24 := by
  unfold a03315
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)))

@[irreducible]
def a03316 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03315 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03314 ^ 1)
theorem ha03316 : a03316.IsHomogeneous 24 := by
  unfold a03316
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03315.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03314.pow 1)))

@[irreducible]
def a03317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00865 ^ 1)
theorem ha03317 : a03317.IsHomogeneous 21 := by
  unfold a03317
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00865.pow 1)))

@[irreducible]
def a03318 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03314 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a03317 ^ 1)
theorem ha03318 : a03318.IsHomogeneous 21 := by
  unfold a03318
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03314.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha03317.pow 1)))

@[irreducible]
def a03319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03316 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03318 ^ 1)
theorem ha03319 : a03319.IsHomogeneous 24 := by
  unfold a03319
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03318.pow 1)))

@[irreducible]
def a03320 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00865 ^ 1)
theorem ha03320 : a03320.IsHomogeneous 24 := by
  unfold a03320
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00865.pow 1)))

@[irreducible]
def a03321 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03320 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a03317 ^ 1)
theorem ha03321 : a03321.IsHomogeneous 24 := by
  unfold a03321
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03320.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha03317.pow 1)))

@[irreducible]
def a03322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03321 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03318 ^ 1)
theorem ha03322 : a03322.IsHomogeneous 24 := by
  unfold a03322
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03321.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03318.pow 1)))

@[irreducible]
def a03323 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03319 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03322 ^ 1)
theorem ha03323 : a03323.IsHomogeneous 24 := by
  unfold a03323
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03319.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03322.pow 1)))

@[irreducible]
def a03324 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1) + (C ((7 : ℂ) / (24 : ℂ)) * a00324 ^ 1)
theorem ha03324 : a03324.IsHomogeneous 6 := by
  unfold a03324
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (24 : ℂ))).mul (ha00324.pow 1)))

@[irreducible]
def a03325 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01570 ^ 1) + (C ((72 : ℂ) / (5 : ℂ)) * a03324 ^ 1)
theorem ha03325 : a03325.IsHomogeneous 6 := by
  unfold a03325
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01570.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((72 : ℂ) / (5 : ℂ))).mul (ha03324.pow 1)))

@[irreducible]
def a03326 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01571 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03325 ^ 1)
theorem ha03326 : a03326.IsHomogeneous 6 := by
  unfold a03326
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01571.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03325.pow 1)))

@[irreducible]
def a03327 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01468 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a03324 ^ 1)
theorem ha03327 : a03327.IsHomogeneous 6 := by
  unfold a03327
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01468.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha03324.pow 1)))

@[irreducible]
def a03328 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03325 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a03327 ^ 1)
theorem ha03328 : a03328.IsHomogeneous 6 := by
  unfold a03328
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03325.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha03327.pow 1)))

@[irreducible]
def a03329 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03326 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03328 ^ 1)
theorem ha03329 : a03329.IsHomogeneous 6 := by
  unfold a03329
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03326.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03328.pow 1)))

@[irreducible]
def a03330 : Poly := (C ((-7 : ℂ) / (324 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a03329 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03323 ^ 1)
theorem ha03330 : a03330.IsHomogeneous 24 := by
  unfold a03330
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (324 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha03329.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03323.pow 1)))

@[irreducible]
def a03331 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a03330 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01555 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a01555 ^ 1)
theorem ha03331 : a03331.IsHomogeneous 39 := by
  unfold a03331
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha03330.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a03332 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03309 ^ 1) + (C ((2 : ℂ) / (45 : ℂ)) * a00014 ^ 1 * a03331 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03303 ^ 1)
theorem ha03332 : a03332.IsHomogeneous 45 := by
  unfold a03332
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03309.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (45 : ℂ))).mul (ha00014.pow 1)).mul (ha03331.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03303.pow 1)))

@[irreducible]
def a03333 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03310 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03304 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a03332 ^ 1)
theorem ha03333 : a03333.IsHomogeneous 51 := by
  unfold a03333
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03310.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03304.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha03332.pow 1)))

@[irreducible]
def a03334 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03313 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a03307 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03333 ^ 1)
theorem ha03334 : a03334.IsHomogeneous 51 := by
  unfold a03334
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03313.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha03307.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03333.pow 1)))

@[irreducible]
def a03335 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a03334 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a03051 ^ 1)
theorem ha03335 : a03335.IsHomogeneous 57 := by
  unfold a03335
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha03334.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha03051.pow 1)))

@[irreducible]
def a03336 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03335 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 5 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 1 * a03090 ^ 1)
theorem ha03336 : a03336.IsHomogeneous 57 := by
  unfold a03336
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03335.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha03090.pow 1)))

@[irreducible]
def a03337 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03297 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03336 ^ 1)
theorem ha03337 : a03337.IsHomogeneous 57 := by
  unfold a03337
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03297.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03336.pow 1)))

@[irreducible]
def a03338 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00316 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00632 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00324 ^ 1)
theorem ha03338 : a03338.IsHomogeneous 24 := by
  unfold a03338
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a03339 : Poly := (C ((-8 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00207 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00316 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a00864 ^ 1)
theorem ha03339 : a03339.IsHomogeneous 30 := by
  unfold a03339
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a03340 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00207 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00316 ^ 1 * a00324 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00058 ^ 1)
theorem ha03340 : a03340.IsHomogeneous 24 := by
  unfold a03340
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00316.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00058.pow 1)))

@[irreducible]
def a03341 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a03340 ^ 1) + (C ((-7 : ℂ) / (8 : ℂ)) * a03339 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03338 ^ 1)
theorem ha03341 : a03341.IsHomogeneous 30 := by
  unfold a03341
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha03340.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha03339.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03338.pow 1)))

@[irreducible]
def a03342 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00207 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a00632 ^ 1)
theorem ha03342 : a03342.IsHomogeneous 24 := by
  unfold a03342
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00207.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00207.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a03343 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a00632 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00133 ^ 1 * a01575 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a00632 ^ 1)
theorem ha03343 : a03343.IsHomogeneous 24 := by
  unfold a03343
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a03344 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03338 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03343 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03342 ^ 1)
theorem ha03344 : a03344.IsHomogeneous 30 := by
  unfold a03344
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03338.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03343.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03342.pow 1)))

@[irreducible]
def a03345 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00058 ^ 1)
theorem ha03345 : a03345.IsHomogeneous 18 := by
  unfold a03345
  exact (((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)))

@[irreducible]
def a03346 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03342 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03340 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03345 ^ 1)
theorem ha03346 : a03346.IsHomogeneous 30 := by
  unfold a03346
  exact (((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03342.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03340.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03345.pow 1)))

@[irreducible]
def a03347 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a00014 ^ 1 * a03346 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03341 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03344 ^ 1)
theorem ha03347 : a03347.IsHomogeneous 36 := by
  unfold a03347
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha00014.pow 1)).mul (ha03346.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03341.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03344.pow 1)))

@[irreducible]
def a03348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00316 ^ 1 * a00632 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00207 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a00864 ^ 1)
theorem ha03348 : a03348.IsHomogeneous 30 := by
  unfold a03348
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a03349 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00316 ^ 1 * a00632 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00632 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1 * a01575 ^ 1)
theorem ha03349 : a03349.IsHomogeneous 24 := by
  unfold a03349
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00316.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00632.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a03350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03338 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03349 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a03348 ^ 1)
theorem ha03350 : a03350.IsHomogeneous 30 := by
  unfold a03350
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03338.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03349.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha03348.pow 1)))

@[irreducible]
def a03351 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a00864 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00058 ^ 1 * a02007 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a00864 ^ 1)
theorem ha03351 : a03351.IsHomogeneous 30 := by
  unfold a03351
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha00864.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha02007.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a03352 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a03348 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03339 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a03351 ^ 1)
theorem ha03352 : a03352.IsHomogeneous 30 := by
  unfold a03352
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha03348.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03339.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha03351.pow 1)))

@[irreducible]
def a03353 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a03352 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03341 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03350 ^ 1)
theorem ha03353 : a03353.IsHomogeneous 30 := by
  unfold a03353
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha03352.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03341.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03350.pow 1)))

@[irreducible]
def a03354 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00324 ^ 1)
theorem ha03354 : a03354.IsHomogeneous 6 := by
  unfold a03354
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00324.pow 1)))

@[irreducible]
def a03355 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00133 ^ 1)
theorem ha03355 : a03355.IsHomogeneous 6 := by
  unfold a03355
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00133.pow 1)))

@[irreducible]
def a03356 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03354 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a03355 ^ 1)
theorem ha03356 : a03356.IsHomogeneous 6 := by
  unfold a03356
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03354.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha03355.pow 1)))

@[irreducible]
def a03357 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00324 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6)
theorem ha03357 : a03357.IsHomogeneous 6 := by
  unfold a03357
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00324.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a03358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03354 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a03357 ^ 1)
theorem ha03358 : a03358.IsHomogeneous 6 := by
  unfold a03358
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03354.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha03357.pow 1)))

@[irreducible]
def a03359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03356 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03358 ^ 1)
theorem ha03359 : a03359.IsHomogeneous 6 := by
  unfold a03359
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03356.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03358.pow 1)))

@[irreducible]
def a03360 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00782 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a03357 ^ 1)
theorem ha03360 : a03360.IsHomogeneous 6 := by
  unfold a03360
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00782.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha03357.pow 1)))

@[irreducible]
def a03361 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03358 ^ 1) + (C ((21 : ℂ) / (1 : ℂ)) * a03360 ^ 1)
theorem ha03361 : a03361.IsHomogeneous 6 := by
  unfold a03361
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03358.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (1 : ℂ))).mul (ha03360.pow 1)))

@[irreducible]
def a03362 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03359 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03361 ^ 1)
theorem ha03362 : a03362.IsHomogeneous 6 := by
  unfold a03362
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03359.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03361.pow 1)))

@[irreducible]
def a03363 : Poly := (C ((-1 : ℂ) / (84 : ℂ)) * a03362 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03186 ^ 1)
theorem ha03363 : a03363.IsHomogeneous 6 := by
  unfold a03363
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (84 : ℂ))).mul (ha03362.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03186.pow 1)))

@[irreducible]
def a03364 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a03363 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a01575 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a01575 ^ 1)
theorem ha03364 : a03364.IsHomogeneous 18 := by
  unfold a03364
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha03363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a03365 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03349 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a03343 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03364 ^ 1)
theorem ha03365 : a03365.IsHomogeneous 30 := by
  unfold a03365
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03349.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha03343.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03364.pow 1)))

@[irreducible]
def a03366 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03350 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03344 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a03365 ^ 1)
theorem ha03366 : a03366.IsHomogeneous 36 := by
  unfold a03366
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03350.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03344.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha03365.pow 1)))

@[irreducible]
def a03367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03353 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03347 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03366 ^ 1)
theorem ha03367 : a03367.IsHomogeneous 36 := by
  unfold a03367
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03353.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03347.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03366.pow 1)))

@[irreducible]
def a03368 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a03367 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00003 ^ 5 * a00005 ^ 2 * a00014 ^ 1 * a03120 ^ 1)
theorem ha03368 : a03368.IsHomogeneous 48 := by
  unfold a03368
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha03367.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha03120.pow 1)))

@[irreducible]
def a03369 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a03367 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03368 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00003 ^ 5 * a00005 ^ 2 * a00014 ^ 1 * a03120 ^ 1)
theorem ha03369 : a03369.IsHomogeneous 48 := by
  unfold a03369
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha03367.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03368.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00005.pow 2)).mul (ha00014.pow 1)).mul (ha03120.pow 1)))

@[irreducible]
def a03370 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a03337 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03275 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00004 ^ 2 * a03369 ^ 1)
theorem ha03370 : a03370.IsHomogeneous 57 := by
  unfold a03370
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha03337.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03275.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha03369.pow 1)))

@[irreducible]
def a03371 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01473 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a00317 ^ 1 * a00577 ^ 1)
theorem ha03371 : a03371.IsHomogeneous 45 := by
  unfold a03371
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01473.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha00317.pow 1)).mul (ha00577.pow 1)))

@[irreducible]
def a03372 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00179 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00317 ^ 1 * a00577 ^ 1)
theorem ha03372 : a03372.IsHomogeneous 45 := by
  unfold a03372
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00179.pow 1)).mul (ha00865.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00317.pow 1)).mul (ha00577.pow 1)))

@[irreducible]
def a03373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03371 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a03372 ^ 1)
theorem ha03373 : a03373.IsHomogeneous 45 := by
  unfold a03373
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03371.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha03372.pow 1)))

@[irreducible]
def a03374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00040 ^ 1 * a02008 ^ 1)
theorem ha03374 : a03374.IsHomogeneous 39 := by
  unfold a03374
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a03375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03374 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03372 ^ 1)
theorem ha03375 : a03375.IsHomogeneous 45 := by
  unfold a03375
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03374.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03372.pow 1)))

@[irreducible]
def a03376 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03373 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a03375 ^ 1)
theorem ha03376 : a03376.IsHomogeneous 45 := by
  unfold a03376
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03373.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha03375.pow 1)))

@[irreducible]
def a03377 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a01473 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a03191 ^ 1)
theorem ha03377 : a03377.IsHomogeneous 45 := by
  unfold a03377
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha01473.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha03191.pow 1)))

@[irreducible]
def a03378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03371 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03377 ^ 1)
theorem ha03378 : a03378.IsHomogeneous 45 := by
  unfold a03378
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03371.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03377.pow 1)))

@[irreducible]
def a03379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03373 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03378 ^ 1)
theorem ha03379 : a03379.IsHomogeneous 45 := by
  unfold a03379
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03373.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03378.pow 1)))

@[irreducible]
def a03380 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03376 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03379 ^ 1)
theorem ha03380 : a03380.IsHomogeneous 45 := by
  unfold a03380
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03376.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03379.pow 1)))

@[irreducible]
def a03381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a03131 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03380 ^ 1)
theorem ha03381 : a03381.IsHomogeneous 50 := by
  unfold a03381
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha03131.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03380.pow 1)))

@[irreducible]
def a03382 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03381 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03380 ^ 1)
theorem ha03382 : a03382.IsHomogeneous 50 := by
  unfold a03382
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03381.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03380.pow 1)))

@[irreducible]
def a03383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00506 ^ 1 * a00655 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a00218 ^ 1 * a01327 ^ 1)
theorem ha03383 : a03383.IsHomogeneous 45 := by
  unfold a03383
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00506.pow 1)).mul (ha00655.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha00218.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a01617 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00506 ^ 1 * a00655 ^ 1)
theorem ha03384 : a03384.IsHomogeneous 45 := by
  unfold a03384
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha01617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00506.pow 1)).mul (ha00655.pow 1)))

@[irreducible]
def a03385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03383 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03384 ^ 1)
theorem ha03385 : a03385.IsHomogeneous 45 := by
  unfold a03385
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03383.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03384.pow 1)))

@[irreducible]
def a03386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a02935 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00218 ^ 1 * a01327 ^ 1)
theorem ha03386 : a03386.IsHomogeneous 42 := by
  unfold a03386
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha02935.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00218.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03387 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03383 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00003 ^ 3 * a03386 ^ 1)
theorem ha03387 : a03387.IsHomogeneous 45 := by
  unfold a03387
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03383.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00003.pow 3)).mul (ha03386.pow 1)))

@[irreducible]
def a03388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03385 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03387 ^ 1)
theorem ha03388 : a03388.IsHomogeneous 45 := by
  unfold a03388
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03385.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03387.pow 1)))

@[irreducible]
def a03389 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00042 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00130 ^ 1)
theorem ha03389 : a03389.IsHomogeneous 30 := by
  unfold a03389
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a03390 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00317 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1)
theorem ha03390 : a03390.IsHomogeneous 27 := by
  unfold a03390
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)))

@[irreducible]
def a03391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1)
theorem ha03391 : a03391.IsHomogeneous 24 := by
  unfold a03391
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)))

@[irreducible]
def a03392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03389 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a03391 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a03390 ^ 1)
theorem ha03392 : a03392.IsHomogeneous 30 := by
  unfold a03392
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03389.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha03391.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha03390.pow 1)))

@[irreducible]
def a03393 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00129 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00025 ^ 1 * a00317 ^ 1)
theorem ha03393 : a03393.IsHomogeneous 27 := by
  unfold a03393
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a03394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1)
theorem ha03394 : a03394.IsHomogeneous 30 := by
  unfold a03394
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a03395 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03389 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a03394 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a03393 ^ 1)
theorem ha03395 : a03395.IsHomogeneous 30 := by
  unfold a03395
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03389.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha03394.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha03393.pow 1)))

@[irreducible]
def a03396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00025 ^ 1 * a00865 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00317 ^ 1)
theorem ha03396 : a03396.IsHomogeneous 27 := by
  unfold a03396
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00025.pow 1)).mul (ha00865.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a03397 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03390 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03393 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03396 ^ 1)
theorem ha03397 : a03397.IsHomogeneous 27 := by
  unfold a03397
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03390.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03393.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03396.pow 1)))

@[irreducible]
def a03398 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03392 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03395 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a03397 ^ 1)
theorem ha03398 : a03398.IsHomogeneous 30 := by
  unfold a03398
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03392.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03395.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha03397.pow 1)))

@[irreducible]
def a03399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00129 ^ 1)
theorem ha03399 : a03399.IsHomogeneous 27 := by
  unfold a03399
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00317.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)))

@[irreducible]
def a03400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00317 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00130 ^ 1 * a00317 ^ 1)
theorem ha03400 : a03400.IsHomogeneous 33 := by
  unfold a03400
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00130.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a03401 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03390 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a03399 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a03400 ^ 1)
theorem ha03401 : a03401.IsHomogeneous 33 := by
  unfold a03401
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03390.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha03399.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha03400.pow 1)))

@[irreducible]
def a03402 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00042 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00129 ^ 1)
theorem ha03402 : a03402.IsHomogeneous 30 := by
  unfold a03402
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a03403 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03402 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03391 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a03399 ^ 1)
theorem ha03403 : a03403.IsHomogeneous 30 := by
  unfold a03403
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03402.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03391.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha03399.pow 1)))

@[irreducible]
def a03404 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03392 ^ 1) + (C ((7 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a03403 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03401 ^ 1)
theorem ha03404 : a03404.IsHomogeneous 33 := by
  unfold a03404
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03392.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha03403.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03401.pow 1)))

@[irreducible]
def a03405 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00025 ^ 1 * a02008 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00865 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00130 ^ 1 * a00865 ^ 1)
theorem ha03405 : a03405.IsHomogeneous 33 := by
  unfold a03405
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03396 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a03405 ^ 1) + (C ((14 : ℂ) / (5 : ℂ)) * a03400 ^ 1)
theorem ha03406 : a03406.IsHomogeneous 33 := by
  unfold a03406
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03396.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha03405.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (5 : ℂ))).mul (ha03400.pow 1)))

@[irreducible]
def a03407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03397 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03401 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03406 ^ 1)
theorem ha03407 : a03407.IsHomogeneous 33 := by
  unfold a03407
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03397.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03401.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03406.pow 1)))

@[irreducible]
def a03408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03398 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03404 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a03407 ^ 1)
theorem ha03408 : a03408.IsHomogeneous 33 := by
  unfold a03408
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03398.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03404.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha03407.pow 1)))

@[irreducible]
def a03409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00133 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00649 ^ 1)
theorem ha03409 : a03409.IsHomogeneous 12 := by
  unfold a03409
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00649.pow 1)))

@[irreducible]
def a03410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00032 ^ 1)
theorem ha03410 : a03410.IsHomogeneous 6 := by
  unfold a03410
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00032.pow 1)))

@[irreducible]
def a03411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a03410 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03409 ^ 1)
theorem ha03411 : a03411.IsHomogeneous 12 := by
  unfold a03411
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha03410.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03409.pow 1)))

@[irreducible]
def a03412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00649 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a01607 ^ 1)
theorem ha03412 : a03412.IsHomogeneous 12 := by
  unfold a03412
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00649.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha01607.pow 1)))

@[irreducible]
def a03413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03409 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a03412 ^ 1)
theorem ha03413 : a03413.IsHomogeneous 12 := by
  unfold a03413
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03409.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha03412.pow 1)))

@[irreducible]
def a03414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03411 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03413 ^ 1)
theorem ha03414 : a03414.IsHomogeneous 12 := by
  unfold a03414
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03411.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03413.pow 1)))

@[irreducible]
def a03415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1) + (C ((7 : ℂ) / (8 : ℂ)) * a00324 ^ 2)
theorem ha03415 : a03415.IsHomogeneous 12 := by
  unfold a03415
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (8 : ℂ))).mul (ha00324.pow 2)))

@[irreducible]
def a03416 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00629 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a03415 ^ 1)
theorem ha03416 : a03416.IsHomogeneous 12 := by
  unfold a03416
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00629.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha03415.pow 1)))

@[irreducible]
def a03417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03415 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a03416 ^ 1)
theorem ha03417 : a03417.IsHomogeneous 12 := by
  unfold a03417
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03415.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha03416.pow 1)))

@[irreducible]
def a03418 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01607 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a03417 ^ 1)
theorem ha03418 : a03418.IsHomogeneous 18 := by
  unfold a03418
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01607.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha03417.pow 1)))

@[irreducible]
def a03419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03412 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a03418 ^ 1)
theorem ha03419 : a03419.IsHomogeneous 18 := by
  unfold a03419
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03412.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha03418.pow 1)))

@[irreducible]
def a03420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03413 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a03419 ^ 1)
theorem ha03420 : a03420.IsHomogeneous 18 := by
  unfold a03420
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03413.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha03419.pow 1)))

@[irreducible]
def a03421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03414 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03420 ^ 1)
theorem ha03421 : a03421.IsHomogeneous 18 := by
  unfold a03421
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03414.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03420.pow 1)))

@[irreducible]
def a03422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (24 : ℂ)) * a00324 ^ 1 * a00574 ^ 1)
theorem ha03422 : a03422.IsHomogeneous 18 := by
  unfold a03422
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (24 : ℂ))).mul (ha00324.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a03423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00133 ^ 1 * a01469 ^ 1) + (C ((7 : ℂ) / (8 : ℂ)) * a00324 ^ 1 * a00574 ^ 1)
theorem ha03423 : a03423.IsHomogeneous 18 := by
  unfold a03423
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00133.pow 1)).mul (ha01469.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (8 : ℂ))).mul (ha00324.pow 1)).mul (ha00574.pow 1)))

@[irreducible]
def a03424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03422 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03423 ^ 1)
theorem ha03424 : a03424.IsHomogeneous 18 := by
  unfold a03424
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03422.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03423.pow 1)))

@[irreducible]
def a03425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00025 ^ 1)
theorem ha03425 : a03425.IsHomogeneous 6 := by
  unfold a03425
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00025.pow 1)))

@[irreducible]
def a03426 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a03425 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03422 ^ 1)
theorem ha03426 : a03426.IsHomogeneous 18 := by
  unfold a03426
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha03425.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03422.pow 1)))

@[irreducible]
def a03427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03424 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03426 ^ 1)
theorem ha03427 : a03427.IsHomogeneous 18 := by
  unfold a03427
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03424.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03426.pow 1)))

@[irreducible]
def a03428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a03186 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00133 ^ 1 * a01469 ^ 1)
theorem ha03428 : a03428.IsHomogeneous 12 := by
  unfold a03428
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha03186.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00133.pow 1)).mul (ha01469.pow 1)))

@[irreducible]
def a03429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03428 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a03423 ^ 1)
theorem ha03429 : a03429.IsHomogeneous 18 := by
  unfold a03429
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03428.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha03423.pow 1)))

@[irreducible]
def a03430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03424 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a03429 ^ 1)
theorem ha03430 : a03430.IsHomogeneous 18 := by
  unfold a03430
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03424.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha03429.pow 1)))

@[irreducible]
def a03431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03427 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03430 ^ 1)
theorem ha03431 : a03431.IsHomogeneous 18 := by
  unfold a03431
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03427.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03430.pow 1)))

@[irreducible]
def a03432 : Poly := (C ((-1 : ℂ) / (162 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03421 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03408 ^ 1) + (C ((7 : ℂ) / (30 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03431 ^ 1)
theorem ha03432 : a03432.IsHomogeneous 33 := by
  unfold a03432
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (162 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03421.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03408.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (30 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03431.pow 1)))

@[irreducible]
def a03433 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a01617 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a03432 ^ 1)
theorem ha03433 : a03433.IsHomogeneous 39 := by
  unfold a03433
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha01617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha03432.pow 1)))

@[irreducible]
def a03434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03433 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03384 ^ 1)
theorem ha03434 : a03434.IsHomogeneous 45 := by
  unfold a03434
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03433.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03384.pow 1)))

@[irreducible]
def a03435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03385 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03434 ^ 1)
theorem ha03435 : a03435.IsHomogeneous 45 := by
  unfold a03435
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03385.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03434.pow 1)))

@[irreducible]
def a03436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03388 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03435 ^ 1)
theorem ha03436 : a03436.IsHomogeneous 45 := by
  unfold a03436
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03388.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03435.pow 1)))

@[irreducible]
def a03437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a03131 ^ 1) + (C ((8 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03436 ^ 1)
theorem ha03437 : a03437.IsHomogeneous 50 := by
  unfold a03437
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha03131.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03436.pow 1)))

@[irreducible]
def a03438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03381 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03437 ^ 1)
theorem ha03438 : a03438.IsHomogeneous 50 := by
  unfold a03438
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03381.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03437.pow 1)))

@[irreducible]
def a03439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03382 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03438 ^ 1)
theorem ha03439 : a03439.IsHomogeneous 50 := by
  unfold a03439
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03382.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03438.pow 1)))

@[irreducible]
def a03440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03382 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03380 ^ 1)
theorem ha03440 : a03440.IsHomogeneous 50 := by
  unfold a03440
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03382.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03380.pow 1)))

@[irreducible]
def a03441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03439 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03440 ^ 1)
theorem ha03441 : a03441.IsHomogeneous 50 := by
  unfold a03441
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03439.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03440.pow 1)))

@[irreducible]
def a03442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a00317 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00547 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00129 ^ 1 * a00168 ^ 1)
theorem ha03442 : a03442.IsHomogeneous 45 := by
  unfold a03442
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a03443 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00168 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00547 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00168 ^ 1)
theorem ha03443 : a03443.IsHomogeneous 42 := by
  unfold a03443
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00168.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00547.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00168.pow 1)))

@[irreducible]
def a03444 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00547 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00130 ^ 1 * a01412 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00547 ^ 1)
theorem ha03444 : a03444.IsHomogeneous 45 := by
  unfold a03444
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00547.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a03445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03442 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a03444 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a03443 ^ 1)
theorem ha03445 : a03445.IsHomogeneous 45 := by
  unfold a03445
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03442.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha03444.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha03443.pow 1)))

@[irreducible]
def a03446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00168 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00317 ^ 1)
theorem ha03446 : a03446.IsHomogeneous 33 := by
  unfold a03446
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a03447 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00168 ^ 1 * a00317 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00037 ^ 1 * a00317 ^ 1)
theorem ha03447 : a03447.IsHomogeneous 39 := by
  unfold a03447
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00317.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a03448 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03447 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03442 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03446 ^ 1)
theorem ha03448 : a03448.IsHomogeneous 45 := by
  unfold a03448
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03447.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03442.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03446.pow 1)))

@[irreducible]
def a03449 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00168 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00042 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00037 ^ 1 * a00129 ^ 1)
theorem ha03449 : a03449.IsHomogeneous 36 := by
  unfold a03449
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00042.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a03450 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03449 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03443 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03446 ^ 1)
theorem ha03450 : a03450.IsHomogeneous 42 := by
  unfold a03450
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03449.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03443.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03446.pow 1)))

@[irreducible]
def a03451 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03445 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03448 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a03450 ^ 1)
theorem ha03451 : a03451.IsHomogeneous 45 := by
  unfold a03451
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03445.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03448.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha03450.pow 1)))

@[irreducible]
def a03452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00129 ^ 1 * a01412 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a00547 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a00547 ^ 1)
theorem ha03452 : a03452.IsHomogeneous 45 := by
  unfold a03452
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha01412.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha00547.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a03453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00168 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00168 ^ 1 * a00317 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00317 ^ 1 * a00547 ^ 1)
theorem ha03453 : a03453.IsHomogeneous 45 := by
  unfold a03453
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00168.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00317.pow 1)).mul (ha00547.pow 1)))

@[irreducible]
def a03454 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03442 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03452 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03453 ^ 1)
theorem ha03454 : a03454.IsHomogeneous 45 := by
  unfold a03454
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03442.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03452.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03453.pow 1)))

@[irreducible]
def a03455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a03085 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a01412 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1 * a01412 ^ 1)
theorem ha03455 : a03455.IsHomogeneous 42 := by
  unfold a03455
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha03085.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha01412.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).mul (ha01412.pow 1)))

@[irreducible]
def a03456 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03444 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03452 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00003 ^ 3 * a03455 ^ 1)
theorem ha03456 : a03456.IsHomogeneous 45 := by
  unfold a03456
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03444.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03452.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00003.pow 3)).mul (ha03455.pow 1)))

@[irreducible]
def a03457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03445 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03454 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a03456 ^ 1)
theorem ha03457 : a03457.IsHomogeneous 45 := by
  unfold a03457
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03445.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03454.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha03456.pow 1)))

@[irreducible]
def a03458 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1 * a00865 ^ 1)
theorem ha03458 : a03458.IsHomogeneous 39 := by
  unfold a03458
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).mul (ha00865.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha02008.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a03459 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03447 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a03458 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03453 ^ 1)
theorem ha03459 : a03459.IsHomogeneous 45 := by
  unfold a03459
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03447.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha03458.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03453.pow 1)))

@[irreducible]
def a03460 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03448 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03454 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03459 ^ 1)
theorem ha03460 : a03460.IsHomogeneous 45 := by
  unfold a03460
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03448.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03454.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03459.pow 1)))

@[irreducible]
def a03461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03451 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03457 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03460 ^ 1)
theorem ha03461 : a03461.IsHomogeneous 45 := by
  unfold a03461
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03451.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03457.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03460.pow 1)))

@[irreducible]
def a03462 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a02989 ^ 1)
theorem ha03462 : a03462.IsHomogeneous 50 := by
  unfold a03462
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03461.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha02989.pow 1)))

@[irreducible]
def a03463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03462 ^ 1)
theorem ha03463 : a03463.IsHomogeneous 50 := by
  unfold a03463
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03461.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03462.pow 1)))

@[irreducible]
def a03464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a00621 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00155 ^ 1 * a00201 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a00506 ^ 1)
theorem ha03464 : a03464.IsHomogeneous 45 := by
  unfold a03464
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00621.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a00130 ^ 1 * a01327 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a00506 ^ 1)
theorem ha03465 : a03465.IsHomogeneous 45 := by
  unfold a03465
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00506.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03466 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00054 ^ 1 * a00506 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00155 ^ 1 * a00201 ^ 1)
theorem ha03466 : a03466.IsHomogeneous 42 := by
  unfold a03466
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00054.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a03467 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03464 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a03466 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a03465 ^ 1)
theorem ha03467 : a03467.IsHomogeneous 45 := by
  unfold a03467
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03464.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha03466.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha03465.pow 1)))

@[irreducible]
def a03468 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00621 ^ 1)
theorem ha03468 : a03468.IsHomogeneous 33 := by
  unfold a03468
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00201.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a03469 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00155 ^ 1 * a00621 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01555 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00621 ^ 1)
theorem ha03469 : a03469.IsHomogeneous 39 := by
  unfold a03469
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00621.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a03470 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03469 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03464 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03468 ^ 1)
theorem ha03470 : a03470.IsHomogeneous 45 := by
  unfold a03470
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03469.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03464.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03468.pow 1)))

@[irreducible]
def a03471 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00155 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00201 ^ 1)
theorem ha03471 : a03471.IsHomogeneous 36 := by
  unfold a03471
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a03472 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03471 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03466 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03468 ^ 1)
theorem ha03472 : a03472.IsHomogeneous 42 := by
  unfold a03472
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03471.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03466.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03468.pow 1)))

@[irreducible]
def a03473 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03467 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03470 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a03472 ^ 1)
theorem ha03473 : a03473.IsHomogeneous 45 := by
  unfold a03473
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03467.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03470.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha03472.pow 1)))

@[irreducible]
def a03474 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a00621 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00201 ^ 1 * a01327 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a00506 ^ 1)
theorem ha03474 : a03474.IsHomogeneous 45 := by
  unfold a03474
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha00621.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03475 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00155 ^ 1 * a01555 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00155 ^ 1 * a00621 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00506 ^ 1 * a00621 ^ 1)
theorem ha03475 : a03475.IsHomogeneous 45 := by
  unfold a03475
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha01555.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00155.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00506.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a03476 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03464 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03474 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a03475 ^ 1)
theorem ha03476 : a03476.IsHomogeneous 45 := by
  unfold a03476
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03464.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03474.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha03475.pow 1)))

@[irreducible]
def a03477 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00054 ^ 1 * a02935 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a01327 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00201 ^ 1 * a01327 ^ 1)
theorem ha03477 : a03477.IsHomogeneous 42 := by
  unfold a03477
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha02935.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha01327.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00201.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03478 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03465 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a03474 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00003 ^ 3 * a03477 ^ 1)
theorem ha03478 : a03478.IsHomogeneous 45 := by
  unfold a03478
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03465.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha03474.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00003.pow 3)).mul (ha03477.pow 1)))

@[irreducible]
def a03479 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03467 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03476 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a03478 ^ 1)
theorem ha03479 : a03479.IsHomogeneous 45 := by
  unfold a03479
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03467.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03476.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha03478.pow 1)))

@[irreducible]
def a03480 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00155 ^ 1 * a01555 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a03330 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a01555 ^ 1)
theorem ha03480 : a03480.IsHomogeneous 39 := by
  unfold a03480
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00155.pow 1)).mul (ha01555.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha03330.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a03481 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03469 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a03480 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a03475 ^ 1)
theorem ha03481 : a03481.IsHomogeneous 45 := by
  unfold a03481
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03469.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha03480.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha03475.pow 1)))

@[irreducible]
def a03482 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03470 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03476 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03481 ^ 1)
theorem ha03482 : a03482.IsHomogeneous 45 := by
  unfold a03482
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03470.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03476.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03481.pow 1)))

@[irreducible]
def a03483 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03473 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03479 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03482 ^ 1)
theorem ha03483 : a03483.IsHomogeneous 45 := by
  unfold a03483
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03473.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03479.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03482.pow 1)))

@[irreducible]
def a03484 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03483 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a02989 ^ 1)
theorem ha03484 : a03484.IsHomogeneous 50 := by
  unfold a03484
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03483.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha02989.pow 1)))

@[irreducible]
def a03485 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03462 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03484 ^ 1)
theorem ha03485 : a03485.IsHomogeneous 50 := by
  unfold a03485
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03462.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03484.pow 1)))

@[irreducible]
def a03486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03463 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03485 ^ 1)
theorem ha03486 : a03486.IsHomogeneous 50 := by
  unfold a03486
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03485.pow 1)))

@[irreducible]
def a03487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03483 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03484 ^ 1)
theorem ha03487 : a03487.IsHomogeneous 50 := by
  unfold a03487
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03483.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03484.pow 1)))

@[irreducible]
def a03488 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03485 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03487 ^ 1)
theorem ha03488 : a03488.IsHomogeneous 50 := by
  unfold a03488
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03485.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03487.pow 1)))

@[irreducible]
def a03489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03486 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03488 ^ 1)
theorem ha03489 : a03489.IsHomogeneous 50 := by
  unfold a03489
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03486.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03488.pow 1)))

@[irreducible]
def a03490 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00171 ^ 1 * a00324 ^ 1) + (C ((4 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00133 ^ 1 * a00555 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a00317 ^ 1)
theorem ha03490 : a03490.IsHomogeneous 45 := by
  unfold a03490
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a03491 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00171 ^ 1 * a00324 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00324 ^ 1 * a00555 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00042 ^ 1 * a00171 ^ 1)
theorem ha03491 : a03491.IsHomogeneous 45 := by
  unfold a03491
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a03492 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00133 ^ 1 * a00555 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a00555 ^ 1)
theorem ha03492 : a03492.IsHomogeneous 42 := by
  unfold a03492
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a03493 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03490 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03491 ^ 1) + (C ((10 : ℂ) / (63 : ℂ)) * a00003 ^ 3 * a03492 ^ 1)
theorem ha03493 : a03493.IsHomogeneous 45 := by
  unfold a03493
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03490.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03491.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (63 : ℂ))).mul (ha00003.pow 3)).mul (ha03492.pow 1)))

@[irreducible]
def a03494 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1 * a00324 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00171 ^ 1 * a00324 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1)
theorem ha03494 : a03494.IsHomogeneous 39 := by
  unfold a03494
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00171.pow 1)).mul (ha00324.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a03495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00133 ^ 1 * a00171 ^ 1 * a00317 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00317 ^ 1 * a00324 ^ 1)
theorem ha03495 : a03495.IsHomogeneous 39 := by
  unfold a03495
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00317.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a03496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03494 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a00014 ^ 1 * a03495 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a03490 ^ 1)
theorem ha03496 : a03496.IsHomogeneous 45 := by
  unfold a03496
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03494.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha00014.pow 1)).mul (ha03495.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha03490.pow 1)))

@[irreducible]
def a03497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00171 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1)
theorem ha03497 : a03497.IsHomogeneous 36 := by
  unfold a03497
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00171.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a03498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03494 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03497 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a03491 ^ 1)
theorem ha03498 : a03498.IsHomogeneous 45 := by
  unfold a03498
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03494.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03497.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha03491.pow 1)))

@[irreducible]
def a03499 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03493 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a03496 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a03498 ^ 1)
theorem ha03499 : a03499.IsHomogeneous 45 := by
  unfold a03499
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03493.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha03496.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha03498.pow 1)))

@[irreducible]
def a03500 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00129 ^ 1 * a01429 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00317 ^ 1 * a00555 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00133 ^ 1 * a00555 ^ 1)
theorem ha03500 : a03500.IsHomogeneous 39 := by
  unfold a03500
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha01429.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00317.pow 1)).mul (ha00555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a03501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00171 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00171 ^ 1 * a00317 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00317 ^ 1 * a00555 ^ 1)
theorem ha03501 : a03501.IsHomogeneous 45 := by
  unfold a03501
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha00865.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00171.pow 1)).mul (ha00317.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00317.pow 1)).mul (ha00555.pow 1)))

@[irreducible]
def a03502 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03490 ^ 1) + (C ((10 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a03500 ^ 1) + (C ((10 : ℂ) / (21 : ℂ)) * a03501 ^ 1)
theorem ha03502 : a03502.IsHomogeneous 45 := by
  unfold a03502
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03490.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha03500.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (21 : ℂ))).mul (ha03501.pow 1)))

@[irreducible]
def a03503 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00042 ^ 1 * a03116 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a01429 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00032 ^ 1 * a00129 ^ 1 * a01429 ^ 1)
theorem ha03503 : a03503.IsHomogeneous 42 := by
  unfold a03503
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00042.pow 1)).mul (ha03116.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha01429.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00032.pow 1)).mul (ha00129.pow 1)).mul (ha01429.pow 1)))

@[irreducible]
def a03504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03492 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a03503 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03500 ^ 1)
theorem ha03504 : a03504.IsHomogeneous 42 := by
  unfold a03504
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03492.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha03503.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03500.pow 1)))

@[irreducible]
def a03505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03493 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03502 ^ 1) + (C ((10 : ℂ) / (63 : ℂ)) * a00003 ^ 3 * a03504 ^ 1)
theorem ha03505 : a03505.IsHomogeneous 45 := by
  unfold a03505
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03493.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03502.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (63 : ℂ))).mul (ha00003.pow 3)).mul (ha03504.pow 1)))

@[irreducible]
def a03506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1 * a00865 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a02008 ^ 1)
theorem ha03506 : a03506.IsHomogeneous 39 := by
  unfold a03506
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)).mul (ha00865.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a03507 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03495 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03506 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03501 ^ 1)
theorem ha03507 : a03507.IsHomogeneous 45 := by
  unfold a03507
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03495.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03506.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03501.pow 1)))

@[irreducible]
def a03508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03496 ^ 1) + (C ((4 : ℂ) / (21 : ℂ)) * a03507 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a03502 ^ 1)
theorem ha03508 : a03508.IsHomogeneous 45 := by
  unfold a03508
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03496.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (21 : ℂ))).mul (ha03507.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha03502.pow 1)))

@[irreducible]
def a03509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03499 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03505 ^ 1) + (C ((5 : ℂ) / (6 : ℂ)) * a03508 ^ 1)
theorem ha03509 : a03509.IsHomogeneous 45 := by
  unfold a03509
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03499.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03505.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (6 : ℂ))).mul (ha03508.pow 1)))

@[irreducible]
def a03510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a00632 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00207 ^ 1 * a00324 ^ 1) + (C ((12 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00506 ^ 1)
theorem ha03510 : a03510.IsHomogeneous 30 := by
  unfold a03510
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03511 : Poly := (C ((-8 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (21 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00133 ^ 1 * a01327 ^ 1)
theorem ha03511 : a03511.IsHomogeneous 30 := by
  unfold a03511
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00506.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (21 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03512 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00058 ^ 1 * a00155 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a00506 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a00207 ^ 1 * a00324 ^ 1)
theorem ha03512 : a03512.IsHomogeneous 30 := by
  unfold a03512
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha00506.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a03513 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a03511 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03510 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03512 ^ 1)
theorem ha03513 : a03513.IsHomogeneous 30 := by
  unfold a03513
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha03511.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03510.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03512.pow 1)))

@[irreducible]
def a03514 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00207 ^ 1 * a00324 ^ 1) + (C ((7 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00207 ^ 1)
theorem ha03514 : a03514.IsHomogeneous 24 := by
  unfold a03514
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00207.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a03515 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00155 ^ 1 * a00632 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00133 ^ 1 * a01575 ^ 1) + (C ((21 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00324 ^ 1 * a00632 ^ 1)
theorem ha03515 : a03515.IsHomogeneous 24 := by
  unfold a03515
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a03516 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03514 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a03515 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03510 ^ 1)
theorem ha03516 : a03516.IsHomogeneous 30 := by
  unfold a03516
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03514.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha03515.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03510.pow 1)))

@[irreducible]
def a03517 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00155 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00058 ^ 1)
theorem ha03517 : a03517.IsHomogeneous 18 := by
  unfold a03517
  exact (((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)))

@[irreducible]
def a03518 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03517 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03514 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03512 ^ 1)
theorem ha03518 : a03518.IsHomogeneous 30 := by
  unfold a03518
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03517.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03514.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03512.pow 1)))

@[irreducible]
def a03519 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03513 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03516 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03518 ^ 1)
theorem ha03519 : a03519.IsHomogeneous 30 := by
  unfold a03519
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03513.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03516.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03518.pow 1)))

@[irreducible]
def a03520 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00506 ^ 1 * a00632 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00207 ^ 1 * a01327 ^ 1) + (C ((2 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00506 ^ 1)
theorem ha03520 : a03520.IsHomogeneous 30 := by
  unfold a03520
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha01327.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00506.pow 1)))

@[irreducible]
def a03521 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a00155 ^ 1 * a00632 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00506 ^ 1 * a00632 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1 * a00155 ^ 1 * a01575 ^ 1)
theorem ha03521 : a03521.IsHomogeneous 30 := by
  unfold a03521
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha00155.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00506.pow 1)).mul (ha00632.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a03522 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03510 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03521 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a03520 ^ 1)
theorem ha03522 : a03522.IsHomogeneous 30 := by
  unfold a03522
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03521.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha03520.pow 1)))

@[irreducible]
def a03523 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00032 ^ 1 * a00207 ^ 1 * a01327 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00058 ^ 1 * a02935 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00058 ^ 1 * a00133 ^ 1 * a01327 ^ 1)
theorem ha03523 : a03523.IsHomogeneous 24 := by
  unfold a03523
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00032.pow 1)).mul (ha00207.pow 1)).mul (ha01327.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha02935.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha01327.pow 1)))

@[irreducible]
def a03524 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a03520 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03511 ^ 1) + (C ((5 : ℂ) / (42 : ℂ)) * a00003 ^ 6 * a03523 ^ 1)
theorem ha03524 : a03524.IsHomogeneous 30 := by
  unfold a03524
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha03520.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03511.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (42 : ℂ))).mul (ha00003.pow 6)).mul (ha03523.pow 1)))

@[irreducible]
def a03525 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a03524 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03513 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03522 ^ 1)
theorem ha03525 : a03525.IsHomogeneous 30 := by
  unfold a03525
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha03524.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03513.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03522.pow 1)))

@[irreducible]
def a03526 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00133 ^ 1 * a01575 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00155 ^ 1 * a01575 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a03363 ^ 1)
theorem ha03526 : a03526.IsHomogeneous 18 := by
  unfold a03526
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)).mul (ha01575.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00155.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha03363.pow 1)))

@[irreducible]
def a03527 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03515 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03521 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a03526 ^ 1)
theorem ha03527 : a03527.IsHomogeneous 30 := by
  unfold a03527
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03515.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03521.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha03526.pow 1)))

@[irreducible]
def a03528 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03516 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03522 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03527 ^ 1)
theorem ha03528 : a03528.IsHomogeneous 30 := by
  unfold a03528
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03516.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03522.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03527.pow 1)))

@[irreducible]
def a03529 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03519 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03525 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03528 ^ 1)
theorem ha03529 : a03529.IsHomogeneous 30 := by
  unfold a03529
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03519.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03525.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03528.pow 1)))

@[irreducible]
def a03530 : Poly := (C ((-1 : ℂ) / (1458 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03529 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03509 ^ 1)
theorem ha03530 : a03530.IsHomogeneous 45 := by
  unfold a03530
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1458 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03529.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03509.pow 1)))

@[irreducible]
def a03531 : Poly := (C ((-1 : ℂ) / (1458 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03529 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03509 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03530 ^ 1)
theorem ha03531 : a03531.IsHomogeneous 45 := by
  unfold a03531
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1458 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03529.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03509.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03530.pow 1)))

@[irreducible]
def a03532 : Poly := (C ((-1 : ℂ) / (729 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03529 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03530 ^ 1)
theorem ha03532 : a03532.IsHomogeneous 45 := by
  unfold a03532
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (729 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03529.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03530.pow 1)))

@[irreducible]
def a03533 : Poly := (C ((-1 : ℂ) / (486 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03529 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03531 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a03532 ^ 1)
theorem ha03533 : a03533.IsHomogeneous 45 := by
  unfold a03533
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (486 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03529.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03531.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha03532.pow 1)))

@[irreducible]
def a03534 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a03489 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03441 ^ 1) + (C ((14 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a03533 ^ 1)
theorem ha03534 : a03534.IsHomogeneous 50 := by
  unfold a03534
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha03489.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03441.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((14 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha03533.pow 1)))

@[irreducible]
def a03535 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a00864 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00316 ^ 1 * a00655 ^ 1)
theorem ha03535 : a03535.IsHomogeneous 48 := by
  unfold a03535
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha00864.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).mul (ha00655.pow 1)))

@[irreducible]
def a03536 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01617 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00316 ^ 1 * a00655 ^ 1)
theorem ha03536 : a03536.IsHomogeneous 39 := by
  unfold a03536
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00316.pow 1)).mul (ha00655.pow 1)))

@[irreducible]
def a03537 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03535 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a03536 ^ 1)
theorem ha03537 : a03537.IsHomogeneous 48 := by
  unfold a03537
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03535.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha03536.pow 1)))

@[irreducible]
def a03538 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a02007 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00218 ^ 1 * a00864 ^ 1)
theorem ha03538 : a03538.IsHomogeneous 48 := by
  unfold a03538
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha02007.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00218.pow 1)).mul (ha00864.pow 1)))

@[irreducible]
def a03539 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03535 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a03538 ^ 1)
theorem ha03539 : a03539.IsHomogeneous 48 := by
  unfold a03539
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03535.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha03538.pow 1)))

@[irreducible]
def a03540 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03537 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03539 ^ 1)
theorem ha03540 : a03540.IsHomogeneous 48 := by
  unfold a03540
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03537.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03539.pow 1)))

@[irreducible]
def a03541 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a01617 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a03432 ^ 1)
theorem ha03541 : a03541.IsHomogeneous 39 := by
  unfold a03541
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha01617.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha03432.pow 1)))

@[irreducible]
def a03542 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a03536 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03541 ^ 1)
theorem ha03542 : a03542.IsHomogeneous 45 := by
  unfold a03542
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha03536.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03541.pow 1)))

@[irreducible]
def a03543 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03537 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03542 ^ 1)
theorem ha03543 : a03543.IsHomogeneous 51 := by
  unfold a03543
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03537.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03542.pow 1)))

@[irreducible]
def a03544 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03543 ^ 1)
theorem ha03544 : a03544.IsHomogeneous 51 := by
  unfold a03544
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03543.pow 1)))

@[irreducible]
def a03545 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03270 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a03544 ^ 1)
theorem ha03545 : a03545.IsHomogeneous 51 := by
  unfold a03545
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03270.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha03544.pow 1)))

@[irreducible]
def a03546 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03270 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03545 ^ 1)
theorem ha03546 : a03546.IsHomogeneous 51 := by
  unfold a03546
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03270.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03545.pow 1)))

@[irreducible]
def a03547 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03270 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03546 ^ 1)
theorem ha03547 : a03547.IsHomogeneous 51 := by
  unfold a03547
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03270.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03546.pow 1)))

@[irreducible]
def a03548 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03544 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a03545 ^ 1)
theorem ha03548 : a03548.IsHomogeneous 51 := by
  unfold a03548
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03544.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha03545.pow 1)))

@[irreducible]
def a03549 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03546 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a03548 ^ 1)
theorem ha03549 : a03549.IsHomogeneous 51 := by
  unfold a03549
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03546.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha03548.pow 1)))

@[irreducible]
def a03550 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03547 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03549 ^ 1)
theorem ha03550 : a03550.IsHomogeneous 51 := by
  unfold a03550
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03547.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03549.pow 1)))

@[irreducible]
def a03551 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03270 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03547 ^ 1)
theorem ha03551 : a03551.IsHomogeneous 51 := by
  unfold a03551
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03270.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03547.pow 1)))

@[irreducible]
def a03552 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03550 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03551 ^ 1)
theorem ha03552 : a03552.IsHomogeneous 51 := by
  unfold a03552
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03550.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03551.pow 1)))

@[irreducible]
def a03553 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03295 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03334 ^ 1)
theorem ha03553 : a03553.IsHomogeneous 51 := by
  unfold a03553
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03295.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03334.pow 1)))

@[irreducible]
def a03554 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03553 ^ 1)
theorem ha03554 : a03554.IsHomogeneous 51 := by
  unfold a03554
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03295.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03553.pow 1)))

@[irreducible]
def a03555 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03554 ^ 1)
theorem ha03555 : a03555.IsHomogeneous 51 := by
  unfold a03555
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03295.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03554.pow 1)))

@[irreducible]
def a03556 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03334 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a03553 ^ 1)
theorem ha03556 : a03556.IsHomogeneous 51 := by
  unfold a03556
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03334.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha03553.pow 1)))

@[irreducible]
def a03557 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03554 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03556 ^ 1)
theorem ha03557 : a03557.IsHomogeneous 51 := by
  unfold a03557
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03554.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03556.pow 1)))

@[irreducible]
def a03558 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03555 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03557 ^ 1)
theorem ha03558 : a03558.IsHomogeneous 51 := by
  unfold a03558
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03555.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03557.pow 1)))

@[irreducible]
def a03559 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03334 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03556 ^ 1)
theorem ha03559 : a03559.IsHomogeneous 51 := by
  unfold a03559
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03334.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03556.pow 1)))

@[irreducible]
def a03560 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03557 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a03559 ^ 1)
theorem ha03560 : a03560.IsHomogeneous 51 := by
  unfold a03560
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03557.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha03559.pow 1)))

@[irreducible]
def a03561 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03558 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03560 ^ 1)
theorem ha03561 : a03561.IsHomogeneous 51 := by
  unfold a03561
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03558.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03560.pow 1)))

@[irreducible]
def a03562 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03367 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a03561 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03552 ^ 1)
theorem ha03562 : a03562.IsHomogeneous 51 := by
  unfold a03562
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03367.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha03561.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03552.pow 1)))

@[irreducible]
def a03563 : Poly := (C ((-27 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00012 ^ 5 * a00014 ^ 2 * a02990 ^ 1) + (C ((-3 : ℂ) / (4 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 3 * a00012 ^ 3 * a03250 ^ 1) + (C ((-1 : ℂ) / (144 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a03370 ^ 1) + (C ((-1 : ℂ) / (34560 : ℂ)) * a00000 ^ 1 * a00001 ^ 18 * a00002 ^ 6 * a00004 ^ 6 * a00005 ^ 6 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 2 * a00012 ^ 4 * a00014 ^ 1 * a03121 ^ 1) + (C ((1 : ℂ) / (1536 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 6 * a00003 ^ 2 * a00004 ^ 5 * a00005 ^ 5 * a00012 ^ 1 * a03534 ^ 1)
theorem ha03563 : a03563.IsHomogeneous 88 := by
  unfold a03563
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00012.pow 5)).mul (ha00014.pow 2)).mul (ha02990.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00012.pow 3)).mul (ha03250.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha03370.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (34560 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 18)).mul (ha00002.pow 6)).mul (ha00004.pow 6)).mul (ha00005.pow 6)).mul (ha03562.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00012.pow 4)).mul (ha00014.pow 1)).mul (ha03121.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1536 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 6)).mul (ha00003.pow 2)).mul (ha00004.pow 5)).mul (ha00005.pow 5)).mul (ha00012.pow 1)).mul (ha03534.pow 1)))

@[irreducible]
def a03564 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00014 ^ 1 * a00101 ^ 1 * a03563 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a01703 ^ 1)
theorem ha03564 : a03564.IsHomogeneous 174 := by
  unfold a03564
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00014.pow 1)).mul (ha00101.pow 1)).mul (ha03563.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha01703.pow 1)))

@[irreducible]
def a03565 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a03564 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a02925 ^ 1)
theorem ha03565 : a03565.IsHomogeneous 180 := by
  unfold a03565
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha03564.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha02925.pow 1)))

@[irreducible]
def a03566 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02925 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a03565 ^ 1)
theorem ha03566 : a03566.IsHomogeneous 180 := by
  unfold a03566
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02925.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha03565.pow 1)))

@[irreducible]
def a03567 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a03566 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a01705 ^ 1)
theorem ha03567 : a03567.IsHomogeneous 260 := by
  unfold a03567
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha03566.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha01705.pow 1)))

@[irreducible]
def a03568 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 1 * a00101 ^ 1 * a03567 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02918 ^ 1)
theorem ha03568 : a03568.IsHomogeneous 340 := by
  unfold a03568
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 1)).mul (ha00101.pow 1)).mul (ha03567.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02918.pow 1)))

@[irreducible]
def a03569 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a02924 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03568 ^ 1)
theorem ha03569 : a03569.IsHomogeneous 340 := by
  unfold a03569
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02924.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03568.pow 1)))

@[irreducible]
def a03570 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a03569 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00295 ^ 1 * a01707 ^ 1)
theorem ha03570 : a03570.IsHomogeneous 723 := by
  unfold a03570
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha03569.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00295.pow 1)).mul (ha01707.pow 1)))

@[irreducible]
def a03571 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03570 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a02915 ^ 1)
theorem ha03571 : a03571.IsHomogeneous 977 := by
  unfold a03571
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03570.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha02915.pow 1)))

@[irreducible]
def a03572 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03571 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a02917 ^ 1)
theorem ha03572 : a03572.IsHomogeneous 1231 := by
  unfold a03572
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03571.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha02917.pow 1)))

@[irreducible]
def a03573 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00294 ^ 1 * a01871 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00795 ^ 1 * a00800 ^ 1)
theorem ha03573 : a03573.IsHomogeneous 915 := by
  unfold a03573
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00294.pow 1)).mul (ha01871.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00795.pow 1)).mul (ha00800.pow 1)))

@[irreducible]
def a03574 : Poly := (C ((-5 : ℂ) / (72 : ℂ)) * a00003 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00292 ^ 1 * a01880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00795 ^ 1 * a00800 ^ 1)
theorem ha03574 : a03574.IsHomogeneous 661 := by
  unfold a03574
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00292.pow 1)).mul (ha01880.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00795.pow 1)).mul (ha00800.pow 1)))

@[irreducible]
def a03575 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03573 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a03574 ^ 1)
theorem ha03575 : a03575.IsHomogeneous 915 := by
  unfold a03575
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03573.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha03574.pow 1)))

@[irreducible]
def a03576 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00291 ^ 1 * a01830 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a00778 ^ 1 * a00793 ^ 1)
theorem ha03576 : a03576.IsHomogeneous 902 := by
  unfold a03576
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00291.pow 1)).mul (ha01830.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha00778.pow 1)).mul (ha00793.pow 1)))

@[irreducible]
def a03577 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00778 ^ 1 * a00793 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00287 ^ 1 * a01868 ^ 1)
theorem ha03577 : a03577.IsHomogeneous 920 := by
  unfold a03577
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00778.pow 1)).mul (ha00793.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00287.pow 1)).mul (ha01868.pow 1)))

@[irreducible]
def a03578 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a03576 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00103 ^ 1 * a03577 ^ 1)
theorem ha03578 : a03578.IsHomogeneous 962 := by
  unfold a03578
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha03576.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00103.pow 1)).mul (ha03577.pow 1)))

@[irreducible]
def a03579 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00286 ^ 1 * a01739 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00734 ^ 1 * a00776 ^ 1)
theorem ha03579 : a03579.IsHomogeneous 479 := by
  unfold a03579
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00286.pow 1)).mul (ha01739.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00734.pow 1)).mul (ha00776.pow 1)))

@[irreducible]
def a03580 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00734 ^ 1 * a00776 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00271 ^ 1 * a01827 ^ 1)
theorem ha03580 : a03580.IsHomogeneous 569 := by
  unfold a03580
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00734.pow 1)).mul (ha00776.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00271.pow 1)).mul (ha01827.pow 1)))

@[irreducible]
def a03581 : Poly := (C ((-4 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a03579 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a03580 ^ 1)
theorem ha03581 : a03581.IsHomogeneous 624 := by
  unfold a03581
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha03579.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha03580.pow 1)))

@[irreducible]
def a03582 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00105 ^ 1 * a00724 ^ 1 * a00732 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00270 ^ 1 * a01726 ^ 1)
theorem ha03582 : a03582.IsHomogeneous 189 := by
  unfold a03582
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00105.pow 1)).mul (ha00724.pow 1)).mul (ha00732.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00270.pow 1)).mul (ha01726.pow 1)))

@[irreducible]
def a03583 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00724 ^ 1 * a00732 ^ 1) + (C ((5 : ℂ) / (48 : ℂ)) * a00105 ^ 1 * a00265 ^ 1 * a01736 ^ 1)
theorem ha03583 : a03583.IsHomogeneous 132 := by
  unfold a03583
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00724.pow 1)).mul (ha00732.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (48 : ℂ))).mul (ha00105.pow 1)).mul (ha00265.pow 1)).mul (ha01736.pow 1)))

end CycleQ2Concrete
