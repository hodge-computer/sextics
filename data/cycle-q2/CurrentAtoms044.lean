import Proposal.CurrentAtoms043

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a13056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13050 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13055 ^ 1)
theorem ha13056 : a13056.IsHomogeneous 48 := by
  unfold a13056
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13050.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13055.pow 1)))

@[irreducible]
def a13057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13051 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a13056 ^ 1)
theorem ha13057 : a13057.IsHomogeneous 48 := by
  unfold a13057
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13051.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha13056.pow 1)))

@[irreducible]
def a13058 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13057 ^ 1)
theorem ha13058 : a13058.IsHomogeneous 48 := by
  unfold a13058
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13057.pow 1)))

@[irreducible]
def a13059 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a07558 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00298 ^ 1 * a04086 ^ 1)
theorem ha13059 : a13059.IsHomogeneous 48 := by
  unfold a13059
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha07558.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00298.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a13060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13052 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a13059 ^ 1)
theorem ha13060 : a13060.IsHomogeneous 48 := by
  unfold a13060
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13052.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha13059.pow 1)))

@[irreducible]
def a13061 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13053 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a13060 ^ 1)
theorem ha13061 : a13061.IsHomogeneous 48 := by
  unfold a13061
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13053.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha13060.pow 1)))

@[irreducible]
def a13062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13061 ^ 1)
theorem ha13062 : a13062.IsHomogeneous 48 := by
  unfold a13062
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13061.pow 1)))

@[irreducible]
def a13063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13058 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13062 ^ 1)
theorem ha13063 : a13063.IsHomogeneous 48 := by
  unfold a13063
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13058.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13062.pow 1)))

@[irreducible]
def a13064 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a12998 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a07248 ^ 1)
theorem ha13064 : a13064.IsHomogeneous 48 := by
  unfold a13064
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha12998.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha07248.pow 1)))

@[irreducible]
def a13065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13055 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a13064 ^ 1)
theorem ha13065 : a13065.IsHomogeneous 48 := by
  unfold a13065
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13055.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha13064.pow 1)))

@[irreducible]
def a13066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13056 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13065 ^ 1)
theorem ha13066 : a13066.IsHomogeneous 48 := by
  unfold a13066
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13056.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13065.pow 1)))

@[irreducible]
def a13067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13057 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a13066 ^ 1)
theorem ha13067 : a13067.IsHomogeneous 48 := by
  unfold a13067
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13057.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha13066.pow 1)))

@[irreducible]
def a13068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13058 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13067 ^ 1)
theorem ha13068 : a13068.IsHomogeneous 48 := by
  unfold a13068
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13058.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13067.pow 1)))

@[irreducible]
def a13069 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13063 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13068 ^ 1)
theorem ha13069 : a13069.IsHomogeneous 48 := by
  unfold a13069
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13063.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13068.pow 1)))

@[irreducible]
def a13070 : Poly := (C ((-2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13069 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07297 ^ 1)
theorem ha13070 : a13070.IsHomogeneous 90 := by
  unfold a13070
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13069.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07297.pow 1)))

@[irreducible]
def a13071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13040 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a13070 ^ 1)
theorem ha13071 : a13071.IsHomogeneous 96 := by
  unfold a13071
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13040.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha13070.pow 1)))

@[irreducible]
def a13072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13041 ^ 1)
theorem ha13072 : a13072.IsHomogeneous 102 := by
  unfold a13072
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13041.pow 1)))

@[irreducible]
def a13073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13042 ^ 1) + (C ((243 : ℂ) / (5 : ℂ)) * a13072 ^ 1)
theorem ha13073 : a13073.IsHomogeneous 102 := by
  unfold a13073
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((243 : ℂ) / (5 : ℂ))).mul (ha13072.pow 1)))

@[irreducible]
def a13074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13043 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13073 ^ 1)
theorem ha13074 : a13074.IsHomogeneous 102 := by
  unfold a13074
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13043.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13073.pow 1)))

@[irreducible]
def a13075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13048 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13074 ^ 1)
theorem ha13075 : a13075.IsHomogeneous 102 := by
  unfold a13075
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13048.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13074.pow 1)))

@[irreducible]
def a13076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a13075 ^ 1) + (C ((243 : ℂ) / (5 : ℂ)) * a00299 ^ 1 * a07302 ^ 1)
theorem ha13076 : a13076.IsHomogeneous 120 := by
  unfold a13076
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha13075.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((243 : ℂ) / (5 : ℂ))).mul (ha00299.pow 1)).mul (ha07302.pow 1)))

@[irreducible]
def a13077 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13025 ^ 1) + (C ((5 : ℂ) / (243 : ℂ)) * a13076 ^ 1)
theorem ha13077 : a13077.IsHomogeneous 120 := by
  unfold a13077
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (243 : ℂ))).mul (ha13076.pow 1)))

@[irreducible]
def a13078 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13026 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a13077 ^ 1)
theorem ha13078 : a13078.IsHomogeneous 120 := by
  unfold a13078
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13026.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha13077.pow 1)))

@[irreducible]
def a13079 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13027 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a13078 ^ 1)
theorem ha13079 : a13079.IsHomogeneous 120 := by
  unfold a13079
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13027.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha13078.pow 1)))

@[irreducible]
def a13080 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13028 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13079 ^ 1)
theorem ha13080 : a13080.IsHomogeneous 120 := by
  unfold a13080
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13028.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13079.pow 1)))

@[irreducible]
def a13081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13033 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13080 ^ 1)
theorem ha13081 : a13081.IsHomogeneous 120 := by
  unfold a13081
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13033.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13080.pow 1)))

@[irreducible]
def a13082 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13081 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a07307 ^ 1)
theorem ha13082 : a13082.IsHomogeneous 126 := by
  unfold a13082
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13081.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha07307.pow 1)))

@[irreducible]
def a13083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13082 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a13010 ^ 1)
theorem ha13083 : a13083.IsHomogeneous 132 := by
  unfold a13083
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13082.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha13010.pow 1)))

@[irreducible]
def a13084 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13083 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13011 ^ 1)
theorem ha13084 : a13084.IsHomogeneous 138 := by
  unfold a13084
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13083.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13011.pow 1)))

@[irreducible]
def a13085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13012 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a13084 ^ 1)
theorem ha13085 : a13085.IsHomogeneous 138 := by
  unfold a13085
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13012.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha13084.pow 1)))

@[irreducible]
def a13086 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13013 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13085 ^ 1)
theorem ha13086 : a13086.IsHomogeneous 138 := by
  unfold a13086
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13013.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13085.pow 1)))

@[irreducible]
def a13087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13018 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13086 ^ 1)
theorem ha13087 : a13087.IsHomogeneous 138 := by
  unfold a13087
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13018.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13086.pow 1)))

@[irreducible]
def a13088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a13087 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a07312 ^ 1)
theorem ha13088 : a13088.IsHomogeneous 171 := by
  unfold a13088
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha13087.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha07312.pow 1)))

@[irreducible]
def a13089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13088 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12983 ^ 1)
theorem ha13089 : a13089.IsHomogeneous 171 := by
  unfold a13089
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13088.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12983.pow 1)))

@[irreducible]
def a13090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13089 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12984 ^ 1)
theorem ha13090 : a13090.IsHomogeneous 171 := by
  unfold a13090
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13089.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12984.pow 1)))

@[irreducible]
def a13091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13090 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12985 ^ 1)
theorem ha13091 : a13091.IsHomogeneous 171 := by
  unfold a13091
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13090.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12985.pow 1)))

@[irreducible]
def a13092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13091 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a12986 ^ 1)
theorem ha13092 : a13092.IsHomogeneous 171 := by
  unfold a13092
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13091.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha12986.pow 1)))

@[irreducible]
def a13093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13092 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13003 ^ 1)
theorem ha13093 : a13093.IsHomogeneous 171 := by
  unfold a13093
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13092.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13003.pow 1)))

@[irreducible]
def a13094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a07317 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a13093 ^ 1)
theorem ha13094 : a13094.IsHomogeneous 231 := by
  unfold a13094
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha07317.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha13093.pow 1)))

@[irreducible]
def a13095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12970 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a13094 ^ 1)
theorem ha13095 : a13095.IsHomogeneous 291 := by
  unfold a13095
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12970.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha13094.pow 1)))

@[irreducible]
def a13096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12971 ^ 1) + (C ((5 : ℂ) / (162 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a13095 ^ 1)
theorem ha13096 : a13096.IsHomogeneous 354 := by
  unfold a13096
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12971.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (162 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha13095.pow 1)))

@[irreducible]
def a13097 : Poly := (C ((-1 : ℂ) / (10 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a13096 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12972 ^ 1)
theorem ha13097 : a13097.IsHomogeneous 414 := by
  unfold a13097
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (10 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha13096.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12972.pow 1)))

@[irreducible]
def a13098 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a13097 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12976 ^ 1)
theorem ha13098 : a13098.IsHomogeneous 474 := by
  unfold a13098
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha13097.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12976.pow 1)))

@[irreducible]
def a13099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01944 ^ 1 * a03945 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a01929 ^ 1 * a03971 ^ 1)
theorem ha13099 : a13099.IsHomogeneous 348 := by
  unfold a13099
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01944.pow 1)).mul (ha03945.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha01929.pow 1)).mul (ha03971.pow 1)))

@[irreducible]
def a13100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00833 ^ 1 * a07334 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a01944 ^ 1 * a03945 ^ 1)
theorem ha13100 : a13100.IsHomogeneous 372 := by
  unfold a13100
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00833.pow 1)).mul (ha07334.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha01944.pow 1)).mul (ha03945.pow 1)))

@[irreducible]
def a13101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13100 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a13099 ^ 1)
theorem ha13101 : a13101.IsHomogeneous 372 := by
  unfold a13101
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13100.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha13099.pow 1)))

@[irreducible]
def a13102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01929 ^ 1 * a03971 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00305 ^ 1 * a07373 ^ 1)
theorem ha13102 : a13102.IsHomogeneous 285 := by
  unfold a13102
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01929.pow 1)).mul (ha03971.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00305.pow 1)).mul (ha07373.pow 1)))

@[irreducible]
def a13103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13099 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a13102 ^ 1)
theorem ha13103 : a13103.IsHomogeneous 348 := by
  unfold a13103
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13099.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha13102.pow 1)))

@[irreducible]
def a13104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13101 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a13103 ^ 1)
theorem ha13104 : a13104.IsHomogeneous 372 := by
  unfold a13104
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13101.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha13103.pow 1)))

@[irreducible]
def a13105 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01944 ^ 1 * a03943 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a00305 ^ 1 * a03971 ^ 1)
theorem ha13105 : a13105.IsHomogeneous 282 := by
  unfold a13105
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01944.pow 1)).mul (ha03943.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00305.pow 1)).mul (ha03971.pow 1)))

@[irreducible]
def a13106 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00833 ^ 1 * a07331 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a01944 ^ 1 * a03943 ^ 1)
theorem ha13106 : a13106.IsHomogeneous 306 := by
  unfold a13106
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00833.pow 1)).mul (ha07331.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha01944.pow 1)).mul (ha03943.pow 1)))

@[irreducible]
def a13107 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13106 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a13105 ^ 1)
theorem ha13107 : a13107.IsHomogeneous 306 := by
  unfold a13107
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13106.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha13105.pow 1)))

@[irreducible]
def a13108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a03971 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a07373 ^ 1)
theorem ha13108 : a13108.IsHomogeneous 219 := by
  unfold a13108
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha03971.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha07373.pow 1)))

@[irreducible]
def a13109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13105 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a13108 ^ 1)
theorem ha13109 : a13109.IsHomogeneous 282 := by
  unfold a13109
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13105.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha13108.pow 1)))

@[irreducible]
def a13110 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13107 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a13109 ^ 1)
theorem ha13110 : a13110.IsHomogeneous 306 := by
  unfold a13110
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13107.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha13109.pow 1)))

@[irreducible]
def a13111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a01944 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a03971 ^ 1)
theorem ha13111 : a13111.IsHomogeneous 216 := by
  unfold a13111
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha01944.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha03971.pow 1)))

@[irreducible]
def a13112 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00833 ^ 1 * a07329 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a00305 ^ 1 * a01944 ^ 1)
theorem ha13112 : a13112.IsHomogeneous 240 := by
  unfold a13112
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00833.pow 1)).mul (ha07329.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha00305.pow 1)).mul (ha01944.pow 1)))

@[irreducible]
def a13113 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13112 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a13111 ^ 1)
theorem ha13113 : a13113.IsHomogeneous 240 := by
  unfold a13113
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13112.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha13111.pow 1)))

@[irreducible]
def a13114 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a01944 ^ 1)
theorem ha13114 : a13114.IsHomogeneous 174 := by
  unfold a13114
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha00833.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha01944.pow 1)))

@[irreducible]
def a13115 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 2)
theorem ha13115 : a13115.IsHomogeneous 132 := by
  unfold a13115
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 2)))

@[irreducible]
def a13116 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00833 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13115 ^ 1)
theorem ha13116 : a13116.IsHomogeneous 132 := by
  unfold a13116
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13115.pow 1)))

@[irreducible]
def a13117 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a13114 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a13116 ^ 1)
theorem ha13117 : a13117.IsHomogeneous 198 := by
  unfold a13117
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha13114.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha13116.pow 1)))

@[irreducible]
def a13118 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00833 ^ 1 * a07329 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a13117 ^ 1)
theorem ha13118 : a13118.IsHomogeneous 264 := by
  unfold a13118
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).mul (ha07329.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha13117.pow 1)))

@[irreducible]
def a13119 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a13112 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13118 ^ 1)
theorem ha13119 : a13119.IsHomogeneous 264 := by
  unfold a13119
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha13112.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13118.pow 1)))

@[irreducible]
def a13120 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a13113 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13119 ^ 1)
theorem ha13120 : a13120.IsHomogeneous 264 := by
  unfold a13120
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha13113.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13119.pow 1)))

@[irreducible]
def a13121 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00833 ^ 1 * a07331 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a13120 ^ 1)
theorem ha13121 : a13121.IsHomogeneous 330 := by
  unfold a13121
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).mul (ha07331.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha13120.pow 1)))

@[irreducible]
def a13122 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a13106 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13121 ^ 1)
theorem ha13122 : a13122.IsHomogeneous 330 := by
  unfold a13122
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha13106.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13121.pow 1)))

@[irreducible]
def a13123 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a13107 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13122 ^ 1)
theorem ha13123 : a13123.IsHomogeneous 330 := by
  unfold a13123
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha13107.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13122.pow 1)))

@[irreducible]
def a13124 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a13110 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13123 ^ 1)
theorem ha13124 : a13124.IsHomogeneous 330 := by
  unfold a13124
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha13110.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13123.pow 1)))

@[irreducible]
def a13125 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a00833 ^ 1 * a07334 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a13124 ^ 1)
theorem ha13125 : a13125.IsHomogeneous 396 := by
  unfold a13125
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha00833.pow 1)).mul (ha07334.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha13124.pow 1)))

@[irreducible]
def a13126 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a13100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13125 ^ 1)
theorem ha13126 : a13126.IsHomogeneous 396 := by
  unfold a13126
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha13100.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13125.pow 1)))

@[irreducible]
def a13127 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a13101 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13126 ^ 1)
theorem ha13127 : a13127.IsHomogeneous 396 := by
  unfold a13127
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha13101.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13126.pow 1)))

@[irreducible]
def a13128 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a13104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13127 ^ 1)
theorem ha13128 : a13128.IsHomogeneous 396 := by
  unfold a13128
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha13104.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13127.pow 1)))

@[irreducible]
def a13129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00831 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00865 ^ 1 * a01941 ^ 1)
theorem ha13129 : a13129.IsHomogeneous 147 := by
  unfold a13129
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00831.pow 1)).mul (ha02008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00865.pow 1)).mul (ha01941.pow 1)))

@[irreducible]
def a13130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00317 ^ 1 * a03967 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00865 ^ 1 * a01941 ^ 1)
theorem ha13130 : a13130.IsHomogeneous 153 := by
  unfold a13130
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00317.pow 1)).mul (ha03967.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00865.pow 1)).mul (ha01941.pow 1)))

@[irreducible]
def a13131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13130 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a13129 ^ 1)
theorem ha13131 : a13131.IsHomogeneous 153 := by
  unfold a13131
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha13129.pow 1)))

@[irreducible]
def a13132 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a04086 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00831 ^ 1 * a02008 ^ 1)
theorem ha13132 : a13132.IsHomogeneous 102 := by
  unfold a13132
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha04086.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00831.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a13133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13132 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13129 ^ 1)
theorem ha13133 : a13133.IsHomogeneous 147 := by
  unfold a13133
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13132.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13129.pow 1)))

@[irreducible]
def a13134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13131 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a13133 ^ 1)
theorem ha13134 : a13134.IsHomogeneous 153 := by
  unfold a13134
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13131.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha13133.pow 1)))

@[irreducible]
def a13135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a07368 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a03967 ^ 1)
theorem ha13135 : a13135.IsHomogeneous 156 := by
  unfold a13135
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha07368.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha03967.pow 1)))

@[irreducible]
def a13136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13135 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a13130 ^ 1)
theorem ha13136 : a13136.IsHomogeneous 159 := by
  unfold a13136
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13135.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha13130.pow 1)))

@[irreducible]
def a13137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13136 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a13131 ^ 1)
theorem ha13137 : a13137.IsHomogeneous 159 := by
  unfold a13137
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13136.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha13131.pow 1)))

@[irreducible]
def a13138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13137 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a13134 ^ 1)
theorem ha13138 : a13138.IsHomogeneous 159 := by
  unfold a13138
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13137.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha13134.pow 1)))

@[irreducible]
def a13139 : Poly := (C ((-5 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a07558 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04086 ^ 1)
theorem ha13139 : a13139.IsHomogeneous 60 := by
  unfold a13139
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha07558.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04086.pow 1)))

@[irreducible]
def a13140 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a13139 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13132 ^ 1)
theorem ha13140 : a13140.IsHomogeneous 102 := by
  unfold a13140
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13139.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13132.pow 1)))

@[irreducible]
def a13141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13140 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13133 ^ 1)
theorem ha13141 : a13141.IsHomogeneous 147 := by
  unfold a13141
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13140.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13133.pow 1)))

@[irreducible]
def a13142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13134 ^ 1) + (C ((2 : ℂ) / (15 : ℂ)) * a00014 ^ 1 * a13141 ^ 1)
theorem ha13142 : a13142.IsHomogeneous 153 := by
  unfold a13142
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13134.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (15 : ℂ))).mul (ha00014.pow 1)).mul (ha13141.pow 1)))

@[irreducible]
def a13143 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13138 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a13142 ^ 1)
theorem ha13143 : a13143.IsHomogeneous 159 := by
  unfold a13143
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13138.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha13142.pow 1)))

@[irreducible]
def a13144 : Poly := (C ((-2 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00829 ^ 1 * a03562 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a01702 ^ 1 * a01938 ^ 1)
theorem ha13144 : a13144.IsHomogeneous 141 := by
  unfold a13144
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00829.pow 1)).mul (ha03562.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha01702.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a13145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a03963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01702 ^ 1 * a01938 ^ 1)
theorem ha13145 : a13145.IsHomogeneous 138 := by
  unfold a13145
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha03963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01702.pow 1)).mul (ha01938.pow 1)))

@[irreducible]
def a13146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13145 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13144 ^ 1)
theorem ha13146 : a13146.IsHomogeneous 141 := by
  unfold a13146
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13145.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13144.pow 1)))

@[irreducible]
def a13147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00260 ^ 1 * a06725 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00829 ^ 1 * a03562 ^ 1)
theorem ha13147 : a13147.IsHomogeneous 135 := by
  unfold a13147
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha06725.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00829.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a13148 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00014 ^ 1 * a13147 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13144 ^ 1)
theorem ha13148 : a13148.IsHomogeneous 141 := by
  unfold a13148
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00014.pow 1)).mul (ha13147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13144.pow 1)))

@[irreducible]
def a13149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13146 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13148 ^ 1)
theorem ha13149 : a13149.IsHomogeneous 141 := by
  unfold a13149
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13146.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13148.pow 1)))

@[irreducible]
def a13150 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00712 ^ 1 * a03963 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07363 ^ 1)
theorem ha13150 : a13150.IsHomogeneous 141 := by
  unfold a13150
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00712.pow 1)).mul (ha03963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07363.pow 1)))

@[irreducible]
def a13151 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a13145 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13150 ^ 1)
theorem ha13151 : a13151.IsHomogeneous 141 := by
  unfold a13151
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha13145.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13150.pow 1)))

@[irreducible]
def a13152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13146 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13151 ^ 1)
theorem ha13152 : a13152.IsHomogeneous 141 := by
  unfold a13152
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13146.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13151.pow 1)))

@[irreducible]
def a13153 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13149 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13152 ^ 1)
theorem ha13153 : a13153.IsHomogeneous 141 := by
  unfold a13153
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13149.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13152.pow 1)))

@[irreducible]
def a13154 : Poly := (C ((-1 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a12210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a06725 ^ 1)
theorem ha13154 : a13154.IsHomogeneous 90 := by
  unfold a13154
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha12210.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha06725.pow 1)))

@[irreducible]
def a13155 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a13154 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13147 ^ 1)
theorem ha13155 : a13155.IsHomogeneous 135 := by
  unfold a13155
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha13154.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13147.pow 1)))

@[irreducible]
def a13156 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00014 ^ 1 * a13155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13148 ^ 1)
theorem ha13156 : a13156.IsHomogeneous 141 := by
  unfold a13156
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00014.pow 1)).mul (ha13155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13148.pow 1)))

@[irreducible]
def a13157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13149 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13156 ^ 1)
theorem ha13157 : a13157.IsHomogeneous 141 := by
  unfold a13157
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13149.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13156.pow 1)))

@[irreducible]
def a13158 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13157 ^ 1)
theorem ha13158 : a13158.IsHomogeneous 141 := by
  unfold a13158
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13153.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13157.pow 1)))

@[irreducible]
def a13159 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00712 ^ 1 * a03562 ^ 1) + (C ((45 : ℂ) / (8 : ℂ)) * a01702 ^ 2)
theorem ha13159 : a13159.IsHomogeneous 102 := by
  unfold a13159
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00712.pow 1)).mul (ha03562.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (8 : ℂ))).mul (ha01702.pow 2)))

@[irreducible]
def a13160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a03562 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00260 ^ 1 * a06725 ^ 1)
theorem ha13160 : a13160.IsHomogeneous 96 := by
  unfold a13160
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha03562.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00260.pow 1)).mul (ha06725.pow 1)))

@[irreducible]
def a13161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13160 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13159 ^ 1)
theorem ha13161 : a13161.IsHomogeneous 102 := by
  unfold a13161
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13160.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13159.pow 1)))

@[irreducible]
def a13162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13159 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13161 ^ 1)
theorem ha13162 : a13162.IsHomogeneous 102 := by
  unfold a13162
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13159.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13161.pow 1)))

@[irreducible]
def a13163 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a12210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a06725 ^ 1)
theorem ha13163 : a13163.IsHomogeneous 90 := by
  unfold a13163
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha12210.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha06725.pow 1)))

@[irreducible]
def a13164 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13160 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a13163 ^ 1)
theorem ha13164 : a13164.IsHomogeneous 96 := by
  unfold a13164
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13160.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha13163.pow 1)))

@[irreducible]
def a13165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13164 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13161 ^ 1)
theorem ha13165 : a13165.IsHomogeneous 102 := by
  unfold a13165
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13164.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13161.pow 1)))

@[irreducible]
def a13166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13162 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13165 ^ 1)
theorem ha13166 : a13166.IsHomogeneous 102 := by
  unfold a13166
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13162.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13165.pow 1)))

@[irreducible]
def a13167 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13162 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13166 ^ 1)
theorem ha13167 : a13167.IsHomogeneous 102 := by
  unfold a13167
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13162.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13166.pow 1)))

@[irreducible]
def a13168 : Poly := (C ((-81 : ℂ) / (4 : ℂ)) * a00260 ^ 1 * a07363 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13167 ^ 1)
theorem ha13168 : a13168.IsHomogeneous 141 := by
  unfold a13168
  exact ((((isHomogeneous_C (σ := Fin 6) ((-81 : ℂ) / (4 : ℂ))).mul (ha00260.pow 1)).mul (ha07363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13167.pow 1)))

@[irreducible]
def a13169 : Poly := (C ((-8 : ℂ) / (81 : ℂ)) * a13168 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13150 ^ 1)
theorem ha13169 : a13169.IsHomogeneous 141 := by
  unfold a13169
  exact (((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (81 : ℂ))).mul (ha13168.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13150.pow 1)))

@[irreducible]
def a13170 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13151 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13169 ^ 1)
theorem ha13170 : a13170.IsHomogeneous 141 := by
  unfold a13170
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13151.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13169.pow 1)))

@[irreducible]
def a13171 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13152 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13170 ^ 1)
theorem ha13171 : a13171.IsHomogeneous 141 := by
  unfold a13171
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13152.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13170.pow 1)))

@[irreducible]
def a13172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13171 ^ 1)
theorem ha13172 : a13172.IsHomogeneous 141 := by
  unfold a13172
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13153.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13171.pow 1)))

@[irreducible]
def a13173 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13158 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13172 ^ 1)
theorem ha13173 : a13173.IsHomogeneous 141 := by
  unfold a13173
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13158.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13172.pow 1)))

@[irreducible]
def a13174 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a13173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a07368 ^ 1)
theorem ha13174 : a13174.IsHomogeneous 165 := by
  unfold a13174
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha13173.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha07368.pow 1)))

@[irreducible]
def a13175 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a13135 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13174 ^ 1)
theorem ha13175 : a13175.IsHomogeneous 165 := by
  unfold a13175
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha13135.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13174.pow 1)))

@[irreducible]
def a13176 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13136 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13175 ^ 1)
theorem ha13176 : a13176.IsHomogeneous 165 := by
  unfold a13176
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13136.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13175.pow 1)))

@[irreducible]
def a13177 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13137 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13176 ^ 1)
theorem ha13177 : a13177.IsHomogeneous 165 := by
  unfold a13177
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13137.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13176.pow 1)))

@[irreducible]
def a13178 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13138 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13177 ^ 1)
theorem ha13178 : a13178.IsHomogeneous 165 := by
  unfold a13178
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13138.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13177.pow 1)))

@[irreducible]
def a13179 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13143 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13178 ^ 1)
theorem ha13179 : a13179.IsHomogeneous 165 := by
  unfold a13179
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13143.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13178.pow 1)))

@[irreducible]
def a13180 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00305 ^ 1 * a07373 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a13179 ^ 1)
theorem ha13180 : a13180.IsHomogeneous 225 := by
  unfold a13180
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00305.pow 1)).mul (ha07373.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha13179.pow 1)))

@[irreducible]
def a13181 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13102 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a13180 ^ 1)
theorem ha13181 : a13181.IsHomogeneous 285 := by
  unfold a13181
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13102.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha13180.pow 1)))

@[irreducible]
def a13182 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13103 ^ 1) + (C ((5 : ℂ) / (216 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00100 ^ 1 * a13181 ^ 1)
theorem ha13182 : a13182.IsHomogeneous 348 := by
  unfold a13182
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13103.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (216 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha13181.pow 1)))

@[irreducible]
def a13183 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13104 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a13182 ^ 1)
theorem ha13183 : a13183.IsHomogeneous 372 := by
  unfold a13183
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha13182.pow 1)))

@[irreducible]
def a13184 : Poly := (C ((-1 : ℂ) / (27 : ℂ)) * a00042 ^ 1 * a13183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13128 ^ 1)
theorem ha13184 : a13184.IsHomogeneous 396 := by
  unfold a13184
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (27 : ℂ))).mul (ha00042.pow 1)).mul (ha13183.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13128.pow 1)))

@[irreducible]
def a13185 : Poly := (C ((-18 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a13184 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00304 ^ 1 * a07377 ^ 1)
theorem ha13185 : a13185.IsHomogeneous 444 := by
  unfold a13185
  exact (((((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha13184.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00304.pow 1)).mul (ha07377.pow 1)))

@[irreducible]
def a13186 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a13185 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a12973 ^ 1)
theorem ha13186 : a13186.IsHomogeneous 474 := by
  unfold a13186
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha13185.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12973.pow 1)))

@[irreducible]
def a13187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12974 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13186 ^ 1)
theorem ha13187 : a13187.IsHomogeneous 474 := by
  unfold a13187
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12974.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13186.pow 1)))

@[irreducible]
def a13188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12975 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13187 ^ 1)
theorem ha13188 : a13188.IsHomogeneous 474 := by
  unfold a13188
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12975.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13187.pow 1)))

@[irreducible]
def a13189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a12976 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13188 ^ 1)
theorem ha13189 : a13189.IsHomogeneous 474 := by
  unfold a13189
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha12976.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13188.pow 1)))

@[irreducible]
def a13190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13098 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13189 ^ 1)
theorem ha13190 : a13190.IsHomogeneous 474 := by
  unfold a13190
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13098.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13189.pow 1)))

@[irreducible]
def a13191 : Poly := (C ((-8 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a00296 ^ 1 * a07382 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a13190 ^ 1)
theorem ha13191 : a13191.IsHomogeneous 900 := by
  unfold a13191
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha00296.pow 1)).mul (ha07382.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha13190.pow 1)))

@[irreducible]
def a13192 : Poly := (C ((-8 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a10713 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13191 ^ 1)
theorem ha13192 : a13192.IsHomogeneous 1233 := by
  unfold a13192
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha10713.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13191.pow 1)))

@[irreducible]
def a13193 : Poly := (C ((-8 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a10714 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13192 ^ 1)
theorem ha13193 : a13193.IsHomogeneous 1566 := by
  unfold a13193
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha10714.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13192.pow 1)))

@[irreducible]
def a13194 : Poly := (C ((-8 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a10715 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13193 ^ 1)
theorem ha13194 : a13194.IsHomogeneous 1899 := by
  unfold a13194
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha10715.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13193.pow 1)))

@[irreducible]
def a13195 : Poly := (C ((-8 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a10716 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13194 ^ 1)
theorem ha13195 : a13195.IsHomogeneous 2232 := by
  unfold a13195
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha10716.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13194.pow 1)))

@[irreducible]
def a13196 : Poly := (C ((-8 : ℂ) / (45 : ℂ)) * a00042 ^ 1 * a12966 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13195 ^ 1)
theorem ha13196 : a13196.IsHomogeneous 2565 := by
  unfold a13196
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (45 : ℂ))).mul (ha00042.pow 1)).mul (ha12966.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13195.pow 1)))

@[irreducible]
def a13197 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00850 ^ 1 * a03873 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a01886 ^ 1 * a01979 ^ 1)
theorem ha13197 : a13197.IsHomogeneous 1683 := by
  unfold a13197
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00850.pow 1)).mul (ha03873.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha01886.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a13198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00804 ^ 1 * a04032 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00100 ^ 1 * a01886 ^ 1 * a01979 ^ 1)
theorem ha13198 : a13198.IsHomogeneous 1386 := by
  unfold a13198
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00804.pow 1)).mul (ha04032.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00100.pow 1)).mul (ha01886.pow 1)).mul (ha01979.pow 1)))

@[irreducible]
def a13199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13198 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00100 ^ 1 * a13197 ^ 1)
theorem ha13199 : a13199.IsHomogeneous 1719 := by
  unfold a13199
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13198.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00100.pow 1)).mul (ha13197.pow 1)))

@[irreducible]
def a13200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00850 ^ 1 * a03873 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00310 ^ 1 * a07222 ^ 1)
theorem ha13200 : a13200.IsHomogeneous 1980 := by
  unfold a13200
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00850.pow 1)).mul (ha03873.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00310.pow 1)).mul (ha07222.pow 1)))

@[irreducible]
def a13201 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a13200 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13197 ^ 1)
theorem ha13201 : a13201.IsHomogeneous 2016 := by
  unfold a13201
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha13200.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13197.pow 1)))

@[irreducible]
def a13202 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13199 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00100 ^ 1 * a13201 ^ 1)
theorem ha13202 : a13202.IsHomogeneous 2052 := by
  unfold a13202
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13199.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00100.pow 1)).mul (ha13201.pow 1)))

@[irreducible]
def a13203 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00804 ^ 1 * a04032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00296 ^ 1 * a07468 ^ 1)
theorem ha13203 : a13203.IsHomogeneous 1089 := by
  unfold a13203
  exact (((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00804.pow 1)).mul (ha04032.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00296.pow 1)).mul (ha07468.pow 1)))

@[irreducible]
def a13204 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a13198 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13203 ^ 1)
theorem ha13204 : a13204.IsHomogeneous 1422 := by
  unfold a13204
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha13198.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13203.pow 1)))

@[irreducible]
def a13205 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a13199 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13204 ^ 1)
theorem ha13205 : a13205.IsHomogeneous 1755 := by
  unfold a13205
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha13199.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13204.pow 1)))

@[irreducible]
def a13206 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a13202 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13205 ^ 1)
theorem ha13206 : a13206.IsHomogeneous 2088 := by
  unfold a13206
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha13202.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13205.pow 1)))

@[irreducible]
def a13207 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a12961 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00310 ^ 1 * a07222 ^ 1)
theorem ha13207 : a13207.IsHomogeneous 2247 := by
  unfold a13207
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha12961.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00310.pow 1)).mul (ha07222.pow 1)))

@[irreducible]
def a13208 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13200 ^ 1) + (C ((5 : ℂ) / (96 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a13207 ^ 1)
theorem ha13208 : a13208.IsHomogeneous 2313 := by
  unfold a13208
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13200.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (96 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha13207.pow 1)))

@[irreducible]
def a13209 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a13208 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13201 ^ 1)
theorem ha13209 : a13209.IsHomogeneous 2349 := by
  unfold a13209
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha13208.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13201.pow 1)))

@[irreducible]
def a13210 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13202 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00100 ^ 1 * a13209 ^ 1)
theorem ha13210 : a13210.IsHomogeneous 2385 := by
  unfold a13210
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13202.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00100.pow 1)).mul (ha13209.pow 1)))

@[irreducible]
def a13211 : Poly := (C ((-16 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a13210 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a13206 ^ 1)
theorem ha13211 : a13211.IsHomogeneous 2421 := by
  unfold a13211
  exact ((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha13210.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha13206.pow 1)))

@[irreducible]
def a13212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01970 ^ 1 * a01976 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a00848 ^ 1 * a04015 ^ 1)
theorem ha13212 : a13212.IsHomogeneous 219 := by
  unfold a13212
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01970.pow 1)).mul (ha01976.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha00848.pow 1)).mul (ha04015.pow 1)))

@[irreducible]
def a13213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00846 ^ 1 * a04028 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01970 ^ 1 * a01976 ^ 1)
theorem ha13213 : a13213.IsHomogeneous 258 := by
  unfold a13213
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00846.pow 1)).mul (ha04028.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01970.pow 1)).mul (ha01976.pow 1)))

@[irreducible]
def a13214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13213 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13212 ^ 1)
theorem ha13214 : a13214.IsHomogeneous 258 := by
  unfold a13214
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13213.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13212.pow 1)))

@[irreducible]
def a13215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00848 ^ 1 * a04015 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a07439 ^ 1)
theorem ha13215 : a13215.IsHomogeneous 183 := by
  unfold a13215
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00848.pow 1)).mul (ha04015.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha07439.pow 1)))

@[irreducible]
def a13216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13212 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a13215 ^ 1)
theorem ha13216 : a13216.IsHomogeneous 219 := by
  unfold a13216
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13212.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha13215.pow 1)))

@[irreducible]
def a13217 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13214 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13216 ^ 1)
theorem ha13217 : a13217.IsHomogeneous 258 := by
  unfold a13217
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13214.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13216.pow 1)))

@[irreducible]
def a13218 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00309 ^ 1 * a07463 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a00846 ^ 1 * a04028 ^ 1)
theorem ha13218 : a13218.IsHomogeneous 294 := by
  unfold a13218
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00309.pow 1)).mul (ha07463.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha00846.pow 1)).mul (ha04028.pow 1)))

@[irreducible]
def a13219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13218 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13213 ^ 1)
theorem ha13219 : a13219.IsHomogeneous 294 := by
  unfold a13219
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13218.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13213.pow 1)))

@[irreducible]
def a13220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13219 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13214 ^ 1)
theorem ha13220 : a13220.IsHomogeneous 294 := by
  unfold a13220
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13219.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13214.pow 1)))

@[irreducible]
def a13221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13220 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13217 ^ 1)
theorem ha13221 : a13221.IsHomogeneous 294 := by
  unfold a13221
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13220.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13217.pow 1)))

@[irreducible]
def a13222 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00843 ^ 1 * a03803 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a01841 ^ 1 * a01965 ^ 1)
theorem ha13222 : a13222.IsHomogeneous 96 := by
  unfold a13222
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00843.pow 1)).mul (ha03803.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha01841.pow 1)).mul (ha01965.pow 1)))

@[irreducible]
def a13223 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00155 ^ 1 * a04008 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a01841 ^ 1 * a01965 ^ 1)
theorem ha13223 : a13223.IsHomogeneous 87 := by
  unfold a13223
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00155.pow 1)).mul (ha04008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01841.pow 1)).mul (ha01965.pow 1)))

@[irreducible]
def a13224 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13222 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a13223 ^ 1)
theorem ha13224 : a13224.IsHomogeneous 96 := by
  unfold a13224
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13222.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha13223.pow 1)))

@[irreducible]
def a13225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00308 ^ 1 * a07120 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00843 ^ 1 * a03803 ^ 1)
theorem ha13225 : a13225.IsHomogeneous 102 := by
  unfold a13225
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00308.pow 1)).mul (ha07120.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00843.pow 1)).mul (ha03803.pow 1)))

@[irreducible]
def a13226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13225 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13222 ^ 1)
theorem ha13226 : a13226.IsHomogeneous 102 := by
  unfold a13226
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13225.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13222.pow 1)))

@[irreducible]
def a13227 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13226 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13224 ^ 1)
theorem ha13227 : a13227.IsHomogeneous 102 := by
  unfold a13227
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13226.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13224.pow 1)))

@[irreducible]
def a13228 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a04008 ^ 1) + (C ((108 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a07430 ^ 1)
theorem ha13228 : a13228.IsHomogeneous 81 := by
  unfold a13228
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha04008.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((108 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha07430.pow 1)))

@[irreducible]
def a13229 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13228 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13223 ^ 1)
theorem ha13229 : a13229.IsHomogeneous 87 := by
  unfold a13229
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13228.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13223.pow 1)))

@[irreducible]
def a13230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13224 ^ 1) + (C ((5 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a13229 ^ 1)
theorem ha13230 : a13230.IsHomogeneous 96 := by
  unfold a13230
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13224.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha13229.pow 1)))

@[irreducible]
def a13231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13227 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13230 ^ 1)
theorem ha13231 : a13231.IsHomogeneous 102 := by
  unfold a13231
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13227.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13230.pow 1)))

@[irreducible]
def a13232 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01903 ^ 1 * a01962 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00006 ^ 1 * a00841 ^ 1 * a03811 ^ 1)
theorem ha13232 : a13232.IsHomogeneous 72 := by
  unfold a13232
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01903.pow 1)).mul (ha01962.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00006.pow 1)).mul (ha00841.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a13233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00812 ^ 1 * a04004 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a01903 ^ 1 * a01962 ^ 1)
theorem ha13233 : a13233.IsHomogeneous 72 := by
  unfold a13233
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00812.pow 1)).mul (ha04004.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha01903.pow 1)).mul (ha01962.pow 1)))

@[irreducible]
def a13234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13232 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a13233 ^ 1)
theorem ha13234 : a13234.IsHomogeneous 72 := by
  unfold a13234
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13232.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha13233.pow 1)))

@[irreducible]
def a13235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00298 ^ 1 * a07132 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00841 ^ 1 * a03811 ^ 1)
theorem ha13235 : a13235.IsHomogeneous 66 := by
  unfold a13235
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00298.pow 1)).mul (ha07132.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00841.pow 1)).mul (ha03811.pow 1)))

@[irreducible]
def a13236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13232 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00006 ^ 1 * a13235 ^ 1)
theorem ha13236 : a13236.IsHomogeneous 72 := by
  unfold a13236
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13232.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00006.pow 1)).mul (ha13235.pow 1)))

@[irreducible]
def a13237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13234 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13236 ^ 1)
theorem ha13237 : a13237.IsHomogeneous 72 := by
  unfold a13237
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13234.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13236.pow 1)))

@[irreducible]
def a13238 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00299 ^ 1 * a07425 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00812 ^ 1 * a04004 ^ 1)
theorem ha13238 : a13238.IsHomogeneous 72 := by
  unfold a13238
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00299.pow 1)).mul (ha07425.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00812.pow 1)).mul (ha04004.pow 1)))

@[irreducible]
def a13239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13233 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a13238 ^ 1)
theorem ha13239 : a13239.IsHomogeneous 72 := by
  unfold a13239
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13233.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha13238.pow 1)))

@[irreducible]
def a13240 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13234 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a13239 ^ 1)
theorem ha13240 : a13240.IsHomogeneous 72 := by
  unfold a13240
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13234.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha13239.pow 1)))

@[irreducible]
def a13241 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13237 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13240 ^ 1)
theorem ha13241 : a13241.IsHomogeneous 72 := by
  unfold a13241
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13237.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13240.pow 1)))

@[irreducible]
def a13242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a07132 ^ 1) + (C ((7 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a12835 ^ 1)
theorem ha13242 : a13242.IsHomogeneous 36 := by
  unfold a13242
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha07132.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha12835.pow 1)))

@[irreducible]
def a13243 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a13242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13235 ^ 1)
theorem ha13243 : a13243.IsHomogeneous 66 := by
  unfold a13243
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha13242.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13235.pow 1)))

@[irreducible]
def a13244 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13236 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00006 ^ 1 * a13243 ^ 1)
theorem ha13244 : a13244.IsHomogeneous 72 := by
  unfold a13244
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13236.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00006.pow 1)).mul (ha13243.pow 1)))

@[irreducible]
def a13245 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13237 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13244 ^ 1)
theorem ha13245 : a13245.IsHomogeneous 72 := by
  unfold a13245
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13237.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13244.pow 1)))

@[irreducible]
def a13246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13245 ^ 1)
theorem ha13246 : a13246.IsHomogeneous 72 := by
  unfold a13246
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13241.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13245.pow 1)))

@[irreducible]
def a13247 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a03890 ^ 1) + (C ((45 : ℂ) / (14 : ℂ)) * a01896 ^ 2)
theorem ha13247 : a13247.IsHomogeneous 54 := by
  unfold a13247
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha03890.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((45 : ℂ) / (14 : ℂ))).mul (ha01896.pow 2)))

@[irreducible]
def a13248 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a07248 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00809 ^ 1 * a03890 ^ 1)
theorem ha13248 : a13248.IsHomogeneous 54 := by
  unfold a13248
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha07248.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00809.pow 1)).mul (ha03890.pow 1)))

@[irreducible]
def a13249 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13247 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a13248 ^ 1)
theorem ha13249 : a13249.IsHomogeneous 54 := by
  unfold a13249
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13247.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha13248.pow 1)))

@[irreducible]
def a13250 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13247 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13249 ^ 1)
theorem ha13250 : a13250.IsHomogeneous 54 := by
  unfold a13250
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13247.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13249.pow 1)))

@[irreducible]
def a13251 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a12998 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a07248 ^ 1)
theorem ha13251 : a13251.IsHomogeneous 54 := by
  unfold a13251
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha12998.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha07248.pow 1)))

@[irreducible]
def a13252 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13248 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a13251 ^ 1)
theorem ha13252 : a13252.IsHomogeneous 54 := by
  unfold a13252
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13248.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha13251.pow 1)))

@[irreducible]
def a13253 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13249 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a13252 ^ 1)
theorem ha13253 : a13253.IsHomogeneous 54 := by
  unfold a13253
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13249.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha13252.pow 1)))

@[irreducible]
def a13254 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13250 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13253 ^ 1)
theorem ha13254 : a13254.IsHomogeneous 54 := by
  unfold a13254
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13250.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13253.pow 1)))

@[irreducible]
def a13255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13250 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a13254 ^ 1)
theorem ha13255 : a13255.IsHomogeneous 54 := by
  unfold a13255
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13250.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha13254.pow 1)))

@[irreducible]
def a13256 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a13255 ^ 1) + (C ((54 : ℂ) / (7 : ℂ)) * a00299 ^ 1 * a07425 ^ 1)
theorem ha13256 : a13256.IsHomogeneous 72 := by
  unfold a13256
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha13255.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (7 : ℂ))).mul (ha00299.pow 1)).mul (ha07425.pow 1)))

@[irreducible]
def a13257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13238 ^ 1) + (C ((7 : ℂ) / (54 : ℂ)) * a13256 ^ 1)
theorem ha13257 : a13257.IsHomogeneous 72 := by
  unfold a13257
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13238.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (54 : ℂ))).mul (ha13256.pow 1)))

@[irreducible]
def a13258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13239 ^ 1) + (C ((24 : ℂ) / (5 : ℂ)) * a13257 ^ 1)
theorem ha13258 : a13258.IsHomogeneous 72 := by
  unfold a13258
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13239.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (5 : ℂ))).mul (ha13257.pow 1)))

@[irreducible]
def a13259 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13240 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a13258 ^ 1)
theorem ha13259 : a13259.IsHomogeneous 72 := by
  unfold a13259
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13240.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha13258.pow 1)))

@[irreducible]
def a13260 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13259 ^ 1)
theorem ha13260 : a13260.IsHomogeneous 72 := by
  unfold a13260
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13241.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13259.pow 1)))

@[irreducible]
def a13261 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13246 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13260 ^ 1)
theorem ha13261 : a13261.IsHomogeneous 72 := by
  unfold a13261
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13246.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13260.pow 1)))

@[irreducible]
def a13262 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13261 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a07430 ^ 1)
theorem ha13262 : a13262.IsHomogeneous 78 := by
  unfold a13262
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13261.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha07430.pow 1)))

@[irreducible]
def a13263 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13262 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a13228 ^ 1)
theorem ha13263 : a13263.IsHomogeneous 84 := by
  unfold a13263
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha13228.pow 1)))

@[irreducible]
def a13264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13263 ^ 1) + (C ((5 : ℂ) / (12 : ℂ)) * a00003 ^ 3 * a13229 ^ 1)
theorem ha13264 : a13264.IsHomogeneous 90 := by
  unfold a13264
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13263.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (12 : ℂ))).mul (ha00003.pow 3)).mul (ha13229.pow 1)))

@[irreducible]
def a13265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13230 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13264 ^ 1)
theorem ha13265 : a13265.IsHomogeneous 96 := by
  unfold a13265
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13230.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13264.pow 1)))

@[irreducible]
def a13266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13231 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13265 ^ 1)
theorem ha13266 : a13266.IsHomogeneous 102 := by
  unfold a13266
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13231.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13265.pow 1)))

@[irreducible]
def a13267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00308 ^ 1 * a07120 ^ 1) + (C ((25 : ℂ) / (12 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a12818 ^ 1)
theorem ha13267 : a13267.IsHomogeneous 78 := by
  unfold a13267
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00308.pow 1)).mul (ha07120.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (12 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha12818.pow 1)))

@[irreducible]
def a13268 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13225 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a13267 ^ 1)
theorem ha13268 : a13268.IsHomogeneous 108 := by
  unfold a13268
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13225.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha13267.pow 1)))

@[irreducible]
def a13269 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13226 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13268 ^ 1)
theorem ha13269 : a13269.IsHomogeneous 108 := by
  unfold a13269
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13226.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13268.pow 1)))

@[irreducible]
def a13270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13227 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13269 ^ 1)
theorem ha13270 : a13270.IsHomogeneous 108 := by
  unfold a13270
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13227.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13269.pow 1)))

@[irreducible]
def a13271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13231 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13270 ^ 1)
theorem ha13271 : a13271.IsHomogeneous 108 := by
  unfold a13271
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13231.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13270.pow 1)))

@[irreducible]
def a13272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a13266 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13271 ^ 1)
theorem ha13272 : a13272.IsHomogeneous 108 := by
  unfold a13272
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha13266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13271.pow 1)))

@[irreducible]
def a13273 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13272 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07439 ^ 1)
theorem ha13273 : a13273.IsHomogeneous 147 := by
  unfold a13273
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13272.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07439.pow 1)))

@[irreducible]
def a13274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13215 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00100 ^ 1 * a13273 ^ 1)
theorem ha13274 : a13274.IsHomogeneous 183 := by
  unfold a13274
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13215.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00100.pow 1)).mul (ha13273.pow 1)))

@[irreducible]
def a13275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13216 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00100 ^ 1 * a13274 ^ 1)
theorem ha13275 : a13275.IsHomogeneous 219 := by
  unfold a13275
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13216.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00100.pow 1)).mul (ha13274.pow 1)))

@[irreducible]
def a13276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13217 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13275 ^ 1)
theorem ha13276 : a13276.IsHomogeneous 258 := by
  unfold a13276
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13217.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13275.pow 1)))

@[irreducible]
def a13277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13221 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13276 ^ 1)
theorem ha13277 : a13277.IsHomogeneous 294 := by
  unfold a13277
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13221.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13276.pow 1)))

@[irreducible]
def a13278 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01938 ^ 1 * a04025 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a01974 ^ 1 * a03963 ^ 1)
theorem ha13278 : a13278.IsHomogeneous 213 := by
  unfold a13278
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01938.pow 1)).mul (ha04025.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha01974.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a13279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01974 ^ 1 * a03963 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a07363 ^ 1)
theorem ha13279 : a13279.IsHomogeneous 177 := by
  unfold a13279
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01974.pow 1)).mul (ha03963.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha07363.pow 1)))

@[irreducible]
def a13280 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13278 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13279 ^ 1)
theorem ha13280 : a13280.IsHomogeneous 213 := by
  unfold a13280
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13278.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13279.pow 1)))

@[irreducible]
def a13281 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01938 ^ 1 * a04025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a07459 ^ 1)
theorem ha13281 : a13281.IsHomogeneous 252 := by
  unfold a13281
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01938.pow 1)).mul (ha04025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha07459.pow 1)))

@[irreducible]
def a13282 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13278 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13281 ^ 1)
theorem ha13282 : a13282.IsHomogeneous 252 := by
  unfold a13282
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13278.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13281.pow 1)))

@[irreducible]
def a13283 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13280 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13282 ^ 1)
theorem ha13283 : a13283.IsHomogeneous 252 := by
  unfold a13283
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13280.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13282.pow 1)))

@[irreducible]
def a13284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a07363 ^ 1) + (C ((1 : ℂ) / (81 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13167 ^ 1)
theorem ha13284 : a13284.IsHomogeneous 141 := by
  unfold a13284
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha07363.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (81 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13167.pow 1)))

@[irreducible]
def a13285 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13279 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a13284 ^ 1)
theorem ha13285 : a13285.IsHomogeneous 177 := by
  unfold a13285
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13279.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha13284.pow 1)))

@[irreducible]
def a13286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13280 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00100 ^ 1 * a13285 ^ 1)
theorem ha13286 : a13286.IsHomogeneous 213 := by
  unfold a13286
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13280.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00100.pow 1)).mul (ha13285.pow 1)))

@[irreducible]
def a13287 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13286 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13283 ^ 1)
theorem ha13287 : a13287.IsHomogeneous 252 := by
  unfold a13287
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13286.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13283.pow 1)))

@[irreducible]
def a13288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a01938 ^ 1 * a04023 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a03963 ^ 1)
theorem ha13288 : a13288.IsHomogeneous 171 := by
  unfold a13288
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha01938.pow 1)).mul (ha04023.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a13289 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a03963 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a07363 ^ 1)
theorem ha13289 : a13289.IsHomogeneous 135 := by
  unfold a13289
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha03963.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha07363.pow 1)))

@[irreducible]
def a13290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13288 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00100 ^ 1 * a13289 ^ 1)
theorem ha13290 : a13290.IsHomogeneous 171 := by
  unfold a13290
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13288.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00100.pow 1)).mul (ha13289.pow 1)))

@[irreducible]
def a13291 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01938 ^ 1 * a04023 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a07456 ^ 1)
theorem ha13291 : a13291.IsHomogeneous 210 := by
  unfold a13291
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01938.pow 1)).mul (ha04023.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha07456.pow 1)))

@[irreducible]
def a13292 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13288 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13291 ^ 1)
theorem ha13292 : a13292.IsHomogeneous 210 := by
  unfold a13292
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13288.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13291.pow 1)))

@[irreducible]
def a13293 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13290 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13292 ^ 1)
theorem ha13293 : a13293.IsHomogeneous 210 := by
  unfold a13293
  exact (((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13290.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13292.pow 1)))

@[irreducible]
def a13294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01938 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00100 ^ 1 * a03963 ^ 1)
theorem ha13294 : a13294.IsHomogeneous 129 := by
  unfold a13294
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00100.pow 1)).mul (ha03963.pow 1)))

@[irreducible]
def a13295 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00260 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a07454 ^ 1)
theorem ha13295 : a13295.IsHomogeneous 168 := by
  unfold a13295
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha07454.pow 1)))

@[irreducible]
def a13296 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a13294 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13295 ^ 1)
theorem ha13296 : a13296.IsHomogeneous 168 := by
  unfold a13296
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha13294.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13295.pow 1)))

@[irreducible]
def a13297 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a01938 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00829 ^ 1)
theorem ha13297 : a13297.IsHomogeneous 126 := by
  unfold a13297
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha01938.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00829.pow 1)))

@[irreducible]
def a13298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (12 : ℂ)) * a00829 ^ 1)
theorem ha13298 : a13298.IsHomogeneous 84 := by
  unfold a13298
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00829.pow 1)))

@[irreducible]
def a13299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a13298 ^ 1)
theorem ha13299 : a13299.IsHomogeneous 84 := by
  unfold a13299
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha13298.pow 1)))

@[irreducible]
def a13300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a13299 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13297 ^ 1)
theorem ha13300 : a13300.IsHomogeneous 126 := by
  unfold a13300
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha13299.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13297.pow 1)))

@[irreducible]
def a13301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a13300 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a07454 ^ 1)
theorem ha13301 : a13301.IsHomogeneous 168 := by
  unfold a13301
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha13300.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha07454.pow 1)))

@[irreducible]
def a13302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13295 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13301 ^ 1)
theorem ha13302 : a13302.IsHomogeneous 168 := by
  unfold a13302
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13295.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13301.pow 1)))

@[irreducible]
def a13303 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13296 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13302 ^ 1)
theorem ha13303 : a13303.IsHomogeneous 168 := by
  unfold a13303
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13296.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13302.pow 1)))

@[irreducible]
def a13304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a13303 ^ 1) + (C ((1 : ℂ) / (10 : ℂ)) * a00829 ^ 1 * a07456 ^ 1)
theorem ha13304 : a13304.IsHomogeneous 210 := by
  unfold a13304
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha13303.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (10 : ℂ))).mul (ha00829.pow 1)).mul (ha07456.pow 1)))

@[irreducible]
def a13305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13291 ^ 1) + (C ((10 : ℂ) / (1 : ℂ)) * a13304 ^ 1)
theorem ha13305 : a13305.IsHomogeneous 210 := by
  unfold a13305
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13291.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((10 : ℂ) / (1 : ℂ))).mul (ha13304.pow 1)))

@[irreducible]
def a13306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13292 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13305 ^ 1)
theorem ha13306 : a13306.IsHomogeneous 210 := by
  unfold a13306
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13292.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13305.pow 1)))

@[irreducible]
def a13307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13293 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13306 ^ 1)
theorem ha13307 : a13307.IsHomogeneous 210 := by
  unfold a13307
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13293.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13306.pow 1)))

@[irreducible]
def a13308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a13307 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00829 ^ 1 * a07459 ^ 1)
theorem ha13308 : a13308.IsHomogeneous 252 := by
  unfold a13308
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha13307.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00829.pow 1)).mul (ha07459.pow 1)))

@[irreducible]
def a13309 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13281 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13308 ^ 1)
theorem ha13309 : a13309.IsHomogeneous 252 := by
  unfold a13309
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13281.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13308.pow 1)))

@[irreducible]
def a13310 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13282 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13309 ^ 1)
theorem ha13310 : a13310.IsHomogeneous 252 := by
  unfold a13310
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13282.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13309.pow 1)))

@[irreducible]
def a13311 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a13283 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a13310 ^ 1)
theorem ha13311 : a13311.IsHomogeneous 252 := by
  unfold a13311
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13283.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha13310.pow 1)))

end CycleQ2Concrete
