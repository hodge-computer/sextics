import Proposal.CurrentAtoms008

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a04096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00054 ^ 1 * a00317 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00201 ^ 1)
theorem ha04096 : a04096.IsHomogeneous 51 := by
  unfold a04096
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00054.pow 1)).mul (ha00317.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a04097 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04095 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a04096 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a04091 ^ 1)
theorem ha04097 : a04097.IsHomogeneous 51 := by
  unfold a04097
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04095.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha04096.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha04091.pow 1)))

@[irreducible]
def a04098 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00130 ^ 1 * a02008 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00130 ^ 1 * a00201 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a00865 ^ 1)
theorem ha04098 : a04098.IsHomogeneous 54 := by
  unfold a04098
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00130.pow 1)).mul (ha02008.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00130.pow 1)).mul (ha00201.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha00865.pow 1)))

@[irreducible]
def a04099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04092 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a04098 ^ 1) + (C ((35 : ℂ) / (72 : ℂ)) * a00003 ^ 3 * a04095 ^ 1)
theorem ha04099 : a04099.IsHomogeneous 54 := by
  unfold a04099
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04092.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha04098.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (72 : ℂ))).mul (ha00003.pow 3)).mul (ha04095.pow 1)))

@[irreducible]
def a04100 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04094 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04099 ^ 1) + (C ((35 : ℂ) / (72 : ℂ)) * a00003 ^ 3 * a04097 ^ 1)
theorem ha04100 : a04100.IsHomogeneous 54 := by
  unfold a04100
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04094.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04099.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (72 : ℂ))).mul (ha00003.pow 3)).mul (ha04097.pow 1)))

@[irreducible]
def a04101 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00621 ^ 1) + (C ((4 : ℂ) / (15 : ℂ)) * a00042 ^ 1 * a01555 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00621 ^ 1)
theorem ha04101 : a04101.IsHomogeneous 51 := by
  unfold a04101
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00621.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (15 : ℂ))).mul (ha00042.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00621.pow 1)))

@[irreducible]
def a04102 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00201 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00042 ^ 1 * a00621 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00201 ^ 1)
theorem ha04102 : a04102.IsHomogeneous 51 := by
  unfold a04102
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00201.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00042.pow 1)).mul (ha00621.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a04103 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04101 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a04102 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a04091 ^ 1)
theorem ha04103 : a04103.IsHomogeneous 51 := by
  unfold a04103
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04101.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha04102.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha04091.pow 1)))

@[irreducible]
def a04104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a03330 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00130 ^ 1 * a01555 ^ 1) + (C ((7 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a01555 ^ 1)
theorem ha04104 : a04104.IsHomogeneous 54 := by
  unfold a04104
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha03330.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00130.pow 1)).mul (ha01555.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha01555.pow 1)))

@[irreducible]
def a04105 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04093 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a04104 ^ 1) + (C ((35 : ℂ) / (24 : ℂ)) * a00003 ^ 3 * a04101 ^ 1)
theorem ha04105 : a04105.IsHomogeneous 54 := by
  unfold a04105
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04093.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha04104.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (24 : ℂ))).mul (ha00003.pow 3)).mul (ha04101.pow 1)))

@[irreducible]
def a04106 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04094 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a04105 ^ 1) + (C ((35 : ℂ) / (72 : ℂ)) * a00003 ^ 3 * a04103 ^ 1)
theorem ha04106 : a04106.IsHomogeneous 54 := by
  unfold a04106
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04094.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha04105.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((35 : ℂ) / (72 : ℂ))).mul (ha00003.pow 3)).mul (ha04103.pow 1)))

@[irreducible]
def a04107 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00054 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00201 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00054 ^ 1 * a00129 ^ 1)
theorem ha04107 : a04107.IsHomogeneous 54 := by
  unfold a04107
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00054.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00201.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00054.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a04108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04107 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04096 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04102 ^ 1)
theorem ha04108 : a04108.IsHomogeneous 54 := by
  unfold a04108
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04107.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04096.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04102.pow 1)))

@[irreducible]
def a04109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04108 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a04097 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a04103 ^ 1)
theorem ha04109 : a04109.IsHomogeneous 54 := by
  unfold a04109
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04108.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha04097.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha04103.pow 1)))

@[irreducible]
def a04110 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04106 ^ 1) + (C ((7 : ℂ) / (108 : ℂ)) * a04109 ^ 1)
theorem ha04110 : a04110.IsHomogeneous 54 := by
  unfold a04110
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04100.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04106.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (108 : ℂ))).mul (ha04109.pow 1)))

@[irreducible]
def a04111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((5 : ℂ) / (7 : ℂ)) * a00207 ^ 1 * a00317 ^ 1 * a00324 ^ 1) + (C ((24 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00207 ^ 1)
theorem ha04111 : a04111.IsHomogeneous 39 := by
  unfold a04111
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (7 : ℂ))).mul (ha00207.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((24 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a04112 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00865 ^ 1) + (C ((7 : ℂ) / (4 : ℂ)) * a00133 ^ 1 * a00317 ^ 1 * a00632 ^ 1) + (C ((21 : ℂ) / (4 : ℂ)) * a00207 ^ 1 * a00317 ^ 1 * a00324 ^ 1)
theorem ha04112 : a04112.IsHomogeneous 39 := by
  unfold a04112
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (4 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (4 : ℂ))).mul (ha00207.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)))

@[irreducible]
def a04113 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((5 : ℂ) / (21 : ℂ)) * a00133 ^ 1 * a00317 ^ 1 * a00632 ^ 1) + (C ((8 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a00133 ^ 1 * a01575 ^ 1)
theorem ha04113 : a04113.IsHomogeneous 39 := by
  unfold a04113
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (21 : ℂ))).mul (ha00133.pow 1)).mul (ha00317.pow 1)).mul (ha00632.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a04114 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04111 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04113 ^ 1) + (C ((20 : ℂ) / (147 : ℂ)) * a04112 ^ 1)
theorem ha04114 : a04114.IsHomogeneous 39 := by
  unfold a04114
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04111.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04113.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (147 : ℂ))).mul (ha04112.pow 1)))

@[irreducible]
def a04115 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00207 ^ 1 * a00317 ^ 1 * a00324 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a00865 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00058 ^ 1 * a00317 ^ 1)
theorem ha04115 : a04115.IsHomogeneous 39 := by
  unfold a04115
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00207.pow 1)).mul (ha00317.pow 1)).mul (ha00324.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00058.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a04116 : Poly := (C ((-24 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00317 ^ 1)
theorem ha04116 : a04116.IsHomogeneous 33 := by
  unfold a04116
  exact (((((isHomogeneous_C (σ := Fin 6) ((-24 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a04117 : Poly := (C ((-5 : ℂ) / (7 : ℂ)) * a00003 ^ 6 * a04116 ^ 1) + (C ((-5 : ℂ) / (42 : ℂ)) * a04115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04111 ^ 1)
theorem ha04117 : a04117.IsHomogeneous 39 := by
  unfold a04117
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (7 : ℂ))).mul (ha00003.pow 6)).mul (ha04116.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (42 : ℂ))).mul (ha04115.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04111.pow 1)))

@[irreducible]
def a04118 : Poly := (C ((-8 : ℂ) / (7 : ℂ)) * a00133 ^ 1 * a00207 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00324 ^ 1 * a00865 ^ 1) + (C ((1 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00133 ^ 1 * a02008 ^ 1)
theorem ha04118 : a04118.IsHomogeneous 39 := by
  unfold a04118
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (7 : ℂ))).mul (ha00133.pow 1)).mul (ha00207.pow 1)).mul (ha00865.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00324.pow 1)).mul (ha00865.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00133.pow 1)).mul (ha02008.pow 1)))

@[irreducible]
def a04119 : Poly := (C ((-7 : ℂ) / (8 : ℂ)) * a04115 ^ 1) + (C ((-7 : ℂ) / (8 : ℂ)) * a04118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04112 ^ 1)
theorem ha04119 : a04119.IsHomogeneous 39 := by
  unfold a04119
  exact ((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha04115.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (8 : ℂ))).mul (ha04118.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04112.pow 1)))

@[irreducible]
def a04120 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04114 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04117 ^ 1) + (C ((20 : ℂ) / (147 : ℂ)) * a04119 ^ 1)
theorem ha04120 : a04120.IsHomogeneous 39 := by
  unfold a04120
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04114.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04117.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (147 : ℂ))).mul (ha04119.pow 1)))

@[irreducible]
def a04121 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00324 ^ 1 * a00632 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00324 ^ 1 * a01575 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00632 ^ 1)
theorem ha04121 : a04121.IsHomogeneous 39 := by
  unfold a04121
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00324.pow 1)).mul (ha00632.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00632.pow 1)))

@[irreducible]
def a04122 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1) + (C ((7 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00632 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00207 ^ 1)
theorem ha04122 : a04122.IsHomogeneous 36 := by
  unfold a04122
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00632.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a04123 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04111 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04121 ^ 1) + (C ((20 : ℂ) / (21 : ℂ)) * a00003 ^ 3 * a04122 ^ 1)
theorem ha04123 : a04123.IsHomogeneous 39 := by
  unfold a04123
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04111.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04121.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (21 : ℂ))).mul (ha00003.pow 3)).mul (ha04122.pow 1)))

@[irreducible]
def a04124 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a03363 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00129 ^ 1 * a00133 ^ 1 * a01575 ^ 1) + (C ((21 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00324 ^ 1 * a01575 ^ 1)
theorem ha04124 : a04124.IsHomogeneous 36 := by
  unfold a04124
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha03363.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00129.pow 1)).mul (ha00133.pow 1)).mul (ha01575.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((21 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00324.pow 1)).mul (ha01575.pow 1)))

@[irreducible]
def a04125 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04113 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04121 ^ 1) + (C ((20 : ℂ) / (63 : ℂ)) * a00003 ^ 3 * a04124 ^ 1)
theorem ha04125 : a04125.IsHomogeneous 39 := by
  unfold a04125
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04113.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04121.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (63 : ℂ))).mul (ha00003.pow 3)).mul (ha04124.pow 1)))

@[irreducible]
def a04126 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04114 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04123 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04125 ^ 1)
theorem ha04126 : a04126.IsHomogeneous 39 := by
  unfold a04126
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04114.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04123.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04125.pow 1)))

@[irreducible]
def a04127 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00058 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00129 ^ 1)
theorem ha04127 : a04127.IsHomogeneous 36 := by
  unfold a04127
  exact (((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00058.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a04128 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a04116 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a04127 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04122 ^ 1)
theorem ha04128 : a04128.IsHomogeneous 36 := by
  unfold a04128
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha04116.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha04127.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04122.pow 1)))

@[irreducible]
def a04129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04117 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04123 ^ 1) + (C ((20 : ℂ) / (21 : ℂ)) * a00003 ^ 3 * a04128 ^ 1)
theorem ha04129 : a04129.IsHomogeneous 39 := by
  unfold a04129
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04117.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04123.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((20 : ℂ) / (21 : ℂ))).mul (ha00003.pow 3)).mul (ha04128.pow 1)))

@[irreducible]
def a04130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04120 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04129 ^ 1)
theorem ha04130 : a04130.IsHomogeneous 39 := by
  unfold a04130
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04120.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04126.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04129.pow 1)))

@[irreducible]
def a04131 : Poly := (C ((-49 : ℂ) / (180 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a04130 ^ 1) + (C ((-18 : ℂ) / (1 : ℂ)) * a04110 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04070 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a04090 ^ 1)
theorem ha04131 : a04131.IsHomogeneous 54 := by
  unfold a04131
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-49 : ℂ) / (180 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha04130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-18 : ℂ) / (1 : ℂ))).mul (ha04110.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04070.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha04090.pow 1)))

@[irreducible]
def a04132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02032 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a04131 ^ 1)
theorem ha04132 : a04132.IsHomogeneous 99 := by
  unfold a04132
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02032.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha04131.pow 1)))

@[irreducible]
def a04133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04048 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a04132 ^ 1)
theorem ha04133 : a04133.IsHomogeneous 141 := by
  unfold a04133
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04048.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha04132.pow 1)))

@[irreducible]
def a04134 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04050 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a04133 ^ 1)
theorem ha04134 : a04134.IsHomogeneous 183 := by
  unfold a04134
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04050.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha04133.pow 1)))

@[irreducible]
def a04135 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00712 ^ 1 * a02036 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00100 ^ 1 * a00260 ^ 1 * a01702 ^ 1)
theorem ha04135 : a04135.IsHomogeneous 129 := by
  unfold a04135
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00712.pow 1)).mul (ha02036.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00100.pow 1)).mul (ha00260.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a04136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a01702 ^ 1) + (C ((2 : ℂ) / (81 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a03562 ^ 1)
theorem ha04136 : a04136.IsHomogeneous 93 := by
  unfold a04136
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha01702.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (81 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha03562.pow 1)))

@[irreducible]
def a04137 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04135 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00100 ^ 1 * a04136 ^ 1)
theorem ha04137 : a04137.IsHomogeneous 129 := by
  unfold a04137
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04135.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00100.pow 1)).mul (ha04136.pow 1)))

@[irreducible]
def a04138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a00712 ^ 1) + (C ((5 : ℂ) / (54 : ℂ)) * a00100 ^ 1 * a01702 ^ 1)
theorem ha04138 : a04138.IsHomogeneous 87 := by
  unfold a04138
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha00712.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (54 : ℂ))).mul (ha00100.pow 1)).mul (ha01702.pow 1)))

@[irreducible]
def a04139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 2) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1)
theorem ha04139 : a04139.IsHomogeneous 84 := by
  unfold a04139
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a04140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04139 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1)
theorem ha04140 : a04140.IsHomogeneous 84 := by
  unfold a04140
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04139.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)))

@[irreducible]
def a04141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04140 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a04138 ^ 1)
theorem ha04141 : a04141.IsHomogeneous 126 := by
  unfold a04141
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04140.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha04138.pow 1)))

@[irreducible]
def a04142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a04141 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a00712 ^ 1 * a02036 ^ 1)
theorem ha04142 : a04142.IsHomogeneous 168 := by
  unfold a04142
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha04141.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha00712.pow 1)).mul (ha02036.pow 1)))

@[irreducible]
def a04143 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04142 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a04135 ^ 1)
theorem ha04143 : a04143.IsHomogeneous 168 := by
  unfold a04143
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04142.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha04135.pow 1)))

@[irreducible]
def a04144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04143 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00100 ^ 1 * a04137 ^ 1)
theorem ha04144 : a04144.IsHomogeneous 168 := by
  unfold a04144
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04143.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00100.pow 1)).mul (ha04137.pow 1)))

@[irreducible]
def a04145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a04144 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00326 ^ 1 * a02038 ^ 1)
theorem ha04145 : a04145.IsHomogeneous 228 := by
  unfold a04145
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha04144.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00326.pow 1)).mul (ha02038.pow 1)))

@[irreducible]
def a04146 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04145 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a04049 ^ 1)
theorem ha04146 : a04146.IsHomogeneous 228 := by
  unfold a04146
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04145.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha04049.pow 1)))

@[irreducible]
def a04147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04146 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a04050 ^ 1)
theorem ha04147 : a04147.IsHomogeneous 228 := by
  unfold a04147
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04146.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha04050.pow 1)))

@[irreducible]
def a04148 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04147 ^ 1) + (C ((5 : ℂ) / (72 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a04134 ^ 1)
theorem ha04148 : a04148.IsHomogeneous 228 := by
  unfold a04148
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04147.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (72 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha04134.pow 1)))

@[irreducible]
def a04149 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a04148 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a02041 ^ 1)
theorem ha04149 : a04149.IsHomogeneous 288 := by
  unfold a04149
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha04148.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha02041.pow 1)))

@[irreducible]
def a04150 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a04149 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04041 ^ 1)
theorem ha04150 : a04150.IsHomogeneous 348 := by
  unfold a04150
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha04149.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04041.pow 1)))

@[irreducible]
def a04151 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00134 ^ 1 * a04150 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04047 ^ 1)
theorem ha04151 : a04151.IsHomogeneous 408 := by
  unfold a04151
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00134.pow 1)).mul (ha04150.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04047.pow 1)))

@[irreducible]
def a04152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00312 ^ 1 * a02043 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04151 ^ 1)
theorem ha04152 : a04152.IsHomogeneous 906 := by
  unfold a04152
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00312.pow 1)).mul (ha02043.pow 1)).add ((((((((((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04151.pow 1)))

@[irreducible]
def a04153 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a04152 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a02910 ^ 1)
theorem ha04153 : a04153.IsHomogeneous 1293 := by
  unfold a04153
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha04152.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha02910.pow 1)))

@[irreducible]
def a04154 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a02911 ^ 1)
theorem ha04154 : a04154.IsHomogeneous 1650 := by
  unfold a04154
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04153.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha02911.pow 1)))

@[irreducible]
def a04155 : Poly := (C ((-1 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04154 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a04040 ^ 1)
theorem ha04155 : a04155.IsHomogeneous 2007 := by
  unfold a04155
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04154.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha04040.pow 1)))

@[irreducible]
def a04156 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00883 ^ 1 * a00931 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00328 ^ 1 * a02104 ^ 1)
theorem ha04156 : a04156.IsHomogeneous 1234 := by
  unfold a04156
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00883.pow 1)).mul (ha00931.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00328.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a04157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02102 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00878 ^ 1 * a00930 ^ 1)
theorem ha04157 : a04157.IsHomogeneous 229 := by
  unfold a04157
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02102.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00878.pow 1)).mul (ha00930.pow 1)))

@[irreducible]
def a04158 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a02038 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00878 ^ 1 * a00930 ^ 1)
theorem ha04158 : a04158.IsHomogeneous 229 := by
  unfold a04158
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha02038.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00878.pow 1)).mul (ha00930.pow 1)))

@[irreducible]
def a04159 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04157 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a04158 ^ 1)
theorem ha04159 : a04159.IsHomogeneous 229 := by
  unfold a04159
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04157.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha04158.pow 1)))

@[irreducible]
def a04160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00129 ^ 1 * a00455 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1)
theorem ha04160 : a04160.IsHomogeneous 33 := by
  unfold a04160
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00129.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a04161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00455 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a01207 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a00455 ^ 1)
theorem ha04161 : a04161.IsHomogeneous 42 := by
  unfold a04161
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha01207.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a04162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00042 ^ 1)
theorem ha04162 : a04162.IsHomogeneous 36 := by
  unfold a04162
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00455.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a04163 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04162 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04161 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04160 ^ 1)
theorem ha04163 : a04163.IsHomogeneous 42 := by
  unfold a04163
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04162.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04161.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04160.pow 1)))

@[irreducible]
def a04164 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00129 ^ 1 * a01207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00129 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00317 ^ 1 * a00455 ^ 1)
theorem ha04164 : a04164.IsHomogeneous 39 := by
  unfold a04164
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00129.pow 1)).mul (ha01207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha00455.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00317.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a04165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00317 ^ 1 * a00455 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00865 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00317 ^ 1)
theorem ha04165 : a04165.IsHomogeneous 33 := by
  unfold a04165
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00317.pow 1)).mul (ha00455.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00865.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00317.pow 1)))

@[irreducible]
def a04166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04160 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04165 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04164 ^ 1)
theorem ha04166 : a04166.IsHomogeneous 39 := by
  unfold a04166
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04160.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04165.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04164.pow 1)))

@[irreducible]
def a04167 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a01207 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a02710 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00129 ^ 1 * a01207 ^ 1)
theorem ha04167 : a04167.IsHomogeneous 42 := by
  unfold a04167
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha01207.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha02710.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00129.pow 1)).mul (ha01207.pow 1)))

@[irreducible]
def a04168 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04161 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a04167 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04164 ^ 1)
theorem ha04168 : a04168.IsHomogeneous 48 := by
  unfold a04168
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04161.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha04167.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04164.pow 1)))

@[irreducible]
def a04169 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04163 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04168 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04166 ^ 1)
theorem ha04169 : a04169.IsHomogeneous 48 := by
  unfold a04169
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04163.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04168.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04166.pow 1)))

@[irreducible]
def a04170 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha04170 : a04170.IsHomogeneous 36 := by
  unfold a04170
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a04171 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00298 ^ 1)
theorem ha04171 : a04171.IsHomogeneous 36 := by
  unfold a04171
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00298.pow 1)))

@[irreducible]
def a04172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha04172 : a04172.IsHomogeneous 36 := by
  unfold a04172
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a04173 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04171 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a04172 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a04170 ^ 1)
theorem ha04173 : a04173.IsHomogeneous 42 := by
  unfold a04173
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04171.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha04172.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha04170.pow 1)))

@[irreducible]
def a04174 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00298 ^ 1 * a00316 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00809 ^ 1)
theorem ha04174 : a04174.IsHomogeneous 36 := by
  unfold a04174
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00298.pow 1)).mul (ha00316.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00809.pow 1)))

@[irreducible]
def a04175 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00126 ^ 1 * a00316 ^ 1) + (C ((4 : ℂ) / (5 : ℂ)) * a00126 ^ 1 * a00864 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a00298 ^ 1 * a00316 ^ 1)
theorem ha04175 : a04175.IsHomogeneous 42 := by
  unfold a04175
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00126.pow 1)).mul (ha00316.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (5 : ℂ))).mul (ha00126.pow 1)).mul (ha00864.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)).mul (ha00316.pow 1)))

@[irreducible]
def a04176 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04170 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04175 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00014 ^ 1 * a04174 ^ 1)
theorem ha04176 : a04176.IsHomogeneous 42 := by
  unfold a04176
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04170.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04175.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00014.pow 1)).mul (ha04174.pow 1)))

@[irreducible]
def a04177 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00809 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a01896 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 6 * a00809 ^ 1)
theorem ha04177 : a04177.IsHomogeneous 33 := by
  unfold a04177
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00809.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha01896.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)).mul (ha00809.pow 1)))

@[irreducible]
def a04178 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04171 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a04177 ^ 1) + (C ((9 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a04174 ^ 1)
theorem ha04178 : a04178.IsHomogeneous 42 := by
  unfold a04178
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04171.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha04177.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha04174.pow 1)))

@[irreducible]
def a04179 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04178 ^ 1) + (C ((5 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a04176 ^ 1)
theorem ha04179 : a04179.IsHomogeneous 48 := by
  unfold a04179
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04173.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04178.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha04176.pow 1)))

@[irreducible]
def a04180 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04169 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a04179 ^ 1)
theorem ha04180 : a04180.IsHomogeneous 48 := by
  unfold a04180
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04169.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha04179.pow 1)))

@[irreducible]
def a04181 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04169 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04180 ^ 1)
theorem ha04181 : a04181.IsHomogeneous 48 := by
  unfold a04181
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04169.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04180.pow 1)))

@[irreducible]
def a04182 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04169 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04181 ^ 1)
theorem ha04182 : a04182.IsHomogeneous 48 := by
  unfold a04182
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04169.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04181.pow 1)))

@[irreducible]
def a04183 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04179 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a04180 ^ 1)
theorem ha04183 : a04183.IsHomogeneous 48 := by
  unfold a04183
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04179.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha04180.pow 1)))

@[irreducible]
def a04184 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04181 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a04183 ^ 1)
theorem ha04184 : a04184.IsHomogeneous 48 := by
  unfold a04184
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04181.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha04183.pow 1)))

@[irreducible]
def a04185 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04182 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04184 ^ 1)
theorem ha04185 : a04185.IsHomogeneous 48 := by
  unfold a04185
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04182.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04184.pow 1)))

@[irreducible]
def a04186 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04169 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04182 ^ 1)
theorem ha04186 : a04186.IsHomogeneous 48 := by
  unfold a04186
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04169.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04182.pow 1)))

@[irreducible]
def a04187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04185 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04186 ^ 1)
theorem ha04187 : a04187.IsHomogeneous 48 := by
  unfold a04187
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04185.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04186.pow 1)))

@[irreducible]
def a04188 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04179 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04183 ^ 1)
theorem ha04188 : a04188.IsHomogeneous 48 := by
  unfold a04188
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04179.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04183.pow 1)))

@[irreducible]
def a04189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04184 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a04188 ^ 1)
theorem ha04189 : a04189.IsHomogeneous 48 := by
  unfold a04189
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04184.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha04188.pow 1)))

@[irreducible]
def a04190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04185 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04189 ^ 1)
theorem ha04190 : a04190.IsHomogeneous 48 := by
  unfold a04190
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04185.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04189.pow 1)))

@[irreducible]
def a04191 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04187 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04190 ^ 1)
theorem ha04191 : a04191.IsHomogeneous 48 := by
  unfold a04191
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04187.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04190.pow 1)))

@[irreducible]
def a04192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03540 ^ 1) + (C ((15 : ℂ) / (16 : ℂ)) * a03269 ^ 1)
theorem ha04192 : a04192.IsHomogeneous 51 := by
  unfold a04192
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (16 : ℂ))).mul (ha03269.pow 1)))

@[irreducible]
def a04193 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04192 ^ 1)
theorem ha04193 : a04193.IsHomogeneous 51 := by
  unfold a04193
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04192.pow 1)))

@[irreducible]
def a04194 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03269 ^ 1) + (C ((16 : ℂ) / (15 : ℂ)) * a04192 ^ 1)
theorem ha04194 : a04194.IsHomogeneous 51 := by
  unfold a04194
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (15 : ℂ))).mul (ha04192.pow 1)))

@[irreducible]
def a04195 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04193 ^ 1) + (C ((15 : ℂ) / (16 : ℂ)) * a04194 ^ 1)
theorem ha04195 : a04195.IsHomogeneous 51 := by
  unfold a04195
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04193.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (16 : ℂ))).mul (ha04194.pow 1)))

@[irreducible]
def a04196 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03269 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04194 ^ 1)
theorem ha04196 : a04196.IsHomogeneous 51 := by
  unfold a04196
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04194.pow 1)))

@[irreducible]
def a04197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04195 ^ 1) + (C ((15 : ℂ) / (16 : ℂ)) * a04196 ^ 1)
theorem ha04197 : a04197.IsHomogeneous 51 := by
  unfold a04197
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04195.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (16 : ℂ))).mul (ha04196.pow 1)))

@[irreducible]
def a04198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a03540 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04193 ^ 1)
theorem ha04198 : a04198.IsHomogeneous 51 := by
  unfold a04198
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha03540.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04193.pow 1)))

@[irreducible]
def a04199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04195 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04198 ^ 1)
theorem ha04199 : a04199.IsHomogeneous 51 := by
  unfold a04199
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04195.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04198.pow 1)))

@[irreducible]
def a04200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04197 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04199 ^ 1)
theorem ha04200 : a04200.IsHomogeneous 51 := by
  unfold a04200
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04197.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04199.pow 1)))

@[irreducible]
def a04201 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03269 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04196 ^ 1)
theorem ha04201 : a04201.IsHomogeneous 51 := by
  unfold a04201
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04196.pow 1)))

@[irreducible]
def a04202 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04197 ^ 1) + (C ((15 : ℂ) / (16 : ℂ)) * a04201 ^ 1)
theorem ha04202 : a04202.IsHomogeneous 51 := by
  unfold a04202
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04197.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (16 : ℂ))).mul (ha04201.pow 1)))

@[irreducible]
def a04203 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04200 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04202 ^ 1)
theorem ha04203 : a04203.IsHomogeneous 51 := by
  unfold a04203
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04200.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04202.pow 1)))

@[irreducible]
def a04204 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03285 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03307 ^ 1)
theorem ha04204 : a04204.IsHomogeneous 51 := by
  unfold a04204
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03307.pow 1)))

@[irreducible]
def a04205 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03285 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04204 ^ 1)
theorem ha04205 : a04205.IsHomogeneous 51 := by
  unfold a04205
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04204.pow 1)))

@[irreducible]
def a04206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03285 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a03307 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04204 ^ 1)
theorem ha04206 : a04206.IsHomogeneous 51 := by
  unfold a04206
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03307.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04204.pow 1)))

@[irreducible]
def a04207 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03285 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04205 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04206 ^ 1)
theorem ha04207 : a04207.IsHomogeneous 51 := by
  unfold a04207
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04205.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04206.pow 1)))

@[irreducible]
def a04208 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03285 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04205 ^ 1)
theorem ha04208 : a04208.IsHomogeneous 51 := by
  unfold a04208
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04205.pow 1)))

@[irreducible]
def a04209 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03285 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a04208 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a04207 ^ 1)
theorem ha04209 : a04209.IsHomogeneous 51 := by
  unfold a04209
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03285.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha04208.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha04207.pow 1)))

@[irreducible]
def a04210 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03307 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04204 ^ 1)
theorem ha04210 : a04210.IsHomogeneous 51 := by
  unfold a04210
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03307.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04204.pow 1)))

@[irreducible]
def a04211 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04205 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04210 ^ 1)
theorem ha04211 : a04211.IsHomogeneous 51 := by
  unfold a04211
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04205.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04210.pow 1)))

@[irreducible]
def a04212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03307 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04206 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04210 ^ 1)
theorem ha04212 : a04212.IsHomogeneous 51 := by
  unfold a04212
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03307.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04206.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04210.pow 1)))

@[irreducible]
def a04213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04212 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04211 ^ 1)
theorem ha04213 : a04213.IsHomogeneous 51 := by
  unfold a04213
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04207.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04212.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04211.pow 1)))

@[irreducible]
def a04214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04208 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04211 ^ 1)
theorem ha04214 : a04214.IsHomogeneous 51 := by
  unfold a04214
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04208.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04211.pow 1)))

@[irreducible]
def a04215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04209 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a04214 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a04213 ^ 1)
theorem ha04215 : a04215.IsHomogeneous 51 := by
  unfold a04215
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04209.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha04214.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha04213.pow 1)))

@[irreducible]
def a04216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03307 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04210 ^ 1)
theorem ha04216 : a04216.IsHomogeneous 51 := by
  unfold a04216
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03307.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04210.pow 1)))

@[irreducible]
def a04217 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04211 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04216 ^ 1)
theorem ha04217 : a04217.IsHomogeneous 51 := by
  unfold a04217
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04211.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04216.pow 1)))

@[irreducible]
def a04218 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a03307 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a04216 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a04212 ^ 1)
theorem ha04218 : a04218.IsHomogeneous 51 := by
  unfold a04218
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha03307.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha04216.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha04212.pow 1)))

@[irreducible]
def a04219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04213 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a04217 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a04218 ^ 1)
theorem ha04219 : a04219.IsHomogeneous 51 := by
  unfold a04219
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04213.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha04217.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha04218.pow 1)))

@[irreducible]
def a04220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04214 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04217 ^ 1)
theorem ha04220 : a04220.IsHomogeneous 51 := by
  unfold a04220
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04214.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04217.pow 1)))

@[irreducible]
def a04221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04215 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a04220 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a04219 ^ 1)
theorem ha04221 : a04221.IsHomogeneous 51 := by
  unfold a04221
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04215.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha04220.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha04219.pow 1)))

@[irreducible]
def a04222 : Poly := (C ((-7 : ℂ) / (6 : ℂ)) * a04221 ^ 1) + (C ((-5 : ℂ) / (9 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a03347 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a04191 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a04203 ^ 1)
theorem ha04222 : a04222.IsHomogeneous 51 := by
  unfold a04222
  exact (((((isHomogeneous_C (σ := Fin 6) ((-7 : ℂ) / (6 : ℂ))).mul (ha04221.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (9 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha03347.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha04191.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha04203.pow 1)))

@[irreducible]
def a04223 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00241 ^ 1 * a00880 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a00327 ^ 1 * a00691 ^ 1)
theorem ha04223 : a04223.IsHomogeneous 193 := by
  unfold a04223
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00241.pow 1)).mul (ha00880.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha00327.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a04224 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00134 ^ 1 * a01678 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a00691 ^ 1)
theorem ha04224 : a04224.IsHomogeneous 155 := by
  unfold a04224
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00134.pow 1)).mul (ha01678.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha00691.pow 1)))

@[irreducible]
def a04225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04223 ^ 1) + (C ((5 : ℂ) / (36 : ℂ)) * a00003 ^ 2 * a00100 ^ 1 * a04224 ^ 1)
theorem ha04225 : a04225.IsHomogeneous 193 := by
  unfold a04225
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04223.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (36 : ℂ))).mul (ha00003.pow 2)).mul (ha00100.pow 1)).mul (ha04224.pow 1)))

@[irreducible]
def a04226 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00241 ^ 1 * a00880 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02041 ^ 1)
theorem ha04226 : a04226.IsHomogeneous 229 := by
  unfold a04226
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)).mul (ha00880.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02041.pow 1)))

@[irreducible]
def a04227 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04223 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04226 ^ 1)
theorem ha04227 : a04227.IsHomogeneous 229 := by
  unfold a04227
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04223.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04226.pow 1)))

@[irreducible]
def a04228 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a04225 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04227 ^ 1)
theorem ha04228 : a04228.IsHomogeneous 229 := by
  unfold a04228
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha04225.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04227.pow 1)))

@[irreducible]
def a04229 : Poly := (C ((-1 : ℂ) / (4860 : ℂ)) * a00001 ^ 5 * a00003 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 4 * a04222 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04228 ^ 1)
theorem ha04229 : a04229.IsHomogeneous 229 := by
  unfold a04229
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4860 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 4)).mul (ha04222.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04228.pow 1)))

@[irreducible]
def a04230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1 * a02102 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a04229 ^ 1)
theorem ha04230 : a04230.IsHomogeneous 229 := by
  unfold a04230
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)).mul (ha02102.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha04229.pow 1)))

@[irreducible]
def a04231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04157 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04230 ^ 1)
theorem ha04231 : a04231.IsHomogeneous 229 := by
  unfold a04231
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04157.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04230.pow 1)))

@[irreducible]
def a04232 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04159 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04231 ^ 1)
theorem ha04232 : a04232.IsHomogeneous 229 := by
  unfold a04232
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04159.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04231.pow 1)))

@[irreducible]
def a04233 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a04232 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00328 ^ 1 * a02104 ^ 1)
theorem ha04233 : a04233.IsHomogeneous 787 := by
  unfold a04233
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha04232.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00328.pow 1)).mul (ha02104.pow 1)))

@[irreducible]
def a04234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04156 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a04233 ^ 1)
theorem ha04234 : a04234.IsHomogeneous 1234 := by
  unfold a04234
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04156.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha04233.pow 1)))

@[irreducible]
def a04235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a02046 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00883 ^ 1 * a00931 ^ 1)
theorem ha04235 : a04235.IsHomogeneous 1651 := by
  unfold a04235
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha02046.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00883.pow 1)).mul (ha00931.pow 1)))

@[irreducible]
def a04236 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04235 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a04156 ^ 1)
theorem ha04236 : a04236.IsHomogeneous 1651 := by
  unfold a04236
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04235.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha04156.pow 1)))

@[irreducible]
def a04237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04236 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a04234 ^ 1)
theorem ha04237 : a04237.IsHomogeneous 1651 := by
  unfold a04237
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04236.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha04234.pow 1)))

@[irreducible]
def a04238 : Poly := (C ((-27 : ℂ) / (100 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a04155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a04237 ^ 1)
theorem ha04238 : a04238.IsHomogeneous 2068 := by
  unfold a04238
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (100 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha04155.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha04237.pow 1)))

@[irreducible]
def a04239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a04238 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 5 * a02908 ^ 1)
theorem ha04239 : a04239.IsHomogeneous 2096 := by
  unfold a04239
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha04238.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 5)).mul (ha02908.pow 1)))

@[irreducible]
def a04240 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a02109 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04239 ^ 1)
theorem ha04240 : a04240.IsHomogeneous 2096 := by
  unfold a04240
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha02109.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04239.pow 1)))

@[irreducible]
def a04241 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a02660 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04240 ^ 1)
theorem ha04241 : a04241.IsHomogeneous 2096 := by
  unfold a04241
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha02660.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04240.pow 1)))

@[irreducible]
def a04242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00881 ^ 1 * a00934 ^ 1) + (C ((15 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00364 ^ 1 * a02043 ^ 1)
theorem ha04242 : a04242.IsHomogeneous 1382 := by
  unfold a04242
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00881.pow 1)).mul (ha00934.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((15 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00364.pow 1)).mul (ha02043.pow 1)))

@[irreducible]
def a04243 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04242 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a02660 ^ 1)
theorem ha04243 : a04243.IsHomogeneous 1739 := by
  unfold a04243
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04242.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha02660.pow 1)))

@[irreducible]
def a04244 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04243 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04241 ^ 1)
theorem ha04244 : a04244.IsHomogeneous 2096 := by
  unfold a04244
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04243.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04241.pow 1)))

@[irreducible]
def a04245 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00126 ^ 1 * a00134 ^ 1 * a00364 ^ 1 * a02104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00931 ^ 1 * a00935 ^ 1)
theorem ha04245 : a04245.IsHomogeneous 1323 := by
  unfold a04245
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00126.pow 1)).mul (ha00134.pow 1)).mul (ha00364.pow 1)).mul (ha02104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00931.pow 1)).mul (ha00935.pow 1)))

@[irreducible]
def a04246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a02112 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a00935 ^ 1)
theorem ha04246 : a04246.IsHomogeneous 1740 := by
  unfold a04246
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha02112.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha00935.pow 1)))

@[irreducible]
def a04247 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04246 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a04245 ^ 1)
theorem ha04247 : a04247.IsHomogeneous 1740 := by
  unfold a04247
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04246.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha04245.pow 1)))

@[irreducible]
def a04248 : Poly := (C ((-27 : ℂ) / (125 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a04244 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a04247 ^ 1)
theorem ha04248 : a04248.IsHomogeneous 2157 := by
  unfold a04248
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (125 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha04244.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha04247.pow 1)))

@[irreducible]
def a04249 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a04248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a02659 ^ 1)
theorem ha04249 : a04249.IsHomogeneous 2164 := by
  unfold a04249
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha04248.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha02659.pow 1)))

@[irreducible]
def a04250 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a02115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04249 ^ 1)
theorem ha04250 : a04250.IsHomogeneous 2164 := by
  unfold a04250
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha02115.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04249.pow 1)))

@[irreducible]
def a04251 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00327 ^ 1 * a02115 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00881 ^ 1 * a00937 ^ 1)
theorem ha04251 : a04251.IsHomogeneous 1807 := by
  unfold a04251
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00327.pow 1)).mul (ha02115.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00881.pow 1)).mul (ha00937.pow 1)))

@[irreducible]
def a04252 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04251 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04250 ^ 1)
theorem ha04252 : a04252.IsHomogeneous 2164 := by
  unfold a04252
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04251.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04250.pow 1)))

@[irreducible]
def a04253 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00931 ^ 1 * a00937 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00362 ^ 1 * a02116 ^ 1)
theorem ha04253 : a04253.IsHomogeneous 1808 := by
  unfold a04253
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00931.pow 1)).mul (ha00937.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00362.pow 1)).mul (ha02116.pow 1)))

@[irreducible]
def a04254 : Poly := (C ((-27 : ℂ) / (200 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a04252 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a04253 ^ 1)
theorem ha04254 : a04254.IsHomogeneous 2225 := by
  unfold a04254
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (200 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha04252.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha04253.pow 1)))

@[irreducible]
def a04255 : Poly := (C ((-25 : ℂ) / (1728 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00012 ^ 1 * a04254 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a02380 ^ 1)
theorem ha04255 : a04255.IsHomogeneous 2237 := by
  unfold a04255
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-25 : ℂ) / (1728 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha04254.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha02380.pow 1)))

@[irreducible]
def a04256 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00327 ^ 1 * a02118 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04255 ^ 1)
theorem ha04256 : a04256.IsHomogeneous 2237 := by
  unfold a04256
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00327.pow 1)).mul (ha02118.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04255.pow 1)))

@[irreducible]
def a04257 : Poly := (C ((-9 : ℂ) / (50 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a04256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 1 * a00362 ^ 1 * a02118 ^ 1)
theorem ha04257 : a04257.IsHomogeneous 2298 := by
  unfold a04257
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (50 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha04256.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 1)).mul (ha00362.pow 1)).mul (ha02118.pow 1)))

@[irreducible]
def a04258 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00101 ^ 2 * a00103 ^ 2 * a00105 ^ 2 * a00123 ^ 2 * a00124 ^ 2 * a00134 ^ 3 * a02206 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a04257 ^ 1)
theorem ha04258 : a04258.IsHomogeneous 2304 := by
  unfold a04258
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00101.pow 2)).mul (ha00103.pow 2)).mul (ha00105.pow 2)).mul (ha00123.pow 2)).mul (ha00124.pow 2)).mul (ha00134.pow 3)).mul (ha02206.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha04257.pow 1)))

@[irreducible]
def a04259 : Poly := (C ((-144 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00007 ^ 1 * a00025 ^ 1 * a00389 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 8 * a00003 ^ 1 * a00005 ^ 3 * a00014 ^ 2 * a00148 ^ 1)
theorem ha04259 : a04259.IsHomogeneous 157 := by
  unfold a04259
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00007.pow 1)).mul (ha00025.pow 1)).mul (ha00389.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 8)).mul (ha00003.pow 1)).mul (ha00005.pow 3)).mul (ha00014.pow 2)).mul (ha00148.pow 1)))

@[irreducible]
def a04260 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00005 ^ 2 * a00368 ^ 1 * a00976 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a04259 ^ 1)
theorem ha04260 : a04260.IsHomogeneous 169 := by
  unfold a04260
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00005.pow 2)).mul (ha00368.pow 1)).mul (ha00976.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha04259.pow 1)))

@[irreducible]
def a04261 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04260 ^ 1) + (C ((27 : ℂ) / (25 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a00025 ^ 1 * a02159 ^ 1)
theorem ha04261 : a04261.IsHomogeneous 169 := by
  unfold a04261
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04260.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (25 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).mul (ha02159.pow 1)))

@[irreducible]
def a04262 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2) + (C ((1 : ℂ) / (144 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1)
theorem ha04262 : a04262.IsHomogeneous 19 := by
  unfold a04262
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)))

@[irreducible]
def a04263 : Poly := (C ((-1 : ℂ) / (144 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a04262 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00032 ^ 1)
theorem ha04263 : a04263.IsHomogeneous 25 := by
  unfold a04263
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha04262.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a04264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02129 ^ 1) + (C ((3 : ℂ) / (10 : ℂ)) * a00001 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04263 ^ 1)
theorem ha04264 : a04264.IsHomogeneous 79 := by
  unfold a04264
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02129.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (10 : ℂ))).mul (ha00001.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04263.pow 1)))

@[irreducible]
def a04265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a00950 ^ 1) + (C ((144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04264 ^ 1)
theorem ha04265 : a04265.IsHomogeneous 128 := by
  unfold a04265
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha00950.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04264.pow 1)))

@[irreducible]
def a04266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00370 ^ 1 * a00982 ^ 1) + (C ((5 : ℂ) / (576 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a04265 ^ 1)
theorem ha04266 : a04266.IsHomogeneous 130 := by
  unfold a04266
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00370.pow 1)).mul (ha00982.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (576 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha04265.pow 1)))

@[irreducible]
def a04267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a02166 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a04266 ^ 1)
theorem ha04267 : a04267.IsHomogeneous 139 := by
  unfold a04267
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha02166.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha04266.pow 1)))

@[irreducible]
def a04268 : Poly := (C ((-1 : ℂ) / (25 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00146 ^ 1 * a02133 ^ 1)
theorem ha04268 : a04268.IsHomogeneous 116 := by
  unfold a04268
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (25 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00146.pow 1)).mul (ha02133.pow 1)))

@[irreducible]
def a04269 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00387 ^ 1 * a00953 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a04268 ^ 1)
theorem ha04269 : a04269.IsHomogeneous 126 := by
  unfold a04269
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00387.pow 1)).mul (ha00953.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha04268.pow 1)))

@[irreducible]
def a04270 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00009 ^ 1 * a00014 ^ 2 * a00372 ^ 1 * a00974 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a04269 ^ 1)
theorem ha04270 : a04270.IsHomogeneous 127 := by
  unfold a04270
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).mul (ha00372.pow 1)).mul (ha00974.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha04269.pow 1)))

@[irreducible]
def a04271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04270 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 3 * a00138 ^ 1 * a02157 ^ 1)
theorem ha04271 : a04271.IsHomogeneous 127 := by
  unfold a04271
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04270.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 3)).mul (ha00138.pow 1)).mul (ha02157.pow 1)))

@[irreducible]
def a04272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00368 ^ 1)
theorem ha04272 : a04272.IsHomogeneous 6 := by
  unfold a04272
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00368.pow 1)))

@[irreducible]
def a04273 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02138 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 1 * a00003 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04272 ^ 1)
theorem ha04273 : a04273.IsHomogeneous 68 := by
  unfold a04273
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02138.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04272.pow 1)))

@[irreducible]
def a04274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00958 ^ 1) + (C ((1 : ℂ) / (192 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a04273 ^ 1)
theorem ha04274 : a04274.IsHomogeneous 78 := by
  unfold a04274
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00958.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (192 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha04273.pow 1)))

@[irreducible]
def a04275 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00046 ^ 1 * a00375 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a04274 ^ 1)
theorem ha04275 : a04275.IsHomogeneous 79 := by
  unfold a04275
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00046.pow 1)).mul (ha00375.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha04274.pow 1)))

@[irreducible]
def a04276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04275 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a00039 ^ 1 * a00139 ^ 1)
theorem ha04276 : a04276.IsHomogeneous 79 := by
  unfold a04276
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04275.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00039.pow 1)).mul (ha00139.pow 1)))

@[irreducible]
def a04277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04276 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00009 ^ 1 * a00035 ^ 1 * a00042 ^ 1 * a00126 ^ 1)
theorem ha04277 : a04277.IsHomogeneous 79 := by
  unfold a04277
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04276.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00009.pow 1)).mul (ha00035.pow 1)).mul (ha00042.pow 1)).mul (ha00126.pow 1)))

@[irreducible]
def a04278 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2)
theorem ha04278 : a04278.IsHomogeneous 19 := by
  unfold a04278
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a04279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02144 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00001 ^ 4 * a00002 ^ 1 * a00003 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04278 ^ 1)
theorem ha04279 : a04279.IsHomogeneous 74 := by
  unfold a04279
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02144.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04278.pow 1)))

@[irreducible]
def a04280 : Poly := (C ((-144 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00061 ^ 1 * a00963 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a04279 ^ 1)
theorem ha04280 : a04280.IsHomogeneous 79 := by
  unfold a04280
  exact (((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00061.pow 1)).mul (ha00963.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha04279.pow 1)))

@[irreducible]
def a04281 : Poly := (C ((-16 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00046 ^ 1 * a00379 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04280 ^ 1)
theorem ha04281 : a04281.IsHomogeneous 79 := by
  unfold a04281
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00046.pow 1)).mul (ha00379.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04280.pow 1)))

@[irreducible]
def a04282 : Poly := (C ((-16 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a00039 ^ 1 * a00141 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04281 ^ 1)
theorem ha04282 : a04282.IsHomogeneous 79 := by
  unfold a04282
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-16 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00039.pow 1)).mul (ha00141.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04281.pow 1)))

@[irreducible]
def a04283 : Poly := (C ((-144 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00009 ^ 1 * a00035 ^ 1 * a00042 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04282 ^ 1)
theorem ha04283 : a04283.IsHomogeneous 79 := by
  unfold a04283
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00009.pow 1)).mul (ha00035.pow 1)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04282.pow 1)))

@[irreducible]
def a04284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04277 ^ 1) + (C ((1 : ℂ) / (60 : ℂ)) * a04283 ^ 1)
theorem ha04284 : a04284.IsHomogeneous 79 := by
  unfold a04284
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04277.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (60 : ℂ))).mul (ha04283.pow 1)))

@[irreducible]
def a04285 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2)
theorem ha04285 : a04285.IsHomogeneous 19 := by
  unfold a04285
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a04286 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04285 ^ 1)
theorem ha04286 : a04286.IsHomogeneous 19 := by
  unfold a04286
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00368.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04285.pow 1)))

@[irreducible]
def a04287 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a02152 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00001 ^ 4 * a00002 ^ 1 * a00003 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04286 ^ 1)
theorem ha04287 : a04287.IsHomogeneous 74 := by
  unfold a04287
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha02152.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04286.pow 1)))

@[irreducible]
def a04288 : Poly := (C ((-108 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00061 ^ 1 * a00970 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a04287 ^ 1)
theorem ha04288 : a04288.IsHomogeneous 79 := by
  unfold a04288
  exact (((((isHomogeneous_C (σ := Fin 6) ((-108 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00061.pow 1)).mul (ha00970.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha04287.pow 1)))

@[irreducible]
def a04289 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00046 ^ 1 * a00384 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04288 ^ 1)
theorem ha04289 : a04289.IsHomogeneous 79 := by
  unfold a04289
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00046.pow 1)).mul (ha00384.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04288.pow 1)))

@[irreducible]
def a04290 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 2 * a00039 ^ 1 * a00144 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04289 ^ 1)
theorem ha04290 : a04290.IsHomogeneous 79 := by
  unfold a04290
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00039.pow 1)).mul (ha00144.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04289.pow 1)))

@[irreducible]
def a04291 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04284 ^ 1) + (C ((1 : ℂ) / (45 : ℂ)) * a04290 ^ 1)
theorem ha04291 : a04291.IsHomogeneous 79 := by
  unfold a04291
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04284.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (45 : ℂ))).mul (ha04290.pow 1)))

@[irreducible]
def a04292 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 4 * a00127 ^ 1 * a04291 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a04271 ^ 1)
theorem ha04292 : a04292.IsHomogeneous 127 := by
  unfold a04292
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha00127.pow 1)).mul (ha04291.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha04271.pow 1)))

@[irreducible]
def a04293 : Poly := (C ((-10 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a04292 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04267 ^ 1)
theorem ha04293 : a04293.IsHomogeneous 139 := by
  unfold a04293
  exact ((((isHomogeneous_C (σ := Fin 6) ((-10 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha04292.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04267.pow 1)))

@[irreducible]
def a04294 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a04293 ^ 1) + (C ((5 : ℂ) / (9 : ℂ)) * a04261 ^ 1)
theorem ha04294 : a04294.IsHomogeneous 169 := by
  unfold a04294
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha04293.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (9 : ℂ))).mul (ha04261.pow 1)))

@[irreducible]
def a04295 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a00395 ^ 1) + (C ((8 : ℂ) / (5 : ℂ)) * a00000 ^ 3 * a00002 ^ 4 * a00003 ^ 2 * a00005 ^ 1 * a00985 ^ 1)
theorem ha04295 : a04295.IsHomogeneous 146 := by
  unfold a04295
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha00395.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (5 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00005.pow 1)).mul (ha00985.pow 1)))

@[irreducible]
def a04296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a02170 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a04295 ^ 1)
theorem ha04296 : a04296.IsHomogeneous 147 := by
  unfold a04296
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha02170.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha04295.pow 1)))

@[irreducible]
def a04297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 4 * a00003 ^ 1 * a00005 ^ 1 * a00039 ^ 1 * a00082 ^ 1) + (C ((27 : ℂ) / (5 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00009 ^ 1 * a00014 ^ 2 * a00035 ^ 1 * a00100 ^ 1)
theorem ha04297 : a04297.IsHomogeneous 74 := by
  unfold a04297
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00039.pow 1)).mul (ha00082.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((27 : ℂ) / (5 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).mul (ha00035.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a04298 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00061 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00001 ^ 3 * a00004 ^ 2 * a04297 ^ 1)
theorem ha04298 : a04298.IsHomogeneous 79 := by
  unfold a04298
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00061.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha04297.pow 1)))

@[irreducible]
def a04299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00046 ^ 1 * a00061 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04298 ^ 1)
theorem ha04299 : a04299.IsHomogeneous 79 := by
  unfold a04299
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00046.pow 1)).mul (ha00061.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04298.pow 1)))

@[irreducible]
def a04300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04299 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00001 ^ 3 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 1 * a00039 ^ 1 * a00082 ^ 1)
theorem ha04300 : a04300.IsHomogeneous 79 := by
  unfold a04300
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04299.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00039.pow 1)).mul (ha00082.pow 1)))

@[irreducible]
def a04301 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04300 ^ 1) + (C ((3 : ℂ) / (40 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00009 ^ 1 * a00014 ^ 2 * a00035 ^ 1 * a00100 ^ 1)
theorem ha04301 : a04301.IsHomogeneous 79 := by
  unfold a04301
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04300.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (40 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).mul (ha00035.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a04302 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00082 ^ 1 * a02166 ^ 1) + (C ((144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a04301 ^ 1)
theorem ha04302 : a04302.IsHomogeneous 129 := by
  unfold a04302
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00082.pow 1)).mul (ha02166.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha04301.pow 1)))

@[irreducible]
def a04303 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00061 ^ 1 * a00982 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a04302 ^ 1)
theorem ha04303 : a04303.IsHomogeneous 129 := by
  unfold a04303
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00061.pow 1)).mul (ha00982.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha04302.pow 1)))

@[irreducible]
def a04304 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04303 ^ 1) + (C ((5 : ℂ) / (144 : ℂ)) * a00005 ^ 1 * a00046 ^ 1 * a00393 ^ 1)
theorem ha04304 : a04304.IsHomogeneous 129 := by
  unfold a04304
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04303.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (144 : ℂ))).mul (ha00005.pow 1)).mul (ha00046.pow 1)).mul (ha00393.pow 1)))

@[irreducible]
def a04305 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04304 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00039 ^ 1 * a00082 ^ 1 * a00100 ^ 1)
theorem ha04305 : a04305.IsHomogeneous 129 := by
  unfold a04305
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04304.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00039.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a04306 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04305 ^ 1) + (C ((3 : ℂ) / (40 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 4 * a00035 ^ 1 * a00100 ^ 2)
theorem ha04306 : a04306.IsHomogeneous 129 := by
  unfold a04306
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04305.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (40 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 4)).mul (ha00035.pow 1)).mul (ha00100.pow 2)))

@[irreducible]
def a04307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a04306 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00001 ^ 3 * a00004 ^ 2 * a00005 ^ 1 * a04296 ^ 1)
theorem ha04307 : a04307.IsHomogeneous 153 := by
  unfold a04307
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha04306.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha04296.pow 1)))

@[irreducible]
def a04308 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00001 ^ 2 * a00006 ^ 1 * a00014 ^ 6 * a00042 ^ 4 * a00100 ^ 2 * a00126 ^ 2 * a00127 ^ 1 * a04307 ^ 1) + (C ((-9 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00150 ^ 1 * a02173 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00396 ^ 1 * a00988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 2 * a00398 ^ 1 * a00986 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00004 ^ 1 * a00014 ^ 2 * a00042 ^ 3 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a02171 ^ 1)
theorem ha04308 : a04308.IsHomogeneous 443 := by
  unfold a04308
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 6)).mul (ha00042.pow 4)).mul (ha00100.pow 2)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha04307.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00150.pow 1)).mul (ha02173.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00396.pow 1)).mul (ha00988.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 2)).mul (ha00398.pow 1)).mul (ha00986.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha02171.pow 1)))

@[irreducible]
def a04309 : Poly := (C ((-27 : ℂ) / (200 : ℂ)) * a00001 ^ 7 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00042 ^ 4 * a00100 ^ 4 * a04294 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04308 ^ 1)
theorem ha04309 : a04309.IsHomogeneous 443 := by
  unfold a04309
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (200 : ℂ))).mul (ha00001.pow 7)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 4)).mul (ha00100.pow 4)).mul (ha04294.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04308.pow 1)))

@[irreducible]
def a04310 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2)
theorem ha04310 : a04310.IsHomogeneous 19 := by
  unfold a04310
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00368.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a04311 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00368 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04310 ^ 1)
theorem ha04311 : a04311.IsHomogeneous 19 := by
  unfold a04311
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00368.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04310.pow 1)))

@[irreducible]
def a04312 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a04311 ^ 1)
theorem ha04312 : a04312.IsHomogeneous 19 := by
  unfold a04312
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04311.pow 1)))

@[irreducible]
def a04313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a00006 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00127 ^ 1 * a04312 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00138 ^ 1 * a02177 ^ 1)
theorem ha04313 : a04313.IsHomogeneous 57 := by
  unfold a04313
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00127.pow 1)).mul (ha04312.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00138.pow 1)).mul (ha02177.pow 1)))

@[irreducible]
def a04314 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00009 ^ 1 * a00025 ^ 1 * a00372 ^ 1 * a00991 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04313 ^ 1)
theorem ha04314 : a04314.IsHomogeneous 63 := by
  unfold a04314
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00372.pow 1)).mul (ha00991.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04313.pow 1)))

@[irreducible]
def a04315 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00400 ^ 1 * a00953 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a04314 ^ 1)
theorem ha04315 : a04315.IsHomogeneous 69 := by
  unfold a04315
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00400.pow 1)).mul (ha00953.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha04314.pow 1)))

@[irreducible]
def a04316 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00005 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a02133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04315 ^ 1)
theorem ha04316 : a04316.IsHomogeneous 69 := by
  unfold a04316
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha02133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04315.pow 1)))

@[irreducible]
def a04317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a04316 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00002 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a00007 ^ 1 * a00009 ^ 1 * a00126 ^ 2)
theorem ha04317 : a04317.IsHomogeneous 81 := by
  unfold a04317
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha04316.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00126.pow 2)))

@[irreducible]
def a04318 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00001 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 6 * a00100 ^ 3 * a00126 ^ 2 * a00127 ^ 1 * a04301 ^ 1) + (C ((-4 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00082 ^ 1 * a02183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00100 ^ 1 * a00404 ^ 1 * a00982 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1 * a00996 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00004 ^ 1 * a00014 ^ 4 * a00100 ^ 2 * a00126 ^ 1 * a00153 ^ 1 * a02166 ^ 1)
theorem ha04318 : a04318.IsHomogeneous 311 := by
  unfold a04318
  exact (((((((((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 6)).mul (ha00100.pow 3)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha04301.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00082.pow 1)).mul (ha02183.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha00982.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).mul (ha00996.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00004.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 2)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha02166.pow 1)))

@[irreducible]
def a04319 : Poly := (C ((-9 : ℂ) / (1000 : ℂ)) * a00001 ^ 11 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 5 * a00100 ^ 5 * a04317 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04318 ^ 1)
theorem ha04319 : a04319.IsHomogeneous 311 := by
  unfold a04319
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1000 : ℂ))).mul (ha00001.pow 11)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 5)).mul (ha00100.pow 5)).mul (ha04317.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04318.pow 1)))

@[irreducible]
def a04320 : Poly := (C ((-48 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00042 ^ 2 * a00100 ^ 1 * a00367 ^ 1 * a00988 ^ 1) + (C ((-48 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 2 * a00014 ^ 3 * a00042 ^ 5 * a00100 ^ 1 * a00367 ^ 1 * a00996 ^ 1) + (C ((-1 : ℂ) / (3 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 3 * a00100 ^ 2 * a00398 ^ 1 * a00940 ^ 1) + (C ((-1 : ℂ) / (5 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 2 * a00014 ^ 3 * a00042 ^ 4 * a00100 ^ 3 * a00126 ^ 1 * a00151 ^ 1 * a02121 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a00001 ^ 2 * a00012 ^ 1 * a00014 ^ 4 * a00042 ^ 5 * a00100 ^ 2 * a00404 ^ 1 * a00940 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00042 ^ 5 * a00136 ^ 1 * a02183 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 3 * a00042 ^ 1 * a00136 ^ 1 * a02173 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 4 * a00125 ^ 1 * a04309 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 4 * a00014 ^ 2 * a00042 ^ 5 * a00125 ^ 1 * a04319 ^ 1) + (C ((3 : ℂ) / (5000 : ℂ)) * a00001 ^ 12 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 1 * a00014 ^ 6 * a00042 ^ 5 * a00100 ^ 6 * a00940 ^ 1)
theorem ha04320 : a04320.IsHomogeneous 540 := by
  unfold a04320
  exact (((((((((((((((((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha00367.pow 1)).mul (ha00988.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((-48 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 3)).mul (ha00042.pow 5)).mul (ha00100.pow 1)).mul (ha00367.pow 1)).mul (ha00996.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 3)).mul (ha00100.pow 2)).mul (ha00398.pow 1)).mul (ha00940.pow 1))).add (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00014.pow 3)).mul (ha00042.pow 4)).mul (ha00100.pow 3)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha02121.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00001.pow 2)).mul (ha00012.pow 1)).mul (ha00014.pow 4)).mul (ha00042.pow 5)).mul (ha00100.pow 2)).mul (ha00404.pow 1)).mul (ha00940.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha00136.pow 1)).mul (ha02183.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 3)).mul (ha00042.pow 1)).mul (ha00136.pow 1)).mul (ha02173.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 4)).mul (ha00125.pow 1)).mul (ha04309.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha00125.pow 1)).mul (ha04319.pow 1))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5000 : ℂ))).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha00014.pow 6)).mul (ha00042.pow 5)).mul (ha00100.pow 6)).mul (ha00940.pow 1)))

@[irreducible]
def a04321 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a04272 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04278 ^ 1)
theorem ha04321 : a04321.IsHomogeneous 19 := by
  unfold a04321
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha04272.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04278.pow 1)))

@[irreducible]
def a04322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((18 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00040 ^ 1)
theorem ha04322 : a04322.IsHomogeneous 18 := by
  unfold a04322
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00040.pow 1)))

@[irreducible]
def a04323 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00003 ^ 5 * a00005 ^ 2 * a00014 ^ 2)
theorem ha04323 : a04323.IsHomogeneous 24 := by
  unfold a04323
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00003.pow 5)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a04324 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00000 ^ 5 * a00004 ^ 1 * a00007 ^ 1 * a04322 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a04323 ^ 1)
theorem ha04324 : a04324.IsHomogeneous 30 := by
  unfold a04324
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 5)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha04322.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha04323.pow 1)))

@[irreducible]
def a04325 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00009 ^ 1 * a00014 ^ 2 * a00156 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00058 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1)
theorem ha04325 : a04325.IsHomogeneous 31 := by
  unfold a04325
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).mul (ha00156.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00058.pow 1)).mul (ha00156.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a04326 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a04324 ^ 1) + (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00014 ^ 1 * a00130 ^ 1 * a01016 ^ 1) + (C ((-1 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a04321 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04325 ^ 1)
theorem ha04326 : a04326.IsHomogeneous 31 := by
  unfold a04326
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha04324.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha01016.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha04321.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04325.pow 1)))

@[irreducible]
def a04327 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00100 ^ 1 * a01026 ^ 1) + (C ((-2 : ℂ) / (5 : ℂ)) * a00001 ^ 6 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 6 * a00039 ^ 1 * a00100 ^ 3 * a00362 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 2 * a00005 ^ 1 * a00014 ^ 4 * a00046 ^ 1 * a00100 ^ 2 * a00445 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00082 ^ 1 * a02203 ^ 1) + (C ((54 : ℂ) / (25 : ℂ)) * a00000 ^ 1 * a00001 ^ 7 * a00004 ^ 2 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 8 * a00035 ^ 1 * a00100 ^ 4 * a00134 ^ 1)
theorem ha04327 : a04327.IsHomogeneous 287 := by
  unfold a04327
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00100.pow 1)).mul (ha01026.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 6)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 6)).mul (ha00039.pow 1)).mul (ha00100.pow 3)).mul (ha00362.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 2)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00046.pow 1)).mul (ha00100.pow 2)).mul (ha00445.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00082.pow 1)).mul (ha02203.pow 1))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (25 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 7)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 8)).mul (ha00035.pow 1)).mul (ha00100.pow 4)).mul (ha00134.pow 1)))

@[irreducible]
def a04328 : Poly := (C ((-9 : ℂ) / (250 : ℂ)) * a00001 ^ 11 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 9 * a00100 ^ 5 * a04326 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a04327 ^ 1)
theorem ha04328 : a04328.IsHomogeneous 287 := by
  unfold a04328
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (250 : ℂ))).mul (ha00001.pow 11)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 9)).mul (ha00100.pow 5)).mul (ha04326.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04327.pow 1)))

@[irreducible]
def a04329 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 4 * a00014 ^ 2 * a00042 ^ 5 * a00125 ^ 1 * a00126 ^ 2 * a00127 ^ 1 * a04328 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a04320 ^ 1)
theorem ha04329 : a04329.IsHomogeneous 600 := by
  unfold a04329
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 2)).mul (ha00042.pow 5)).mul (ha00125.pow 1)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha04328.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha04320.pow 1)))

@[irreducible]
def a04330 : Poly := (C ((-6 : ℂ) / (5 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a04329 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 3 * a00042 ^ 4 * a00126 ^ 1 * a00364 ^ 1 * a02203 ^ 1)
theorem ha04330 : a04330.IsHomogeneous 1077 := by
  unfold a04330
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha04329.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 3)).mul (ha00042.pow 4)).mul (ha00126.pow 1)).mul (ha00364.pow 1)).mul (ha02203.pow 1)))

@[irreducible]
def a04331 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a04330 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 2 * a00042 ^ 3 * a00937 ^ 1 * a01026 ^ 1)
theorem ha04331 : a04331.IsHomogeneous 1530 := by
  unfold a04331
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha04330.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00042.pow 3)).mul (ha00937.pow 1)).mul (ha01026.pow 1)))

@[irreducible]
def a04332 : Poly := (C ((-5 : ℂ) / (2 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a04331 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00042 ^ 2 * a00445 ^ 1 * a02118 ^ 1)
theorem ha04332 : a04332.IsHomogeneous 1983 := by
  unfold a04332
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (2 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha04331.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00042.pow 2)).mul (ha00445.pow 1)).mul (ha02118.pow 1)))

@[irreducible]
def a04333 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00188 ^ 1) + (C ((-1 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00211 ^ 1) + (C ((-1 : ℂ) / (7680 : ℂ)) * a00000 ^ 1 * a00001 ^ 14 * a00002 ^ 3 * a00004 ^ 5 * a00005 ^ 4 * a00014 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a00012 ^ 4 * a00014 ^ 3 * a00173 ^ 1) + (C ((1 : ℂ) / (1536 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 1 * a00241 ^ 1)
theorem ha04333 : a04333.IsHomogeneous 75 := by
  unfold a04333
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00188.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00211.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (7680 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 14)).mul (ha00002.pow 3)).mul (ha00004.pow 5)).mul (ha00005.pow 4)).mul (ha00014.pow 1)).mul (ha00260.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 3)).mul (ha00173.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1536 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a04334 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00125 ^ 1 * a04333 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00293 ^ 1 * a02119 ^ 1)
theorem ha04334 : a04334.IsHomogeneous 144 := by
  unfold a04334
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00125.pow 1)).mul (ha04333.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00293.pow 1)).mul (ha02119.pow 1)))

@[irreducible]
def a04335 : Poly := (C ((-1 : ℂ) / (256 : ℂ)) * a00000 ^ 1 * a00001 ^ 8 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 2 * a00012 ^ 1 * a00241 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 3 * a00014 ^ 2 * a00188 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00012 ^ 2 * a00014 ^ 1 * a00211 ^ 1) + (C ((1 : ℂ) / (960 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 3 * a00004 ^ 5 * a00005 ^ 3 * a00014 ^ 1 * a00260 ^ 1)
theorem ha04335 : a04335.IsHomogeneous 73 := by
  unfold a04335
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (256 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00241.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00188.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00211.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (960 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 3)).mul (ha00004.pow 5)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a04336 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a04335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00261 ^ 1 * a02120 ^ 1)
theorem ha04336 : a04336.IsHomogeneous 152 := by
  unfold a04336
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha04335.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00261.pow 1)).mul (ha02120.pow 1)))

@[irreducible]
def a04337 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a04336 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 3 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a04334 ^ 1)
theorem ha04337 : a04337.IsHomogeneous 152 := by
  unfold a04337
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha04336.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha04334.pow 1)))

@[irreducible]
def a04338 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a04337 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00292 ^ 1 * a02121 ^ 1)
theorem ha04338 : a04338.IsHomogeneous 430 := by
  unfold a04338
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha04337.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00292.pow 1)).mul (ha02121.pow 1)))

@[irreducible]
def a04339 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00261 ^ 1 * a02121 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a04338 ^ 1)
theorem ha04339 : a04339.IsHomogeneous 509 := by
  unfold a04339
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00261.pow 1)).mul (ha02121.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha04338.pow 1)))

@[irreducible]
def a04340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00306 ^ 1 * a02121 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a04339 ^ 1)
theorem ha04340 : a04340.IsHomogeneous 617 := by
  unfold a04340
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00306.pow 1)).mul (ha02121.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha04339.pow 1)))

@[irreducible]
def a04341 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00492 ^ 1 * a00940 ^ 1)
theorem ha04341 : a04341.IsHomogeneous 727 := by
  unfold a04341
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00492.pow 1)).mul (ha00940.pow 1)))

@[irreducible]
def a04342 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00153 ^ 1 * a02213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00501 ^ 1 * a00940 ^ 1)
theorem ha04342 : a04342.IsHomogeneous 667 := by
  unfold a04342
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha02213.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00501.pow 1)).mul (ha00940.pow 1)))

@[irreducible]
def a04343 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00398 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a01103 ^ 1)
theorem ha04343 : a04343.IsHomogeneous 787 := by
  unfold a04343
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00398.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha01103.pow 1)))

@[irreducible]
def a04344 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00404 ^ 1 * a01035 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00367 ^ 1 * a01118 ^ 1)
theorem ha04344 : a04344.IsHomogeneous 703 := by
  unfold a04344
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00404.pow 1)).mul (ha01035.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00367.pow 1)).mul (ha01118.pow 1)))

@[irreducible]
def a04345 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00452 ^ 1 * a00988 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a02308 ^ 1)
theorem ha04345 : a04345.IsHomogeneous 849 := by
  unfold a04345
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha00988.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha02308.pow 1)))

@[irreducible]
def a04346 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00452 ^ 1 * a00996 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a02327 ^ 1)
theorem ha04346 : a04346.IsHomogeneous 741 := by
  unfold a04346
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00452.pow 1)).mul (ha00996.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha02327.pow 1)))

@[irreducible]
def a04347 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00303 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00156 ^ 1)
theorem ha04347 : a04347.IsHomogeneous 114 := by
  unfold a04347
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00303.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a04348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 2 * a00006 ^ 1 * a00014 ^ 4 * a04347 ^ 1) + (C ((75 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a01043 ^ 1)
theorem ha04348 : a04348.IsHomogeneous 153 := by
  unfold a04348
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 4)).mul (ha04347.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((75 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha01043.pow 1)))

@[irreducible]
def a04349 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00368 ^ 1 * a01083 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00389 ^ 1 * a01041 ^ 1)
theorem ha04349 : a04349.IsHomogeneous 156 := by
  unfold a04349
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00368.pow 1)).mul (ha01083.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00389.pow 1)).mul (ha01041.pow 1)))

@[irreducible]
def a04350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a04348 ^ 1) + (C ((25 : ℂ) / (2 : ℂ)) * a00000 ^ 5 * a00002 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a04349 ^ 1)
theorem ha04350 : a04350.IsHomogeneous 165 := by
  unfold a04350
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha04348.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((25 : ℂ) / (2 : ℂ))).mul (ha00000.pow 5)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha04349.pow 1)))

@[irreducible]
def a04351 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a02282 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00455 ^ 1 * a00976 ^ 1)
theorem ha04351 : a04351.IsHomogeneous 163 := by
  unfold a04351
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha02282.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00455.pow 1)).mul (ha00976.pow 1)))

end CycleQ2Concrete
