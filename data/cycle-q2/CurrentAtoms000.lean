import Proposal.CurrentCore

noncomputable section
namespace CycleQ2Concrete
open MvPolynomial

@[irreducible]
def a00000 : Poly := X (0 : Fin 6)
theorem ha00000 : a00000.IsHomogeneous 1 := by
  unfold a00000
  exact isHomogeneous_X ℂ (0 : Fin 6)

@[irreducible]
def a00001 : Poly := X (1 : Fin 6)
theorem ha00001 : a00001.IsHomogeneous 1 := by
  unfold a00001
  exact isHomogeneous_X ℂ (1 : Fin 6)

@[irreducible]
def a00002 : Poly := X (2 : Fin 6)
theorem ha00002 : a00002.IsHomogeneous 1 := by
  unfold a00002
  exact isHomogeneous_X ℂ (2 : Fin 6)

@[irreducible]
def a00003 : Poly := X (3 : Fin 6)
theorem ha00003 : a00003.IsHomogeneous 1 := by
  unfold a00003
  exact isHomogeneous_X ℂ (3 : Fin 6)

@[irreducible]
def a00004 : Poly := X (4 : Fin 6)
theorem ha00004 : a00004.IsHomogeneous 1 := by
  unfold a00004
  exact isHomogeneous_X ℂ (4 : Fin 6)

@[irreducible]
def a00005 : Poly := X (5 : Fin 6)
theorem ha00005 : a00005.IsHomogeneous 1 := by
  unfold a00005
  exact isHomogeneous_X ℂ (5 : Fin 6)

@[irreducible]
def a00006 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00004 ^ 6)
theorem ha00006 : a00006.IsHomogeneous 6 := by
  unfold a00006
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 6)))

@[irreducible]
def a00007 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 6)
theorem ha00007 : a00007.IsHomogeneous 6 := by
  unfold a00007
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)))

@[irreducible]
def a00008 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1)
theorem ha00008 : a00008.IsHomogeneous 6 := by
  unfold a00008
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)))

@[irreducible]
def a00009 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha00009 : a00009.IsHomogeneous 6 := by
  unfold a00009
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00010 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 3 * a00001 ^ 1 * a00003 ^ 1 * a00004 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00008 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00009 ^ 1)
theorem ha00010 : a00010.IsHomogeneous 6 := by
  unfold a00010
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 3)).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00008.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)))

@[irreducible]
def a00011 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 3 * a00001 ^ 1 * a00003 ^ 1 * a00004 ^ 1)
theorem ha00011 : a00011.IsHomogeneous 6 := by
  unfold a00011
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 3)).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)))

@[irreducible]
def a00012 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00004 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 6)
theorem ha00012 : a00012.IsHomogeneous 6 := by
  unfold a00012
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00004.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 6)))

@[irreducible]
def a00013 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1)
theorem ha00013 : a00013.IsHomogeneous 6 := by
  unfold a00013
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)))

@[irreducible]
def a00014 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00000 ^ 6) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha00014 : a00014.IsHomogeneous 6 := by
  unfold a00014
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00015 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00000 ^ 3 * a00001 ^ 1 * a00003 ^ 1 * a00004 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1)
theorem ha00015 : a00015.IsHomogeneous 6 := by
  unfold a00015
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 3)).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a00016 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 3 * a00001 ^ 1 * a00003 ^ 1 * a00004 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1)
theorem ha00016 : a00016.IsHomogeneous 6 := by
  unfold a00016
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 3)).mul (ha00001.pow 1)).mul (ha00003.pow 1)).mul (ha00004.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)))

@[irreducible]
def a00017 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00014 ^ 1)
theorem ha00017 : a00017.IsHomogeneous 6 := by
  unfold a00017
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a00018 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00008 ^ 1 * a00014 ^ 3) + (C ((1 : ℂ) / (12 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00017 ^ 1)
theorem ha00018 : a00018.IsHomogeneous 24 := by
  unfold a00018
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00008.pow 1)).mul (ha00014.pow 3)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00017.pow 1)))

@[irreducible]
def a00019 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00014 ^ 2) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00001 ^ 2 * a00003 ^ 1 * a00004 ^ 2 * a00014 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00000 ^ 5 * a00001 ^ 2 * a00003 ^ 1 * a00004 ^ 2 * a00009 ^ 1)
theorem ha00019 : a00019.IsHomogeneous 16 := by
  unfold a00019
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 2)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00014.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 2)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00009.pow 1)))

@[irreducible]
def a00020 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00014 ^ 1)
theorem ha00020 : a00020.IsHomogeneous 6 := by
  unfold a00020
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a00021 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a00019 ^ 1 * a00020 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00018 ^ 1)
theorem ha00021 : a00021.IsHomogeneous 30 := by
  unfold a00021
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00019.pow 1)).mul (ha00020.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00018.pow 1)))

@[irreducible]
def a00022 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00011 ^ 1 * a00018 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00015 ^ 2 * a00016 ^ 1 * a00021 ^ 1)
theorem ha00022 : a00022.IsHomogeneous 54 := by
  unfold a00022
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00011.pow 1)).mul (ha00018.pow 2)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00015.pow 2)).mul (ha00016.pow 1)).mul (ha00021.pow 1)))

@[irreducible]
def a00023 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00010 ^ 1 * a00011 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00013 ^ 1 * a00015 ^ 1)
theorem ha00023 : a00023.IsHomogeneous 12 := by
  unfold a00023
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00010.pow 1)).mul (ha00011.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00013.pow 1)).mul (ha00015.pow 1)))

@[irreducible]
def a00024 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 5) + (C ((1 : ℂ) / (12 : ℂ)) * a00000 ^ 1 * a00002 ^ 3 * a00005 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00000 ^ 3 * a00001 ^ 1 * a00004 ^ 1)
theorem ha00024 : a00024.IsHomogeneous 5 := by
  unfold a00024
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 5)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 1)).mul (ha00002.pow 3)).mul (ha00005.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 3)).mul (ha00001.pow 1)).mul (ha00004.pow 1)))

@[irreducible]
def a00025 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1)
theorem ha00025 : a00025.IsHomogeneous 6 := by
  unfold a00025
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a00026 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a00018 ^ 1 * a00019 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00018 ^ 2) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 3 * a00003 ^ 3 * a00019 ^ 3)
theorem ha00026 : a00026.IsHomogeneous 54 := by
  unfold a00026
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00018.pow 1)).mul (ha00019.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00018.pow 2))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 3)).mul (ha00003.pow 3)).mul (ha00019.pow 3)))

@[irreducible]
def a00027 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00009 ^ 1 * a00018 ^ 1 * a00025 ^ 1) + (C ((-1 : ℂ) / (8 : ℂ)) * a00000 ^ 5 * a00001 ^ 2 * a00003 ^ 2 * a00004 ^ 2 * a00019 ^ 1 * a00025 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00009 ^ 1 * a00019 ^ 2)
theorem ha00027 : a00027.IsHomogeneous 39 := by
  unfold a00027
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00009.pow 1)).mul (ha00018.pow 1)).mul (ha00025.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 2)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00019.pow 1)).mul (ha00025.pow 2))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00009.pow 1)).mul (ha00019.pow 2)))

@[irreducible]
def a00028 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00001 ^ 3 * a00002 ^ 1 * a00004 ^ 1 * a00005 ^ 1)
theorem ha00028 : a00028.IsHomogeneous 6 := by
  unfold a00028
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00001.pow 3)).mul (ha00002.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)))

@[irreducible]
def a00029 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 3 * a00028 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00017 ^ 1)
theorem ha00029 : a00029.IsHomogeneous 24 := by
  unfold a00029
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 3)).mul (ha00028.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00017.pow 1)))

@[irreducible]
def a00030 : Poly := (C ((-1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 1 * a00003 ^ 2 * a00004 ^ 1 * a00019 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00018 ^ 1)
theorem ha00030 : a00030.IsHomogeneous 30 := by
  unfold a00030
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 1)).mul (ha00003.pow 2)).mul (ha00004.pow 1)).mul (ha00019.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00018.pow 1)))

@[irreducible]
def a00031 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00000 ^ 5 * a00001 ^ 2 * a00003 ^ 1 * a00004 ^ 2 * a00025 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00019 ^ 1)
theorem ha00031 : a00031.IsHomogeneous 22 := by
  unfold a00031
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 2)).mul (ha00003.pow 1)).mul (ha00004.pow 2)).mul (ha00025.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00019.pow 1)))

@[irreducible]
def a00032 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1)
theorem ha00032 : a00032.IsHomogeneous 6 := by
  unfold a00032
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a00033 : Poly := (C ((-1 : ℂ) / (6 : ℂ)) * a00000 ^ 5 * a00001 ^ 2 * a00003 ^ 2 * a00004 ^ 2 * a00018 ^ 1 * a00031 ^ 1 * a00032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00027 ^ 1 * a00029 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00018 ^ 1 * a00025 ^ 1 * a00030 ^ 1)
theorem ha00033 : a00033.IsHomogeneous 63 := by
  unfold a00033
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 2)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00018.pow 1)).mul (ha00031.pow 1)).mul (ha00032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00027.pow 1)).mul (ha00029.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00018.pow 1)).mul (ha00025.pow 1)).mul (ha00030.pow 1)))

@[irreducible]
def a00034 : Poly := (C ((-6 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 1 * a00004 ^ 1 * a00018 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 1 * a00019 ^ 2)
theorem ha00034 : a00034.IsHomogeneous 33 := by
  unfold a00034
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 1)).mul (ha00004.pow 1)).mul (ha00018.pow 1)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 1)).mul (ha00019.pow 2)))

@[irreducible]
def a00035 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 3 * a00005 ^ 3)
theorem ha00035 : a00035.IsHomogeneous 18 := by
  unfold a00035
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 2)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 3)).mul (ha00005.pow 3)))

@[irreducible]
def a00036 : Poly := (C ((-1 : ℂ) / (8 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2)
theorem ha00036 : a00036.IsHomogeneous 19 := by
  unfold a00036
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)))

@[irreducible]
def a00037 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1)
theorem ha00037 : a00037.IsHomogeneous 6 := by
  unfold a00037
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)))

@[irreducible]
def a00038 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00037 ^ 1)
theorem ha00038 : a00038.IsHomogeneous 6 := by
  unfold a00038
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00037.pow 1)))

@[irreducible]
def a00039 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00009 ^ 1 * a00032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00036 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00025 ^ 1 * a00038 ^ 1)
theorem ha00039 : a00039.IsHomogeneous 25 := by
  unfold a00039
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00036.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00025.pow 1)).mul (ha00038.pow 1)))

@[irreducible]
def a00040 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 2)
theorem ha00040 : a00040.IsHomogeneous 12 := by
  unfold a00040
  exact (((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 2)))

@[irreducible]
def a00041 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00009 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00040 ^ 1)
theorem ha00041 : a00041.IsHomogeneous 31 := by
  unfold a00041
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00040.pow 1)))

@[irreducible]
def a00042 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 3) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00017 ^ 1)
theorem ha00042 : a00042.IsHomogeneous 24 := by
  unfold a00042
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 3)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00017.pow 1)))

@[irreducible]
def a00043 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a00042 ^ 1)
theorem ha00043 : a00043.IsHomogeneous 31 := by
  unfold a00043
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00044 : Poly := (C ((-1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00041 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00043 ^ 1)
theorem ha00044 : a00044.IsHomogeneous 37 := by
  unfold a00044
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00041.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00043.pow 1)))

@[irreducible]
def a00045 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00009 ^ 1 * a00014 ^ 2) + (C ((1 : ℂ) / (144 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00037 ^ 1)
theorem ha00045 : a00045.IsHomogeneous 25 := by
  unfold a00045
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00037.pow 1)))

@[irreducible]
def a00046 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1 * a00009 ^ 1 * a00032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00044 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00025 ^ 1 * a00045 ^ 1)
theorem ha00046 : a00046.IsHomogeneous 37 := by
  unfold a00046
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00044.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00025.pow 1)).mul (ha00045.pow 1)))

@[irreducible]
def a00047 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00009 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00040 ^ 1)
theorem ha00047 : a00047.IsHomogeneous 42 := by
  unfold a00047
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00040.pow 1)))

@[irreducible]
def a00048 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00040 ^ 1)
theorem ha00048 : a00048.IsHomogeneous 12 := by
  unfold a00048
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00040.pow 1)))

@[irreducible]
def a00049 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00047 ^ 1) + (C ((1 : ℂ) / (24 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00048 ^ 1)
theorem ha00049 : a00049.IsHomogeneous 42 := by
  unfold a00049
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00047.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00048.pow 1)))

@[irreducible]
def a00050 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00009 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00047 ^ 1)
theorem ha00050 : a00050.IsHomogeneous 42 := by
  unfold a00050
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00047.pow 1)))

@[irreducible]
def a00051 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00049 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00050 ^ 1)
theorem ha00051 : a00051.IsHomogeneous 42 := by
  unfold a00051
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00049.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00050.pow 1)))

@[irreducible]
def a00052 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00009 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00037 ^ 1)
theorem ha00052 : a00052.IsHomogeneous 36 := by
  unfold a00052
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00037.pow 1)))

@[irreducible]
def a00053 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00052 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00038 ^ 1)
theorem ha00053 : a00053.IsHomogeneous 36 := by
  unfold a00053
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00052.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00038.pow 1)))

@[irreducible]
def a00054 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00025 ^ 1 * a00032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1)
theorem ha00054 : a00054.IsHomogeneous 30 := by
  unfold a00054
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00025.pow 1)).mul (ha00032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00055 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00054 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00009 ^ 1 * a00014 ^ 2)
theorem ha00055 : a00055.IsHomogeneous 36 := by
  unfold a00055
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00054.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 2)))

@[irreducible]
def a00056 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00055 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00038 ^ 1)
theorem ha00056 : a00056.IsHomogeneous 36 := by
  unfold a00056
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00055.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00038.pow 1)))

@[irreducible]
def a00057 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00053 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00056 ^ 1)
theorem ha00057 : a00057.IsHomogeneous 36 := by
  unfold a00057
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00053.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00056.pow 1)))

@[irreducible]
def a00058 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00025 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00032 ^ 1)
theorem ha00058 : a00058.IsHomogeneous 12 := by
  unfold a00058
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a00059 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00009 ^ 1 * a00014 ^ 2) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00058 ^ 1)
theorem ha00059 : a00059.IsHomogeneous 25 := by
  unfold a00059
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00058.pow 1)))

@[irreducible]
def a00060 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00059 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00009 ^ 1 * a00014 ^ 2) + (C ((2 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00058 ^ 1)
theorem ha00060 : a00060.IsHomogeneous 25 := by
  unfold a00060
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00059.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00014.pow 2))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00058.pow 1)))

@[irreducible]
def a00061 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00051 ^ 1) + (C ((-1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00032 ^ 1 * a00060 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00057 ^ 1)
theorem ha00061 : a00061.IsHomogeneous 42 := by
  unfold a00061
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00051.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00032.pow 1)).mul (ha00060.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00057.pow 1)))

@[irreducible]
def a00062 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 4 * a00025 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00040 ^ 1 * a00042 ^ 1)
theorem ha00062 : a00062.IsHomogeneous 43 := by
  unfold a00062
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00040.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00063 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00062 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00040 ^ 1 * a00042 ^ 1)
theorem ha00063 : a00063.IsHomogeneous 43 := by
  unfold a00063
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00062.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00040.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00064 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00009 ^ 1 * a00032 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00025 ^ 2 * a00032 ^ 1)
theorem ha00064 : a00064.IsHomogeneous 36 := by
  unfold a00064
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00009.pow 1)).mul (ha00032.pow 2)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00025.pow 2)).mul (ha00032.pow 1)))

@[irreducible]
def a00065 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 4 * a00025 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00064 ^ 1)
theorem ha00065 : a00065.IsHomogeneous 43 := by
  unfold a00065
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00064.pow 1)))

@[irreducible]
def a00066 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00062 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00065 ^ 1)
theorem ha00066 : a00066.IsHomogeneous 43 := by
  unfold a00066
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00062.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00065.pow 1)))

@[irreducible]
def a00067 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00063 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00066 ^ 1)
theorem ha00067 : a00067.IsHomogeneous 43 := by
  unfold a00067
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00063.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00066.pow 1)))

@[irreducible]
def a00068 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00063 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00040 ^ 1 * a00042 ^ 1)
theorem ha00068 : a00068.IsHomogeneous 43 := by
  unfold a00068
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00063.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00040.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00069 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00067 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00068 ^ 1)
theorem ha00069 : a00069.IsHomogeneous 43 := by
  unfold a00069
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00067.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00068.pow 1)))

@[irreducible]
def a00070 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 4) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00037 ^ 1 * a00042 ^ 1)
theorem ha00070 : a00070.IsHomogeneous 37 := by
  unfold a00070
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 4)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00037.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00071 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00070 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00037 ^ 1 * a00042 ^ 1)
theorem ha00071 : a00071.IsHomogeneous 37 := by
  unfold a00071
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00070.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00037.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00072 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 4) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00054 ^ 1)
theorem ha00072 : a00072.IsHomogeneous 37 := by
  unfold a00072
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 4)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00054.pow 1)))

@[irreducible]
def a00073 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00070 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00072 ^ 1)
theorem ha00073 : a00073.IsHomogeneous 37 := by
  unfold a00073
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00070.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00072.pow 1)))

@[irreducible]
def a00074 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00073 ^ 1)
theorem ha00074 : a00074.IsHomogeneous 37 := by
  unfold a00074
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00071.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00073.pow 1)))

@[irreducible]
def a00075 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00072 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00054 ^ 1)
theorem ha00075 : a00075.IsHomogeneous 37 := by
  unfold a00075
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00072.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00054.pow 1)))

@[irreducible]
def a00076 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00075 ^ 1)
theorem ha00076 : a00076.IsHomogeneous 37 := by
  unfold a00076
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00075.pow 1)))

@[irreducible]
def a00077 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00074 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00076 ^ 1)
theorem ha00077 : a00077.IsHomogeneous 37 := by
  unfold a00077
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00074.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00076.pow 1)))

@[irreducible]
def a00078 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00058 ^ 1)
theorem ha00078 : a00078.IsHomogeneous 30 := by
  unfold a00078
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00058.pow 1)))

@[irreducible]
def a00079 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00078 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00058 ^ 1)
theorem ha00079 : a00079.IsHomogeneous 30 := by
  unfold a00079
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00078.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00058.pow 1)))

@[irreducible]
def a00080 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00078 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00058 ^ 1)
theorem ha00080 : a00080.IsHomogeneous 30 := by
  unfold a00080
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00078.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00058.pow 1)))

@[irreducible]
def a00081 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00079 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00080 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00058 ^ 1)
theorem ha00081 : a00081.IsHomogeneous 30 := by
  unfold a00081
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00079.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00080.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00058.pow 1)))

@[irreducible]
def a00082 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00032 ^ 1 * a00081 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00069 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00077 ^ 1)
theorem ha00082 : a00082.IsHomogeneous 43 := by
  unfold a00082
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00032.pow 1)).mul (ha00081.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00069.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00077.pow 1)))

@[irreducible]
def a00083 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00064 ^ 1)
theorem ha00083 : a00083.IsHomogeneous 36 := by
  unfold a00083
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00064.pow 1)))

@[irreducible]
def a00084 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00083 ^ 1)
theorem ha00084 : a00084.IsHomogeneous 36 := by
  unfold a00084
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00083.pow 1)))

@[irreducible]
def a00085 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00084 ^ 1)
theorem ha00085 : a00085.IsHomogeneous 36 := by
  unfold a00085
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00084.pow 1)))

@[irreducible]
def a00086 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00083 ^ 1)
theorem ha00086 : a00086.IsHomogeneous 36 := by
  unfold a00086
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00083.pow 1)))

@[irreducible]
def a00087 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00084 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00086 ^ 1)
theorem ha00087 : a00087.IsHomogeneous 36 := by
  unfold a00087
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00084.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00086.pow 1)))

@[irreducible]
def a00088 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00085 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00087 ^ 1)
theorem ha00088 : a00088.IsHomogeneous 36 := by
  unfold a00088
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00085.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00087.pow 1)))

@[irreducible]
def a00089 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00085 ^ 1)
theorem ha00089 : a00089.IsHomogeneous 36 := by
  unfold a00089
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00085.pow 1)))

@[irreducible]
def a00090 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00088 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00089 ^ 1)
theorem ha00090 : a00090.IsHomogeneous 36 := by
  unfold a00090
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00088.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00089.pow 1)))

@[irreducible]
def a00091 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1)
theorem ha00091 : a00091.IsHomogeneous 30 := by
  unfold a00091
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)))

@[irreducible]
def a00092 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00091 ^ 1)
theorem ha00092 : a00092.IsHomogeneous 30 := by
  unfold a00092
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00091.pow 1)))

@[irreducible]
def a00093 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00092 ^ 1)
theorem ha00093 : a00093.IsHomogeneous 30 := by
  unfold a00093
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00092.pow 1)))

@[irreducible]
def a00094 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00091 ^ 1)
theorem ha00094 : a00094.IsHomogeneous 30 := by
  unfold a00094
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00091.pow 1)))

@[irreducible]
def a00095 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00092 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00094 ^ 1)
theorem ha00095 : a00095.IsHomogeneous 30 := by
  unfold a00095
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00092.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00094.pow 1)))

@[irreducible]
def a00096 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00093 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00095 ^ 1)
theorem ha00096 : a00096.IsHomogeneous 30 := by
  unfold a00096
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00093.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00095.pow 1)))

@[irreducible]
def a00097 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00094 ^ 1)
theorem ha00097 : a00097.IsHomogeneous 30 := by
  unfold a00097
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00094.pow 1)))

@[irreducible]
def a00098 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00095 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00097 ^ 1)
theorem ha00098 : a00098.IsHomogeneous 30 := by
  unfold a00098
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00095.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00097.pow 1)))

@[irreducible]
def a00099 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00096 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00098 ^ 1)
theorem ha00099 : a00099.IsHomogeneous 30 := by
  unfold a00099
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00096.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00098.pow 1)))

@[irreducible]
def a00100 : Poly := (C ((-5 : ℂ) / (27 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00032 ^ 1 * a00058 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00090 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00099 ^ 1)
theorem ha00100 : a00100.IsHomogeneous 36 := by
  unfold a00100
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (27 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00032.pow 1)).mul (ha00058.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00090.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00099.pow 1)))

@[irreducible]
def a00101 : Poly := (C ((-27 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00009 ^ 1 * a00012 ^ 5 * a00014 ^ 4 * a00035 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 3 * a00012 ^ 3 * a00014 ^ 2 * a00046 ^ 1) + (C ((-1 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 6 * a00004 ^ 5 * a00005 ^ 5 * a00012 ^ 1 * a00082 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00012 ^ 4 * a00014 ^ 3 * a00039 ^ 1) + (C ((1 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 1 * a00061 ^ 1) + (C ((1 : ℂ) / (5760 : ℂ)) * a00000 ^ 1 * a00001 ^ 18 * a00002 ^ 6 * a00004 ^ 6 * a00005 ^ 6 * a00014 ^ 1 * a00100 ^ 1)
theorem ha00101 : a00101.IsHomogeneous 79 := by
  unfold a00101
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00009.pow 1)).mul (ha00012.pow 5)).mul (ha00014.pow 4)).mul (ha00035.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00046.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 6)).mul (ha00004.pow 5)).mul (ha00005.pow 5)).mul (ha00012.pow 1)).mul (ha00082.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00012.pow 4)).mul (ha00014.pow 3)).mul (ha00039.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00061.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5760 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 18)).mul (ha00002.pow 6)).mul (ha00004.pow 6)).mul (ha00005.pow 6)).mul (ha00014.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a00102 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00012 ^ 3) + (C ((1 : ℂ) / (72 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 1)
theorem ha00102 : a00102.IsHomogeneous 24 := by
  unfold a00102
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00006.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00012.pow 3))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 1)))

@[irreducible]
def a00103 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00014 ^ 2) + (C ((-1 : ℂ) / (46656 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 3 * a00004 ^ 6 * a00005 ^ 3 * a00017 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 3 * a00102 ^ 1)
theorem ha00103 : a00103.IsHomogeneous 42 := by
  unfold a00103
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (46656 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).mul (ha00017.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 3)).mul (ha00102.pow 1)))

@[irreducible]
def a00104 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00012 ^ 2 * a00014 ^ 2) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00014 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00009 ^ 1)
theorem ha00104 : a00104.IsHomogeneous 25 := by
  unfold a00104
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00014.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00009.pow 1)))

@[irreducible]
def a00105 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00025 ^ 1 * a00103 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1 * a00104 ^ 2)
theorem ha00105 : a00105.IsHomogeneous 55 := by
  unfold a00105
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00025.pow 1)).mul (ha00103.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00104.pow 2)))

@[irreducible]
def a00106 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00005 ^ 6 * a00012 ^ 2) + (C ((-1 : ℂ) / (216 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 6 * a00012 ^ 2)
theorem ha00106 : a00106.IsHomogeneous 18 := by
  unfold a00106
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00005.pow 6)).mul (ha00012.pow 2)).add (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 6)).mul (ha00012.pow 2)))

@[irreducible]
def a00107 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1)
theorem ha00107 : a00107.IsHomogeneous 6 := by
  unfold a00107
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)))

@[irreducible]
def a00108 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3) + (C ((216 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00012 ^ 2)
theorem ha00108 : a00108.IsHomogeneous 18 := by
  unfold a00108
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).add (((isHomogeneous_C (σ := Fin 6) ((216 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00012.pow 2)))

@[irreducible]
def a00109 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00108 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1)
theorem ha00109 : a00109.IsHomogeneous 24 := by
  unfold a00109
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00108.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a00110 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3) + (C ((1296 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00012 ^ 2)
theorem ha00110 : a00110.IsHomogeneous 15 := by
  unfold a00110
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).add (((isHomogeneous_C (σ := Fin 6) ((1296 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00012.pow 2)))

@[irreducible]
def a00111 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 1 * a00009 ^ 1 * a00110 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00012 ^ 1)
theorem ha00111 : a00111.IsHomogeneous 22 := by
  unfold a00111
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00110.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a00112 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00107 ^ 1 * a00111 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00109 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00107 ^ 1 * a00109 ^ 1)
theorem ha00112 : a00112.IsHomogeneous 30 := by
  unfold a00112
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00107.pow 1)).mul (ha00111.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00109.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00107.pow 1)).mul (ha00109.pow 1)))

@[irreducible]
def a00113 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3) + (C ((3888 : ℂ) / (1 : ℂ)) * a00005 ^ 3 * a00012 ^ 2)
theorem ha00113 : a00113.IsHomogeneous 15 := by
  unfold a00113
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).add (((isHomogeneous_C (σ := Fin 6) ((3888 : ℂ) / (1 : ℂ))).mul (ha00005.pow 3)).mul (ha00012.pow 2)))

@[irreducible]
def a00114 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00005 ^ 4 * a00009 ^ 1 * a00012 ^ 2) + (C ((1 : ℂ) / (432 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 1 * a00009 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00012 ^ 1)
theorem ha00114 : a00114.IsHomogeneous 22 := by
  unfold a00114
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00005.pow 4)).mul (ha00009.pow 1)).mul (ha00012.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00009.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a00115 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00012 ^ 1)
theorem ha00115 : a00115.IsHomogeneous 13 := by
  unfold a00115
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a00116 : Poly := (C ((-1 : ℂ) / (648 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00107 ^ 1 * a00115 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00114 ^ 1)
theorem ha00116 : a00116.IsHomogeneous 28 := by
  unfold a00116
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (648 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00107.pow 1)).mul (ha00115.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00114.pow 1)))

@[irreducible]
def a00117 : Poly := (C ((-432 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00114 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00109 ^ 1)
theorem ha00117 : a00117.IsHomogeneous 24 := by
  unfold a00117
  exact ((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00114.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00109.pow 1)))

@[irreducible]
def a00118 : Poly := (C ((-1 : ℂ) / (288 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 4 * a00005 ^ 2 * a00025 ^ 2 * a00104 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00104 ^ 2) + (C ((1 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00009 ^ 1 * a00025 ^ 1 * a00103 ^ 1)
theorem ha00118 : a00118.IsHomogeneous 61 := by
  unfold a00118
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (288 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00025.pow 2)).mul (ha00104.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00104.pow 2))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00103.pow 1)))

@[irreducible]
def a00119 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00012 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1)
theorem ha00119 : a00119.IsHomogeneous 6 := by
  unfold a00119
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)))

@[irreducible]
def a00120 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00012 ^ 2 * a00014 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00119 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 8 * a00003 ^ 3 * a00004 ^ 4 * a00005 ^ 1 * a00017 ^ 1)
theorem ha00120 : a00120.IsHomogeneous 31 := by
  unfold a00120
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00119.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 8)).mul (ha00003.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00017.pow 1)))

@[irreducible]
def a00121 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00103 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00025 ^ 1 * a00104 ^ 1)
theorem ha00121 : a00121.IsHomogeneous 48 := by
  unfold a00121
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00103.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00025.pow 1)).mul (ha00104.pow 1)))

@[irreducible]
def a00122 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00025 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00104 ^ 1)
theorem ha00122 : a00122.IsHomogeneous 31 := by
  unfold a00122
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00025.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00104.pow 1)))

@[irreducible]
def a00123 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00032 ^ 1 * a00103 ^ 1 * a00122 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00118 ^ 1 * a00120 ^ 1) + (C ((54 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00025 ^ 1 * a00103 ^ 1 * a00121 ^ 1)
theorem ha00123 : a00123.IsHomogeneous 97 := by
  unfold a00123
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00032.pow 1)).mul (ha00103.pow 1)).mul (ha00122.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00118.pow 1)).mul (ha00120.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00025.pow 1)).mul (ha00103.pow 1)).mul (ha00121.pow 1)))

@[irreducible]
def a00124 : Poly := (C ((-1 : ℂ) / (11664 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 3 * a00004 ^ 6 * a00005 ^ 3 * a00102 ^ 1) + (C ((-1 : ℂ) / (15552 : ℂ)) * a00000 ^ 8 * a00001 ^ 8 * a00002 ^ 8 * a00003 ^ 4 * a00004 ^ 4 * a00005 ^ 4 * a00012 ^ 4) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 2 * a00102 ^ 2) + (C ((1 : ℂ) / (36 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00009 ^ 1 * a00012 ^ 2 * a00102 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 3 * a00005 ^ 3 * a00009 ^ 1 * a00012 ^ 6)
theorem ha00124 : a00124.IsHomogeneous 60 := by
  unfold a00124
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (11664 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).mul (ha00102.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (15552 : ℂ))).mul (ha00000.pow 8)).mul (ha00001.pow 8)).mul (ha00002.pow 8)).mul (ha00003.pow 4)).mul (ha00004.pow 4)).mul (ha00005.pow 4)).mul (ha00012.pow 4))).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 2)).mul (ha00102.pow 2))).add ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00009.pow 1)).mul (ha00012.pow 2)).mul (ha00102.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 3)).mul (ha00005.pow 3)).mul (ha00009.pow 1)).mul (ha00012.pow 6)))

@[irreducible]
def a00125 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00046 ^ 1) + (C ((-1 : ℂ) / (288 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 1 * a00082 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a00012 ^ 4 * a00014 ^ 3 * a00039 ^ 1) + (C ((1 : ℂ) / (1152 : ℂ)) * a00000 ^ 1 * a00001 ^ 14 * a00002 ^ 3 * a00004 ^ 5 * a00005 ^ 4 * a00014 ^ 1 * a00100 ^ 1) + (C ((3 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00061 ^ 1)
theorem ha00125 : a00125.IsHomogeneous 69 := by
  unfold a00125
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00046.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (288 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha00082.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 3)).mul (ha00039.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1152 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 14)).mul (ha00002.pow 3)).mul (ha00004.pow 5)).mul (ha00005.pow 4)).mul (ha00014.pow 1)).mul (ha00100.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00061.pow 1)))

@[irreducible]
def a00126 : Poly := (C ((-1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00032 ^ 2) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1)
theorem ha00126 : a00126.IsHomogeneous 30 := by
  unfold a00126
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00032.pow 2)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00127 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 2) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3)
theorem ha00127 : a00127.IsHomogeneous 18 := by
  unfold a00127
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 2)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a00128 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00017 ^ 1) + (C ((8 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha00128 : a00128.IsHomogeneous 6 := by
  unfold a00128
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00017.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00129 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 2) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00128 ^ 1)
theorem ha00129 : a00129.IsHomogeneous 21 := by
  unfold a00129
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 2)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00128.pow 1)))

@[irreducible]
def a00130 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((1 : ℂ) / (12 : ℂ)) * a00025 ^ 1)
theorem ha00130 : a00130.IsHomogeneous 6 := by
  unfold a00130
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00025.pow 1)))

@[irreducible]
def a00131 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha00131 : a00131.IsHomogeneous 6 := by
  unfold a00131
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00132 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha00132 : a00132.IsHomogeneous 6 := by
  unfold a00132
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00133 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00131 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00132 ^ 1)
theorem ha00133 : a00133.IsHomogeneous 6 := by
  unfold a00133
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00131.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00132.pow 1)))

@[irreducible]
def a00134 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00054 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00064 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00042 ^ 1 * a00058 ^ 1 * a00133 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00126 ^ 1)
theorem ha00134 : a00134.IsHomogeneous 60 := by
  unfold a00134
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00054.pow 1)).mul (ha00130.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00064.pow 1)).mul (ha00129.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00042.pow 1)).mul (ha00058.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00126.pow 1)))

@[irreducible]
def a00135 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00082 ^ 1)
theorem ha00135 : a00135.IsHomogeneous 49 := by
  unfold a00135
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00082.pow 1)))

@[irreducible]
def a00136 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00125 ^ 1 * a00135 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a00101 ^ 1)
theorem ha00136 : a00136.IsHomogeneous 122 := by
  unfold a00136
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00125.pow 1)).mul (ha00135.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00101.pow 1)))

@[irreducible]
def a00137 : Poly := (C ((-1 : ℂ) / (72 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00025 ^ 1 * a00032 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 2) + (C ((1 : ℂ) / (23328 : ℂ)) * a00000 ^ 18 * a00001 ^ 6 * a00003 ^ 6 * a00004 ^ 6 * a00032 ^ 3)
theorem ha00137 : a00137.IsHomogeneous 54 := by
  unfold a00137
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha00042.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 2))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (23328 : ℂ))).mul (ha00000.pow 18)).mul (ha00001.pow 6)).mul (ha00003.pow 6)).mul (ha00004.pow 6)).mul (ha00032.pow 3)))

@[irreducible]
def a00138 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00009 ^ 2) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3)
theorem ha00138 : a00138.IsHomogeneous 18 := by
  unfold a00138
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00009.pow 2)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a00139 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00126 ^ 1)
theorem ha00139 : a00139.IsHomogeneous 30 := by
  unfold a00139
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00126.pow 1)))

@[irreducible]
def a00140 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00082 ^ 1 * a00126 ^ 1) + (C ((9 : ℂ) / (20 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1 * a00139 ^ 1)
theorem ha00140 : a00140.IsHomogeneous 97 := by
  unfold a00140
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00082.pow 1)).mul (ha00126.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (20 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha00139.pow 1)))

@[irreducible]
def a00141 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00126 ^ 1)
theorem ha00141 : a00141.IsHomogeneous 30 := by
  unfold a00141
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00126.pow 1)))

@[irreducible]
def a00142 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00082 ^ 1 * a00126 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1 * a00141 ^ 1)
theorem ha00142 : a00142.IsHomogeneous 97 := by
  unfold a00142
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00082.pow 1)).mul (ha00126.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha00141.pow 1)))

@[irreducible]
def a00143 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a00142 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00140 ^ 1)
theorem ha00143 : a00143.IsHomogeneous 97 := by
  unfold a00143
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha00142.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00140.pow 1)))

@[irreducible]
def a00144 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1)
theorem ha00144 : a00144.IsHomogeneous 30 := by
  unfold a00144
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)))

@[irreducible]
def a00145 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00082 ^ 1 * a00126 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1 * a00144 ^ 1)
theorem ha00145 : a00145.IsHomogeneous 97 := by
  unfold a00145
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00082.pow 1)).mul (ha00126.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha00144.pow 1)))

@[irreducible]
def a00146 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00145 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00143 ^ 1)
theorem ha00146 : a00146.IsHomogeneous 97 := by
  unfold a00146
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00145.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00143.pow 1)))

@[irreducible]
def a00147 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00127 ^ 1 * a00146 ^ 1) + (C ((6 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00138 ^ 1)
theorem ha00147 : a00147.IsHomogeneous 121 := by
  unfold a00147
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00127.pow 1)).mul (ha00146.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00138.pow 1)))

@[irreducible]
def a00148 : Poly := (C ((-27 : ℂ) / (1000 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00100 ^ 2 * a00137 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a00147 ^ 1)
theorem ha00148 : a00148.IsHomogeneous 133 := by
  unfold a00148
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (1000 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00100.pow 2)).mul (ha00137.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha00147.pow 1)))

@[irreducible]
def a00149 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00148 ^ 1) + (C ((3 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 6 * a00025 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00127 ^ 1)
theorem ha00149 : a00149.IsHomogeneous 133 := by
  unfold a00149
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00148.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 6)).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00127.pow 1)))

@[irreducible]
def a00150 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00082 ^ 1) + (C ((1 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1)
theorem ha00150 : a00150.IsHomogeneous 67 := by
  unfold a00150
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00082.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)))

@[irreducible]
def a00151 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a00149 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00126 ^ 1 * a00127 ^ 1 * a00150 ^ 1)
theorem ha00151 : a00151.IsHomogeneous 133 := by
  unfold a00151
  exact (((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha00149.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00150.pow 1)))

@[irreducible]
def a00152 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 3 * a00025 ^ 1 * a00127 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00138 ^ 1)
theorem ha00152 : a00152.IsHomogeneous 48 := by
  unfold a00152
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00025.pow 1)).mul (ha00127.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00138.pow 1)))

@[irreducible]
def a00153 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00100 ^ 1 * a00152 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00082 ^ 1 * a00126 ^ 1 * a00127 ^ 1)
theorem ha00153 : a00153.IsHomogeneous 97 := by
  unfold a00153
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00152.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00082.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)))

@[irreducible]
def a00154 : Poly := (C ((-8 : ℂ) / (5 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a00125 ^ 1 * a00153 ^ 1) + (C ((-6 : ℂ) / (5 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a00125 ^ 1 * a00151 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00136 ^ 1)
theorem ha00154 : a00154.IsHomogeneous 212 := by
  unfold a00154
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (5 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha00125.pow 1)).mul (ha00153.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((-6 : ℂ) / (5 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00125.pow 1)).mul (ha00151.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00136.pow 1)))

@[irreducible]
def a00155 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha00155 : a00155.IsHomogeneous 6 := by
  unfold a00155
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00156 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((1 : ℂ) / (12 : ℂ)) * a00014 ^ 1)
theorem ha00156 : a00156.IsHomogeneous 6 := by
  unfold a00156
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a00157 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha00157 : a00157.IsHomogeneous 12 := by
  unfold a00157
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a00158 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00157 ^ 1)
theorem ha00158 : a00158.IsHomogeneous 12 := by
  unfold a00158
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)))

@[irreducible]
def a00159 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1)
theorem ha00159 : a00159.IsHomogeneous 18 := by
  unfold a00159
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00160 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 2 * a00159 ^ 1) + (C ((1 : ℂ) / (486 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 3 * a00005 ^ 3 * a00158 ^ 1)
theorem ha00160 : a00160.IsHomogeneous 30 := by
  unfold a00160
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 2)).mul (ha00159.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (486 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 3)).mul (ha00005.pow 3)).mul (ha00158.pow 1)))

@[irreducible]
def a00161 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1)
theorem ha00161 : a00161.IsHomogeneous 18 := by
  unfold a00161
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00162 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00161 ^ 1)
theorem ha00162 : a00162.IsHomogeneous 18 := by
  unfold a00162
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)))

@[irreducible]
def a00163 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00157 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00009 ^ 1)
theorem ha00163 : a00163.IsHomogeneous 12 := by
  unfold a00163
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00157.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)))

@[irreducible]
def a00164 : Poly := (C ((-1 : ℂ) / (96 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00162 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a00163 ^ 1)
theorem ha00164 : a00164.IsHomogeneous 31 := by
  unfold a00164
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (96 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00162.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00163.pow 1)))

@[irreducible]
def a00165 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1)
theorem ha00165 : a00165.IsHomogeneous 18 := by
  unfold a00165
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)))

@[irreducible]
def a00166 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1)
theorem ha00166 : a00166.IsHomogeneous 12 := by
  unfold a00166
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)))

@[irreducible]
def a00167 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00156 ^ 1)
theorem ha00167 : a00167.IsHomogeneous 12 := by
  unfold a00167
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a00168 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00167 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00166 ^ 1)
theorem ha00168 : a00168.IsHomogeneous 12 := by
  unfold a00168
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00167.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00166.pow 1)))

@[irreducible]
def a00169 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00037 ^ 1)
theorem ha00169 : a00169.IsHomogeneous 18 := by
  unfold a00169
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00037.pow 1)))

@[irreducible]
def a00170 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00165 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00169 ^ 1)
theorem ha00170 : a00170.IsHomogeneous 18 := by
  unfold a00170
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00165.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00169.pow 1)))

@[irreducible]
def a00171 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00156 ^ 1)
theorem ha00171 : a00171.IsHomogeneous 12 := by
  unfold a00171
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a00172 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00032 ^ 1)
theorem ha00172 : a00172.IsHomogeneous 18 := by
  unfold a00172
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a00173 : Poly := (C ((-1 : ℂ) / (24 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00172 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00164 ^ 1) + (C ((1 : ℂ) / (32 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00170 ^ 1)
theorem ha00173 : a00173.IsHomogeneous 31 := by
  unfold a00173
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (24 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00172.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00164.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (32 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00170.pow 1)))

@[irreducible]
def a00174 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00009 ^ 1 * a00025 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00161 ^ 1)
theorem ha00174 : a00174.IsHomogeneous 18 := by
  unfold a00174
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00161.pow 1)))

@[irreducible]
def a00175 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00025 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00025 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00130 ^ 1)
theorem ha00175 : a00175.IsHomogeneous 18 := by
  unfold a00175
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00025.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00176 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00133 ^ 1)
theorem ha00176 : a00176.IsHomogeneous 12 := by
  unfold a00176
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00177 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00176 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00032 ^ 1)
theorem ha00177 : a00177.IsHomogeneous 18 := by
  unfold a00177
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00176.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00032.pow 1)))

@[irreducible]
def a00178 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00156 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha00178 : a00178.IsHomogeneous 12 := by
  unfold a00178
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00156.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00179 : Poly := (C ((-8 : ℂ) / (3 : ℂ)) * a00177 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00178 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00175 ^ 1)
theorem ha00179 : a00179.IsHomogeneous 18 := by
  unfold a00179
  exact ((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (3 : ℂ))).mul (ha00177.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00178.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00175.pow 1)))

@[irreducible]
def a00180 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00040 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00179 ^ 1)
theorem ha00180 : a00180.IsHomogeneous 18 := by
  unfold a00180
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00040.pow 1)).mul (ha00155.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)))

@[irreducible]
def a00181 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00174 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00180 ^ 1)
theorem ha00181 : a00181.IsHomogeneous 37 := by
  unfold a00181
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00174.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00180.pow 1)))

@[irreducible]
def a00182 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00157 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00129 ^ 1)
theorem ha00182 : a00182.IsHomogeneous 36 := by
  unfold a00182
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00157.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00183 : Poly := (C ((-3 : ℂ) / (16 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00007 ^ 1 * a00014 ^ 2 * a00174 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 5 * a00003 ^ 1 * a00005 ^ 1 * a00182 ^ 1)
theorem ha00183 : a00183.IsHomogeneous 43 := by
  unfold a00183
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (16 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00174.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 5)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00182.pow 1)))

@[irreducible]
def a00184 : Poly := (C ((-3 : ℂ) / (16 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00181 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00183 ^ 1)
theorem ha00184 : a00184.IsHomogeneous 43 := by
  unfold a00184
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (16 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00181.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00183.pow 1)))

@[irreducible]
def a00185 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00037 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00168 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00130 ^ 1)
theorem ha00185 : a00185.IsHomogeneous 18 := by
  unfold a00185
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00168.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00186 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00007 ^ 1 * a00014 ^ 2 * a00159 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 8 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00185 ^ 1)
theorem ha00186 : a00186.IsHomogeneous 37 := by
  unfold a00186
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00007.pow 1)).mul (ha00014.pow 2)).mul (ha00159.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 8)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00185.pow 1)))

@[irreducible]
def a00187 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00032 ^ 1 * a00155 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00171 ^ 1)
theorem ha00187 : a00187.IsHomogeneous 18 := by
  unfold a00187
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00032.pow 1)).mul (ha00155.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00171.pow 1)))

@[irreducible]
def a00188 : Poly := (C ((-1 : ℂ) / (864 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00002 ^ 5 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1 * a00187 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00184 ^ 1) + (C ((9 : ℂ) / (8 : ℂ)) * a00000 ^ 1 * a00001 ^ 3 * a00004 ^ 2 * a00186 ^ 1)
theorem ha00188 : a00188.IsHomogeneous 43 := by
  unfold a00188
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (864 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00002.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1)).mul (ha00187.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00184.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (8 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 3)).mul (ha00004.pow 2)).mul (ha00186.pow 1)))

@[irreducible]
def a00189 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00179 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00040 ^ 1)
theorem ha00189 : a00189.IsHomogeneous 18 := by
  unfold a00189
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00179.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00040.pow 1)))

@[irreducible]
def a00190 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00161 ^ 1)
theorem ha00190 : a00190.IsHomogeneous 42 := by
  unfold a00190
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00161.pow 1)))

@[irreducible]
def a00191 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00190 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00189 ^ 1)
theorem ha00191 : a00191.IsHomogeneous 48 := by
  unfold a00191
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00190.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00189.pow 1)))

@[irreducible]
def a00192 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00162 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00189 ^ 1)
theorem ha00192 : a00192.IsHomogeneous 18 := by
  unfold a00192
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00162.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00189.pow 1)))

@[irreducible]
def a00193 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00191 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00192 ^ 1)
theorem ha00193 : a00193.IsHomogeneous 48 := by
  unfold a00193
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00191.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00192.pow 1)))

@[irreducible]
def a00194 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00190 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00191 ^ 1)
theorem ha00194 : a00194.IsHomogeneous 48 := by
  unfold a00194
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00190.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00191.pow 1)))

@[irreducible]
def a00195 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00193 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00194 ^ 1)
theorem ha00195 : a00195.IsHomogeneous 48 := by
  unfold a00195
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00193.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00194.pow 1)))

@[irreducible]
def a00196 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00020 ^ 1 * a00025 ^ 1 * a00042 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00130 ^ 1)
theorem ha00196 : a00196.IsHomogeneous 42 := by
  unfold a00196
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00020.pow 1)).mul (ha00025.pow 1)).mul (ha00042.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00197 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00196 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00169 ^ 1)
theorem ha00197 : a00197.IsHomogeneous 48 := by
  unfold a00197
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00196.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00169.pow 1)))

@[irreducible]
def a00198 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00197 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00170 ^ 1)
theorem ha00198 : a00198.IsHomogeneous 48 := by
  unfold a00198
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00197.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00170.pow 1)))

@[irreducible]
def a00199 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00042 ^ 1)
theorem ha00199 : a00199.IsHomogeneous 27 := by
  unfold a00199
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)))

@[irreducible]
def a00200 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00133 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1)
theorem ha00200 : a00200.IsHomogeneous 12 := by
  unfold a00200
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00201 : Poly := (C ((-1 : ℂ) / (1944 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00200 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00199 ^ 1)
theorem ha00201 : a00201.IsHomogeneous 27 := by
  unfold a00201
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1944 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00200.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00199.pow 1)))

@[irreducible]
def a00202 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00054 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00054 ^ 1 * a00130 ^ 1)
theorem ha00202 : a00202.IsHomogeneous 42 := by
  unfold a00202
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00201.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00054.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00203 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00007 ^ 1 * a00202 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00165 ^ 1)
theorem ha00203 : a00203.IsHomogeneous 48 := by
  unfold a00203
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00007.pow 1)).mul (ha00202.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00165.pow 1)))

@[irreducible]
def a00204 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00203 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00170 ^ 1)
theorem ha00204 : a00204.IsHomogeneous 48 := by
  unfold a00204
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00203.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00170.pow 1)))

@[irreducible]
def a00205 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00198 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00204 ^ 1)
theorem ha00205 : a00205.IsHomogeneous 48 := by
  unfold a00205
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00198.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00204.pow 1)))

@[irreducible]
def a00206 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00133 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00032 ^ 1)
theorem ha00206 : a00206.IsHomogeneous 12 := by
  unfold a00206
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)))

@[irreducible]
def a00207 : Poly := (C ((-1 : ℂ) / (12 : ℂ)) * a00206 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00130 ^ 1)
theorem ha00207 : a00207.IsHomogeneous 12 := by
  unfold a00207
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00206.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00208 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00032 ^ 1 * a00058 ^ 1) + (C ((-1 : ℂ) / (12 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00207 ^ 1)
theorem ha00208 : a00208.IsHomogeneous 24 := by
  unfold a00208
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)).mul (ha00058.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (12 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00207.pow 1)))

@[irreducible]
def a00209 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00208 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a00172 ^ 1)
theorem ha00209 : a00209.IsHomogeneous 37 := by
  unfold a00209
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00208.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00172.pow 1)))

@[irreducible]
def a00210 : Poly := (C ((-8 : ℂ) / (1 : ℂ)) * a00000 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00007 ^ 1 * a00208 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00209 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00002 ^ 4 * a00005 ^ 2 * a00014 ^ 2 * a00172 ^ 1)
theorem ha00210 : a00210.IsHomogeneous 37 := by
  unfold a00210
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (1 : ℂ))).mul (ha00000.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00007.pow 1)).mul (ha00208.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00209.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00002.pow 4)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00172.pow 1)))

@[irreducible]
def a00211 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00205 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00195 ^ 1) + (C ((1 : ℂ) / (162 : ℂ)) * a00000 ^ 4 * a00001 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00210 ^ 1)
theorem ha00211 : a00211.IsHomogeneous 48 := by
  unfold a00211
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00205.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00195.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (162 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00210.pow 1)))

@[irreducible]
def a00212 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00179 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00040 ^ 1 * a00129 ^ 1)
theorem ha00212 : a00212.IsHomogeneous 42 := by
  unfold a00212
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00179.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00040.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00213 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00174 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00212 ^ 1)
theorem ha00213 : a00213.IsHomogeneous 49 := by
  unfold a00213
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00174.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00212.pow 1)))

@[irreducible]
def a00214 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00213 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00212 ^ 1)
theorem ha00214 : a00214.IsHomogeneous 49 := by
  unfold a00214
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00213.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00212.pow 1)))

@[irreducible]
def a00215 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00042 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00042 ^ 1 * a00130 ^ 1)
theorem ha00215 : a00215.IsHomogeneous 36 := by
  unfold a00215
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00042.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00216 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00133 ^ 1) + (C ((3 : ℂ) / (2 : ℂ)) * a00003 ^ 6 * a00032 ^ 1)
theorem ha00216 : a00216.IsHomogeneous 12 := by
  unfold a00216
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 6)).mul (ha00032.pow 1)))

@[irreducible]
def a00217 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00025 ^ 1 * a00133 ^ 1)
theorem ha00217 : a00217.IsHomogeneous 12 := by
  unfold a00217
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00025.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00218 : Poly := (C ((-1 : ℂ) / (243 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00032 ^ 1 * a00216 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00215 ^ 1) + (C ((1 : ℂ) / (54 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00025 ^ 1 * a00217 ^ 1)
theorem ha00218 : a00218.IsHomogeneous 36 := by
  unfold a00218
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (243 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00032.pow 1)).mul (ha00216.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00215.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00025.pow 1)).mul (ha00217.pow 1)))

@[irreducible]
def a00219 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a00155 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00218 ^ 1)
theorem ha00219 : a00219.IsHomogeneous 42 := by
  unfold a00219
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha00155.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00218.pow 1)))

@[irreducible]
def a00220 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00174 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00219 ^ 1)
theorem ha00220 : a00220.IsHomogeneous 49 := by
  unfold a00220
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00174.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00219.pow 1)))

@[irreducible]
def a00221 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00213 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00220 ^ 1)
theorem ha00221 : a00221.IsHomogeneous 49 := by
  unfold a00221
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00213.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00220.pow 1)))

@[irreducible]
def a00222 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00214 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00221 ^ 1)
theorem ha00222 : a00222.IsHomogeneous 49 := by
  unfold a00222
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00214.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00221.pow 1)))

@[irreducible]
def a00223 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00214 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00212 ^ 1)
theorem ha00223 : a00223.IsHomogeneous 49 := by
  unfold a00223
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00214.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00212.pow 1)))

@[irreducible]
def a00224 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00222 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00223 ^ 1)
theorem ha00224 : a00224.IsHomogeneous 49 := by
  unfold a00224
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00222.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00223.pow 1)))

@[irreducible]
def a00225 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a00168 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00037 ^ 1 * a00042 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00037 ^ 1 * a00129 ^ 1)
theorem ha00225 : a00225.IsHomogeneous 42 := by
  unfold a00225
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha00168.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00037.pow 1)).mul (ha00042.pow 1)).mul (ha00130.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00037.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00226 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00159 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00225 ^ 1)
theorem ha00226 : a00226.IsHomogeneous 49 := by
  unfold a00226
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00159.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00225.pow 1)))

@[irreducible]
def a00227 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00226 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00225 ^ 1)
theorem ha00227 : a00227.IsHomogeneous 49 := by
  unfold a00227
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00226.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00225.pow 1)))

@[irreducible]
def a00228 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00054 ^ 1 * a00155 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00054 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00201 ^ 1)
theorem ha00228 : a00228.IsHomogeneous 42 := by
  unfold a00228
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00054.pow 1)).mul (ha00155.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00054.pow 1)).mul (ha00130.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00201.pow 1)))

@[irreducible]
def a00229 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00159 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00228 ^ 1)
theorem ha00229 : a00229.IsHomogeneous 49 := by
  unfold a00229
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00159.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00228.pow 1)))

@[irreducible]
def a00230 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00226 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00229 ^ 1)
theorem ha00230 : a00230.IsHomogeneous 49 := by
  unfold a00230
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00226.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00229.pow 1)))

@[irreducible]
def a00231 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00227 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00230 ^ 1)
theorem ha00231 : a00231.IsHomogeneous 49 := by
  unfold a00231
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00227.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00230.pow 1)))

@[irreducible]
def a00232 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00229 ^ 1) + (C ((1 : ℂ) / (18 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00228 ^ 1)
theorem ha00232 : a00232.IsHomogeneous 49 := by
  unfold a00232
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00229.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (18 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00228.pow 1)))

@[irreducible]
def a00233 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00230 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00232 ^ 1)
theorem ha00233 : a00233.IsHomogeneous 49 := by
  unfold a00233
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00230.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00232.pow 1)))

@[irreducible]
def a00234 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00231 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00233 ^ 1)
theorem ha00234 : a00234.IsHomogeneous 49 := by
  unfold a00234
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00231.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00233.pow 1)))

@[irreducible]
def a00235 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00133 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00042 ^ 1 * a00171 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00009 ^ 1 * a00014 ^ 1 * a00032 ^ 1 * a00129 ^ 1)
theorem ha00235 : a00235.IsHomogeneous 42 := by
  unfold a00235
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00042.pow 1)).mul (ha00171.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00236 : Poly := (C ((-12 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00032 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00058 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00058 ^ 1 * a00155 ^ 1)
theorem ha00236 : a00236.IsHomogeneous 24 := by
  unfold a00236
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-12 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00032.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00133.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00058.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a00237 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00235 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00236 ^ 1)
theorem ha00237 : a00237.IsHomogeneous 42 := by
  unfold a00237
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00235.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00236.pow 1)))

@[irreducible]
def a00238 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00235 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00237 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00236 ^ 1)
theorem ha00238 : a00238.IsHomogeneous 42 := by
  unfold a00238
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00235.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00237.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00236.pow 1)))

@[irreducible]
def a00239 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00237 ^ 1) + (C ((1 : ℂ) / (108 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00236 ^ 1)
theorem ha00239 : a00239.IsHomogeneous 42 := by
  unfold a00239
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00237.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (108 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00236.pow 1)))

@[irreducible]
def a00240 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00238 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00239 ^ 1) + (C ((1 : ℂ) / (72 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00236 ^ 1)
theorem ha00240 : a00240.IsHomogeneous 42 := by
  unfold a00240
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00238.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00239.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (72 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00236.pow 1)))

@[irreducible]
def a00241 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00234 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00224 ^ 1) + (C ((4 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00240 ^ 1)
theorem ha00241 : a00241.IsHomogeneous 49 := by
  unfold a00241
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00234.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00224.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00240.pow 1)))

@[irreducible]
def a00242 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00064 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00218 ^ 1)
theorem ha00242 : a00242.IsHomogeneous 42 := by
  unfold a00242
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00064.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00218.pow 1)))

@[irreducible]
def a00243 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00190 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00242 ^ 1)
theorem ha00243 : a00243.IsHomogeneous 42 := by
  unfold a00243
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00190.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00242.pow 1)))

@[irreducible]
def a00244 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00190 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00243 ^ 1)
theorem ha00244 : a00244.IsHomogeneous 42 := by
  unfold a00244
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00190.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00243.pow 1)))

@[irreducible]
def a00245 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00190 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00244 ^ 1)
theorem ha00245 : a00245.IsHomogeneous 42 := by
  unfold a00245
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00190.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00244.pow 1)))

@[irreducible]
def a00246 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00242 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00243 ^ 1)
theorem ha00246 : a00246.IsHomogeneous 42 := by
  unfold a00246
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00242.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00243.pow 1)))

@[irreducible]
def a00247 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00244 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00246 ^ 1)
theorem ha00247 : a00247.IsHomogeneous 42 := by
  unfold a00247
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00244.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00246.pow 1)))

@[irreducible]
def a00248 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00245 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00247 ^ 1)
theorem ha00248 : a00248.IsHomogeneous 42 := by
  unfold a00248
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00245.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00247.pow 1)))

@[irreducible]
def a00249 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00190 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00245 ^ 1)
theorem ha00249 : a00249.IsHomogeneous 42 := by
  unfold a00249
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00190.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00245.pow 1)))

@[irreducible]
def a00250 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00248 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00249 ^ 1)
theorem ha00250 : a00250.IsHomogeneous 42 := by
  unfold a00250
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00248.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00249.pow 1)))

@[irreducible]
def a00251 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00202 ^ 1)
theorem ha00251 : a00251.IsHomogeneous 42 := by
  unfold a00251
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00196.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00202.pow 1)))

@[irreducible]
def a00252 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00251 ^ 1)
theorem ha00252 : a00252.IsHomogeneous 42 := by
  unfold a00252
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00196.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00251.pow 1)))

@[irreducible]
def a00253 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00196 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00252 ^ 1)
theorem ha00253 : a00253.IsHomogeneous 42 := by
  unfold a00253
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00196.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00252.pow 1)))

@[irreducible]
def a00254 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00202 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00251 ^ 1)
theorem ha00254 : a00254.IsHomogeneous 42 := by
  unfold a00254
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00202.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00251.pow 1)))

@[irreducible]
def a00255 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00252 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00254 ^ 1)
theorem ha00255 : a00255.IsHomogeneous 42 := by
  unfold a00255
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00252.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00254.pow 1)))

@[irreducible]
def a00256 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00253 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00255 ^ 1)
theorem ha00256 : a00256.IsHomogeneous 42 := by
  unfold a00256
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00253.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00255.pow 1)))

@[irreducible]
def a00257 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00202 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00254 ^ 1)
theorem ha00257 : a00257.IsHomogeneous 42 := by
  unfold a00257
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00202.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00254.pow 1)))

@[irreducible]
def a00258 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00255 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00257 ^ 1)
theorem ha00258 : a00258.IsHomogeneous 42 := by
  unfold a00258
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00255.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00257.pow 1)))

@[irreducible]
def a00259 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00256 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00258 ^ 1)
theorem ha00259 : a00259.IsHomogeneous 42 := by
  unfold a00259
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00256.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00258.pow 1)))

@[irreducible]
def a00260 : Poly := (C ((-20 : ℂ) / (81 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00208 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00259 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00250 ^ 1)
theorem ha00260 : a00260.IsHomogeneous 42 := by
  unfold a00260
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-20 : ℂ) / (81 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00208.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00259.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00250.pow 1)))

@[irreducible]
def a00261 : Poly := (C ((-81 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00012 ^ 5 * a00014 ^ 4 * a00160 ^ 1) + (C ((-1 : ℂ) / (2 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 3 * a00012 ^ 3 * a00014 ^ 2 * a00188 ^ 1) + (C ((-1 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 1 * a00211 ^ 1) + (C ((-1 : ℂ) / (7680 : ℂ)) * a00000 ^ 1 * a00001 ^ 18 * a00002 ^ 6 * a00004 ^ 6 * a00005 ^ 6 * a00014 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 4 * a00002 ^ 4 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 2 * a00012 ^ 4 * a00014 ^ 3 * a00173 ^ 1) + (C ((1 : ℂ) / (1536 : ℂ)) * a00000 ^ 1 * a00001 ^ 13 * a00002 ^ 6 * a00004 ^ 5 * a00005 ^ 5 * a00012 ^ 1 * a00241 ^ 1)
theorem ha00261 : a00261.IsHomogeneous 85 := by
  unfold a00261
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-81 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00012.pow 5)).mul (ha00014.pow 4)).mul (ha00160.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 3)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00188.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00211.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (7680 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 18)).mul (ha00002.pow 6)).mul (ha00004.pow 6)).mul (ha00005.pow 6)).mul (ha00014.pow 1)).mul (ha00260.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 2)).mul (ha00012.pow 4)).mul (ha00014.pow 3)).mul (ha00173.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1536 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 13)).mul (ha00002.pow 6)).mul (ha00004.pow 5)).mul (ha00005.pow 5)).mul (ha00012.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a00262 : Poly := (C ((-1 : ℂ) / (648 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00014 ^ 1 * a00155 ^ 1) + (C ((-1 : ℂ) / (279936 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 6 * a00005 ^ 3 * a00128 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00014 ^ 2 * a00102 ^ 1)
theorem ha00262 : a00262.IsHomogeneous 40 := by
  unfold a00262
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00155.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (279936 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).mul (ha00128.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00014.pow 2)).mul (ha00102.pow 1)))

@[irreducible]
def a00263 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00262 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00130 ^ 1)
theorem ha00263 : a00263.IsHomogeneous 48 := by
  unfold a00263
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00264 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00132 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00131 ^ 1)
theorem ha00264 : a00264.IsHomogeneous 25 := by
  unfold a00264
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00156.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00132.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00131.pow 1)))

@[irreducible]
def a00265 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1 * a00104 ^ 1 * a00264 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00263 ^ 1)
theorem ha00265 : a00265.IsHomogeneous 55 := by
  unfold a00265
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00104.pow 1)).mul (ha00264.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00263.pow 1)))

@[irreducible]
def a00266 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00108 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1)
theorem ha00266 : a00266.IsHomogeneous 22 := by
  unfold a00266
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00108.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a00267 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00266 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00109 ^ 1)
theorem ha00267 : a00267.IsHomogeneous 24 := by
  unfold a00267
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00266.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00109.pow 1)))

@[irreducible]
def a00268 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00005 ^ 4 * a00012 ^ 2) + (C ((1 : ℂ) / (432 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00003 ^ 4 * a00004 ^ 3 * a00005 ^ 1) + (C ((1 : ℂ) / (3888 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00012 ^ 1)
theorem ha00268 : a00268.IsHomogeneous 20 := by
  unfold a00268
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00005.pow 4)).mul (ha00012.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00003.pow 4)).mul (ha00004.pow 3)).mul (ha00005.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3888 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00012.pow 1)))

@[irreducible]
def a00269 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00268 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00114 ^ 1)
theorem ha00269 : a00269.IsHomogeneous 22 := by
  unfold a00269
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00268.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00114.pow 1)))

@[irreducible]
def a00270 : Poly := (C ((-432 : ℂ) / (1 : ℂ)) * a00005 ^ 2 * a00269 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00267 ^ 1)
theorem ha00270 : a00270.IsHomogeneous 24 := by
  unfold a00270
  exact ((((isHomogeneous_C (σ := Fin 6) ((-432 : ℂ) / (1 : ℂ))).mul (ha00005.pow 2)).mul (ha00269.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00267.pow 1)))

@[irreducible]
def a00271 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00117 ^ 1 * a00265 ^ 1) + (C ((1 : ℂ) / (12 : ℂ)) * a00105 ^ 1 * a00270 ^ 1)
theorem ha00271 : a00271.IsHomogeneous 79 := by
  unfold a00271
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00117.pow 1)).mul (ha00265.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (12 : ℂ))).mul (ha00105.pow 1)).mul (ha00270.pow 1)))

@[irreducible]
def a00272 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00009 ^ 1 * a00025 ^ 1 * a00262 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00025 ^ 1 * a00103 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00009 ^ 1 * a00103 ^ 1 * a00130 ^ 1)
theorem ha00272 : a00272.IsHomogeneous 54 := by
  unfold a00272
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00009.pow 1)).mul (ha00025.pow 1)).mul (ha00262.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).mul (ha00103.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00009.pow 1)).mul (ha00103.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00273 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00264 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00104 ^ 1)
theorem ha00273 : a00273.IsHomogeneous 31 := by
  unfold a00273
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00104.pow 1)))

@[irreducible]
def a00274 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00025 ^ 1 * a00264 ^ 1)
theorem ha00274 : a00274.IsHomogeneous 31 := by
  unfold a00274
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha00130.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00025.pow 1)).mul (ha00264.pow 1)))

@[irreducible]
def a00275 : Poly := (C ((-1 : ℂ) / (288 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 4 * a00005 ^ 2 * a00025 ^ 1 * a00274 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00003 ^ 1 * a00005 ^ 1 * a00104 ^ 1 * a00273 ^ 1) + (C ((3 : ℂ) / (16 : ℂ)) * a00000 ^ 1 * a00001 ^ 4 * a00004 ^ 2 * a00272 ^ 1)
theorem ha00275 : a00275.IsHomogeneous 61 := by
  unfold a00275
  exact (((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (288 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 4)).mul (ha00005.pow 2)).mul (ha00025.pow 1)).mul (ha00274.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00005.pow 1)).mul (ha00104.pow 1)).mul (ha00273.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (16 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 4)).mul (ha00004.pow 2)).mul (ha00272.pow 1)))

@[irreducible]
def a00276 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 2 * a00119 ^ 1) + (C ((1 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00155 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00128 ^ 1)
theorem ha00276 : a00276.IsHomogeneous 29 := by
  unfold a00276
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 2)).mul (ha00119.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00155.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00128.pow 1)))

@[irreducible]
def a00277 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00118 ^ 1 * a00276 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00120 ^ 1 * a00275 ^ 1)
theorem ha00277 : a00277.IsHomogeneous 92 := by
  unfold a00277
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00118.pow 1)).mul (ha00276.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00120.pow 1)).mul (ha00275.pow 1)))

@[irreducible]
def a00278 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00262 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 4 * a00103 ^ 1)
theorem ha00278 : a00278.IsHomogeneous 46 := by
  unfold a00278
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00262.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 4)).mul (ha00103.pow 1)))

@[irreducible]
def a00279 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00264 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00104 ^ 1 * a00130 ^ 1)
theorem ha00279 : a00279.IsHomogeneous 31 := by
  unfold a00279
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00264.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00104.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00280 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00278 ^ 1) + (C ((1 : ℂ) / (324 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00279 ^ 1)
theorem ha00280 : a00280.IsHomogeneous 46 := by
  unfold a00280
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00278.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (324 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00279.pow 1)))

@[irreducible]
def a00281 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00103 ^ 1 * a00280 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00025 ^ 1 * a00121 ^ 1 * a00262 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00121 ^ 1 * a00130 ^ 1)
theorem ha00281 : a00281.IsHomogeneous 96 := by
  unfold a00281
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00103.pow 1)).mul (ha00280.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00025.pow 1)).mul (ha00121.pow 1)).mul (ha00262.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00121.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00282 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00104 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00264 ^ 1)
theorem ha00282 : a00282.IsHomogeneous 31 := by
  unfold a00282
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00104.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00264.pow 1)))

@[irreducible]
def a00283 : Poly := (C ((-1 : ℂ) / (54 : ℂ)) * a00000 ^ 5 * a00001 ^ 8 * a00003 ^ 1 * a00004 ^ 4 * a00005 ^ 1 * a00025 ^ 1 * a00130 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00282 ^ 1)
theorem ha00283 : a00283.IsHomogeneous 31 := by
  unfold a00283
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (54 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 8)).mul (ha00003.pow 1)).mul (ha00004.pow 4)).mul (ha00005.pow 1)).mul (ha00025.pow 1)).mul (ha00130.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00282.pow 1)))

@[irreducible]
def a00284 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00103 ^ 1 * a00283 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00122 ^ 1 * a00133 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00032 ^ 1 * a00122 ^ 1 * a00262 ^ 1)
theorem ha00284 : a00284.IsHomogeneous 79 := by
  unfold a00284
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00103.pow 1)).mul (ha00283.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00122.pow 1)).mul (ha00133.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00032.pow 1)).mul (ha00122.pow 1)).mul (ha00262.pow 1)))

@[irreducible]
def a00285 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 2 * a00277 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 5 * a00001 ^ 4 * a00002 ^ 3 * a00003 ^ 2 * a00004 ^ 2 * a00005 ^ 2 * a00284 ^ 1) + (C ((54 : ℂ) / (1 : ℂ)) * a00000 ^ 1 * a00281 ^ 1)
theorem ha00285 : a00285.IsHomogeneous 97 := by
  unfold a00285
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 2)).mul (ha00277.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 5)).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00003.pow 2)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00284.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((54 : ℂ) / (1 : ℂ))).mul (ha00000.pow 1)).mul (ha00281.pow 1)))

@[irreducible]
def a00286 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00123 ^ 1 * a00262 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00285 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 6 * a00103 ^ 1 * a00123 ^ 1)
theorem ha00286 : a00286.IsHomogeneous 145 := by
  unfold a00286
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00123.pow 1)).mul (ha00262.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00285.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 6)).mul (ha00103.pow 1)).mul (ha00123.pow 1)))

@[irreducible]
def a00287 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00103 ^ 1 * a00123 ^ 1 * a00271 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00105 ^ 1 * a00117 ^ 1 * a00286 ^ 1)
theorem ha00287 : a00287.IsHomogeneous 224 := by
  unfold a00287
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00103.pow 1)).mul (ha00123.pow 1)).mul (ha00271.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00286.pow 1)))

@[irreducible]
def a00288 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha00288 : a00288.IsHomogeneous 6 := by
  unfold a00288
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00289 : Poly := (C ((-1 : ℂ) / (46656 : ℂ)) * a00000 ^ 8 * a00001 ^ 8 * a00002 ^ 8 * a00003 ^ 2 * a00004 ^ 4 * a00005 ^ 4 * a00012 ^ 4) + (C ((-1 : ℂ) / (46656 : ℂ)) * a00000 ^ 9 * a00001 ^ 12 * a00002 ^ 3 * a00003 ^ 1 * a00004 ^ 6 * a00005 ^ 3 * a00102 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 4 * a00009 ^ 1 * a00102 ^ 2) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 3 * a00002 ^ 9 * a00003 ^ 1 * a00005 ^ 3 * a00012 ^ 6 * a00288 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 4 * a00001 ^ 4 * a00002 ^ 4 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 2 * a00102 ^ 1 * a00131 ^ 1)
theorem ha00289 : a00289.IsHomogeneous 58 := by
  unfold a00289
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (46656 : ℂ))).mul (ha00000.pow 8)).mul (ha00001.pow 8)).mul (ha00002.pow 8)).mul (ha00003.pow 2)).mul (ha00004.pow 4)).mul (ha00005.pow 4)).mul (ha00012.pow 4)).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (46656 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 12)).mul (ha00002.pow 3)).mul (ha00003.pow 1)).mul (ha00004.pow 6)).mul (ha00005.pow 3)).mul (ha00102.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 4)).mul (ha00009.pow 1)).mul (ha00102.pow 2))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 3)).mul (ha00002.pow 9)).mul (ha00003.pow 1)).mul (ha00005.pow 3)).mul (ha00012.pow 6)).mul (ha00288.pow 1))).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 4)).mul (ha00001.pow 4)).mul (ha00002.pow 4)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 2)).mul (ha00102.pow 1)).mul (ha00131.pow 1)))

@[irreducible]
def a00290 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00124 ^ 1 * a00265 ^ 1) + (C ((1 : ℂ) / (4 : ℂ)) * a00003 ^ 2 * a00014 ^ 1 * a00105 ^ 1 * a00289 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00003 ^ 6 * a00105 ^ 1 * a00124 ^ 1)
theorem ha00290 : a00290.IsHomogeneous 121 := by
  unfold a00290
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00124.pow 1)).mul (ha00265.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (4 : ℂ))).mul (ha00003.pow 2)).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00289.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00003.pow 6)).mul (ha00105.pow 1)).mul (ha00124.pow 1)))

@[irreducible]
def a00291 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00014 ^ 1 * a00105 ^ 1 * a00124 ^ 1 * a00285 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00123 ^ 1 * a00290 ^ 1)
theorem ha00291 : a00291.IsHomogeneous 218 := by
  unfold a00291
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00014.pow 1)).mul (ha00105.pow 1)).mul (ha00124.pow 1)).mul (ha00285.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00123.pow 1)).mul (ha00290.pow 1)))

@[irreducible]
def a00292 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00124 ^ 1 * a00287 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00117 ^ 1 * a00291 ^ 1)
theorem ha00292 : a00292.IsHomogeneous 284 := by
  unfold a00292
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00124.pow 1)).mul (ha00287.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00117.pow 1)).mul (ha00291.pow 1)))

@[irreducible]
def a00293 : Poly := (C ((-3 : ℂ) / (32 : ℂ)) * a00000 ^ 1 * a00001 ^ 5 * a00004 ^ 2 * a00005 ^ 1 * a00012 ^ 2 * a00014 ^ 1 * a00211 ^ 1) + (C ((-1 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00005 ^ 1 * a00012 ^ 3 * a00014 ^ 2 * a00188 ^ 1) + (C ((-1 : ℂ) / (1536 : ℂ)) * a00000 ^ 1 * a00001 ^ 14 * a00002 ^ 3 * a00004 ^ 5 * a00005 ^ 4 * a00014 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 1 * a00003 ^ 1 * a00012 ^ 4 * a00014 ^ 3 * a00173 ^ 1) + (C ((1 : ℂ) / (384 : ℂ)) * a00000 ^ 1 * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 4 * a00005 ^ 3 * a00012 ^ 1 * a00241 ^ 1)
theorem ha00293 : a00293.IsHomogeneous 75 := by
  unfold a00293
  exact ((((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (32 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 5)).mul (ha00004.pow 2)).mul (ha00005.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00211.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00005.pow 1)).mul (ha00012.pow 3)).mul (ha00014.pow 2)).mul (ha00188.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1536 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 14)).mul (ha00002.pow 3)).mul (ha00004.pow 5)).mul (ha00005.pow 4)).mul (ha00014.pow 1)).mul (ha00260.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 1)).mul (ha00003.pow 1)).mul (ha00012.pow 4)).mul (ha00014.pow 3)).mul (ha00173.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (384 : ℂ))).mul (ha00000.pow 1)).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 4)).mul (ha00005.pow 3)).mul (ha00012.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a00294 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00125 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00293 ^ 1)
theorem ha00294 : a00294.IsHomogeneous 111 := by
  unfold a00294
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00125.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00293.pow 1)))

@[irreducible]
def a00295 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00294 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00125 ^ 1 * a00292 ^ 1)
theorem ha00295 : a00295.IsHomogeneous 389 := by
  unfold a00295
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00294.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00125.pow 1)).mul (ha00292.pow 1)))

@[irreducible]
def a00296 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00261 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00295 ^ 1)
theorem ha00296 : a00296.IsHomogeneous 468 := by
  unfold a00296
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00261.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00295.pow 1)))

@[irreducible]
def a00297 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00129 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00130 ^ 1)
theorem ha00297 : a00297.IsHomogeneous 30 := by
  unfold a00297
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00298 : Poly := (C ((-1 : ℂ) / (972 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00032 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00297 ^ 1)
theorem ha00298 : a00298.IsHomogeneous 30 := by
  unfold a00298
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (972 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00032.pow 1)).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00297.pow 1)))

@[irreducible]
def a00299 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00009 ^ 1) + (C ((1 : ℂ) / (216 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3)
theorem ha00299 : a00299.IsHomogeneous 15 := by
  unfold a00299
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00009.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (216 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a00300 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00298 ^ 1)
theorem ha00300 : a00300.IsHomogeneous 54 := by
  unfold a00300
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a00301 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00100 ^ 1 * a00300 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00260 ^ 1)
theorem ha00301 : a00301.IsHomogeneous 96 := by
  unfold a00301
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00300.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a00302 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00299 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a00301 ^ 1)
theorem ha00302 : a00302.IsHomogeneous 114 := by
  unfold a00302
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00299.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha00301.pow 1)))

@[irreducible]
def a00303 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00302 ^ 1)
theorem ha00303 : a00303.IsHomogeneous 114 := by
  unfold a00303
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00302.pow 1)))

@[irreducible]
def a00304 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00127 ^ 1 * a00298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00303 ^ 1)
theorem ha00304 : a00304.IsHomogeneous 114 := by
  unfold a00304
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00127.pow 1)).mul (ha00298.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00303.pow 1)))

@[irreducible]
def a00305 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00260 ^ 1)
theorem ha00305 : a00305.IsHomogeneous 66 := by
  unfold a00305
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a00306 : Poly := (C ((-3 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a00305 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00304 ^ 1)
theorem ha00306 : a00306.IsHomogeneous 114 := by
  unfold a00306
  exact (((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00305.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00304.pow 1)))

@[irreducible]
def a00307 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00306 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00296 ^ 1)
theorem ha00307 : a00307.IsHomogeneous 540 := by
  unfold a00307
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00306.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00296.pow 1)))

@[irreducible]
def a00308 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a00298 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00299 ^ 1)
theorem ha00308 : a00308.IsHomogeneous 48 := by
  unfold a00308
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00299.pow 1)))

@[irreducible]
def a00309 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1 * a00127 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00308 ^ 1)
theorem ha00309 : a00309.IsHomogeneous 54 := by
  unfold a00309
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00308.pow 1)))

@[irreducible]
def a00310 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00309 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a00260 ^ 1)
theorem ha00310 : a00310.IsHomogeneous 90 := by
  unfold a00310
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00309.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a00311 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00310 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a00296 ^ 1)
theorem ha00311 : a00311.IsHomogeneous 516 := by
  unfold a00311
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00310.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00296.pow 1)))

@[irreducible]
def a00312 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00307 ^ 1) + (C ((16 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00311 ^ 1)
theorem ha00312 : a00312.IsHomogeneous 540 := by
  unfold a00312
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00307.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((16 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00311.pow 1)))

@[irreducible]
def a00313 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00129 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00042 ^ 1 * a00298 ^ 1)
theorem ha00313 : a00313.IsHomogeneous 54 := by
  unfold a00313
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00129.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00042.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a00314 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00017 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha00314 : a00314.IsHomogeneous 6 := by
  unfold a00314
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00017.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00315 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00314 ^ 1) + (C ((32 : ℂ) / (1 : ℂ)) * a00003 ^ 6)
theorem ha00315 : a00315.IsHomogeneous 6 := by
  unfold a00315
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00314.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((32 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00316 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((12 : ℂ) / (5 : ℂ)) * a00003 ^ 6)
theorem ha00316 : a00316.IsHomogeneous 6 := by
  unfold a00316
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00317 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00014 ^ 1 * a00316 ^ 1) + (C ((1 : ℂ) / (3240 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00315 ^ 1)
theorem ha00317 : a00317.IsHomogeneous 21 := by
  unfold a00317
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00316.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3240 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00315.pow 1)))

@[irreducible]
def a00318 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00064 ^ 1 * a00317 ^ 1) + (C ((18 : ℂ) / (5 : ℂ)) * a00129 ^ 1 * a00218 ^ 1)
theorem ha00318 : a00318.IsHomogeneous 57 := by
  unfold a00318
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00064.pow 1)).mul (ha00317.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((18 : ℂ) / (5 : ℂ))).mul (ha00129.pow 1)).mul (ha00218.pow 1)))

@[irreducible]
def a00319 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00130 ^ 1 * a00201 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1 * a00129 ^ 1 * a00130 ^ 1) + (C ((7 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00042 ^ 1 * a00054 ^ 1)
theorem ha00319 : a00319.IsHomogeneous 57 := by
  unfold a00319
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00130.pow 1)).mul (ha00201.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).mul (ha00129.pow 1)).mul (ha00130.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)).mul (ha00054.pow 1)))

@[irreducible]
def a00320 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((1 : ℂ) / (6 : ℂ)) * a00009 ^ 1)
theorem ha00320 : a00320.IsHomogeneous 6 := by
  unfold a00320
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00009.pow 1)))

@[irreducible]
def a00321 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((2 : ℂ) / (7 : ℂ)) * a00320 ^ 1)
theorem ha00321 : a00321.IsHomogeneous 6 := by
  unfold a00321
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00320.pow 1)))

@[irreducible]
def a00322 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1)
theorem ha00322 : a00322.IsHomogeneous 6 := by
  unfold a00322
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a00323 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6) + (C ((2 : ℂ) / (7 : ℂ)) * a00322 ^ 1)
theorem ha00323 : a00323.IsHomogeneous 6 := by
  unfold a00323
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (7 : ℂ))).mul (ha00322.pow 1)))

@[irreducible]
def a00324 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00321 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00323 ^ 1)
theorem ha00324 : a00324.IsHomogeneous 6 := by
  unfold a00324
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00321.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00323.pow 1)))

@[irreducible]
def a00325 : Poly := (C ((-8 : ℂ) / (7 : ℂ)) * a00042 ^ 1 * a00133 ^ 1 * a00207 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00058 ^ 1 * a00324 ^ 1) + (C ((6 : ℂ) / (7 : ℂ)) * a00003 ^ 3 * a00058 ^ 1 * a00129 ^ 1 * a00133 ^ 1)
theorem ha00325 : a00325.IsHomogeneous 42 := by
  unfold a00325
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (7 : ℂ))).mul (ha00042.pow 1)).mul (ha00133.pow 1)).mul (ha00207.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00058.pow 1)).mul (ha00324.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (7 : ℂ))).mul (ha00003.pow 3)).mul (ha00058.pow 1)).mul (ha00129.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00326 : Poly := (C ((-36 : ℂ) / (5 : ℂ)) * a00319 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00318 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00313 ^ 1) + (C ((7 : ℂ) / (540 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00325 ^ 1)
theorem ha00326 : a00326.IsHomogeneous 57 := by
  unfold a00326
  exact (((((isHomogeneous_C (σ := Fin 6) ((-36 : ℂ) / (5 : ℂ))).mul (ha00319.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00318.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00313.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((7 : ℂ) / (540 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00325.pow 1)))

@[irreducible]
def a00327 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00260 ^ 1) + (C ((5 : ℂ) / (18 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00326 ^ 1)
theorem ha00327 : a00327.IsHomogeneous 102 := by
  unfold a00327
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00260.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (18 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00326.pow 1)))

@[irreducible]
def a00328 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00134 ^ 1 * a00312 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00327 ^ 1)
theorem ha00328 : a00328.IsHomogeneous 600 := by
  unfold a00328
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00134.pow 1)).mul (ha00312.pow 1)).add ((((((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00327.pow 1)))

@[irreducible]
def a00329 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00139 ^ 1)
theorem ha00329 : a00329.IsHomogeneous 30 := by
  unfold a00329
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00139.pow 1)))

@[irreducible]
def a00330 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00329 ^ 1)
theorem ha00330 : a00330.IsHomogeneous 30 := by
  unfold a00330
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00329.pow 1)))

@[irreducible]
def a00331 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00139 ^ 1)
theorem ha00331 : a00331.IsHomogeneous 30 := by
  unfold a00331
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00139.pow 1)))

@[irreducible]
def a00332 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00329 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00331 ^ 1)
theorem ha00332 : a00332.IsHomogeneous 30 := by
  unfold a00332
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00329.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00331.pow 1)))

@[irreducible]
def a00333 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00330 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00332 ^ 1)
theorem ha00333 : a00333.IsHomogeneous 30 := by
  unfold a00333
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00330.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00332.pow 1)))

@[irreducible]
def a00334 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00330 ^ 1)
theorem ha00334 : a00334.IsHomogeneous 30 := by
  unfold a00334
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00330.pow 1)))

@[irreducible]
def a00335 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00333 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00334 ^ 1)
theorem ha00335 : a00335.IsHomogeneous 30 := by
  unfold a00335
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00333.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00334.pow 1)))

@[irreducible]
def a00336 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00331 ^ 1)
theorem ha00336 : a00336.IsHomogeneous 30 := by
  unfold a00336
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00331.pow 1)))

@[irreducible]
def a00337 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00332 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00336 ^ 1)
theorem ha00337 : a00337.IsHomogeneous 30 := by
  unfold a00337
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00332.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00336.pow 1)))

@[irreducible]
def a00338 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00333 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00337 ^ 1)
theorem ha00338 : a00338.IsHomogeneous 30 := by
  unfold a00338
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00333.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00337.pow 1)))

@[irreducible]
def a00339 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00335 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00338 ^ 1)
theorem ha00339 : a00339.IsHomogeneous 30 := by
  unfold a00339
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00335.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00338.pow 1)))

@[irreducible]
def a00340 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00064 ^ 1)
theorem ha00340 : a00340.IsHomogeneous 39 := by
  unfold a00340
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00064.pow 1)))

@[irreducible]
def a00341 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00340 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00064 ^ 1)
theorem ha00341 : a00341.IsHomogeneous 39 := by
  unfold a00341
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00340.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00064.pow 1)))

@[irreducible]
def a00342 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00340 ^ 1)
theorem ha00342 : a00342.IsHomogeneous 39 := by
  unfold a00342
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00340.pow 1)))

@[irreducible]
def a00343 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00341 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00342 ^ 1)
theorem ha00343 : a00343.IsHomogeneous 39 := by
  unfold a00343
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00341.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00342.pow 1)))

@[irreducible]
def a00344 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00342 ^ 1)
theorem ha00344 : a00344.IsHomogeneous 39 := by
  unfold a00344
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00342.pow 1)))

@[irreducible]
def a00345 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00343 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00344 ^ 1)
theorem ha00345 : a00345.IsHomogeneous 39 := by
  unfold a00345
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00343.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00344.pow 1)))

@[irreducible]
def a00346 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00341 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00064 ^ 1)
theorem ha00346 : a00346.IsHomogeneous 39 := by
  unfold a00346
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00341.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00064.pow 1)))

@[irreducible]
def a00347 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00343 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00346 ^ 1)
theorem ha00347 : a00347.IsHomogeneous 39 := by
  unfold a00347
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00343.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00346.pow 1)))

@[irreducible]
def a00348 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00345 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00347 ^ 1)
theorem ha00348 : a00348.IsHomogeneous 39 := by
  unfold a00348
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00345.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00347.pow 1)))

@[irreducible]
def a00349 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00344 ^ 1)
theorem ha00349 : a00349.IsHomogeneous 39 := by
  unfold a00349
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00344.pow 1)))

@[irreducible]
def a00350 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00345 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00349 ^ 1)
theorem ha00350 : a00350.IsHomogeneous 39 := by
  unfold a00350
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00345.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00349.pow 1)))

@[irreducible]
def a00351 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00348 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00350 ^ 1)
theorem ha00351 : a00351.IsHomogeneous 39 := by
  unfold a00351
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00348.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00350.pow 1)))

@[irreducible]
def a00352 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00091 ^ 1)
theorem ha00352 : a00352.IsHomogeneous 30 := by
  unfold a00352
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00091.pow 1)))

@[irreducible]
def a00353 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00092 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00352 ^ 1)
theorem ha00353 : a00353.IsHomogeneous 30 := by
  unfold a00353
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00092.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00352.pow 1)))

@[irreducible]
def a00354 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00093 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00353 ^ 1)
theorem ha00354 : a00354.IsHomogeneous 30 := by
  unfold a00354
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00093.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00353.pow 1)))

@[irreducible]
def a00355 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00094 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00352 ^ 1)
theorem ha00355 : a00355.IsHomogeneous 30 := by
  unfold a00355
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00094.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00352.pow 1)))

@[irreducible]
def a00356 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00095 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00353 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00355 ^ 1)
theorem ha00356 : a00356.IsHomogeneous 30 := by
  unfold a00356
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00095.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00353.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00355.pow 1)))

@[irreducible]
def a00357 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00096 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00356 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00354 ^ 1)
theorem ha00357 : a00357.IsHomogeneous 30 := by
  unfold a00357
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00096.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00356.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00354.pow 1)))

@[irreducible]
def a00358 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00054 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00097 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00355 ^ 1)
theorem ha00358 : a00358.IsHomogeneous 30 := by
  unfold a00358
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00097.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00355.pow 1)))

@[irreducible]
def a00359 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00098 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00356 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00358 ^ 1)
theorem ha00359 : a00359.IsHomogeneous 30 := by
  unfold a00359
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00098.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00356.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00358.pow 1)))

@[irreducible]
def a00360 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00099 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00357 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00359 ^ 1)
theorem ha00360 : a00360.IsHomogeneous 30 := by
  unfold a00360
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00099.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00357.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00359.pow 1)))

@[irreducible]
def a00361 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00360 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00351 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00339 ^ 1) + (C ((5 : ℂ) / (81 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00058 ^ 1 * a00133 ^ 1)
theorem ha00361 : a00361.IsHomogeneous 42 := by
  unfold a00361
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00360.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00351.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00339.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (81 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00058.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00362 : Poly := (C ((-3 : ℂ) / (100 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a00361 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00134 ^ 1)
theorem ha00362 : a00362.IsHomogeneous 103 := by
  unfold a00362
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (100 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha00361.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00134.pow 1)))

@[irreducible]
def a00363 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00134 ^ 1 * a00362 ^ 1) + (C ((1 : ℂ) / (100 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 3 * a00100 ^ 1 * a00328 ^ 1)
theorem ha00363 : a00363.IsHomogeneous 661 := by
  unfold a00363
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00134.pow 1)).mul (ha00362.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (100 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 3)).mul (ha00100.pow 1)).mul (ha00328.pow 1)))

@[irreducible]
def a00364 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00134 ^ 2 * a00154 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00006 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00363 ^ 1)
theorem ha00364 : a00364.IsHomogeneous 689 := by
  unfold a00364
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00134.pow 2)).mul (ha00154.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00363.pow 1)))

@[irreducible]
def a00365 : Poly := (C ((-1 : ℂ) / (144 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00012 ^ 1 * a00082 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a00014 ^ 1 * a00061 ^ 1) + (C ((1 : ℂ) / (720 : ℂ)) * a00001 ^ 9 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00014 ^ 1 * a00100 ^ 1)
theorem ha00365 : a00365.IsHomogeneous 60 := by
  unfold a00365
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (144 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00012.pow 1)).mul (ha00082.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 1)).mul (ha00061.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (720 : ℂ))).mul (ha00001.pow 9)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a00366 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00082 ^ 1)
theorem ha00366 : a00366.IsHomogeneous 49 := by
  unfold a00366
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00082.pow 1)))

@[irreducible]
def a00367 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00125 ^ 1 * a00365 ^ 1) + (C ((1 : ℂ) / (144 : ℂ)) * a00004 ^ 1 * a00101 ^ 1 * a00366 ^ 1)
theorem ha00367 : a00367.IsHomogeneous 129 := by
  unfold a00367
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00125.pow 1)).mul (ha00365.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (144 : ℂ))).mul (ha00004.pow 1)).mul (ha00101.pow 1)).mul (ha00366.pow 1)))

@[irreducible]
def a00368 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1)
theorem ha00368 : a00368.IsHomogeneous 6 := by
  unfold a00368
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00032.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)))

@[irreducible]
def a00369 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00148 ^ 1) + (C ((1 : ℂ) / (25 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00368 ^ 1)
theorem ha00369 : a00369.IsHomogeneous 139 := by
  unfold a00369
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00148.pow 1)).add (((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (25 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a00370 : Poly := (C ((-1 : ℂ) / (144 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00025 ^ 1 * a00032 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00042 ^ 1)
theorem ha00370 : a00370.IsHomogeneous 30 := by
  unfold a00370
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (144 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00025.pow 1)).mul (ha00032.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00371 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00137 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1 * a00370 ^ 1)
theorem ha00371 : a00371.IsHomogeneous 97 := by
  unfold a00371
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00137.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha00370.pow 1)))

@[irreducible]
def a00372 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00006 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1)
theorem ha00372 : a00372.IsHomogeneous 13 := by
  unfold a00372
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00006.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)))

@[irreducible]
def a00373 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00372 ^ 1) + (C ((50 : ℂ) / (3 : ℂ)) * a00138 ^ 1 * a00146 ^ 1)
theorem ha00373 : a00373.IsHomogeneous 115 := by
  unfold a00373
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00372.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((50 : ℂ) / (3 : ℂ))).mul (ha00138.pow 1)).mul (ha00146.pow 1)))

@[irreducible]
def a00374 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00025 ^ 1) + (C ((2 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00042 ^ 1 * a00368 ^ 1)
theorem ha00374 : a00374.IsHomogeneous 37 := by
  unfold a00374
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a00375 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00374 ^ 1) + (C ((4 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00126 ^ 1)
theorem ha00375 : a00375.IsHomogeneous 37 := by
  unfold a00375
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00374.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00126.pow 1)))

@[irreducible]
def a00376 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00139 ^ 1) + (C ((3 : ℂ) / (5 : ℂ)) * a00100 ^ 1 * a00375 ^ 1)
theorem ha00376 : a00376.IsHomogeneous 73 := by
  unfold a00376
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00139.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (5 : ℂ))).mul (ha00100.pow 1)).mul (ha00375.pow 1)))

@[irreducible]
def a00377 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00061 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (64 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00376 ^ 1)
theorem ha00377 : a00377.IsHomogeneous 96 := by
  unfold a00377
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00061.pow 1)).mul (ha00126.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (64 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00376.pow 1)))

@[irreducible]
def a00378 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00025 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00042 ^ 1 * a00368 ^ 1)
theorem ha00378 : a00378.IsHomogeneous 37 := by
  unfold a00378
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a00379 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00378 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00126 ^ 1)
theorem ha00379 : a00379.IsHomogeneous 37 := by
  unfold a00379
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00378.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00126.pow 1)))

@[irreducible]
def a00380 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00141 ^ 1) + (C ((2 : ℂ) / (5 : ℂ)) * a00100 ^ 1 * a00379 ^ 1)
theorem ha00380 : a00380.IsHomogeneous 73 := by
  unfold a00380
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00141.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (5 : ℂ))).mul (ha00100.pow 1)).mul (ha00379.pow 1)))

@[irreducible]
def a00381 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00061 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00380 ^ 1)
theorem ha00381 : a00381.IsHomogeneous 96 := by
  unfold a00381
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00061.pow 1)).mul (ha00126.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00380.pow 1)))

@[irreducible]
def a00382 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a00381 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00377 ^ 1)
theorem ha00382 : a00382.IsHomogeneous 96 := by
  unfold a00382
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha00381.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00377.pow 1)))

@[irreducible]
def a00383 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00025 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00042 ^ 1 * a00368 ^ 1)
theorem ha00383 : a00383.IsHomogeneous 37 := by
  unfold a00383
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a00384 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00383 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00126 ^ 1)
theorem ha00384 : a00384.IsHomogeneous 37 := by
  unfold a00384
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00383.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00126.pow 1)))

@[irreducible]
def a00385 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00144 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00100 ^ 1 * a00384 ^ 1)
theorem ha00385 : a00385.IsHomogeneous 73 := by
  unfold a00385
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00144.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00100.pow 1)).mul (ha00384.pow 1)))

@[irreducible]
def a00386 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00061 ^ 1 * a00126 ^ 1) + (C ((1 : ℂ) / (36 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00385 ^ 1)
theorem ha00386 : a00386.IsHomogeneous 96 := by
  unfold a00386
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00061.pow 1)).mul (ha00126.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (36 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00385.pow 1)))

@[irreducible]
def a00387 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a00386 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00382 ^ 1)
theorem ha00387 : a00387.IsHomogeneous 96 := by
  unfold a00387
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha00386.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00382.pow 1)))

@[irreducible]
def a00388 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 1 * a00127 ^ 1 * a00387 ^ 1) + (C ((1 : ℂ) / (400 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00373 ^ 1)
theorem ha00388 : a00388.IsHomogeneous 126 := by
  unfold a00388
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 1)).mul (ha00127.pow 1)).mul (ha00387.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (400 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00373.pow 1)))

@[irreducible]
def a00389 : Poly := (C ((-3 : ℂ) / (1600 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00100 ^ 1 * a00371 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 3 * a00388 ^ 1)
theorem ha00389 : a00389.IsHomogeneous 144 := by
  unfold a00389
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1600 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00100.pow 1)).mul (ha00371.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 3)).mul (ha00388.pow 1)))

@[irreducible]
def a00390 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00389 ^ 1) + (C ((1 : ℂ) / (48 : ℂ)) * a00001 ^ 4 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a00369 ^ 1)
theorem ha00390 : a00390.IsHomogeneous 174 := by
  unfold a00390
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00389.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (48 : ℂ))).mul (ha00001.pow 4)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00369.pow 1)))

@[irreducible]
def a00391 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1) + (C ((1 : ℂ) / (15 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00100 ^ 1)
theorem ha00391 : a00391.IsHomogeneous 43 := by
  unfold a00391
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (15 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00100.pow 1)))

@[irreducible]
def a00392 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 2) + (C ((144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00100 ^ 1)
theorem ha00392 : a00392.IsHomogeneous 91 := by
  unfold a00392
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 2)).add (((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a00393 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00392 ^ 1) + (C ((144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00100 ^ 1)
theorem ha00393 : a00393.IsHomogeneous 91 := by
  unfold a00393
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00392.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a00394 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00393 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 2)
theorem ha00394 : a00394.IsHomogeneous 91 := by
  unfold a00394
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00393.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 2)))

@[irreducible]
def a00395 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00394 ^ 1) + (C ((144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00100 ^ 1)
theorem ha00395 : a00395.IsHomogeneous 91 := by
  unfold a00395
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00394.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00100.pow 1)))

@[irreducible]
def a00396 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00395 ^ 1) + (C ((9 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 4 * a00100 ^ 1 * a00391 ^ 1)
theorem ha00396 : a00396.IsHomogeneous 115 := by
  unfold a00396
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00395.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha00391.pow 1)))

@[irreducible]
def a00397 : Poly := (C ((-9 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00150 ^ 1 * a00151 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00396 ^ 1)
theorem ha00397 : a00397.IsHomogeneous 205 := by
  unfold a00397
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00150.pow 1)).mul (ha00151.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00396.pow 1)))

@[irreducible]
def a00398 : Poly := (C ((-144 : ℂ) / (1 : ℂ)) * a00001 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00390 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00397 ^ 1)
theorem ha00398 : a00398.IsHomogeneous 235 := by
  unfold a00398
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (1 : ℂ))).mul (ha00001.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00390.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00397.pow 1)))

@[irreducible]
def a00399 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00025 ^ 2) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00126 ^ 1 * a00368 ^ 1)
theorem ha00399 : a00399.IsHomogeneous 43 := by
  unfold a00399
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 2)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00126.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a00400 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00399 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00126 ^ 1 * a00368 ^ 1)
theorem ha00400 : a00400.IsHomogeneous 43 := by
  unfold a00400
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00399.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00126.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a00401 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00127 ^ 1 * a00400 ^ 1) + (C ((4 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a00138 ^ 1)
theorem ha00401 : a00401.IsHomogeneous 67 := by
  unfold a00401
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00127.pow 1)).mul (ha00400.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha00138.pow 1)))

@[irreducible]
def a00402 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00126 ^ 2 * a00372 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a00401 ^ 1)
theorem ha00402 : a00402.IsHomogeneous 79 := by
  unfold a00402
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00126.pow 2)).mul (ha00372.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha00401.pow 1)))

@[irreducible]
def a00403 : Poly := (C ((-4 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 1 * a00153 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00393 ^ 1)
theorem ha00403 : a00403.IsHomogeneous 145 := by
  unfold a00403
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha00153.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00393.pow 1)))

@[irreducible]
def a00404 : Poly := (C ((-9 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 2 * a00100 ^ 2 * a00402 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00403 ^ 1)
theorem ha00404 : a00404.IsHomogeneous 175 := by
  unfold a00404
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 2)).mul (ha00100.pow 2)).mul (ha00402.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00403.pow 1)))

@[irreducible]
def a00405 : Poly := (C ((-288 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00006 ^ 1 * a00014 ^ 3 * a00042 ^ 2 * a00100 ^ 1 * a00126 ^ 2 * a00127 ^ 1 * a00367 ^ 1) + (C ((-9 : ℂ) / (12500 : ℂ)) * a00001 ^ 10 * a00002 ^ 3 * a00004 ^ 3 * a00005 ^ 3 * a00012 ^ 2 * a00014 ^ 4 * a00042 ^ 2 * a00100 ^ 4 * a00125 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a00125 ^ 1 * a00398 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 2 * a00125 ^ 1 * a00404 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 2 * a00126 ^ 1 * a00136 ^ 1 * a00153 ^ 1) + (C ((3 : ℂ) / (1 : ℂ)) * a00004 ^ 1 * a00012 ^ 1 * a00042 ^ 1 * a00126 ^ 1 * a00136 ^ 1 * a00151 ^ 1)
theorem ha00405 : a00405.IsHomogeneous 316 := by
  unfold a00405
  exact ((((((((((((((isHomogeneous_C (σ := Fin 6) ((-288 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 3)).mul (ha00042.pow 2)).mul (ha00100.pow 1)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha00367.pow 1)).add ((((((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (12500 : ℂ))).mul (ha00001.pow 10)).mul (ha00002.pow 3)).mul (ha00004.pow 3)).mul (ha00005.pow 3)).mul (ha00012.pow 2)).mul (ha00014.pow 4)).mul (ha00042.pow 2)).mul (ha00100.pow 4)).mul (ha00125.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha00125.pow 1)).mul (ha00398.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00125.pow 1)).mul (ha00404.pow 1))).add ((((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00126.pow 1)).mul (ha00136.pow 1)).mul (ha00153.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (1 : ℂ))).mul (ha00004.pow 1)).mul (ha00012.pow 1)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00136.pow 1)).mul (ha00151.pow 1)))

@[irreducible]
def a00406 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00383 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00042 ^ 1 * a00368 ^ 1)
theorem ha00406 : a00406.IsHomogeneous 37 := by
  unfold a00406
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00383.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a00407 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00025 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00126 ^ 1)
theorem ha00407 : a00407.IsHomogeneous 37 := by
  unfold a00407
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00126.pow 1)))

@[irreducible]
def a00408 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00383 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00407 ^ 1)
theorem ha00408 : a00408.IsHomogeneous 37 := by
  unfold a00408
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00383.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00407.pow 1)))

@[irreducible]
def a00409 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00406 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00408 ^ 1)
theorem ha00409 : a00409.IsHomogeneous 37 := by
  unfold a00409
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00406.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00408.pow 1)))

@[irreducible]
def a00410 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00406 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00042 ^ 1 * a00368 ^ 1)
theorem ha00410 : a00410.IsHomogeneous 37 := by
  unfold a00410
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00406.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00042.pow 1)).mul (ha00368.pow 1)))

@[irreducible]
def a00411 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00409 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00410 ^ 1)
theorem ha00411 : a00411.IsHomogeneous 37 := by
  unfold a00411
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00409.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00410.pow 1)))

@[irreducible]
def a00412 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00407 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00126 ^ 1)
theorem ha00412 : a00412.IsHomogeneous 37 := by
  unfold a00412
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00407.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00126.pow 1)))

@[irreducible]
def a00413 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00408 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00412 ^ 1)
theorem ha00413 : a00413.IsHomogeneous 37 := by
  unfold a00413
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00408.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00412.pow 1)))

@[irreducible]
def a00414 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00409 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00413 ^ 1)
theorem ha00414 : a00414.IsHomogeneous 37 := by
  unfold a00414
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00409.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00413.pow 1)))

@[irreducible]
def a00415 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00411 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00414 ^ 1)
theorem ha00415 : a00415.IsHomogeneous 37 := by
  unfold a00415
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00411.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00414.pow 1)))

@[irreducible]
def a00416 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 4 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 4 * a00025 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00064 ^ 1 * a00155 ^ 1)
theorem ha00416 : a00416.IsHomogeneous 47 := by
  unfold a00416
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 4)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 4)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00064.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a00417 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00003 ^ 1 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 3 * a00025 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00040 ^ 1 * a00129 ^ 1)
theorem ha00417 : a00417.IsHomogeneous 38 := by
  unfold a00417
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00003.pow 1)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 3)).mul (ha00025.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00040.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00418 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00417 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00416 ^ 1)
theorem ha00418 : a00418.IsHomogeneous 47 := by
  unfold a00418
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00417.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00416.pow 1)))

@[irreducible]
def a00419 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00417 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00040 ^ 1 * a00129 ^ 1)
theorem ha00419 : a00419.IsHomogeneous 38 := by
  unfold a00419
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00417.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00040.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00420 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00419 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00418 ^ 1)
theorem ha00420 : a00420.IsHomogeneous 47 := by
  unfold a00420
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00419.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00418.pow 1)))

@[irreducible]
def a00421 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00416 ^ 1) + (C ((2 : ℂ) / (27 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00064 ^ 1 * a00155 ^ 1)
theorem ha00421 : a00421.IsHomogeneous 47 := by
  unfold a00421
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00416.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (27 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00064.pow 1)).mul (ha00155.pow 1)))

@[irreducible]
def a00422 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00418 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00421 ^ 1)
theorem ha00422 : a00422.IsHomogeneous 47 := by
  unfold a00422
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00418.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00421.pow 1)))

@[irreducible]
def a00423 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00420 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00422 ^ 1)
theorem ha00423 : a00423.IsHomogeneous 47 := by
  unfold a00423
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00420.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00422.pow 1)))

@[irreducible]
def a00424 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00419 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00040 ^ 1 * a00129 ^ 1)
theorem ha00424 : a00424.IsHomogeneous 38 := by
  unfold a00424
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00419.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00040.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00425 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00424 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00420 ^ 1)
theorem ha00425 : a00425.IsHomogeneous 47 := by
  unfold a00425
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00424.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00420.pow 1)))

@[irreducible]
def a00426 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00423 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00425 ^ 1)
theorem ha00426 : a00426.IsHomogeneous 47 := by
  unfold a00426
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00423.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00425.pow 1)))

@[irreducible]
def a00427 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 4) + (C ((1 : ℂ) / (1 : ℂ)) * a00070 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00037 ^ 1 * a00042 ^ 1)
theorem ha00427 : a00427.IsHomogeneous 37 := by
  unfold a00427
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 4)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00070.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00037.pow 1)).mul (ha00042.pow 1)))

@[irreducible]
def a00428 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00037 ^ 1 * a00042 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00071 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00427 ^ 1)
theorem ha00428 : a00428.IsHomogeneous 37 := by
  unfold a00428
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00037.pow 1)).mul (ha00042.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00071.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00427.pow 1)))

@[irreducible]
def a00429 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00009 ^ 1 * a00014 ^ 4) + (C ((1 : ℂ) / (1 : ℂ)) * a00072 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00054 ^ 1)
theorem ha00429 : a00429.IsHomogeneous 37 := by
  unfold a00429
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00009.pow 1)).mul (ha00014.pow 4)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00072.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00054.pow 1)))

@[irreducible]
def a00430 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00073 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00427 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00429 ^ 1)
theorem ha00430 : a00430.IsHomogeneous 37 := by
  unfold a00430
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00073.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00427.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00429.pow 1)))

@[irreducible]
def a00431 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00074 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00428 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00430 ^ 1)
theorem ha00431 : a00431.IsHomogeneous 37 := by
  unfold a00431
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00074.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00428.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00430.pow 1)))

@[irreducible]
def a00432 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00054 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00075 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00429 ^ 1)
theorem ha00432 : a00432.IsHomogeneous 37 := by
  unfold a00432
  exact (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00054.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00075.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00429.pow 1)))

@[irreducible]
def a00433 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00076 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00430 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00432 ^ 1)
theorem ha00433 : a00433.IsHomogeneous 37 := by
  unfold a00433
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00076.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00430.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00432.pow 1)))

@[irreducible]
def a00434 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00077 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00431 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00433 ^ 1)
theorem ha00434 : a00434.IsHomogeneous 37 := by
  unfold a00434
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00077.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00431.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00433.pow 1)))

@[irreducible]
def a00435 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00156 ^ 1)
theorem ha00435 : a00435.IsHomogeneous 18 := by
  unfold a00435
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a00436 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00014 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00435 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00156 ^ 1)
theorem ha00436 : a00436.IsHomogeneous 18 := by
  unfold a00436
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00014.pow 1)).mul (ha00133.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00435.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a00437 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00133 ^ 1)
theorem ha00437 : a00437.IsHomogeneous 30 := by
  unfold a00437
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00156.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00438 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00156 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00437 ^ 1) + (C ((1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00133 ^ 1)
theorem ha00438 : a00438.IsHomogeneous 30 := by
  unfold a00438
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00437.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00439 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00079 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00436 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00438 ^ 1)
theorem ha00439 : a00439.IsHomogeneous 42 := by
  unfold a00439
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00079.pow 1)).mul (ha00133.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00436.pow 1))).add (((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00438.pow 1)))

@[irreducible]
def a00440 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00437 ^ 1) + (C ((1 : ℂ) / (648 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00133 ^ 1)
theorem ha00440 : a00440.IsHomogeneous 30 := by
  unfold a00440
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00437.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (648 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00441 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00438 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00440 ^ 1) + (C ((1 : ℂ) / (432 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00003 ^ 3 * a00004 ^ 3 * a00014 ^ 1 * a00133 ^ 1)
theorem ha00441 : a00441.IsHomogeneous 30 := by
  unfold a00441
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00438.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00440.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00003.pow 3)).mul (ha00004.pow 3)).mul (ha00014.pow 1)).mul (ha00133.pow 1)))

@[irreducible]
def a00442 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00058 ^ 1 * a00441 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00014 ^ 1 * a00081 ^ 1 * a00133 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00439 ^ 1)
theorem ha00442 : a00442.IsHomogeneous 42 := by
  unfold a00442
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00058.pow 1)).mul (ha00441.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00014.pow 1)).mul (ha00081.pow 1)).mul (ha00133.pow 1))).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00439.pow 1)))

@[irreducible]
def a00443 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00130 ^ 1 * a00434 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 2 * a00426 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00014 ^ 1 * a00415 ^ 1) + (C ((8 : ℂ) / (9 : ℂ)) * a00000 ^ 4 * a00002 ^ 1 * a00003 ^ 2 * a00442 ^ 1)
theorem ha00443 : a00443.IsHomogeneous 49 := by
  unfold a00443
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)).mul (ha00434.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 2)).mul (ha00426.pow 1))).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00014.pow 1)).mul (ha00415.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (9 : ℂ))).mul (ha00000.pow 4)).mul (ha00002.pow 1)).mul (ha00003.pow 2)).mul (ha00442.pow 1)))

@[irreducible]
def a00444 : Poly := (C ((-144 : ℂ) / (5 : ℂ)) * a00001 ^ 1 * a00014 ^ 2 * a00061 ^ 1 * a00100 ^ 1 * a00134 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00004 ^ 1 * a00005 ^ 1 * a00082 ^ 1 * a00362 ^ 1)
theorem ha00444 : a00444.IsHomogeneous 151 := by
  unfold a00444
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-144 : ℂ) / (5 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 2)).mul (ha00061.pow 1)).mul (ha00100.pow 1)).mul (ha00134.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00082.pow 1)).mul (ha00362.pow 1)))

@[irreducible]
def a00445 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00444 ^ 1) + (C ((9 : ℂ) / (250 : ℂ)) * a00001 ^ 5 * a00002 ^ 3 * a00004 ^ 2 * a00005 ^ 2 * a00014 ^ 3 * a00100 ^ 2 * a00443 ^ 1)
theorem ha00445 : a00445.IsHomogeneous 151 := by
  unfold a00445
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00444.pow 1)).add ((((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (250 : ℂ))).mul (ha00001.pow 5)).mul (ha00002.pow 3)).mul (ha00004.pow 2)).mul (ha00005.pow 2)).mul (ha00014.pow 3)).mul (ha00100.pow 2)).mul (ha00443.pow 1)))

@[irreducible]
def a00446 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00012 ^ 2 * a00014 ^ 2 * a00042 ^ 2 * a00125 ^ 1 * a00126 ^ 2 * a00127 ^ 1 * a00445 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00134 ^ 1 * a00405 ^ 1)
theorem ha00446 : a00446.IsHomogeneous 376 := by
  unfold a00446
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00012.pow 2)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00125.pow 1)).mul (ha00126.pow 2)).mul (ha00127.pow 1)).mul (ha00445.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00134.pow 1)).mul (ha00405.pow 1)))

@[irreducible]
def a00447 : Poly := (C ((-1 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00012 ^ 1 * a00241 ^ 1)
theorem ha00447 : a00447.IsHomogeneous 55 := by
  unfold a00447
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00012.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a00448 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00135 ^ 1 * a00293 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00125 ^ 1 * a00447 ^ 1)
theorem ha00448 : a00448.IsHomogeneous 124 := by
  unfold a00448
  exact ((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00135.pow 1)).mul (ha00293.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00125.pow 1)).mul (ha00447.pow 1)))

@[irreducible]
def a00449 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00261 ^ 1)
theorem ha00449 : a00449.IsHomogeneous 121 := by
  unfold a00449
  exact ((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00261.pow 1)))

@[irreducible]
def a00450 : Poly := (C ((-4 : ℂ) / (15 : ℂ)) * a00001 ^ 1 * a00014 ^ 1 * a00449 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00448 ^ 1)
theorem ha00450 : a00450.IsHomogeneous 128 := by
  unfold a00450
  exact (((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (15 : ℂ))).mul (ha00001.pow 1)).mul (ha00014.pow 1)).mul (ha00449.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00448.pow 1)))

@[irreducible]
def a00451 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00136 ^ 1 * a00292 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00450 ^ 1)
theorem ha00451 : a00451.IsHomogeneous 406 := by
  unfold a00451
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00136.pow 1)).mul (ha00292.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00450.pow 1)))

@[irreducible]
def a00452 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a00261 ^ 1) + (C ((3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00451 ^ 1)
theorem ha00452 : a00452.IsHomogeneous 485 := by
  unfold a00452
  exact (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha00261.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00451.pow 1)))

@[irreducible]
def a00453 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a00306 ^ 1) + (C ((8 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00452 ^ 1)
theorem ha00453 : a00453.IsHomogeneous 593 := by
  unfold a00453
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha00306.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((8 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00452.pow 1)))

@[irreducible]
def a00454 : Poly := (C ((-4 : ℂ) / (3 : ℂ)) * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00452 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00136 ^ 1 * a00310 ^ 1)
theorem ha00454 : a00454.IsHomogeneous 569 := by
  unfold a00454
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-4 : ℂ) / (3 : ℂ))).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00452.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00136.pow 1)).mul (ha00310.pow 1)))

@[irreducible]
def a00455 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00025 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00014 ^ 1 * a00130 ^ 1)
theorem ha00455 : a00455.IsHomogeneous 12 := by
  unfold a00455
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00025.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00014.pow 1)).mul (ha00130.pow 1)))

@[irreducible]
def a00456 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00455 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00303 ^ 1)
theorem ha00456 : a00456.IsHomogeneous 120 := by
  unfold a00456
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00455.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00303.pow 1)))

@[irreducible]
def a00457 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (6 : ℂ)) * a00003 ^ 3 * a00042 ^ 1)
theorem ha00457 : a00457.IsHomogeneous 27 := by
  unfold a00457
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (6 : ℂ))).mul (ha00003.pow 3)).mul (ha00042.pow 1)))

@[irreducible]
def a00458 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00025 ^ 1 * a00042 ^ 1 * a00133 ^ 1) + (C ((6 : ℂ) / (1 : ℂ)) * a00032 ^ 1 * a00042 ^ 1 * a00130 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00025 ^ 1 * a00032 ^ 1 * a00129 ^ 1)
theorem ha00458 : a00458.IsHomogeneous 36 := by
  unfold a00458
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00025.pow 1)).mul (ha00042.pow 1)).mul (ha00133.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (1 : ℂ))).mul (ha00032.pow 1)).mul (ha00042.pow 1)).mul (ha00130.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00025.pow 1)).mul (ha00032.pow 1)).mul (ha00129.pow 1)))

@[irreducible]
def a00459 : Poly := (C ((-1 : ℂ) / (1296 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3 * a00458 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00457 ^ 1) + (C ((1 : ℂ) / (139968 : ℂ)) * a00000 ^ 18 * a00001 ^ 6 * a00003 ^ 3 * a00004 ^ 6 * a00032 ^ 2 * a00133 ^ 1)
theorem ha00459 : a00459.IsHomogeneous 51 := by
  unfold a00459
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1296 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)).mul (ha00458.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00457.pow 1))).add (((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (139968 : ℂ))).mul (ha00000.pow 18)).mul (ha00001.pow 6)).mul (ha00003.pow 3)).mul (ha00004.pow 6)).mul (ha00032.pow 2)).mul (ha00133.pow 1)))

@[irreducible]
def a00460 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00100 ^ 1 * a00459 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00137 ^ 1 * a00260 ^ 1)
theorem ha00460 : a00460.IsHomogeneous 96 := by
  unfold a00460
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00100.pow 1)).mul (ha00459.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00137.pow 1)).mul (ha00260.pow 1)))

@[irreducible]
def a00461 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00006 ^ 1 * a00009 ^ 1) + (C ((1 : ℂ) / (432 : ℂ)) * a00000 ^ 9 * a00001 ^ 3 * a00004 ^ 3)
theorem ha00461 : a00461.IsHomogeneous 15 := by
  unfold a00461
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00006.pow 1)).mul (ha00009.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (432 : ℂ))).mul (ha00000.pow 9)).mul (ha00001.pow 3)).mul (ha00004.pow 3)))

@[irreducible]
def a00462 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00042 ^ 1 * a00100 ^ 1 * a00126 ^ 1 * a00461 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a00301 ^ 1)
theorem ha00462 : a00462.IsHomogeneous 114 := by
  unfold a00462
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00126.pow 1)).mul (ha00461.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha00301.pow 1)))

@[irreducible]
def a00463 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00455 ^ 1)
theorem ha00463 : a00463.IsHomogeneous 36 := by
  unfold a00463
  exact ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a00464 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00298 ^ 1)
theorem ha00464 : a00464.IsHomogeneous 36 := by
  unfold a00464
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00298.pow 1)))

@[irreducible]
def a00465 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00463 ^ 1) + (C ((4 : ℂ) / (3 : ℂ)) * a00464 ^ 1)
theorem ha00465 : a00465.IsHomogeneous 36 := by
  unfold a00465
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((4 : ℂ) / (3 : ℂ))).mul (ha00464.pow 1)))

@[irreducible]
def a00466 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00139 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00465 ^ 1)
theorem ha00466 : a00466.IsHomogeneous 72 := by
  unfold a00466
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00139.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00465.pow 1)))

@[irreducible]
def a00467 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00082 ^ 1 * a00300 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00241 ^ 1)
theorem ha00467 : a00467.IsHomogeneous 103 := by
  unfold a00467
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00300.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a00468 : Poly := (C ((-9 : ℂ) / (20 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00466 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00467 ^ 1)
theorem ha00468 : a00468.IsHomogeneous 103 := by
  unfold a00468
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-9 : ℂ) / (20 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00466.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00467.pow 1)))

@[irreducible]
def a00469 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00463 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00464 ^ 1)
theorem ha00469 : a00469.IsHomogeneous 36 := by
  unfold a00469
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00464.pow 1)))

@[irreducible]
def a00470 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00141 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00469 ^ 1)
theorem ha00470 : a00470.IsHomogeneous 72 := by
  unfold a00470
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00141.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00469.pow 1)))

@[irreducible]
def a00471 : Poly := (C ((-3 : ℂ) / (5 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00470 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00467 ^ 1)
theorem ha00471 : a00471.IsHomogeneous 103 := by
  unfold a00471
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (5 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00470.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00467.pow 1)))

@[irreducible]
def a00472 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a00471 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00468 ^ 1)
theorem ha00472 : a00472.IsHomogeneous 103 := by
  unfold a00472
  exact (((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha00471.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00468.pow 1)))

@[irreducible]
def a00473 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00463 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00464 ^ 1)
theorem ha00473 : a00473.IsHomogeneous 36 := by
  unfold a00473
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00463.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00464.pow 1)))

@[irreducible]
def a00474 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00144 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00473 ^ 1)
theorem ha00474 : a00474.IsHomogeneous 72 := by
  unfold a00474
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00144.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00473.pow 1)))

@[irreducible]
def a00475 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00474 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00467 ^ 1)
theorem ha00475 : a00475.IsHomogeneous 103 := by
  unfold a00475
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00474.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00467.pow 1)))

@[irreducible]
def a00476 : Poly := (C ((-2 : ℂ) / (5 : ℂ)) * a00475 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00472 ^ 1)
theorem ha00476 : a00476.IsHomogeneous 103 := by
  unfold a00476
  exact (((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (5 : ℂ))).mul (ha00475.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00472.pow 1)))

@[irreducible]
def a00477 : Poly := (C ((-2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00146 ^ 1 * a00299 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a00476 ^ 1)
theorem ha00477 : a00477.IsHomogeneous 121 := by
  unfold a00477
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00146.pow 1)).mul (ha00299.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha00476.pow 1)))

@[irreducible]
def a00478 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00477 ^ 1) + (C ((6 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00462 ^ 1)
theorem ha00478 : a00478.IsHomogeneous 127 := by
  unfold a00478
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00477.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00462.pow 1)))

@[irreducible]
def a00479 : Poly := (C ((-2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00147 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00478 ^ 1)
theorem ha00479 : a00479.IsHomogeneous 127 := by
  unfold a00479
  exact ((((isHomogeneous_C (σ := Fin 6) ((-2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00147.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00478.pow 1)))

@[irreducible]
def a00480 : Poly := (C ((-27 : ℂ) / (500 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00100 ^ 1 * a00460 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 2 * a00479 ^ 1)
theorem ha00480 : a00480.IsHomogeneous 139 := by
  unfold a00480
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-27 : ℂ) / (500 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00100.pow 1)).mul (ha00460.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 2)).mul (ha00479.pow 1)))

@[irreducible]
def a00481 : Poly := (C ((-1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00148 ^ 1 * a00298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00480 ^ 1)
theorem ha00481 : a00481.IsHomogeneous 169 := by
  unfold a00481
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00148.pow 1)).mul (ha00298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00480.pow 1)))

@[irreducible]
def a00482 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00481 ^ 1) + (C ((3 : ℂ) / (25 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00006 ^ 1 * a00014 ^ 6 * a00456 ^ 1)
theorem ha00482 : a00482.IsHomogeneous 169 := by
  unfold a00482
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00481.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((3 : ℂ) / (25 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00006.pow 1)).mul (ha00014.pow 6)).mul (ha00456.pow 1)))

@[irreducible]
def a00483 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00003 ^ 6 * a00100 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00260 ^ 1)
theorem ha00483 : a00483.IsHomogeneous 42 := by
  unfold a00483
  exact ((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 6)).mul (ha00100.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00260.pow 1)))

@[irreducible]
def a00484 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00100 ^ 1 * a00241 ^ 1)
theorem ha00484 : a00484.IsHomogeneous 85 := by
  unfold a00484
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a00485 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00484 ^ 1)
theorem ha00485 : a00485.IsHomogeneous 85 := by
  unfold a00485
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00260.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00484.pow 1)))

@[irreducible]
def a00486 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (2 : ℂ)) * a00100 ^ 1 * a00241 ^ 1)
theorem ha00486 : a00486.IsHomogeneous 85 := by
  unfold a00486
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00260.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (2 : ℂ))).mul (ha00100.pow 1)).mul (ha00241.pow 1)))

@[irreducible]
def a00487 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00485 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00486 ^ 1)
theorem ha00487 : a00487.IsHomogeneous 85 := by
  unfold a00487
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00485.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00486.pow 1)))

@[irreducible]
def a00488 : Poly := (C ((-3 : ℂ) / (2 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00082 ^ 1 * a00100 ^ 1 * a00129 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00042 ^ 1 * a00487 ^ 1)
theorem ha00488 : a00488.IsHomogeneous 109 := by
  unfold a00488
  exact (((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (2 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00082.pow 1)).mul (ha00100.pow 1)).mul (ha00129.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00042.pow 1)).mul (ha00487.pow 1)))

@[irreducible]
def a00489 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00488 ^ 1) + (C ((9 : ℂ) / (10 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 4 * a00100 ^ 1 * a00483 ^ 1)
theorem ha00489 : a00489.IsHomogeneous 109 := by
  unfold a00489
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00488.pow 1)).add (((((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (10 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 4)).mul (ha00100.pow 1)).mul (ha00483.pow 1)))

@[irreducible]
def a00490 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00150 ^ 1 * a00306 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00127 ^ 1 * a00489 ^ 1)
theorem ha00490 : a00490.IsHomogeneous 181 := by
  unfold a00490
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00150.pow 1)).mul (ha00306.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00489.pow 1)))

@[irreducible]
def a00491 : Poly := (C ((-5 : ℂ) / (3 : ℂ)) * a00042 ^ 1 * a00100 ^ 1 * a00482 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00126 ^ 1 * a00490 ^ 1)
theorem ha00491 : a00491.IsHomogeneous 229 := by
  unfold a00491
  exact (((((isHomogeneous_C (σ := Fin 6) ((-5 : ℂ) / (3 : ℂ))).mul (ha00042.pow 1)).mul (ha00100.pow 1)).mul (ha00482.pow 1)).add (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00126.pow 1)).mul (ha00490.pow 1)))

@[irreducible]
def a00492 : Poly := (C ((-1 : ℂ) / (3 : ℂ)) * a00491 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00151 ^ 1 * a00305 ^ 1)
theorem ha00492 : a00492.IsHomogeneous 229 := by
  unfold a00492
  exact (((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (3 : ℂ))).mul (ha00491.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha00305.pow 1)))

@[irreducible]
def a00493 : Poly := (C ((-8 : ℂ) / (9 : ℂ)) * a00042 ^ 1 * a00126 ^ 1 * a00151 ^ 1 * a00296 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00492 ^ 1)
theorem ha00493 : a00493.IsHomogeneous 655 := by
  unfold a00493
  exact ((((((isHomogeneous_C (σ := Fin 6) ((-8 : ℂ) / (9 : ℂ))).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00151.pow 1)).mul (ha00296.pow 1)).add (((((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00492.pow 1)))

@[irreducible]
def a00494 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00025 ^ 1 * a00298 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00455 ^ 1)
theorem ha00494 : a00494.IsHomogeneous 42 := by
  unfold a00494
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00298.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00455.pow 1)))

@[irreducible]
def a00495 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00127 ^ 1 * a00494 ^ 1) + (C ((2 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00014 ^ 1 * a00025 ^ 1 * a00126 ^ 1 * a00299 ^ 1)
theorem ha00495 : a00495.IsHomogeneous 60 := by
  unfold a00495
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00127.pow 1)).mul (ha00494.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00014.pow 1)).mul (ha00025.pow 1)).mul (ha00126.pow 1)).mul (ha00299.pow 1)))

@[irreducible]
def a00496 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00138 ^ 1 * a00298 ^ 1) + (C ((1 : ℂ) / (3 : ℂ)) * a00003 ^ 3 * a00126 ^ 1 * a00461 ^ 1)
theorem ha00496 : a00496.IsHomogeneous 48 := by
  unfold a00496
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00138.pow 1)).mul (ha00298.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (3 : ℂ))).mul (ha00003.pow 3)).mul (ha00126.pow 1)).mul (ha00461.pow 1)))

@[irreducible]
def a00497 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00495 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00496 ^ 1)
theorem ha00497 : a00497.IsHomogeneous 78 := by
  unfold a00497
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00495.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00496.pow 1)))

@[irreducible]
def a00498 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00497 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00126 ^ 1 * a00152 ^ 1)
theorem ha00498 : a00498.IsHomogeneous 84 := by
  unfold a00498
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00497.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00126.pow 1)).mul (ha00152.pow 1)))

@[irreducible]
def a00499 : Poly := (C ((-1 : ℂ) / (2 : ℂ)) * a00126 ^ 1 * a00127 ^ 1 * a00484 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00082 ^ 1 * a00310 ^ 1)
theorem ha00499 : a00499.IsHomogeneous 133 := by
  unfold a00499
  exact (((((isHomogeneous_C (σ := Fin 6) ((-1 : ℂ) / (2 : ℂ))).mul (ha00126.pow 1)).mul (ha00127.pow 1)).mul (ha00484.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00082.pow 1)).mul (ha00310.pow 1)))

@[irreducible]
def a00500 : Poly := (C ((-3 : ℂ) / (10 : ℂ)) * a00001 ^ 5 * a00004 ^ 1 * a00005 ^ 1 * a00014 ^ 1 * a00100 ^ 2 * a00498 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00126 ^ 1 * a00499 ^ 1)
theorem ha00500 : a00500.IsHomogeneous 169 := by
  unfold a00500
  exact ((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (10 : ℂ))).mul (ha00001.pow 5)).mul (ha00004.pow 1)).mul (ha00005.pow 1)).mul (ha00014.pow 1)).mul (ha00100.pow 2)).mul (ha00498.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00126.pow 1)).mul (ha00499.pow 1)))

@[irreducible]
def a00501 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00153 ^ 1 * a00260 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00500 ^ 1)
theorem ha00501 : a00501.IsHomogeneous 169 := by
  unfold a00501
  exact (((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha00260.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00500.pow 1)))

@[irreducible]
def a00502 : Poly := (C ((-3 : ℂ) / (4 : ℂ)) * a00101 ^ 1 * a00103 ^ 1 * a00105 ^ 1 * a00117 ^ 1 * a00123 ^ 1 * a00124 ^ 1 * a00125 ^ 1 * a00501 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00126 ^ 1 * a00153 ^ 1 * a00296 ^ 1)
theorem ha00502 : a00502.IsHomogeneous 595 := by
  unfold a00502
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (4 : ℂ))).mul (ha00101.pow 1)).mul (ha00103.pow 1)).mul (ha00105.pow 1)).mul (ha00117.pow 1)).mul (ha00123.pow 1)).mul (ha00124.pow 1)).mul (ha00125.pow 1)).mul (ha00501.pow 1)).add ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00126.pow 1)).mul (ha00153.pow 1)).mul (ha00296.pow 1)))

@[irreducible]
def a00503 : Poly := (C ((-32 : ℂ) / (3 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a00014 ^ 2 * a00042 ^ 2 * a00502 ^ 1) + (C ((-3 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 2 * a00126 ^ 1 * a00454 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00006 ^ 1 * a00014 ^ 2 * a00042 ^ 1 * a00126 ^ 1 * a00453 ^ 1) + (C ((9 : ℂ) / (1 : ℂ)) * a00002 ^ 3 * a00005 ^ 1 * a00012 ^ 1 * a00493 ^ 1)
theorem ha00503 : a00503.IsHomogeneous 665 := by
  unfold a00503
  exact ((((((((((isHomogeneous_C (σ := Fin 6) ((-32 : ℂ) / (3 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00502.pow 1)).add ((((((isHomogeneous_C (σ := Fin 6) ((-3 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 2)).mul (ha00126.pow 1)).mul (ha00454.pow 1))).add ((((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00006.pow 1)).mul (ha00014.pow 2)).mul (ha00042.pow 1)).mul (ha00126.pow 1)).mul (ha00453.pow 1))).add (((((isHomogeneous_C (σ := Fin 6) ((9 : ℂ) / (1 : ℂ))).mul (ha00002.pow 3)).mul (ha00005.pow 1)).mul (ha00012.pow 1)).mul (ha00493.pow 1)))

@[irreducible]
def a00504 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((6 : ℂ) / (5 : ℂ)) * a00003 ^ 6)
theorem ha00504 : a00504.IsHomogeneous 6 := by
  unfold a00504
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((6 : ℂ) / (5 : ℂ))).mul (ha00003.pow 6)))

@[irreducible]
def a00505 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((5 : ℂ) / (2 : ℂ)) * a00504 ^ 1)
theorem ha00505 : a00505.IsHomogeneous 6 := by
  unfold a00505
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (2 : ℂ))).mul (ha00504.pow 1)))

@[irreducible]
def a00506 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00505 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1 * a00156 ^ 1)
theorem ha00506 : a00506.IsHomogeneous 12 := by
  unfold a00506
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00505.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).mul (ha00156.pow 1)))

@[irreducible]
def a00507 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00009 ^ 1 * a00506 ^ 1) + (C ((2 : ℂ) / (1 : ℂ)) * a00155 ^ 1 * a00157 ^ 1)
theorem ha00507 : a00507.IsHomogeneous 18 := by
  unfold a00507
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00009.pow 1)).mul (ha00506.pow 1)).add (((isHomogeneous_C (σ := Fin 6) ((2 : ℂ) / (1 : ℂ))).mul (ha00155.pow 1)).mul (ha00157.pow 1)))

@[irreducible]
def a00508 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00156 ^ 1) + (C ((5 : ℂ) / (24 : ℂ)) * a00014 ^ 1)
theorem ha00508 : a00508.IsHomogeneous 6 := by
  unfold a00508
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00156.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (24 : ℂ))).mul (ha00014.pow 1)))

@[irreducible]
def a00509 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((5 : ℂ) / (1 : ℂ)) * a00504 ^ 1)
theorem ha00509 : a00509.IsHomogeneous 6 := by
  unfold a00509
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((5 : ℂ) / (1 : ℂ))).mul (ha00504.pow 1)))

@[irreducible]
def a00510 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00014 ^ 1) + (C ((1 : ℂ) / (1 : ℂ)) * a00509 ^ 1)
theorem ha00510 : a00510.IsHomogeneous 6 := by
  unfold a00510
  exact (((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00014.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00509.pow 1)))

@[irreducible]
def a00511 : Poly := (C ((1 : ℂ) / (1 : ℂ)) * a00003 ^ 6 * a00510 ^ 1) + (C ((12 : ℂ) / (1 : ℂ)) * a00156 ^ 2)
theorem ha00511 : a00511.IsHomogeneous 12 := by
  unfold a00511
  exact ((((isHomogeneous_C (σ := Fin 6) ((1 : ℂ) / (1 : ℂ))).mul (ha00003.pow 6)).mul (ha00510.pow 1)).add ((isHomogeneous_C (σ := Fin 6) ((12 : ℂ) / (1 : ℂ))).mul (ha00156.pow 2)))

end CycleQ2Concrete
